-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1336_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:03:19.833918+00:00
-- url     : https://prove2.me/submissions/374f0cad-778e-450d-989e-0770efa15a11

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_signed_majorant
/- Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa,
bwdaugherty and Yuxuan Xu. All new numerical implications are checked below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring
theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]
end HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalRealBundle
theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'
end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_support {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (w x : ι → ℝ)
    (hw : (∑ i, |w i| ^ q) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ w x hpq.symm
  have hq : 0 ≤ 1/q := hpq.symm.one_div_nonneg
  have hr := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (w i)) q) hw hq
  rw [Real.one_rpow] at hr
  have hn := lpNorm_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hr hn
  simpa only [lpNorm, Real.norm_eq_abs, one_mul] using h.trans hm

theorem power12over11_upper {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^12 ≤ y^11) : x^(12/11 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 12) h (by norm_num : (0 : ℝ) ≤ 1/11)
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast y 11,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy] at hr
  norm_num at hr ⊢
  exact hr

theorem norm_support12 (w v x : Fin 3 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i, |w i|^12 ≤ (v i)^11)
    (hs : (∑ i, v i) ≤ 1) : (∑ i, w i*x i) ≤ lpNorm 12 x := by
  apply norm_support (q := 12/11)
    (Real.holderConjugate_iff.mpr (by norm_num))
  exact (Finset.sum_le_sum fun i _ => power12over11_upper (abs_nonneg _) (hv i) (hp i)).trans hs

theorem power_ratio_upper {x y : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^m ≤ y^n) :
    x^((m : ℝ)/(n : ℝ)) ≤ y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.rpow_le_rpow (pow_nonneg hx m) h (one_div_nonneg.mpr hn0.le)
  rw [← Real.rpow_natCast x m, ← Real.rpow_natCast y n,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy,
    mul_one_div_cancel hn0.ne', Real.rpow_one] at hr
  simpa only [div_eq_mul_inv, one_div, one_mul] using hr

theorem norm_support_interval {p b : ℝ} (hp : 1 < p) (hb : 1 < b)
    (hpb : p ≤ b) (w x : Fin 3 → ℝ)
    (hw1 : ∀ i, |w i| ≤ 1)
    (hw : (∑ i, |w i|^(b/(b-1))) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have hqp : b/(b-1) ≤ p/(p-1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hq0 : 0 ≤ b/(b-1) := div_nonneg (by linarith) (by linarith)
  apply norm_support (q := p/(p-1))
    ((Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl)
  apply le_trans _ hw
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
    (abs_nonneg _) (hw1 i) hq0 hqp

theorem norm_support_interval_cert {p b : ℝ} (m n : ℕ) (hn : 0 < n)
    (hp : 1 < p) (hb : 1 < b) (hpb : p ≤ b)
    (hconj : b/(b-1) = (m : ℝ)/(n : ℝ))
    (w v x : Fin 3 → ℝ) (hw1 : ∀ i, |w i| ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (hpowers : ∀ i, |w i|^m ≤ (v i)^n) (hs : (∑ i, v i) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  apply norm_support_interval hp hb hpb w x hw1
  rw [hconj]
  exact (Finset.sum_le_sum fun i _ =>
    power_ratio_upper m n hn (abs_nonneg _) (hv i) (hpowers i)).trans hs

end HlawkaSchatten.DiagonalCutoff12


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6




theorem total_eq (X : Fin 3 → Fin 3 → ℝ) : total X = X 0+X 1+X 2 := by
  simp [total,Fin.sum_univ_three]
theorem pair0 (X : Fin 3 → Fin 3 → ℝ) : pair X 0 = X 1+X 2 := by
  rw [pair,total_eq];abel
theorem pair1 (X : Fin 3 → Fin 3 → ℝ) : pair X 1 = X 0+X 2 := by
  rw [pair,total_eq];abel
theorem pair2 (X : Fin 3 → Fin 3 → ℝ) : pair X 2 = X 0+X 1 := by
  rw [pair,total_eq];abel


theorem oriented_frame {p q k d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : RelativeOrientedData p q k d X) : Frame p k (3*q) d X := by
  constructor
  · simpa [Fin.sum_univ_three] using h.sum
  · simpa [total_eq] using h.norm_le_total
  · simpa [total_eq] using h.total_one
  · simpa [total_eq] using h.total_cap.le
  · intro i;fin_cases i
    · simpa [pair0] using h.main0
    · simpa [pair1] using h.main1
    · simpa [pair2] using h.main2
  · intro i h';fin_cases i
    · simpa [pair0] using h.max0 h'
    · simpa [pair1] using h.max1 h'
    · simpa [pair2] using h.max2 h'
  · simpa [total_eq,Fin.sum_univ_three,pair0,pair1,pair2] using h.linear_failure

theorem total_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) :
    total (relabel e X) = total X ∘ e := by
  ext h
  simp only [total,Finset.sum_apply,relabel,Function.comp_apply]
  exact Equiv.sum_comp e (fun j => X j (e h))

theorem pair_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    pair (relabel e X) i = pair X (e i) ∘ e := by
  ext h
  simp [pair,total_relabel,relabel]

theorem frame_relabel {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : Frame p k A d X) (e : Equiv.Perm (Fin 3)) : Frame p k A d (relabel e X) := by
  have hr (j : Fin 3) : lpNorm p (relabel e X j) = lpNorm p (X (e j)) :=
    lpNorm_comp_equiv p (X (e j)) e
  have ht : lpNorm p (total (relabel e X)) = lpNorm p (total X) := by
    rw [total_relabel,lpNorm_comp_equiv]
  have hp (i : Fin 3) : lpNorm p (pair (relabel e X) i) = lpNorm p (pair X (e i)) := by
    rw [pair_relabel,lpNorm_comp_equiv]
  constructor
  · simp_rw [hr];rw [Equiv.sum_comp e (fun j => lpNorm p (X j))];exact h.sum
  · intro j;rw [hr,ht];exact h.row_total (e j)
  · rw [ht];exact h.total_one
  · rw [ht];exact h.total_cap
  · intro i;rw [hp,pair_relabel];exact h.main (e i)
  · intro i j;rw [pair_relabel];exact h.maximal (e i) (e j)
  · simp_rw [ht,hp];rw [Equiv.sum_comp e (fun i => lpNorm p (pair X i))];exact h.linear_failure

theorem frame_box_of_base {p k A d ell u v w rho : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_ratio_of_base {p k A d rho R : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201

end HlawkaSchatten.DiagonalCutoff6

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6


theorem pair_eq_of_distinct (X : Fin 3 → Fin 3 → ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : pair X i = X j+X l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
  all_goals first
    | exact pair0 X
    | exact (pair0 X).trans (add_comm _ _)
    | exact pair1 X
    | exact (pair1 X).trans (add_comm _ _)
    | exact pair2 X
    | exact (pair2 X).trans (add_comm _ _)

theorem frame_linear_data {p k A d : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : Frame p k A d X) :
    LinearData k A d X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · exact h.main
  · exact h.maximal
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem linear_data_bounds {k A d T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : LinearData k A d X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]

theorem positive_pair_majorant {p a rho alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha)
    (hc1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hc2 : 1+2*rho^a ≤ (1+2*alpha*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hm : ∀ i, 0 ≤ pair X i i)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ pair X i i+alpha*(pair X i j+pair X i l) := by
  rw [HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p _ hij hil hjl]
  have hh := signed_majorant hp ha hap hrho hrho1 halpha hc1 hc2 (hm i)
    (hratio i j hij) (hratio i l hil)
  simpa only [abs_of_nonneg (hsign i j hij),abs_of_nonneg (hsign i l hil)] using hh

theorem frame_weaken {p k A d k' A' d' : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (h : Frame p k A d X) (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    Frame p k' A' d' X := by
  have f := frame_linear_data hp X h
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  constructor
  · exact h.sum
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap.trans hA
  · intro i
    exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (h.main i)
  · exact h.maximal
  · have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
    linarith only [hh,h.linear_failure]

end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

end HlawkaSchatten.DiagonalCutoff4

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff4

theorem rational_powers_le (a b c d m n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : a^m*d^n ≤ c^n*b^m) :
    ((a : ℝ)/b)^m ≤ ((c : ℝ)/d)^n := by
  rw [div_pow,div_pow]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)).mpr
  exact_mod_cast h

theorem rectangle_budgets {a lo hi c alpha pl ph : ℝ}
    (hl : lo^a ≤ pl) (hh : hi^a ≤ ph)
    (h00 : 1+2*pl ≤ (c+2*alpha*lo)^a)
    (h10 : 1+ph+pl ≤ (c+alpha*(hi+lo))^a)
    (h11 : 1+2*ph ≤ (c+2*alpha*hi)^a) :
    1+2*lo^a ≤ (c+2*alpha*lo)^a ∧
    1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a ∧
    1+2*hi^a ≤ (c+2*alpha*hi)^a := by
  constructor
  · linarith only [hl,h00]
  constructor
  · linarith only [hl,hh,h10]
  · linarith only [hh,h11]

theorem sum_two_bounds {x y X Y z : ℝ} (hx : x ≤ X) (hy : y ≤ Y)
    (hz : X+2*Y ≤ z) : x+2*y ≤ z := by
  linarith only [hx,hy,hz]

theorem three_bounds {x X : ℝ} (hx : x ≤ X) (hX : 3*X ≤ 1) : x+x+x ≤ 1 := by
  linarith only [hx,hX]

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1336_s3_0 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1023671899/5000000000 : ℝ)*x 0 + (5427945371/10000000000 : ℝ)*x 1 + (5230689749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1023671899/5000000000 : ℝ)^537 ≤ (778936649273/6250000000000 : ℝ)^409 := by
    have hnat : (1023671899 : ℕ)^537*6250000000000^409 ≤ 778936649273^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023671899 5000000000 778936649273 6250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427945371/10000000000 : ℝ)^537 ≤ (22415963138213/50000000000000 : ℝ)^409 := by
    have hnat : (5427945371 : ℕ)^537*50000000000000^409 ≤ 22415963138213^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427945371 10000000000 22415963138213 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230689749/10000000000 : ℝ)^537 ≤ (21352543655703/50000000000000 : ℝ)^409 := by
    have hnat : (5230689749 : ℕ)^537*50000000000000^409 ≤ 21352543655703^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230689749 10000000000 21352543655703 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1023671899/5000000000 : ℝ), (5427945371/10000000000 : ℝ), (5230689749/10000000000 : ℝ)] ![(778936649273/6250000000000 : ℝ), (22415963138213/50000000000000 : ℝ), (21352543655703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1023671899/5000000000 : ℝ)|^537 ≤ (778936649273/6250000000000 : ℝ)^409
        have hw : |(-1023671899/5000000000 : ℝ)|=(1023671899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427945371/10000000000 : ℝ)|^537 ≤ (22415963138213/50000000000000 : ℝ)^409
        have hw : |(5427945371/10000000000 : ℝ)|=(5427945371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230689749/10000000000 : ℝ)|^537 ≤ (21352543655703/50000000000000 : ℝ)^409
        have hw : |(5230689749/10000000000 : ℝ)|=(5230689749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s3_1 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5352904043/10000000000 : ℝ)*x 0 + (-429634299/2000000000 : ℝ)*x 1 + (1307672457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352904043/10000000000 : ℝ)^537 ≤ (34390561773/78125000000 : ℝ)^409 := by
    have hnat : (5352904043 : ℕ)^537*78125000000^409 ≤ 34390561773^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352904043 10000000000 34390561773 78125000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429634299/2000000000 : ℝ)^537 ≤ (13274992764439/100000000000000 : ℝ)^409 := by
    have hnat : (429634299 : ℕ)^537*100000000000000^409 ≤ 13274992764439^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429634299 2000000000 13274992764439 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307672457/2500000000 : ℝ)^537 ≤ (42705088158241/100000000000000 : ℝ)^409 := by
    have hnat : (1307672457 : ℕ)^537*100000000000000^409 ≤ 42705088158241^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307672457 2500000000 42705088158241 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352904043/10000000000 : ℝ), (-429634299/2000000000 : ℝ), (1307672457/2500000000 : ℝ)] ![(34390561773/78125000000 : ℝ), (13274992764439/100000000000000 : ℝ), (42705088158241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352904043/10000000000 : ℝ)|^537 ≤ (34390561773/78125000000 : ℝ)^409
        have hw : |(5352904043/10000000000 : ℝ)|=(5352904043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429634299/2000000000 : ℝ)|^537 ≤ (13274992764439/100000000000000 : ℝ)^409
        have hw : |(-429634299/2000000000 : ℝ)|=(429634299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307672457/2500000000 : ℝ)|^537 ≤ (42705088158241/100000000000000 : ℝ)^409
        have hw : |(1307672457/2500000000 : ℝ)|=(1307672457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s3_2 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (334556489/625000000 : ℝ)*x 0 + (2615345041/5000000000 : ℝ)*x 1 + (-42963429/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334556489/625000000 : ℝ)^537 ≤ (8803983340971/20000000000000 : ℝ)^409 := by
    have hnat : (334556489 : ℕ)^537*20000000000000^409 ≤ 8803983340971^409*625000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334556489 625000000 8803983340971 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615345041/5000000000 : ℝ)^537 ≤ (2669068180061/6250000000000 : ℝ)^409 := by
    have hnat : (2615345041 : ℕ)^537*6250000000000^409 ≤ 2669068180061^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615345041 5000000000 2669068180061 6250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42963429/200000000 : ℝ)^537 ≤ (530999695973/4000000000000 : ℝ)^409 := by
    have hnat : (42963429 : ℕ)^537*4000000000000^409 ≤ 530999695973^409*200000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42963429 200000000 530999695973 4000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334556489/625000000 : ℝ), (2615345041/5000000000 : ℝ), (-42963429/200000000 : ℝ)] ![(8803983340971/20000000000000 : ℝ), (2669068180061/6250000000000 : ℝ), (530999695973/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334556489/625000000 : ℝ)|^537 ≤ (8803983340971/20000000000000 : ℝ)^409
        have hw : |(334556489/625000000 : ℝ)|=(334556489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615345041/5000000000 : ℝ)|^537 ≤ (2669068180061/6250000000000 : ℝ)^409
        have hw : |(2615345041/5000000000 : ℝ)|=(2615345041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42963429/200000000 : ℝ)|^537 ≤ (530999695973/4000000000000 : ℝ)^409
        have hw : |(-42963429/200000000 : ℝ)|=(42963429/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s3_3 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1081772143/2500000000 : ℝ)*x 0 + (1031392419/2500000000 : ℝ)*x 1 + (1134450777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081772143/2500000000 : ℝ)^537 ≤ (33292023083163/100000000000000 : ℝ)^409 := by
    have hnat : (1081772143 : ℕ)^537*100000000000000^409 ≤ 33292023083163^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081772143 2500000000 33292023083163 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031392419/2500000000 : ℝ)^537 ≤ (31271331791099/100000000000000 : ℝ)^409 := by
    have hnat : (1031392419 : ℕ)^537*100000000000000^409 ≤ 31271331791099^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031392419 2500000000 31271331791099 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134450777/2500000000 : ℝ)^537 ≤ (7087329022451/20000000000000 : ℝ)^409 := by
    have hnat : (1134450777 : ℕ)^537*20000000000000^409 ≤ 7087329022451^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134450777 2500000000 7087329022451 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081772143/2500000000 : ℝ), (1031392419/2500000000 : ℝ), (1134450777/2500000000 : ℝ)] ![(33292023083163/100000000000000 : ℝ), (31271331791099/100000000000000 : ℝ), (7087329022451/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081772143/2500000000 : ℝ)|^537 ≤ (33292023083163/100000000000000 : ℝ)^409
        have hw : |(1081772143/2500000000 : ℝ)|=(1081772143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031392419/2500000000 : ℝ)|^537 ≤ (31271331791099/100000000000000 : ℝ)^409
        have hw : |(1031392419/2500000000 : ℝ)|=(1031392419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1134450777/2500000000 : ℝ)|^537 ≤ (7087329022451/20000000000000 : ℝ)^409
        have hw : |(1134450777/2500000000 : ℝ)|=(1134450777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s3_4 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2047363471/10000000000 : ℝ)*x 0 + (5231514769/10000000000 : ℝ)*x 1 + (2713557657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2047363471/10000000000 : ℝ)^537 ≤ (623157181247/5000000000000 : ℝ)^409 := by
    have hnat : (2047363471 : ℕ)^537*5000000000000^409 ≤ 623157181247^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047363471 10000000000 623157181247 5000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231514769/10000000000 : ℝ)^537 ≤ (21356965636273/50000000000000 : ℝ)^409 := by
    have hnat : (5231514769 : ℕ)^537*50000000000000^409 ≤ 21356965636273^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231514769 10000000000 21356965636273 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713557657/5000000000 : ℝ)^537 ≤ (44822925075989/100000000000000 : ℝ)^409 := by
    have hnat : (2713557657 : ℕ)^537*100000000000000^409 ≤ 44822925075989^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713557657 5000000000 44822925075989 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2047363471/10000000000 : ℝ), (5231514769/10000000000 : ℝ), (2713557657/5000000000 : ℝ)] ![(623157181247/5000000000000 : ℝ), (21356965636273/50000000000000 : ℝ), (44822925075989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2047363471/10000000000 : ℝ)|^537 ≤ (623157181247/5000000000000 : ℝ)^409
        have hw : |(-2047363471/10000000000 : ℝ)|=(2047363471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231514769/10000000000 : ℝ)|^537 ≤ (21356965636273/50000000000000 : ℝ)^409
        have hw : |(5231514769/10000000000 : ℝ)|=(5231514769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713557657/5000000000 : ℝ)|^537 ≤ (44822925075989/100000000000000 : ℝ)^409
        have hw : |(2713557657/5000000000 : ℝ)|=(2713557657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s3_5 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1325532211/2500000000 : ℝ)*x 0 + (-48793657/250000000 : ℝ)*x 1 + (5427115541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325532211/2500000000 : ℝ)^537 ≤ (10868126271387/25000000000000 : ℝ)^409 := by
    have hnat : (1325532211 : ℕ)^537*25000000000000^409 ≤ 10868126271387^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325532211 2500000000 10868126271387 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48793657/250000000 : ℝ)^537 ≤ (117045673627/1000000000000 : ℝ)^409 := by
    have hnat : (48793657 : ℕ)^537*1000000000000^409 ≤ 117045673627^409*250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48793657 250000000 117045673627 1000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427115541/10000000000 : ℝ)^537 ≤ (8964585507507/20000000000000 : ℝ)^409 := by
    have hnat : (5427115541 : ℕ)^537*20000000000000^409 ≤ 8964585507507^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427115541 10000000000 8964585507507 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325532211/2500000000 : ℝ), (-48793657/250000000 : ℝ), (5427115541/10000000000 : ℝ)] ![(10868126271387/25000000000000 : ℝ), (117045673627/1000000000000 : ℝ), (8964585507507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325532211/2500000000 : ℝ)|^537 ≤ (10868126271387/25000000000000 : ℝ)^409
        have hw : |(1325532211/2500000000 : ℝ)|=(1325532211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-48793657/250000000 : ℝ)|^537 ≤ (117045673627/1000000000000 : ℝ)^409
        have hw : |(-48793657/250000000 : ℝ)|=(48793657/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427115541/10000000000 : ℝ)|^537 ≤ (8964585507507/20000000000000 : ℝ)^409
        have hw : |(5427115541/10000000000 : ℝ)|=(5427115541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s3_6 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5302130521/10000000000 : ℝ)*x 0 + (5427114381/10000000000 : ℝ)*x 1 + (-390349117/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302130521/10000000000 : ℝ)^537 ≤ (43472523138509/100000000000000 : ℝ)^409 := by
    have hnat : (5302130521 : ℕ)^537*100000000000000^409 ≤ 43472523138509^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302130521 10000000000 43472523138509 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427114381/10000000000 : ℝ)^537 ≤ (44822914958709/100000000000000 : ℝ)^409 := by
    have hnat : (5427114381 : ℕ)^537*100000000000000^409 ≤ 44822914958709^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427114381 10000000000 44822914958709 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (390349117/2000000000 : ℝ)^537 ≤ (11704561890427/100000000000000 : ℝ)^409 := by
    have hnat : (390349117 : ℕ)^537*100000000000000^409 ≤ 11704561890427^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390349117 2000000000 11704561890427 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302130521/10000000000 : ℝ), (5427114381/10000000000 : ℝ), (-390349117/2000000000 : ℝ)] ![(43472523138509/100000000000000 : ℝ), (44822914958709/100000000000000 : ℝ), (11704561890427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302130521/10000000000 : ℝ)|^537 ≤ (43472523138509/100000000000000 : ℝ)^409
        have hw : |(5302130521/10000000000 : ℝ)|=(5302130521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427114381/10000000000 : ℝ)|^537 ≤ (44822914958709/100000000000000 : ℝ)^409
        have hw : |(5427114381/10000000000 : ℝ)|=(5427114381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-390349117/2000000000 : ℝ)|^537 ≤ (11704561890427/100000000000000 : ℝ)^409
        have hw : |(-390349117/2000000000 : ℝ)|=(390349117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s3_7 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4327130269/10000000000 : ℝ)*x 0 + (4536078979/10000000000 : ℝ)*x 1 + (16122279/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327130269/10000000000 : ℝ)^537 ≤ (33292444295269/100000000000000 : ℝ)^409 := by
    have hnat : (4327130269 : ℕ)^537*100000000000000^409 ≤ 33292444295269^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327130269 10000000000 33292444295269 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4536078979/10000000000 : ℝ)^537 ≤ (35418968384959/100000000000000 : ℝ)^409 := by
    have hnat : (4536078979 : ℕ)^537*100000000000000^409 ≤ 35418968384959^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536078979 10000000000 35418968384959 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16122279/39062500 : ℝ)^537 ≤ (31288587307361/100000000000000 : ℝ)^409 := by
    have hnat : (16122279 : ℕ)^537*100000000000000^409 ≤ 31288587307361^409*39062500^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16122279 39062500 31288587307361 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327130269/10000000000 : ℝ), (4536078979/10000000000 : ℝ), (16122279/39062500 : ℝ)] ![(33292444295269/100000000000000 : ℝ), (35418968384959/100000000000000 : ℝ), (31288587307361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327130269/10000000000 : ℝ)|^537 ≤ (33292444295269/100000000000000 : ℝ)^409
        have hw : |(4327130269/10000000000 : ℝ)|=(4327130269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4536078979/10000000000 : ℝ)|^537 ≤ (35418968384959/100000000000000 : ℝ)^409
        have hw : |(4536078979/10000000000 : ℝ)|=(4536078979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16122279/39062500 : ℝ)|^537 ≤ (31288587307361/100000000000000 : ℝ)^409
        have hw : |(16122279/39062500 : ℝ)|=(16122279/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1336_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (504/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2453/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10841/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3003/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (504/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2453/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (504/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2453/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (504/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2453/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (504/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2453/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (504/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2453/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (504/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2453/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (2453/25000 : ℝ) ^ (4295/1024 : ℝ) ≤ (5903266835545271/100000000000000000000 : ℝ) := by
    have hpowers : (2453/25000 : ℝ)^4295 ≤ (5903266835545271/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2453 : ℕ)^4295*100000000000000000000^1024 ≤ 5903266835545271^1024*25000^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2453 25000 5903266835545271 100000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2453/25000 : ℝ)) (X := (5903266835545271/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (504/3125 : ℝ) ^ (4295/1024 : ℝ) ≤ (9491972496802403/20000000000000000000 : ℝ) := by
    have hpowers : (504/3125 : ℝ)^4295 ≤ (9491972496802403/20000000000000000000 : ℝ)^1024 := by
      have hnat : (504 : ℕ)^4295*20000000000000000000^1024 ≤ 9491972496802403^1024*3125^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        504 3125 9491972496802403 20000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (504/3125 : ℝ)) (X := (9491972496802403/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005903266835545271/50000000000000000000 : ℝ) ≤ (10000281474900491/10000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (50005903266835545271/50000000000000000000 : ℝ)^1024 ≤ (10000281474900491/10000000000000000 : ℝ)^4295 := by
      have hnat : (50005903266835545271 : ℕ)^1024*10000000000000000^4295 ≤ 10000281474900491^4295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005903266835545271 50000000000000000000 10000281474900491 10000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281474900491/10000000000000000 : ℝ)) (X := (50005903266835545271/50000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026681564659778643/50000000000000000000 : ℝ) ≤ (2500318002003173/2500000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (50026681564659778643/50000000000000000000 : ℝ)^1024 ≤ (2500318002003173/2500000000000000 : ℝ)^4295 := by
      have hnat : (50026681564659778643 : ℕ)^1024*2500000000000000^4295 ≤ 2500318002003173^4295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026681564659778643 50000000000000000000 2500318002003173 2500000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500318002003173/2500000000000000 : ℝ)) (X := (50026681564659778643/50000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10009491972496802403/10000000000000000000 : ℝ) ≤ (10002262541124893/10000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (10009491972496802403/10000000000000000000 : ℝ)^1024 ≤ (10002262541124893/10000000000000000 : ℝ)^4295 := by
      have hnat : (10009491972496802403 : ℕ)^1024*10000000000000000^4295 ≤ 10002262541124893^4295*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009491972496802403 10000000000000000000 10002262541124893 10000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002262541124893/10000000000000000 : ℝ)) (X := (10009491972496802403/10000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5903266835545271/100000000000000000000 : ℝ) ≤ ((15785584893419417183/15790000000000000000 : ℝ)+2*(990533112201/631600000000000 : ℝ)*(2453/25000 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (15785584893419417183/15790000000000000000 : ℝ)+2*(990533112201/631600000000000 : ℝ)*(2453/25000 : ℝ)=(10000281474900491/10000000000000000 : ℝ) by norm_num, show 1+2*(5903266835545271/100000000000000000000 : ℝ)=(50005903266835545271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9491972496802403/20000000000000000000 : ℝ)+(5903266835545271/100000000000000000000 : ℝ) ≤ ((15785584893419417183/15790000000000000000 : ℝ)+(990533112201/631600000000000 : ℝ)*((504/3125 : ℝ)+(2453/25000 : ℝ)))^(4295/1024 : ℝ) := by
    rw [show (15785584893419417183/15790000000000000000 : ℝ)+(990533112201/631600000000000 : ℝ)*((504/3125 : ℝ)+(2453/25000 : ℝ))=(2500318002003173/2500000000000000 : ℝ) by norm_num, show 1+(9491972496802403/20000000000000000000 : ℝ)+(5903266835545271/100000000000000000000 : ℝ)=(50026681564659778643/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9491972496802403/20000000000000000000 : ℝ) ≤ ((15785584893419417183/15790000000000000000 : ℝ)+2*(990533112201/631600000000000 : ℝ)*(504/3125 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (15785584893419417183/15790000000000000000 : ℝ)+2*(990533112201/631600000000000 : ℝ)*(504/3125 : ℝ)=(10002262541124893/10000000000000000 : ℝ) by norm_num, show 1+2*(9491972496802403/20000000000000000000 : ℝ)=(10009491972496802403/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15785584893419417183/15790000000000000000 : ℝ)*(X 1 0+X 2 0)+(990533112201/631600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (2453/25000 : ℝ)) (hi := (504/3125 : ℝ)) (c := (15785584893419417183/15790000000000000000 : ℝ)) (alpha := (990533112201/631600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15785584893419417183/15790000000000000000 : ℝ)*(X 0 1+X 2 1)+(990533112201/631600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (2453/25000 : ℝ)) (hi := (504/3125 : ℝ)) (c := (15785584893419417183/15790000000000000000 : ℝ)) (alpha := (990533112201/631600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15785584893419417183/15790000000000000000 : ℝ)*(X 0 2+X 1 2)+(990533112201/631600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (2453/25000 : ℝ)) (hi := (504/3125 : ℝ)) (c := (15785584893419417183/15790000000000000000 : ℝ)) (alpha := (990533112201/631600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1023671899/5000000000 : ℝ)*X 0 0+(5427945371/10000000000 : ℝ)*X 0 1+(5230689749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352904043/10000000000 : ℝ)*X 1 0+(-429634299/2000000000 : ℝ)*X 1 1+(1307672457/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334556489/625000000 : ℝ)*X 2 0+(2615345041/5000000000 : ℝ)*X 2 1+(-42963429/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081772143/2500000000 : ℝ)*X 0 0+(1031392419/2500000000 : ℝ)*X 0 1+(1134450777/2500000000 : ℝ)*X 0 2+(1081772143/2500000000 : ℝ)*X 1 0+(1031392419/2500000000 : ℝ)*X 1 1+(1134450777/2500000000 : ℝ)*X 1 2+(1081772143/2500000000 : ℝ)*X 2 0+(1031392419/2500000000 : ℝ)*X 2 1+(1134450777/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2047363471/10000000000 : ℝ)*X 0 0+(5231514769/10000000000 : ℝ)*X 0 1+(2713557657/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325532211/2500000000 : ℝ)*X 1 0+(-48793657/250000000 : ℝ)*X 1 1+(5427115541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302130521/10000000000 : ℝ)*X 2 0+(5427114381/10000000000 : ℝ)*X 2 1+(-390349117/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4327130269/10000000000 : ℝ)*X 0 0+(4536078979/10000000000 : ℝ)*X 0 1+(16122279/39062500 : ℝ)*X 0 2+(4327130269/10000000000 : ℝ)*X 1 0+(4536078979/10000000000 : ℝ)*X 1 1+(16122279/39062500 : ℝ)*X 1 2+(4327130269/10000000000 : ℝ)*X 2 0+(4536078979/10000000000 : ℝ)*X 2 1+(16122279/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1955108214566367785774478801/197375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1773311251/100000000000000 : ℝ)*(base19) + (1542031541/100000000000000 : ℝ)*(base23) + (28182743/12500000000000 : ℝ)*(upper3) + (12776897/100000000000000 : ℝ)*(upper4) + (108948601/50000000000000 : ℝ)*(upper5) + (1873868521989649/50000000000000 : ℝ)*(major0) + (1873868521989649/50000000000000 : ℝ)*(major1) + (1873868521989649/50000000000000 : ℝ)*(major2) + (2534799327308029/50000000000000 : ℝ)*(sp0) + (2534815249444329/50000000000000 : ℝ)*(sp1) + (5069630730168369/100000000000000 : ℝ)*(sp2) + (1212912966965531/50000000000000 : ℝ)*(sp3) + (33617583851/100000000000000 : ℝ)*(sp4) + (15551642569/100000000000000 : ℝ)*(sp7) + (2425841485573631/100000000000000 : ℝ)*(f.failure) + (506963227219991/10000000000000 : ℝ)*(f.sum) + (95082402934351/15790000000000000000000000000 : ℝ)*base66 + (2426478356274963767/789500000000000000000000000000000 : ℝ)*base67 + (5624751620691036233/789500000000000000000000000000000 : ℝ)*base70 + (2842007453275536233/789500000000000000000000000000000 : ℝ)*base72 + (22406252702579/15790000000000000000000000000 : ℝ)*base73 + (1797719189827036233/789500000000000000000000000000000 : ℝ)*base76 + (2975353025874536233/789500000000000000000000000000000 : ℝ)*base78 + (14557761440654536233/789500000000000000000000000000000 : ℝ)*base80 + (55763763125131/15790000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2839061/1250000000000000000000 : ℝ)*base89 + (2839061/1250000000000000000000 : ℝ)*base91 + (2839061/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55525098382052766567257883/197375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53010031/12500000000000 : ℝ)*(base19) + (2455554799/100000000000000 : ℝ)*(base23) + (110430437/50000000000000 : ℝ)*(upper3) + (31801929/50000000000000 : ℝ)*(lower4) + (2181189/3125000000000 : ℝ)*(upper5) + (1889700933571533/50000000000000 : ℝ)*(major0) + (1889700933571533/50000000000000 : ℝ)*(major1) + (1889700933571533/50000000000000 : ℝ)*(major2) + (181481551/4000000000000 : ℝ)*(sp1) + (35291550951/100000000000000 : ℝ)*(sp2) + (5112466179776457/100000000000000 : ℝ)*(sp4) + (2556230609328717/50000000000000 : ℝ)*(sp5) + (2556214216335353/50000000000000 : ℝ)*(sp6) + (611584386283101/25000000000000 : ℝ)*(sp7) + (611584386283101/25000000000000 : ℝ)*(f.failure) + (5112466179776457/100000000000000 : ℝ)*(f.sum) + (84498439940223/15790000000000000000000000000 : ℝ)*base65 + (3501968320617676539/789500000000000000000000000000000 : ℝ)*base67 + (4910290385490176539/789500000000000000000000000000000 : ℝ)*base69 + (279658793628323461/789500000000000000000000000000000 : ℝ)*base72 + (115540996626043/15790000000000000000000000000 : ℝ)*base73 + (19145528038648176539/789500000000000000000000000000000 : ℝ)*base75 + (7131961281876176539/789500000000000000000000000000000 : ℝ)*base77 + (17200268966735176539/789500000000000000000000000000000 : ℝ)*base79 + (17294069758693/15790000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1512369/312500000000000000000 : ℝ)*base90 + (1512369/312500000000000000000 : ℝ)*base92 + (1512369/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1336_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (504/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2453/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10841/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3003/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1336_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1336_s4_0 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-409770919/2000000000 : ℝ)*x 0 + (676960811/1250000000 : ℝ)*x 1 + (5241956703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409770919/2000000000 : ℝ)^537 ≤ (6237531409233/50000000000000 : ℝ)^409 := by
    have hnat : (409770919 : ℕ)^537*50000000000000^409 ≤ 6237531409233^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409770919 2000000000 6237531409233 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676960811/1250000000 : ℝ)^537 ≤ (139684480791/312500000000 : ℝ)^409 := by
    have hnat : (676960811 : ℕ)^537*312500000000^409 ≤ 139684480791^409*1250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676960811 1250000000 139684480791 312500000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241956703/10000000000 : ℝ)^537 ≤ (42825903307063/100000000000000 : ℝ)^409 := by
    have hnat : (5241956703 : ℕ)^537*100000000000000^409 ≤ 42825903307063^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241956703 10000000000 42825903307063 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-409770919/2000000000 : ℝ), (676960811/1250000000 : ℝ), (5241956703/10000000000 : ℝ)] ![(6237531409233/50000000000000 : ℝ), (139684480791/312500000000 : ℝ), (42825903307063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-409770919/2000000000 : ℝ)|^537 ≤ (6237531409233/50000000000000 : ℝ)^409
        have hw : |(-409770919/2000000000 : ℝ)|=(409770919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676960811/1250000000 : ℝ)|^537 ≤ (139684480791/312500000000 : ℝ)^409
        have hw : |(676960811/1250000000 : ℝ)|=(676960811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241956703/10000000000 : ℝ)|^537 ≤ (42825903307063/100000000000000 : ℝ)^409
        have hw : |(5241956703/10000000000 : ℝ)|=(5241956703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s4_1 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5349782387/10000000000 : ℝ)*x 0 + (-534356667/2500000000 : ℝ)*x 1 + (1310489137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349782387/10000000000 : ℝ)^537 ≤ (21993108515717/50000000000000 : ℝ)^409 := by
    have hnat : (5349782387 : ℕ)^537*50000000000000^409 ≤ 21993108515717^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349782387 10000000000 21993108515717 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534356667/2500000000 : ℝ)^537 ≤ (13187881301113/100000000000000 : ℝ)^409 := by
    have hnat : (534356667 : ℕ)^537*100000000000000^409 ≤ 13187881301113^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534356667 2500000000 13187881301113 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310489137/2500000000 : ℝ)^537 ≤ (2676618852777/6250000000000 : ℝ)^409 := by
    have hnat : (1310489137 : ℕ)^537*6250000000000^409 ≤ 2676618852777^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310489137 2500000000 2676618852777 6250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349782387/10000000000 : ℝ), (-534356667/2500000000 : ℝ), (1310489137/2500000000 : ℝ)] ![(21993108515717/50000000000000 : ℝ), (13187881301113/100000000000000 : ℝ), (2676618852777/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349782387/10000000000 : ℝ)|^537 ≤ (21993108515717/50000000000000 : ℝ)^409
        have hw : |(5349782387/10000000000 : ℝ)|=(5349782387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534356667/2500000000 : ℝ)|^537 ≤ (13187881301113/100000000000000 : ℝ)^409
        have hw : |(-534356667/2500000000 : ℝ)|=(534356667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310489137/2500000000 : ℝ)|^537 ≤ (2676618852777/6250000000000 : ℝ)^409
        have hw : |(1310489137/2500000000 : ℝ)|=(1310489137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s4_2 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5349782599/10000000000 : ℝ)*x 0 + (5241956247/10000000000 : ℝ)*x 1 + (-427485357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349782599/10000000000 : ℝ)^537 ≤ (43986219320021/100000000000000 : ℝ)^409 := by
    have hnat : (5349782599 : ℕ)^537*100000000000000^409 ≤ 43986219320021^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349782599 10000000000 43986219320021 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241956247/10000000000 : ℝ)^537 ≤ (42825898415711/100000000000000 : ℝ)^409 := by
    have hnat : (5241956247 : ℕ)^537*100000000000000^409 ≤ 42825898415711^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241956247 10000000000 42825898415711 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427485357/2000000000 : ℝ)^537 ≤ (6593941124461/50000000000000 : ℝ)^409 := by
    have hnat : (427485357 : ℕ)^537*50000000000000^409 ≤ 6593941124461^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427485357 2000000000 6593941124461 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349782599/10000000000 : ℝ), (5241956247/10000000000 : ℝ), (-427485357/2000000000 : ℝ)] ![(43986219320021/100000000000000 : ℝ), (42825898415711/100000000000000 : ℝ), (6593941124461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349782599/10000000000 : ℝ)|^537 ≤ (43986219320021/100000000000000 : ℝ)^409
        have hw : |(5349782599/10000000000 : ℝ)|=(5349782599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241956247/10000000000 : ℝ)|^537 ≤ (42825898415711/100000000000000 : ℝ)^409
        have hw : |(5241956247/10000000000 : ℝ)|=(5241956247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427485357/2000000000 : ℝ)|^537 ≤ (6593941124461/50000000000000 : ℝ)^409
        have hw : |(-427485357/2000000000 : ℝ)|=(427485357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s4_3 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1082001357/2500000000 : ℝ)*x 0 + (4150037881/10000000000 : ℝ)*x 1 + (282069189/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082001357/2500000000 : ℝ)^537 ≤ (16650642606981/50000000000000 : ℝ)^409 := by
    have hnat : (1082001357 : ℕ)^537*50000000000000^409 ≤ 16650642606981^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082001357 2500000000 16650642606981 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4150037881/10000000000 : ℝ)^537 ≤ (7878766692077/25000000000000 : ℝ)^409 := by
    have hnat : (4150037881 : ℕ)^537*25000000000000^409 ≤ 7878766692077^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150037881 10000000000 7878766692077 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282069189/625000000 : ℝ)^537 ≤ (35183648005727/100000000000000 : ℝ)^409 := by
    have hnat : (282069189 : ℕ)^537*100000000000000^409 ≤ 35183648005727^409*625000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282069189 625000000 35183648005727 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082001357/2500000000 : ℝ), (4150037881/10000000000 : ℝ), (282069189/625000000 : ℝ)] ![(16650642606981/50000000000000 : ℝ), (7878766692077/25000000000000 : ℝ), (35183648005727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082001357/2500000000 : ℝ)|^537 ≤ (16650642606981/50000000000000 : ℝ)^409
        have hw : |(1082001357/2500000000 : ℝ)|=(1082001357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4150037881/10000000000 : ℝ)|^537 ≤ (7878766692077/25000000000000 : ℝ)^409
        have hw : |(4150037881/10000000000 : ℝ)|=(4150037881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282069189/625000000 : ℝ)|^537 ≤ (35183648005727/100000000000000 : ℝ)^409
        have hw : |(282069189/625000000 : ℝ)|=(282069189/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s4_4 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-256108537/1250000000 : ℝ)*x 0 + (5242597129/10000000000 : ℝ)*x 1 + (5415042433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256108537/1250000000 : ℝ)^537 ≤ (499006893961/4000000000000 : ℝ)^409 := by
    have hnat : (256108537 : ℕ)^537*4000000000000^409 ≤ 499006893961^409*1250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256108537 1250000000 499006893961 4000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242597129/10000000000 : ℝ)^537 ≤ (42832773063469/100000000000000 : ℝ)^409 := by
    have hnat : (5242597129 : ℕ)^537*100000000000000^409 ≤ 42832773063469^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242597129 10000000000 42832773063469 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415042433/10000000000 : ℝ)^537 ≤ (44692054575521/100000000000000 : ℝ)^409 := by
    have hnat : (5415042433 : ℕ)^537*100000000000000^409 ≤ 44692054575521^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415042433 10000000000 44692054575521 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256108537/1250000000 : ℝ), (5242597129/10000000000 : ℝ), (5415042433/10000000000 : ℝ)] ![(499006893961/4000000000000 : ℝ), (42832773063469/100000000000000 : ℝ), (44692054575521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256108537/1250000000 : ℝ)|^537 ≤ (499006893961/4000000000000 : ℝ)^409
        have hw : |(-256108537/1250000000 : ℝ)|=(256108537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242597129/10000000000 : ℝ)|^537 ≤ (42832773063469/100000000000000 : ℝ)^409
        have hw : |(5242597129/10000000000 : ℝ)|=(5242597129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415042433/10000000000 : ℝ)|^537 ≤ (44692054575521/100000000000000 : ℝ)^409
        have hw : |(5415042433/10000000000 : ℝ)|=(5415042433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s4_5 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (265253227/500000000 : ℝ)*x 0 + (-1964340409/10000000000 : ℝ)*x 1 + (2707521403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265253227/500000000 : ℝ)^537 ≤ (21752055343869/50000000000000 : ℝ)^409 := by
    have hnat : (265253227 : ℕ)^537*50000000000000^409 ≤ 21752055343869^409*500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265253227 500000000 21752055343869 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1964340409/10000000000 : ℝ)^537 ≤ (11803830676539/100000000000000 : ℝ)^409 := by
    have hnat : (1964340409 : ℕ)^537*100000000000000^409 ≤ 11803830676539^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964340409 10000000000 11803830676539 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707521403/5000000000 : ℝ)^537 ≤ (22346029308723/50000000000000 : ℝ)^409 := by
    have hnat : (2707521403 : ℕ)^537*50000000000000^409 ≤ 22346029308723^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707521403 5000000000 22346029308723 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265253227/500000000 : ℝ), (-1964340409/10000000000 : ℝ), (2707521403/5000000000 : ℝ)] ![(21752055343869/50000000000000 : ℝ), (11803830676539/100000000000000 : ℝ), (22346029308723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265253227/500000000 : ℝ)|^537 ≤ (21752055343869/50000000000000 : ℝ)^409
        have hw : |(265253227/500000000 : ℝ)|=(265253227/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1964340409/10000000000 : ℝ)|^537 ≤ (11803830676539/100000000000000 : ℝ)^409
        have hw : |(-1964340409/10000000000 : ℝ)|=(1964340409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707521403/5000000000 : ℝ)|^537 ≤ (22346029308723/50000000000000 : ℝ)^409
        have hw : |(2707521403/5000000000 : ℝ)|=(2707521403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s4_6 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652532139/5000000000 : ℝ)*x 0 + (5415042829/10000000000 : ℝ)*x 1 + (-392868147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652532139/5000000000 : ℝ)^537 ≤ (4350410786681/10000000000000 : ℝ)^409 := by
    have hnat : (2652532139 : ℕ)^537*10000000000000^409 ≤ 4350410786681^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652532139 5000000000 4350410786681 10000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415042829/10000000000 : ℝ)^537 ≤ (1117301471667/2500000000000 : ℝ)^409 := by
    have hnat : (5415042829 : ℕ)^537*2500000000000^409 ≤ 1117301471667^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415042829 10000000000 1117301471667 2500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (392868147/2000000000 : ℝ)^537 ≤ (5901916624281/50000000000000 : ℝ)^409 := by
    have hnat : (392868147 : ℕ)^537*50000000000000^409 ≤ 5901916624281^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392868147 2000000000 5901916624281 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652532139/5000000000 : ℝ), (5415042829/10000000000 : ℝ), (-392868147/2000000000 : ℝ)] ![(4350410786681/10000000000000 : ℝ), (1117301471667/2500000000000 : ℝ), (5901916624281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652532139/5000000000 : ℝ)|^537 ≤ (4350410786681/10000000000000 : ℝ)^409
        have hw : |(2652532139/5000000000 : ℝ)|=(2652532139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415042829/10000000000 : ℝ)|^537 ≤ (1117301471667/2500000000000 : ℝ)^409
        have hw : |(5415042829/10000000000 : ℝ)|=(5415042829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-392868147/2000000000 : ℝ)|^537 ≤ (5901916624281/50000000000000 : ℝ)^409
        have hw : |(-392868147/2000000000 : ℝ)|=(392868147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s4_7 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2164016581/5000000000 : ℝ)*x 0 + (281985523/625000000 : ℝ)*x 1 + (830276781/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164016581/5000000000 : ℝ)^537 ≤ (8325391348489/25000000000000 : ℝ)^409 := by
    have hnat : (2164016581 : ℕ)^537*25000000000000^409 ≤ 8325391348489^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164016581 5000000000 8325391348489 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281985523/625000000 : ℝ)^537 ≤ (17584973301339/50000000000000 : ℝ)^409 := by
    have hnat : (281985523 : ℕ)^537*50000000000000^409 ≤ 17584973301339^409*625000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281985523 625000000 17584973301339 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830276781/2000000000 : ℝ)^537 ≤ (31528487988181/100000000000000 : ℝ)^409 := by
    have hnat : (830276781 : ℕ)^537*100000000000000^409 ≤ 31528487988181^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830276781 2000000000 31528487988181 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2164016581/5000000000 : ℝ), (281985523/625000000 : ℝ), (830276781/2000000000 : ℝ)] ![(8325391348489/25000000000000 : ℝ), (17584973301339/50000000000000 : ℝ), (31528487988181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2164016581/5000000000 : ℝ)|^537 ≤ (8325391348489/25000000000000 : ℝ)^409
        have hw : |(2164016581/5000000000 : ℝ)|=(2164016581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281985523/625000000 : ℝ)|^537 ≤ (17584973301339/50000000000000 : ℝ)^409
        have hw : |(281985523/625000000 : ℝ)|=(281985523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830276781/2000000000 : ℝ)|^537 ≤ (31528487988181/100000000000000 : ℝ)^409
        have hw : |(830276781/2000000000 : ℝ)|=(830276781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1336_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3003/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10841/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5541/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14759/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3003/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10841/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3003/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10841/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3003/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10841/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3003/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10841/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3003/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10841/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3003/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10841/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (10841/100000 : ℝ) ^ (4295/1024 : ℝ) ≤ (4484630626061521/50000000000000000000 : ℝ) := by
    have hpowers : (10841/100000 : ℝ)^4295 ≤ (4484630626061521/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10841 : ℕ)^4295*50000000000000000000^1024 ≤ 4484630626061521^1024*100000^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10841 100000 4484630626061521 50000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10841/100000 : ℝ)) (X := (4484630626061521/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3003/20000 : ℝ) ^ (4295/1024 : ℝ) ≤ (35161761629168199/100000000000000000000 : ℝ) := by
    have hpowers : (3003/20000 : ℝ)^4295 ≤ (35161761629168199/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3003 : ℕ)^4295*100000000000000000000^1024 ≤ 35161761629168199^1024*20000^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3003 20000 35161761629168199 100000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3003/20000 : ℝ)) (X := (35161761629168199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004484630626061521/25000000000000000000 : ℝ) ≤ (2000085531047341/2000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (25004484630626061521/25000000000000000000 : ℝ)^1024 ≤ (2000085531047341/2000000000000000 : ℝ)^4295 := by
      have hnat : (25004484630626061521 : ℕ)^1024*2000000000000000^4295 ≤ 2000085531047341^4295*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004484630626061521 25000000000000000000 2000085531047341 2000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000085531047341/2000000000000000 : ℝ)) (X := (25004484630626061521/25000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044131022881291241/100000000000000000000 : ℝ) ≤ (10001051980798953/10000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (100044131022881291241/100000000000000000000 : ℝ)^1024 ≤ (10001051980798953/10000000000000000 : ℝ)^4295 := by
      have hnat : (100044131022881291241 : ℕ)^1024*10000000000000000^4295 ≤ 10001051980798953^4295*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044131022881291241 100000000000000000000 10001051980798953 10000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001051980798953/10000000000000000 : ℝ)) (X := (100044131022881291241/100000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035161761629168199/50000000000000000000 : ℝ) ≤ (10001676306361201/10000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (50035161761629168199/50000000000000000000 : ℝ)^1024 ≤ (10001676306361201/10000000000000000 : ℝ)^4295 := by
      have hnat : (50035161761629168199 : ℕ)^1024*10000000000000000^4295 ≤ 10001676306361201^4295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035161761629168199 50000000000000000000 10001676306361201 10000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001676306361201/10000000000000000 : ℝ)) (X := (50035161761629168199/50000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4484630626061521/50000000000000000000 : ℝ) ≤ ((20864124203058672767/20870000000000000000 : ℝ)+2*(78040695281/52175000000000 : ℝ)*(10841/100000 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (20864124203058672767/20870000000000000000 : ℝ)+2*(78040695281/52175000000000 : ℝ)*(10841/100000 : ℝ)=(2000085531047341/2000000000000000 : ℝ) by norm_num, show 1+2*(4484630626061521/50000000000000000000 : ℝ)=(25004484630626061521/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35161761629168199/100000000000000000000 : ℝ)+(4484630626061521/50000000000000000000 : ℝ) ≤ ((20864124203058672767/20870000000000000000 : ℝ)+(78040695281/52175000000000 : ℝ)*((3003/20000 : ℝ)+(10841/100000 : ℝ)))^(4295/1024 : ℝ) := by
    rw [show (20864124203058672767/20870000000000000000 : ℝ)+(78040695281/52175000000000 : ℝ)*((3003/20000 : ℝ)+(10841/100000 : ℝ))=(10001051980798953/10000000000000000 : ℝ) by norm_num, show 1+(35161761629168199/100000000000000000000 : ℝ)+(4484630626061521/50000000000000000000 : ℝ)=(100044131022881291241/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35161761629168199/100000000000000000000 : ℝ) ≤ ((20864124203058672767/20870000000000000000 : ℝ)+2*(78040695281/52175000000000 : ℝ)*(3003/20000 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (20864124203058672767/20870000000000000000 : ℝ)+2*(78040695281/52175000000000 : ℝ)*(3003/20000 : ℝ)=(10001676306361201/10000000000000000 : ℝ) by norm_num, show 1+2*(35161761629168199/100000000000000000000 : ℝ)=(50035161761629168199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20864124203058672767/20870000000000000000 : ℝ)*(X 1 0+X 2 0)+(78040695281/52175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (10841/100000 : ℝ)) (hi := (3003/20000 : ℝ)) (c := (20864124203058672767/20870000000000000000 : ℝ)) (alpha := (78040695281/52175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20864124203058672767/20870000000000000000 : ℝ)*(X 0 1+X 2 1)+(78040695281/52175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (10841/100000 : ℝ)) (hi := (3003/20000 : ℝ)) (c := (20864124203058672767/20870000000000000000 : ℝ)) (alpha := (78040695281/52175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20864124203058672767/20870000000000000000 : ℝ)*(X 0 2+X 1 2)+(78040695281/52175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (10841/100000 : ℝ)) (hi := (3003/20000 : ℝ)) (c := (20864124203058672767/20870000000000000000 : ℝ)) (alpha := (78040695281/52175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-409770919/2000000000 : ℝ)*X 0 0+(676960811/1250000000 : ℝ)*X 0 1+(5241956703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349782387/10000000000 : ℝ)*X 1 0+(-534356667/2500000000 : ℝ)*X 1 1+(1310489137/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349782599/10000000000 : ℝ)*X 2 0+(5241956247/10000000000 : ℝ)*X 2 1+(-427485357/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1082001357/2500000000 : ℝ)*X 0 0+(4150037881/10000000000 : ℝ)*X 0 1+(282069189/625000000 : ℝ)*X 0 2+(1082001357/2500000000 : ℝ)*X 1 0+(4150037881/10000000000 : ℝ)*X 1 1+(282069189/625000000 : ℝ)*X 1 2+(1082001357/2500000000 : ℝ)*X 2 0+(4150037881/10000000000 : ℝ)*X 2 1+(282069189/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-256108537/1250000000 : ℝ)*X 0 0+(5242597129/10000000000 : ℝ)*X 0 1+(5415042433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265253227/500000000 : ℝ)*X 1 0+(-1964340409/10000000000 : ℝ)*X 1 1+(2707521403/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652532139/5000000000 : ℝ)*X 2 0+(5415042829/10000000000 : ℝ)*X 2 1+(-392868147/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2164016581/5000000000 : ℝ)*X 0 0+(281985523/625000000 : ℝ)*X 0 1+(830276781/2000000000 : ℝ)*X 0 2+(2164016581/5000000000 : ℝ)*X 1 0+(281985523/625000000 : ℝ)*X 1 1+(830276781/2000000000 : ℝ)*X 1 2+(2164016581/5000000000 : ℝ)*X 2 0+(281985523/625000000 : ℝ)*X 2 1+(830276781/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2796296693599939090457776419/521750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113558747/10000000000000 : ℝ)*(base19) + (1287152443/100000000000000 : ℝ)*(base23) + (64766961/50000000000000 : ℝ)*(lower2) + (9682221/6250000000000 : ℝ)*(upper3) + (88588537/100000000000000 : ℝ)*(lower4) + (4255211606312479/100000000000000 : ℝ)*(major0) + (4255211606312479/100000000000000 : ℝ)*(major1) + (26595072539453/625000000000 : ℝ)*(major2) + (2878042727635851/50000000000000 : ℝ)*(sp0) + (57561014315701/1000000000000 : ℝ)*(sp1) + (5756101280005127/100000000000000 : ℝ)*(sp2) + (1377153342099647/50000000000000 : ℝ)*(sp3) + (17111885869/100000000000000 : ℝ)*(sp4) + (21535343/156250000000 : ℝ)*(sp7) + (1377160233409407/50000000000000 : ℝ)*(f.failure) + (5756102567157571/100000000000000 : ℝ)*(f.sum) + (4423946559557/2608750000000000000000000000 : ℝ)*base65 + (28141173222875440607/2087000000000000000000000000000000 : ℝ)*base68 + (59747373698032299/13043750000000000000000000000000 : ℝ)*base70 + (9357936809602440607/2087000000000000000000000000000000 : ℝ)*base72 + (1179281356817/2608750000000000000000000000 : ℝ)*base73 + (129437743163526049/13043750000000000000000000000000 : ℝ)*base76 + (5882067238165840607/2087000000000000000000000000000000 : ℝ)*base78 + (3513327660191840607/2087000000000000000000000000000000 : ℝ)*base80 + (1122008353361/10435000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5222117/625000000000000000000 : ℝ)*base89 + (5222117/625000000000000000000 : ℝ)*base91 + (1027883/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4054905616517191171486616301/1043500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (777694213/100000000000000 : ℝ)*(base19) + (251920013/50000000000000 : ℝ)*(base23) + (40051839/100000000000000 : ℝ)*(upper2) + (159534371/100000000000000 : ℝ)*(upper3) + (9730299/25000000000000 : ℝ)*(upper5) + (4286873457932667/100000000000000 : ℝ)*(major0) + (4286873457932667/100000000000000 : ℝ)*(major1) + (4286873457932667/100000000000000 : ℝ)*(major2) + (23880305219/100000000000000 : ℝ)*(sp1) + (1641079969/10000000000000 : ℝ)*(sp2) + (1159786436676883/20000000000000 : ℝ)*(sp4) + (5798907525384983/100000000000000 : ℝ)*(sp5) + (5798915268744699/100000000000000 : ℝ)*(sp6) + (1387407301475951/50000000000000 : ℝ)*(sp7) + (1387407301475951/50000000000000 : ℝ)*(f.failure) + (1159786436676883/20000000000000 : ℝ)*(f.sum) + (3104760189427/652187500000000000000000000 : ℝ)*base66 + (18207005816533620411/2087000000000000000000000000000000 : ℝ)*base68 + (14653760036991620411/2087000000000000000000000000000000 : ℝ)*base70 + (23972915626195620411/2087000000000000000000000000000000 : ℝ)*base72 + (63629952646987/10435000000000000000000000000 : ℝ)*base74 + (16269775508496620411/2087000000000000000000000000000000 : ℝ)*base76 + (23662320061328620411/2087000000000000000000000000000000 : ℝ)*base78 + (34549326864375620411/2087000000000000000000000000000000 : ℝ)*base80 + (19855642071617/10435000000000000000000000000 : ℝ)*base82 + (4740981/625000000000000000000 : ℝ)*base89 + (4740981/625000000000000000000 : ℝ)*base91 + (4740981/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1336_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3003/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10841/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5541/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1336_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1336_s5_0 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1024558399/5000000000 : ℝ)*x 0 + (5413423219/10000000000 : ℝ)*x 1 + (5244047487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024558399/5000000000 : ℝ)^537 ≤ (779822437513/6250000000000 : ℝ)^409 := by
    have hnat : (1024558399 : ℕ)^537*6250000000000^409 ≤ 779822437513^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024558399 5000000000 779822437513 6250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413423219/10000000000 : ℝ)^537 ≤ (44674509171981/100000000000000 : ℝ)^409 := by
    have hnat : (5413423219 : ℕ)^537*100000000000000^409 ≤ 44674509171981^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413423219 10000000000 44674509171981 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244047487/10000000000 : ℝ)^537 ≤ (42848331813317/100000000000000 : ℝ)^409 := by
    have hnat : (5244047487 : ℕ)^537*100000000000000^409 ≤ 42848331813317^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244047487 10000000000 42848331813317 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1024558399/5000000000 : ℝ), (5413423219/10000000000 : ℝ), (5244047487/10000000000 : ℝ)] ![(779822437513/6250000000000 : ℝ), (44674509171981/100000000000000 : ℝ), (42848331813317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1024558399/5000000000 : ℝ)|^537 ≤ (779822437513/6250000000000 : ℝ)^409
        have hw : |(-1024558399/5000000000 : ℝ)|=(1024558399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413423219/10000000000 : ℝ)|^537 ≤ (44674509171981/100000000000000 : ℝ)^409
        have hw : |(5413423219/10000000000 : ℝ)|=(5413423219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244047487/10000000000 : ℝ)|^537 ≤ (42848331813317/100000000000000 : ℝ)^409
        have hw : |(5244047487/10000000000 : ℝ)|=(5244047487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s5_1 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1337301237/2500000000 : ℝ)*x 0 + (-2135426797/10000000000 : ℝ)*x 1 + (5244047651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337301237/2500000000 : ℝ)^537 ≤ (21989991778009/50000000000000 : ℝ)^409 := by
    have hnat : (1337301237 : ℕ)^537*50000000000000^409 ≤ 21989991778009^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337301237 2500000000 21989991778009 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2135426797/10000000000 : ℝ)^537 ≤ (13171682862159/100000000000000 : ℝ)^409 := by
    have hnat : (2135426797 : ℕ)^537*100000000000000^409 ≤ 13171682862159^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135426797 10000000000 13171682862159 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244047651/10000000000 : ℝ)^537 ≤ (42848333572707/100000000000000 : ℝ)^409 := by
    have hnat : (5244047651 : ℕ)^537*100000000000000^409 ≤ 42848333572707^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244047651 10000000000 42848333572707 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337301237/2500000000 : ℝ), (-2135426797/10000000000 : ℝ), (5244047651/10000000000 : ℝ)] ![(21989991778009/50000000000000 : ℝ), (13171682862159/100000000000000 : ℝ), (42848333572707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337301237/2500000000 : ℝ)|^537 ≤ (21989991778009/50000000000000 : ℝ)^409
        have hw : |(1337301237/2500000000 : ℝ)|=(1337301237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2135426797/10000000000 : ℝ)|^537 ≤ (13171682862159/100000000000000 : ℝ)^409
        have hw : |(-2135426797/10000000000 : ℝ)|=(2135426797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244047651/10000000000 : ℝ)|^537 ≤ (42848333572707/100000000000000 : ℝ)^409
        have hw : |(5244047651/10000000000 : ℝ)|=(5244047651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s5_2 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5349204479/10000000000 : ℝ)*x 0 + (1048809569/2000000000 : ℝ)*x 1 + (-533856791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349204479/10000000000 : ℝ)^537 ≤ (43979978493231/100000000000000 : ℝ)^409 := by
    have hnat : (5349204479 : ℕ)^537*100000000000000^409 ≤ 43979978493231^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349204479 10000000000 43979978493231 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048809569/2000000000 : ℝ)^537 ≤ (42848335653937/100000000000000 : ℝ)^409 := by
    have hnat : (1048809569 : ℕ)^537*100000000000000^409 ≤ 42848335653937^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048809569 2000000000 42848335653937 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533856791/2500000000 : ℝ)^537 ≤ (13171685834329/100000000000000 : ℝ)^409 := by
    have hnat : (533856791 : ℕ)^537*100000000000000^409 ≤ 13171685834329^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533856791 2500000000 13171685834329 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349204479/10000000000 : ℝ), (1048809569/2000000000 : ℝ), (-533856791/2500000000 : ℝ)] ![(43979978493231/100000000000000 : ℝ), (42848335653937/100000000000000 : ℝ), (13171685834329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349204479/10000000000 : ℝ)|^537 ≤ (43979978493231/100000000000000 : ℝ)^409
        have hw : |(5349204479/10000000000 : ℝ)|=(5349204479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048809569/2000000000 : ℝ)|^537 ≤ (42848335653937/100000000000000 : ℝ)^409
        have hw : |(1048809569/2000000000 : ℝ)|=(1048809569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-533856791/2500000000 : ℝ)|^537 ≤ (13171685834329/100000000000000 : ℝ)^409
        have hw : |(-533856791/2500000000 : ℝ)|=(533856791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s5_3 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (216408089/500000000 : ℝ)*x 0 + (4154568937/10000000000 : ℝ)*x 1 + (2254268777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216408089/500000000 : ℝ)^537 ≤ (33302864751937/100000000000000 : ℝ)^409 := by
    have hnat : (216408089 : ℕ)^537*100000000000000^409 ≤ 33302864751937^409*500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216408089 500000000 33302864751937 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4154568937/10000000000 : ℝ)^537 ≤ (31560251400407/100000000000000 : ℝ)^409 := by
    have hnat : (4154568937 : ℕ)^537*100000000000000^409 ≤ 31560251400407^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154568937 10000000000 31560251400407 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254268777/5000000000 : ℝ)^537 ≤ (35136883837459/100000000000000 : ℝ)^409 := by
    have hnat : (2254268777 : ℕ)^537*100000000000000^409 ≤ 35136883837459^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254268777 5000000000 35136883837459 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216408089/500000000 : ℝ), (4154568937/10000000000 : ℝ), (2254268777/5000000000 : ℝ)] ![(33302864751937/100000000000000 : ℝ), (31560251400407/100000000000000 : ℝ), (35136883837459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216408089/500000000 : ℝ)|^537 ≤ (33302864751937/100000000000000 : ℝ)^409
        have hw : |(216408089/500000000 : ℝ)|=(216408089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4154568937/10000000000 : ℝ)|^537 ≤ (31560251400407/100000000000000 : ℝ)^409
        have hw : |(4154568937/10000000000 : ℝ)|=(4154568937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254268777/5000000000 : ℝ)|^537 ≤ (35136883837459/100000000000000 : ℝ)^409
        have hw : |(2254268777/5000000000 : ℝ)|=(2254268777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s5_4 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1024564423/5000000000 : ℝ)*x 0 + (2622328279/5000000000 : ℝ)*x 1 + (2706405633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024564423/5000000000 : ℝ)^537 ≤ (6238627659977/50000000000000 : ℝ)^409 := by
    have hnat : (1024564423 : ℕ)^537*50000000000000^409 ≤ 6238627659977^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024564423 5000000000 6238627659977 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622328279/5000000000 : ℝ)^537 ≤ (21427433019233/50000000000000 : ℝ)^409 := by
    have hnat : (2622328279 : ℕ)^537*50000000000000^409 ≤ 21427433019233^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622328279 5000000000 21427433019233 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706405633/5000000000 : ℝ)^537 ≤ (44667878627823/100000000000000 : ℝ)^409 := by
    have hnat : (2706405633 : ℕ)^537*100000000000000^409 ≤ 44667878627823^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706405633 5000000000 44667878627823 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1024564423/5000000000 : ℝ), (2622328279/5000000000 : ℝ), (2706405633/5000000000 : ℝ)] ![(6238627659977/50000000000000 : ℝ), (21427433019233/50000000000000 : ℝ), (44667878627823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1024564423/5000000000 : ℝ)|^537 ≤ (6238627659977/50000000000000 : ℝ)^409
        have hw : |(-1024564423/5000000000 : ℝ)|=(1024564423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622328279/5000000000 : ℝ)|^537 ≤ (21427433019233/50000000000000 : ℝ)^409
        have hw : |(2622328279/5000000000 : ℝ)|=(2622328279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706405633/5000000000 : ℝ)|^537 ≤ (44667878627823/100000000000000 : ℝ)^409
        have hw : |(2706405633/5000000000 : ℝ)|=(2706405633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s5_5 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (663200989/1250000000 : ℝ)*x 0 + (-1966663207/10000000000 : ℝ)*x 1 + (5412811269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663200989/1250000000 : ℝ)^537 ≤ (21754980606217/50000000000000 : ℝ)^409 := by
    have hnat : (663200989 : ℕ)^537*50000000000000^409 ≤ 21754980606217^409*1250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663200989 1250000000 21754980606217 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1966663207/10000000000 : ℝ)^537 ≤ (5911080053517/50000000000000 : ℝ)^409 := by
    have hnat : (1966663207 : ℕ)^537*50000000000000^409 ≤ 5911080053517^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966663207 10000000000 5911080053517 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412811269/10000000000 : ℝ)^537 ≤ (5583484832541/12500000000000 : ℝ)^409 := by
    have hnat : (5412811269 : ℕ)^537*12500000000000^409 ≤ 5583484832541^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412811269 10000000000 5583484832541 12500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663200989/1250000000 : ℝ), (-1966663207/10000000000 : ℝ), (5412811269/10000000000 : ℝ)] ![(21754980606217/50000000000000 : ℝ), (5911080053517/50000000000000 : ℝ), (5583484832541/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663200989/1250000000 : ℝ)|^537 ≤ (21754980606217/50000000000000 : ℝ)^409
        have hw : |(663200989/1250000000 : ℝ)|=(663200989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1966663207/10000000000 : ℝ)|^537 ≤ (5911080053517/50000000000000 : ℝ)^409
        have hw : |(-1966663207/10000000000 : ℝ)|=(1966663207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412811269/10000000000 : ℝ)|^537 ≤ (5583484832541/12500000000000 : ℝ)^409
        have hw : |(5412811269/10000000000 : ℝ)|=(5412811269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s5_6 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (530560789/1000000000 : ℝ)*x 0 + (541281129/1000000000 : ℝ)*x 1 + (-1966663209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530560789/1000000000 : ℝ)^537 ≤ (8701992195111/20000000000000 : ℝ)^409 := by
    have hnat : (530560789 : ℕ)^537*20000000000000^409 ≤ 8701992195111^409*1000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530560789 1000000000 8701992195111 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541281129/1000000000 : ℝ)^537 ≤ (2233393944393/5000000000000 : ℝ)^409 := by
    have hnat : (541281129 : ℕ)^537*5000000000000^409 ≤ 2233393944393^409*1000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541281129 1000000000 2233393944393 5000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1966663209/10000000000 : ℝ)^537 ≤ (11822160122819/100000000000000 : ℝ)^409 := by
    have hnat : (1966663209 : ℕ)^537*100000000000000^409 ≤ 11822160122819^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966663209 10000000000 11822160122819 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530560789/1000000000 : ℝ), (541281129/1000000000 : ℝ), (-1966663209/10000000000 : ℝ)] ![(8701992195111/20000000000000 : ℝ), (2233393944393/5000000000000 : ℝ), (11822160122819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530560789/1000000000 : ℝ)|^537 ≤ (8701992195111/20000000000000 : ℝ)^409
        have hw : |(530560789/1000000000 : ℝ)|=(530560789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541281129/1000000000 : ℝ)|^537 ≤ (2233393944393/5000000000000 : ℝ)^409
        have hw : |(541281129/1000000000 : ℝ)|=(541281129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1966663209/10000000000 : ℝ)|^537 ≤ (11822160122819/100000000000000 : ℝ)^409
        have hw : |(-1966663209/10000000000 : ℝ)|=(1966663209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s5_7 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4328188069/10000000000 : ℝ)*x 0 + (4507265021/10000000000 : ℝ)*x 1 + (519480963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328188069/10000000000 : ℝ)^537 ≤ (33303130336951/100000000000000 : ℝ)^409 := by
    have hnat : (4328188069 : ℕ)^537*100000000000000^409 ≤ 33303130336951^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328188069 10000000000 33303130336951 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507265021/10000000000 : ℝ)^537 ≤ (35123863315337/100000000000000 : ℝ)^409 := by
    have hnat : (4507265021 : ℕ)^537*100000000000000^409 ≤ 35123863315337^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507265021 10000000000 35123863315337 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519480963/1250000000 : ℝ)^537 ≤ (7893251580533/25000000000000 : ℝ)^409 := by
    have hnat : (519480963 : ℕ)^537*25000000000000^409 ≤ 7893251580533^409*1250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519480963 1250000000 7893251580533 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328188069/10000000000 : ℝ), (4507265021/10000000000 : ℝ), (519480963/1250000000 : ℝ)] ![(33303130336951/100000000000000 : ℝ), (35123863315337/100000000000000 : ℝ), (7893251580533/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328188069/10000000000 : ℝ)|^537 ≤ (33303130336951/100000000000000 : ℝ)^409
        have hw : |(4328188069/10000000000 : ℝ)|=(4328188069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507265021/10000000000 : ℝ)|^537 ≤ (35123863315337/100000000000000 : ℝ)^409
        have hw : |(4507265021/10000000000 : ℝ)|=(4507265021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519480963/1250000000 : ℝ)|^537 ≤ (7893251580533/25000000000000 : ℝ)^409
        have hw : |(519480963/1250000000 : ℝ)|=(519480963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1336_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5541/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11127/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1839/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5541/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5541/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5541/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5541/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5541/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5541/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (5541/50000 : ℝ) ^ (4295/1024 : ℝ) ≤ (9835751663674207/100000000000000000000 : ℝ) := by
    have hpowers : (5541/50000 : ℝ)^4295 ≤ (9835751663674207/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5541 : ℕ)^4295*100000000000000000000^1024 ≤ 9835751663674207^1024*50000^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5541 50000 9835751663674207 100000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5541/50000 : ℝ)) (X := (9835751663674207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14759/100000 : ℝ) ^ (4295/1024 : ℝ) ≤ (4089362818938873/12500000000000000000 : ℝ) := by
    have hpowers : (14759/100000 : ℝ)^4295 ≤ (4089362818938873/12500000000000000000 : ℝ)^1024 := by
      have hnat : (14759 : ℕ)^4295*12500000000000000000^1024 ≤ 4089362818938873^1024*100000^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14759 100000 4089362818938873 12500000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14759/100000 : ℝ)) (X := (4089362818938873/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009835751663674207/50000000000000000000 : ℝ) ≤ (200009379329767/200000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (50009835751663674207/50000000000000000000 : ℝ)^1024 ≤ (200009379329767/200000000000000 : ℝ)^4295 := by
      have hnat : (50009835751663674207 : ℕ)^1024*200000000000000^4295 ≤ 200009379329767^4295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009835751663674207 50000000000000000000 200009379329767 200000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200009379329767/200000000000000 : ℝ)) (X := (50009835751663674207/50000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042550654215185191/100000000000000000000 : ℝ) ≤ (10001014314592763/10000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (100042550654215185191/100000000000000000000 : ℝ)^1024 ≤ (10001014314592763/10000000000000000 : ℝ)^4295 := by
      have hnat : (100042550654215185191 : ℕ)^1024*10000000000000000^4295 ≤ 10001014314592763^4295*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042550654215185191 100000000000000000000 10001014314592763 10000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001014314592763/10000000000000000 : ℝ)) (X := (100042550654215185191/100000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254089362818938873/6250000000000000000 : ℝ) ≤ (1250194957837147/1250000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (6254089362818938873/6250000000000000000 : ℝ)^1024 ≤ (1250194957837147/1250000000000000 : ℝ)^4295 := by
      have hnat : (6254089362818938873 : ℕ)^1024*1250000000000000^4295 ≤ 1250194957837147^4295*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254089362818938873 6250000000000000000 1250194957837147 1250000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250194957837147/1250000000000000 : ℝ)) (X := (6254089362818938873/6250000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9835751663674207/100000000000000000000 : ℝ) ≤ ((18379818647195726609/18385000000000000000 : ℝ)+2*(545348104413/367700000000000 : ℝ)*(5541/50000 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (18379818647195726609/18385000000000000000 : ℝ)+2*(545348104413/367700000000000 : ℝ)*(5541/50000 : ℝ)=(200009379329767/200000000000000 : ℝ) by norm_num, show 1+2*(9835751663674207/100000000000000000000 : ℝ)=(50009835751663674207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4089362818938873/12500000000000000000 : ℝ)+(9835751663674207/100000000000000000000 : ℝ) ≤ ((18379818647195726609/18385000000000000000 : ℝ)+(545348104413/367700000000000 : ℝ)*((14759/100000 : ℝ)+(5541/50000 : ℝ)))^(4295/1024 : ℝ) := by
    rw [show (18379818647195726609/18385000000000000000 : ℝ)+(545348104413/367700000000000 : ℝ)*((14759/100000 : ℝ)+(5541/50000 : ℝ))=(10001014314592763/10000000000000000 : ℝ) by norm_num, show 1+(4089362818938873/12500000000000000000 : ℝ)+(9835751663674207/100000000000000000000 : ℝ)=(100042550654215185191/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4089362818938873/12500000000000000000 : ℝ) ≤ ((18379818647195726609/18385000000000000000 : ℝ)+2*(545348104413/367700000000000 : ℝ)*(14759/100000 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (18379818647195726609/18385000000000000000 : ℝ)+2*(545348104413/367700000000000 : ℝ)*(14759/100000 : ℝ)=(1250194957837147/1250000000000000 : ℝ) by norm_num, show 1+2*(4089362818938873/12500000000000000000 : ℝ)=(6254089362818938873/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18379818647195726609/18385000000000000000 : ℝ)*(X 1 0+X 2 0)+(545348104413/367700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (5541/50000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (18379818647195726609/18385000000000000000 : ℝ)) (alpha := (545348104413/367700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18379818647195726609/18385000000000000000 : ℝ)*(X 0 1+X 2 1)+(545348104413/367700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (5541/50000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (18379818647195726609/18385000000000000000 : ℝ)) (alpha := (545348104413/367700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18379818647195726609/18385000000000000000 : ℝ)*(X 0 2+X 1 2)+(545348104413/367700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (5541/50000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (18379818647195726609/18385000000000000000 : ℝ)) (alpha := (545348104413/367700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1024558399/5000000000 : ℝ)*X 0 0+(5413423219/10000000000 : ℝ)*X 0 1+(5244047487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337301237/2500000000 : ℝ)*X 1 0+(-2135426797/10000000000 : ℝ)*X 1 1+(5244047651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349204479/10000000000 : ℝ)*X 2 0+(1048809569/2000000000 : ℝ)*X 2 1+(-533856791/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((216408089/500000000 : ℝ)*X 0 0+(4154568937/10000000000 : ℝ)*X 0 1+(2254268777/5000000000 : ℝ)*X 0 2+(216408089/500000000 : ℝ)*X 1 0+(4154568937/10000000000 : ℝ)*X 1 1+(2254268777/5000000000 : ℝ)*X 1 2+(216408089/500000000 : ℝ)*X 2 0+(4154568937/10000000000 : ℝ)*X 2 1+(2254268777/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1024564423/5000000000 : ℝ)*X 0 0+(2622328279/5000000000 : ℝ)*X 0 1+(2706405633/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663200989/1250000000 : ℝ)*X 1 0+(-1966663207/10000000000 : ℝ)*X 1 1+(5412811269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530560789/1000000000 : ℝ)*X 2 0+(541281129/1000000000 : ℝ)*X 2 1+(-1966663209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4328188069/10000000000 : ℝ)*X 0 0+(4507265021/10000000000 : ℝ)*X 0 1+(519480963/1250000000 : ℝ)*X 0 2+(4328188069/10000000000 : ℝ)*X 1 0+(4507265021/10000000000 : ℝ)*X 1 1+(519480963/1250000000 : ℝ)*X 1 2+(4328188069/10000000000 : ℝ)*X 2 0+(4507265021/10000000000 : ℝ)*X 2 1+(519480963/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2439388564553652090978368979/919250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (366492987/100000000000000 : ℝ)*(base19) + (265335141/100000000000000 : ℝ)*(base23) + (52994861/20000000000000 : ℝ)*(upper2) + (48036333/20000000000000 : ℝ)*(upper3) + (42185531/100000000000000 : ℝ)*(upper4) + (34098327412539/781250000000 : ℝ)*(major0) + (34098327412539/781250000000 : ℝ)*(major1) + (4364585908804993/100000000000000 : ℝ)*(major2) + (2952026723805203/50000000000000 : ℝ)*(sp0) + (5904054914873517/100000000000000 : ℝ)*(sp1) + (5904055016031363/100000000000000 : ℝ)*(sp2) + (2825112788938669/100000000000000 : ℝ)*(sp3) + (916878049/50000000000000 : ℝ)*(sp4) + (73176981/2000000000000 : ℝ)*(sp7) + (1412558223893859/50000000000000 : ℝ)*(f.failure) + (738006910170813/12500000000000 : ℝ)*(f.sum) + (3960358702873/1470800000000000000000000000 : ℝ)*base65 + (209261424253538617/114906250000000000000000000000000 : ℝ)*base68 + (27391798426509041263/1838500000000000000000000000000000 : ℝ)*base70 + (1565293623070569867/114906250000000000000000000000000 : ℝ)*base72 + (1870947766711/1470800000000000000000000000 : ℝ)*base74 + (8447910563023541263/1838500000000000000000000000000000 : ℝ)*base76 + (84496205795258371/57453125000000000000000000000000 : ℝ)*base78 + (125648136135183873/28726562500000000000000000000000 : ℝ)*base80 + (22364755697747/9192500000000000000000000000 : ℝ)*base82 + (1211871/625000000000000000000 : ℝ)*base90 + (1211871/625000000000000000000 : ℝ)*base92 + (7461871/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6268046895190406701767/919250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1229502549/100000000000000 : ℝ)*(base19) + (128359571/10000000000000 : ℝ)*(base23) + (148992961/100000000000000 : ℝ)*(upper3) + (17470181/50000000000000 : ℝ)*(lower4) + (6856891/5000000000000 : ℝ)*(upper5) + (54953267991523/1250000000000 : ℝ)*(major0) + (54953267991523/1250000000000 : ℝ)*(major1) + (54953267991523/1250000000000 : ℝ)*(major2) + (24696503843/100000000000000 : ℝ)*(sp1) + (26266268151/100000000000000 : ℝ)*(sp2) + (5946903213335381/100000000000000 : ℝ)*(sp4) + (5946877287328989/100000000000000 : ℝ)*(sp5) + (37167972896697/625000000000 : ℝ)*(sp6) + (1422809719009927/50000000000000 : ℝ)*(sp7) + (1422809719009927/50000000000000 : ℝ)*(f.failure) + (5946903213335381/100000000000000 : ℝ)*(f.sum) + (573963752049/229812500000000000000000000 : ℝ)*base65 + (107969764330210507/22981250000000000000000000000000 : ℝ)*base67 + (112259830884226993/22981250000000000000000000000000 : ℝ)*base70 + (98386754842073007/22981250000000000000000000000000 : ℝ)*base71 + (1447555719951/919250000000000000000000000 : ℝ)*base73 + (35341529405326993/22981250000000000000000000000000 : ℝ)*base76 + (6972279495233243/22981250000000000000000000000000 : ℝ)*base78 + (142945691751654257/22981250000000000000000000000000 : ℝ)*base79 + (351080248183/183850000000000000000000000 : ℝ)*base82 + (5431763/625000000000000000000 : ℝ)*base90 + (5431763/625000000000000000000 : ℝ)*base92 + (5431763/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1336_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5541/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11127/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1336_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1336_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (504/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2453/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11127/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1336_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1336_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1336_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (504/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2453/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11127/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1336_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
