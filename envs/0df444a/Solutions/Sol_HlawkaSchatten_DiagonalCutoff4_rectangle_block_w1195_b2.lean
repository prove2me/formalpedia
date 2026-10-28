-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1195_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:01:07.807875+00:00
-- url     : https://prove2.me/submissions/50b47cc8-9557-4473-a854-18c88db9b61b

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
theorem support_rectangle_w1195_s6_0 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141770403/10000000000 : ℝ)*x 0 + (337020301/625000000 : ℝ)*x 1 + (526631547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141770403/10000000000 : ℝ)^2097 ≤ (3254869435517/25000000000000 : ℝ)^1585 := by
    have hnat : (2141770403 : ℕ)^2097*25000000000000^1585 ≤ 3254869435517^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141770403 10000000000 3254869435517 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337020301/625000000 : ℝ)^2097 ≤ (22085238642957/50000000000000 : ℝ)^1585 := by
    have hnat : (337020301 : ℕ)^2097*50000000000000^1585 ≤ 22085238642957^1585*625000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337020301 625000000 22085238642957 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526631547/1000000000 : ℝ)^2097 ≤ (10702511239443/25000000000000 : ℝ)^1585 := by
    have hnat : (526631547 : ℕ)^2097*25000000000000^1585 ≤ 10702511239443^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526631547 1000000000 10702511239443 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141770403/10000000000 : ℝ), (337020301/625000000 : ℝ), (526631547/1000000000 : ℝ)] ![(3254869435517/25000000000000 : ℝ), (22085238642957/50000000000000 : ℝ), (10702511239443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141770403/10000000000 : ℝ)|^2097 ≤ (3254869435517/25000000000000 : ℝ)^1585
        have hw : |(-2141770403/10000000000 : ℝ)|=(2141770403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337020301/625000000 : ℝ)|^2097 ≤ (22085238642957/50000000000000 : ℝ)^1585
        have hw : |(337020301/625000000 : ℝ)|=(337020301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526631547/1000000000 : ℝ)|^2097 ≤ (10702511239443/25000000000000 : ℝ)^1585
        have hw : |(526631547/1000000000 : ℝ)|=(526631547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s6_1 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534460541/1000000000 : ℝ)*x 0 + (-1102837587/5000000000 : ℝ)*x 1 + (5266315541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534460541/1000000000 : ℝ)^2097 ≤ (21827031763893/50000000000000 : ℝ)^1585 := by
    have hnat : (534460541 : ℕ)^2097*50000000000000^1585 ≤ 21827031763893^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534460541 1000000000 21827031763893 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102837587/5000000000 : ℝ)^2097 ≤ (84599317031/625000000000 : ℝ)^1585 := by
    have hnat : (1102837587 : ℕ)^2097*625000000000^1585 ≤ 84599317031^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102837587 5000000000 84599317031 625000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266315541/10000000000 : ℝ)^2097 ≤ (10702511430343/25000000000000 : ℝ)^1585 := by
    have hnat : (5266315541 : ℕ)^2097*25000000000000^1585 ≤ 10702511430343^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266315541 10000000000 10702511430343 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534460541/1000000000 : ℝ), (-1102837587/5000000000 : ℝ), (5266315541/10000000000 : ℝ)] ![(21827031763893/50000000000000 : ℝ), (84599317031/625000000000 : ℝ), (10702511430343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534460541/1000000000 : ℝ)|^2097 ≤ (21827031763893/50000000000000 : ℝ)^1585
        have hw : |(534460541/1000000000 : ℝ)|=(534460541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1102837587/5000000000 : ℝ)|^2097 ≤ (84599317031/625000000000 : ℝ)^1585
        have hw : |(-1102837587/5000000000 : ℝ)|=(1102837587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266315541/10000000000 : ℝ)|^2097 ≤ (10702511430343/25000000000000 : ℝ)^1585
        have hw : |(5266315541/10000000000 : ℝ)|=(5266315541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s6_2 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (213784221/400000000 : ℝ)*x 0 + (2633157647/5000000000 : ℝ)*x 1 + (-2205675349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213784221/400000000 : ℝ)^2097 ≤ (21827032385257/50000000000000 : ℝ)^1585 := by
    have hnat : (213784221 : ℕ)^2097*50000000000000^1585 ≤ 21827032385257^1585*400000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213784221 400000000 21827032385257 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633157647/5000000000 : ℝ)^2097 ≤ (21405021532451/50000000000000 : ℝ)^1585 := by
    have hnat : (2633157647 : ℕ)^2097*50000000000000^1585 ≤ 21405021532451^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633157647 5000000000 21405021532451 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205675349/10000000000 : ℝ)^2097 ≤ (422996629557/3125000000000 : ℝ)^1585 := by
    have hnat : (2205675349 : ℕ)^2097*3125000000000^1585 ≤ 422996629557^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205675349 10000000000 422996629557 3125000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213784221/400000000 : ℝ), (2633157647/5000000000 : ℝ), (-2205675349/10000000000 : ℝ)] ![(21827032385257/50000000000000 : ℝ), (21405021532451/50000000000000 : ℝ), (422996629557/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213784221/400000000 : ℝ)|^2097 ≤ (21827032385257/50000000000000 : ℝ)^1585
        have hw : |(213784221/400000000 : ℝ)|=(213784221/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633157647/5000000000 : ℝ)|^2097 ≤ (21405021532451/50000000000000 : ℝ)^1585
        have hw : |(2633157647/5000000000 : ℝ)|=(2633157647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205675349/10000000000 : ℝ)|^2097 ≤ (422996629557/3125000000000 : ℝ)^1585
        have hw : |(-2205675349/10000000000 : ℝ)|=(2205675349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s6_3 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1089311827/2500000000 : ℝ)*x 0 + (4232405147/10000000000 : ℝ)*x 1 + (4485707023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089311827/2500000000 : ℝ)^2097 ≤ (33317124444149/100000000000000 : ℝ)^1585 := by
    have hnat : (1089311827 : ℕ)^2097*100000000000000^1585 ≤ 33317124444149^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089311827 2500000000 33317124444149 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232405147/10000000000 : ℝ)^2097 ≤ (641201167481/2000000000000 : ℝ)^1585 := by
    have hnat : (4232405147 : ℕ)^2097*2000000000000^1585 ≤ 641201167481^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232405147 10000000000 641201167481 2000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485707023/10000000000 : ℝ)^2097 ≤ (34622817158169/100000000000000 : ℝ)^1585 := by
    have hnat : (4485707023 : ℕ)^2097*100000000000000^1585 ≤ 34622817158169^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485707023 10000000000 34622817158169 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089311827/2500000000 : ℝ), (4232405147/10000000000 : ℝ), (4485707023/10000000000 : ℝ)] ![(33317124444149/100000000000000 : ℝ), (641201167481/2000000000000 : ℝ), (34622817158169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089311827/2500000000 : ℝ)|^2097 ≤ (33317124444149/100000000000000 : ℝ)^1585
        have hw : |(1089311827/2500000000 : ℝ)|=(1089311827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232405147/10000000000 : ℝ)|^2097 ≤ (641201167481/2000000000000 : ℝ)^1585
        have hw : |(4232405147/10000000000 : ℝ)|=(4232405147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485707023/10000000000 : ℝ)|^2097 ≤ (34622817158169/100000000000000 : ℝ)^1585
        have hw : |(4485707023/10000000000 : ℝ)|=(4485707023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s6_4 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-535443803/2500000000 : ℝ)*x 0 + (5266633753/10000000000 : ℝ)*x 1 + (269600269/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535443803/2500000000 : ℝ)^2097 ≤ (813719776147/6250000000000 : ℝ)^1585 := by
    have hnat : (535443803 : ℕ)^2097*6250000000000^1585 ≤ 813719776147^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535443803 2500000000 813719776147 6250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266633753/10000000000 : ℝ)^2097 ≤ (21406734052817/50000000000000 : ℝ)^1585 := by
    have hnat : (5266633753 : ℕ)^2097*50000000000000^1585 ≤ 21406734052817^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266633753 10000000000 21406734052817 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269600269/500000000 : ℝ)^2097 ≤ (44167015462469/100000000000000 : ℝ)^1585 := by
    have hnat : (269600269 : ℕ)^2097*100000000000000^1585 ≤ 44167015462469^1585*500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269600269 500000000 44167015462469 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535443803/2500000000 : ℝ), (5266633753/10000000000 : ℝ), (269600269/500000000 : ℝ)] ![(813719776147/6250000000000 : ℝ), (21406734052817/50000000000000 : ℝ), (44167015462469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535443803/2500000000 : ℝ)|^2097 ≤ (813719776147/6250000000000 : ℝ)^1585
        have hw : |(-535443803/2500000000 : ℝ)|=(535443803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266633753/10000000000 : ℝ)|^2097 ≤ (21406734052817/50000000000000 : ℝ)^1585
        have hw : |(5266633753/10000000000 : ℝ)|=(5266633753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269600269/500000000 : ℝ)|^2097 ≤ (44167015462469/100000000000000 : ℝ)^1585
        have hw : |(269600269/500000000 : ℝ)|=(269600269/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s6_5 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (332034863/625000000 : ℝ)*x 0 + (-2079985363/10000000000 : ℝ)*x 1 + (21568021/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332034863/625000000 : ℝ)^2097 ≤ (43308082446859/100000000000000 : ℝ)^1585 := by
    have hnat : (332034863 : ℕ)^2097*100000000000000^1585 ≤ 43308082446859^1585*625000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332034863 625000000 43308082446859 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079985363/10000000000 : ℝ)^2097 ≤ (12524903480977/100000000000000 : ℝ)^1585 := by
    have hnat : (2079985363 : ℕ)^2097*100000000000000^1585 ≤ 12524903480977^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079985363 10000000000 12524903480977 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21568021/40000000 : ℝ)^2097 ≤ (22083507026817/50000000000000 : ℝ)^1585 := by
    have hnat : (21568021 : ℕ)^2097*50000000000000^1585 ≤ 22083507026817^1585*40000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21568021 40000000 22083507026817 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332034863/625000000 : ℝ), (-2079985363/10000000000 : ℝ), (21568021/40000000 : ℝ)] ![(43308082446859/100000000000000 : ℝ), (12524903480977/100000000000000 : ℝ), (22083507026817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332034863/625000000 : ℝ)|^2097 ≤ (43308082446859/100000000000000 : ℝ)^1585
        have hw : |(332034863/625000000 : ℝ)|=(332034863/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079985363/10000000000 : ℝ)|^2097 ≤ (12524903480977/100000000000000 : ℝ)^1585
        have hw : |(-2079985363/10000000000 : ℝ)|=(2079985363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21568021/40000000 : ℝ)|^2097 ≤ (22083507026817/50000000000000 : ℝ)^1585
        have hw : |(21568021/40000000 : ℝ)|=(21568021/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s6_6 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656278913/5000000000 : ℝ)*x 0 + (5392005237/10000000000 : ℝ)*x 1 + (-2079985357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656278913/5000000000 : ℝ)^2097 ≤ (8661616528199/20000000000000 : ℝ)^1585 := by
    have hnat : (2656278913 : ℕ)^2097*20000000000000^1585 ≤ 8661616528199^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656278913 5000000000 8661616528199 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392005237/10000000000 : ℝ)^2097 ≤ (44167013912751/100000000000000 : ℝ)^1585 := by
    have hnat : (5392005237 : ℕ)^2097*100000000000000^1585 ≤ 44167013912751^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392005237 10000000000 44167013912751 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079985357/10000000000 : ℝ)^2097 ≤ (1565612929147/12500000000000 : ℝ)^1585 := by
    have hnat : (2079985357 : ℕ)^2097*12500000000000^1585 ≤ 1565612929147^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079985357 10000000000 1565612929147 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656278913/5000000000 : ℝ), (5392005237/10000000000 : ℝ), (-2079985357/10000000000 : ℝ)] ![(8661616528199/20000000000000 : ℝ), (44167013912751/100000000000000 : ℝ), (1565612929147/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656278913/5000000000 : ℝ)|^2097 ≤ (8661616528199/20000000000000 : ℝ)^1585
        have hw : |(2656278913/5000000000 : ℝ)|=(2656278913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392005237/10000000000 : ℝ)|^2097 ≤ (44167013912751/100000000000000 : ℝ)^1585
        have hw : |(5392005237/10000000000 : ℝ)|=(5392005237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2079985357/10000000000 : ℝ)|^2097 ≤ (1565612929147/12500000000000 : ℝ)^1585
        have hw : |(-2079985357/10000000000 : ℝ)|=(2079985357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s6_7 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2178628321/5000000000 : ℝ)*x 0 + (448506693/1000000000 : ℝ)*x 1 + (52913099/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178628321/5000000000 : ℝ)^2097 ≤ (33317218870327/100000000000000 : ℝ)^1585 := by
    have hnat : (2178628321 : ℕ)^2097*100000000000000^1585 ≤ 33317218870327^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178628321 5000000000 33317218870327 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448506693/1000000000 : ℝ)^2097 ≤ (34616280831797/100000000000000 : ℝ)^1585 := by
    have hnat : (448506693 : ℕ)^2097*100000000000000^1585 ≤ 34616280831797^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448506693 1000000000 34616280831797 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52913099/125000000 : ℝ)^2097 ≤ (32066500282031/100000000000000 : ℝ)^1585 := by
    have hnat : (52913099 : ℕ)^2097*100000000000000^1585 ≤ 32066500282031^1585*125000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52913099 125000000 32066500282031 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178628321/5000000000 : ℝ), (448506693/1000000000 : ℝ), (52913099/125000000 : ℝ)] ![(33317218870327/100000000000000 : ℝ), (34616280831797/100000000000000 : ℝ), (32066500282031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178628321/5000000000 : ℝ)|^2097 ≤ (33317218870327/100000000000000 : ℝ)^1585
        have hw : |(2178628321/5000000000 : ℝ)|=(2178628321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448506693/1000000000 : ℝ)|^2097 ≤ (34616280831797/100000000000000 : ℝ)^1585
        have hw : |(448506693/1000000000 : ℝ)|=(448506693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52913099/125000000 : ℝ)|^2097 ≤ (32066500282031/100000000000000 : ℝ)^1585
        have hw : |(52913099/125000000 : ℝ)|=(52913099/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1195_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2283/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2817/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11391/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11391/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11391/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11391/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11391/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11391/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11391/100000 : ℝ) ^ (8387/2048 : ℝ) ≤ (2738092320806923/20000000000000000000 : ℝ) := by
    have hpowers : (11391/100000 : ℝ)^8387 ≤ (2738092320806923/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11391 : ℕ)^8387*20000000000000000000^2048 ≤ 2738092320806923^2048*100000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11391 100000 2738092320806923 20000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11391/100000 : ℝ)) (X := (2738092320806923/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14111/100000 : ℝ) ^ (8387/2048 : ℝ) ≤ (32904587100888481/100000000000000000000 : ℝ) := by
    have hpowers : (14111/100000 : ℝ)^8387 ≤ (32904587100888481/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14111 : ℕ)^8387*100000000000000000000^2048 ≤ 32904587100888481^2048*100000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14111 100000 32904587100888481 100000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14111/100000 : ℝ)) (X := (32904587100888481/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002738092320806923/10000000000000000000 : ℝ) ≤ (2500167134640591/2500000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (10002738092320806923/10000000000000000000 : ℝ)^2048 ≤ (2500167134640591/2500000000000000 : ℝ)^8387 := by
      have hnat : (10002738092320806923 : ℕ)^2048*2500000000000000^8387 ≤ 2500167134640591^8387*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002738092320806923 10000000000000000000 2500167134640591 2500000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500167134640591/2500000000000000 : ℝ)) (X := (10002738092320806923/10000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505824381088115387/12500000000000000000 : ℝ) ≤ (10001137592238779/10000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (12505824381088115387/12500000000000000000 : ℝ)^2048 ≤ (10001137592238779/10000000000000000 : ℝ)^8387 := by
      have hnat : (12505824381088115387 : ℕ)^2048*10000000000000000^8387 ≤ 10001137592238779^8387*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505824381088115387 12500000000000000000 10001137592238779 10000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001137592238779/10000000000000000 : ℝ)) (X := (12505824381088115387/12500000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032904587100888481/50000000000000000000 : ℝ) ≤ (5000803322957597/5000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (50032904587100888481/50000000000000000000 : ℝ)^2048 ≤ (5000803322957597/5000000000000000 : ℝ)^8387 := by
      have hnat : (50032904587100888481 : ℕ)^2048*5000000000000000^8387 ≤ 5000803322957597^8387*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032904587100888481 50000000000000000000 5000803322957597 5000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000803322957597/5000000000000000 : ℝ)) (X := (50032904587100888481/50000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2738092320806923/20000000000000000000 : ℝ) ≤ ((543822648880670871/544000000000000000 : ℝ)+2*(93810735283/54400000000000 : ℝ)*(11391/100000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (543822648880670871/544000000000000000 : ℝ)+2*(93810735283/54400000000000 : ℝ)*(11391/100000 : ℝ)=(2500167134640591/2500000000000000 : ℝ) by norm_num, show 1+2*(2738092320806923/20000000000000000000 : ℝ)=(10002738092320806923/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32904587100888481/100000000000000000000 : ℝ)+(2738092320806923/20000000000000000000 : ℝ) ≤ ((543822648880670871/544000000000000000 : ℝ)+(93810735283/54400000000000 : ℝ)*((14111/100000 : ℝ)+(11391/100000 : ℝ)))^(8387/2048 : ℝ) := by
    rw [show (543822648880670871/544000000000000000 : ℝ)+(93810735283/54400000000000 : ℝ)*((14111/100000 : ℝ)+(11391/100000 : ℝ))=(10001137592238779/10000000000000000 : ℝ) by norm_num, show 1+(32904587100888481/100000000000000000000 : ℝ)+(2738092320806923/20000000000000000000 : ℝ)=(12505824381088115387/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32904587100888481/100000000000000000000 : ℝ) ≤ ((543822648880670871/544000000000000000 : ℝ)+2*(93810735283/54400000000000 : ℝ)*(14111/100000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (543822648880670871/544000000000000000 : ℝ)+2*(93810735283/54400000000000 : ℝ)*(14111/100000 : ℝ)=(5000803322957597/5000000000000000 : ℝ) by norm_num, show 1+2*(32904587100888481/100000000000000000000 : ℝ)=(50032904587100888481/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (543822648880670871/544000000000000000 : ℝ)*(X 1 0+X 2 0)+(93810735283/54400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (543822648880670871/544000000000000000 : ℝ)) (alpha := (93810735283/54400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (543822648880670871/544000000000000000 : ℝ)*(X 0 1+X 2 1)+(93810735283/54400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (543822648880670871/544000000000000000 : ℝ)) (alpha := (93810735283/54400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (543822648880670871/544000000000000000 : ℝ)*(X 0 2+X 1 2)+(93810735283/54400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (11391/100000 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (543822648880670871/544000000000000000 : ℝ)) (alpha := (93810735283/54400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2141770403/10000000000 : ℝ)*X 0 0+(337020301/625000000 : ℝ)*X 0 1+(526631547/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534460541/1000000000 : ℝ)*X 1 0+(-1102837587/5000000000 : ℝ)*X 1 1+(5266315541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213784221/400000000 : ℝ)*X 2 0+(2633157647/5000000000 : ℝ)*X 2 1+(-2205675349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089311827/2500000000 : ℝ)*X 0 0+(4232405147/10000000000 : ℝ)*X 0 1+(4485707023/10000000000 : ℝ)*X 0 2+(1089311827/2500000000 : ℝ)*X 1 0+(4232405147/10000000000 : ℝ)*X 1 1+(4485707023/10000000000 : ℝ)*X 1 2+(1089311827/2500000000 : ℝ)*X 2 0+(4232405147/10000000000 : ℝ)*X 2 1+(4485707023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-535443803/2500000000 : ℝ)*X 0 0+(5266633753/10000000000 : ℝ)*X 0 1+(269600269/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332034863/625000000 : ℝ)*X 1 0+(-2079985363/10000000000 : ℝ)*X 1 1+(21568021/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656278913/5000000000 : ℝ)*X 2 0+(5392005237/10000000000 : ℝ)*X 2 1+(-2079985357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178628321/5000000000 : ℝ)*X 0 0+(448506693/1000000000 : ℝ)*X 0 1+(52913099/125000000 : ℝ)*X 0 2+(2178628321/5000000000 : ℝ)*X 1 0+(448506693/1000000000 : ℝ)*X 1 1+(52913099/125000000 : ℝ)*X 1 2+(2178628321/5000000000 : ℝ)*X 2 0+(448506693/1000000000 : ℝ)*X 2 1+(52913099/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (157192859264851650667075137/13600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (198206659/10000000000000 : ℝ)*(base19) + (91751209/5000000000000 : ℝ)*(base23) + (105644729/50000000000000 : ℝ)*(lower2) + (486197269/100000000000000 : ℝ)*(upper3) + (2589807/6250000000000 : ℝ)*(lower4) + (2970984475016749/50000000000000 : ℝ)*(major0) + (2970984475016749/50000000000000 : ℝ)*(major1) + (2970984475016749/50000000000000 : ℝ)*(major2) + (991997130130293/12500000000000 : ℝ)*(sp0) + (7936015507428331/100000000000000 : ℝ)*(sp1) + (7936015654470741/100000000000000 : ℝ)*(sp2) + (3947883023960303/100000000000000 : ℝ)*(sp3) + (40448452577/100000000000000 : ℝ)*(sp4) + (2312583447/6250000000000 : ℝ)*(sp7) + (789584005059091/20000000000000 : ℝ)*(f.failure) + (7936017489494921/100000000000000 : ℝ)*(f.sum) + (3664176240247/1360000000000000000000000000 : ℝ)*base65 + (283011360691888379/27200000000000000000000000000000 : ℝ)*base67 + (82463470141711621/27200000000000000000000000000000 : ℝ)*base70 + (94117224978511621/27200000000000000000000000000000 : ℝ)*base72 + (22811442553/1360000000000000000000000000 : ℝ)*base74 + (123205428904911621/27200000000000000000000000000000 : ℝ)*base76 + (100905619146511621/27200000000000000000000000000000 : ℝ)*base78 + (225951944095088379/27200000000000000000000000000000 : ℝ)*base79 + (1681576097033/1360000000000000000000000000 : ℝ)*base82 + (103927/125000000000000000000 : ℝ)*base90 + (103927/125000000000000000000 : ℝ)*base92 + (103927/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31591654109784991227430833/3400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128606389/10000000000000 : ℝ)*(base19) + (767542789/50000000000000 : ℝ)*(base23) + (93479469/100000000000000 : ℝ)*(upper3) + (5264179/5000000000000 : ℝ)*(lower4) + (295637/195312500000 : ℝ)*(upper5) + (1493029943909941/25000000000000 : ℝ)*(major0) + (1493029943909941/25000000000000 : ℝ)*(major1) + (1493029943909941/25000000000000 : ℝ)*(major2) + (31462112047/100000000000000 : ℝ)*(sp1) + (35410293709/100000000000000 : ℝ)*(sp2) + (7976286622825157/100000000000000 : ℝ)*(sp4) + (398812693732461/5000000000000 : ℝ)*(sp5) + (7976249677445871/100000000000000 : ℝ)*(sp6) + (793590523746453/20000000000000 : ℝ)*(sp7) + (793590523746453/20000000000000 : ℝ)*(f.failure) + (7976286622825157/100000000000000 : ℝ)*(f.sum) + (192667973023/680000000000000000000000000 : ℝ)*base65 + (106141712756541389/13600000000000000000000000000000 : ℝ)*base68 + (123478486686941389/13600000000000000000000000000000 : ℝ)*base70 + (97285489393058611/13600000000000000000000000000000 : ℝ)*base71 + (911354571857/680000000000000000000000000 : ℝ)*base74 + (50099452318141389/13600000000000000000000000000000 : ℝ)*base76 + (83214997724541389/13600000000000000000000000000000 : ℝ)*base78 + (240523144823741389/13600000000000000000000000000000 : ℝ)*base80 + (2133658228143/680000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (319759/125000000000000000000 : ℝ)*base89 + (319759/125000000000000000000 : ℝ)*base91 + (319759/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1195_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1195_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1195_s7_0 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141794573/10000000000 : ℝ)*x 0 + (5392079061/10000000000 : ℝ)*x 1 + (658318129/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141794573/10000000000 : ℝ)^2097 ≤ (2603934425817/20000000000000 : ℝ)^1585 := by
    have hnat : (2141794573 : ℕ)^2097*20000000000000^1585 ≤ 2603934425817^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141794573 10000000000 2603934425817 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392079061/10000000000 : ℝ)^2097 ≤ (44167813959619/100000000000000 : ℝ)^1585 := by
    have hnat : (5392079061 : ℕ)^2097*100000000000000^1585 ≤ 44167813959619^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392079061 10000000000 44167813959619 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658318129/1250000000 : ℝ)^2097 ≤ (42812513900603/100000000000000 : ℝ)^1585 := by
    have hnat : (658318129 : ℕ)^2097*100000000000000^1585 ≤ 42812513900603^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658318129 1250000000 42812513900603 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141794573/10000000000 : ℝ), (5392079061/10000000000 : ℝ), (658318129/1250000000 : ℝ)] ![(2603934425817/20000000000000 : ℝ), (44167813959619/100000000000000 : ℝ), (42812513900603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141794573/10000000000 : ℝ)|^2097 ≤ (2603934425817/20000000000000 : ℝ)^1585
        have hw : |(-2141794573/10000000000 : ℝ)|=(2141794573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392079061/10000000000 : ℝ)|^2097 ≤ (44167813959619/100000000000000 : ℝ)^1585
        have hw : |(5392079061/10000000000 : ℝ)|=(5392079061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658318129/1250000000 : ℝ)|^2097 ≤ (42812513900603/100000000000000 : ℝ)^1585
        have hw : |(658318129/1250000000 : ℝ)|=(658318129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s7_1 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668067769/1250000000 : ℝ)*x 0 + (-2205454991/10000000000 : ℝ)*x 1 + (131663633/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668067769/1250000000 : ℝ)^2097 ≤ (43653379942321/100000000000000 : ℝ)^1585 := by
    have hnat : (668067769 : ℕ)^2097*100000000000000^1585 ≤ 43653379942321^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668067769 1250000000 43653379942321 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205454991/10000000000 : ℝ)^2097 ≤ (6767051519497/50000000000000 : ℝ)^1585 := by
    have hnat : (2205454991 : ℕ)^2097*50000000000000^1585 ≤ 6767051519497^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205454991 10000000000 6767051519497 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131663633/250000000 : ℝ)^2097 ≤ (4281251699807/10000000000000 : ℝ)^1585 := by
    have hnat : (131663633 : ℕ)^2097*10000000000000^1585 ≤ 4281251699807^1585*250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131663633 250000000 4281251699807 10000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668067769/1250000000 : ℝ), (-2205454991/10000000000 : ℝ), (131663633/250000000 : ℝ)] ![(43653379942321/100000000000000 : ℝ), (6767051519497/50000000000000 : ℝ), (4281251699807/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668067769/1250000000 : ℝ)|^2097 ≤ (43653379942321/100000000000000 : ℝ)^1585
        have hw : |(668067769/1250000000 : ℝ)|=(668067769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2205454991/10000000000 : ℝ)|^2097 ≤ (6767051519497/50000000000000 : ℝ)^1585
        have hw : |(-2205454991/10000000000 : ℝ)|=(2205454991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131663633/250000000 : ℝ)|^2097 ≤ (4281251699807/10000000000000 : ℝ)^1585
        have hw : |(131663633/250000000 : ℝ)|=(131663633/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s7_2 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534454233/1000000000 : ℝ)*x 0 + (1316636353/2500000000 : ℝ)*x 1 + (-275681829/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534454233/1000000000 : ℝ)^2097 ≤ (43653381865841/100000000000000 : ℝ)^1585 := by
    have hnat : (534454233 : ℕ)^2097*100000000000000^1585 ≤ 43653381865841^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534454233 1000000000 43653381865841 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316636353/2500000000 : ℝ)^2097 ≤ (21406258993769/50000000000000 : ℝ)^1585 := by
    have hnat : (1316636353 : ℕ)^2097*50000000000000^1585 ≤ 21406258993769^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316636353 2500000000 21406258993769 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275681829/1250000000 : ℝ)^2097 ≤ (13534100124287/100000000000000 : ℝ)^1585 := by
    have hnat : (275681829 : ℕ)^2097*100000000000000^1585 ≤ 13534100124287^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275681829 1250000000 13534100124287 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534454233/1000000000 : ℝ), (1316636353/2500000000 : ℝ), (-275681829/1250000000 : ℝ)] ![(43653381865841/100000000000000 : ℝ), (21406258993769/50000000000000 : ℝ), (13534100124287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534454233/1000000000 : ℝ)|^2097 ≤ (43653381865841/100000000000000 : ℝ)^1585
        have hw : |(534454233/1000000000 : ℝ)|=(534454233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316636353/2500000000 : ℝ)|^2097 ≤ (21406258993769/50000000000000 : ℝ)^1585
        have hw : |(1316636353/2500000000 : ℝ)|=(1316636353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275681829/1250000000 : ℝ)|^2097 ≤ (13534100124287/100000000000000 : ℝ)^1585
        have hw : |(-275681829/1250000000 : ℝ)|=(275681829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s7_3 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4357259689/10000000000 : ℝ)*x 0 + (4232881521/10000000000 : ℝ)*x 1 + (1121306807/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357259689/10000000000 : ℝ)^2097 ≤ (16658624847457/50000000000000 : ℝ)^1585 := by
    have hnat : (4357259689 : ℕ)^2097*50000000000000^1585 ≤ 16658624847457^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357259689 10000000000 16658624847457 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232881521/10000000000 : ℝ)^2097 ≤ (32064832591367/100000000000000 : ℝ)^1585 := by
    have hnat : (4232881521 : ℕ)^2097*100000000000000^1585 ≤ 32064832591367^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232881521 10000000000 32064832591367 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121306807/2500000000 : ℝ)^2097 ≤ (34617917690727/100000000000000 : ℝ)^1585 := by
    have hnat : (1121306807 : ℕ)^2097*100000000000000^1585 ≤ 34617917690727^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121306807 2500000000 34617917690727 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357259689/10000000000 : ℝ), (4232881521/10000000000 : ℝ), (1121306807/2500000000 : ℝ)] ![(16658624847457/50000000000000 : ℝ), (32064832591367/100000000000000 : ℝ), (34617917690727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357259689/10000000000 : ℝ)|^2097 ≤ (16658624847457/50000000000000 : ℝ)^1585
        have hw : |(4357259689/10000000000 : ℝ)|=(4357259689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232881521/10000000000 : ℝ)|^2097 ≤ (32064832591367/100000000000000 : ℝ)^1585
        have hw : |(4232881521/10000000000 : ℝ)|=(4232881521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121306807/2500000000 : ℝ)|^2097 ≤ (34617917690727/100000000000000 : ℝ)^1585
        have hw : |(1121306807/2500000000 : ℝ)|=(1121306807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s7_4 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070899561/5000000000 : ℝ)*x 0 + (263343067/500000000 : ℝ)*x 1 + (5391761769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070899561/5000000000 : ℝ)^2097 ≤ (6509854357229/50000000000000 : ℝ)^1585 := by
    have hnat : (1070899561 : ℕ)^2097*50000000000000^1585 ≤ 6509854357229^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070899561 5000000000 6509854357229 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263343067/500000000 : ℝ)^2097 ≤ (21407957927473/50000000000000 : ℝ)^1585 := by
    have hnat : (263343067 : ℕ)^2097*50000000000000^1585 ≤ 21407957927473^1585*500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263343067 500000000 21407957927473 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391761769/10000000000 : ℝ)^2097 ≤ (11041093855437/25000000000000 : ℝ)^1585 := by
    have hnat : (5391761769 : ℕ)^2097*25000000000000^1585 ≤ 11041093855437^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391761769 10000000000 11041093855437 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070899561/5000000000 : ℝ), (263343067/500000000 : ℝ), (5391761769/10000000000 : ℝ)] ![(6509854357229/50000000000000 : ℝ), (21407957927473/50000000000000 : ℝ), (11041093855437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070899561/5000000000 : ℝ)|^2097 ≤ (6509854357229/50000000000000 : ℝ)^1585
        have hw : |(-1070899561/5000000000 : ℝ)|=(1070899561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263343067/500000000 : ℝ)|^2097 ≤ (21407957927473/50000000000000 : ℝ)^1585
        have hw : |(263343067/500000000 : ℝ)|=(263343067/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391761769/10000000000 : ℝ)|^2097 ≤ (11041093855437/25000000000000 : ℝ)^1585
        have hw : |(5391761769/10000000000 : ℝ)|=(5391761769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s7_5 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312616073/10000000000 : ℝ)*x 0 + (-1040118627/5000000000 : ℝ)*x 1 + (1078352417/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312616073/10000000000 : ℝ)^2097 ≤ (43308710856689/100000000000000 : ℝ)^1585 := by
    have hnat : (5312616073 : ℕ)^2097*100000000000000^1585 ≤ 43308710856689^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312616073 10000000000 43308710856689 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040118627/5000000000 : ℝ)^2097 ≤ (12526910282481/100000000000000 : ℝ)^1585 := by
    have hnat : (1040118627 : ℕ)^2097*100000000000000^1585 ≤ 12526910282481^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040118627 5000000000 12526910282481 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078352417/2000000000 : ℝ)^2097 ≤ (11041094711563/25000000000000 : ℝ)^1585 := by
    have hnat : (1078352417 : ℕ)^2097*25000000000000^1585 ≤ 11041094711563^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078352417 2000000000 11041094711563 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312616073/10000000000 : ℝ), (-1040118627/5000000000 : ℝ), (1078352417/2000000000 : ℝ)] ![(43308710856689/100000000000000 : ℝ), (12526910282481/100000000000000 : ℝ), (11041094711563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312616073/10000000000 : ℝ)|^2097 ≤ (43308710856689/100000000000000 : ℝ)^1585
        have hw : |(5312616073/10000000000 : ℝ)|=(5312616073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040118627/5000000000 : ℝ)|^2097 ≤ (12526910282481/100000000000000 : ℝ)^1585
        have hw : |(-1040118627/5000000000 : ℝ)|=(1040118627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078352417/2000000000 : ℝ)|^2097 ≤ (11041094711563/25000000000000 : ℝ)^1585
        have hw : |(1078352417/2000000000 : ℝ)|=(1078352417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s7_6 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328153909/2500000000 : ℝ)*x 0 + (5391762421/10000000000 : ℝ)*x 1 + (-2080237389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328153909/2500000000 : ℝ)^2097 ≤ (2706794133967/6250000000000 : ℝ)^1585 := by
    have hnat : (1328153909 : ℕ)^2097*6250000000000^1585 ≤ 2706794133967^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328153909 2500000000 2706794133967 6250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391762421/10000000000 : ℝ)^2097 ≤ (44164382487497/100000000000000 : ℝ)^1585 := by
    have hnat : (5391762421 : ℕ)^2097*100000000000000^1585 ≤ 44164382487497^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391762421 10000000000 44164382487497 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080237389/10000000000 : ℝ)^2097 ≤ (12526911358039/100000000000000 : ℝ)^1585 := by
    have hnat : (2080237389 : ℕ)^2097*100000000000000^1585 ≤ 12526911358039^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080237389 10000000000 12526911358039 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328153909/2500000000 : ℝ), (5391762421/10000000000 : ℝ), (-2080237389/10000000000 : ℝ)] ![(2706794133967/6250000000000 : ℝ), (44164382487497/100000000000000 : ℝ), (12526911358039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328153909/2500000000 : ℝ)|^2097 ≤ (2706794133967/6250000000000 : ℝ)^1585
        have hw : |(1328153909/2500000000 : ℝ)|=(1328153909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391762421/10000000000 : ℝ)|^2097 ≤ (44164382487497/100000000000000 : ℝ)^1585
        have hw : |(5391762421/10000000000 : ℝ)|=(5391762421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080237389/10000000000 : ℝ)|^2097 ≤ (12526911358039/100000000000000 : ℝ)^1585
        have hw : |(-2080237389/10000000000 : ℝ)|=(2080237389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s7_7 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4357268933/10000000000 : ℝ)*x 0 + (2242296007/5000000000 : ℝ)*x 1 + (529189921/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357268933/10000000000 : ℝ)^2097 ≤ (6663468642141/20000000000000 : ℝ)^1585 := by
    have hnat : (4357268933 : ℕ)^2097*20000000000000^1585 ≤ 6663468642141^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357268933 10000000000 6663468642141 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242296007/5000000000 : ℝ)^2097 ≤ (34611431409393/100000000000000 : ℝ)^1585 := by
    have hnat : (2242296007 : ℕ)^2097*100000000000000^1585 ≤ 34611431409393^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242296007 5000000000 34611431409393 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529189921/1250000000 : ℝ)^2097 ≤ (16035612680943/50000000000000 : ℝ)^1585 := by
    have hnat : (529189921 : ℕ)^2097*50000000000000^1585 ≤ 16035612680943^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529189921 1250000000 16035612680943 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357268933/10000000000 : ℝ), (2242296007/5000000000 : ℝ), (529189921/1250000000 : ℝ)] ![(6663468642141/20000000000000 : ℝ), (34611431409393/100000000000000 : ℝ), (16035612680943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357268933/10000000000 : ℝ)|^2097 ≤ (6663468642141/20000000000000 : ℝ)^1585
        have hw : |(4357268933/10000000000 : ℝ)|=(4357268933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242296007/5000000000 : ℝ)|^2097 ≤ (34611431409393/100000000000000 : ℝ)^1585
        have hw : |(2242296007/5000000000 : ℝ)|=(2242296007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529189921/1250000000 : ℝ)|^2097 ≤ (16035612680943/50000000000000 : ℝ)^1585
        have hw : |(529189921/1250000000 : ℝ)|=(529189921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1195_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (571/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (88/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2283/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2283/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2283/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2283/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2283/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2283/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2283/20000 : ℝ) ^ (8387/2048 : ℝ) ≤ (3452243245546879/25000000000000000000 : ℝ) := by
    have hpowers : (2283/20000 : ℝ)^8387 ≤ (3452243245546879/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2283 : ℕ)^8387*25000000000000000000^2048 ≤ 3452243245546879^2048*20000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2283 20000 3452243245546879 25000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2283/20000 : ℝ)) (X := (3452243245546879/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2817/20000 : ℝ) ^ (8387/2048 : ℝ) ≤ (3265701020046563/10000000000000000000 : ℝ) := by
    have hpowers : (2817/20000 : ℝ)^8387 ≤ (3265701020046563/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2817 : ℕ)^8387*10000000000000000000^2048 ≤ 3265701020046563^2048*20000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2817 20000 3265701020046563 10000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2817/20000 : ℝ)) (X := (3265701020046563/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503452243245546879/12500000000000000000 : ℝ) ≤ (2000134865031507/2000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (12503452243245546879/12500000000000000000 : ℝ)^2048 ≤ (2000134865031507/2000000000000000 : ℝ)^8387 := by
      have hnat : (12503452243245546879 : ℕ)^2048*2000000000000000^8387 ≤ 2000134865031507^8387*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503452243245546879 12500000000000000000 2000134865031507 2000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000134865031507/2000000000000000 : ℝ)) (X := (12503452243245546879/12500000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023232991591326573/50000000000000000000 : ℝ) ≤ (5000567220864421/5000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (50023232991591326573/50000000000000000000 : ℝ)^2048 ≤ (5000567220864421/5000000000000000 : ℝ)^8387 := by
      have hnat : (50023232991591326573 : ℕ)^2048*5000000000000000^8387 ≤ 5000567220864421^8387*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023232991591326573 50000000000000000000 5000567220864421 5000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000567220864421/5000000000000000 : ℝ)) (X := (50023232991591326573/50000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003265701020046563/5000000000000000000 : ℝ) ≤ (10001594558300149/10000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (5003265701020046563/5000000000000000000 : ℝ)^2048 ≤ (10001594558300149/10000000000000000 : ℝ)^8387 := by
      have hnat : (5003265701020046563 : ℕ)^2048*10000000000000000^8387 ≤ 10001594558300149^8387*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003265701020046563 5000000000000000000 10001594558300149 10000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001594558300149/10000000000000000 : ℝ)) (X := (5003265701020046563/5000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3452243245546879/25000000000000000000 : ℝ) ≤ ((222427466557063997/222500000000000000 : ℝ)+2*(460116571307/267000000000000 : ℝ)*(2283/20000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (222427466557063997/222500000000000000 : ℝ)+2*(460116571307/267000000000000 : ℝ)*(2283/20000 : ℝ)=(2000134865031507/2000000000000000 : ℝ) by norm_num, show 1+2*(3452243245546879/25000000000000000000 : ℝ)=(12503452243245546879/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3265701020046563/10000000000000000000 : ℝ)+(3452243245546879/25000000000000000000 : ℝ) ≤ ((222427466557063997/222500000000000000 : ℝ)+(460116571307/267000000000000 : ℝ)*((2817/20000 : ℝ)+(2283/20000 : ℝ)))^(8387/2048 : ℝ) := by
    rw [show (222427466557063997/222500000000000000 : ℝ)+(460116571307/267000000000000 : ℝ)*((2817/20000 : ℝ)+(2283/20000 : ℝ))=(5000567220864421/5000000000000000 : ℝ) by norm_num, show 1+(3265701020046563/10000000000000000000 : ℝ)+(3452243245546879/25000000000000000000 : ℝ)=(50023232991591326573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3265701020046563/10000000000000000000 : ℝ) ≤ ((222427466557063997/222500000000000000 : ℝ)+2*(460116571307/267000000000000 : ℝ)*(2817/20000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (222427466557063997/222500000000000000 : ℝ)+2*(460116571307/267000000000000 : ℝ)*(2817/20000 : ℝ)=(10001594558300149/10000000000000000 : ℝ) by norm_num, show 1+2*(3265701020046563/10000000000000000000 : ℝ)=(5003265701020046563/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (222427466557063997/222500000000000000 : ℝ)*(X 1 0+X 2 0)+(460116571307/267000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (2283/20000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (222427466557063997/222500000000000000 : ℝ)) (alpha := (460116571307/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (222427466557063997/222500000000000000 : ℝ)*(X 0 1+X 2 1)+(460116571307/267000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (2283/20000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (222427466557063997/222500000000000000 : ℝ)) (alpha := (460116571307/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (222427466557063997/222500000000000000 : ℝ)*(X 0 2+X 1 2)+(460116571307/267000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (2283/20000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (222427466557063997/222500000000000000 : ℝ)) (alpha := (460116571307/267000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2141794573/10000000000 : ℝ)*X 0 0+(5392079061/10000000000 : ℝ)*X 0 1+(658318129/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668067769/1250000000 : ℝ)*X 1 0+(-2205454991/10000000000 : ℝ)*X 1 1+(131663633/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534454233/1000000000 : ℝ)*X 2 0+(1316636353/2500000000 : ℝ)*X 2 1+(-275681829/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357259689/10000000000 : ℝ)*X 0 0+(4232881521/10000000000 : ℝ)*X 0 1+(1121306807/2500000000 : ℝ)*X 0 2+(4357259689/10000000000 : ℝ)*X 1 0+(4232881521/10000000000 : ℝ)*X 1 1+(1121306807/2500000000 : ℝ)*X 1 2+(4357259689/10000000000 : ℝ)*X 2 0+(4232881521/10000000000 : ℝ)*X 2 1+(1121306807/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1070899561/5000000000 : ℝ)*X 0 0+(263343067/500000000 : ℝ)*X 0 1+(5391761769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312616073/10000000000 : ℝ)*X 1 0+(-1040118627/5000000000 : ℝ)*X 1 1+(1078352417/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328153909/2500000000 : ℝ)*X 2 0+(5391762421/10000000000 : ℝ)*X 2 1+(-2080237389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357268933/10000000000 : ℝ)*X 0 0+(2242296007/5000000000 : ℝ)*X 0 1+(529189921/1250000000 : ℝ)*X 0 2+(4357268933/10000000000 : ℝ)*X 1 0+(2242296007/5000000000 : ℝ)*X 1 1+(529189921/1250000000 : ℝ)*X 1 2+(4357268933/10000000000 : ℝ)*X 2 0+(2242296007/5000000000 : ℝ)*X 2 1+(529189921/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63322086061014099746956449/5562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1413457217/100000000000000 : ℝ)*(base19) + (810233697/50000000000000 : ℝ)*(base23) + (53519373/25000000000000 : ℝ)*(upper3) + (1246323/4000000000000 : ℝ)*(upper4) + (402272163/50000000000000 : ℝ)*(upper5) + (5964450213774411/100000000000000 : ℝ)*(major0) + (5964450213774411/100000000000000 : ℝ)*(major1) + (5964450213774411/100000000000000 : ℝ)*(major2) + (995748565886367/12500000000000 : ℝ)*(sp0) + (7966041770713741/100000000000000 : ℝ)*(sp1) + (1991510390925891/25000000000000 : ℝ)*(sp2) + (1981421152966349/50000000000000 : ℝ)*(sp3) + (27328540011/50000000000000 : ℝ)*(sp4) + (3639496741/25000000000000 : ℝ)*(sp7) + (1981428431959831/50000000000000 : ℝ)*(f.failure) + (3983021592085479/50000000000000 : ℝ)*(f.sum) + (18874549007841/4450000000000000000000000000 : ℝ)*base66 + (180429926043128267/22250000000000000000000000000000 : ℝ)*base67 + (25805574992128267/22250000000000000000000000000000 : ℝ)*base69 + (89879296042128267/22250000000000000000000000000000 : ℝ)*base71 + (9646931662709/4450000000000000000000000000 : ℝ)*base73 + (436831310179628267/22250000000000000000000000000000 : ℝ)*base75 + (610322719065871733/22250000000000000000000000000000 : ℝ)*base78 + (218130152671128267/22250000000000000000000000000000 : ℝ)*base79 + (14505158531459/4450000000000000000000000000 : ℝ)*base81 + (244707/312500000000000000000 : ℝ)*base90 + (244707/312500000000000000000 : ℝ)*base92 + (244707/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12072466685238577419992161/1390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (316767067/12500000000000 : ℝ)*(base19) + (7517539/400000000000 : ℝ)*(base23) + (11297279/100000000000000 : ℝ)*(upper2) + (42117559/10000000000000 : ℝ)*(upper3) + (2269221/1250000000000 : ℝ)*(upper5) + (374664708891749/6250000000000 : ℝ)*(major0) + (374664708891749/6250000000000 : ℝ)*(major1) + (374664708891749/6250000000000 : ℝ)*(major2) + (39915411237/50000000000000 : ℝ)*(sp1) + (3077105557/4000000000000 : ℝ)*(sp2) + (8006358146525777/100000000000000 : ℝ)*(sp4) + (8006275781566767/100000000000000 : ℝ)*(sp5) + (4003139669751051/50000000000000 : ℝ)*(sp6) + (995728062158177/25000000000000 : ℝ)*(sp7) + (995728062158177/25000000000000 : ℝ)*(f.failure) + (8006358146525777/100000000000000 : ℝ)*(f.sum) + (19730137663897/3337500000000000000000000000 : ℝ)*base65 + (10316031182297741/4171875000000000000000000000000 : ℝ)*base68 + (6994575536414279/1042968750000000000000000000000 : ℝ)*base70 + (3226252678874567/2085937500000000000000000000000 : ℝ)*base71 + (225856164517/208593750000000000000000000 : ℝ)*base73 + (21916821960750433/2085937500000000000000000000000 : ℝ)*base76 + (20871156926016491/4171875000000000000000000000000 : ℝ)*base78 + (13114148887828991/4171875000000000000000000000000 : ℝ)*base80 + (6780792870997/3337500000000000000000000000 : ℝ)*base81 + (878131/156250000000000000000 : ℝ)*base89 + (878131/156250000000000000000 : ℝ)*base91 + (878131/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1195_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (571/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1195_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1195_s8_0 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141797601/10000000000 : ℝ)*x 0 + (269601561/500000000 : ℝ)*x 1 + (2633295487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141797601/10000000000 : ℝ)^2097 ≤ (13019696481799/100000000000000 : ℝ)^1585 := by
    have hnat : (2141797601 : ℕ)^2097*100000000000000^1585 ≤ 13019696481799^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141797601 10000000000 13019696481799 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269601561/500000000 : ℝ)^2097 ≤ (44167295495813/100000000000000 : ℝ)^1585 := by
    have hnat : (269601561 : ℕ)^2097*100000000000000^1585 ≤ 44167295495813^1585*500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269601561 500000000 44167295495813 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633295487/5000000000 : ℝ)^2097 ≤ (42813008011693/100000000000000 : ℝ)^1585 := by
    have hnat : (2633295487 : ℕ)^2097*100000000000000^1585 ≤ 42813008011693^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633295487 5000000000 42813008011693 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141797601/10000000000 : ℝ), (269601561/500000000 : ℝ), (2633295487/5000000000 : ℝ)] ![(13019696481799/100000000000000 : ℝ), (44167295495813/100000000000000 : ℝ), (42813008011693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141797601/10000000000 : ℝ)|^2097 ≤ (13019696481799/100000000000000 : ℝ)^1585
        have hw : |(-2141797601/10000000000 : ℝ)|=(2141797601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269601561/500000000 : ℝ)|^2097 ≤ (44167295495813/100000000000000 : ℝ)^1585
        have hw : |(269601561/500000000 : ℝ)|=(269601561/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633295487/5000000000 : ℝ)|^2097 ≤ (42813008011693/100000000000000 : ℝ)^1585
        have hw : |(2633295487/5000000000 : ℝ)|=(2633295487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s8_1 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344530817/10000000000 : ℝ)*x 0 + (-551352401/2500000000 : ℝ)*x 1 + (1316647743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344530817/10000000000 : ℝ)^2097 ≤ (4365325745309/10000000000000 : ℝ)^1585 := by
    have hnat : (5344530817 : ℕ)^2097*10000000000000^1585 ≤ 4365325745309^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344530817 10000000000 4365325745309 10000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551352401/2500000000 : ℝ)^2097 ≤ (6766867272473/50000000000000 : ℝ)^1585 := by
    have hnat : (551352401 : ℕ)^2097*50000000000000^1585 ≤ 6766867272473^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551352401 2500000000 6766867272473 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316647743/2500000000 : ℝ)^2097 ≤ (42813007990183/100000000000000 : ℝ)^1585 := by
    have hnat : (1316647743 : ℕ)^2097*100000000000000^1585 ≤ 42813007990183^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316647743 2500000000 42813007990183 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344530817/10000000000 : ℝ), (-551352401/2500000000 : ℝ), (1316647743/2500000000 : ℝ)] ![(4365325745309/10000000000000 : ℝ), (6766867272473/50000000000000 : ℝ), (42813007990183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344530817/10000000000 : ℝ)|^2097 ≤ (4365325745309/10000000000000 : ℝ)^1585
        have hw : |(5344530817/10000000000 : ℝ)|=(5344530817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-551352401/2500000000 : ℝ)|^2097 ≤ (6766867272473/50000000000000 : ℝ)^1585
        have hw : |(-551352401/2500000000 : ℝ)|=(551352401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316647743/2500000000 : ℝ)|^2097 ≤ (42813007990183/100000000000000 : ℝ)^1585
        have hw : |(1316647743/2500000000 : ℝ)|=(1316647743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s8_2 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344530817/10000000000 : ℝ)*x 0 + (2633295487/5000000000 : ℝ)*x 1 + (-2205409601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344530817/10000000000 : ℝ)^2097 ≤ (4365325745309/10000000000000 : ℝ)^1585 := by
    have hnat : (5344530817 : ℕ)^2097*10000000000000^1585 ≤ 4365325745309^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344530817 10000000000 4365325745309 10000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633295487/5000000000 : ℝ)^2097 ≤ (42813008011693/100000000000000 : ℝ)^1585 := by
    have hnat : (2633295487 : ℕ)^2097*100000000000000^1585 ≤ 42813008011693^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633295487 5000000000 42813008011693 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205409601/10000000000 : ℝ)^2097 ≤ (13533734520589/100000000000000 : ℝ)^1585 := by
    have hnat : (2205409601 : ℕ)^2097*100000000000000^1585 ≤ 13533734520589^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205409601 10000000000 13533734520589 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344530817/10000000000 : ℝ), (2633295487/5000000000 : ℝ), (-2205409601/10000000000 : ℝ)] ![(4365325745309/10000000000000 : ℝ), (42813008011693/100000000000000 : ℝ), (13533734520589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344530817/10000000000 : ℝ)|^2097 ≤ (4365325745309/10000000000000 : ℝ)^1585
        have hw : |(5344530817/10000000000 : ℝ)|=(5344530817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633295487/5000000000 : ℝ)|^2097 ≤ (42813008011693/100000000000000 : ℝ)^1585
        have hw : |(2633295487/5000000000 : ℝ)|=(2633295487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205409601/10000000000 : ℝ)|^2097 ≤ (13533734520589/100000000000000 : ℝ)^1585
        have hw : |(-2205409601/10000000000 : ℝ)|=(2205409601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s8_3 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2178630757/5000000000 : ℝ)*x 0 + (1058243949/2500000000 : ℝ)*x 1 + (1121283223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178630757/5000000000 : ℝ)^2097 ≤ (33317268157297/100000000000000 : ℝ)^1585 := by
    have hnat : (2178630757 : ℕ)^2097*100000000000000^1585 ≤ 33317268157297^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178630757 5000000000 33317268157297 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058243949/2500000000 : ℝ)^2097 ≤ (6413155487083/20000000000000 : ℝ)^1585 := by
    have hnat : (1058243949 : ℕ)^2097*20000000000000^1585 ≤ 6413155487083^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058243949 2500000000 6413155487083 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121283223/2500000000 : ℝ)^2097 ≤ (8654238597639/25000000000000 : ℝ)^1585 := by
    have hnat : (1121283223 : ℕ)^2097*25000000000000^1585 ≤ 8654238597639^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121283223 2500000000 8654238597639 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178630757/5000000000 : ℝ), (1058243949/2500000000 : ℝ), (1121283223/2500000000 : ℝ)] ![(33317268157297/100000000000000 : ℝ), (6413155487083/20000000000000 : ℝ), (8654238597639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178630757/5000000000 : ℝ)|^2097 ≤ (33317268157297/100000000000000 : ℝ)^1585
        have hw : |(2178630757/5000000000 : ℝ)|=(2178630757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058243949/2500000000 : ℝ)|^2097 ≤ (6413155487083/20000000000000 : ℝ)^1585
        have hw : |(1058243949/2500000000 : ℝ)|=(1058243949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121283223/2500000000 : ℝ)|^2097 ≤ (8654238597639/25000000000000 : ℝ)^1585
        have hw : |(1121283223/2500000000 : ℝ)|=(1121283223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s8_4 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141802089/10000000000 : ℝ)*x 0 + (5266906643/10000000000 : ℝ)*x 1 + (1078342921/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141802089/10000000000 : ℝ)^2097 ≤ (2603946515319/20000000000000 : ℝ)^1585 := by
    have hnat : (2141802089 : ℕ)^2097*20000000000000^1585 ≤ 2603946515319^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141802089 10000000000 2603946515319 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266906643/10000000000 : ℝ)^2097 ≤ (21408201551483/50000000000000 : ℝ)^1585 := by
    have hnat : (5266906643 : ℕ)^2097*50000000000000^1585 ≤ 21408201551483^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266906643 10000000000 21408201551483 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078342921/2000000000 : ℝ)^2097 ≤ (44163864304451/100000000000000 : ℝ)^1585 := by
    have hnat : (1078342921 : ℕ)^2097*100000000000000^1585 ≤ 44163864304451^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078342921 2000000000 44163864304451 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141802089/10000000000 : ℝ), (5266906643/10000000000 : ℝ), (1078342921/2000000000 : ℝ)] ![(2603946515319/20000000000000 : ℝ), (21408201551483/50000000000000 : ℝ), (44163864304451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141802089/10000000000 : ℝ)|^2097 ≤ (2603946515319/20000000000000 : ℝ)^1585
        have hw : |(-2141802089/10000000000 : ℝ)|=(2141802089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266906643/10000000000 : ℝ)|^2097 ≤ (21408201551483/50000000000000 : ℝ)^1585
        have hw : |(5266906643/10000000000 : ℝ)|=(5266906643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078342921/2000000000 : ℝ)|^2097 ≤ (44163864304451/100000000000000 : ℝ)^1585
        have hw : |(1078342921/2000000000 : ℝ)|=(1078342921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s8_5 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (664078449/1250000000 : ℝ)*x 0 + (-520071557/2500000000 : ℝ)*x 1 + (673964327/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664078449/1250000000 : ℝ)^2097 ≤ (43308835093679/100000000000000 : ℝ)^1585 := by
    have hnat : (664078449 : ℕ)^2097*100000000000000^1585 ≤ 43308835093679^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664078449 1250000000 43308835093679 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520071557/2500000000 : ℝ)^2097 ≤ (12527300464713/100000000000000 : ℝ)^1585 := by
    have hnat : (520071557 : ℕ)^2097*100000000000000^1585 ≤ 12527300464713^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520071557 2500000000 12527300464713 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673964327/1250000000 : ℝ)^2097 ≤ (22081932211829/50000000000000 : ℝ)^1585 := by
    have hnat : (673964327 : ℕ)^2097*50000000000000^1585 ≤ 22081932211829^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673964327 1250000000 22081932211829 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664078449/1250000000 : ℝ), (-520071557/2500000000 : ℝ), (673964327/1250000000 : ℝ)] ![(43308835093679/100000000000000 : ℝ), (12527300464713/100000000000000 : ℝ), (22081932211829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664078449/1250000000 : ℝ)|^2097 ≤ (43308835093679/100000000000000 : ℝ)^1585
        have hw : |(664078449/1250000000 : ℝ)|=(664078449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-520071557/2500000000 : ℝ)|^2097 ≤ (12527300464713/100000000000000 : ℝ)^1585
        have hw : |(-520071557/2500000000 : ℝ)|=(520071557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673964327/1250000000 : ℝ)|^2097 ≤ (22081932211829/50000000000000 : ℝ)^1585
        have hw : |(673964327/1250000000 : ℝ)|=(673964327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s8_6 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312627609/10000000000 : ℝ)*x 0 + (1078342933/2000000000 : ℝ)*x 1 + (-2080286139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312627609/10000000000 : ℝ)^2097 ≤ (4330883527703/10000000000000 : ℝ)^1585 := by
    have hnat : (5312627609 : ℕ)^2097*10000000000000^1585 ≤ 4330883527703^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312627609 10000000000 4330883527703 10000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078342933/2000000000 : ℝ)^2097 ≤ (44163864954671/100000000000000 : ℝ)^1585 := by
    have hnat : (1078342933 : ℕ)^2097*100000000000000^1585 ≤ 44163864954671^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078342933 2000000000 44163864954671 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080286139/10000000000 : ℝ)^2097 ≤ (3131824938909/25000000000000 : ℝ)^1585 := by
    have hnat : (2080286139 : ℕ)^2097*25000000000000^1585 ≤ 3131824938909^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080286139 10000000000 3131824938909 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312627609/10000000000 : ℝ), (1078342933/2000000000 : ℝ), (-2080286139/10000000000 : ℝ)] ![(4330883527703/10000000000000 : ℝ), (44163864954671/100000000000000 : ℝ), (3131824938909/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312627609/10000000000 : ℝ)|^2097 ≤ (4330883527703/10000000000000 : ℝ)^1585
        have hw : |(5312627609/10000000000 : ℝ)|=(5312627609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078342933/2000000000 : ℝ)|^2097 ≤ (44163864954671/100000000000000 : ℝ)^1585
        have hw : |(1078342933/2000000000 : ℝ)|=(1078342933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080286139/10000000000 : ℝ)|^2097 ≤ (3131824938909/25000000000000 : ℝ)^1585
        have hw : |(-2080286139/10000000000 : ℝ)|=(2080286139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s8_7 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2178635549/5000000000 : ℝ)*x 0 + (179379937/400000000 : ℝ)*x 1 + (423361253/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178635549/5000000000 : ℝ)^2097 ≤ (3331736511267/10000000000000 : ℝ)^1585 := by
    have hnat : (2178635549 : ℕ)^2097*10000000000000^1585 ≤ 3331736511267^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178635549 5000000000 3331736511267 10000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179379937/400000000 : ℝ)^2097 ≤ (2163154736301/6250000000000 : ℝ)^1585 := by
    have hnat : (179379937 : ℕ)^2097*6250000000000^1585 ≤ 2163154736301^1585*400000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179379937 400000000 2163154736301 6250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423361253/1000000000 : ℝ)^2097 ≤ (16036079548309/50000000000000 : ℝ)^1585 := by
    have hnat : (423361253 : ℕ)^2097*50000000000000^1585 ≤ 16036079548309^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423361253 1000000000 16036079548309 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178635549/5000000000 : ℝ), (179379937/400000000 : ℝ), (423361253/1000000000 : ℝ)] ![(3331736511267/10000000000000 : ℝ), (2163154736301/6250000000000 : ℝ), (16036079548309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178635549/5000000000 : ℝ)|^2097 ≤ (3331736511267/10000000000000 : ℝ)^1585
        have hw : |(2178635549/5000000000 : ℝ)|=(2178635549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179379937/400000000 : ℝ)|^2097 ≤ (2163154736301/6250000000000 : ℝ)^1585
        have hw : |(179379937/400000000 : ℝ)|=(179379937/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423361253/1000000000 : ℝ)|^2097 ≤ (16036079548309/50000000000000 : ℝ)^1585
        have hw : |(423361253/1000000000 : ℝ)|=(423361253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1195_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (571/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11421/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14079/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (571/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (571/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (571/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (571/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (571/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (571/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (571/5000 : ℝ) ^ (8387/2048 : ℝ) ≤ (13833760129643109/100000000000000000000 : ℝ) := by
    have hpowers : (571/5000 : ℝ)^8387 ≤ (13833760129643109/100000000000000000000 : ℝ)^2048 := by
      have hnat : (571 : ℕ)^8387*100000000000000000000^2048 ≤ 13833760129643109^2048*5000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        571 5000 13833760129643109 100000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (571/5000 : ℝ)) (X := (13833760129643109/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (88/625 : ℝ) ^ (8387/2048 : ℝ) ≤ (32609561134701173/100000000000000000000 : ℝ) := by
    have hpowers : (88/625 : ℝ)^8387 ≤ (32609561134701173/100000000000000000000 : ℝ)^2048 := by
      have hnat : (88 : ℕ)^8387*100000000000000000000^2048 ≤ 32609561134701173^2048*625^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88 625 32609561134701173 100000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88/625 : ℝ)) (X := (32609561134701173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013833760129643109/50000000000000000000 : ℝ) ≤ (5000337767723331/5000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (50013833760129643109/50000000000000000000 : ℝ)^2048 ≤ (5000337767723331/5000000000000000 : ℝ)^8387 := by
      have hnat : (50013833760129643109 : ℕ)^2048*5000000000000000^8387 ≤ 5000337767723331^8387*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013833760129643109 50000000000000000000 5000337767723331 5000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000337767723331/5000000000000000 : ℝ)) (X := (50013833760129643109/50000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023221660632172141/50000000000000000000 : ℝ) ≤ (10001133888547493/10000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (50023221660632172141/50000000000000000000 : ℝ)^2048 ≤ (10001133888547493/10000000000000000 : ℝ)^8387 := by
      have hnat : (50023221660632172141 : ℕ)^2048*10000000000000000^8387 ≤ 10001133888547493^8387*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023221660632172141 50000000000000000000 10001133888547493 10000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001133888547493/10000000000000000 : ℝ)) (X := (50023221660632172141/50000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032609561134701173/50000000000000000000 : ℝ) ≤ (2500398060412081/2500000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (50032609561134701173/50000000000000000000 : ℝ)^2048 ≤ (2500398060412081/2500000000000000 : ℝ)^8387 := by
      have hnat : (50032609561134701173 : ℕ)^2048*2500000000000000^8387 ≤ 2500398060412081^8387*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032609561134701173 50000000000000000000 2500398060412081 2500000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500398060412081/2500000000000000 : ℝ)) (X := (50032609561134701173/50000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13833760129643109/100000000000000000000 : ℝ) ≤ ((332391601743314261/332500000000000000 : ℝ)+2*(458353100831/266000000000000 : ℝ)*(571/5000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (332391601743314261/332500000000000000 : ℝ)+2*(458353100831/266000000000000 : ℝ)*(571/5000 : ℝ)=(5000337767723331/5000000000000000 : ℝ) by norm_num, show 1+2*(13833760129643109/100000000000000000000 : ℝ)=(50013833760129643109/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32609561134701173/100000000000000000000 : ℝ)+(13833760129643109/100000000000000000000 : ℝ) ≤ ((332391601743314261/332500000000000000 : ℝ)+(458353100831/266000000000000 : ℝ)*((88/625 : ℝ)+(571/5000 : ℝ)))^(8387/2048 : ℝ) := by
    rw [show (332391601743314261/332500000000000000 : ℝ)+(458353100831/266000000000000 : ℝ)*((88/625 : ℝ)+(571/5000 : ℝ))=(10001133888547493/10000000000000000 : ℝ) by norm_num, show 1+(32609561134701173/100000000000000000000 : ℝ)+(13833760129643109/100000000000000000000 : ℝ)=(50023221660632172141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32609561134701173/100000000000000000000 : ℝ) ≤ ((332391601743314261/332500000000000000 : ℝ)+2*(458353100831/266000000000000 : ℝ)*(88/625 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (332391601743314261/332500000000000000 : ℝ)+2*(458353100831/266000000000000 : ℝ)*(88/625 : ℝ)=(2500398060412081/2500000000000000 : ℝ) by norm_num, show 1+2*(32609561134701173/100000000000000000000 : ℝ)=(50032609561134701173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (332391601743314261/332500000000000000 : ℝ)*(X 1 0+X 2 0)+(458353100831/266000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (571/5000 : ℝ)) (hi := (88/625 : ℝ)) (c := (332391601743314261/332500000000000000 : ℝ)) (alpha := (458353100831/266000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (332391601743314261/332500000000000000 : ℝ)*(X 0 1+X 2 1)+(458353100831/266000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (571/5000 : ℝ)) (hi := (88/625 : ℝ)) (c := (332391601743314261/332500000000000000 : ℝ)) (alpha := (458353100831/266000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (332391601743314261/332500000000000000 : ℝ)*(X 0 2+X 1 2)+(458353100831/266000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (571/5000 : ℝ)) (hi := (88/625 : ℝ)) (c := (332391601743314261/332500000000000000 : ℝ)) (alpha := (458353100831/266000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2141797601/10000000000 : ℝ)*X 0 0+(269601561/500000000 : ℝ)*X 0 1+(2633295487/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344530817/10000000000 : ℝ)*X 1 0+(-551352401/2500000000 : ℝ)*X 1 1+(1316647743/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344530817/10000000000 : ℝ)*X 2 0+(2633295487/5000000000 : ℝ)*X 2 1+(-2205409601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178630757/5000000000 : ℝ)*X 0 0+(1058243949/2500000000 : ℝ)*X 0 1+(1121283223/2500000000 : ℝ)*X 0 2+(2178630757/5000000000 : ℝ)*X 1 0+(1058243949/2500000000 : ℝ)*X 1 1+(1121283223/2500000000 : ℝ)*X 1 2+(2178630757/5000000000 : ℝ)*X 2 0+(1058243949/2500000000 : ℝ)*X 2 1+(1121283223/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2141802089/10000000000 : ℝ)*X 0 0+(5266906643/10000000000 : ℝ)*X 0 1+(1078342921/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664078449/1250000000 : ℝ)*X 1 0+(-520071557/2500000000 : ℝ)*X 1 1+(673964327/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312627609/10000000000 : ℝ)*X 2 0+(1078342933/2000000000 : ℝ)*X 2 1+(-2080286139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178635549/5000000000 : ℝ)*X 0 0+(179379937/400000000 : ℝ)*X 0 1+(423361253/1000000000 : ℝ)*X 0 2+(2178635549/5000000000 : ℝ)*X 1 0+(179379937/400000000 : ℝ)*X 1 1+(423361253/1000000000 : ℝ)*X 1 2+(2178635549/5000000000 : ℝ)*X 2 0+(179379937/400000000 : ℝ)*X 2 1+(423361253/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10220246295639412560064623/1039062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (960106027/50000000000000 : ℝ)*(base19) + (1787110303/100000000000000 : ℝ)*(base23) + (71136641/100000000000000 : ℝ)*(lower2) + (245737461/100000000000000 : ℝ)*(upper3) + (152340027/100000000000000 : ℝ)*(upper5) + (5968933588749223/100000000000000 : ℝ)*(major0) + (5968933588749223/100000000000000 : ℝ)*(major1) + (5968933588749223/100000000000000 : ℝ)*(major2) + (3985989149897631/50000000000000 : ℝ)*(sp0) + (996503656741419/12500000000000 : ℝ)*(sp1) + (7972029387033103/100000000000000 : ℝ)*(sp2) + (1982903652583701/50000000000000 : ℝ)*(sp3) + (3304646759/6250000000000 : ℝ)*(sp4) + (14185160039/50000000000000 : ℝ)*(sp7) + (99145891887187/2500000000000 : ℝ)*(f.failure) + (3986015587071703/50000000000000 : ℝ)*(f.sum) + (79550706915887/13300000000000000000000000000 : ℝ)*base66 + (551930844696539547/33250000000000000000000000000000 : ℝ)*base68 + (260757032225039547/33250000000000000000000000000000 : ℝ)*base70 + (219479638473039547/33250000000000000000000000000000 : ℝ)*base72 + (23801649397887/13300000000000000000000000000 : ℝ)*base74 + (630530968727960453/33250000000000000000000000000000 : ℝ)*base75 + (220016977325789547/33250000000000000000000000000000 : ℝ)*base78 + (440829696689039547/33250000000000000000000000000000 : ℝ)*base80 + (48714776974987/13300000000000000000000000000 : ℝ)*base82 + (239411/15625000000000000000 : ℝ)*base89 + (239411/15625000000000000000 : ℝ)*base91 + (239411/15625000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42681727778870365487669571/3325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (760842249/100000000000000 : ℝ)*(base19) + (93712743/6250000000000 : ℝ)*(base23) + (1543327/625000000000 : ℝ)*(lower1) + (56249503/50000000000000 : ℝ)*(upper3) + (63339077/20000000000000 : ℝ)*(lower4) + (103762581/50000000000000 : ℝ)*(upper5) + (1199814805007263/20000000000000 : ℝ)*(major0) + (1199814805007263/20000000000000 : ℝ)*(major1) + (1199814805007263/20000000000000 : ℝ)*(major2) + (19450718599/100000000000000 : ℝ)*(sp2) + (801228625605761/10000000000000 : ℝ)*(sp4) + (6259598043137/78125000000 : ℝ)*(sp5) + (4006132652967561/50000000000000 : ℝ)*(sp6) + (249116335383/6250000000 : ℝ)*(sp7) + (249116335383/6250000000 : ℝ)*(f.failure) + (801228625605761/10000000000000 : ℝ)*(f.sum) + (15795443086953/2660000000000000000000000000 : ℝ)*base65 + (283754882763581107/6650000000000000000000000000000 : ℝ)*base68 + (5412847283418893/6650000000000000000000000000000 : ℝ)*base69 + (470842868867918893/6650000000000000000000000000000 : ℝ)*base71 + (6761732531647/2660000000000000000000000000 : ℝ)*base74 + (653078848988081107/6650000000000000000000000000000 : ℝ)*base76 + (3132837387268893/6650000000000000000000000000000 : ℝ)*base77 + (15271768168518893/6650000000000000000000000000000 : ℝ)*base79 + (9135068201173/2660000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (17/312500000000000000 : ℝ)*base89 + (17/312500000000000000 : ℝ)*base91 + (17/312500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1195_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (571/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1195_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1195_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1195_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1195_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1195_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1195_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
