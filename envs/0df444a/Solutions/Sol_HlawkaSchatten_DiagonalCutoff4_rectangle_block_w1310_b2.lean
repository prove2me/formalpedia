-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1310_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:39:19.988802+00:00
-- url     : https://prove2.me/submissions/cad41db4-a32c-4b1e-b6d2-914a15f7622f

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
theorem support_rectangle_w1310_s6_0 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-129496007/625000000 : ℝ)*x 0 + (1353596223/2500000000 : ℝ)*x 1 + (655443419/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129496007/625000000 : ℝ)^2135 ≤ (6305026323087/50000000000000 : ℝ)^1623 := by
    have hnat : (129496007 : ℕ)^2135*50000000000000^1623 ≤ 6305026323087^1623*625000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129496007 625000000 6305026323087 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353596223/2500000000 : ℝ)^2135 ≤ (44616258723059/100000000000000 : ℝ)^1623 := by
    have hnat : (1353596223 : ℕ)^2135*100000000000000^1623 ≤ 44616258723059^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353596223 2500000000 44616258723059 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655443419/1250000000 : ℝ)^2135 ≤ (1069342215293/2500000000000 : ℝ)^1623 := by
    have hnat : (655443419 : ℕ)^2135*2500000000000^1623 ≤ 1069342215293^1623*1250000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655443419 1250000000 1069342215293 2500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129496007/625000000 : ℝ), (1353596223/2500000000 : ℝ), (655443419/1250000000 : ℝ)] ![(6305026323087/50000000000000 : ℝ), (44616258723059/100000000000000 : ℝ), (1069342215293/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129496007/625000000 : ℝ)|^2135 ≤ (6305026323087/50000000000000 : ℝ)^1623
        have hw : |(-129496007/625000000 : ℝ)|=(129496007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353596223/2500000000 : ℝ)|^2135 ≤ (44616258723059/100000000000000 : ℝ)^1623
        have hw : |(1353596223/2500000000 : ℝ)|=(1353596223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655443419/1250000000 : ℝ)|^2135 ≤ (1069342215293/2500000000000 : ℝ)^1623
        have hw : |(655443419/1250000000 : ℝ)|=(655443419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s6_1 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668691509/1250000000 : ℝ)*x 0 + (-2159006053/10000000000 : ℝ)*x 1 + (1048709419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668691509/1250000000 : ℝ)^2135 ≤ (43914595519117/100000000000000 : ℝ)^1623 := by
    have hnat : (668691509 : ℕ)^2135*100000000000000^1623 ≤ 43914595519117^1623*1250000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668691509 1250000000 43914595519117 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2159006053/10000000000 : ℝ)^2135 ≤ (1331171861111/10000000000000 : ℝ)^1623 := by
    have hnat : (2159006053 : ℕ)^2135*10000000000000^1623 ≤ 1331171861111^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159006053 10000000000 1331171861111 10000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048709419/2000000000 : ℝ)^2135 ≤ (5346710731739/12500000000000 : ℝ)^1623 := by
    have hnat : (1048709419 : ℕ)^2135*12500000000000^1623 ≤ 5346710731739^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048709419 2000000000 5346710731739 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668691509/1250000000 : ℝ), (-2159006053/10000000000 : ℝ), (1048709419/2000000000 : ℝ)] ![(43914595519117/100000000000000 : ℝ), (1331171861111/10000000000000 : ℝ), (5346710731739/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668691509/1250000000 : ℝ)|^2135 ≤ (43914595519117/100000000000000 : ℝ)^1623
        have hw : |(668691509/1250000000 : ℝ)|=(668691509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2159006053/10000000000 : ℝ)|^2135 ≤ (1331171861111/10000000000000 : ℝ)^1623
        have hw : |(-2159006053/10000000000 : ℝ)|=(2159006053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048709419/2000000000 : ℝ)|^2135 ≤ (5346710731739/12500000000000 : ℝ)^1623
        have hw : |(1048709419/2000000000 : ℝ)|=(1048709419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s6_2 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349531561/10000000000 : ℝ)*x 0 + (327721707/625000000 : ℝ)*x 1 + (-2159006447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349531561/10000000000 : ℝ)^2135 ≤ (43914590000969/100000000000000 : ℝ)^1623 := by
    have hnat : (5349531561 : ℕ)^2135*100000000000000^1623 ≤ 43914590000969^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349531561 10000000000 43914590000969 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327721707/625000000 : ℝ)^2135 ≤ (42773688182489/100000000000000 : ℝ)^1623 := by
    have hnat : (327721707 : ℕ)^2135*100000000000000^1623 ≤ 42773688182489^1623*625000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327721707 625000000 42773688182489 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2159006447/10000000000 : ℝ)^2135 ≤ (2662344361347/20000000000000 : ℝ)^1623 := by
    have hnat : (2159006447 : ℕ)^2135*20000000000000^1623 ≤ 2662344361347^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159006447 10000000000 2662344361347 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349531561/10000000000 : ℝ), (327721707/625000000 : ℝ), (-2159006447/10000000000 : ℝ)] ![(43914590000969/100000000000000 : ℝ), (42773688182489/100000000000000 : ℝ), (2662344361347/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349531561/10000000000 : ℝ)|^2135 ≤ (43914590000969/100000000000000 : ℝ)^1623
        have hw : |(5349531561/10000000000 : ℝ)|=(5349531561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327721707/625000000 : ℝ)|^2135 ≤ (42773688182489/100000000000000 : ℝ)^1623
        have hw : |(327721707/625000000 : ℝ)|=(327721707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2159006447/10000000000 : ℝ)|^2135 ≤ (2662344361347/20000000000000 : ℝ)^1623
        have hw : |(-2159006447/10000000000 : ℝ)|=(2159006447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s6_3 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4335053201/10000000000 : ℝ)*x 0 + (1040426551/2500000000 : ℝ)*x 1 + (2257617397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335053201/10000000000 : ℝ)^2135 ≤ (6660530286531/20000000000000 : ℝ)^1623 := by
    have hnat : (4335053201 : ℕ)^2135*20000000000000^1623 ≤ 6660530286531^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335053201 10000000000 6660530286531 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040426551/2500000000 : ℝ)^2135 ≤ (31562020981569/100000000000000 : ℝ)^1623 := by
    have hnat : (1040426551 : ℕ)^2135*100000000000000^1623 ≤ 31562020981569^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040426551 2500000000 31562020981569 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257617397/5000000000 : ℝ)^2135 ≤ (35135327571811/100000000000000 : ℝ)^1623 := by
    have hnat : (2257617397 : ℕ)^2135*100000000000000^1623 ≤ 35135327571811^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257617397 5000000000 35135327571811 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335053201/10000000000 : ℝ), (1040426551/2500000000 : ℝ), (2257617397/5000000000 : ℝ)] ![(6660530286531/20000000000000 : ℝ), (31562020981569/100000000000000 : ℝ), (35135327571811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335053201/10000000000 : ℝ)|^2135 ≤ (6660530286531/20000000000000 : ℝ)^1623
        have hw : |(4335053201/10000000000 : ℝ)|=(4335053201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040426551/2500000000 : ℝ)|^2135 ≤ (31562020981569/100000000000000 : ℝ)^1623
        have hw : |(1040426551/2500000000 : ℝ)|=(1040426551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257617397/5000000000 : ℝ)|^2135 ≤ (35135327571811/100000000000000 : ℝ)^1623
        have hw : |(2257617397/5000000000 : ℝ)|=(2257617397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s6_4 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1035974457/5000000000 : ℝ)*x 0 + (2622078739/5000000000 : ℝ)*x 1 + (5413771429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035974457/5000000000 : ℝ)^2135 ≤ (1576269392513/12500000000000 : ℝ)^1623 := by
    have hnat : (1035974457 : ℕ)^2135*12500000000000^1623 ≤ 1576269392513^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035974457 5000000000 1576269392513 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622078739/5000000000 : ℝ)^2135 ≤ (42780235853389/100000000000000 : ℝ)^1623 := by
    have hnat : (2622078739 : ℕ)^2135*100000000000000^1623 ≤ 42780235853389^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622078739 5000000000 42780235853389 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413771429/10000000000 : ℝ)^2135 ≤ (22304804496647/50000000000000 : ℝ)^1623 := by
    have hnat : (5413771429 : ℕ)^2135*50000000000000^1623 ≤ 22304804496647^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413771429 10000000000 22304804496647 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1035974457/5000000000 : ℝ), (2622078739/5000000000 : ℝ), (5413771429/10000000000 : ℝ)] ![(1576269392513/12500000000000 : ℝ), (42780235853389/100000000000000 : ℝ), (22304804496647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1035974457/5000000000 : ℝ)|^2135 ≤ (1576269392513/12500000000000 : ℝ)^1623
        have hw : |(-1035974457/5000000000 : ℝ)|=(1035974457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622078739/5000000000 : ℝ)|^2135 ≤ (42780235853389/100000000000000 : ℝ)^1623
        have hw : |(2622078739/5000000000 : ℝ)|=(2622078739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413771429/10000000000 : ℝ)|^2135 ≤ (22304804496647/50000000000000 : ℝ)^1623
        have hw : |(5413771429/10000000000 : ℝ)|=(5413771429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s6_5 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305694797/10000000000 : ℝ)*x 0 + (-31074721/156250000 : ℝ)*x 1 + (5413771439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305694797/10000000000 : ℝ)^2135 ≤ (43441821901637/100000000000000 : ℝ)^1623 := by
    have hnat : (5305694797 : ℕ)^2135*100000000000000^1623 ≤ 43441821901637^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305694797 10000000000 43441821901637 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31074721/156250000 : ℝ)^2135 ≤ (11948568979221/100000000000000 : ℝ)^1623 := by
    have hnat : (31074721 : ℕ)^2135*100000000000000^1623 ≤ 11948568979221^1623*156250000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31074721 156250000 11948568979221 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413771439/10000000000 : ℝ)^2135 ≤ (44609609101689/100000000000000 : ℝ)^1623 := by
    have hnat : (5413771439 : ℕ)^2135*100000000000000^1623 ≤ 44609609101689^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413771439 10000000000 44609609101689 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305694797/10000000000 : ℝ), (-31074721/156250000 : ℝ), (5413771439/10000000000 : ℝ)] ![(43441821901637/100000000000000 : ℝ), (11948568979221/100000000000000 : ℝ), (44609609101689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305694797/10000000000 : ℝ)|^2135 ≤ (43441821901637/100000000000000 : ℝ)^1623
        have hw : |(5305694797/10000000000 : ℝ)|=(5305694797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31074721/156250000 : ℝ)|^2135 ≤ (11948568979221/100000000000000 : ℝ)^1623
        have hw : |(-31074721/156250000 : ℝ)|=(31074721/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413771439/10000000000 : ℝ)|^2135 ≤ (44609609101689/100000000000000 : ℝ)^1623
        have hw : |(5413771439/10000000000 : ℝ)|=(5413771439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s6_6 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305694837/10000000000 : ℝ)*x 0 + (5413771403/10000000000 : ℝ)*x 1 + (-1988782139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305694837/10000000000 : ℝ)^2135 ≤ (21720911166233/50000000000000 : ℝ)^1623 := by
    have hnat : (5305694837 : ℕ)^2135*50000000000000^1623 ≤ 21720911166233^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305694837 10000000000 21720911166233 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413771403/10000000000 : ℝ)^2135 ≤ (11152402177867/25000000000000 : ℝ)^1623 := by
    have hnat : (5413771403 : ℕ)^2135*25000000000000^1623 ≤ 11152402177867^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413771403 10000000000 11152402177867 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1988782139/10000000000 : ℝ)^2135 ≤ (1493571117463/12500000000000 : ℝ)^1623 := by
    have hnat : (1988782139 : ℕ)^2135*12500000000000^1623 ≤ 1493571117463^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988782139 10000000000 1493571117463 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305694837/10000000000 : ℝ), (5413771403/10000000000 : ℝ), (-1988782139/10000000000 : ℝ)] ![(21720911166233/50000000000000 : ℝ), (11152402177867/25000000000000 : ℝ), (1493571117463/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305694837/10000000000 : ℝ)|^2135 ≤ (21720911166233/50000000000000 : ℝ)^1623
        have hw : |(5305694837/10000000000 : ℝ)|=(5305694837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413771403/10000000000 : ℝ)|^2135 ≤ (11152402177867/25000000000000 : ℝ)^1623
        have hw : |(5413771403/10000000000 : ℝ)|=(5413771403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1988782139/10000000000 : ℝ)|^2135 ≤ (1493571117463/12500000000000 : ℝ)^1623
        have hw : |(-1988782139/10000000000 : ℝ)|=(1988782139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s6_7 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4335079439/10000000000 : ℝ)*x 0 + (451397161/1000000000 : ℝ)*x 1 + (4162975603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335079439/10000000000 : ℝ)^2135 ≤ (104071614327/312500000000 : ℝ)^1623 := by
    have hnat : (4335079439 : ℕ)^2135*312500000000^1623 ≤ 104071614327^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335079439 10000000000 104071614327 312500000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451397161/1000000000 : ℝ)^2135 ≤ (8780599452847/25000000000000 : ℝ)^1623 := by
    have hnat : (451397161 : ℕ)^2135*25000000000000^1623 ≤ 8780599452847^1623*1000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451397161 1000000000 8780599452847 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4162975603/10000000000 : ℝ)^2135 ≤ (31574685590689/100000000000000 : ℝ)^1623 := by
    have hnat : (4162975603 : ℕ)^2135*100000000000000^1623 ≤ 31574685590689^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162975603 10000000000 31574685590689 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335079439/10000000000 : ℝ), (451397161/1000000000 : ℝ), (4162975603/10000000000 : ℝ)] ![(104071614327/312500000000 : ℝ), (8780599452847/25000000000000 : ℝ), (31574685590689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335079439/10000000000 : ℝ)|^2135 ≤ (104071614327/312500000000 : ℝ)^1623
        have hw : |(4335079439/10000000000 : ℝ)|=(4335079439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451397161/1000000000 : ℝ)|^2135 ≤ (8780599452847/25000000000000 : ℝ)^1623
        have hw : |(451397161/1000000000 : ℝ)|=(451397161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4162975603/10000000000 : ℝ)|^2135 ≤ (31574685590689/100000000000000 : ℝ)^1623
        have hw : |(4162975603/10000000000 : ℝ)|=(4162975603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1310_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11071/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14687/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14697/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11061/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14697/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11061/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14697/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11061/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14697/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11061/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14697/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11061/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14697/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11061/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11061/100000 : ℝ) ^ (4269/1024 : ℝ) ≤ (10318845597842769/100000000000000000000 : ℝ) := by
    have hpowers : (11061/100000 : ℝ)^4269 ≤ (10318845597842769/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11061 : ℕ)^4269*100000000000000000000^1024 ≤ 10318845597842769^1024*100000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11061 100000 10318845597842769 100000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11061/100000 : ℝ)) (X := (10318845597842769/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14697/100000 : ℝ) ^ (4269/1024 : ℝ) ≤ (210912337805893/625000000000000000 : ℝ) := by
    have hpowers : (14697/100000 : ℝ)^4269 ≤ (210912337805893/625000000000000000 : ℝ)^1024 := by
      have hnat : (14697 : ℕ)^4269*625000000000000000^1024 ≤ 210912337805893^1024*100000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14697 100000 210912337805893 625000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14697/100000 : ℝ)) (X := (210912337805893/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010318845597842769/50000000000000000000 : ℝ) ≤ (5000247497521449/5000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (50010318845597842769/50000000000000000000 : ℝ)^1024 ≤ (5000247497521449/5000000000000000 : ℝ)^4269 := by
      have hnat : (50010318845597842769 : ℕ)^1024*5000000000000000^4269 ≤ 5000247497521449^4269*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010318845597842769 50000000000000000000 5000247497521449 5000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000247497521449/5000000000000000 : ℝ)) (X := (50010318845597842769/50000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044064819646785649/100000000000000000000 : ℝ) ≤ (10001056800665071/10000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (100044064819646785649/100000000000000000000 : ℝ)^1024 ≤ (10001056800665071/10000000000000000 : ℝ)^4269 := by
      have hnat : (100044064819646785649 : ℕ)^1024*10000000000000000^4269 ≤ 10001056800665071^4269*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044064819646785649 100000000000000000000 10001056800665071 10000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001056800665071/10000000000000000 : ℝ)) (X := (100044064819646785649/100000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (312710912337805893/312500000000000000 : ℝ) ≤ (2500404651571811/2500000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (312710912337805893/312500000000000000 : ℝ)^1024 ≤ (2500404651571811/2500000000000000 : ℝ)^4269 := by
      have hnat : (312710912337805893 : ℕ)^1024*2500000000000000^4269 ≤ 2500404651571811^4269*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312710912337805893 312500000000000000 2500404651571811 2500000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500404651571811/2500000000000000 : ℝ)) (X := (312710912337805893/312500000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10318845597842769/100000000000000000000 : ℝ) ≤ ((2019409529889014779/2020000000000000000 : ℝ)+2*(561805622173/363600000000000 : ℝ)*(11061/100000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (2019409529889014779/2020000000000000000 : ℝ)+2*(561805622173/363600000000000 : ℝ)*(11061/100000 : ℝ)=(5000247497521449/5000000000000000 : ℝ) by norm_num, show 1+2*(10318845597842769/100000000000000000000 : ℝ)=(50010318845597842769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(210912337805893/625000000000000000 : ℝ)+(10318845597842769/100000000000000000000 : ℝ) ≤ ((2019409529889014779/2020000000000000000 : ℝ)+(561805622173/363600000000000 : ℝ)*((14697/100000 : ℝ)+(11061/100000 : ℝ)))^(4269/1024 : ℝ) := by
    rw [show (2019409529889014779/2020000000000000000 : ℝ)+(561805622173/363600000000000 : ℝ)*((14697/100000 : ℝ)+(11061/100000 : ℝ))=(10001056800665071/10000000000000000 : ℝ) by norm_num, show 1+(210912337805893/625000000000000000 : ℝ)+(10318845597842769/100000000000000000000 : ℝ)=(100044064819646785649/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(210912337805893/625000000000000000 : ℝ) ≤ ((2019409529889014779/2020000000000000000 : ℝ)+2*(561805622173/363600000000000 : ℝ)*(14697/100000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (2019409529889014779/2020000000000000000 : ℝ)+2*(561805622173/363600000000000 : ℝ)*(14697/100000 : ℝ)=(2500404651571811/2500000000000000 : ℝ) by norm_num, show 1+2*(210912337805893/625000000000000000 : ℝ)=(312710912337805893/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2019409529889014779/2020000000000000000 : ℝ)*(X 1 0+X 2 0)+(561805622173/363600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (11061/100000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (2019409529889014779/2020000000000000000 : ℝ)) (alpha := (561805622173/363600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2019409529889014779/2020000000000000000 : ℝ)*(X 0 1+X 2 1)+(561805622173/363600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (11061/100000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (2019409529889014779/2020000000000000000 : ℝ)) (alpha := (561805622173/363600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2019409529889014779/2020000000000000000 : ℝ)*(X 0 2+X 1 2)+(561805622173/363600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (11061/100000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (2019409529889014779/2020000000000000000 : ℝ)) (alpha := (561805622173/363600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-129496007/625000000 : ℝ)*X 0 0+(1353596223/2500000000 : ℝ)*X 0 1+(655443419/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668691509/1250000000 : ℝ)*X 1 0+(-2159006053/10000000000 : ℝ)*X 1 1+(1048709419/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349531561/10000000000 : ℝ)*X 2 0+(327721707/625000000 : ℝ)*X 2 1+(-2159006447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4335053201/10000000000 : ℝ)*X 0 0+(1040426551/2500000000 : ℝ)*X 0 1+(2257617397/5000000000 : ℝ)*X 0 2+(4335053201/10000000000 : ℝ)*X 1 0+(1040426551/2500000000 : ℝ)*X 1 1+(2257617397/5000000000 : ℝ)*X 1 2+(4335053201/10000000000 : ℝ)*X 2 0+(1040426551/2500000000 : ℝ)*X 2 1+(2257617397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1035974457/5000000000 : ℝ)*X 0 0+(2622078739/5000000000 : ℝ)*X 0 1+(5413771429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305694797/10000000000 : ℝ)*X 1 0+(-31074721/156250000 : ℝ)*X 1 1+(5413771439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305694837/10000000000 : ℝ)*X 2 0+(5413771403/10000000000 : ℝ)*X 2 1+(-1988782139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4335079439/10000000000 : ℝ)*X 0 0+(451397161/1000000000 : ℝ)*X 0 1+(4162975603/10000000000 : ℝ)*X 0 2+(4335079439/10000000000 : ℝ)*X 1 0+(451397161/1000000000 : ℝ)*X 1 1+(4162975603/10000000000 : ℝ)*X 1 2+(4335079439/10000000000 : ℝ)*X 2 0+(451397161/1000000000 : ℝ)*X 2 1+(4162975603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (103690553010941555302746043/15150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (588704819/50000000000000 : ℝ)*(base19) + (761869271/100000000000000 : ℝ)*(base23) + (8921639/20000000000000 : ℝ)*(upper3) + (24806359/20000000000000 : ℝ)*(lower4) + (434111049637087/10000000000000 : ℝ)*(major0) + (434111049637087/10000000000000 : ℝ)*(major1) + (434111049637087/10000000000000 : ℝ)*(major2) + (5853544892833487/100000000000000 : ℝ)*(sp0) + (5853565156838361/100000000000000 : ℝ)*(sp1) + (146338870076029/2500000000000 : ℝ)*(sp2) + (1414320623365209/50000000000000 : ℝ)*(sp3) + (1340088407/6250000000000 : ℝ)*(sp4) + (10769337567/100000000000000 : ℝ)*(sp6) + (527344851/4000000000000 : ℝ)*(sp7) + (707163607587923/25000000000000 : ℝ)*(f.failure) + (5853566334247999/100000000000000 : ℝ)*(f.sum) + (7740188269907/1818000000000000000000000000 : ℝ)*base66 + (1543874643416528957/181800000000000000000000000000000 : ℝ)*base67 + (1914427288627928957/181800000000000000000000000000000 : ℝ)*base69 + (1346060256554871043/181800000000000000000000000000000 : ℝ)*base72 + (898157374151/1818000000000000000000000000 : ℝ)*base74 + (1867385225486528957/181800000000000000000000000000000 : ℝ)*base75 + (2461799219960528957/181800000000000000000000000000000 : ℝ)*base77 + (5119051766130728957/181800000000000000000000000000000 : ℝ)*base79 + (10795942942061/1818000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (363207/25000000000000000000 : ℝ)*base90 + (363207/25000000000000000000 : ℝ)*base92 + (363207/25000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2384121603921840773300049677/303000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1365960593/100000000000000 : ℝ)*(base19) + (770482143/50000000000000 : ℝ)*(base23) + (155194581/100000000000000 : ℝ)*(upper3) + (59220547/100000000000000 : ℝ)*(lower4) + (21185461/12500000000000 : ℝ)*(upper5) + (4372388091492607/100000000000000 : ℝ)*(major0) + (4372388091492607/100000000000000 : ℝ)*(major1) + (4372388091492607/100000000000000 : ℝ)*(major2) + (5606271079/20000000000000 : ℝ)*(sp1) + (30323875831/100000000000000 : ℝ)*(sp2) + (5895741104255513/100000000000000 : ℝ)*(sp4) + (235828468277581/4000000000000 : ℝ)*(sp5) + (1473927309853849/25000000000000 : ℝ)*(sp6) + (2849034816450091/100000000000000 : ℝ)*(sp7) + (2849034816450091/100000000000000 : ℝ)*(f.failure) + (5895741104255513/100000000000000 : ℝ)*(f.sum) + (128920890676951/18180000000000000000000000000 : ℝ)*base65 + (2185074020351300323/1818000000000000000000000000000000 : ℝ)*base68 + (3093534018780699677/1818000000000000000000000000000000 : ℝ)*base69 + (15902633228028699677/1818000000000000000000000000000000 : ℝ)*base71 + (48493426809511/18180000000000000000000000000 : ℝ)*base73 + (1114983129233300323/1818000000000000000000000000000000 : ℝ)*base76 + (1306977962375300323/1818000000000000000000000000000000 : ℝ)*base78 + (17170594674779300323/1818000000000000000000000000000000 : ℝ)*base80 + (77065725712051/18180000000000000000000000000 : ℝ)*base81 + (393119/100000000000000000000 : ℝ)*base90 + (393119/100000000000000000000 : ℝ)*base92 + (393119/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1310_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1310_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1310_s7_0 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-517986191/2500000000 : ℝ)*x 0 + (2707149003/5000000000 : ℝ)*x 1 + (1048725733/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517986191/2500000000 : ℝ)^2135 ≤ (12610121914819/100000000000000 : ℝ)^1623 := by
    have hnat : (517986191 : ℕ)^2135*100000000000000^1623 ≤ 12610121914819^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517986191 2500000000 12610121914819 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707149003/5000000000 : ℝ)^2135 ≤ (22307658446997/50000000000000 : ℝ)^1623 := by
    have hnat : (2707149003 : ℕ)^2135*50000000000000^1623 ≤ 22307658446997^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707149003 5000000000 22307658446997 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048725733/2000000000 : ℝ)^2135 ≤ (42774561164919/100000000000000 : ℝ)^1623 := by
    have hnat : (1048725733 : ℕ)^2135*100000000000000^1623 ≤ 42774561164919^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048725733 2000000000 42774561164919 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-517986191/2500000000 : ℝ), (2707149003/5000000000 : ℝ), (1048725733/2000000000 : ℝ)] ![(12610121914819/100000000000000 : ℝ), (22307658446997/50000000000000 : ℝ), (42774561164919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-517986191/2500000000 : ℝ)|^2135 ≤ (12610121914819/100000000000000 : ℝ)^1623
        have hw : |(-517986191/2500000000 : ℝ)|=(517986191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707149003/5000000000 : ℝ)|^2135 ≤ (22307658446997/50000000000000 : ℝ)^1623
        have hw : |(2707149003/5000000000 : ℝ)|=(2707149003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048725733/2000000000 : ℝ)|^2135 ≤ (42774561164919/100000000000000 : ℝ)^1623
        have hw : |(1048725733/2000000000 : ℝ)|=(1048725733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s7_1 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674755229/5000000000 : ℝ)*x 0 + (-2158927223/10000000000 : ℝ)*x 1 + (1310907107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674755229/5000000000 : ℝ)^2135 ≤ (1097859052891/2500000000000 : ℝ)^1623 := by
    have hnat : (2674755229 : ℕ)^2135*2500000000000^1623 ≤ 1097859052891^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674755229 5000000000 1097859052891 2500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2158927223/10000000000 : ℝ)^2135 ≤ (13311079246411/100000000000000 : ℝ)^1623 := by
    have hnat : (2158927223 : ℕ)^2135*100000000000000^1623 ≤ 13311079246411^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158927223 10000000000 13311079246411 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310907107/2500000000 : ℝ)^2135 ≤ (21387279310857/50000000000000 : ℝ)^1623 := by
    have hnat : (1310907107 : ℕ)^2135*50000000000000^1623 ≤ 21387279310857^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310907107 2500000000 21387279310857 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674755229/5000000000 : ℝ), (-2158927223/10000000000 : ℝ), (1310907107/2500000000 : ℝ)] ![(1097859052891/2500000000000 : ℝ), (13311079246411/100000000000000 : ℝ), (21387279310857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674755229/5000000000 : ℝ)|^2135 ≤ (1097859052891/2500000000000 : ℝ)^1623
        have hw : |(2674755229/5000000000 : ℝ)|=(2674755229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2158927223/10000000000 : ℝ)|^2135 ≤ (13311079246411/100000000000000 : ℝ)^1623
        have hw : |(-2158927223/10000000000 : ℝ)|=(2158927223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310907107/2500000000 : ℝ)|^2135 ≤ (21387279310857/50000000000000 : ℝ)^1623
        have hw : |(1310907107/2500000000 : ℝ)|=(1310907107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s7_2 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674754989/5000000000 : ℝ)*x 0 + (262181433/500000000 : ℝ)*x 1 + (-539731889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674754989/5000000000 : ℝ)^2135 ≤ (43914356932259/100000000000000 : ℝ)^1623 := by
    have hnat : (2674754989 : ℕ)^2135*100000000000000^1623 ≤ 43914356932259^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674754989 5000000000 43914356932259 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262181433/500000000 : ℝ)^2135 ≤ (8554912222253/20000000000000 : ℝ)^1623 := by
    have hnat : (262181433 : ℕ)^2135*20000000000000^1623 ≤ 8554912222253^1623*500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262181433 500000000 8554912222253 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539731889/2500000000 : ℝ)^2135 ≤ (13311081947251/100000000000000 : ℝ)^1623 := by
    have hnat : (539731889 : ℕ)^2135*100000000000000^1623 ≤ 13311081947251^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539731889 2500000000 13311081947251 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674754989/5000000000 : ℝ), (262181433/500000000 : ℝ), (-539731889/2500000000 : ℝ)] ![(43914356932259/100000000000000 : ℝ), (8554912222253/20000000000000 : ℝ), (13311081947251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674754989/5000000000 : ℝ)|^2135 ≤ (43914356932259/100000000000000 : ℝ)^1623
        have hw : |(2674754989/5000000000 : ℝ)|=(2674754989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262181433/500000000 : ℝ)|^2135 ≤ (8554912222253/20000000000000 : ℝ)^1623
        have hw : |(262181433/500000000 : ℝ)|=(262181433/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-539731889/2500000000 : ℝ)|^2135 ≤ (13311081947251/100000000000000 : ℝ)^1623
        have hw : |(-539731889/2500000000 : ℝ)|=(539731889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s7_3 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4335059803/10000000000 : ℝ)*x 0 + (1040469917/2500000000 : ℝ)*x 1 + (903011843/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335059803/10000000000 : ℝ)^2135 ≤ (33302718150093/100000000000000 : ℝ)^1623 := by
    have hnat : (4335059803 : ℕ)^2135*100000000000000^1623 ≤ 33302718150093^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335059803 10000000000 33302718150093 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040469917/2500000000 : ℝ)^2135 ≤ (15781875767391/50000000000000 : ℝ)^1623 := by
    have hnat : (1040469917 : ℕ)^2135*50000000000000^1623 ≤ 15781875767391^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040469917 2500000000 15781875767391 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903011843/2000000000 : ℝ)^2135 ≤ (1405341212137/4000000000000 : ℝ)^1623 := by
    have hnat : (903011843 : ℕ)^2135*4000000000000^1623 ≤ 1405341212137^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903011843 2000000000 1405341212137 4000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335059803/10000000000 : ℝ), (1040469917/2500000000 : ℝ), (903011843/2000000000 : ℝ)] ![(33302718150093/100000000000000 : ℝ), (15781875767391/50000000000000 : ℝ), (1405341212137/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335059803/10000000000 : ℝ)|^2135 ≤ (33302718150093/100000000000000 : ℝ)^1623
        have hw : |(4335059803/10000000000 : ℝ)|=(4335059803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040469917/2500000000 : ℝ)|^2135 ≤ (15781875767391/50000000000000 : ℝ)^1623
        have hw : |(1040469917/2500000000 : ℝ)|=(1040469917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903011843/2000000000 : ℝ)|^2135 ≤ (1405341212137/4000000000000 : ℝ)^1623
        have hw : |(903011843/2000000000 : ℝ)|=(903011843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s7_4 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2071957381/10000000000 : ℝ)*x 0 + (16388243/31250000 : ℝ)*x 1 + (2706842847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071957381/10000000000 : ℝ)^2135 ≤ (2522044585551/20000000000000 : ℝ)^1623 := by
    have hnat : (2071957381 : ℕ)^2135*20000000000000^1623 ≤ 2522044585551^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071957381 10000000000 2522044585551 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16388243/31250000 : ℝ)^2135 ≤ (10695274343683/25000000000000 : ℝ)^1623 := by
    have hnat : (16388243 : ℕ)^2135*25000000000000^1623 ≤ 10695274343683^1623*31250000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16388243 31250000 10695274343683 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706842847/5000000000 : ℝ)^2135 ≤ (5576084959257/12500000000000 : ℝ)^1623 := by
    have hnat : (2706842847 : ℕ)^2135*12500000000000^1623 ≤ 5576084959257^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706842847 5000000000 5576084959257 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2071957381/10000000000 : ℝ), (16388243/31250000 : ℝ), (2706842847/5000000000 : ℝ)] ![(2522044585551/20000000000000 : ℝ), (10695274343683/25000000000000 : ℝ), (5576084959257/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2071957381/10000000000 : ℝ)|^2135 ≤ (2522044585551/20000000000000 : ℝ)^1623
        have hw : |(-2071957381/10000000000 : ℝ)|=(2071957381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16388243/31250000 : ℝ)|^2135 ≤ (10695274343683/25000000000000 : ℝ)^1623
        have hw : |(16388243/31250000 : ℝ)|=(16388243/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706842847/5000000000 : ℝ)|^2135 ≤ (5576084959257/12500000000000 : ℝ)^1623
        have hw : |(2706842847/5000000000 : ℝ)|=(2706842847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s7_5 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061143267/2000000000 : ℝ)*x 0 + (-1988870391/10000000000 : ℝ)*x 1 + (2706842847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061143267/2000000000 : ℝ)^2135 ≤ (43442053881761/100000000000000 : ℝ)^1623 := by
    have hnat : (1061143267 : ℕ)^2135*100000000000000^1623 ≤ 43442053881761^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061143267 2000000000 43442053881761 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988870391/10000000000 : ℝ)^2135 ≤ (2389853285187/20000000000000 : ℝ)^1623 := by
    have hnat : (1988870391 : ℕ)^2135*20000000000000^1623 ≤ 2389853285187^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988870391 10000000000 2389853285187 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706842847/5000000000 : ℝ)^2135 ≤ (5576084959257/12500000000000 : ℝ)^1623 := by
    have hnat : (2706842847 : ℕ)^2135*12500000000000^1623 ≤ 5576084959257^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706842847 5000000000 5576084959257 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061143267/2000000000 : ℝ), (-1988870391/10000000000 : ℝ), (2706842847/5000000000 : ℝ)] ![(43442053881761/100000000000000 : ℝ), (2389853285187/20000000000000 : ℝ), (5576084959257/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061143267/2000000000 : ℝ)|^2135 ≤ (43442053881761/100000000000000 : ℝ)^1623
        have hw : |(1061143267/2000000000 : ℝ)|=(1061143267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1988870391/10000000000 : ℝ)|^2135 ≤ (2389853285187/20000000000000 : ℝ)^1623
        have hw : |(-1988870391/10000000000 : ℝ)|=(1988870391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706842847/5000000000 : ℝ)|^2135 ≤ (5576084959257/12500000000000 : ℝ)^1623
        have hw : |(2706842847/5000000000 : ℝ)|=(2706842847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s7_6 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061143267/2000000000 : ℝ)*x 0 + (2706842847/5000000000 : ℝ)*x 1 + (-1988870391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061143267/2000000000 : ℝ)^2135 ≤ (43442053881761/100000000000000 : ℝ)^1623 := by
    have hnat : (1061143267 : ℕ)^2135*100000000000000^1623 ≤ 43442053881761^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061143267 2000000000 43442053881761 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706842847/5000000000 : ℝ)^2135 ≤ (5576084959257/12500000000000 : ℝ)^1623 := by
    have hnat : (2706842847 : ℕ)^2135*12500000000000^1623 ≤ 5576084959257^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706842847 5000000000 5576084959257 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1988870391/10000000000 : ℝ)^2135 ≤ (2389853285187/20000000000000 : ℝ)^1623 := by
    have hnat : (1988870391 : ℕ)^2135*20000000000000^1623 ≤ 2389853285187^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988870391 10000000000 2389853285187 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061143267/2000000000 : ℝ), (2706842847/5000000000 : ℝ), (-1988870391/10000000000 : ℝ)] ![(43442053881761/100000000000000 : ℝ), (5576084959257/12500000000000 : ℝ), (2389853285187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061143267/2000000000 : ℝ)|^2135 ≤ (43442053881761/100000000000000 : ℝ)^1623
        have hw : |(1061143267/2000000000 : ℝ)|=(1061143267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706842847/5000000000 : ℝ)|^2135 ≤ (5576084959257/12500000000000 : ℝ)^1623
        have hw : |(2706842847/5000000000 : ℝ)|=(2706842847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1988870391/10000000000 : ℝ)|^2135 ≤ (2389853285187/20000000000000 : ℝ)^1623
        have hw : |(-1988870391/10000000000 : ℝ)|=(1988870391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s7_7 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2167542663/5000000000 : ℝ)*x 0 + (4513799107/10000000000 : ℝ)*x 1 + (4163146603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167542663/5000000000 : ℝ)^2135 ≤ (33302976076657/100000000000000 : ℝ)^1623 := by
    have hnat : (2167542663 : ℕ)^2135*100000000000000^1623 ≤ 33302976076657^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167542663 5000000000 33302976076657 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4513799107/10000000000 : ℝ)^2135 ≤ (4390079023167/12500000000000 : ℝ)^1623 := by
    have hnat : (4513799107 : ℕ)^2135*12500000000000^1623 ≤ 4390079023167^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513799107 10000000000 4390079023167 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4163146603/10000000000 : ℝ)^2135 ≤ (15788195862963/50000000000000 : ℝ)^1623 := by
    have hnat : (4163146603 : ℕ)^2135*50000000000000^1623 ≤ 15788195862963^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163146603 10000000000 15788195862963 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2167542663/5000000000 : ℝ), (4513799107/10000000000 : ℝ), (4163146603/10000000000 : ℝ)] ![(33302976076657/100000000000000 : ℝ), (4390079023167/12500000000000 : ℝ), (15788195862963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2167542663/5000000000 : ℝ)|^2135 ≤ (33302976076657/100000000000000 : ℝ)^1623
        have hw : |(2167542663/5000000000 : ℝ)|=(2167542663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4513799107/10000000000 : ℝ)|^2135 ≤ (4390079023167/12500000000000 : ℝ)^1623
        have hw : |(4513799107/10000000000 : ℝ)|=(4513799107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4163146603/10000000000 : ℝ)|^2135 ≤ (15788195862963/50000000000000 : ℝ)^1623
        have hw : |(4163146603/10000000000 : ℝ)|=(4163146603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1310_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11073/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2937/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14687/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11071/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14687/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11071/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14687/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11071/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14687/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11071/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14687/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11071/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14687/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11071/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11071/100000 : ℝ) ^ (4269/1024 : ℝ) ≤ (10357793583523007/100000000000000000000 : ℝ) := by
    have hpowers : (11071/100000 : ℝ)^4269 ≤ (10357793583523007/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11071 : ℕ)^4269*100000000000000000000^1024 ≤ 10357793583523007^1024*100000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11071 100000 10357793583523007 100000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11071/100000 : ℝ)) (X := (10357793583523007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14687/100000 : ℝ) ^ (4269/1024 : ℝ) ≤ (2103147093641203/6250000000000000000 : ℝ) := by
    have hpowers : (14687/100000 : ℝ)^4269 ≤ (2103147093641203/6250000000000000000 : ℝ)^1024 := by
      have hnat : (14687 : ℕ)^4269*6250000000000000000^1024 ≤ 2103147093641203^1024*100000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14687 100000 2103147093641203 6250000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14687/100000 : ℝ)) (X := (2103147093641203/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010357793583523007/50000000000000000000 : ℝ) ≤ (1000049686323077/1000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (50010357793583523007/50000000000000000000 : ℝ)^1024 ≤ (1000049686323077/1000000000000000 : ℝ)^4269 := by
      have hnat : (50010357793583523007 : ℕ)^1024*1000000000000000^4269 ≤ 1000049686323077^4269*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010357793583523007 50000000000000000000 1000049686323077 1000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000049686323077/1000000000000000 : ℝ)) (X := (50010357793583523007/50000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008801629416356451/20000000000000000000 : ℝ) ≤ (10001055441721793/10000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (20008801629416356451/20000000000000000000 : ℝ)^1024 ≤ (10001055441721793/10000000000000000 : ℝ)^4269 := by
      have hnat : (20008801629416356451 : ℕ)^1024*10000000000000000^4269 ≤ 10001055441721793^4269*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008801629416356451 20000000000000000000 10001055441721793 10000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001055441721793/10000000000000000 : ℝ)) (X := (20008801629416356451/20000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127103147093641203/3125000000000000000 : ℝ) ≤ (625100876263301/625000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (3127103147093641203/3125000000000000000 : ℝ)^1024 ≤ (625100876263301/625000000000000 : ℝ)^4269 := by
      have hnat : (3127103147093641203 : ℕ)^1024*625000000000000^4269 ≤ 625100876263301^4269*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127103147093641203 3125000000000000000 625100876263301 625000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625100876263301/625000000000000 : ℝ)) (X := (3127103147093641203/3125000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10357793583523007/100000000000000000000 : ℝ) ≤ ((18074714306247116527/18080000000000000000 : ℝ)+2*(558578491023/361600000000000 : ℝ)*(11071/100000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (18074714306247116527/18080000000000000000 : ℝ)+2*(558578491023/361600000000000 : ℝ)*(11071/100000 : ℝ)=(1000049686323077/1000000000000000 : ℝ) by norm_num, show 1+2*(10357793583523007/100000000000000000000 : ℝ)=(50010357793583523007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2103147093641203/6250000000000000000 : ℝ)+(10357793583523007/100000000000000000000 : ℝ) ≤ ((18074714306247116527/18080000000000000000 : ℝ)+(558578491023/361600000000000 : ℝ)*((14687/100000 : ℝ)+(11071/100000 : ℝ)))^(4269/1024 : ℝ) := by
    rw [show (18074714306247116527/18080000000000000000 : ℝ)+(558578491023/361600000000000 : ℝ)*((14687/100000 : ℝ)+(11071/100000 : ℝ))=(10001055441721793/10000000000000000 : ℝ) by norm_num, show 1+(2103147093641203/6250000000000000000 : ℝ)+(10357793583523007/100000000000000000000 : ℝ)=(20008801629416356451/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2103147093641203/6250000000000000000 : ℝ) ≤ ((18074714306247116527/18080000000000000000 : ℝ)+2*(558578491023/361600000000000 : ℝ)*(14687/100000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (18074714306247116527/18080000000000000000 : ℝ)+2*(558578491023/361600000000000 : ℝ)*(14687/100000 : ℝ)=(625100876263301/625000000000000 : ℝ) by norm_num, show 1+2*(2103147093641203/6250000000000000000 : ℝ)=(3127103147093641203/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18074714306247116527/18080000000000000000 : ℝ)*(X 1 0+X 2 0)+(558578491023/361600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (11071/100000 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (18074714306247116527/18080000000000000000 : ℝ)) (alpha := (558578491023/361600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18074714306247116527/18080000000000000000 : ℝ)*(X 0 1+X 2 1)+(558578491023/361600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (11071/100000 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (18074714306247116527/18080000000000000000 : ℝ)) (alpha := (558578491023/361600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18074714306247116527/18080000000000000000 : ℝ)*(X 0 2+X 1 2)+(558578491023/361600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (11071/100000 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (18074714306247116527/18080000000000000000 : ℝ)) (alpha := (558578491023/361600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-517986191/2500000000 : ℝ)*X 0 0+(2707149003/5000000000 : ℝ)*X 0 1+(1048725733/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674755229/5000000000 : ℝ)*X 1 0+(-2158927223/10000000000 : ℝ)*X 1 1+(1310907107/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674754989/5000000000 : ℝ)*X 2 0+(262181433/500000000 : ℝ)*X 2 1+(-539731889/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4335059803/10000000000 : ℝ)*X 0 0+(1040469917/2500000000 : ℝ)*X 0 1+(903011843/2000000000 : ℝ)*X 0 2+(4335059803/10000000000 : ℝ)*X 1 0+(1040469917/2500000000 : ℝ)*X 1 1+(903011843/2000000000 : ℝ)*X 1 2+(4335059803/10000000000 : ℝ)*X 2 0+(1040469917/2500000000 : ℝ)*X 2 1+(903011843/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2071957381/10000000000 : ℝ)*X 0 0+(16388243/31250000 : ℝ)*X 0 1+(2706842847/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061143267/2000000000 : ℝ)*X 1 0+(-1988870391/10000000000 : ℝ)*X 1 1+(2706842847/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061143267/2000000000 : ℝ)*X 2 0+(2706842847/5000000000 : ℝ)*X 2 1+(-1988870391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2167542663/5000000000 : ℝ)*X 0 0+(4513799107/10000000000 : ℝ)*X 0 1+(4163146603/10000000000 : ℝ)*X 0 2+(2167542663/5000000000 : ℝ)*X 1 0+(4513799107/10000000000 : ℝ)*X 1 1+(4163146603/10000000000 : ℝ)*X 1 2+(2167542663/5000000000 : ℝ)*X 2 0+(4513799107/10000000000 : ℝ)*X 2 1+(4163146603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50918496686877028970571/18080000000000000000000000000 : ℝ) := by norm_num
    linear_combination (502155253/50000000000000 : ℝ)*(base19) + (805168267/100000000000000 : ℝ)*(base23) + (150603857/100000000000000 : ℝ)*(upper3) + (93089081/50000000000000 : ℝ)*(lower4) + (4345376743705321/100000000000000 : ℝ)*(major0) + (4345376743705321/100000000000000 : ℝ)*(major1) + (4345376743705321/100000000000000 : ℝ)*(major2) + (2929654010723249/50000000000000 : ℝ)*(sp0) + (5859318085051/100000000000 : ℝ)*(sp1) + (1464828916716323/25000000000000 : ℝ)*(sp2) + (1415714129379957/50000000000000 : ℝ)*(sp3) + (43234043/390625000000 : ℝ)*(sp4) + (654331987/25000000000000 : ℝ)*(sp6) + (3022706463/50000000000000 : ℝ)*(sp7) + (70785857604321/2500000000000 : ℝ)*(f.failure) + (2929659544680753/50000000000000 : ℝ)*(f.sum) + (56129465554457/18080000000000000000000000000 : ℝ)*base66 + (8522100783509909833/1808000000000000000000000000000000 : ℝ)*base68 + (14925330678826090167/1808000000000000000000000000000000 : ℝ)*base69 + (11211770622762090167/1808000000000000000000000000000000 : ℝ)*base71 + (16682991410663/18080000000000000000000000000 : ℝ)*base73 + (10340844240202090167/1808000000000000000000000000000000 : ℝ)*base75 + (12885535707285909833/1808000000000000000000000000000000 : ℝ)*base78 + (21726032475221909833/1808000000000000000000000000000000 : ℝ)*base80 + (127278148299943/18080000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (25189/2500000000000000000 : ℝ)*base90 + (25189/2500000000000000000 : ℝ)*base92 + (25189/2500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6103139303283703184471319/1000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (538714749/50000000000000 : ℝ)*(base19) + (1171841359/100000000000000 : ℝ)*(base23) + (92478027/25000000000000 : ℝ)*(lower1) + (124230923/100000000000000 : ℝ)*(upper3) + (8369/19531250000 : ℝ)*(lower4) + (125499957/100000000000000 : ℝ)*(upper5) + (1094163839230587/25000000000000 : ℝ)*(major0) + (1094163839230587/25000000000000 : ℝ)*(major1) + (1094163839230587/25000000000000 : ℝ)*(major2) + (826943529/50000000000000 : ℝ)*(sp2) + (2950747578373833/50000000000000 : ℝ)*(sp4) + (737686759914771/12500000000000 : ℝ)*(sp5) + (5901492331019249/100000000000000 : ℝ)*(sp6) + (2851815353659041/100000000000000 : ℝ)*(sp7) + (2851815353659041/100000000000000 : ℝ)*(f.failure) + (2950747578373833/50000000000000 : ℝ)*(f.sum) + (245056203877/40000000000000000000000000 : ℝ)*base65 + (98134574674401227/4000000000000000000000000000000 : ℝ)*base68 + (8239908194401227/4000000000000000000000000000000 : ℝ)*base70 + (29197623070401227/4000000000000000000000000000000 : ℝ)*base72 + (320192080717/40000000000000000000000000 : ℝ)*base73 + (49775101746401227/4000000000000000000000000000000 : ℝ)*base76 + (25782685493598773/4000000000000000000000000000000 : ℝ)*base77 + (56745526378401227/4000000000000000000000000000000 : ℝ)*base80 + (228210144037/40000000000000000000000000 : ℝ)*base81 + (708669/100000000000000000000 : ℝ)*base90 + (708669/100000000000000000000 : ℝ)*base92 + (708669/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1310_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11073/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1310_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1310_box_0 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1902099157/10000000000 : ℝ)*x 0 + (5391271081/10000000000 : ℝ)*x 1 + (5391271063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1902099157/10000000000 : ℝ)^2135 ≤ (11268245602299/100000000000000 : ℝ)^1623 := by
    have hnat : (1902099157 : ℕ)^2135*100000000000000^1623 ≤ 11268245602299^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902099157 10000000000 11268245602299 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391271081/10000000000 : ℝ)^2135 ≤ (44365877288309/100000000000000 : ℝ)^1623 := by
    have hnat : (5391271081 : ℕ)^2135*100000000000000^1623 ≤ 44365877288309^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391271081 10000000000 44365877288309 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391271063/10000000000 : ℝ)^2135 ≤ (8873175418691/20000000000000 : ℝ)^1623 := by
    have hnat : (5391271063 : ℕ)^2135*20000000000000^1623 ≤ 8873175418691^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391271063 10000000000 8873175418691 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1902099157/10000000000 : ℝ), (5391271081/10000000000 : ℝ), (5391271063/10000000000 : ℝ)] ![(11268245602299/100000000000000 : ℝ), (44365877288309/100000000000000 : ℝ), (8873175418691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1902099157/10000000000 : ℝ)|^2135 ≤ (11268245602299/100000000000000 : ℝ)^1623
        have hw : |(-1902099157/10000000000 : ℝ)|=(1902099157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391271081/10000000000 : ℝ)|^2135 ≤ (44365877288309/100000000000000 : ℝ)^1623
        have hw : |(5391271081/10000000000 : ℝ)|=(5391271081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391271063/10000000000 : ℝ)|^2135 ≤ (8873175418691/20000000000000 : ℝ)^1623
        have hw : |(5391271063/10000000000 : ℝ)|=(5391271063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_1 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5284681197/10000000000 : ℝ)*x 0 + (-1023982731/5000000000 : ℝ)*x 1 + (2695635459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284681197/10000000000 : ℝ)^2135 ≤ (21607815808299/50000000000000 : ℝ)^1623 := by
    have hnat : (5284681197 : ℕ)^2135*50000000000000^1623 ≤ 21607815808299^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284681197 10000000000 21607815808299 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023982731/5000000000 : ℝ)^2135 ≤ (6209246425983/50000000000000 : ℝ)^1623 := by
    have hnat : (1023982731 : ℕ)^2135*50000000000000^1623 ≤ 6209246425983^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023982731 5000000000 6209246425983 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695635459/5000000000 : ℝ)^2135 ≤ (11091468880949/25000000000000 : ℝ)^1623 := by
    have hnat : (2695635459 : ℕ)^2135*25000000000000^1623 ≤ 11091468880949^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695635459 5000000000 11091468880949 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284681197/10000000000 : ℝ), (-1023982731/5000000000 : ℝ), (2695635459/5000000000 : ℝ)] ![(21607815808299/50000000000000 : ℝ), (6209246425983/50000000000000 : ℝ), (11091468880949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284681197/10000000000 : ℝ)|^2135 ≤ (21607815808299/50000000000000 : ℝ)^1623
        have hw : |(5284681197/10000000000 : ℝ)|=(5284681197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1023982731/5000000000 : ℝ)|^2135 ≤ (6209246425983/50000000000000 : ℝ)^1623
        have hw : |(-1023982731/5000000000 : ℝ)|=(1023982731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695635459/5000000000 : ℝ)|^2135 ≤ (11091468880949/25000000000000 : ℝ)^1623
        have hw : |(2695635459/5000000000 : ℝ)|=(2695635459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_2 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1056936193/2000000000 : ℝ)*x 0 + (336954447/625000000 : ℝ)*x 1 + (-127997841/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056936193/2000000000 : ℝ)^2135 ≤ (8643125824183/20000000000000 : ℝ)^1623 := by
    have hnat : (1056936193 : ℕ)^2135*20000000000000^1623 ≤ 8643125824183^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056936193 2000000000 8643125824183 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336954447/625000000 : ℝ)^2135 ≤ (44365878056901/100000000000000 : ℝ)^1623 := by
    have hnat : (336954447 : ℕ)^2135*100000000000000^1623 ≤ 44365878056901^1623*625000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336954447 625000000 44365878056901 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127997841/625000000 : ℝ)^2135 ≤ (2483698560821/20000000000000 : ℝ)^1623 := by
    have hnat : (127997841 : ℕ)^2135*20000000000000^1623 ≤ 2483698560821^1623*625000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127997841 625000000 2483698560821 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056936193/2000000000 : ℝ), (336954447/625000000 : ℝ), (-127997841/625000000 : ℝ)] ![(8643125824183/20000000000000 : ℝ), (44365878056901/100000000000000 : ℝ), (2483698560821/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056936193/2000000000 : ℝ)|^2135 ≤ (8643125824183/20000000000000 : ℝ)^1623
        have hw : |(1056936193/2000000000 : ℝ)|=(1056936193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336954447/625000000 : ℝ)|^2135 ≤ (44365878056901/100000000000000 : ℝ)^1623
        have hw : |(336954447/625000000 : ℝ)|=(336954447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127997841/625000000 : ℝ)|^2135 ≤ (2483698560821/20000000000000 : ℝ)^1623
        have hw : |(-127997841/625000000 : ℝ)|=(127997841/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_3 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (448402657/1000000000 : ℝ)*x 0 + (2132269209/5000000000 : ℝ)*x 1 + (4264538511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448402657/1000000000 : ℝ)^2135 ≤ (870405490949/2500000000000 : ℝ)^1623 := by
    have hnat : (448402657 : ℕ)^2135*2500000000000^1623 ≤ 870405490949^1623*1000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448402657 1000000000 870405490949 2500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132269209/5000000000 : ℝ)^2135 ≤ (32591889705879/100000000000000 : ℝ)^1623 := by
    have hnat : (2132269209 : ℕ)^2135*100000000000000^1623 ≤ 32591889705879^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132269209 5000000000 32591889705879 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4264538511/10000000000 : ℝ)^2135 ≤ (16295945320427/50000000000000 : ℝ)^1623 := by
    have hnat : (4264538511 : ℕ)^2135*50000000000000^1623 ≤ 16295945320427^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4264538511 10000000000 16295945320427 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(448402657/1000000000 : ℝ), (2132269209/5000000000 : ℝ), (4264538511/10000000000 : ℝ)] ![(870405490949/2500000000000 : ℝ), (32591889705879/100000000000000 : ℝ), (16295945320427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(448402657/1000000000 : ℝ)|^2135 ≤ (870405490949/2500000000000 : ℝ)^1623
        have hw : |(448402657/1000000000 : ℝ)|=(448402657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2132269209/5000000000 : ℝ)|^2135 ≤ (32591889705879/100000000000000 : ℝ)^1623
        have hw : |(2132269209/5000000000 : ℝ)|=(2132269209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4264538511/10000000000 : ℝ)|^2135 ≤ (16295945320427/50000000000000 : ℝ)^1623
        have hw : |(4264538511/10000000000 : ℝ)|=(4264538511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_4 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-280568559/1250000000 : ℝ)*x 0 + (5264166471/10000000000 : ℝ)*x 1 + (1316041699/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280568559/1250000000 : ℝ)^2135 ≤ (7004913510141/50000000000000 : ℝ)^1623 := by
    have hnat : (280568559 : ℕ)^2135*50000000000000^1623 ≤ 7004913510141^1623*1250000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280568559 1250000000 7004913510141 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264166471/10000000000 : ℝ)^2135 ≤ (42995084739143/100000000000000 : ℝ)^1623 := by
    have hnat : (5264166471 : ℕ)^2135*100000000000000^1623 ≤ 42995084739143^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264166471 10000000000 42995084739143 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316041699/2500000000 : ℝ)^2135 ≤ (10748772057741/25000000000000 : ℝ)^1623 := by
    have hnat : (1316041699 : ℕ)^2135*25000000000000^1623 ≤ 10748772057741^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316041699 2500000000 10748772057741 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-280568559/1250000000 : ℝ), (5264166471/10000000000 : ℝ), (1316041699/2500000000 : ℝ)] ![(7004913510141/50000000000000 : ℝ), (42995084739143/100000000000000 : ℝ), (10748772057741/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-280568559/1250000000 : ℝ)|^2135 ≤ (7004913510141/50000000000000 : ℝ)^1623
        have hw : |(-280568559/1250000000 : ℝ)|=(280568559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264166471/10000000000 : ℝ)|^2135 ≤ (42995084739143/100000000000000 : ℝ)^1623
        have hw : |(5264166471/10000000000 : ℝ)|=(5264166471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316041699/2500000000 : ℝ)|^2135 ≤ (10748772057741/25000000000000 : ℝ)^1623
        have hw : |(1316041699/2500000000 : ℝ)|=(1316041699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_5 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5374078147/10000000000 : ℝ)*x 0 + (-1049368399/5000000000 : ℝ)*x 1 + (1052833373/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374078147/10000000000 : ℝ)^2135 ≤ (22089926727521/50000000000000 : ℝ)^1623 := by
    have hnat : (5374078147 : ℕ)^2135*50000000000000^1623 ≤ 22089926727521^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374078147 10000000000 22089926727521 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049368399/5000000000 : ℝ)^2135 ≤ (2565011513053/20000000000000 : ℝ)^1623 := by
    have hnat : (1049368399 : ℕ)^2135*20000000000000^1623 ≤ 2565011513053^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049368399 5000000000 2565011513053 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052833373/2000000000 : ℝ)^2135 ≤ (2687193060769/6250000000000 : ℝ)^1623 := by
    have hnat : (1052833373 : ℕ)^2135*6250000000000^1623 ≤ 2687193060769^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052833373 2000000000 2687193060769 6250000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374078147/10000000000 : ℝ), (-1049368399/5000000000 : ℝ), (1052833373/2000000000 : ℝ)] ![(22089926727521/50000000000000 : ℝ), (2565011513053/20000000000000 : ℝ), (2687193060769/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374078147/10000000000 : ℝ)|^2135 ≤ (22089926727521/50000000000000 : ℝ)^1623
        have hw : |(5374078147/10000000000 : ℝ)|=(5374078147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1049368399/5000000000 : ℝ)|^2135 ≤ (2565011513053/20000000000000 : ℝ)^1623
        have hw : |(-1049368399/5000000000 : ℝ)|=(1049368399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052833373/2000000000 : ℝ)|^2135 ≤ (2687193060769/6250000000000 : ℝ)^1623
        have hw : |(1052833373/2000000000 : ℝ)|=(1052833373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_6 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1343519527/2500000000 : ℝ)*x 0 + (5264166687/10000000000 : ℝ)*x 1 + (-32792767/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343519527/2500000000 : ℝ)^2135 ≤ (11044963258321/25000000000000 : ℝ)^1623 := by
    have hnat : (1343519527 : ℕ)^2135*25000000000000^1623 ≤ 11044963258321^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343519527 2500000000 11044963258321 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264166687/10000000000 : ℝ)^2135 ≤ (42995087059861/100000000000000 : ℝ)^1623 := by
    have hnat : (5264166687 : ℕ)^2135*100000000000000^1623 ≤ 42995087059861^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264166687 10000000000 42995087059861 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32792767/156250000 : ℝ)^2135 ≤ (12825059896461/100000000000000 : ℝ)^1623 := by
    have hnat : (32792767 : ℕ)^2135*100000000000000^1623 ≤ 12825059896461^1623*156250000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32792767 156250000 12825059896461 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343519527/2500000000 : ℝ), (5264166687/10000000000 : ℝ), (-32792767/156250000 : ℝ)] ![(11044963258321/25000000000000 : ℝ), (42995087059861/100000000000000 : ℝ), (12825059896461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343519527/2500000000 : ℝ)|^2135 ≤ (11044963258321/25000000000000 : ℝ)^1623
        have hw : |(1343519527/2500000000 : ℝ)|=(1343519527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264166687/10000000000 : ℝ)|^2135 ≤ (42995087059861/100000000000000 : ℝ)^1623
        have hw : |(5264166687/10000000000 : ℝ)|=(5264166687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32792767/156250000 : ℝ)|^2135 ≤ (12825059896461/100000000000000 : ℝ)^1623
        have hw : |(-32792767/156250000 : ℝ)|=(32792767/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_7 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4185214581/10000000000 : ℝ)*x 0 + (2206945009/5000000000 : ℝ)*x 1 + (4413889483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185214581/10000000000 : ℝ)^2135 ≤ (31796758049269/100000000000000 : ℝ)^1623 := by
    have hnat : (4185214581 : ℕ)^2135*100000000000000^1623 ≤ 31796758049269^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185214581 10000000000 31796758049269 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2206945009/5000000000 : ℝ)^2135 ≤ (34101623689793/100000000000000 : ℝ)^1623 := by
    have hnat : (2206945009 : ℕ)^2135*100000000000000^1623 ≤ 34101623689793^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206945009 5000000000 34101623689793 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4413889483/10000000000 : ℝ)^2135 ≤ (34101618252451/100000000000000 : ℝ)^1623 := by
    have hnat : (4413889483 : ℕ)^2135*100000000000000^1623 ≤ 34101618252451^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413889483 10000000000 34101618252451 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4185214581/10000000000 : ℝ), (2206945009/5000000000 : ℝ), (4413889483/10000000000 : ℝ)] ![(31796758049269/100000000000000 : ℝ), (34101623689793/100000000000000 : ℝ), (34101618252451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4185214581/10000000000 : ℝ)|^2135 ≤ (31796758049269/100000000000000 : ℝ)^1623
        have hw : |(4185214581/10000000000 : ℝ)|=(4185214581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2206945009/5000000000 : ℝ)|^2135 ≤ (34101623689793/100000000000000 : ℝ)^1623
        have hw : |(2206945009/5000000000 : ℝ)|=(2206945009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4413889483/10000000000 : ℝ)|^2135 ≤ (34101618252451/100000000000000 : ℝ)^1623
        have hw : |(4413889483/10000000000 : ℝ)|=(4413889483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_8 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172722841/10000000000 : ℝ)*x 0 + (5176818011/10000000000 : ℝ)*x 1 + (1351325879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172722841/10000000000 : ℝ)^2135 ≤ (3355770755481/25000000000000 : ℝ)^1623 := by
    have hnat : (2172722841 : ℕ)^2135*25000000000000^1623 ≤ 3355770755481^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172722841 10000000000 3355770755481 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176818011/10000000000 : ℝ)^2135 ≤ (42059072970859/100000000000000 : ℝ)^1623 := by
    have hnat : (5176818011 : ℕ)^2135*100000000000000^1623 ≤ 42059072970859^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176818011 10000000000 42059072970859 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351325879/2500000000 : ℝ)^2135 ≤ (44517843997563/100000000000000 : ℝ)^1623 := by
    have hnat : (1351325879 : ℕ)^2135*100000000000000^1623 ≤ 44517843997563^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351325879 2500000000 44517843997563 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172722841/10000000000 : ℝ), (5176818011/10000000000 : ℝ), (1351325879/2500000000 : ℝ)] ![(3355770755481/25000000000000 : ℝ), (42059072970859/100000000000000 : ℝ), (44517843997563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172722841/10000000000 : ℝ)|^2135 ≤ (3355770755481/25000000000000 : ℝ)^1623
        have hw : |(-2172722841/10000000000 : ℝ)|=(2172722841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176818011/10000000000 : ℝ)|^2135 ≤ (42059072970859/100000000000000 : ℝ)^1623
        have hw : |(5176818011/10000000000 : ℝ)|=(5176818011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351325879/2500000000 : ℝ)|^2135 ≤ (44517843997563/100000000000000 : ℝ)^1623
        have hw : |(1351325879/2500000000 : ℝ)|=(1351325879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_9 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1054961151/2000000000 : ℝ)*x 0 + (-1021112777/5000000000 : ℝ)*x 1 + (1351325841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054961151/2000000000 : ℝ)^2135 ≤ (8621886060511/20000000000000 : ℝ)^1623 := by
    have hnat : (1054961151 : ℕ)^2135*20000000000000^1623 ≤ 8621886060511^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054961151 2000000000 8621886060511 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021112777/5000000000 : ℝ)^2135 ≤ (12372727332637/100000000000000 : ℝ)^1623 := by
    have hnat : (1021112777 : ℕ)^2135*100000000000000^1623 ≤ 12372727332637^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021112777 5000000000 12372727332637 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351325841/2500000000 : ℝ)^2135 ≤ (22258921175389/50000000000000 : ℝ)^1623 := by
    have hnat : (1351325841 : ℕ)^2135*50000000000000^1623 ≤ 22258921175389^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351325841 2500000000 22258921175389 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054961151/2000000000 : ℝ), (-1021112777/5000000000 : ℝ), (1351325841/2500000000 : ℝ)] ![(8621886060511/20000000000000 : ℝ), (12372727332637/100000000000000 : ℝ), (22258921175389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054961151/2000000000 : ℝ)|^2135 ≤ (8621886060511/20000000000000 : ℝ)^1623
        have hw : |(1054961151/2000000000 : ℝ)|=(1054961151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021112777/5000000000 : ℝ)|^2135 ≤ (12372727332637/100000000000000 : ℝ)^1623
        have hw : |(-1021112777/5000000000 : ℝ)|=(1021112777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351325841/2500000000 : ℝ)|^2135 ≤ (22258921175389/50000000000000 : ℝ)^1623
        have hw : |(1351325841/2500000000 : ℝ)|=(1351325841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_10 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1318701467/2500000000 : ℝ)*x 0 + (2702651521/5000000000 : ℝ)*x 1 + (-25527823/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318701467/2500000000 : ℝ)^2135 ≤ (1347169734919/3125000000000 : ℝ)^1623 := by
    have hnat : (1318701467 : ℕ)^2135*3125000000000^1623 ≤ 1347169734919^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318701467 2500000000 1347169734919 3125000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702651521/5000000000 : ℝ)^2135 ≤ (44517838862193/100000000000000 : ℝ)^1623 := by
    have hnat : (2702651521 : ℕ)^2135*100000000000000^1623 ≤ 44517838862193^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702651521 5000000000 44517838862193 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25527823/125000000 : ℝ)^2135 ≤ (6186364805983/50000000000000 : ℝ)^1623 := by
    have hnat : (25527823 : ℕ)^2135*50000000000000^1623 ≤ 6186364805983^1623*125000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25527823 125000000 6186364805983 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318701467/2500000000 : ℝ), (2702651521/5000000000 : ℝ), (-25527823/125000000 : ℝ)] ![(1347169734919/3125000000000 : ℝ), (44517838862193/100000000000000 : ℝ), (6186364805983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318701467/2500000000 : ℝ)|^2135 ≤ (1347169734919/3125000000000 : ℝ)^1623
        have hw : |(1318701467/2500000000 : ℝ)|=(1318701467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702651521/5000000000 : ℝ)|^2135 ≤ (44517838862193/100000000000000 : ℝ)^1623
        have hw : |(2702651521/5000000000 : ℝ)|=(2702651521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25527823/125000000 : ℝ)|^2135 ≤ (6186364805983/50000000000000 : ℝ)^1623
        have hw : |(-25527823/125000000 : ℝ)|=(25527823/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_11 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1129113799/2500000000 : ℝ)*x 0 + (132751141/312500000 : ℝ)*x 1 + (21240183/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1129113799/2500000000 : ℝ)^2135 ≤ (8786955126499/25000000000000 : ℝ)^1623 := by
    have hnat : (1129113799 : ℕ)^2135*25000000000000^1623 ≤ 8786955126499^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129113799 2500000000 8786955126499 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132751141/312500000 : ℝ)^2135 ≤ (16213044650017/50000000000000 : ℝ)^1623 := by
    have hnat : (132751141 : ℕ)^2135*50000000000000^1623 ≤ 16213044650017^1623*312500000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132751141 312500000 16213044650017 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21240183/50000000 : ℝ)^2135 ≤ (32426090183659/100000000000000 : ℝ)^1623 := by
    have hnat : (21240183 : ℕ)^2135*100000000000000^1623 ≤ 32426090183659^1623*50000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21240183 50000000 32426090183659 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1129113799/2500000000 : ℝ), (132751141/312500000 : ℝ), (21240183/50000000 : ℝ)] ![(8786955126499/25000000000000 : ℝ), (16213044650017/50000000000000 : ℝ), (32426090183659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1129113799/2500000000 : ℝ)|^2135 ≤ (8786955126499/25000000000000 : ℝ)^1623
        have hw : |(1129113799/2500000000 : ℝ)|=(1129113799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132751141/312500000 : ℝ)|^2135 ≤ (16213044650017/50000000000000 : ℝ)^1623
        have hw : |(132751141/312500000 : ℝ)|=(132751141/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21240183/50000000 : ℝ)|^2135 ≤ (32426090183659/100000000000000 : ℝ)^1623
        have hw : |(21240183/50000000 : ℝ)|=(21240183/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_12 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-30848843/156250000 : ℝ)*x 0 + (5476339877/10000000000 : ℝ)*x 1 + (5253125647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30848843/156250000 : ℝ)^2135 ≤ (11834448680327/100000000000000 : ℝ)^1623 := by
    have hnat : (30848843 : ℕ)^2135*100000000000000^1623 ≤ 11834448680327^1623*156250000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30848843 156250000 11834448680327 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476339877/10000000000 : ℝ)^2135 ≤ (11322262654379/25000000000000 : ℝ)^1623 := by
    have hnat : (5476339877 : ℕ)^2135*25000000000000^1623 ≤ 11322262654379^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476339877 10000000000 11322262654379 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253125647/10000000000 : ℝ)^2135 ≤ (42876500690279/100000000000000 : ℝ)^1623 := by
    have hnat : (5253125647 : ℕ)^2135*100000000000000^1623 ≤ 42876500690279^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253125647 10000000000 42876500690279 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-30848843/156250000 : ℝ), (5476339877/10000000000 : ℝ), (5253125647/10000000000 : ℝ)] ![(11834448680327/100000000000000 : ℝ), (11322262654379/25000000000000 : ℝ), (42876500690279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-30848843/156250000 : ℝ)|^2135 ≤ (11834448680327/100000000000000 : ℝ)^1623
        have hw : |(-30848843/156250000 : ℝ)|=(30848843/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476339877/10000000000 : ℝ)|^2135 ≤ (11322262654379/25000000000000 : ℝ)^1623
        have hw : |(5476339877/10000000000 : ℝ)|=(5476339877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253125647/10000000000 : ℝ)|^2135 ≤ (42876500690279/100000000000000 : ℝ)^1623
        have hw : |(5253125647/10000000000 : ℝ)|=(5253125647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_13 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5381841113/10000000000 : ℝ)*x 0 + (-8215007/39062500 : ℝ)*x 1 + (82080089/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381841113/10000000000 : ℝ)^2135 ≤ (44263823859763/100000000000000 : ℝ)^1623 := by
    have hnat : (5381841113 : ℕ)^2135*100000000000000^1623 ≤ 44263823859763^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381841113 10000000000 44263823859763 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8215007/39062500 : ℝ)^2135 ≤ (10046621019/78125000000 : ℝ)^1623 := by
    have hnat : (8215007 : ℕ)^2135*78125000000^1623 ≤ 10046621019^1623*39062500^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8215007 39062500 10046621019 78125000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82080089/156250000 : ℝ)^2135 ≤ (4287650121639/10000000000000 : ℝ)^1623 := by
    have hnat : (82080089 : ℕ)^2135*10000000000000^1623 ≤ 4287650121639^1623*156250000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82080089 156250000 4287650121639 10000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381841113/10000000000 : ℝ), (-8215007/39062500 : ℝ), (82080089/156250000 : ℝ)] ![(44263823859763/100000000000000 : ℝ), (10046621019/78125000000 : ℝ), (4287650121639/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381841113/10000000000 : ℝ)|^2135 ≤ (44263823859763/100000000000000 : ℝ)^1623
        have hw : |(5381841113/10000000000 : ℝ)|=(5381841113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8215007/39062500 : ℝ)|^2135 ≤ (10046621019/78125000000 : ℝ)^1623
        have hw : |(-8215007/39062500 : ℝ)|=(8215007/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82080089/156250000 : ℝ)|^2135 ≤ (4287650121639/10000000000000 : ℝ)^1623
        have hw : |(82080089/156250000 : ℝ)|=(82080089/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_14 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5381840973/10000000000 : ℝ)*x 0 + (5253126137/10000000000 : ℝ)*x 1 + (-2103041393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381840973/10000000000 : ℝ)^2135 ≤ (44263822345067/100000000000000 : ℝ)^1623 := by
    have hnat : (5381840973 : ℕ)^2135*100000000000000^1623 ≤ 44263822345067^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381840973 10000000000 44263822345067 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253126137/10000000000 : ℝ)^2135 ≤ (5359563243923/12500000000000 : ℝ)^1623 := by
    have hnat : (5253126137 : ℕ)^2135*12500000000000^1623 ≤ 5359563243923^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253126137 10000000000 5359563243923 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2103041393/10000000000 : ℝ)^2135 ≤ (6429835847421/50000000000000 : ℝ)^1623 := by
    have hnat : (2103041393 : ℕ)^2135*50000000000000^1623 ≤ 6429835847421^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103041393 10000000000 6429835847421 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381840973/10000000000 : ℝ), (5253126137/10000000000 : ℝ), (-2103041393/10000000000 : ℝ)] ![(44263822345067/100000000000000 : ℝ), (5359563243923/12500000000000 : ℝ), (6429835847421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381840973/10000000000 : ℝ)|^2135 ≤ (44263822345067/100000000000000 : ℝ)^1623
        have hw : |(5381840973/10000000000 : ℝ)|=(5381840973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253126137/10000000000 : ℝ)|^2135 ≤ (5359563243923/12500000000000 : ℝ)^1623
        have hw : |(5253126137/10000000000 : ℝ)|=(5253126137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2103041393/10000000000 : ℝ)|^2135 ≤ (6429835847421/50000000000000 : ℝ)^1623
        have hw : |(-2103041393/10000000000 : ℝ)|=(2103041393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_box_15 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (519851373/1250000000 : ℝ)*x 0 + (2213426713/5000000000 : ℝ)*x 1 + (4426852381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519851373/1250000000 : ℝ)^2135 ≤ (3153314035241/10000000000000 : ℝ)^1623 := by
    have hnat : (519851373 : ℕ)^2135*10000000000000^1623 ≤ 3153314035241^1623*1250000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519851373 1250000000 3153314035241 10000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213426713/5000000000 : ℝ)^2135 ≤ (34233435130523/100000000000000 : ℝ)^1623 := by
    have hnat : (2213426713 : ℕ)^2135*100000000000000^1623 ≤ 34233435130523^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213426713 5000000000 34233435130523 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4426852381/10000000000 : ℝ)^2135 ≤ (3423342450009/10000000000000 : ℝ)^1623 := by
    have hnat : (4426852381 : ℕ)^2135*10000000000000^1623 ≤ 3423342450009^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426852381 10000000000 3423342450009 10000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519851373/1250000000 : ℝ), (2213426713/5000000000 : ℝ), (4426852381/10000000000 : ℝ)] ![(3153314035241/10000000000000 : ℝ), (34233435130523/100000000000000 : ℝ), (3423342450009/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519851373/1250000000 : ℝ)|^2135 ≤ (3153314035241/10000000000000 : ℝ)^1623
        have hw : |(519851373/1250000000 : ℝ)|=(519851373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2213426713/5000000000 : ℝ)|^2135 ≤ (34233435130523/100000000000000 : ℝ)^1623
        have hw : |(2213426713/5000000000 : ℝ)|=(2213426713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4426852381/10000000000 : ℝ)|^2135 ≤ (3423342450009/10000000000000 : ℝ)^1623
        have hw : |(4426852381/10000000000 : ℝ)|=(4426852381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1310_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11073/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15711/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58879/100000 : ℝ) ∧ (15953/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42113/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2937/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11073/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2937/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11073/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2937/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11073/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2937/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11073/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2937/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11073/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2937/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11073/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11073/100000 : ℝ) ^ (4269/1024 : ℝ) ≤ (5182798285457109/50000000000000000000 : ℝ) := by
    have hpowers : (11073/100000 : ℝ)^4269 ≤ (5182798285457109/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11073 : ℕ)^4269*50000000000000000000^1024 ≤ 5182798285457109^1024*100000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11073 100000 5182798285457109 50000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11073/100000 : ℝ)) (X := (5182798285457109/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2937/20000 : ℝ) ^ (4269/1024 : ℝ) ≤ (16815627064544487/50000000000000000000 : ℝ) := by
    have hpowers : (2937/20000 : ℝ)^4269 ≤ (16815627064544487/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2937 : ℕ)^4269*50000000000000000000^1024 ≤ 16815627064544487^1024*20000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2937 20000 16815627064544487 50000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2937/20000 : ℝ)) (X := (16815627064544487/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005182798285457109/25000000000000000000 : ℝ) ≤ (10000497237510491/10000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (25005182798285457109/25000000000000000000 : ℝ)^1024 ≤ (10000497237510491/10000000000000000 : ℝ)^4269 := by
      have hnat : (25005182798285457109 : ℕ)^1024*10000000000000000^4269 ≤ 10000497237510491^4269*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005182798285457109 25000000000000000000 10000497237510491 10000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000497237510491/10000000000000000 : ℝ)) (X := (25005182798285457109/25000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505499606337500399/12500000000000000000 : ℝ) ≤ (10001055170847411/10000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (12505499606337500399/12500000000000000000 : ℝ)^1024 ≤ (10001055170847411/10000000000000000 : ℝ)^4269 := by
      have hnat : (12505499606337500399 : ℕ)^1024*10000000000000000^4269 ≤ 10001055170847411^4269*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505499606337500399 12500000000000000000 10001055170847411 10000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001055170847411/10000000000000000 : ℝ)) (X := (12505499606337500399/12500000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016815627064544487/25000000000000000000 : ℝ) ≤ (10001613104184331/10000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (25016815627064544487/25000000000000000000 : ℝ)^1024 ≤ (10001613104184331/10000000000000000 : ℝ)^4269 := by
      have hnat : (25016815627064544487 : ℕ)^1024*10000000000000000^4269 ≤ 10001613104184331^4269*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016815627064544487 25000000000000000000 10001613104184331 10000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001613104184331/10000000000000000 : ℝ)) (X := (25016815627064544487/25000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5182798285457109/50000000000000000000 : ℝ) ≤ ((3009120002517371931/3010000000000000000 : ℝ)+2*(13948333423/9030000000000 : ℝ)*(11073/100000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (3009120002517371931/3010000000000000000 : ℝ)+2*(13948333423/9030000000000 : ℝ)*(11073/100000 : ℝ)=(10000497237510491/10000000000000000 : ℝ) by norm_num, show 1+2*(5182798285457109/50000000000000000000 : ℝ)=(25005182798285457109/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16815627064544487/50000000000000000000 : ℝ)+(5182798285457109/50000000000000000000 : ℝ) ≤ ((3009120002517371931/3010000000000000000 : ℝ)+(13948333423/9030000000000 : ℝ)*((2937/20000 : ℝ)+(11073/100000 : ℝ)))^(4269/1024 : ℝ) := by
    rw [show (3009120002517371931/3010000000000000000 : ℝ)+(13948333423/9030000000000 : ℝ)*((2937/20000 : ℝ)+(11073/100000 : ℝ))=(10001055170847411/10000000000000000 : ℝ) by norm_num, show 1+(16815627064544487/50000000000000000000 : ℝ)+(5182798285457109/50000000000000000000 : ℝ)=(12505499606337500399/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16815627064544487/50000000000000000000 : ℝ) ≤ ((3009120002517371931/3010000000000000000 : ℝ)+2*(13948333423/9030000000000 : ℝ)*(2937/20000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (3009120002517371931/3010000000000000000 : ℝ)+2*(13948333423/9030000000000 : ℝ)*(2937/20000 : ℝ)=(10001613104184331/10000000000000000 : ℝ) by norm_num, show 1+2*(16815627064544487/50000000000000000000 : ℝ)=(25016815627064544487/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3009120002517371931/3010000000000000000 : ℝ)*(X 1 0+X 2 0)+(13948333423/9030000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (11073/100000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (3009120002517371931/3010000000000000000 : ℝ)) (alpha := (13948333423/9030000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3009120002517371931/3010000000000000000 : ℝ)*(X 0 1+X 2 1)+(13948333423/9030000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (11073/100000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (3009120002517371931/3010000000000000000 : ℝ)) (alpha := (13948333423/9030000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3009120002517371931/3010000000000000000 : ℝ)*(X 0 2+X 1 2)+(13948333423/9030000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (11073/100000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (3009120002517371931/3010000000000000000 : ℝ)) (alpha := (13948333423/9030000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1902099157/10000000000 : ℝ)*X 0 0+(5391271081/10000000000 : ℝ)*X 0 1+(5391271063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284681197/10000000000 : ℝ)*X 1 0+(-1023982731/5000000000 : ℝ)*X 1 1+(2695635459/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1056936193/2000000000 : ℝ)*X 2 0+(336954447/625000000 : ℝ)*X 2 1+(-127997841/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((448402657/1000000000 : ℝ)*X 0 0+(2132269209/5000000000 : ℝ)*X 0 1+(4264538511/10000000000 : ℝ)*X 0 2+(448402657/1000000000 : ℝ)*X 1 0+(2132269209/5000000000 : ℝ)*X 1 1+(4264538511/10000000000 : ℝ)*X 1 2+(448402657/1000000000 : ℝ)*X 2 0+(2132269209/5000000000 : ℝ)*X 2 1+(4264538511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-280568559/1250000000 : ℝ)*X 0 0+(5264166471/10000000000 : ℝ)*X 0 1+(1316041699/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374078147/10000000000 : ℝ)*X 1 0+(-1049368399/5000000000 : ℝ)*X 1 1+(1052833373/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1343519527/2500000000 : ℝ)*X 2 0+(5264166687/10000000000 : ℝ)*X 2 1+(-32792767/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4185214581/10000000000 : ℝ)*X 0 0+(2206945009/5000000000 : ℝ)*X 0 1+(4413889483/10000000000 : ℝ)*X 0 2+(4185214581/10000000000 : ℝ)*X 1 0+(2206945009/5000000000 : ℝ)*X 1 1+(4413889483/10000000000 : ℝ)*X 1 2+(4185214581/10000000000 : ℝ)*X 2 0+(2206945009/5000000000 : ℝ)*X 2 1+(4413889483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2172722841/10000000000 : ℝ)*X 0 0+(5176818011/10000000000 : ℝ)*X 0 1+(1351325879/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1054961151/2000000000 : ℝ)*X 1 0+(-1021112777/5000000000 : ℝ)*X 1 1+(1351325841/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1318701467/2500000000 : ℝ)*X 2 0+(2702651521/5000000000 : ℝ)*X 2 1+(-25527823/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1129113799/2500000000 : ℝ)*X 0 0+(132751141/312500000 : ℝ)*X 0 1+(21240183/50000000 : ℝ)*X 0 2+(1129113799/2500000000 : ℝ)*X 1 0+(132751141/312500000 : ℝ)*X 1 1+(21240183/50000000 : ℝ)*X 1 2+(1129113799/2500000000 : ℝ)*X 2 0+(132751141/312500000 : ℝ)*X 2 1+(21240183/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-30848843/156250000 : ℝ)*X 0 0+(5476339877/10000000000 : ℝ)*X 0 1+(5253125647/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5381841113/10000000000 : ℝ)*X 1 0+(-8215007/39062500 : ℝ)*X 1 1+(82080089/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5381840973/10000000000 : ℝ)*X 2 0+(5253126137/10000000000 : ℝ)*X 2 1+(-2103041393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((519851373/1250000000 : ℝ)*X 0 0+(2213426713/5000000000 : ℝ)*X 0 1+(4426852381/10000000000 : ℝ)*X 0 2+(519851373/1250000000 : ℝ)*X 1 0+(2213426713/5000000000 : ℝ)*X 1 1+(4426852381/10000000000 : ℝ)*X 1 2+(519851373/1250000000 : ℝ)*X 2 0+(2213426713/5000000000 : ℝ)*X 2 1+(4426852381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15711/25000 : ℝ) ≤ (-47288367389861360993330006150159/75250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93913729/50000000000000 : ℝ)*(upper1) + (135346423/100000000000000 : ℝ)*(upper2) + (9311959/25000000000000 : ℝ)*(upper3) + (77715109/100000000000000 : ℝ)*(upper5) + (1442273486261179/50000000000000 : ℝ)*(major0) + (1442273486261179/50000000000000 : ℝ)*(major1) + (1442273486261179/50000000000000 : ℝ)*(major2) + (2133336307/50000000000000 : ℝ)*(sp3) + (1955239558158959/50000000000000 : ℝ)*(sp4) + (3910318298267609/100000000000000 : ℝ)*(sp5) + (3910473001368969/100000000000000 : ℝ)*(sp6) + (1879557790133843/100000000000000 : ℝ)*(sp7) + (16081805031/10000000000000 : ℝ)*(sp13) + (122298979/2000000000000 : ℝ)*(sp14) + (1879562056806457/100000000000000 : ℝ)*(f.failure) + (1955239558158959/50000000000000 : ℝ)*(f.sum) + (2763703569833/903000000000000000000000000 : ℝ)*base66 + (866250060634328579/64500000000000000000000000000000 : ℝ)*base68 + (457144004465828579/64500000000000000000000000000000 : ℝ)*base70 + (679262181358328579/64500000000000000000000000000000 : ℝ)*base72 + (87363594287/112875000000000000000000000 : ℝ)*base73 + (1267708462162328579/64500000000000000000000000000000 : ℝ)*base76 + (1382410443818828579/64500000000000000000000000000000 : ℝ)*base78 + (1173200044271828579/64500000000000000000000000000000 : ℝ)*base80 + (3776126326387/180600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (299787/100000000000000000000 : ℝ)*base89 + (299787/100000000000000000000 : ℝ)*base91 + (299787/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58879/100000 : ℝ) ≤ (177234529600486333268798437/301000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2768063/50000000000000 : ℝ)*(lower0) + (3161351/20000000000000 : ℝ)*(upper2) + (15717861/50000000000000 : ℝ)*(lower4) + (738041447392141/25000000000000 : ℝ)*(major0) + (738041447392141/25000000000000 : ℝ)*(major1) + (738041447392141/25000000000000 : ℝ)*(major2) + (198054063156381/5000000000000 : ℝ)*(sp0) + (990262094732883/25000000000000 : ℝ)*(sp1) + (3961080724596709/100000000000000 : ℝ)*(sp2) + (961810750220189/50000000000000 : ℝ)*(sp3) + (1280499467/100000000000000 : ℝ)*(sp6) + (154485329/20000000000000 : ℝ)*(sp7) + (33626164643/100000000000000 : ℝ)*(sp9) + (148393711/20000000000000 : ℝ)*(sp12) + (1923622272867023/100000000000000 : ℝ)*(f.failure) + (247567625318511/6250000000000 : ℝ)*(f.sum) + (13436564279129/903000000000000000000000000 : ℝ)*base65 + (671529975728366741/32250000000000000000000000000000 : ℝ)*base68 + (20040144346383259/32250000000000000000000000000000 : ℝ)*base69 + (30401532835383259/32250000000000000000000000000000 : ℝ)*base71 + (43066823197/22575000000000000000000000 : ℝ)*base74 + (92527038530366741/32250000000000000000000000000000 : ℝ)*base76 + (588984808483383259/32250000000000000000000000000000 : ℝ)*base77 + (556190096682866741/32250000000000000000000000000000 : ℝ)*base80 + (176149899913/180600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (394893/100000000000000000000 : ℝ)*base89 + (394893/100000000000000000000 : ℝ)*base91 + (394893/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (15953/20000 : ℝ) ≤ (60025018727449025475932479930693/75250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72484127/100000000000000 : ℝ)*(upper0) + (12230469/12500000000000 : ℝ)*(upper1) + (90054767/100000000000000 : ℝ)*(upper2) + (1632763378839301/50000000000000 : ℝ)*(major0) + (1632763378839301/50000000000000 : ℝ)*(major1) + (1632763378839301/50000000000000 : ℝ)*(major2) + (70635314909/50000000000000 : ℝ)*(sp1) + (39378911271/100000000000000 : ℝ)*(sp3) + (2550880667/25000000000000 : ℝ)*(sp4) + (4376645321725431/100000000000000 : ℝ)*(sp8) + (2188257880030661/50000000000000 : ℝ)*(sp9) + (218832851534557/5000000000000 : ℝ)*(sp10) + (132985496885769/6250000000000 : ℝ)*(sp11) + (752721521/50000000000000 : ℝ)*(sp12) + (85112293163343/4000000000000 : ℝ)*(f.failure) + (218832851534557/5000000000000 : ℝ)*(f.sum) + (630395253317/903000000000000000000000000 : ℝ)*base66 + (353483009332759901/64500000000000000000000000000000 : ℝ)*base68 + (126621548557759901/64500000000000000000000000000000 : ℝ)*base70 + (44679284492740099/64500000000000000000000000000000 : ℝ)*base71 + (909372222187/451500000000000000000000000 : ℝ)*base74 + (37068174649240099/64500000000000000000000000000000 : ℝ)*base75 + (174425233035259901/64500000000000000000000000000000 : ℝ)*base78 + (171338858499259901/64500000000000000000000000000000 : ℝ)*base80 + (1217004802451/903000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (47987/4000000000000000000 : ℝ)*base90 + (47987/4000000000000000000 : ℝ)*base92 + (47987/4000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42113/50000 : ℝ) ≤ (-63378476582817125659237677962893/75250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37660659/10000000000000 : ℝ)*(lower0) + (12769701/100000000000000 : ℝ)*(upper3) + (308534437/100000000000000 : ℝ)*(upper5) + (3301618303155299/100000000000000 : ℝ)*(major0) + (3301618303155299/100000000000000 : ℝ)*(major1) + (3301618303155299/100000000000000 : ℝ)*(major2) + (51814943/2000000000000 : ℝ)*(sp0) + (80793622481/100000000000000 : ℝ)*(sp5) + (33048416189/100000000000000 : ℝ)*(sp7) + (1028366581/25000000000000 : ℝ)*(sp8) + (895996012236571/20000000000000 : ℝ)*(sp12) + (559988246471731/12500000000000 : ℝ)*(sp13) + (4479986765396329/100000000000000 : ℝ)*(sp14) + (2151291422213599/100000000000000 : ℝ)*(sp15) + (2151324470629787/100000000000000 : ℝ)*(f.failure) + (4479986765396329/100000000000000 : ℝ)*(f.sum) + (2803896824639/903000000000000000000000000 : ℝ)*base66 + (903786543155494699/129000000000000000000000000000000 : ℝ)*base68 + (1923697462955494699/129000000000000000000000000000000 : ℝ)*base70 + (1834209057554494699/129000000000000000000000000000000 : ℝ)*base72 + (4603247820803/225750000000000000000000000 : ℝ)*base74 + (1828520289521494699/129000000000000000000000000000000 : ℝ)*base76 + (1470603541148494699/129000000000000000000000000000000 : ℝ)*base78 + (3907241170248505301/129000000000000000000000000000000 : ℝ)*base79 + (2392229940773/903000000000000000000000000 : ℝ)*base82 + (559183/100000000000000000000 : ℝ)*base90 + (559183/100000000000000000000 : ℝ)*base92 + (559183/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1310_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11073/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15711/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58879/100000 : ℝ) else (15953/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42113/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1310_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1310_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15711/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58879/100000 : ℝ) else (15953/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42113/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1310_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1310_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1310_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15711/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58879/100000 : ℝ) else (15953/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42113/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1310_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
