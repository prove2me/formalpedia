-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b016
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:08:49.310043+00:00
-- url     : https://prove2.me/submissions/57ceb4de-87d6-48c7-a657-42aae4ff980c

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c326037_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-97165121/1250000000 : ℝ)*x 0 + (-3379396781/5000000000 : ℝ)*x 1 + (102026951/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97165121/1250000000 : ℝ)^89 ≤ (555078384129/12500000000000 : ℝ)^73 := by
    have hnat : (97165121 : ℕ)^89*12500000000000^73 ≤ 555078384129^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97165121 1250000000 555078384129 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3379396781/5000000000 : ℝ)^89 ≤ (15506730671807/25000000000000 : ℝ)^73 := by
    have hnat : (3379396781 : ℕ)^89*25000000000000^73 ≤ 15506730671807^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3379396781 5000000000 15506730671807 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102026951/250000000 : ℝ)^89 ≤ (33532450221787/100000000000000 : ℝ)^73 := by
    have hnat : (102026951 : ℕ)^89*100000000000000^73 ≤ 33532450221787^73*250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102026951 250000000 33532450221787 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-97165121/1250000000 : ℝ), (-3379396781/5000000000 : ℝ), (102026951/250000000 : ℝ)] ![(555078384129/12500000000000 : ℝ), (15506730671807/25000000000000 : ℝ), (33532450221787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-97165121/1250000000 : ℝ)|^89 ≤ (555078384129/12500000000000 : ℝ)^73
        have hw : |(-97165121/1250000000 : ℝ)|=(97165121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3379396781/5000000000 : ℝ)|^89 ≤ (15506730671807/25000000000000 : ℝ)^73
        have hw : |(-3379396781/5000000000 : ℝ)|=(3379396781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(102026951/250000000 : ℝ)|^89 ≤ (33532450221787/100000000000000 : ℝ)^73
        have hw : |(102026951/250000000 : ℝ)|=(102026951/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4916663741/10000000000 : ℝ)*x 0 + (-2970330197/10000000000 : ℝ)*x 1 + (-4242273387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4916663741/10000000000 : ℝ)^89 ≤ (5260190265729/12500000000000 : ℝ)^73 := by
    have hnat : (4916663741 : ℕ)^89*12500000000000^73 ≤ 5260190265729^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4916663741 10000000000 5260190265729 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2970330197/10000000000 : ℝ)^89 ≤ (11382170492619/50000000000000 : ℝ)^73 := by
    have hnat : (2970330197 : ℕ)^89*50000000000000^73 ≤ 11382170492619^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2970330197 10000000000 11382170492619 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242273387/10000000000 : ℝ)^89 ≤ (1098566777481/3125000000000 : ℝ)^73 := by
    have hnat : (4242273387 : ℕ)^89*3125000000000^73 ≤ 1098566777481^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242273387 10000000000 1098566777481 3125000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4916663741/10000000000 : ℝ), (-2970330197/10000000000 : ℝ), (-4242273387/10000000000 : ℝ)] ![(5260190265729/12500000000000 : ℝ), (11382170492619/50000000000000 : ℝ), (1098566777481/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4916663741/10000000000 : ℝ)|^89 ≤ (5260190265729/12500000000000 : ℝ)^73
        have hw : |(4916663741/10000000000 : ℝ)|=(4916663741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2970330197/10000000000 : ℝ)|^89 ≤ (11382170492619/50000000000000 : ℝ)^73
        have hw : |(-2970330197/10000000000 : ℝ)|=(2970330197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4242273387/10000000000 : ℝ)|^89 ≤ (1098566777481/3125000000000 : ℝ)^73
        have hw : |(-4242273387/10000000000 : ℝ)|=(4242273387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8041645491/10000000000 : ℝ)*x 0 + (-1285448787/10000000000 : ℝ)*x 1 + (2125253119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8041645491/10000000000 : ℝ)^89 ≤ (76665258716873/100000000000000 : ℝ)^73 := by
    have hnat : (8041645491 : ℕ)^89*100000000000000^73 ≤ 76665258716873^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8041645491 10000000000 76665258716873 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285448787/10000000000 : ℝ)^89 ≤ (8199344121387/100000000000000 : ℝ)^73 := by
    have hnat : (1285448787 : ℕ)^89*100000000000000^73 ≤ 8199344121387^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285448787 10000000000 8199344121387 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125253119/10000000000 : ℝ)^89 ≤ (1513539714337/10000000000000 : ℝ)^73 := by
    have hnat : (2125253119 : ℕ)^89*10000000000000^73 ≤ 1513539714337^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125253119 10000000000 1513539714337 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8041645491/10000000000 : ℝ), (-1285448787/10000000000 : ℝ), (2125253119/10000000000 : ℝ)] ![(76665258716873/100000000000000 : ℝ), (8199344121387/100000000000000 : ℝ), (1513539714337/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8041645491/10000000000 : ℝ)|^89 ≤ (76665258716873/100000000000000 : ℝ)^73
        have hw : |(8041645491/10000000000 : ℝ)|=(8041645491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1285448787/10000000000 : ℝ)|^89 ≤ (8199344121387/100000000000000 : ℝ)^73
        have hw : |(-1285448787/10000000000 : ℝ)|=(1285448787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125253119/10000000000 : ℝ)|^89 ≤ (1513539714337/10000000000000 : ℝ)^73
        have hw : |(2125253119/10000000000 : ℝ)|=(2125253119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-375856629/5000000000 : ℝ)*x 0 + (-7358517013/10000000000 : ℝ)*x 1 + (3409953453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375856629/5000000000 : ℝ)^89 ≤ (1065730751739/25000000000000 : ℝ)^73 := by
    have hnat : (375856629 : ℕ)^89*25000000000000^73 ≤ 1065730751739^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375856629 5000000000 1065730751739 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7358517013/10000000000 : ℝ)^89 ≤ (34400412928771/50000000000000 : ℝ)^73 := by
    have hnat : (7358517013 : ℕ)^89*50000000000000^73 ≤ 34400412928771^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7358517013 10000000000 34400412928771 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3409953453/10000000000 : ℝ)^89 ≤ (2693625112547/10000000000000 : ℝ)^73 := by
    have hnat : (3409953453 : ℕ)^89*10000000000000^73 ≤ 2693625112547^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3409953453 10000000000 2693625112547 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375856629/5000000000 : ℝ), (-7358517013/10000000000 : ℝ), (3409953453/10000000000 : ℝ)] ![(1065730751739/25000000000000 : ℝ), (34400412928771/50000000000000 : ℝ), (2693625112547/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375856629/5000000000 : ℝ)|^89 ≤ (1065730751739/25000000000000 : ℝ)^73
        have hw : |(-375856629/5000000000 : ℝ)|=(375856629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7358517013/10000000000 : ℝ)|^89 ≤ (34400412928771/50000000000000 : ℝ)^73
        have hw : |(-7358517013/10000000000 : ℝ)|=(7358517013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3409953453/10000000000 : ℝ)|^89 ≤ (2693625112547/10000000000000 : ℝ)^73
        have hw : |(3409953453/10000000000 : ℝ)|=(3409953453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4842518449/10000000000 : ℝ)*x 0 + (1471053169/5000000000 : ℝ)*x 1 + (2172267761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4842518449/10000000000 : ℝ)^89 ≤ (10327276874763/25000000000000 : ℝ)^73 := by
    have hnat : (4842518449 : ℕ)^89*25000000000000^73 ≤ 10327276874763^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4842518449 10000000000 10327276874763 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1471053169/5000000000 : ℝ)^89 ≤ (11250450923103/50000000000000 : ℝ)^73 := by
    have hnat : (1471053169 : ℕ)^89*50000000000000^73 ≤ 11250450923103^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1471053169 5000000000 11250450923103 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172267761/5000000000 : ℝ)^89 ≤ (36189990643217/100000000000000 : ℝ)^73 := by
    have hnat : (2172267761 : ℕ)^89*100000000000000^73 ≤ 36189990643217^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172267761 5000000000 36189990643217 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4842518449/10000000000 : ℝ), (1471053169/5000000000 : ℝ), (2172267761/5000000000 : ℝ)] ![(10327276874763/25000000000000 : ℝ), (11250450923103/50000000000000 : ℝ), (36189990643217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4842518449/10000000000 : ℝ)|^89 ≤ (10327276874763/25000000000000 : ℝ)^73
        have hw : |(4842518449/10000000000 : ℝ)|=(4842518449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1471053169/5000000000 : ℝ)|^89 ≤ (11250450923103/50000000000000 : ℝ)^73
        have hw : |(1471053169/5000000000 : ℝ)|=(1471053169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2172267761/5000000000 : ℝ)|^89 ≤ (36189990643217/100000000000000 : ℝ)^73
        have hw : |(2172267761/5000000000 : ℝ)|=(2172267761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2421259121/5000000000 : ℝ)*x 0 + (-2728044747/10000000000 : ℝ)*x 1 + (-1134633093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2421259121/5000000000 : ℝ)^89 ≤ (41309105346211/100000000000000 : ℝ)^73 := by
    have hnat : (2421259121 : ℕ)^89*100000000000000^73 ≤ 41309105346211^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2421259121 5000000000 41309105346211 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728044747/10000000000 : ℝ)^89 ≤ (5130297022907/25000000000000 : ℝ)^73 := by
    have hnat : (2728044747 : ℕ)^89*25000000000000^73 ≤ 5130297022907^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728044747 10000000000 5130297022907 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134633093/2500000000 : ℝ)^89 ≤ (38169706545869/100000000000000 : ℝ)^73 := by
    have hnat : (1134633093 : ℕ)^89*100000000000000^73 ≤ 38169706545869^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134633093 2500000000 38169706545869 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2421259121/5000000000 : ℝ), (-2728044747/10000000000 : ℝ), (-1134633093/2500000000 : ℝ)] ![(41309105346211/100000000000000 : ℝ), (5130297022907/25000000000000 : ℝ), (38169706545869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2421259121/5000000000 : ℝ)|^89 ≤ (41309105346211/100000000000000 : ℝ)^73
        have hw : |(2421259121/5000000000 : ℝ)|=(2421259121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2728044747/10000000000 : ℝ)|^89 ≤ (5130297022907/25000000000000 : ℝ)^73
        have hw : |(-2728044747/10000000000 : ℝ)|=(2728044747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1134633093/2500000000 : ℝ)|^89 ≤ (38169706545869/100000000000000 : ℝ)^73
        have hw : |(-1134633093/2500000000 : ℝ)|=(1134633093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3978979029/5000000000 : ℝ)*x 0 + (-534503887/10000000000 : ℝ)*x 1 + (2833620269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3978979029/5000000000 : ℝ)^89 ≤ (75693666236643/100000000000000 : ℝ)^73 := by
    have hnat : (3978979029 : ℕ)^89*100000000000000^73 ≤ 75693666236643^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3978979029 5000000000 75693666236643 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534503887/10000000000 : ℝ)^89 ≤ (2812843557373/100000000000000 : ℝ)^73 := by
    have hnat : (534503887 : ℕ)^89*100000000000000^73 ≤ 2812843557373^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534503887 10000000000 2812843557373 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2833620269/10000000000 : ℝ)^89 ≤ (10746745097591/50000000000000 : ℝ)^73 := by
    have hnat : (2833620269 : ℕ)^89*50000000000000^73 ≤ 10746745097591^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2833620269 10000000000 10746745097591 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3978979029/5000000000 : ℝ), (-534503887/10000000000 : ℝ), (2833620269/10000000000 : ℝ)] ![(75693666236643/100000000000000 : ℝ), (2812843557373/100000000000000 : ℝ), (10746745097591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3978979029/5000000000 : ℝ)|^89 ≤ (75693666236643/100000000000000 : ℝ)^73
        have hw : |(3978979029/5000000000 : ℝ)|=(3978979029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534503887/10000000000 : ℝ)|^89 ≤ (2812843557373/100000000000000 : ℝ)^73
        have hw : |(-534503887/10000000000 : ℝ)|=(534503887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2833620269/10000000000 : ℝ)|^89 ≤ (10746745097591/50000000000000 : ℝ)^73
        have hw : |(2833620269/10000000000 : ℝ)|=(2833620269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-13642433/400000000 : ℝ)*x 0 + (-6658409593/10000000000 : ℝ)*x 1 + (4469970607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13642433/400000000 : ℝ)^89 ≤ (813262483979/50000000000000 : ℝ)^73 := by
    have hnat : (13642433 : ℕ)^89*50000000000000^73 ≤ 813262483979^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13642433 400000000 813262483979 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6658409593/10000000000 : ℝ)^89 ≤ (12181119100903/20000000000000 : ℝ)^73 := by
    have hnat : (6658409593 : ℕ)^89*20000000000000^73 ≤ 12181119100903^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6658409593 10000000000 12181119100903 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4469970607/10000000000 : ℝ)^89 ≤ (37467879515593/100000000000000 : ℝ)^73 := by
    have hnat : (4469970607 : ℕ)^89*100000000000000^73 ≤ 37467879515593^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4469970607 10000000000 37467879515593 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13642433/400000000 : ℝ), (-6658409593/10000000000 : ℝ), (4469970607/10000000000 : ℝ)] ![(813262483979/50000000000000 : ℝ), (12181119100903/20000000000000 : ℝ), (37467879515593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13642433/400000000 : ℝ)|^89 ≤ (813262483979/50000000000000 : ℝ)^73
        have hw : |(-13642433/400000000 : ℝ)|=(13642433/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6658409593/10000000000 : ℝ)|^89 ≤ (12181119100903/20000000000000 : ℝ)^73
        have hw : |(-6658409593/10000000000 : ℝ)|=(6658409593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4469970607/10000000000 : ℝ)|^89 ≤ (37467879515593/100000000000000 : ℝ)^73
        have hw : |(4469970607/10000000000 : ℝ)|=(4469970607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2366032799/5000000000 : ℝ)*x 0 + (773399723/2500000000 : ℝ)*x 1 + (4317482041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2366032799/5000000000 : ℝ)^89 ≤ (20081632203991/50000000000000 : ℝ)^73 := by
    have hnat : (2366032799 : ℕ)^89*50000000000000^73 ≤ 20081632203991^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366032799 5000000000 20081632203991 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (773399723/2500000000 : ℝ)^89 ≤ (11960652846747/50000000000000 : ℝ)^73 := by
    have hnat : (773399723 : ℕ)^89*50000000000000^73 ≤ 11960652846747^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773399723 2500000000 11960652846747 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4317482041/10000000000 : ℝ)^89 ≤ (35915429883469/100000000000000 : ℝ)^73 := by
    have hnat : (4317482041 : ℕ)^89*100000000000000^73 ≤ 35915429883469^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317482041 10000000000 35915429883469 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2366032799/5000000000 : ℝ), (773399723/2500000000 : ℝ), (4317482041/10000000000 : ℝ)] ![(20081632203991/50000000000000 : ℝ), (11960652846747/50000000000000 : ℝ), (35915429883469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2366032799/5000000000 : ℝ)|^89 ≤ (20081632203991/50000000000000 : ℝ)^73
        have hw : |(2366032799/5000000000 : ℝ)|=(2366032799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(773399723/2500000000 : ℝ)|^89 ≤ (11960652846747/50000000000000 : ℝ)^73
        have hw : |(773399723/2500000000 : ℝ)|=(773399723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4317482041/10000000000 : ℝ)|^89 ≤ (35915429883469/100000000000000 : ℝ)^73
        have hw : |(4317482041/10000000000 : ℝ)|=(4317482041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1072298323/2000000000 : ℝ)*x 0 + (-1384903187/5000000000 : ℝ)*x 1 + (-3960342651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072298323/2000000000 : ℝ)^89 ≤ (46768234426391/100000000000000 : ℝ)^73 := by
    have hnat : (1072298323 : ℕ)^89*100000000000000^73 ≤ 46768234426391^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072298323 2000000000 46768234426391 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1384903187/5000000000 : ℝ)^89 ≤ (4180965048907/20000000000000 : ℝ)^73 := by
    have hnat : (1384903187 : ℕ)^89*20000000000000^73 ≤ 4180965048907^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384903187 5000000000 4180965048907 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3960342651/10000000000 : ℝ)^89 ≤ (2020433769739/6250000000000 : ℝ)^73 := by
    have hnat : (3960342651 : ℕ)^89*6250000000000^73 ≤ 2020433769739^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3960342651 10000000000 2020433769739 6250000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072298323/2000000000 : ℝ), (-1384903187/5000000000 : ℝ), (-3960342651/10000000000 : ℝ)] ![(46768234426391/100000000000000 : ℝ), (4180965048907/20000000000000 : ℝ), (2020433769739/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072298323/2000000000 : ℝ)|^89 ≤ (46768234426391/100000000000000 : ℝ)^73
        have hw : |(1072298323/2000000000 : ℝ)|=(1072298323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1384903187/5000000000 : ℝ)|^89 ≤ (4180965048907/20000000000000 : ℝ)^73
        have hw : |(-1384903187/5000000000 : ℝ)|=(1384903187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3960342651/10000000000 : ℝ)|^89 ≤ (2020433769739/6250000000000 : ℝ)^73
        have hw : |(-3960342651/10000000000 : ℝ)|=(3960342651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4320844161/5000000000 : ℝ)*x 0 + (-1143351551/10000000000 : ℝ)*x 1 + (176539393/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320844161/5000000000 : ℝ)^89 ≤ (8369555644483/10000000000000 : ℝ)^73 := by
    have hnat : (4320844161 : ℕ)^89*10000000000000^73 ≤ 8369555644483^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320844161 5000000000 8369555644483 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143351551/10000000000 : ℝ)^89 ≤ (3554049245213/50000000000000 : ℝ)^73 := by
    have hnat : (1143351551 : ℕ)^89*50000000000000^73 ≤ 3554049245213^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143351551 10000000000 3554049245213 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176539393/1250000000 : ℝ)^89 ≤ (1839269010351/20000000000000 : ℝ)^73 := by
    have hnat : (176539393 : ℕ)^89*20000000000000^73 ≤ 1839269010351^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176539393 1250000000 1839269010351 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320844161/5000000000 : ℝ), (-1143351551/10000000000 : ℝ), (176539393/1250000000 : ℝ)] ![(8369555644483/10000000000000 : ℝ), (3554049245213/50000000000000 : ℝ), (1839269010351/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320844161/5000000000 : ℝ)|^89 ≤ (8369555644483/10000000000000 : ℝ)^73
        have hw : |(4320844161/5000000000 : ℝ)|=(4320844161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1143351551/10000000000 : ℝ)|^89 ≤ (3554049245213/50000000000000 : ℝ)^73
        have hw : |(-1143351551/10000000000 : ℝ)|=(1143351551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(176539393/1250000000 : ℝ)|^89 ≤ (1839269010351/20000000000000 : ℝ)^73
        have hw : |(176539393/1250000000 : ℝ)|=(176539393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-417105683/10000000000 : ℝ)*x 0 + (-1416904483/2000000000 : ℝ)*x 1 + (987667133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417105683/10000000000 : ℝ)^89 ≤ (1039451665083/50000000000000 : ℝ)^73 := by
    have hnat : (417105683 : ℕ)^89*50000000000000^73 ≤ 1039451665083^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417105683 10000000000 1039451665083 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1416904483/2000000000 : ℝ)^89 ≤ (3284520242511/5000000000000 : ℝ)^73 := by
    have hnat : (1416904483 : ℕ)^89*5000000000000^73 ≤ 3284520242511^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416904483 2000000000 3284520242511 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987667133/2500000000 : ℝ)^89 ≤ (32230691795693/100000000000000 : ℝ)^73 := by
    have hnat : (987667133 : ℕ)^89*100000000000000^73 ≤ 32230691795693^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987667133 2500000000 32230691795693 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417105683/10000000000 : ℝ), (-1416904483/2000000000 : ℝ), (987667133/2500000000 : ℝ)] ![(1039451665083/50000000000000 : ℝ), (3284520242511/5000000000000 : ℝ), (32230691795693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417105683/10000000000 : ℝ)|^89 ≤ (1039451665083/50000000000000 : ℝ)^73
        have hw : |(-417105683/10000000000 : ℝ)|=(417105683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1416904483/2000000000 : ℝ)|^89 ≤ (3284520242511/5000000000000 : ℝ)^73
        have hw : |(-1416904483/2000000000 : ℝ)|=(1416904483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(987667133/2500000000 : ℝ)|^89 ≤ (32230691795693/100000000000000 : ℝ)^73
        have hw : |(987667133/2500000000 : ℝ)|=(987667133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5285446051/10000000000 : ℝ)*x 0 + (290380369/1000000000 : ℝ)*x 1 + (3916883233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285446051/10000000000 : ℝ)^89 ≤ (45960760918339/100000000000000 : ℝ)^73 := by
    have hnat : (5285446051 : ℕ)^89*100000000000000^73 ≤ 45960760918339^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285446051 10000000000 45960760918339 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (290380369/1000000000 : ℝ)^89 ≤ (5536068483053/25000000000000 : ℝ)^73 := by
    have hnat : (290380369 : ℕ)^89*25000000000000^73 ≤ 5536068483053^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290380369 1000000000 5536068483053 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3916883233/10000000000 : ℝ)^89 ≤ (15947482566631/50000000000000 : ℝ)^73 := by
    have hnat : (3916883233 : ℕ)^89*50000000000000^73 ≤ 15947482566631^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3916883233 10000000000 15947482566631 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285446051/10000000000 : ℝ), (290380369/1000000000 : ℝ), (3916883233/10000000000 : ℝ)] ![(45960760918339/100000000000000 : ℝ), (5536068483053/25000000000000 : ℝ), (15947482566631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285446051/10000000000 : ℝ)|^89 ≤ (45960760918339/100000000000000 : ℝ)^73
        have hw : |(5285446051/10000000000 : ℝ)|=(5285446051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(290380369/1000000000 : ℝ)|^89 ≤ (5536068483053/25000000000000 : ℝ)^73
        have hw : |(290380369/1000000000 : ℝ)|=(290380369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3916883233/10000000000 : ℝ)|^89 ≤ (15947482566631/50000000000000 : ℝ)^73
        have hw : |(3916883233/10000000000 : ℝ)|=(3916883233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4715469493/10000000000 : ℝ)*x 0 + (-3040518929/10000000000 : ℝ)*x 1 + (-4383545199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4715469493/10000000000 : ℝ)^89 ≤ (9997899584559/25000000000000 : ℝ)^73 := by
    have hnat : (4715469493 : ℕ)^89*25000000000000^73 ≤ 9997899584559^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4715469493 10000000000 9997899584559 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3040518929/10000000000 : ℝ)^89 ≤ (23421849309553/100000000000000 : ℝ)^73 := by
    have hnat : (3040518929 : ℕ)^89*100000000000000^73 ≤ 23421849309553^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3040518929 10000000000 23421849309553 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4383545199/10000000000 : ℝ)^89 ≤ (9146638084547/25000000000000 : ℝ)^73 := by
    have hnat : (4383545199 : ℕ)^89*25000000000000^73 ≤ 9146638084547^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4383545199 10000000000 9146638084547 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4715469493/10000000000 : ℝ), (-3040518929/10000000000 : ℝ), (-4383545199/10000000000 : ℝ)] ![(9997899584559/25000000000000 : ℝ), (23421849309553/100000000000000 : ℝ), (9146638084547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4715469493/10000000000 : ℝ)|^89 ≤ (9997899584559/25000000000000 : ℝ)^73
        have hw : |(4715469493/10000000000 : ℝ)|=(4715469493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3040518929/10000000000 : ℝ)|^89 ≤ (23421849309553/100000000000000 : ℝ)^73
        have hw : |(-3040518929/10000000000 : ℝ)|=(3040518929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4383545199/10000000000 : ℝ)|^89 ≤ (9146638084547/25000000000000 : ℝ)^73
        have hw : |(-4383545199/10000000000 : ℝ)|=(4383545199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s0_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8693556213/10000000000 : ℝ)*x 0 + (-66744121/1250000000 : ℝ)*x 1 + (465515503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8693556213/10000000000 : ℝ)^89 ≤ (42154203554509/50000000000000 : ℝ)^73 := by
    have hnat : (8693556213 : ℕ)^89*50000000000000^73 ≤ 42154203554509^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8693556213 10000000000 42154203554509 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66744121/1250000000 : ℝ)^89 ≤ (561861856153/20000000000000 : ℝ)^73 := by
    have hnat : (66744121 : ℕ)^89*20000000000000^73 ≤ 561861856153^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66744121 1250000000 561861856153 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (465515503/2500000000 : ℝ)^89 ≤ (3220570899867/25000000000000 : ℝ)^73 := by
    have hnat : (465515503 : ℕ)^89*25000000000000^73 ≤ 3220570899867^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465515503 2500000000 3220570899867 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8693556213/10000000000 : ℝ), (-66744121/1250000000 : ℝ), (465515503/2500000000 : ℝ)] ![(42154203554509/50000000000000 : ℝ), (561861856153/20000000000000 : ℝ), (3220570899867/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8693556213/10000000000 : ℝ)|^89 ≤ (42154203554509/50000000000000 : ℝ)^73
        have hw : |(8693556213/10000000000 : ℝ)|=(8693556213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66744121/1250000000 : ℝ)|^89 ≤ (561861856153/20000000000000 : ℝ)^73
        have hw : |(-66744121/1250000000 : ℝ)|=(66744121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(465515503/2500000000 : ℝ)|^89 ≤ (3220570899867/25000000000000 : ℝ)^73
        have hw : |(465515503/2500000000 : ℝ)|=(465515503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s1_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-998177047/5000000000 : ℝ)*x 0 + (-5639920277/10000000000 : ℝ)*x 1 + (1087126187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998177047/5000000000 : ℝ)^89 ≤ (3505944179009/25000000000000 : ℝ)^73 := by
    have hnat : (998177047 : ℕ)^89*25000000000000^73 ≤ 3505944179009^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998177047 5000000000 3505944179009 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5639920277/10000000000 : ℝ)^89 ≤ (49745918104163/100000000000000 : ℝ)^73 := by
    have hnat : (5639920277 : ℕ)^89*100000000000000^73 ≤ 49745918104163^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5639920277 10000000000 49745918104163 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087126187/2500000000 : ℝ)^89 ≤ (36230305169623/100000000000000 : ℝ)^73 := by
    have hnat : (1087126187 : ℕ)^89*100000000000000^73 ≤ 36230305169623^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087126187 2500000000 36230305169623 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-998177047/5000000000 : ℝ), (-5639920277/10000000000 : ℝ), (1087126187/2500000000 : ℝ)] ![(3505944179009/25000000000000 : ℝ), (49745918104163/100000000000000 : ℝ), (36230305169623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-998177047/5000000000 : ℝ)|^89 ≤ (3505944179009/25000000000000 : ℝ)^73
        have hw : |(-998177047/5000000000 : ℝ)|=(998177047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5639920277/10000000000 : ℝ)|^89 ≤ (49745918104163/100000000000000 : ℝ)^73
        have hw : |(-5639920277/10000000000 : ℝ)|=(5639920277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087126187/2500000000 : ℝ)|^89 ≤ (36230305169623/100000000000000 : ℝ)^73
        have hw : |(1087126187/2500000000 : ℝ)|=(1087126187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s1_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (188014249/400000000 : ℝ)*x 0 + (1672622113/5000000000 : ℝ)*x 1 + (205638801/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (188014249/400000000 : ℝ)^89 ≤ (39835385523491/100000000000000 : ℝ)^73 := by
    have hnat : (188014249 : ℕ)^89*100000000000000^73 ≤ 39835385523491^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188014249 400000000 39835385523491 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1672622113/5000000000 : ℝ)^89 ≤ (13157180656959/50000000000000 : ℝ)^73 := by
    have hnat : (1672622113 : ℕ)^89*50000000000000^73 ≤ 13157180656959^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1672622113 5000000000 13157180656959 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205638801/500000000 : ℝ)^89 ≤ (33850253143833/100000000000000 : ℝ)^73 := by
    have hnat : (205638801 : ℕ)^89*100000000000000^73 ≤ 33850253143833^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205638801 500000000 33850253143833 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(188014249/400000000 : ℝ), (1672622113/5000000000 : ℝ), (205638801/500000000 : ℝ)] ![(39835385523491/100000000000000 : ℝ), (13157180656959/50000000000000 : ℝ), (33850253143833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(188014249/400000000 : ℝ)|^89 ≤ (39835385523491/100000000000000 : ℝ)^73
        have hw : |(188014249/400000000 : ℝ)|=(188014249/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1672622113/5000000000 : ℝ)|^89 ≤ (13157180656959/50000000000000 : ℝ)^73
        have hw : |(1672622113/5000000000 : ℝ)|=(1672622113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205638801/500000000 : ℝ)|^89 ≤ (33850253143833/100000000000000 : ℝ)^73
        have hw : |(205638801/500000000 : ℝ)|=(205638801/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s1_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1174030149/2500000000 : ℝ)*x 0 + (-3347239817/10000000000 : ℝ)*x 1 + (-4115229479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1174030149/2500000000 : ℝ)^89 ≤ (7958325042277/20000000000000 : ℝ)^73 := by
    have hnat : (1174030149 : ℕ)^89*20000000000000^73 ≤ 7958325042277^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174030149 2500000000 7958325042277 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3347239817/10000000000 : ℝ)^89 ≤ (26333500879383/100000000000000 : ℝ)^73 := by
    have hnat : (3347239817 : ℕ)^89*100000000000000^73 ≤ 26333500879383^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3347239817 10000000000 26333500879383 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4115229479/10000000000 : ℝ)^89 ≤ (33874873889401/100000000000000 : ℝ)^73 := by
    have hnat : (4115229479 : ℕ)^89*100000000000000^73 ≤ 33874873889401^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4115229479 10000000000 33874873889401 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1174030149/2500000000 : ℝ), (-3347239817/10000000000 : ℝ), (-4115229479/10000000000 : ℝ)] ![(7958325042277/20000000000000 : ℝ), (26333500879383/100000000000000 : ℝ), (33874873889401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1174030149/2500000000 : ℝ)|^89 ≤ (7958325042277/20000000000000 : ℝ)^73
        have hw : |(1174030149/2500000000 : ℝ)|=(1174030149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3347239817/10000000000 : ℝ)|^89 ≤ (26333500879383/100000000000000 : ℝ)^73
        have hw : |(-3347239817/10000000000 : ℝ)|=(3347239817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4115229479/10000000000 : ℝ)|^89 ≤ (33874873889401/100000000000000 : ℝ)^73
        have hw : |(-4115229479/10000000000 : ℝ)|=(4115229479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326037_s1_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (192976189/312500000 : ℝ)*x 0 + (-3282354533/10000000000 : ℝ)*x 1 + (3163461/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (192976189/312500000 : ℝ)^89 ≤ (55560939921657/100000000000000 : ℝ)^73 := by
    have hnat : (192976189 : ℕ)^89*100000000000000^73 ≤ 55560939921657^73*312500000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192976189 312500000 55560939921657 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3282354533/10000000000 : ℝ)^89 ≤ (25712479078999/100000000000000 : ℝ)^73 := by
    have hnat : (3282354533 : ℕ)^89*100000000000000^73 ≤ 25712479078999^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3282354533 10000000000 25712479078999 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3163461/12500000 : ℝ)^89 ≤ (936329048909/5000000000000 : ℝ)^73 := by
    have hnat : (3163461 : ℕ)^89*5000000000000^73 ≤ 936329048909^73*12500000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3163461 12500000 936329048909 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(192976189/312500000 : ℝ), (-3282354533/10000000000 : ℝ), (3163461/12500000 : ℝ)] ![(55560939921657/100000000000000 : ℝ), (25712479078999/100000000000000 : ℝ), (936329048909/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(192976189/312500000 : ℝ)|^89 ≤ (55560939921657/100000000000000 : ℝ)^73
        have hw : |(192976189/312500000 : ℝ)|=(192976189/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3282354533/10000000000 : ℝ)|^89 ≤ (25712479078999/100000000000000 : ℝ)^73
        have hw : |(-3282354533/10000000000 : ℝ)|=(3282354533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3163461/12500000 : ℝ)|^89 ≤ (936329048909/5000000000000 : ℝ)^73
        have hw : |(3163461/12500000 : ℝ)|=(3163461/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326037 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-97165121/1250000000 : ℝ)*X 0 0+(-3379396781/5000000000 : ℝ)*X 0 1+(102026951/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4916663741/10000000000 : ℝ)*X 2 0+(-2970330197/10000000000 : ℝ)*X 2 1+(-4242273387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((8041645491/10000000000 : ℝ)*X 0 0+(-1285448787/10000000000 : ℝ)*X 0 1+(2125253119/10000000000 : ℝ)*X 0 2+(8041645491/10000000000 : ℝ)*X 1 0+(-1285448787/10000000000 : ℝ)*X 1 1+(2125253119/10000000000 : ℝ)*X 1 2+(8041645491/10000000000 : ℝ)*X 2 0+(-1285448787/10000000000 : ℝ)*X 2 1+(2125253119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-375856629/5000000000 : ℝ)*X 0 0+(-7358517013/10000000000 : ℝ)*X 0 1+(3409953453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4842518449/10000000000 : ℝ)*X 1 0+(1471053169/5000000000 : ℝ)*X 1 1+(2172267761/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2421259121/5000000000 : ℝ)*X 2 0+(-2728044747/10000000000 : ℝ)*X 2 1+(-1134633093/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3978979029/5000000000 : ℝ)*X 0 0+(-534503887/10000000000 : ℝ)*X 0 1+(2833620269/10000000000 : ℝ)*X 0 2+(3978979029/5000000000 : ℝ)*X 1 0+(-534503887/10000000000 : ℝ)*X 1 1+(2833620269/10000000000 : ℝ)*X 1 2+(3978979029/5000000000 : ℝ)*X 2 0+(-534503887/10000000000 : ℝ)*X 2 1+(2833620269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-13642433/400000000 : ℝ)*X 0 0+(-6658409593/10000000000 : ℝ)*X 0 1+(4469970607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2366032799/5000000000 : ℝ)*X 1 0+(773399723/2500000000 : ℝ)*X 1 1+(4317482041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1072298323/2000000000 : ℝ)*X 2 0+(-1384903187/5000000000 : ℝ)*X 2 1+(-3960342651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((4320844161/5000000000 : ℝ)*X 0 0+(-1143351551/10000000000 : ℝ)*X 0 1+(176539393/1250000000 : ℝ)*X 0 2+(4320844161/5000000000 : ℝ)*X 1 0+(-1143351551/10000000000 : ℝ)*X 1 1+(176539393/1250000000 : ℝ)*X 1 2+(4320844161/5000000000 : ℝ)*X 2 0+(-1143351551/10000000000 : ℝ)*X 2 1+(176539393/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-417105683/10000000000 : ℝ)*X 0 0+(-1416904483/2000000000 : ℝ)*X 0 1+(987667133/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((5285446051/10000000000 : ℝ)*X 1 0+(290380369/1000000000 : ℝ)*X 1 1+(3916883233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((4715469493/10000000000 : ℝ)*X 2 0+(-3040518929/10000000000 : ℝ)*X 2 1+(-4383545199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((8693556213/10000000000 : ℝ)*X 0 0+(-66744121/1250000000 : ℝ)*X 0 1+(465515503/2500000000 : ℝ)*X 0 2+(8693556213/10000000000 : ℝ)*X 1 0+(-66744121/1250000000 : ℝ)*X 1 1+(465515503/2500000000 : ℝ)*X 1 2+(8693556213/10000000000 : ℝ)*X 2 0+(-66744121/1250000000 : ℝ)*X 2 1+(465515503/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((3097/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3097/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7616758874958700805103/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8067/100000000000 : ℝ)*(base3) + (2206108982971/1000000000000 : ℝ)*(base40) + (1947349202707/1000000000000 : ℝ)*(base49) + (399430844169/1000000000000 : ℝ)*(base59) + (1886925658817/250000000000 : ℝ)*(major_s0_0) + (1886925658817/250000000000 : ℝ)*(major_s0_1) + (1886925658817/250000000000 : ℝ)*(major_s0_2) + (38625999/500000000000 : ℝ)*(sp_s0_0) + (1143609992613/100000000000 : ℝ)*(sp_s0_7) + (1143599220083/100000000000 : ℝ)*(sp_s0_8) + (1143603800129/100000000000 : ℝ)*(sp_s0_9) + (731845196119/200000000000 : ℝ)*(sp_s0_13) + (11566123/62500000000 : ℝ)*(sp_s0_15) + (69588419/500000000000 : ℝ)*(sp_s0_23) + (731845212253/200000000000 : ℝ)*(f.failure) + (714761073633/62500000000 : ℝ)*(f.sum) + (10834207358531/25000000000000000000000000 : ℝ)*base62 + (2396214337971749/2500000000000000000000000000 : ℝ)*base65 + (2556633211028251/2500000000000000000000000000 : ℝ)*base66 + (31664720313531/50000000000000000000000000 : ℝ)*base68 + (1981444192795199/2500000000000000000000000000 : ℝ)*base71 + (1864503505971749/2500000000000000000000000000 : ℝ)*base72 + (43509909213531/50000000000000000000000000 : ℝ)*base74 + (36954004391469/50000000000000000000000000 : ℝ)*base77 + (8523019413/10000000000000000000000 : ℝ)*base78 + (1009/4000000000000000 : ℝ)*base87 + (1009/4000000000000000 : ℝ)*base89 + (1009/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-6197/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-6197/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4961274577780227109737/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3830303009669/1000000000000 : ℝ)*(base40) + (1743747369427/1000000000000 : ℝ)*(base49) + (2034341/1000000000000 : ℝ)*(base59) + (2621381167657/250000000000 : ℝ)*(major_s0_0) + (2621381167657/250000000000 : ℝ)*(major_s0_1) + (2621381167657/250000000000 : ℝ)*(major_s0_2) + (2172093/1000000000000 : ℝ)*(sp_s0_0) + (17406607/1000000000000 : ℝ)*(sp_s0_6) + (20666433/100000000000 : ℝ)*(sp_s0_8) + (15887524807371/1000000000000 : ℝ)*(sp_s0_14) + (3177464063027/200000000000 : ℝ)*(sp_s0_15) + (3177505395893/200000000000 : ℝ)*(sp_s0_16) + (5083501926787/1000000000000 : ℝ)*(sp_s0_20) + (1705381/1000000000000 : ℝ)*(sp_s0_27) + (2541760519387/500000000000 : ℝ)*(f.failure) + (3177505395893/200000000000 : ℝ)*(f.sum) + (14077460024151/25000000000000000000000000 : ℝ)*base62 + (2158110482090771/2500000000000000000000000000 : ℝ)*base64 + (482685399659229/2500000000000000000000000000 : ℝ)*base67 + (30596733781651/50000000000000000000000000 : ℝ)*base68 + (1927636352423321/2500000000000000000000000000 : ℝ)*base70 + (443510855840771/2500000000000000000000000000 : ℝ)*base73 + (31832914156651/50000000000000000000000000 : ℝ)*base74 + (14311555941651/50000000000000000000000000 : ℝ)*base76 + (1493627791/5000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (8089/10000000000000000 : ℝ)*base86 + (8089/10000000000000000 : ℝ)*base88 + (8089/10000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30949/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(30949/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (77937632988683311303203/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1092673309119/250000000000 : ℝ)*(base40) + (2274767077251/1000000000000 : ℝ)*(base49) + (2635405679/20000000000 : ℝ)*(base59) + (11579198544717/1000000000000 : ℝ)*(major_s0_0) + (11579198544717/1000000000000 : ℝ)*(major_s0_1) + (11579198544717/1000000000000 : ℝ)*(major_s0_2) + (11759997/500000000000 : ℝ)*(sp_s0_0) + (175935537/1000000000000 : ℝ)*(sp_s0_2) + (9809547/125000000000 : ℝ)*(sp_s0_7) + (43482067/500000000000 : ℝ)*(sp_s0_20) + (4386135324919/250000000000 : ℝ)*(sp_s0_21) + (8772321648023/500000000000 : ℝ)*(sp_s0_22) + (17544467360509/1000000000000 : ℝ)*(sp_s0_23) + (5613661633407/1000000000000 : ℝ)*(sp_s0_27) + (5613748597541/1000000000000 : ℝ)*(f.failure) + (8772321648023/500000000000 : ℝ)*(f.sum) + (37798513377231/100000000000000000000000000 : ℝ)*base62 + (4974410855704049/10000000000000000000000000000 : ℝ)*base65 + (4873097910295951/10000000000000000000000000000 : ℝ)*base66 + (99110167767231/200000000000000000000000000 : ℝ)*base68 + (4415856856342499/10000000000000000000000000000 : ℝ)*base71 + (3204712887704049/10000000000000000000000000000 : ℝ)*base72 + (98892197927231/200000000000000000000000000 : ℝ)*base74 + (56338325132769/200000000000000000000000000 : ℝ)*base77 + (460608007/1000000000000000000000 : ℝ)*base78 + (18873/20000000000000000 : ℝ)*base87 + (18873/20000000000000000 : ℝ)*base89 + (18873/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (3097/25000 : ℝ) ^ (87/16 : ℝ) ≤ (292505485911947/25000000000000000000 : ℝ) := by
    have hpowers : (3097/25000 : ℝ)^87 ≤ (292505485911947/25000000000000000000 : ℝ)^16 := by
      have hnat : (3097 : ℕ)^87*25000000000000000000^16 ≤ 292505485911947^16*25000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 25000 292505485911947 25000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/25000 : ℝ)) (X := (292505485911947/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25000292505485911947/25000000000000000000 : ℝ) ≤ (2500005379385553/2500000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (25000292505485911947/25000000000000000000 : ℝ)^16 ≤ (2500005379385553/2500000000000000 : ℝ)^87 := by
      have hnat : (25000292505485911947 : ℕ)^16*2500000000000000^87 ≤ 2500005379385553^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000292505485911947 25000000000000000000 2500005379385553 2500000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500005379385553/2500000000000000 : ℝ)) (X := (25000292505485911947/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12500292505485911947/12500000000000000000 : ℝ) ≤ (10000043034878967/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (12500292505485911947/12500000000000000000 : ℝ)^16 ≤ (10000043034878967/10000000000000000 : ℝ)^87 := by
      have hnat : (12500292505485911947 : ℕ)^16*10000000000000000^87 ≤ 10000043034878967^87*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500292505485911947 12500000000000000000 10000043034878967 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000043034878967/10000000000000000 : ℝ)) (X := (12500292505485911947/12500000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(5379385553/309700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4303467351/247760000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (3097/25000 : ℝ)) (alpha := (5379385553/309700000000000 : ℝ)) (beta := (4303467351/247760000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3097/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(5379385553/309700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4303467351/247760000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6197/25000 : ℝ) ^ (87/16 : ℝ) ≤ (25418978424262671/50000000000000000000 : ℝ) := by
    have hpowers : (6197/25000 : ℝ)^87 ≤ (25418978424262671/50000000000000000000 : ℝ)^16 := by
      have hnat : (6197 : ℕ)^87*50000000000000000000^16 ≤ 25418978424262671^16*25000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6197 25000 25418978424262671 50000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6197/25000 : ℝ)) (X := (25418978424262671/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50025418978424262671/50000000000000000000 : ℝ) ≤ (5000467378520951/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50025418978424262671/50000000000000000000 : ℝ)^16 ≤ (5000467378520951/5000000000000000 : ℝ)^87 := by
      have hnat : (50025418978424262671 : ℕ)^16*5000000000000000^87 ≤ 5000467378520951^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025418978424262671 50000000000000000000 5000467378520951 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000467378520951/5000000000000000 : ℝ)) (X := (50025418978424262671/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25025418978424262671/25000000000000000000 : ℝ) ≤ (10001869126545009/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (25025418978424262671/25000000000000000000 : ℝ)^16 ≤ (10001869126545009/10000000000000000 : ℝ)^87 := by
      have hnat : (25025418978424262671 : ℕ)^16*10000000000000000^87 ≤ 10001869126545009^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25025418978424262671 25000000000000000000 10001869126545009 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001869126545009/10000000000000000 : ℝ)) (X := (25025418978424262671/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(467378520951/1239400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(934369503107/2478800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (6197/25000 : ℝ)) (alpha := (467378520951/1239400000000000 : ℝ)) (beta := (934369503107/2478800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (6197/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(467378520951/1239400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(934369503107/2478800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (30949/100000 : ℝ) ^ (87/16 : ℝ) ≤ (169977329453741429/100000000000000000000 : ℝ) := by
    have hpowers : (30949/100000 : ℝ)^87 ≤ (169977329453741429/100000000000000000000 : ℝ)^16 := by
      have hnat : (30949 : ℕ)^87*100000000000000000000^16 ≤ 169977329453741429^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30949 100000 169977329453741429 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30949/100000 : ℝ)) (X := (169977329453741429/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100169977329453741429/100000000000000000000 : ℝ) ≤ (10003123853917831/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (100169977329453741429/100000000000000000000 : ℝ)^16 ≤ (10003123853917831/10000000000000000 : ℝ)^87 := by
      have hnat : (100169977329453741429 : ℕ)^16*10000000000000000^87 ≤ 10003123853917831^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100169977329453741429 100000000000000000000 10003123853917831 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003123853917831/10000000000000000 : ℝ)) (X := (100169977329453741429/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50169977329453741429/50000000000000000000 : ℝ) ≤ (10006243384859331/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50169977329453741429/50000000000000000000 : ℝ)^16 ≤ (10006243384859331/10000000000000000 : ℝ)^87 := by
      have hnat : (50169977329453741429 : ℕ)^16*10000000000000000^87 ≤ 10006243384859331^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50169977329453741429 50000000000000000000 10006243384859331 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006243384859331/10000000000000000 : ℝ)) (X := (50169977329453741429/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(3123853917831/3094900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(6239061883/6189800000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (30949/100000 : ℝ)) (alpha := (3123853917831/3094900000000000 : ℝ)) (beta := (6239061883/6189800000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (30949/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(3123853917831/3094900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(6239061883/6189800000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-998177047/5000000000 : ℝ)*X 0 0+(-5639920277/10000000000 : ℝ)*X 0 1+(1087126187/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((188014249/400000000 : ℝ)*X 1 0+(1672622113/5000000000 : ℝ)*X 1 1+(205638801/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1174030149/2500000000 : ℝ)*X 2 0+(-3347239817/10000000000 : ℝ)*X 2 1+(-4115229479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((192976189/312500000 : ℝ)*X 0 0+(-3282354533/10000000000 : ℝ)*X 0 1+(3163461/12500000 : ℝ)*X 0 2+(192976189/312500000 : ℝ)*X 1 0+(-3282354533/10000000000 : ℝ)*X 1 1+(3163461/12500000 : ℝ)*X 1 2+(192976189/312500000 : ℝ)*X 2 0+(-3282354533/10000000000 : ℝ)*X 2 1+(3163461/12500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326037_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-93759/10000 : ℝ) < ((-41253/20000 : ℝ)*P 0+(-41253/20000 : ℝ)*P 1+(-41253/20000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-93759/10000 : ℝ) < (-21945768496659413022875992199763033/2375906325764000000000000000000000 : ℝ) := by norm_num
    linear_combination (161/200000000000 : ℝ)*(base10) + (1653/1000000000000 : ℝ)*(base17) + (79/1000000000000 : ℝ)*(base19) + (40118307649/250000000000 : ℝ)*(base39) + (703786037787/1000000000000 : ℝ)*(base40) + (217/200000000000 : ℝ)*(base44) + (117480045311/250000000000 : ℝ)*(base49) + (41253/20000 : ℝ)*(major_s1_0) + (1031324999667/500000000000 : ℝ)*(major_s1_1) + (41253/20000 : ℝ)*(major_s1_2) + (3078932903337/1000000000000 : ℝ)*(sp_s1_0) + (615786580181/200000000000 : ℝ)*(sp_s1_1) + (1539466452071/500000000000 : ℝ)*(sp_s1_2) + (199999999783/200000000000 : ℝ)*(sp_s1_6) + (3078932903723/1000000000000 : ℝ)*(f.sum) + (92639433812851573/19179095300000000000000000000000 : ℝ)*base63 + (19969468741439/77372500000000000000000000 : ℝ)*base65 + (104838279875191/1239400000000000000000000000 : ℝ)*base67 + (9079427756759/61898000000000000000000000 : ℝ)*base69 + (21886780210032949/191698106000000000000000000000 : ℝ)*base71 + (281661618903/309700000000000000000000 : ℝ)*base73 + (69638380095877/619700000000000000000000000 : ℝ)*base75 + (1667974363227/30970000000000000000000000 : ℝ)*base76 + (2988532051307911447/3838421800000000000000000000000 : ℝ)*base79 + (419/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base82 + (419/1000000000000 : ℝ)*base85 + (419/1000000000000 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p026_b016 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=37 := by omega
  rcases hc with rfl
  · exact collision_c326037 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p026_b016 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
