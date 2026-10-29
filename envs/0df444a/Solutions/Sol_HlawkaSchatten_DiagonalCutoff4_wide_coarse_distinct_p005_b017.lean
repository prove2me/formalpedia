-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p005_b017
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:35:24.478776+00:00
-- url     : https://prove2.me/submissions/9f0c0204-9f26-4452-b088-49d9543e9cb4

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
theorem collision_support_c305032_s0_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2814071661/10000000000 : ℝ)*x 0 + (5355912561/10000000000 : ℝ)*x 1 + (-2314278949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2814071661/10000000000 : ℝ)^137 ≤ (29876760859/156250000000 : ℝ)^105 := by
    have hnat : (2814071661 : ℕ)^137*156250000000^105 ≤ 29876760859^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814071661 10000000000 29876760859 156250000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5355912561/10000000000 : ℝ)^137 ≤ (8855686796297/20000000000000 : ℝ)^105 := by
    have hnat : (5355912561 : ℕ)^137*20000000000000^105 ≤ 8855686796297^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355912561 10000000000 8855686796297 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2314278949/5000000000 : ℝ)^137 ≤ (36600439049189/100000000000000 : ℝ)^105 := by
    have hnat : (2314278949 : ℕ)^137*100000000000000^105 ≤ 36600439049189^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314278949 5000000000 36600439049189 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2814071661/10000000000 : ℝ), (5355912561/10000000000 : ℝ), (-2314278949/5000000000 : ℝ)] ![(29876760859/156250000000 : ℝ), (8855686796297/20000000000000 : ℝ), (36600439049189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2814071661/10000000000 : ℝ)|^137 ≤ (29876760859/156250000000 : ℝ)^105
        have hw : |(2814071661/10000000000 : ℝ)|=(2814071661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5355912561/10000000000 : ℝ)|^137 ≤ (8855686796297/20000000000000 : ℝ)^105
        have hw : |(5355912561/10000000000 : ℝ)|=(5355912561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2314278949/5000000000 : ℝ)|^137 ≤ (36600439049189/100000000000000 : ℝ)^105
        have hw : |(-2314278949/5000000000 : ℝ)|=(2314278949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7442403417/10000000000 : ℝ)*x 0 + (-1315228693/5000000000 : ℝ)*x 1 + (2273230597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7442403417/10000000000 : ℝ)^137 ≤ (68016813205967/100000000000000 : ℝ)^105 := by
    have hnat : (7442403417 : ℕ)^137*100000000000000^105 ≤ 68016813205967^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7442403417 10000000000 68016813205967 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315228693/5000000000 : ℝ)^137 ≤ (8754853842281/50000000000000 : ℝ)^105 := by
    have hnat : (1315228693 : ℕ)^137*50000000000000^105 ≤ 8754853842281^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315228693 5000000000 8754853842281 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273230597/10000000000 : ℝ)^137 ≤ (3618369775063/25000000000000 : ℝ)^105 := by
    have hnat : (2273230597 : ℕ)^137*25000000000000^105 ≤ 3618369775063^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273230597 10000000000 3618369775063 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7442403417/10000000000 : ℝ), (-1315228693/5000000000 : ℝ), (2273230597/10000000000 : ℝ)] ![(68016813205967/100000000000000 : ℝ), (8754853842281/50000000000000 : ℝ), (3618369775063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7442403417/10000000000 : ℝ)|^137 ≤ (68016813205967/100000000000000 : ℝ)^105
        have hw : |(7442403417/10000000000 : ℝ)|=(7442403417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1315228693/5000000000 : ℝ)|^137 ≤ (8754853842281/50000000000000 : ℝ)^105
        have hw : |(-1315228693/5000000000 : ℝ)|=(1315228693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2273230597/10000000000 : ℝ)|^137 ≤ (3618369775063/25000000000000 : ℝ)^105
        have hw : |(2273230597/10000000000 : ℝ)|=(2273230597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2386421393/10000000000 : ℝ)*x 0 + (-295451157/625000000 : ℝ)*x 1 + (-5602566601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2386421393/10000000000 : ℝ)^137 ≤ (7710422372713/50000000000000 : ℝ)^105 := by
    have hnat : (2386421393 : ℕ)^137*50000000000000^105 ≤ 7710422372713^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386421393 10000000000 7710422372713 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295451157/625000000 : ℝ)^137 ≤ (470270674189/1250000000000 : ℝ)^105 := by
    have hnat : (295451157 : ℕ)^137*1250000000000^105 ≤ 470270674189^105*625000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295451157 625000000 470270674189 1250000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5602566601/10000000000 : ℝ)^137 ≤ (733710958027/1562500000000 : ℝ)^105 := by
    have hnat : (5602566601 : ℕ)^137*1562500000000^105 ≤ 733710958027^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5602566601 10000000000 733710958027 1562500000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2386421393/10000000000 : ℝ), (-295451157/625000000 : ℝ), (-5602566601/10000000000 : ℝ)] ![(7710422372713/50000000000000 : ℝ), (470270674189/1250000000000 : ℝ), (733710958027/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2386421393/10000000000 : ℝ)|^137 ≤ (7710422372713/50000000000000 : ℝ)^105
        have hw : |(-2386421393/10000000000 : ℝ)|=(2386421393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-295451157/625000000 : ℝ)|^137 ≤ (470270674189/1250000000000 : ℝ)^105
        have hw : |(-295451157/625000000 : ℝ)|=(295451157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5602566601/10000000000 : ℝ)|^137 ≤ (733710958027/1562500000000 : ℝ)^105
        have hw : |(-5602566601/10000000000 : ℝ)|=(5602566601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2846637549/10000000000 : ℝ)*x 0 + (1214237661/2000000000 : ℝ)*x 1 + (-3815203141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2846637549/10000000000 : ℝ)^137 ≤ (2426293979489/12500000000000 : ℝ)^105 := by
    have hnat : (2846637549 : ℕ)^137*12500000000000^105 ≤ 2426293979489^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2846637549 10000000000 2426293979489 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1214237661/2000000000 : ℝ)^137 ≤ (2085853370677/4000000000000 : ℝ)^105 := by
    have hnat : (1214237661 : ℕ)^137*4000000000000^105 ≤ 2085853370677^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214237661 2000000000 2085853370677 4000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3815203141/10000000000 : ℝ)^137 ≤ (5688662778193/20000000000000 : ℝ)^105 := by
    have hnat : (3815203141 : ℕ)^137*20000000000000^105 ≤ 5688662778193^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3815203141 10000000000 5688662778193 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2846637549/10000000000 : ℝ), (1214237661/2000000000 : ℝ), (-3815203141/10000000000 : ℝ)] ![(2426293979489/12500000000000 : ℝ), (2085853370677/4000000000000 : ℝ), (5688662778193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2846637549/10000000000 : ℝ)|^137 ≤ (2426293979489/12500000000000 : ℝ)^105
        have hw : |(2846637549/10000000000 : ℝ)|=(2846637549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1214237661/2000000000 : ℝ)|^137 ≤ (2085853370677/4000000000000 : ℝ)^105
        have hw : |(1214237661/2000000000 : ℝ)|=(1214237661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3815203141/10000000000 : ℝ)|^137 ≤ (5688662778193/20000000000000 : ℝ)^105
        have hw : |(-3815203141/10000000000 : ℝ)|=(3815203141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1474291803/2000000000 : ℝ)*x 0 + (-2282502869/10000000000 : ℝ)*x 1 + (2718399899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1474291803/2000000000 : ℝ)^137 ≤ (33586039799819/50000000000000 : ℝ)^105 := by
    have hnat : (1474291803 : ℕ)^137*50000000000000^105 ≤ 33586039799819^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1474291803 2000000000 33586039799819 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282502869/10000000000 : ℝ)^137 ≤ (2910110924363/20000000000000 : ℝ)^105 := by
    have hnat : (2282502869 : ℕ)^137*20000000000000^105 ≤ 2910110924363^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282502869 10000000000 2910110924363 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718399899/10000000000 : ℝ)^137 ≤ (18277365766903/100000000000000 : ℝ)^105 := by
    have hnat : (2718399899 : ℕ)^137*100000000000000^105 ≤ 18277365766903^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718399899 10000000000 18277365766903 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1474291803/2000000000 : ℝ), (-2282502869/10000000000 : ℝ), (2718399899/10000000000 : ℝ)] ![(33586039799819/50000000000000 : ℝ), (2910110924363/20000000000000 : ℝ), (18277365766903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1474291803/2000000000 : ℝ)|^137 ≤ (33586039799819/50000000000000 : ℝ)^105
        have hw : |(1474291803/2000000000 : ℝ)|=(1474291803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2282502869/10000000000 : ℝ)|^137 ≤ (2910110924363/20000000000000 : ℝ)^105
        have hw : |(-2282502869/10000000000 : ℝ)|=(2282502869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718399899/10000000000 : ℝ)|^137 ≤ (18277365766903/100000000000000 : ℝ)^105
        have hw : |(2718399899/10000000000 : ℝ)|=(2718399899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4506393629/10000000000 : ℝ)*x 0 + (-331504867/1250000000 : ℝ)*x 1 + (-5602566601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4506393629/10000000000 : ℝ)^137 ≤ (35345117419621/100000000000000 : ℝ)^105 := by
    have hnat : (4506393629 : ℕ)^137*100000000000000^105 ≤ 35345117419621^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506393629 10000000000 35345117419621 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (331504867/1250000000 : ℝ)^137 ≤ (4424345313887/25000000000000 : ℝ)^105 := by
    have hnat : (331504867 : ℕ)^137*25000000000000^105 ≤ 4424345313887^105*1250000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331504867 1250000000 4424345313887 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5602566601/10000000000 : ℝ)^137 ≤ (733710958027/1562500000000 : ℝ)^105 := by
    have hnat : (5602566601 : ℕ)^137*1562500000000^105 ≤ 733710958027^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5602566601 10000000000 733710958027 1562500000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4506393629/10000000000 : ℝ), (-331504867/1250000000 : ℝ), (-5602566601/10000000000 : ℝ)] ![(35345117419621/100000000000000 : ℝ), (4424345313887/25000000000000 : ℝ), (733710958027/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4506393629/10000000000 : ℝ)|^137 ≤ (35345117419621/100000000000000 : ℝ)^105
        have hw : |(4506393629/10000000000 : ℝ)|=(4506393629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-331504867/1250000000 : ℝ)|^137 ≤ (4424345313887/25000000000000 : ℝ)^105
        have hw : |(-331504867/1250000000 : ℝ)|=(331504867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5602566601/10000000000 : ℝ)|^137 ≤ (733710958027/1562500000000 : ℝ)^105
        have hw : |(-5602566601/10000000000 : ℝ)|=(5602566601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1946891263/10000000000 : ℝ)*x 0 + (-4491627481/10000000000 : ℝ)*x 1 + (-6145620657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1946891263/10000000000 : ℝ)^137 ≤ (5911941421171/50000000000000 : ℝ)^105 := by
    have hnat : (1946891263 : ℕ)^137*50000000000000^105 ≤ 5911941421171^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946891263 10000000000 5911941421171 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491627481/10000000000 : ℝ)^137 ≤ (7038816197099/20000000000000 : ℝ)^105 := by
    have hnat : (4491627481 : ℕ)^137*20000000000000^105 ≤ 7038816197099^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491627481 10000000000 7038816197099 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6145620657/10000000000 : ℝ)^137 ≤ (52982036160031/100000000000000 : ℝ)^105 := by
    have hnat : (6145620657 : ℕ)^137*100000000000000^105 ≤ 52982036160031^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6145620657 10000000000 52982036160031 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1946891263/10000000000 : ℝ), (-4491627481/10000000000 : ℝ), (-6145620657/10000000000 : ℝ)] ![(5911941421171/50000000000000 : ℝ), (7038816197099/20000000000000 : ℝ), (52982036160031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1946891263/10000000000 : ℝ)|^137 ≤ (5911941421171/50000000000000 : ℝ)^105
        have hw : |(-1946891263/10000000000 : ℝ)|=(1946891263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4491627481/10000000000 : ℝ)|^137 ≤ (7038816197099/20000000000000 : ℝ)^105
        have hw : |(-4491627481/10000000000 : ℝ)|=(4491627481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6145620657/10000000000 : ℝ)|^137 ≤ (52982036160031/100000000000000 : ℝ)^105
        have hw : |(-6145620657/10000000000 : ℝ)|=(6145620657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (62541359/312500000 : ℝ)*x 0 + (2841688123/5000000000 : ℝ)*x 1 + (-494509619/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62541359/312500000 : ℝ)^137 ≤ (6128517406267/50000000000000 : ℝ)^105 := by
    have hnat : (62541359 : ℕ)^137*50000000000000^105 ≤ 6128517406267^105*312500000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62541359 312500000 6128517406267 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2841688123/5000000000 : ℝ)^137 ≤ (47843152563951/100000000000000 : ℝ)^105 := by
    have hnat : (2841688123 : ℕ)^137*100000000000000^105 ≤ 47843152563951^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2841688123 5000000000 47843152563951 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494509619/1000000000 : ℝ)^137 ≤ (39899812618237/100000000000000 : ℝ)^105 := by
    have hnat : (494509619 : ℕ)^137*100000000000000^105 ≤ 39899812618237^105*1000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494509619 1000000000 39899812618237 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(62541359/312500000 : ℝ), (2841688123/5000000000 : ℝ), (-494509619/1000000000 : ℝ)] ![(6128517406267/50000000000000 : ℝ), (47843152563951/100000000000000 : ℝ), (39899812618237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(62541359/312500000 : ℝ)|^137 ≤ (6128517406267/50000000000000 : ℝ)^105
        have hw : |(62541359/312500000 : ℝ)|=(62541359/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2841688123/5000000000 : ℝ)|^137 ≤ (47843152563951/100000000000000 : ℝ)^105
        have hw : |(2841688123/5000000000 : ℝ)|=(2841688123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-494509619/1000000000 : ℝ)|^137 ≤ (39899812618237/100000000000000 : ℝ)^105
        have hw : |(-494509619/1000000000 : ℝ)|=(494509619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2109586253/2500000000 : ℝ)*x 0 + (-1820911581/10000000000 : ℝ)*x 1 + (1584372129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109586253/2500000000 : ℝ)^137 ≤ (10015977002143/12500000000000 : ℝ)^105 := by
    have hnat : (2109586253 : ℕ)^137*12500000000000^105 ≤ 10015977002143^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109586253 2500000000 10015977002143 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1820911581/10000000000 : ℝ)^137 ≤ (135445036461/1250000000000 : ℝ)^105 := by
    have hnat : (1820911581 : ℕ)^137*1250000000000^105 ≤ 135445036461^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820911581 10000000000 135445036461 1250000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584372129/10000000000 : ℝ)^137 ≤ (2259145263733/25000000000000 : ℝ)^105 := by
    have hnat : (1584372129 : ℕ)^137*25000000000000^105 ≤ 2259145263733^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584372129 10000000000 2259145263733 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109586253/2500000000 : ℝ), (-1820911581/10000000000 : ℝ), (1584372129/10000000000 : ℝ)] ![(10015977002143/12500000000000 : ℝ), (135445036461/1250000000000 : ℝ), (2259145263733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109586253/2500000000 : ℝ)|^137 ≤ (10015977002143/12500000000000 : ℝ)^105
        have hw : |(2109586253/2500000000 : ℝ)|=(2109586253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1820911581/10000000000 : ℝ)|^137 ≤ (135445036461/1250000000000 : ℝ)^105
        have hw : |(-1820911581/10000000000 : ℝ)|=(1820911581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1584372129/10000000000 : ℝ)|^137 ≤ (2259145263733/25000000000000 : ℝ)^105
        have hw : |(1584372129/10000000000 : ℝ)|=(1584372129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_19 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5087123409/10000000000 : ℝ)*x 0 + (-102622069/312500000 : ℝ)*x 1 + (-898633821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5087123409/10000000000 : ℝ)^137 ≤ (41401512214863/100000000000000 : ℝ)^105 := by
    have hnat : (5087123409 : ℕ)^137*100000000000000^105 ≤ 41401512214863^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5087123409 10000000000 41401512214863 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102622069/312500000 : ℝ)^137 ≤ (11694322629391/50000000000000 : ℝ)^105 := by
    have hnat : (102622069 : ℕ)^137*50000000000000^105 ≤ 11694322629391^105*312500000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102622069 312500000 11694322629391 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898633821/2000000000 : ℝ)^137 ≤ (35209842514337/100000000000000 : ℝ)^105 := by
    have hnat : (898633821 : ℕ)^137*100000000000000^105 ≤ 35209842514337^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898633821 2000000000 35209842514337 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5087123409/10000000000 : ℝ), (-102622069/312500000 : ℝ), (-898633821/2000000000 : ℝ)] ![(41401512214863/100000000000000 : ℝ), (11694322629391/50000000000000 : ℝ), (35209842514337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5087123409/10000000000 : ℝ)|^137 ≤ (41401512214863/100000000000000 : ℝ)^105
        have hw : |(5087123409/10000000000 : ℝ)|=(5087123409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102622069/312500000 : ℝ)|^137 ≤ (11694322629391/50000000000000 : ℝ)^105
        have hw : |(-102622069/312500000 : ℝ)|=(102622069/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-898633821/2000000000 : ℝ)|^137 ≤ (35209842514337/100000000000000 : ℝ)^105
        have hw : |(-898633821/2000000000 : ℝ)|=(898633821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-167957511/625000000 : ℝ)*x 0 + (-1315673603/2500000000 : ℝ)*x 1 + (-2416280267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167957511/625000000 : ℝ)^137 ≤ (9002595028097/50000000000000 : ℝ)^105 := by
    have hnat : (167957511 : ℕ)^137*50000000000000^105 ≤ 9002595028097^105*625000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167957511 625000000 9002595028097 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315673603/2500000000 : ℝ)^137 ≤ (865511841149/2000000000000 : ℝ)^105 := by
    have hnat : (1315673603 : ℕ)^137*2000000000000^105 ≤ 865511841149^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315673603 2500000000 865511841149 2000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2416280267/5000000000 : ℝ)^137 ≤ (38719217880259/100000000000000 : ℝ)^105 := by
    have hnat : (2416280267 : ℕ)^137*100000000000000^105 ≤ 38719217880259^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416280267 5000000000 38719217880259 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-167957511/625000000 : ℝ), (-1315673603/2500000000 : ℝ), (-2416280267/5000000000 : ℝ)] ![(9002595028097/50000000000000 : ℝ), (865511841149/2000000000000 : ℝ), (38719217880259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-167957511/625000000 : ℝ)|^137 ≤ (9002595028097/50000000000000 : ℝ)^105
        have hw : |(-167957511/625000000 : ℝ)|=(167957511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1315673603/2500000000 : ℝ)|^137 ≤ (865511841149/2000000000000 : ℝ)^105
        have hw : |(-1315673603/2500000000 : ℝ)|=(1315673603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2416280267/5000000000 : ℝ)|^137 ≤ (38719217880259/100000000000000 : ℝ)^105
        have hw : |(-2416280267/5000000000 : ℝ)|=(2416280267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (951189053/5000000000 : ℝ)*x 0 + (228130867/400000000 : ℝ)*x 1 + (-4998771617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (951189053/5000000000 : ℝ)^137 ≤ (11472391816593/100000000000000 : ℝ)^105 := by
    have hnat : (951189053 : ℕ)^137*100000000000000^105 ≤ 11472391816593^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951189053 5000000000 11472391816593 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228130867/400000000 : ℝ)^137 ≤ (48061792440831/100000000000000 : ℝ)^105 := by
    have hnat : (228130867 : ℕ)^137*100000000000000^105 ≤ 48061792440831^105*400000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228130867 400000000 48061792440831 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4998771617/10000000000 : ℝ)^137 ≤ (40465815726049/100000000000000 : ℝ)^105 := by
    have hnat : (4998771617 : ℕ)^137*100000000000000^105 ≤ 40465815726049^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998771617 10000000000 40465815726049 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(951189053/5000000000 : ℝ), (228130867/400000000 : ℝ), (-4998771617/10000000000 : ℝ)] ![(11472391816593/100000000000000 : ℝ), (48061792440831/100000000000000 : ℝ), (40465815726049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(951189053/5000000000 : ℝ)|^137 ≤ (11472391816593/100000000000000 : ℝ)^105
        have hw : |(951189053/5000000000 : ℝ)|=(951189053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(228130867/400000000 : ℝ)|^137 ≤ (48061792440831/100000000000000 : ℝ)^105
        have hw : |(228130867/400000000 : ℝ)|=(228130867/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4998771617/10000000000 : ℝ)|^137 ≤ (40465815726049/100000000000000 : ℝ)^105
        have hw : |(-4998771617/10000000000 : ℝ)|=(4998771617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4481314737/5000000000 : ℝ)*x 0 + (-1335305417/10000000000 : ℝ)*x 1 + (1170361013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4481314737/5000000000 : ℝ)^137 ≤ (10835515816509/12500000000000 : ℝ)^105 := by
    have hnat : (4481314737 : ℕ)^137*12500000000000^105 ≤ 10835515816509^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481314737 5000000000 10835515816509 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1335305417/10000000000 : ℝ)^137 ≤ (7229210858167/100000000000000 : ℝ)^105 := by
    have hnat : (1335305417 : ℕ)^137*100000000000000^105 ≤ 7229210858167^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335305417 10000000000 7229210858167 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1170361013/10000000000 : ℝ)^137 ≤ (1217332518707/20000000000000 : ℝ)^105 := by
    have hnat : (1170361013 : ℕ)^137*20000000000000^105 ≤ 1217332518707^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170361013 10000000000 1217332518707 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4481314737/5000000000 : ℝ), (-1335305417/10000000000 : ℝ), (1170361013/10000000000 : ℝ)] ![(10835515816509/12500000000000 : ℝ), (7229210858167/100000000000000 : ℝ), (1217332518707/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4481314737/5000000000 : ℝ)|^137 ≤ (10835515816509/12500000000000 : ℝ)^105
        have hw : |(4481314737/5000000000 : ℝ)|=(4481314737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1335305417/10000000000 : ℝ)|^137 ≤ (7229210858167/100000000000000 : ℝ)^105
        have hw : |(-1335305417/10000000000 : ℝ)|=(1335305417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1170361013/10000000000 : ℝ)|^137 ≤ (1217332518707/20000000000000 : ℝ)^105
        have hw : |(1170361013/10000000000 : ℝ)|=(1170361013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s0_25 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (167957511/625000000 : ℝ)*x 0 + (-1315673603/2500000000 : ℝ)*x 1 + (-2416280267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167957511/625000000 : ℝ)^137 ≤ (9002595028097/50000000000000 : ℝ)^105 := by
    have hnat : (167957511 : ℕ)^137*50000000000000^105 ≤ 9002595028097^105*625000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167957511 625000000 9002595028097 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315673603/2500000000 : ℝ)^137 ≤ (865511841149/2000000000000 : ℝ)^105 := by
    have hnat : (1315673603 : ℕ)^137*2000000000000^105 ≤ 865511841149^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315673603 2500000000 865511841149 2000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2416280267/5000000000 : ℝ)^137 ≤ (38719217880259/100000000000000 : ℝ)^105 := by
    have hnat : (2416280267 : ℕ)^137*100000000000000^105 ≤ 38719217880259^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416280267 5000000000 38719217880259 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167957511/625000000 : ℝ), (-1315673603/2500000000 : ℝ), (-2416280267/5000000000 : ℝ)] ![(9002595028097/50000000000000 : ℝ), (865511841149/2000000000000 : ℝ), (38719217880259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167957511/625000000 : ℝ)|^137 ≤ (9002595028097/50000000000000 : ℝ)^105
        have hw : |(167957511/625000000 : ℝ)|=(167957511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1315673603/2500000000 : ℝ)|^137 ≤ (865511841149/2000000000000 : ℝ)^105
        have hw : |(-1315673603/2500000000 : ℝ)|=(1315673603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2416280267/5000000000 : ℝ)|^137 ≤ (38719217880259/100000000000000 : ℝ)^105
        have hw : |(-2416280267/5000000000 : ℝ)|=(2416280267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s1_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3450400403/10000000000 : ℝ)*x 0 + (-4251904701/10000000000 : ℝ)*x 1 + (-1034096227/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3450400403/10000000000 : ℝ)^137 ≤ (4989530926373/20000000000000 : ℝ)^105 := by
    have hnat : (3450400403 : ℕ)^137*20000000000000^105 ≤ 4989530926373^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3450400403 10000000000 4989530926373 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4251904701/10000000000 : ℝ)^137 ≤ (32763472775297/100000000000000 : ℝ)^105 := by
    have hnat : (4251904701 : ℕ)^137*100000000000000^105 ≤ 32763472775297^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251904701 10000000000 32763472775297 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034096227/2000000000 : ℝ)^137 ≤ (42288872575291/100000000000000 : ℝ)^105 := by
    have hnat : (1034096227 : ℕ)^137*100000000000000^105 ≤ 42288872575291^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034096227 2000000000 42288872575291 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3450400403/10000000000 : ℝ), (-4251904701/10000000000 : ℝ), (-1034096227/2000000000 : ℝ)] ![(4989530926373/20000000000000 : ℝ), (32763472775297/100000000000000 : ℝ), (42288872575291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3450400403/10000000000 : ℝ)|^137 ≤ (4989530926373/20000000000000 : ℝ)^105
        have hw : |(-3450400403/10000000000 : ℝ)|=(3450400403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4251904701/10000000000 : ℝ)|^137 ≤ (32763472775297/100000000000000 : ℝ)^105
        have hw : |(-4251904701/10000000000 : ℝ)|=(4251904701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1034096227/2000000000 : ℝ)|^137 ≤ (42288872575291/100000000000000 : ℝ)^105
        have hw : |(-1034096227/2000000000 : ℝ)|=(1034096227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s1_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3920090531/10000000000 : ℝ)*x 0 + (4856871233/10000000000 : ℝ)*x 1 + (-1032885617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3920090531/10000000000 : ℝ)^137 ≤ (589356715101/2000000000000 : ℝ)^105 := by
    have hnat : (3920090531 : ℕ)^137*2000000000000^105 ≤ 589356715101^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3920090531 10000000000 589356715101 2000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4856871233/10000000000 : ℝ)^137 ≤ (38973555375137/100000000000000 : ℝ)^105 := by
    have hnat : (4856871233 : ℕ)^137*100000000000000^105 ≤ 38973555375137^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4856871233 10000000000 38973555375137 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032885617/2500000000 : ℝ)^137 ≤ (31558608844161/100000000000000 : ℝ)^105 := by
    have hnat : (1032885617 : ℕ)^137*100000000000000^105 ≤ 31558608844161^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032885617 2500000000 31558608844161 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3920090531/10000000000 : ℝ), (4856871233/10000000000 : ℝ), (-1032885617/2500000000 : ℝ)] ![(589356715101/2000000000000 : ℝ), (38973555375137/100000000000000 : ℝ), (31558608844161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3920090531/10000000000 : ℝ)|^137 ≤ (589356715101/2000000000000 : ℝ)^105
        have hw : |(3920090531/10000000000 : ℝ)|=(3920090531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4856871233/10000000000 : ℝ)|^137 ≤ (38973555375137/100000000000000 : ℝ)^105
        have hw : |(4856871233/10000000000 : ℝ)|=(4856871233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1032885617/2500000000 : ℝ)|^137 ≤ (31558608844161/100000000000000 : ℝ)^105
        have hw : |(-1032885617/2500000000 : ℝ)|=(1032885617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s1_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2719760461/5000000000 : ℝ)*x 0 + (-250229319/625000000 : ℝ)*x 1 + (170287909/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2719760461/5000000000 : ℝ)^137 ≤ (22591216433507/50000000000000 : ℝ)^105 := by
    have hnat : (2719760461 : ℕ)^137*50000000000000^105 ≤ 22591216433507^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719760461 5000000000 22591216433507 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250229319/625000000 : ℝ)^137 ≤ (3786278770003/12500000000000 : ℝ)^105 := by
    have hnat : (250229319 : ℕ)^137*12500000000000^105 ≤ 3786278770003^105*625000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250229319 625000000 3786278770003 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170287909/500000000 : ℝ)^137 ≤ (6131834241313/25000000000000 : ℝ)^105 := by
    have hnat : (170287909 : ℕ)^137*25000000000000^105 ≤ 6131834241313^105*500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170287909 500000000 6131834241313 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2719760461/5000000000 : ℝ), (-250229319/625000000 : ℝ), (170287909/500000000 : ℝ)] ![(22591216433507/50000000000000 : ℝ), (3786278770003/12500000000000 : ℝ), (6131834241313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2719760461/5000000000 : ℝ)|^137 ≤ (22591216433507/50000000000000 : ℝ)^105
        have hw : |(2719760461/5000000000 : ℝ)|=(2719760461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-250229319/625000000 : ℝ)|^137 ≤ (3786278770003/12500000000000 : ℝ)^105
        have hw : |(-250229319/625000000 : ℝ)|=(250229319/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170287909/500000000 : ℝ)|^137 ≤ (6131834241313/25000000000000 : ℝ)^105
        have hw : |(170287909/500000000 : ℝ)|=(170287909/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305032_s1_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2220139957/5000000000 : ℝ)*x 0 + (-3823006453/10000000000 : ℝ)*x 1 + (-232446211/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2220139957/5000000000 : ℝ)^137 ≤ (34670048969603/100000000000000 : ℝ)^105 := by
    have hnat : (2220139957 : ℕ)^137*100000000000000^105 ≤ 34670048969603^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220139957 5000000000 34670048969603 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3823006453/10000000000 : ℝ)^137 ≤ (142596214767/500000000000 : ℝ)^105 := by
    have hnat : (3823006453 : ℕ)^137*500000000000^105 ≤ 142596214767^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3823006453 10000000000 142596214767 500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (232446211/500000000 : ℝ)^137 ≤ (36810708058401/100000000000000 : ℝ)^105 := by
    have hnat : (232446211 : ℕ)^137*100000000000000^105 ≤ 36810708058401^105*500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232446211 500000000 36810708058401 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2220139957/5000000000 : ℝ), (-3823006453/10000000000 : ℝ), (-232446211/500000000 : ℝ)] ![(34670048969603/100000000000000 : ℝ), (142596214767/500000000000 : ℝ), (36810708058401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2220139957/5000000000 : ℝ)|^137 ≤ (34670048969603/100000000000000 : ℝ)^105
        have hw : |(2220139957/5000000000 : ℝ)|=(2220139957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3823006453/10000000000 : ℝ)|^137 ≤ (142596214767/500000000000 : ℝ)^105
        have hw : |(-3823006453/10000000000 : ℝ)|=(3823006453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-232446211/500000000 : ℝ)|^137 ≤ (36810708058401/100000000000000 : ℝ)^105
        have hw : |(-232446211/500000000 : ℝ)|=(232446211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305032 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base30 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((2814071661/10000000000 : ℝ)*X 1 0+(5355912561/10000000000 : ℝ)*X 1 1+(-2314278949/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((7442403417/10000000000 : ℝ)*X 2 0+(-1315228693/5000000000 : ℝ)*X 2 1+(2273230597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2386421393/10000000000 : ℝ)*X 0 0+(-295451157/625000000 : ℝ)*X 0 1+(-5602566601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2846637549/10000000000 : ℝ)*X 1 0+(1214237661/2000000000 : ℝ)*X 1 1+(-3815203141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1474291803/2000000000 : ℝ)*X 2 0+(-2282502869/10000000000 : ℝ)*X 2 1+(2718399899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((4506393629/10000000000 : ℝ)*X 0 0+(-331504867/1250000000 : ℝ)*X 0 1+(-5602566601/10000000000 : ℝ)*X 0 2+(4506393629/10000000000 : ℝ)*X 1 0+(-331504867/1250000000 : ℝ)*X 1 1+(-5602566601/10000000000 : ℝ)*X 1 2+(4506393629/10000000000 : ℝ)*X 2 0+(-331504867/1250000000 : ℝ)*X 2 1+(-5602566601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1946891263/10000000000 : ℝ)*X 0 0+(-4491627481/10000000000 : ℝ)*X 0 1+(-6145620657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((62541359/312500000 : ℝ)*X 1 0+(2841688123/5000000000 : ℝ)*X 1 1+(-494509619/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2109586253/2500000000 : ℝ)*X 2 0+(-1820911581/10000000000 : ℝ)*X 2 1+(1584372129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((5087123409/10000000000 : ℝ)*X 0 0+(-102622069/312500000 : ℝ)*X 0 1+(-898633821/2000000000 : ℝ)*X 0 2+(5087123409/10000000000 : ℝ)*X 1 0+(-102622069/312500000 : ℝ)*X 1 1+(-898633821/2000000000 : ℝ)*X 1 2+(5087123409/10000000000 : ℝ)*X 2 0+(-102622069/312500000 : ℝ)*X 2 1+(-898633821/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-167957511/625000000 : ℝ)*X 0 0+(-1315673603/2500000000 : ℝ)*X 0 1+(-2416280267/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((951189053/5000000000 : ℝ)*X 1 0+(228130867/400000000 : ℝ)*X 1 1+(-4998771617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4481314737/5000000000 : ℝ)*X 2 0+(-1335305417/10000000000 : ℝ)*X 2 1+(1170361013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((167957511/625000000 : ℝ)*X 0 0+(-1315673603/2500000000 : ℝ)*X 0 1+(-2416280267/5000000000 : ℝ)*X 0 2+(167957511/625000000 : ℝ)*X 1 0+(-1315673603/2500000000 : ℝ)*X 1 1+(-2416280267/5000000000 : ℝ)*X 1 2+(167957511/625000000 : ℝ)*X 2 0+(-1315673603/2500000000 : ℝ)*X 2 1+(-2416280267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((4493/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4493/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3702726181782264603189/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (751171983767/1000000000000 : ℝ)*(base1) + (83702276623/200000000000 : ℝ)*(base39) + (52609263/40000000000 : ℝ)*(base50) + (1729051/500000000000 : ℝ)*(base59) + (291018103809/500000000000 : ℝ)*(base60) + (1185122196127/500000000000 : ℝ)*(major_s0_0) + (1185122196127/500000000000 : ℝ)*(major_s0_1) + (1185122196127/500000000000 : ℝ)*(major_s0_2) + (26943053/500000000000 : ℝ)*(sp_s0_2) + (157666007419/40000000000 : ℝ)*(sp_s0_7) + (319057760587/100000000000 : ℝ)*(sp_s0_8) + (797630929941/250000000000 : ℝ)*(sp_s0_9) + (798736726381/1000000000000 : ℝ)*(sp_s0_13) + (49702081/500000000000 : ℝ)*(sp_s0_14) + (1549908710147/1000000000000 : ℝ)*(f.failure) + (319057760587/100000000000 : ℝ)*(f.sum) + (899140421/1250000000000000000000 : ℝ)*base62 + (2666074661431919/5000000000000000000000000000 : ℝ)*base65 + (829392737431919/5000000000000000000000000000 : ℝ)*base67 + (1311269101281383/2500000000000000000000000000 : ℝ)*base68 + (659594697698937/1000000000000000000000000000 : ℝ)*base71 + (2713474533068081/5000000000000000000000000000 : ℝ)*base73 + (305921546218617/2500000000000000000000000000 : ℝ)*base74 + (132122393531383/2500000000000000000000000000 : ℝ)*base77 + (5791911863/10000000000000000000000 : ℝ)*base79 + (1237/3125000000000000 : ℝ)*base86 + (1237/3125000000000000 : ℝ)*base88 + (1237/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29699/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-29699/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6123441375018909/1000000000000000000000 : ℝ) := by norm_num
    linear_combination (7250783/1000000000000 : ℝ)*(base5) + (67195248869/100000000000 : ℝ)*(base39) + (952524980811/1000000000000 : ℝ)*(base40) + (754129387939/1000000000000 : ℝ)*(base60) + (1741882993121/500000000000 : ℝ)*(major_s0_0) + (1741882993121/500000000000 : ℝ)*(major_s0_1) + (1741882993121/500000000000 : ℝ)*(major_s0_2) + (25374717/500000000000 : ℝ)*(sp_s0_1) + (15432843/1000000000000 : ℝ)*(sp_s0_9) + (5060909/125000000000 : ℝ)*(sp_s0_13) + (4689486678139/1000000000000 : ℝ)*(sp_s0_14) + (937887185741/200000000000 : ℝ)*(sp_s0_15) + (4689478496079/1000000000000 : ℝ)*(sp_s0_16) + (2277995515137/1000000000000 : ℝ)*(sp_s0_19) + (284755406649/125000000000 : ℝ)*(f.failure) + (4689486678139/1000000000000 : ℝ)*(f.sum) + (332683141/2500000000000000000000 : ℝ)*base62 + (1936838112432463/5000000000000000000000000000 : ℝ)*base64 + (2683472495932463/5000000000000000000000000000 : ℝ)*base66 + (584931259224391/2500000000000000000000000000 : ℝ)*base69 + (179743394023751/1000000000000000000000000000 : ℝ)*base71 + (2757692144567537/5000000000000000000000000000 : ℝ)*base72 + (1495665053525609/2500000000000000000000000000 : ℝ)*base75 + (1094139879474391/2500000000000000000000000000 : ℝ)*base76 + (1254820191/10000000000000000000000 : ℝ)*base78 + (841/1562500000000000 : ℝ)*base86 + (841/1562500000000000 : ℝ)*base88 + (841/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-4359/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-4359/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3589194982231233573543/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (147446856487/125000000000 : ℝ)*(base1) + (684655491539/500000000000 : ℝ)*(base39) + (626627709091/500000000000 : ℝ)*(base40) + (56913947609/500000000000 : ℝ)*(base50) + (147110823429/1000000000000 : ℝ)*(base60) + (1073311836173/500000000000 : ℝ)*(major_s0_0) + (1073311836173/500000000000 : ℝ)*(major_s0_1) + (1073311836173/500000000000 : ℝ)*(major_s0_2) + (6677559/20000000000 : ℝ)*(sp_s0_15) + (38273769/1000000000000 : ℝ)*(sp_s0_16) + (406913867489/100000000000 : ℝ)*(sp_s0_20) + (577845989009/200000000000 : ℝ)*(sp_s0_21) + (115581021969/40000000000 : ℝ)*(sp_s0_22) + (8964308507/40000000000 : ℝ)*(sp_s0_25) + (140368256457/100000000000 : ℝ)*(f.failure) + (577912764599/200000000000 : ℝ)*(f.sum) + (61710627/125000000000000000000 : ℝ)*base62 + (868849016058819/5000000000000000000000000000 : ℝ)*base64 + (2281062551058819/5000000000000000000000000000 : ℝ)*base66 + (44118863035317/2500000000000000000000000000 : ℝ)*base68 + (68711850497637/1000000000000000000000000000 : ℝ)*base70 + (1675925763558819/5000000000000000000000000000 : ℝ)*base73 + (2073422901035317/2500000000000000000000000000 : ℝ)*base75 + (1281521750964683/2500000000000000000000000000 : ℝ)*base76 + (1247204831/2500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (61/156250000000000 : ℝ)*base86 + (61/156250000000000 : ℝ)*base88 + (61/156250000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (4493/50000 : ℝ) ^ (133/32 : ℝ) ≤ (4474663786799427/100000000000000000000 : ℝ) := by
    have hpowers : (4493/50000 : ℝ)^133 ≤ (4474663786799427/100000000000000000000 : ℝ)^32 := by
      have hnat : (4493 : ℕ)^133*100000000000000000000^32 ≤ 4474663786799427^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4493 50000 4474663786799427 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4493/50000 : ℝ)) (X := (4474663786799427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100004474663786799427/100000000000000000000 : ℝ) ≤ (200002153185089/200000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (100004474663786799427/100000000000000000000 : ℝ)^32 ≤ (200002153185089/200000000000000 : ℝ)^133 := by
      have hnat : (100004474663786799427 : ℕ)^32*200000000000000^133 ≤ 200002153185089^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100004474663786799427 100000000000000000000 200002153185089 200000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200002153185089/200000000000000 : ℝ)) (X := (100004474663786799427/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50004474663786799427/50000000000000000000 : ℝ) ≤ (1250026914356351/1250000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50004474663786799427/50000000000000000000 : ℝ)^32 ≤ (1250026914356351/1250000000000000 : ℝ)^133 := by
      have hnat : (50004474663786799427 : ℕ)^32*1250000000000000^133 ≤ 1250026914356351^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004474663786799427 50000000000000000000 1250026914356351 1250000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250026914356351/1250000000000000 : ℝ)) (X := (50004474663786799427/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2153185089/17972000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(53827798179/449300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (4493/50000 : ℝ)) (alpha := (2153185089/17972000000000 : ℝ)) (beta := (53827798179/449300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4493/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2153185089/17972000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(53827798179/449300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (29699/100000 : ℝ) ^ (133/32 : ℝ) ≤ (160887841254116191/25000000000000000000 : ℝ) := by
    have hpowers : (29699/100000 : ℝ)^133 ≤ (160887841254116191/25000000000000000000 : ℝ)^32 := by
      have hnat : (29699 : ℕ)^133*25000000000000000000^32 ≤ 160887841254116191^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29699 100000 160887841254116191 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29699/100000 : ℝ)) (X := (160887841254116191/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25160887841254116191/25000000000000000000 : ℝ) ≤ (2503861562212187/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (25160887841254116191/25000000000000000000 : ℝ)^32 ≤ (2503861562212187/2500000000000000 : ℝ)^133 := by
      have hnat : (25160887841254116191 : ℕ)^32*2500000000000000^133 ≤ 2503861562212187^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25160887841254116191 25000000000000000000 2503861562212187 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503861562212187/2500000000000000 : ℝ)) (X := (25160887841254116191/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12660887841254116191/12500000000000000000 : ℝ) ≤ (10030817673841703/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (12660887841254116191/12500000000000000000 : ℝ)^32 ≤ (10030817673841703/10000000000000000 : ℝ)^133 := by
      have hnat : (12660887841254116191 : ℕ)^32*10000000000000000^133 ≤ 10030817673841703^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12660887841254116191 12500000000000000000 10030817673841703 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030817673841703/10000000000000000 : ℝ)) (X := (12660887841254116191/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(3861562212187/742475000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(3074284998591/593980000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (29699/100000 : ℝ)) (alpha := (3861562212187/742475000000000 : ℝ)) (beta := (3074284998591/593980000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (29699/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(3861562212187/742475000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(3074284998591/593980000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (4359/20000 : ℝ) ^ (133/32 : ℝ) ≤ (44461669240990469/25000000000000000000 : ℝ) := by
    have hpowers : (4359/20000 : ℝ)^133 ≤ (44461669240990469/25000000000000000000 : ℝ)^32 := by
      have hnat : (4359 : ℕ)^133*25000000000000000000^32 ≤ 44461669240990469^32*20000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4359 20000 44461669240990469 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4359/20000 : ℝ)) (X := (44461669240990469/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25044461669240990469/25000000000000000000 : ℝ) ≤ (10004276131255937/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (25044461669240990469/25000000000000000000 : ℝ)^32 ≤ (10004276131255937/10000000000000000 : ℝ)^133 := by
      have hnat : (25044461669240990469 : ℕ)^32*10000000000000000^133 ≤ 10004276131255937^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25044461669240990469 25000000000000000000 10004276131255937 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004276131255937/10000000000000000 : ℝ)) (X := (25044461669240990469/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12544461669240990469/12500000000000000000 : ℝ) ≤ (5004273250725797/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (12544461669240990469/12500000000000000000 : ℝ)^32 ≤ (5004273250725797/5000000000000000 : ℝ)^133 := by
      have hnat : (12544461669240990469 : ℕ)^32*5000000000000000^133 ≤ 5004273250725797^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12544461669240990469 12500000000000000000 5004273250725797 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004273250725797/5000000000000000 : ℝ)) (X := (12544461669240990469/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(4276131255937/2179500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(4270370195657/2179500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (4359/20000 : ℝ)) (alpha := (4276131255937/2179500000000000 : ℝ)) (beta := (4270370195657/2179500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (4359/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(4276131255937/2179500000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(4270370195657/2179500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3450400403/10000000000 : ℝ)*X 0 0+(-4251904701/10000000000 : ℝ)*X 0 1+(-1034096227/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3920090531/10000000000 : ℝ)*X 1 0+(4856871233/10000000000 : ℝ)*X 1 1+(-1032885617/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2719760461/5000000000 : ℝ)*X 2 0+(-250229319/625000000 : ℝ)*X 2 1+(170287909/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2220139957/5000000000 : ℝ)*X 0 0+(-3823006453/10000000000 : ℝ)*X 0 1+(-232446211/500000000 : ℝ)*X 0 2+(2220139957/5000000000 : ℝ)*X 1 0+(-3823006453/10000000000 : ℝ)*X 1 1+(-232446211/500000000 : ℝ)*X 1 2+(2220139957/5000000000 : ℝ)*X 2 0+(-3823006453/10000000000 : ℝ)*X 2 1+(-232446211/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305032_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-19299/3125 : ℝ) < ((-4779/3125 : ℝ)*P 0+(-4779/3125 : ℝ)*P 1+(-4779/3125 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-19299/3125 : ℝ) < (-741975644688925057898052522422361/121178026856875000000000000000000 : ℝ) := by norm_num
    linear_combination (1181763/1000000000000 : ℝ)*(base1) + (30383/1000000000000 : ℝ)*(base17) + (251227/1000000000000 : ℝ)*(base22) + (583127/1000000000000 : ℝ)*(base30) + (550598804309/1000000000000 : ℝ)*(base39) + (82411236689/250000000000 : ℝ)*(base40) + (17003479279/1000000000000 : ℝ)*(base50) + (56431824823/200000000000 : ℝ)*(base60) + (4779/3125 : ℝ)*(major_s1_0) + (4779/3125 : ℝ)*(major_s1_1) + (4779/3125 : ℝ)*(major_s1_2) + (1020504147967/500000000000 : ℝ)*(sp_s1_0) + (510251770947/250000000000 : ℝ)*(sp_s1_1) + (63781464467/31250000000 : ℝ)*(sp_s1_2) + (99999823511/100000000000 : ℝ)*(sp_s1_6) + (2041007114171/1000000000000 : ℝ)*(f.sum) + (4976325495570857/215763235000000000000000000000 : ℝ)*base63 + (1123044192373/3632500000000000000000000 : ℝ)*base65 + (863380965629/29699000000000000000000000 : ℝ)*base66 + (91596116547/454062500000000000000000 : ℝ)*base68 + (21707587767964177/32641645000000000000000000000 : ℝ)*base71 + (876498410361/5616250000000000000000000 : ℝ)*base72 + (828070581827/74247500000000000000000000 : ℝ)*base75 + (1153081801021/22465000000000000000000000 : ℝ)*base76 + (12850433572022401/33359401750000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c305033_s0_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-834391777/2500000000 : ℝ)*x 0 + (-5411035853/10000000000 : ℝ)*x 1 + (4099284191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834391777/2500000000 : ℝ)^137 ≤ (23888541108721/100000000000000 : ℝ)^105 := by
    have hnat : (834391777 : ℕ)^137*100000000000000^105 ≤ 23888541108721^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834391777 2500000000 23888541108721 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411035853/10000000000 : ℝ)^137 ≤ (8974792934773/20000000000000 : ℝ)^105 := by
    have hnat : (5411035853 : ℕ)^137*20000000000000^105 ≤ 8974792934773^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411035853 10000000000 8974792934773 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4099284191/10000000000 : ℝ)^137 ≤ (15618747100257/50000000000000 : ℝ)^105 := by
    have hnat : (4099284191 : ℕ)^137*50000000000000^105 ≤ 15618747100257^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4099284191 10000000000 15618747100257 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-834391777/2500000000 : ℝ), (-5411035853/10000000000 : ℝ), (4099284191/10000000000 : ℝ)] ![(23888541108721/100000000000000 : ℝ), (8974792934773/20000000000000 : ℝ), (15618747100257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-834391777/2500000000 : ℝ)|^137 ≤ (23888541108721/100000000000000 : ℝ)^105
        have hw : |(-834391777/2500000000 : ℝ)|=(834391777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5411035853/10000000000 : ℝ)|^137 ≤ (8974792934773/20000000000000 : ℝ)^105
        have hw : |(-5411035853/10000000000 : ℝ)|=(5411035853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4099284191/10000000000 : ℝ)|^137 ≤ (15618747100257/50000000000000 : ℝ)^105
        have hw : |(4099284191/10000000000 : ℝ)|=(4099284191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305033_s0_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2746158731/10000000000 : ℝ)*x 0 + (930858757/2000000000 : ℝ)*x 1 + (5386859607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2746158731/10000000000 : ℝ)^137 ≤ (18521262720213/100000000000000 : ℝ)^105 := by
    have hnat : (2746158731 : ℕ)^137*100000000000000^105 ≤ 18521262720213^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746158731 10000000000 18521262720213 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (930858757/2000000000 : ℝ)^137 ≤ (7373238430147/20000000000000 : ℝ)^105 := by
    have hnat : (930858757 : ℕ)^137*20000000000000^105 ≤ 7373238430147^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930858757 2000000000 7373238430147 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386859607/10000000000 : ℝ)^137 ≤ (5576568139509/12500000000000 : ℝ)^105 := by
    have hnat : (5386859607 : ℕ)^137*12500000000000^105 ≤ 5576568139509^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386859607 10000000000 5576568139509 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2746158731/10000000000 : ℝ), (930858757/2000000000 : ℝ), (5386859607/10000000000 : ℝ)] ![(18521262720213/100000000000000 : ℝ), (7373238430147/20000000000000 : ℝ), (5576568139509/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2746158731/10000000000 : ℝ)|^137 ≤ (18521262720213/100000000000000 : ℝ)^105
        have hw : |(2746158731/10000000000 : ℝ)|=(2746158731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(930858757/2000000000 : ℝ)|^137 ≤ (7373238430147/20000000000000 : ℝ)^105
        have hw : |(930858757/2000000000 : ℝ)|=(930858757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386859607/10000000000 : ℝ)|^137 ≤ (5576568139509/12500000000000 : ℝ)^105
        have hw : |(5386859607/10000000000 : ℝ)|=(5386859607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305033_s0_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3140715273/5000000000 : ℝ)*x 0 + (-185330459/625000000 : ℝ)*x 1 + (-1728641111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3140715273/5000000000 : ℝ)^137 ≤ (13628702565517/25000000000000 : ℝ)^105 := by
    have hnat : (3140715273 : ℕ)^137*25000000000000^105 ≤ 13628702565517^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3140715273 5000000000 13628702565517 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185330459/625000000 : ℝ)^137 ≤ (2559074118271/12500000000000 : ℝ)^105 := by
    have hnat : (185330459 : ℕ)^137*12500000000000^105 ≤ 2559074118271^105*625000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185330459 625000000 2559074118271 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1728641111/5000000000 : ℝ)^137 ≤ (25012596780411/100000000000000 : ℝ)^105 := by
    have hnat : (1728641111 : ℕ)^137*100000000000000^105 ≤ 25012596780411^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728641111 5000000000 25012596780411 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3140715273/5000000000 : ℝ), (-185330459/625000000 : ℝ), (-1728641111/5000000000 : ℝ)] ![(13628702565517/25000000000000 : ℝ), (2559074118271/12500000000000 : ℝ), (25012596780411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3140715273/5000000000 : ℝ)|^137 ≤ (13628702565517/25000000000000 : ℝ)^105
        have hw : |(3140715273/5000000000 : ℝ)|=(3140715273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-185330459/625000000 : ℝ)|^137 ≤ (2559074118271/12500000000000 : ℝ)^105
        have hw : |(-185330459/625000000 : ℝ)|=(185330459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1728641111/5000000000 : ℝ)|^137 ≤ (25012596780411/100000000000000 : ℝ)^105
        have hw : |(-1728641111/5000000000 : ℝ)|=(1728641111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305033_s0_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (987171537/2000000000 : ℝ)*x 0 + (-980755753/2500000000 : ℝ)*x 1 + (2022598773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987171537/2000000000 : ℝ)^137 ≤ (39802581479447/100000000000000 : ℝ)^105 := by
    have hnat : (987171537 : ℕ)^137*100000000000000^105 ≤ 39802581479447^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987171537 2000000000 39802581479447 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (980755753/2500000000 : ℝ)^137 ≤ (29496601002409/100000000000000 : ℝ)^105 := by
    have hnat : (980755753 : ℕ)^137*100000000000000^105 ≤ 29496601002409^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980755753 2500000000 29496601002409 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2022598773/5000000000 : ℝ)^137 ≤ (30700817506037/100000000000000 : ℝ)^105 := by
    have hnat : (2022598773 : ℕ)^137*100000000000000^105 ≤ 30700817506037^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022598773 5000000000 30700817506037 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(987171537/2000000000 : ℝ), (-980755753/2500000000 : ℝ), (2022598773/5000000000 : ℝ)] ![(39802581479447/100000000000000 : ℝ), (29496601002409/100000000000000 : ℝ), (30700817506037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(987171537/2000000000 : ℝ)|^137 ≤ (39802581479447/100000000000000 : ℝ)^105
        have hw : |(987171537/2000000000 : ℝ)|=(987171537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-980755753/2500000000 : ℝ)|^137 ≤ (29496601002409/100000000000000 : ℝ)^105
        have hw : |(-980755753/2500000000 : ℝ)|=(980755753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2022598773/5000000000 : ℝ)|^137 ≤ (30700817506037/100000000000000 : ℝ)^105
        have hw : |(2022598773/5000000000 : ℝ)|=(2022598773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305033 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-834391777/2500000000 : ℝ)*X 0 0+(-5411035853/10000000000 : ℝ)*X 0 1+(4099284191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305033_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2746158731/10000000000 : ℝ)*X 1 0+(930858757/2000000000 : ℝ)*X 1 1+(5386859607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305033_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3140715273/5000000000 : ℝ)*X 2 0+(-185330459/625000000 : ℝ)*X 2 1+(-1728641111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305033_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((987171537/2000000000 : ℝ)*X 0 0+(-980755753/2500000000 : ℝ)*X 0 1+(2022598773/5000000000 : ℝ)*X 0 2+(987171537/2000000000 : ℝ)*X 1 0+(-980755753/2500000000 : ℝ)*X 1 1+(2022598773/5000000000 : ℝ)*X 1 2+(987171537/2000000000 : ℝ)*X 2 0+(-980755753/2500000000 : ℝ)*X 2 1+(2022598773/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305033_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-19299/3125 : ℝ) < ((-4779/3125 : ℝ)*P 0+(-4779/3125 : ℝ)*P 1+(-4779/3125 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-19299/3125 : ℝ) < (-1543140267535964917799913651/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154720192969/1000000000000 : ℝ)*(base5) + (202341/250000000000 : ℝ)*(base10) + (6003/500000000000 : ℝ)*(base13) + (442937/1000000000000 : ℝ)*(base39) + (132070138311/500000000000 : ℝ)*(base40) + (79380889263/500000000000 : ℝ)*(base49) + (132007/250000000000 : ℝ)*(base53) + (269492788967/1000000000000 : ℝ)*(base60) + (4779/3125 : ℝ)*(major_s0_0) + (4779/3125 : ℝ)*(major_s0_1) + (382319867993/250000000000 : ℝ)*(major_s0_2) + (128594937957/62500000000 : ℝ)*(sp_s0_0) + (2057519828683/1000000000000 : ℝ)*(sp_s0_1) + (27653006871/12500000000 : ℝ)*(sp_s0_2) + (845279807031/1000000000000 : ℝ)*(sp_s0_6) + (2057520356711/1000000000000 : ℝ)*(f.sum) + (313052284524903/1250000000000000000000000000 : ℝ)*base63 + (1514560856556279/2500000000000000000000000000 : ℝ)*base64 + (1974926821/5000000000000000000000 : ℝ)*base67 + (142351133399903/1250000000000000000000000000 : ℝ)*base69 + (1308200369306279/2500000000000000000000000000 : ℝ)*base70 + (5632942333/10000000000000000000000 : ℝ)*base73 + (19306971/400000000000000000000 : ℝ)*base74 + (45529617/2500000000000000000000 : ℝ)*base76 + (508521517/5000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p005_b017 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (c : Fin 88) (hlo : 32 ≤ c.val) (hhi : c.val < 34)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=32 ∨ c=33 := by omega
  rcases hc with rfl|rfl
  · exact collision_c305032 p hpa (by linarith only [hpb]) X hX
  · exact collision_c305033 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (c : Fin 88) (hlo : 32 ≤ c.val) (hhi : c.val < 34)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p005_b017 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
