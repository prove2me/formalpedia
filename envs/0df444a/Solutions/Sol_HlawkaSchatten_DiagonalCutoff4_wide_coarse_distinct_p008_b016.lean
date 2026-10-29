-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b016
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:43:05.094692+00:00
-- url     : https://prove2.me/submissions/1c125002-1803-4f39-b4ac-f69a67b7b13b

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
theorem collision_support_c308027_s0_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2199043317/5000000000 : ℝ)*x 0 + (-358768081/2500000000 : ℝ)*x 1 + (6520649067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199043317/5000000000 : ℝ)^35 ≤ (34479754038097/100000000000000 : ℝ)^27 := by
    have hnat : (2199043317 : ℕ)^35*100000000000000^27 ≤ 34479754038097^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199043317 5000000000 34479754038097 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (358768081/2500000000 : ℝ)^35 ≤ (4036719937489/50000000000000 : ℝ)^27 := by
    have hnat : (358768081 : ℕ)^35*50000000000000^27 ≤ 4036719937489^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358768081 2500000000 4036719937489 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6520649067/10000000000 : ℝ)^35 ≤ (57446806061837/100000000000000 : ℝ)^27 := by
    have hnat : (6520649067 : ℕ)^35*100000000000000^27 ≤ 57446806061837^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6520649067 10000000000 57446806061837 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2199043317/5000000000 : ℝ), (-358768081/2500000000 : ℝ), (6520649067/10000000000 : ℝ)] ![(34479754038097/100000000000000 : ℝ), (4036719937489/50000000000000 : ℝ), (57446806061837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2199043317/5000000000 : ℝ)|^35 ≤ (34479754038097/100000000000000 : ℝ)^27
        have hw : |(2199043317/5000000000 : ℝ)|=(2199043317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-358768081/2500000000 : ℝ)|^35 ≤ (4036719937489/50000000000000 : ℝ)^27
        have hw : |(-358768081/2500000000 : ℝ)|=(358768081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6520649067/10000000000 : ℝ)|^35 ≤ (57446806061837/100000000000000 : ℝ)^27
        have hw : |(6520649067/10000000000 : ℝ)|=(6520649067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1036098281/2500000000 : ℝ)*x 0 + (81939371/125000000 : ℝ)*x 1 + (-26926041/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036098281/2500000000 : ℝ)^35 ≤ (3192390716111/10000000000000 : ℝ)^27 := by
    have hnat : (1036098281 : ℕ)^35*10000000000000^27 ≤ 3192390716111^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036098281 2500000000 3192390716111 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81939371/125000000 : ℝ)^35 ≤ (57841123531617/100000000000000 : ℝ)^27 := by
    have hnat : (81939371 : ℕ)^35*100000000000000^27 ≤ 57841123531617^27*125000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81939371 125000000 57841123531617 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26926041/156250000 : ℝ)^35 ≤ (10234969290389/100000000000000 : ℝ)^27 := by
    have hnat : (26926041 : ℕ)^35*100000000000000^27 ≤ 10234969290389^27*156250000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26926041 156250000 10234969290389 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036098281/2500000000 : ℝ), (81939371/125000000 : ℝ), (-26926041/156250000 : ℝ)] ![(3192390716111/10000000000000 : ℝ), (57841123531617/100000000000000 : ℝ), (10234969290389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036098281/2500000000 : ℝ)|^35 ≤ (3192390716111/10000000000000 : ℝ)^27
        have hw : |(1036098281/2500000000 : ℝ)|=(1036098281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81939371/125000000 : ℝ)|^35 ≤ (57841123531617/100000000000000 : ℝ)^27
        have hw : |(81939371/125000000 : ℝ)|=(81939371/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26926041/156250000 : ℝ)|^35 ≤ (10234969290389/100000000000000 : ℝ)^27
        have hw : |(-26926041/156250000 : ℝ)|=(26926041/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-29512831/1250000000 : ℝ)*x 0 + (6465897161/10000000000 : ℝ)*x 1 + (2579324129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29512831/1250000000 : ℝ)^35 ≤ (24316814923/3125000000000 : ℝ)^27 := by
    have hnat : (29512831 : ℕ)^35*3125000000000^27 ≤ 24316814923^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29512831 1250000000 24316814923 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6465897161/10000000000 : ℝ)^35 ≤ (14205574900793/25000000000000 : ℝ)^27 := by
    have hnat : (6465897161 : ℕ)^35*25000000000000^27 ≤ 14205574900793^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6465897161 10000000000 14205574900793 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2579324129/5000000000 : ℝ)^35 ≤ (42399562300677/100000000000000 : ℝ)^27 := by
    have hnat : (2579324129 : ℕ)^35*100000000000000^27 ≤ 42399562300677^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579324129 5000000000 42399562300677 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29512831/1250000000 : ℝ), (6465897161/10000000000 : ℝ), (2579324129/5000000000 : ℝ)] ![(24316814923/3125000000000 : ℝ), (14205574900793/25000000000000 : ℝ), (42399562300677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29512831/1250000000 : ℝ)|^35 ≤ (24316814923/3125000000000 : ℝ)^27
        have hw : |(-29512831/1250000000 : ℝ)|=(29512831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6465897161/10000000000 : ℝ)|^35 ≤ (14205574900793/25000000000000 : ℝ)^27
        have hw : |(6465897161/10000000000 : ℝ)|=(6465897161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2579324129/5000000000 : ℝ)|^35 ≤ (42399562300677/100000000000000 : ℝ)^27
        have hw : |(2579324129/5000000000 : ℝ)|=(2579324129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2631051851/5000000000 : ℝ)*x 0 + (1265177467/5000000000 : ℝ)*x 1 + (4899068451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631051851/5000000000 : ℝ)^35 ≤ (43505079474503/100000000000000 : ℝ)^27 := by
    have hnat : (2631051851 : ℕ)^35*100000000000000^27 ≤ 43505079474503^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631051851 5000000000 43505079474503 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1265177467/5000000000 : ℝ)^35 ≤ (263127562407/1562500000000 : ℝ)^27 := by
    have hnat : (1265177467 : ℕ)^35*1562500000000^27 ≤ 263127562407^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265177467 5000000000 263127562407 1562500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4899068451/10000000000 : ℝ)^35 ≤ (39654756513923/100000000000000 : ℝ)^27 := by
    have hnat : (4899068451 : ℕ)^35*100000000000000^27 ≤ 39654756513923^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4899068451 10000000000 39654756513923 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2631051851/5000000000 : ℝ), (1265177467/5000000000 : ℝ), (4899068451/10000000000 : ℝ)] ![(43505079474503/100000000000000 : ℝ), (263127562407/1562500000000 : ℝ), (39654756513923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2631051851/5000000000 : ℝ)|^35 ≤ (43505079474503/100000000000000 : ℝ)^27
        have hw : |(-2631051851/5000000000 : ℝ)|=(2631051851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1265177467/5000000000 : ℝ)|^35 ≤ (263127562407/1562500000000 : ℝ)^27
        have hw : |(1265177467/5000000000 : ℝ)|=(1265177467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4899068451/10000000000 : ℝ)|^35 ≤ (39654756513923/100000000000000 : ℝ)^27
        have hw : |(4899068451/10000000000 : ℝ)|=(4899068451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3809604159/10000000000 : ℝ)*x 0 + (-93693939/10000000000 : ℝ)*x 1 + (7690110481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3809604159/10000000000 : ℝ)^35 ≤ (28621744772601/100000000000000 : ℝ)^27 := by
    have hnat : (3809604159 : ℕ)^35*100000000000000^27 ≤ 28621744772601^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3809604159 10000000000 28621744772601 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93693939/10000000000 : ℝ)^35 ≤ (23482110451/10000000000000 : ℝ)^27 := by
    have hnat : (93693939 : ℕ)^35*10000000000000^27 ≤ 23482110451^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93693939 10000000000 23482110451 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7690110481/10000000000 : ℝ)^35 ≤ (71143434115399/100000000000000 : ℝ)^27 := by
    have hnat : (7690110481 : ℕ)^35*100000000000000^27 ≤ 71143434115399^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7690110481 10000000000 71143434115399 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3809604159/10000000000 : ℝ), (-93693939/10000000000 : ℝ), (7690110481/10000000000 : ℝ)] ![(28621744772601/100000000000000 : ℝ), (23482110451/10000000000000 : ℝ), (71143434115399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3809604159/10000000000 : ℝ)|^35 ≤ (28621744772601/100000000000000 : ℝ)^27
        have hw : |(3809604159/10000000000 : ℝ)|=(3809604159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93693939/10000000000 : ℝ)|^35 ≤ (23482110451/10000000000000 : ℝ)^27
        have hw : |(-93693939/10000000000 : ℝ)|=(93693939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7690110481/10000000000 : ℝ)|^35 ≤ (71143434115399/100000000000000 : ℝ)^27
        have hw : |(7690110481/10000000000 : ℝ)|=(7690110481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2266843189/10000000000 : ℝ)*x 0 + (396337503/500000000 : ℝ)*x 1 + (-1873094573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2266843189/10000000000 : ℝ)^35 ≤ (14602770164473/100000000000000 : ℝ)^27 := by
    have hnat : (2266843189 : ℕ)^35*100000000000000^27 ≤ 14602770164473^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266843189 10000000000 14602770164473 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (396337503/500000000 : ℝ)^35 ≤ (14798831701467/20000000000000 : ℝ)^27 := by
    have hnat : (396337503 : ℕ)^35*20000000000000^27 ≤ 14798831701467^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396337503 500000000 14798831701467 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873094573/10000000000 : ℝ)^35 ≤ (11403071318361/100000000000000 : ℝ)^27 := by
    have hnat : (1873094573 : ℕ)^35*100000000000000^27 ≤ 11403071318361^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873094573 10000000000 11403071318361 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2266843189/10000000000 : ℝ), (396337503/500000000 : ℝ), (-1873094573/10000000000 : ℝ)] ![(14602770164473/100000000000000 : ℝ), (14798831701467/20000000000000 : ℝ), (11403071318361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2266843189/10000000000 : ℝ)|^35 ≤ (14602770164473/100000000000000 : ℝ)^27
        have hw : |(2266843189/10000000000 : ℝ)|=(2266843189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(396337503/500000000 : ℝ)|^35 ≤ (14798831701467/20000000000000 : ℝ)^27
        have hw : |(396337503/500000000 : ℝ)|=(396337503/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1873094573/10000000000 : ℝ)|^35 ≤ (11403071318361/100000000000000 : ℝ)^27
        have hw : |(-1873094573/10000000000 : ℝ)|=(1873094573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-83566843/10000000000 : ℝ)*x 0 + (1000581047/1250000000 : ℝ)*x 1 + (683430181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83566843/10000000000 : ℝ)^35 ≤ (101230263907/50000000000000 : ℝ)^27 := by
    have hnat : (83566843 : ℕ)^35*50000000000000^27 ≤ 101230263907^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83566843 10000000000 101230263907 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000581047/1250000000 : ℝ)^35 ≤ (9367267912247/12500000000000 : ℝ)^27 := by
    have hnat : (1000581047 : ℕ)^35*12500000000000^27 ≤ 9367267912247^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000581047 1250000000 9367267912247 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683430181/2000000000 : ℝ)^35 ≤ (24859396161143/100000000000000 : ℝ)^27 := by
    have hnat : (683430181 : ℕ)^35*100000000000000^27 ≤ 24859396161143^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683430181 2000000000 24859396161143 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-83566843/10000000000 : ℝ), (1000581047/1250000000 : ℝ), (683430181/2000000000 : ℝ)] ![(101230263907/50000000000000 : ℝ), (9367267912247/12500000000000 : ℝ), (24859396161143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-83566843/10000000000 : ℝ)|^35 ≤ (101230263907/50000000000000 : ℝ)^27
        have hw : |(-83566843/10000000000 : ℝ)|=(83566843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000581047/1250000000 : ℝ)|^35 ≤ (9367267912247/12500000000000 : ℝ)^27
        have hw : |(1000581047/1250000000 : ℝ)|=(1000581047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683430181/2000000000 : ℝ)|^35 ≤ (24859396161143/100000000000000 : ℝ)^27
        have hw : |(683430181/2000000000 : ℝ)|=(683430181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-603105411/1000000000 : ℝ)*x 0 + (2210976361/10000000000 : ℝ)*x 1 + (4345200109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (603105411/1000000000 : ℝ)^35 ≤ (6489848577191/12500000000000 : ℝ)^27 := by
    have hnat : (603105411 : ℕ)^35*12500000000000^27 ≤ 6489848577191^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603105411 1000000000 6489848577191 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210976361/10000000000 : ℝ)^35 ≤ (14137961522347/100000000000000 : ℝ)^27 := by
    have hnat : (2210976361 : ℕ)^35*100000000000000^27 ≤ 14137961522347^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210976361 10000000000 14137961522347 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4345200109/10000000000 : ℝ)^35 ≤ (33943249841839/100000000000000 : ℝ)^27 := by
    have hnat : (4345200109 : ℕ)^35*100000000000000^27 ≤ 33943249841839^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345200109 10000000000 33943249841839 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-603105411/1000000000 : ℝ), (2210976361/10000000000 : ℝ), (4345200109/10000000000 : ℝ)] ![(6489848577191/12500000000000 : ℝ), (14137961522347/100000000000000 : ℝ), (33943249841839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-603105411/1000000000 : ℝ)|^35 ≤ (6489848577191/12500000000000 : ℝ)^27
        have hw : |(-603105411/1000000000 : ℝ)|=(603105411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2210976361/10000000000 : ℝ)|^35 ≤ (14137961522347/100000000000000 : ℝ)^27
        have hw : |(2210976361/10000000000 : ℝ)|=(2210976361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4345200109/10000000000 : ℝ)|^35 ≤ (33943249841839/100000000000000 : ℝ)^27
        have hw : |(4345200109/10000000000 : ℝ)|=(4345200109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (9660091/15625000 : ℝ)*x 0 + (-28022743/2500000000 : ℝ)*x 1 + (5501617947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9660091/15625000 : ℝ)^35 ≤ (53614594553371/100000000000000 : ℝ)^27 := by
    have hnat : (9660091 : ℕ)^35*100000000000000^27 ≤ 53614594553371^27*15625000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9660091 15625000 53614594553371 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28022743/2500000000 : ℝ)^35 ≤ (59250993093/20000000000000 : ℝ)^27 := by
    have hnat : (28022743 : ℕ)^35*20000000000000^27 ≤ 59250993093^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28022743 2500000000 59250993093 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5501617947/10000000000 : ℝ)^35 ≤ (46089150459393/100000000000000 : ℝ)^27 := by
    have hnat : (5501617947 : ℕ)^35*100000000000000^27 ≤ 46089150459393^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501617947 10000000000 46089150459393 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9660091/15625000 : ℝ), (-28022743/2500000000 : ℝ), (5501617947/10000000000 : ℝ)] ![(53614594553371/100000000000000 : ℝ), (59250993093/20000000000000 : ℝ), (46089150459393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9660091/15625000 : ℝ)|^35 ≤ (53614594553371/100000000000000 : ℝ)^27
        have hw : |(9660091/15625000 : ℝ)|=(9660091/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28022743/2500000000 : ℝ)|^35 ≤ (59250993093/20000000000000 : ℝ)^27
        have hw : |(-28022743/2500000000 : ℝ)|=(28022743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5501617947/10000000000 : ℝ)|^35 ≤ (46089150459393/100000000000000 : ℝ)^27
        have hw : |(5501617947/10000000000 : ℝ)|=(5501617947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (88457473/250000000 : ℝ)*x 0 + (255483213/400000000 : ℝ)*x 1 + (-2671310397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88457473/250000000 : ℝ)^35 ≤ (13003911691653/50000000000000 : ℝ)^27 := by
    have hnat : (88457473 : ℕ)^35*50000000000000^27 ≤ 13003911691653^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88457473 250000000 13003911691653 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (255483213/400000000 : ℝ)^35 ≤ (55926056053521/100000000000000 : ℝ)^27 := by
    have hnat : (255483213 : ℕ)^35*100000000000000^27 ≤ 55926056053521^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255483213 400000000 55926056053521 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2671310397/10000000000 : ℝ)^35 ≤ (18066120554539/100000000000000 : ℝ)^27 := by
    have hnat : (2671310397 : ℕ)^35*100000000000000^27 ≤ 18066120554539^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2671310397 10000000000 18066120554539 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(88457473/250000000 : ℝ), (255483213/400000000 : ℝ), (-2671310397/10000000000 : ℝ)] ![(13003911691653/50000000000000 : ℝ), (55926056053521/100000000000000 : ℝ), (18066120554539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(88457473/250000000 : ℝ)|^35 ≤ (13003911691653/50000000000000 : ℝ)^27
        have hw : |(88457473/250000000 : ℝ)|=(88457473/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(255483213/400000000 : ℝ)|^35 ≤ (55926056053521/100000000000000 : ℝ)^27
        have hw : |(255483213/400000000 : ℝ)|=(255483213/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2671310397/10000000000 : ℝ)|^35 ≤ (18066120554539/100000000000000 : ℝ)^27
        have hw : |(-2671310397/10000000000 : ℝ)|=(2671310397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-72791441/2500000000 : ℝ)*x 0 + (4152338179/10000000000 : ℝ)*x 1 + (1468037847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72791441/2500000000 : ℝ)^35 ≤ (1021105863151/100000000000000 : ℝ)^27 := by
    have hnat : (72791441 : ℕ)^35*100000000000000^27 ≤ 1021105863151^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72791441 2500000000 1021105863151 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152338179/10000000000 : ℝ)^35 ≤ (1280130524871/4000000000000 : ℝ)^27 := by
    have hnat : (4152338179 : ℕ)^35*4000000000000^27 ≤ 1280130524871^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152338179 10000000000 1280130524871 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1468037847/2000000000 : ℝ)^35 ≤ (66975630999953/100000000000000 : ℝ)^27 := by
    have hnat : (1468037847 : ℕ)^35*100000000000000^27 ≤ 66975630999953^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468037847 2000000000 66975630999953 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-72791441/2500000000 : ℝ), (4152338179/10000000000 : ℝ), (1468037847/2000000000 : ℝ)] ![(1021105863151/100000000000000 : ℝ), (1280130524871/4000000000000 : ℝ), (66975630999953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-72791441/2500000000 : ℝ)|^35 ≤ (1021105863151/100000000000000 : ℝ)^27
        have hw : |(-72791441/2500000000 : ℝ)|=(72791441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152338179/10000000000 : ℝ)|^35 ≤ (1280130524871/4000000000000 : ℝ)^27
        have hw : |(4152338179/10000000000 : ℝ)|=(4152338179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1468037847/2000000000 : ℝ)|^35 ≤ (66975630999953/100000000000000 : ℝ)^27
        have hw : |(1468037847/2000000000 : ℝ)|=(1468037847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1286518537/2000000000 : ℝ)*x 0 + (3294973857/10000000000 : ℝ)*x 1 + (358981157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1286518537/2000000000 : ℝ)^35 ≤ (11288637968083/20000000000000 : ℝ)^27 := by
    have hnat : (1286518537 : ℕ)^35*20000000000000^27 ≤ 11288637968083^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286518537 2000000000 11288637968083 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3294973857/10000000000 : ℝ)^35 ≤ (23713371140489/100000000000000 : ℝ)^27 := by
    have hnat : (3294973857 : ℕ)^35*100000000000000^27 ≤ 23713371140489^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3294973857 10000000000 23713371140489 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (358981157/1250000000 : ℝ)^35 ≤ (3968687802001/20000000000000 : ℝ)^27 := by
    have hnat : (358981157 : ℕ)^35*20000000000000^27 ≤ 3968687802001^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358981157 1250000000 3968687802001 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1286518537/2000000000 : ℝ), (3294973857/10000000000 : ℝ), (358981157/1250000000 : ℝ)] ![(11288637968083/20000000000000 : ℝ), (23713371140489/100000000000000 : ℝ), (3968687802001/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1286518537/2000000000 : ℝ)|^35 ≤ (11288637968083/20000000000000 : ℝ)^27
        have hw : |(-1286518537/2000000000 : ℝ)|=(1286518537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3294973857/10000000000 : ℝ)|^35 ≤ (23713371140489/100000000000000 : ℝ)^27
        have hw : |(3294973857/10000000000 : ℝ)|=(3294973857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(358981157/1250000000 : ℝ)|^35 ≤ (3968687802001/20000000000000 : ℝ)^27
        have hw : |(358981157/1250000000 : ℝ)|=(358981157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (413399947/1000000000 : ℝ)*x 0 + (-1184805937/10000000000 : ℝ)*x 1 + (863213637/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413399947/1000000000 : ℝ)^35 ≤ (31820162406433/100000000000000 : ℝ)^27 := by
    have hnat : (413399947 : ℕ)^35*100000000000000^27 ≤ 31820162406433^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413399947 1000000000 31820162406433 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1184805937/10000000000 : ℝ)^35 ≤ (3148780076523/50000000000000 : ℝ)^27 := by
    have hnat : (1184805937 : ℕ)^35*50000000000000^27 ≤ 3148780076523^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184805937 10000000000 3148780076523 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (863213637/1250000000 : ℝ)^35 ≤ (12376455485377/20000000000000 : ℝ)^27 := by
    have hnat : (863213637 : ℕ)^35*20000000000000^27 ≤ 12376455485377^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863213637 1250000000 12376455485377 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(413399947/1000000000 : ℝ), (-1184805937/10000000000 : ℝ), (863213637/1250000000 : ℝ)] ![(31820162406433/100000000000000 : ℝ), (3148780076523/50000000000000 : ℝ), (12376455485377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(413399947/1000000000 : ℝ)|^35 ≤ (31820162406433/100000000000000 : ℝ)^27
        have hw : |(413399947/1000000000 : ℝ)|=(413399947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1184805937/10000000000 : ℝ)|^35 ≤ (3148780076523/50000000000000 : ℝ)^27
        have hw : |(-1184805937/10000000000 : ℝ)|=(1184805937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(863213637/1250000000 : ℝ)|^35 ≤ (12376455485377/20000000000000 : ℝ)^27
        have hw : |(863213637/1250000000 : ℝ)|=(863213637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6615859753/10000000000 : ℝ)*x 0 + (2402306317/5000000000 : ℝ)*x 1 + (-633482591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6615859753/10000000000 : ℝ)^35 ≤ (29268244665357/50000000000000 : ℝ)^27 := by
    have hnat : (6615859753 : ℕ)^35*50000000000000^27 ≤ 29268244665357^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6615859753 10000000000 29268244665357 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2402306317/5000000000 : ℝ)^35 ≤ (38666506511833/100000000000000 : ℝ)^27 := by
    have hnat : (2402306317 : ℕ)^35*100000000000000^27 ≤ 38666506511833^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2402306317 5000000000 38666506511833 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (633482591/10000000000 : ℝ)^35 ≤ (2797004140993/100000000000000 : ℝ)^27 := by
    have hnat : (633482591 : ℕ)^35*100000000000000^27 ≤ 2797004140993^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633482591 10000000000 2797004140993 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6615859753/10000000000 : ℝ), (2402306317/5000000000 : ℝ), (-633482591/10000000000 : ℝ)] ![(29268244665357/50000000000000 : ℝ), (38666506511833/100000000000000 : ℝ), (2797004140993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6615859753/10000000000 : ℝ)|^35 ≤ (29268244665357/50000000000000 : ℝ)^27
        have hw : |(6615859753/10000000000 : ℝ)|=(6615859753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2402306317/5000000000 : ℝ)|^35 ≤ (38666506511833/100000000000000 : ℝ)^27
        have hw : |(2402306317/5000000000 : ℝ)|=(2402306317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-633482591/10000000000 : ℝ)|^35 ≤ (2797004140993/100000000000000 : ℝ)^27
        have hw : |(-633482591/10000000000 : ℝ)|=(633482591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s0_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-138616701/5000000000 : ℝ)*x 0 + (2088366369/2500000000 : ℝ)*x 1 + (358981157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138616701/5000000000 : ℝ)^35 ≤ (19164454193/2000000000000 : ℝ)^27 := by
    have hnat : (138616701 : ℕ)^35*2000000000000^27 ≤ 19164454193^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138616701 5000000000 19164454193 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088366369/2500000000 : ℝ)^35 ≤ (7919833826281/10000000000000 : ℝ)^27 := by
    have hnat : (2088366369 : ℕ)^35*10000000000000^27 ≤ 7919833826281^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088366369 2500000000 7919833826281 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (358981157/1250000000 : ℝ)^35 ≤ (3968687802001/20000000000000 : ℝ)^27 := by
    have hnat : (358981157 : ℕ)^35*20000000000000^27 ≤ 3968687802001^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358981157 1250000000 3968687802001 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-138616701/5000000000 : ℝ), (2088366369/2500000000 : ℝ), (358981157/1250000000 : ℝ)] ![(19164454193/2000000000000 : ℝ), (7919833826281/10000000000000 : ℝ), (3968687802001/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-138616701/5000000000 : ℝ)|^35 ≤ (19164454193/2000000000000 : ℝ)^27
        have hw : |(-138616701/5000000000 : ℝ)|=(138616701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2088366369/2500000000 : ℝ)|^35 ≤ (7919833826281/10000000000000 : ℝ)^27
        have hw : |(2088366369/2500000000 : ℝ)|=(2088366369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(358981157/1250000000 : ℝ)|^35 ≤ (3968687802001/20000000000000 : ℝ)^27
        have hw : |(358981157/1250000000 : ℝ)|=(358981157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2582592893/5000000000 : ℝ)*x 0 + (3824344517/10000000000 : ℝ)*x 1 + (3824344547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2582592893/5000000000 : ℝ)^35 ≤ (21234614465487/50000000000000 : ℝ)^27 := by
    have hnat : (2582592893 : ℕ)^35*50000000000000^27 ≤ 21234614465487^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582592893 5000000000 21234614465487 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3824344517/10000000000 : ℝ)^35 ≤ (28765385374191/100000000000000 : ℝ)^27 := by
    have hnat : (3824344517 : ℕ)^35*100000000000000^27 ≤ 28765385374191^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3824344517 10000000000 28765385374191 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3824344547/10000000000 : ℝ)^35 ≤ (287653856667/1000000000000 : ℝ)^27 := by
    have hnat : (3824344547 : ℕ)^35*1000000000000^27 ≤ 287653856667^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3824344547 10000000000 287653856667 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2582592893/5000000000 : ℝ), (3824344517/10000000000 : ℝ), (3824344547/10000000000 : ℝ)] ![(21234614465487/50000000000000 : ℝ), (28765385374191/100000000000000 : ℝ), (287653856667/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2582592893/5000000000 : ℝ)|^35 ≤ (21234614465487/50000000000000 : ℝ)^27
        have hw : |(-2582592893/5000000000 : ℝ)|=(2582592893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3824344517/10000000000 : ℝ)|^35 ≤ (28765385374191/100000000000000 : ℝ)^27
        have hw : |(3824344517/10000000000 : ℝ)|=(3824344517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3824344547/10000000000 : ℝ)|^35 ≤ (287653856667/1000000000000 : ℝ)^27
        have hw : |(3824344547/10000000000 : ℝ)|=(3824344547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2217615619/5000000000 : ℝ)*x 0 + (-3088456293/10000000000 : ℝ)*x 1 + (5246451733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2217615619/5000000000 : ℝ)^35 ≤ (34857711019853/100000000000000 : ℝ)^27 := by
    have hnat : (2217615619 : ℕ)^35*100000000000000^27 ≤ 34857711019853^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217615619 5000000000 34857711019853 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3088456293/10000000000 : ℝ)^35 ≤ (2725610270587/12500000000000 : ℝ)^27 := by
    have hnat : (3088456293 : ℕ)^35*12500000000000^27 ≤ 2725610270587^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3088456293 10000000000 2725610270587 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246451733/10000000000 : ℝ)^35 ≤ (21668703404209/50000000000000 : ℝ)^27 := by
    have hnat : (5246451733 : ℕ)^35*50000000000000^27 ≤ 21668703404209^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246451733 10000000000 21668703404209 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2217615619/5000000000 : ℝ), (-3088456293/10000000000 : ℝ), (5246451733/10000000000 : ℝ)] ![(34857711019853/100000000000000 : ℝ), (2725610270587/12500000000000 : ℝ), (21668703404209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2217615619/5000000000 : ℝ)|^35 ≤ (34857711019853/100000000000000 : ℝ)^27
        have hw : |(2217615619/5000000000 : ℝ)|=(2217615619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3088456293/10000000000 : ℝ)|^35 ≤ (2725610270587/12500000000000 : ℝ)^27
        have hw : |(-3088456293/10000000000 : ℝ)|=(3088456293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246451733/10000000000 : ℝ)|^35 ≤ (21668703404209/50000000000000 : ℝ)^27
        have hw : |(5246451733/10000000000 : ℝ)|=(5246451733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2242620709/5000000000 : ℝ)*x 0 + (5154157973/10000000000 : ℝ)*x 1 + (-1570132603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2242620709/5000000000 : ℝ)^35 ≤ (35368061184581/100000000000000 : ℝ)^27 := by
    have hnat : (2242620709 : ℕ)^35*100000000000000^27 ≤ 35368061184581^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242620709 5000000000 35368061184581 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5154157973/10000000000 : ℝ)^35 ≤ (4235172709731/10000000000000 : ℝ)^27 := by
    have hnat : (5154157973 : ℕ)^35*10000000000000^27 ≤ 4235172709731^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5154157973 10000000000 4235172709731 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1570132603/5000000000 : ℝ)^35 ≤ (22280211702679/100000000000000 : ℝ)^27 := by
    have hnat : (1570132603 : ℕ)^35*100000000000000^27 ≤ 22280211702679^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570132603 5000000000 22280211702679 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2242620709/5000000000 : ℝ), (5154157973/10000000000 : ℝ), (-1570132603/5000000000 : ℝ)] ![(35368061184581/100000000000000 : ℝ), (4235172709731/10000000000000 : ℝ), (22280211702679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2242620709/5000000000 : ℝ)|^35 ≤ (35368061184581/100000000000000 : ℝ)^27
        have hw : |(2242620709/5000000000 : ℝ)|=(2242620709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5154157973/10000000000 : ℝ)|^35 ≤ (4235172709731/10000000000000 : ℝ)^27
        have hw : |(5154157973/10000000000 : ℝ)|=(5154157973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1570132603/5000000000 : ℝ)|^35 ≤ (22280211702679/100000000000000 : ℝ)^27
        have hw : |(-1570132603/5000000000 : ℝ)|=(1570132603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308027_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (684544243/5000000000 : ℝ)*x 0 + (2832356681/5000000000 : ℝ)*x 1 + (5358077533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (684544243/5000000000 : ℝ)^35 ≤ (474722037123/6250000000000 : ℝ)^27 := by
    have hnat : (684544243 : ℕ)^35*6250000000000^27 ≤ 474722037123^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684544243 5000000000 474722037123 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2832356681/5000000000 : ℝ)^35 ≤ (47868021422953/100000000000000 : ℝ)^27 := by
    have hnat : (2832356681 : ℕ)^35*100000000000000^27 ≤ 47868021422953^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832356681 5000000000 47868021422953 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5358077533/10000000000 : ℝ)^35 ≤ (44536425975043/100000000000000 : ℝ)^27 := by
    have hnat : (5358077533 : ℕ)^35*100000000000000^27 ≤ 44536425975043^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358077533 10000000000 44536425975043 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(684544243/5000000000 : ℝ), (2832356681/5000000000 : ℝ), (5358077533/10000000000 : ℝ)] ![(474722037123/6250000000000 : ℝ), (47868021422953/100000000000000 : ℝ), (44536425975043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(684544243/5000000000 : ℝ)|^35 ≤ (474722037123/6250000000000 : ℝ)^27
        have hw : |(684544243/5000000000 : ℝ)|=(684544243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2832356681/5000000000 : ℝ)|^35 ≤ (47868021422953/100000000000000 : ℝ)^27
        have hw : |(2832356681/5000000000 : ℝ)|=(2832356681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5358077533/10000000000 : ℝ)|^35 ≤ (44536425975043/100000000000000 : ℝ)^27
        have hw : |(5358077533/10000000000 : ℝ)|=(5358077533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308027 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((2199043317/5000000000 : ℝ)*X 1 0+(-358768081/2500000000 : ℝ)*X 1 1+(6520649067/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1036098281/2500000000 : ℝ)*X 2 0+(81939371/125000000 : ℝ)*X 2 1+(-26926041/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((-29512831/1250000000 : ℝ)*X 0 0+(6465897161/10000000000 : ℝ)*X 0 1+(2579324129/5000000000 : ℝ)*X 0 2+(-29512831/1250000000 : ℝ)*X 1 0+(6465897161/10000000000 : ℝ)*X 1 1+(2579324129/5000000000 : ℝ)*X 1 2+(-29512831/1250000000 : ℝ)*X 2 0+(6465897161/10000000000 : ℝ)*X 2 1+(2579324129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2631051851/5000000000 : ℝ)*X 0 0+(1265177467/5000000000 : ℝ)*X 0 1+(4899068451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3809604159/10000000000 : ℝ)*X 1 0+(-93693939/10000000000 : ℝ)*X 1 1+(7690110481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2266843189/10000000000 : ℝ)*X 2 0+(396337503/500000000 : ℝ)*X 2 1+(-1873094573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-83566843/10000000000 : ℝ)*X 0 0+(1000581047/1250000000 : ℝ)*X 0 1+(683430181/2000000000 : ℝ)*X 0 2+(-83566843/10000000000 : ℝ)*X 1 0+(1000581047/1250000000 : ℝ)*X 1 1+(683430181/2000000000 : ℝ)*X 1 2+(-83566843/10000000000 : ℝ)*X 2 0+(1000581047/1250000000 : ℝ)*X 2 1+(683430181/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-603105411/1000000000 : ℝ)*X 0 0+(2210976361/10000000000 : ℝ)*X 0 1+(4345200109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((9660091/15625000 : ℝ)*X 1 0+(-28022743/2500000000 : ℝ)*X 1 1+(5501617947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((88457473/250000000 : ℝ)*X 2 0+(255483213/400000000 : ℝ)*X 2 1+(-2671310397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-72791441/2500000000 : ℝ)*X 0 0+(4152338179/10000000000 : ℝ)*X 0 1+(1468037847/2000000000 : ℝ)*X 0 2+(-72791441/2500000000 : ℝ)*X 1 0+(4152338179/10000000000 : ℝ)*X 1 1+(1468037847/2000000000 : ℝ)*X 1 2+(-72791441/2500000000 : ℝ)*X 2 0+(4152338179/10000000000 : ℝ)*X 2 1+(1468037847/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1286518537/2000000000 : ℝ)*X 0 0+(3294973857/10000000000 : ℝ)*X 0 1+(358981157/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((413399947/1000000000 : ℝ)*X 1 0+(-1184805937/10000000000 : ℝ)*X 1 1+(863213637/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((6615859753/10000000000 : ℝ)*X 2 0+(2402306317/5000000000 : ℝ)*X 2 1+(-633482591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((-138616701/5000000000 : ℝ)*X 0 0+(2088366369/2500000000 : ℝ)*X 0 1+(358981157/1250000000 : ℝ)*X 0 2+(-138616701/5000000000 : ℝ)*X 1 0+(2088366369/2500000000 : ℝ)*X 1 1+(358981157/1250000000 : ℝ)*X 1 2+(-138616701/5000000000 : ℝ)*X 2 0+(2088366369/2500000000 : ℝ)*X 2 1+(358981157/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((67501/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67501/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1659500311012270902753/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (659134673997/1000000000000 : ℝ)*(base7) + (98568409783/500000000000 : ℝ)*(base39) + (2623012923/6250000000 : ℝ)*(base50) + (10229557/1000000000000 : ℝ)*(base53) + (7873356289/100000000000 : ℝ)*(base60) + (960026093667/500000000000 : ℝ)*(major_s0_0) + (960026093667/500000000000 : ℝ)*(major_s0_1) + (960020978889/500000000000 : ℝ)*(major_s0_2) + (2560761/500000000000 : ℝ)*(sp_s0_6) + (221000697763/100000000000 : ℝ)*(sp_s0_7) + (1104982142159/500000000000 : ℝ)*(sp_s0_8) + (2210017207187/1000000000000 : ℝ)*(sp_s0_9) + (942174033831/500000000000 : ℝ)*(sp_s0_13) + (667083/15625000000 : ℝ)*(sp_s0_22) + (1225218515187/1000000000000 : ℝ)*(f.failure) + (2210017207187/1000000000000 : ℝ)*(f.sum) + (1174922479418397/1250000000000000000000000000 : ℝ)*base63 + (22029908569107/625000000000000000000000000 : ℝ)*base65 + (497542233273321/625000000000000000000000000 : ℝ)*base67 + (1853292545384353/5000000000000000000000000000 : ℝ)*base68 + (548779143898983/1000000000000000000000000000 : ℝ)*base71 + (151495247023321/625000000000000000000000000 : ℝ)*base73 + (61561278442059/5000000000000000000000000000 : ℝ)*base74 + (3235426319057941/5000000000000000000000000000 : ℝ)*base76 + (163977895679571/312500000000000000000000000 : ℝ)*base79 + (69957/100000000000000000 : ℝ)*base87 + (69957/100000000000000000 : ℝ)*base89 + (30043/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(77113/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(77113/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2932063578722976212499/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (573337261359/500000000000 : ℝ)*(base1) + (50251092233/50000000000 : ℝ)*(base7) + (112749881857/500000000000 : ℝ)*(base40) + (685389/250000000000 : ℝ)*(base50) + (2570291/200000000000 : ℝ)*(base54) + (15053899973/40000000000 : ℝ)*(base60) + (1092589683003/500000000000 : ℝ)*(major_s0_0) + (1092589683003/500000000000 : ℝ)*(major_s0_1) + (2185166514551/1000000000000 : ℝ)*(major_s0_2) + (24642887/250000000000 : ℝ)*(sp_s0_2) + (3505302995829/1000000000000 : ℝ)*(sp_s0_14) + (2358628473111/1000000000000 : ℝ)*(sp_s0_15) + (589629262527/250000000000 : ℝ)*(sp_s0_16) + (250547044949/200000000000 : ℝ)*(sp_s0_20) + (697200377129/500000000000 : ℝ)*(f.failure) + (2358628473111/1000000000000 : ℝ)*(f.sum) + (8909802243431589/10000000000000000000000000000 : ℝ)*base62 + (390344190721387/1250000000000000000000000000 : ℝ)*base64 + (110684261620111/625000000000000000000000000 : ℝ)*base66 + (2956278117114527/10000000000000000000000000000 : ℝ)*base68 + (2678542704227017/5000000000000000000000000000 : ℝ)*base70 + (16132871370111/625000000000000000000000000 : ℝ)*base72 + (681552544158531/5000000000000000000000000000 : ℝ)*base74 + (253526569341469/5000000000000000000000000000 : ℝ)*base76 + (80556210838861/312500000000000000000000000 : ℝ)*base78 + (37281/50000000000000000 : ℝ)*base86 + (37281/50000000000000000 : ℝ)*base88 + (37281/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(20471/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(20471/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (409797369791859/39062500000000000000 : ℝ) := by norm_num
    linear_combination (682838910261/1000000000000 : ℝ)*(base1) + (171848932267/200000000000 : ℝ)*(base7) + (13118363049/1000000000000 : ℝ)*(base39) + (128915251913/250000000000 : ℝ)*(base44) + (305198485379/1000000000000 : ℝ)*(base50) + (1133543/500000000000 : ℝ)*(base60) + (520686731349/250000000000 : ℝ)*(major_s0_0) + (97942869859/62500000000 : ℝ)*(major_s0_1) + (520686731349/250000000000 : ℝ)*(major_s0_2) + (12839679/125000000000 : ℝ)*(sp_s0_1) + (2991509981379/1000000000000 : ℝ)*(sp_s0_21) + (896453673017/500000000000 : ℝ)*(sp_s0_22) + (1154335535559/500000000000 : ℝ)*(sp_s0_23) + (989781585377/1000000000000 : ℝ)*(sp_s0_27) + (265807368391/200000000000 : ℝ)*(f.failure) + (1154335535559/500000000000 : ℝ)*(f.sum) + (15165837184789/500000000000000000000000000 : ℝ)*base62 + (208800836295663/312500000000000000000000000 : ℝ)*base64 + (8566103281783/78125000000000000000000000 : ℝ)*base66 + (1512012181009773/2500000000000000000000000000 : ℝ)*base68 + (955264180605531/2500000000000000000000000000 : ℝ)*base70 + (69044867923087/312500000000000000000000000 : ℝ)*base73 + (20297637333957/625000000000000000000000000 : ℝ)*base75 + (631160963490227/2500000000000000000000000000 : ℝ)*base76 + (39566100221691/62500000000000000000000000 : ℝ)*base79 + (2001/20000000000000000 : ℝ)*base87 + (2001/20000000000000000 : ℝ)*base89 + (2001/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (67501/100000 : ℝ) ^ (17/4 : ℝ) ≤ (4704444912670510541/25000000000000000000 : ℝ) := by
    have hpowers : (67501/100000 : ℝ)^17 ≤ (4704444912670510541/25000000000000000000 : ℝ)^4 := by
      have hnat : (67501 : ℕ)^17*25000000000000000000^4 ≤ 4704444912670510541^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67501 100000 4704444912670510541 25000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67501/100000 : ℝ)) (X := (4704444912670510541/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (29704444912670510541/25000000000000000000 : ℝ) ≤ (1041403806061381/1000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (29704444912670510541/25000000000000000000 : ℝ)^4 ≤ (1041403806061381/1000000000000000 : ℝ)^17 := by
      have hnat : (29704444912670510541 : ℕ)^4*1000000000000000^17 ≤ 1041403806061381^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29704444912670510541 25000000000000000000 1041403806061381 1000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1041403806061381/1000000000000000 : ℝ)) (X := (29704444912670510541/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (17204444912670510541/12500000000000000000 : ℝ) ≤ (2695147355982477/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (17204444912670510541/12500000000000000000 : ℝ)^4 ≤ (2695147355982477/2500000000000000 : ℝ)^17 := by
      have hnat : (17204444912670510541 : ℕ)^4*2500000000000000^17 ≤ 2695147355982477^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17204444912670510541 12500000000000000000 2695147355982477 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2695147355982477/2500000000000000 : ℝ)) (X := (17204444912670510541/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(41403806061381/675010000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(183275681658049/3375050000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (67501/100000 : ℝ)) (alpha := (41403806061381/675010000000000 : ℝ)) (beta := (183275681658049/3375050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (67501/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(41403806061381/675010000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(183275681658049/3375050000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (77113/100000 : ℝ) ^ (17/4 : ℝ) ≤ (2070962877064675641/6250000000000000000 : ℝ) := by
    have hpowers : (77113/100000 : ℝ)^17 ≤ (2070962877064675641/6250000000000000000 : ℝ)^4 := by
      have hnat : (77113 : ℕ)^17*6250000000000000000^4 ≤ 2070962877064675641^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77113 100000 2070962877064675641 6250000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77113/100000 : ℝ)) (X := (2070962877064675641/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (8320962877064675641/6250000000000000000 : ℝ) ≤ (10696594817024583/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (8320962877064675641/6250000000000000000 : ℝ)^4 ≤ (10696594817024583/10000000000000000 : ℝ)^17 := by
      have hnat : (8320962877064675641 : ℕ)^4*10000000000000000^17 ≤ 10696594817024583^17*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8320962877064675641 6250000000000000000 10696594817024583 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10696594817024583/10000000000000000 : ℝ)) (X := (8320962877064675641/6250000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5195962877064675641/3125000000000000000 : ℝ) ≤ (11270851041970099/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (5195962877064675641/3125000000000000000 : ℝ)^4 ≤ (11270851041970099/10000000000000000 : ℝ)^17 := by
      have hnat : (5195962877064675641 : ℕ)^4*10000000000000000^17 ≤ 11270851041970099^17*3125000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5195962877064675641 3125000000000000000 11270851041970099 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11270851041970099/10000000000000000 : ℝ)) (X := (5195962877064675641/3125000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(696594817024583/7711300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(143564056236379/1927825000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (77113/100000 : ℝ)) (alpha := (696594817024583/7711300000000000 : ℝ)) (beta := (143564056236379/1927825000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (77113/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(696594817024583/7711300000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(143564056236379/1927825000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (20471/25000 : ℝ) ^ (17/4 : ℝ) ≤ (42765737006132059353/100000000000000000000 : ℝ) := by
    have hpowers : (20471/25000 : ℝ)^17 ≤ (42765737006132059353/100000000000000000000 : ℝ)^4 := by
      have hnat : (20471 : ℕ)^17*100000000000000000000^4 ≤ 42765737006132059353^4*25000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20471 25000 42765737006132059353 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20471/25000 : ℝ)) (X := (42765737006132059353/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (142765737006132059353/100000000000000000000 : ℝ) ≤ (2174763880118757/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (142765737006132059353/100000000000000000000 : ℝ)^4 ≤ (2174763880118757/2000000000000000 : ℝ)^17 := by
      have hnat : (142765737006132059353 : ℕ)^4*2000000000000000^17 ≤ 2174763880118757^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        142765737006132059353 100000000000000000000 2174763880118757 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2174763880118757/2000000000000000 : ℝ)) (X := (142765737006132059353/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (92765737006132059353/50000000000000000000 : ℝ) ≤ (11565304752547197/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (92765737006132059353/50000000000000000000 : ℝ)^4 ≤ (11565304752547197/10000000000000000 : ℝ)^17 := by
      have hnat : (92765737006132059353 : ℕ)^4*10000000000000000^17 ≤ 11565304752547197^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92765737006132059353 50000000000000000000 11565304752547197 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11565304752547197/10000000000000000 : ℝ)) (X := (92765737006132059353/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(174763880118757/1637680000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(172871337988353/2047100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (20471/25000 : ℝ)) (alpha := (174763880118757/1637680000000000 : ℝ)) (beta := (172871337988353/2047100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (20471/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(174763880118757/1637680000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(172871337988353/2047100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2582592893/5000000000 : ℝ)*X 0 0+(3824344517/10000000000 : ℝ)*X 0 1+(3824344547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2217615619/5000000000 : ℝ)*X 1 0+(-3088456293/10000000000 : ℝ)*X 1 1+(5246451733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2242620709/5000000000 : ℝ)*X 2 0+(5154157973/10000000000 : ℝ)*X 2 1+(-1570132603/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((684544243/5000000000 : ℝ)*X 0 0+(2832356681/5000000000 : ℝ)*X 0 1+(5358077533/10000000000 : ℝ)*X 0 2+(684544243/5000000000 : ℝ)*X 1 0+(2832356681/5000000000 : ℝ)*X 1 1+(5358077533/10000000000 : ℝ)*X 1 2+(684544243/5000000000 : ℝ)*X 2 0+(2832356681/5000000000 : ℝ)*X 2 1+(5358077533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308027_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-320133/50000 : ℝ) < ((-156711/100000 : ℝ)*P 0+(-156711/100000 : ℝ)*P 1+(-156711/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-320133/50000 : ℝ) < (-6802253190021253616017142922755762139/1065557436327230000000000000000000000 : ℝ) := by norm_num
    linear_combination (43979/1000000000000 : ℝ)*(base5) + (2321/15625000000 : ℝ)*(base8) + (119947/1000000000000 : ℝ)*(base15) + (303193/1000000000000 : ℝ)*(base23) + (90927/1000000000000 : ℝ)*(base39) + (66843075863/200000000000 : ℝ)*(base50) + (11503/500000000000 : ℝ)*(base59) + (63837533213/200000000000 : ℝ)*(base60) + (156711/100000 : ℝ)*(major_s1_0) + (156711/100000 : ℝ)*(major_s1_1) + (156711/100000 : ℝ)*(major_s1_2) + (425583360299/200000000000 : ℝ)*(sp_s1_0) + (2127916830091/1000000000000 : ℝ)*(sp_s1_1) + (265989586353/125000000000 : ℝ)*(sp_s1_2) + (999999956021/1000000000000 : ℝ)*(sp_s1_6) + (2127916950039/1000000000000 : ℝ)*(f.sum) + (503713004259160959/1973225278750000000000000000000 : ℝ)*base63 + (105020419361493/204710000000000000000000000 : ℝ)*base65 + (120788606761627/385565000000000000000000000 : ℝ)*base66 + (12306038949191/12794375000000000000000000 : ℝ)*base69 + (7050617149863451231/13818129710000000000000000000000 : ℝ)*base71 + (7290901456737/84376250000000000000000000 : ℝ)*base72 + (51185127542047/385565000000000000000000000 : ℝ)*base74 + (113546029756323/337505000000000000000000000 : ℝ)*base77 + (40308175925714049237/52052046130000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p008_b016 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 27 ≤ c.val) (hhi : c.val < 28)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=27 := by omega
  rcases hc with rfl
  · exact collision_c308027 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 27 ≤ c.val) (hhi : c.val < 28)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b016 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
