-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b019
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:49:21.665987+00:00
-- url     : https://prove2.me/submissions/f133f1d7-65c8-4db4-b886-dd4c028a4181

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
theorem collision_support_c322037_s0_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-817786977/10000000000 : ℝ)*x 0 + (-6883186943/10000000000 : ℝ)*x 1 + (4018016919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (817786977/10000000000 : ℝ)^21 ≤ (567153786979/12500000000000 : ℝ)^17 := by
    have hnat : (817786977 : ℕ)^21*12500000000000^17 ≤ 567153786979^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817786977 10000000000 567153786979 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6883186943/10000000000 : ℝ)^21 ≤ (63040899849659/100000000000000 : ℝ)^17 := by
    have hnat : (6883186943 : ℕ)^21*100000000000000^17 ≤ 63040899849659^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6883186943 10000000000 63040899849659 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4018016919/10000000000 : ℝ)^21 ≤ (16210934917337/50000000000000 : ℝ)^17 := by
    have hnat : (4018016919 : ℕ)^21*50000000000000^17 ≤ 16210934917337^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018016919 10000000000 16210934917337 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-817786977/10000000000 : ℝ), (-6883186943/10000000000 : ℝ), (4018016919/10000000000 : ℝ)] ![(567153786979/12500000000000 : ℝ), (63040899849659/100000000000000 : ℝ), (16210934917337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-817786977/10000000000 : ℝ)|^21 ≤ (567153786979/12500000000000 : ℝ)^17
        have hw : |(-817786977/10000000000 : ℝ)|=(817786977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6883186943/10000000000 : ℝ)|^21 ≤ (63040899849659/100000000000000 : ℝ)^17
        have hw : |(-6883186943/10000000000 : ℝ)|=(6883186943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4018016919/10000000000 : ℝ)|^21 ≤ (16210934917337/50000000000000 : ℝ)^17
        have hw : |(4018016919/10000000000 : ℝ)|=(4018016919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2463271071/5000000000 : ℝ)*x 0 + (-2999544089/10000000000 : ℝ)*x 1 + (-4343754793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2463271071/5000000000 : ℝ)^21 ≤ (10426515652469/25000000000000 : ℝ)^17 := by
    have hnat : (2463271071 : ℕ)^21*25000000000000^17 ≤ 10426515652469^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2463271071 5000000000 10426515652469 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2999544089/10000000000 : ℝ)^21 ≤ (22594848112609/100000000000000 : ℝ)^17 := by
    have hnat : (2999544089 : ℕ)^21*100000000000000^17 ≤ 22594848112609^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999544089 10000000000 22594848112609 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4343754793/10000000000 : ℝ)^21 ≤ (35699089259297/100000000000000 : ℝ)^17 := by
    have hnat : (4343754793 : ℕ)^21*100000000000000^17 ≤ 35699089259297^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343754793 10000000000 35699089259297 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2463271071/5000000000 : ℝ), (-2999544089/10000000000 : ℝ), (-4343754793/10000000000 : ℝ)] ![(10426515652469/25000000000000 : ℝ), (22594848112609/100000000000000 : ℝ), (35699089259297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2463271071/5000000000 : ℝ)|^21 ≤ (10426515652469/25000000000000 : ℝ)^17
        have hw : |(2463271071/5000000000 : ℝ)|=(2463271071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2999544089/10000000000 : ℝ)|^21 ≤ (22594848112609/100000000000000 : ℝ)^17
        have hw : |(-2999544089/10000000000 : ℝ)|=(2999544089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4343754793/10000000000 : ℝ)|^21 ≤ (35699089259297/100000000000000 : ℝ)^17
        have hw : |(-4343754793/10000000000 : ℝ)|=(4343754793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7939391609/10000000000 : ℝ)*x 0 + (-335450037/2500000000 : ℝ)*x 1 + (1159219939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7939391609/10000000000 : ℝ)^21 ≤ (75198252314269/100000000000000 : ℝ)^17 := by
    have hnat : (7939391609 : ℕ)^21*100000000000000^17 ≤ 75198252314269^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7939391609 10000000000 75198252314269 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335450037/2500000000 : ℝ)^21 ≤ (8364460110227/100000000000000 : ℝ)^17 := by
    have hnat : (335450037 : ℕ)^21*100000000000000^17 ≤ 8364460110227^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335450037 2500000000 8364460110227 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1159219939/5000000000 : ℝ)^21 ≤ (3287457513187/20000000000000 : ℝ)^17 := by
    have hnat : (1159219939 : ℕ)^21*20000000000000^17 ≤ 3287457513187^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159219939 5000000000 3287457513187 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7939391609/10000000000 : ℝ), (-335450037/2500000000 : ℝ), (1159219939/5000000000 : ℝ)] ![(75198252314269/100000000000000 : ℝ), (8364460110227/100000000000000 : ℝ), (3287457513187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7939391609/10000000000 : ℝ)|^21 ≤ (75198252314269/100000000000000 : ℝ)^17
        have hw : |(7939391609/10000000000 : ℝ)|=(7939391609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-335450037/2500000000 : ℝ)|^21 ≤ (8364460110227/100000000000000 : ℝ)^17
        have hw : |(-335450037/2500000000 : ℝ)|=(335450037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1159219939/5000000000 : ℝ)|^21 ≤ (3287457513187/20000000000000 : ℝ)^17
        have hw : |(1159219939/5000000000 : ℝ)|=(1159219939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-693387473/10000000000 : ℝ)*x 0 + (-250102281/312500000 : ℝ)*x 1 + (1378128611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (693387473/10000000000 : ℝ)^21 ≤ (1850267259857/50000000000000 : ℝ)^17 := by
    have hnat : (693387473 : ℕ)^21*50000000000000^17 ≤ 1850267259857^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693387473 10000000000 1850267259857 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250102281/312500000 : ℝ)^21 ≤ (75946379225693/100000000000000 : ℝ)^17 := by
    have hnat : (250102281 : ℕ)^21*100000000000000^17 ≤ 75946379225693^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250102281 312500000 75946379225693 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378128611/5000000000 : ℝ)^21 ≤ (20353086246839/100000000000000 : ℝ)^17 := by
    have hnat : (1378128611 : ℕ)^21*100000000000000^17 ≤ 20353086246839^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378128611 5000000000 20353086246839 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-693387473/10000000000 : ℝ), (-250102281/312500000 : ℝ), (1378128611/5000000000 : ℝ)] ![(1850267259857/50000000000000 : ℝ), (75946379225693/100000000000000 : ℝ), (20353086246839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-693387473/10000000000 : ℝ)|^21 ≤ (1850267259857/50000000000000 : ℝ)^17
        have hw : |(-693387473/10000000000 : ℝ)|=(693387473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-250102281/312500000 : ℝ)|^21 ≤ (75946379225693/100000000000000 : ℝ)^17
        have hw : |(-250102281/312500000 : ℝ)|=(250102281/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1378128611/5000000000 : ℝ)|^21 ≤ (20353086246839/100000000000000 : ℝ)^17
        have hw : |(1378128611/5000000000 : ℝ)|=(1378128611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (599614539/1250000000 : ℝ)*x 0 + (2877191811/10000000000 : ℝ)*x 1 + (4586882889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (599614539/1250000000 : ℝ)^21 ≤ (40354726696617/100000000000000 : ℝ)^17 := by
    have hnat : (599614539 : ℕ)^21*100000000000000^17 ≤ 40354726696617^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599614539 1250000000 40354726696617 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2877191811/10000000000 : ℝ)^21 ≤ (10730930070037/50000000000000 : ℝ)^17 := by
    have hnat : (2877191811 : ℕ)^21*50000000000000^17 ≤ 10730930070037^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2877191811 10000000000 10730930070037 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4586882889/10000000000 : ℝ)^21 ≤ (19091706572417/50000000000000 : ℝ)^17 := by
    have hnat : (4586882889 : ℕ)^21*50000000000000^17 ≤ 19091706572417^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4586882889 10000000000 19091706572417 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(599614539/1250000000 : ℝ), (2877191811/10000000000 : ℝ), (4586882889/10000000000 : ℝ)] ![(40354726696617/100000000000000 : ℝ), (10730930070037/50000000000000 : ℝ), (19091706572417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(599614539/1250000000 : ℝ)|^21 ≤ (40354726696617/100000000000000 : ℝ)^17
        have hw : |(599614539/1250000000 : ℝ)|=(599614539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2877191811/10000000000 : ℝ)|^21 ≤ (10730930070037/50000000000000 : ℝ)^17
        have hw : |(2877191811/10000000000 : ℝ)|=(2877191811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4586882889/10000000000 : ℝ)|^21 ≤ (19091706572417/50000000000000 : ℝ)^17
        have hw : |(4586882889/10000000000 : ℝ)|=(4586882889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4796918411/10000000000 : ℝ)*x 0 + (-38801181/156250000 : ℝ)*x 1 + (-246548973/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4796918411/10000000000 : ℝ)^21 ≤ (20177374254801/50000000000000 : ℝ)^17 := by
    have hnat : (4796918411 : ℕ)^21*50000000000000^17 ≤ 20177374254801^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796918411 10000000000 20177374254801 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38801181/156250000 : ℝ)^21 ≤ (17892780757259/100000000000000 : ℝ)^17 := by
    have hnat : (38801181 : ℕ)^21*100000000000000^17 ≤ 17892780757259^17*156250000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38801181 156250000 17892780757259 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246548973/500000000 : ℝ)^21 ≤ (41752470724197/100000000000000 : ℝ)^17 := by
    have hnat : (246548973 : ℕ)^21*100000000000000^17 ≤ 41752470724197^17*500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246548973 500000000 41752470724197 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4796918411/10000000000 : ℝ), (-38801181/156250000 : ℝ), (-246548973/500000000 : ℝ)] ![(20177374254801/50000000000000 : ℝ), (17892780757259/100000000000000 : ℝ), (41752470724197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4796918411/10000000000 : ℝ)|^21 ≤ (20177374254801/50000000000000 : ℝ)^17
        have hw : |(4796918411/10000000000 : ℝ)|=(4796918411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38801181/156250000 : ℝ)|^21 ≤ (17892780757259/100000000000000 : ℝ)^17
        have hw : |(-38801181/156250000 : ℝ)|=(38801181/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246548973/500000000 : ℝ)|^21 ≤ (41752470724197/100000000000000 : ℝ)^17
        have hw : |(-246548973/500000000 : ℝ)|=(246548973/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (378637331/500000000 : ℝ)*x 0 + (-380385497/10000000000 : ℝ)*x 1 + (3496463097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (378637331/500000000 : ℝ)^21 ≤ (70932042755753/100000000000000 : ℝ)^17 := by
    have hnat : (378637331 : ℕ)^21*100000000000000^17 ≤ 70932042755753^17*500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378637331 500000000 70932042755753 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (380385497/10000000000 : ℝ)^21 ≤ (881310616189/50000000000000 : ℝ)^17 := by
    have hnat : (380385497 : ℕ)^21*50000000000000^17 ≤ 881310616189^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380385497 10000000000 881310616189 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3496463097/10000000000 : ℝ)^21 ≤ (5461067200987/20000000000000 : ℝ)^17 := by
    have hnat : (3496463097 : ℕ)^21*20000000000000^17 ≤ 5461067200987^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3496463097 10000000000 5461067200987 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(378637331/500000000 : ℝ), (-380385497/10000000000 : ℝ), (3496463097/10000000000 : ℝ)] ![(70932042755753/100000000000000 : ℝ), (881310616189/50000000000000 : ℝ), (5461067200987/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(378637331/500000000 : ℝ)|^21 ≤ (70932042755753/100000000000000 : ℝ)^17
        have hw : |(378637331/500000000 : ℝ)|=(378637331/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-380385497/10000000000 : ℝ)|^21 ≤ (881310616189/50000000000000 : ℝ)^17
        have hw : |(-380385497/10000000000 : ℝ)|=(380385497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3496463097/10000000000 : ℝ)|^21 ≤ (5461067200987/20000000000000 : ℝ)^17
        have hw : |(3496463097/10000000000 : ℝ)|=(3496463097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-152293787/10000000000 : ℝ)*x 0 + (-6697642353/10000000000 : ℝ)*x 1 + (1153989743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (152293787/10000000000 : ℝ)^21 ≤ (71119387493/12500000000000 : ℝ)^17 := by
    have hnat : (152293787 : ℕ)^21*12500000000000^17 ≤ 71119387493^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152293787 10000000000 71119387493 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6697642353/10000000000 : ℝ)^21 ≤ (6094841450381/10000000000000 : ℝ)^17 := by
    have hnat : (6697642353 : ℕ)^21*10000000000000^17 ≤ 6094841450381^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6697642353 10000000000 6094841450381 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1153989743/2500000000 : ℝ)^21 ≤ (38482630379761/100000000000000 : ℝ)^17 := by
    have hnat : (1153989743 : ℕ)^21*100000000000000^17 ≤ 38482630379761^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153989743 2500000000 38482630379761 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-152293787/10000000000 : ℝ), (-6697642353/10000000000 : ℝ), (1153989743/2500000000 : ℝ)] ![(71119387493/12500000000000 : ℝ), (6094841450381/10000000000000 : ℝ), (38482630379761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-152293787/10000000000 : ℝ)|^21 ≤ (71119387493/12500000000000 : ℝ)^17
        have hw : |(-152293787/10000000000 : ℝ)|=(152293787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6697642353/10000000000 : ℝ)|^21 ≤ (6094841450381/10000000000000 : ℝ)^17
        have hw : |(-6697642353/10000000000 : ℝ)|=(6697642353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1153989743/2500000000 : ℝ)|^21 ≤ (38482630379761/100000000000000 : ℝ)^17
        have hw : |(1153989743/2500000000 : ℝ)|=(1153989743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4611359897/10000000000 : ℝ)*x 0 + (784494527/2500000000 : ℝ)*x 1 + (907472081/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4611359897/10000000000 : ℝ)^21 ≤ (19217636222647/50000000000000 : ℝ)^17 := by
    have hnat : (4611359897 : ℕ)^21*50000000000000^17 ≤ 19217636222647^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4611359897 10000000000 19217636222647 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (784494527/2500000000 : ℝ)^21 ≤ (4777982883947/20000000000000 : ℝ)^17 := by
    have hnat : (784494527 : ℕ)^21*20000000000000^17 ≤ 4777982883947^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784494527 2500000000 4777982883947 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (907472081/2000000000 : ℝ)^21 ≤ (941870327989/2500000000000 : ℝ)^17 := by
    have hnat : (907472081 : ℕ)^21*2500000000000^17 ≤ 941870327989^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907472081 2000000000 941870327989 2500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4611359897/10000000000 : ℝ), (784494527/2500000000 : ℝ), (907472081/2000000000 : ℝ)] ![(19217636222647/50000000000000 : ℝ), (4777982883947/20000000000000 : ℝ), (941870327989/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4611359897/10000000000 : ℝ)|^21 ≤ (19217636222647/50000000000000 : ℝ)^17
        have hw : |(4611359897/10000000000 : ℝ)|=(4611359897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(784494527/2500000000 : ℝ)|^21 ≤ (4777982883947/20000000000000 : ℝ)^17
        have hw : |(784494527/2500000000 : ℝ)|=(784494527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(907472081/2000000000 : ℝ)|^21 ≤ (941870327989/2500000000000 : ℝ)^17
        have hw : |(907472081/2000000000 : ℝ)|=(907472081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5618774517/10000000000 : ℝ)*x 0 + (-2652627857/10000000000 : ℝ)*x 1 + (-491003719/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5618774517/10000000000 : ℝ)^21 ≤ (12265175163161/25000000000000 : ℝ)^17 := by
    have hnat : (5618774517 : ℕ)^21*25000000000000^17 ≤ 12265175163161^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5618774517 10000000000 12265175163161 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2652627857/10000000000 : ℝ)^21 ≤ (19412021149253/100000000000000 : ℝ)^17 := by
    have hnat : (2652627857 : ℕ)^21*100000000000000^17 ≤ 19412021149253^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652627857 10000000000 19412021149253 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491003719/1250000000 : ℝ)^21 ≤ (7881819546727/25000000000000 : ℝ)^17 := by
    have hnat : (491003719 : ℕ)^21*25000000000000^17 ≤ 7881819546727^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491003719 1250000000 7881819546727 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5618774517/10000000000 : ℝ), (-2652627857/10000000000 : ℝ), (-491003719/1250000000 : ℝ)] ![(12265175163161/25000000000000 : ℝ), (19412021149253/100000000000000 : ℝ), (7881819546727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5618774517/10000000000 : ℝ)|^21 ≤ (12265175163161/25000000000000 : ℝ)^17
        have hw : |(5618774517/10000000000 : ℝ)|=(5618774517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2652627857/10000000000 : ℝ)|^21 ≤ (19412021149253/100000000000000 : ℝ)^17
        have hw : |(-2652627857/10000000000 : ℝ)|=(2652627857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491003719/1250000000 : ℝ)|^21 ≤ (7881819546727/25000000000000 : ℝ)^17
        have hw : |(-491003719/1250000000 : ℝ)|=(491003719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_17 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9999999871/10000000000 : ℝ)*x 0 + (691/2500000000 : ℝ)*x 1 + (691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9999999871/10000000000 : ℝ)^21 ≤ (99999998406471/100000000000000 : ℝ)^17 := by
    have hnat : (9999999871 : ℕ)^21*100000000000000^17 ≤ 99999998406471^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999871 10000000000 99999998406471 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (691/2500000000 : ℝ)^21 ≤ (395677/50000000000000 : ℝ)^17 := by
    have hnat : (691 : ℕ)^21*50000000000000^17 ≤ 395677^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691 2500000000 395677 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691/2500000000 : ℝ)^21 ≤ (395677/50000000000000 : ℝ)^17 := by
    have hnat : (691 : ℕ)^21*50000000000000^17 ≤ 395677^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691 2500000000 395677 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9999999871/10000000000 : ℝ), (691/2500000000 : ℝ), (691/2500000000 : ℝ)] ![(99999998406471/100000000000000 : ℝ), (395677/50000000000000 : ℝ), (395677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9999999871/10000000000 : ℝ)|^21 ≤ (99999998406471/100000000000000 : ℝ)^17
        have hw : |(9999999871/10000000000 : ℝ)|=(9999999871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(691/2500000000 : ℝ)|^21 ≤ (395677/50000000000000 : ℝ)^17
        have hw : |(691/2500000000 : ℝ)|=(691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(691/2500000000 : ℝ)|^21 ≤ (395677/50000000000000 : ℝ)^17
        have hw : |(691/2500000000 : ℝ)|=(691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4453166109/5000000000 : ℝ)*x 0 + (-104399169/1000000000 : ℝ)*x 1 + (593978853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4453166109/5000000000 : ℝ)^21 ≤ (541680688889/625000000000 : ℝ)^17 := by
    have hnat : (4453166109 : ℕ)^21*625000000000^17 ≤ 541680688889^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4453166109 5000000000 541680688889 625000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104399169/1000000000 : ℝ)^21 ≤ (3067412848689/50000000000000 : ℝ)^17 := by
    have hnat : (104399169 : ℕ)^21*50000000000000^17 ≤ 3067412848689^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104399169 1000000000 3067412848689 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (593978853/5000000000 : ℝ)^21 ≤ (1799066018231/25000000000000 : ℝ)^17 := by
    have hnat : (593978853 : ℕ)^21*25000000000000^17 ≤ 1799066018231^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593978853 5000000000 1799066018231 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4453166109/5000000000 : ℝ), (-104399169/1000000000 : ℝ), (593978853/5000000000 : ℝ)] ![(541680688889/625000000000 : ℝ), (3067412848689/50000000000000 : ℝ), (1799066018231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4453166109/5000000000 : ℝ)|^21 ≤ (541680688889/625000000000 : ℝ)^17
        have hw : |(4453166109/5000000000 : ℝ)|=(4453166109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104399169/1000000000 : ℝ)|^21 ≤ (3067412848689/50000000000000 : ℝ)^17
        have hw : |(-104399169/1000000000 : ℝ)|=(104399169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(593978853/5000000000 : ℝ)|^21 ≤ (1799066018231/25000000000000 : ℝ)^17
        have hw : |(593978853/5000000000 : ℝ)|=(593978853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-198070509/10000000000 : ℝ)*x 0 + (-1499845929/2000000000 : ℝ)*x 1 + (3684480841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198070509/10000000000 : ℝ)^21 ≤ (196793861743/25000000000000 : ℝ)^17 := by
    have hnat : (198070509 : ℕ)^21*25000000000000^17 ≤ 196793861743^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198070509 10000000000 196793861743 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1499845929/2000000000 : ℝ)^21 ≤ (70082374279911/100000000000000 : ℝ)^17 := by
    have hnat : (1499845929 : ℕ)^21*100000000000000^17 ≤ 70082374279911^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499845929 2000000000 70082374279911 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3684480841/10000000000 : ℝ)^21 ≤ (29130450250689/100000000000000 : ℝ)^17 := by
    have hnat : (3684480841 : ℕ)^21*100000000000000^17 ≤ 29130450250689^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3684480841 10000000000 29130450250689 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-198070509/10000000000 : ℝ), (-1499845929/2000000000 : ℝ), (3684480841/10000000000 : ℝ)] ![(196793861743/25000000000000 : ℝ), (70082374279911/100000000000000 : ℝ), (29130450250689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-198070509/10000000000 : ℝ)|^21 ≤ (196793861743/25000000000000 : ℝ)^17
        have hw : |(-198070509/10000000000 : ℝ)|=(198070509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1499845929/2000000000 : ℝ)|^21 ≤ (70082374279911/100000000000000 : ℝ)^17
        have hw : |(-1499845929/2000000000 : ℝ)|=(1499845929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3684480841/10000000000 : ℝ)|^21 ≤ (29130450250689/100000000000000 : ℝ)^17
        have hw : |(3684480841/10000000000 : ℝ)|=(3684480841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5572997763/10000000000 : ℝ)*x 0 + (559163667/2000000000 : ℝ)*x 1 + (3846205893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5572997763/10000000000 : ℝ)^21 ≤ (2428371221743/5000000000000 : ℝ)^17 := by
    have hnat : (5572997763 : ℕ)^21*5000000000000^17 ≤ 2428371221743^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5572997763 10000000000 2428371221743 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559163667/2000000000 : ℝ)^21 ≤ (5178640563721/25000000000000 : ℝ)^17 := by
    have hnat : (559163667 : ℕ)^21*25000000000000^17 ≤ 5178640563721^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559163667 2000000000 5178640563721 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3846205893/10000000000 : ℝ)^21 ≤ (15359006646103/50000000000000 : ℝ)^17 := by
    have hnat : (3846205893 : ℕ)^21*50000000000000^17 ≤ 15359006646103^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3846205893 10000000000 15359006646103 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5572997763/10000000000 : ℝ), (559163667/2000000000 : ℝ), (3846205893/10000000000 : ℝ)] ![(2428371221743/5000000000000 : ℝ), (5178640563721/25000000000000 : ℝ), (15359006646103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5572997763/10000000000 : ℝ)|^21 ≤ (2428371221743/5000000000000 : ℝ)^17
        have hw : |(5572997763/10000000000 : ℝ)|=(5572997763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559163667/2000000000 : ℝ)|^21 ≤ (5178640563721/25000000000000 : ℝ)^17
        have hw : |(559163667/2000000000 : ℝ)|=(559163667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3846205893/10000000000 : ℝ)|^21 ≤ (15359006646103/50000000000000 : ℝ)^17
        have hw : |(3846205893/10000000000 : ℝ)|=(3846205893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2300173127/5000000000 : ℝ)*x 0 + (-1531077519/5000000000 : ℝ)*x 1 + (-1154392343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2300173127/5000000000 : ℝ)^21 ≤ (958047678303/2500000000000 : ℝ)^17 := by
    have hnat : (2300173127 : ℕ)^21*2500000000000^17 ≤ 958047678303^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2300173127 5000000000 958047678303 2500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1531077519/5000000000 : ℝ)^21 ≤ (11589438560433/50000000000000 : ℝ)^17 := by
    have hnat : (1531077519 : ℕ)^21*50000000000000^17 ≤ 11589438560433^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531077519 5000000000 11589438560433 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1154392343/2500000000 : ℝ)^21 ≤ (38499215734617/100000000000000 : ℝ)^17 := by
    have hnat : (1154392343 : ℕ)^21*100000000000000^17 ≤ 38499215734617^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154392343 2500000000 38499215734617 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2300173127/5000000000 : ℝ), (-1531077519/5000000000 : ℝ), (-1154392343/2500000000 : ℝ)] ![(958047678303/2500000000000 : ℝ), (11589438560433/50000000000000 : ℝ), (38499215734617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2300173127/5000000000 : ℝ)|^21 ≤ (958047678303/2500000000000 : ℝ)^17
        have hw : |(2300173127/5000000000 : ℝ)|=(2300173127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1531077519/5000000000 : ℝ)|^21 ≤ (11589438560433/50000000000000 : ℝ)^17
        have hw : |(-1531077519/5000000000 : ℝ)|=(1531077519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1154392343/2500000000 : ℝ)|^21 ≤ (38499215734617/100000000000000 : ℝ)^17
        have hw : |(-1154392343/2500000000 : ℝ)|=(1154392343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s0_27 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8937828917/10000000000 : ℝ)*x 0 + (-399070453/10000000000 : ℝ)*x 1 + (1684999429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8937828917/10000000000 : ℝ)^21 ≤ (43523842192607/50000000000000 : ℝ)^17 := by
    have hnat : (8937828917 : ℕ)^21*50000000000000^17 ≤ 43523842192607^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8937828917 10000000000 43523842192607 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399070453/10000000000 : ℝ)^21 ≤ (935092927423/50000000000000 : ℝ)^17 := by
    have hnat : (399070453 : ℕ)^21*50000000000000^17 ≤ 935092927423^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399070453 10000000000 935092927423 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1684999429/10000000000 : ℝ)^21 ≤ (2216425949623/20000000000000 : ℝ)^17 := by
    have hnat : (1684999429 : ℕ)^21*20000000000000^17 ≤ 2216425949623^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684999429 10000000000 2216425949623 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8937828917/10000000000 : ℝ), (-399070453/10000000000 : ℝ), (1684999429/10000000000 : ℝ)] ![(43523842192607/50000000000000 : ℝ), (935092927423/50000000000000 : ℝ), (2216425949623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8937828917/10000000000 : ℝ)|^21 ≤ (43523842192607/50000000000000 : ℝ)^17
        have hw : |(8937828917/10000000000 : ℝ)|=(8937828917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-399070453/10000000000 : ℝ)|^21 ≤ (935092927423/50000000000000 : ℝ)^17
        have hw : |(-399070453/10000000000 : ℝ)|=(399070453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1684999429/10000000000 : ℝ)|^21 ≤ (2216425949623/20000000000000 : ℝ)^17
        have hw : |(1684999429/10000000000 : ℝ)|=(1684999429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108586583/10000000000 : ℝ)*x 0 + (-2825382077/5000000000 : ℝ)*x 1 + (4370871953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108586583/10000000000 : ℝ)^21 ≤ (14619435408537/100000000000000 : ℝ)^17 := by
    have hnat : (2108586583 : ℕ)^21*100000000000000^17 ≤ 14619435408537^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108586583 10000000000 14619435408537 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2825382077/5000000000 : ℝ)^21 ≤ (2470298666091/5000000000000 : ℝ)^17 := by
    have hnat : (2825382077 : ℕ)^21*5000000000000^17 ≤ 2470298666091^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2825382077 5000000000 2470298666091 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4370871953/10000000000 : ℝ)^21 ≤ (719491825181/2000000000000 : ℝ)^17 := by
    have hnat : (4370871953 : ℕ)^21*2000000000000^17 ≤ 719491825181^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370871953 10000000000 719491825181 2000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108586583/10000000000 : ℝ), (-2825382077/5000000000 : ℝ), (4370871953/10000000000 : ℝ)] ![(14619435408537/100000000000000 : ℝ), (2470298666091/5000000000000 : ℝ), (719491825181/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108586583/10000000000 : ℝ)|^21 ≤ (14619435408537/100000000000000 : ℝ)^17
        have hw : |(-2108586583/10000000000 : ℝ)|=(2108586583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2825382077/5000000000 : ℝ)|^21 ≤ (2470298666091/5000000000000 : ℝ)^17
        have hw : |(-2825382077/5000000000 : ℝ)|=(2825382077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4370871953/10000000000 : ℝ)|^21 ≤ (719491825181/2000000000000 : ℝ)^17
        have hw : |(4370871953/10000000000 : ℝ)|=(4370871953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1179910719/2500000000 : ℝ)*x 0 + (136113939/400000000 : ℝ)*x 1 + (2089881457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1179910719/2500000000 : ℝ)^21 ≤ (39553222850427/100000000000000 : ℝ)^17 := by
    have hnat : (1179910719 : ℕ)^21*100000000000000^17 ≤ 39553222850427^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179910719 2500000000 39553222850427 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136113939/400000000 : ℝ)^21 ≤ (26405106963219/100000000000000 : ℝ)^17 := by
    have hnat : (136113939 : ℕ)^21*100000000000000^17 ≤ 26405106963219^17*400000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136113939 400000000 26405106963219 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089881457/5000000000 : ℝ)^21 ≤ (4255208772319/12500000000000 : ℝ)^17 := by
    have hnat : (2089881457 : ℕ)^21*12500000000000^17 ≤ 4255208772319^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089881457 5000000000 4255208772319 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1179910719/2500000000 : ℝ), (136113939/400000000 : ℝ), (2089881457/5000000000 : ℝ)] ![(39553222850427/100000000000000 : ℝ), (26405106963219/100000000000000 : ℝ), (4255208772319/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1179910719/2500000000 : ℝ)|^21 ≤ (39553222850427/100000000000000 : ℝ)^17
        have hw : |(1179910719/2500000000 : ℝ)|=(1179910719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136113939/400000000 : ℝ)|^21 ≤ (26405106963219/100000000000000 : ℝ)^17
        have hw : |(136113939/400000000 : ℝ)|=(136113939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2089881457/5000000000 : ℝ)|^21 ≤ (4255208772319/12500000000000 : ℝ)^17
        have hw : |(2089881457/5000000000 : ℝ)|=(2089881457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4704210547/10000000000 : ℝ)*x 0 + (-3410124551/10000000000 : ℝ)*x 1 + (-4188700213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4704210547/10000000000 : ℝ)^21 ≤ (39393521956329/100000000000000 : ℝ)^17 := by
    have hnat : (4704210547 : ℕ)^21*100000000000000^17 ≤ 39393521956329^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4704210547 10000000000 39393521956329 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3410124551/10000000000 : ℝ)^21 ≤ (5294973894609/20000000000000 : ℝ)^17 := by
    have hnat : (3410124551 : ℕ)^21*20000000000000^17 ≤ 5294973894609^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3410124551 10000000000 5294973894609 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4188700213/10000000000 : ℝ)^21 ≤ (34131608556093/100000000000000 : ℝ)^17 := by
    have hnat : (4188700213 : ℕ)^21*100000000000000^17 ≤ 34131608556093^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4188700213 10000000000 34131608556093 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4704210547/10000000000 : ℝ), (-3410124551/10000000000 : ℝ), (-4188700213/10000000000 : ℝ)] ![(39393521956329/100000000000000 : ℝ), (5294973894609/20000000000000 : ℝ), (34131608556093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4704210547/10000000000 : ℝ)|^21 ≤ (39393521956329/100000000000000 : ℝ)^17
        have hw : |(4704210547/10000000000 : ℝ)|=(4704210547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3410124551/10000000000 : ℝ)|^21 ≤ (5294973894609/20000000000000 : ℝ)^17
        have hw : |(-3410124551/10000000000 : ℝ)|=(3410124551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4188700213/10000000000 : ℝ)|^21 ≤ (34131608556093/100000000000000 : ℝ)^17
        have hw : |(-4188700213/10000000000 : ℝ)|=(4188700213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322037_s1_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1515130897/2500000000 : ℝ)*x 0 + (-1716487377/5000000000 : ℝ)*x 1 + (531081909/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1515130897/2500000000 : ℝ)^21 ≤ (10773729273277/20000000000000 : ℝ)^17 := by
    have hnat : (1515130897 : ℕ)^21*20000000000000^17 ≤ 10773729273277^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1515130897 2500000000 10773729273277 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1716487377/5000000000 : ℝ)^21 ≤ (26694183124897/100000000000000 : ℝ)^17 := by
    have hnat : (1716487377 : ℕ)^21*100000000000000^17 ≤ 26694183124897^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716487377 5000000000 26694183124897 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531081909/2000000000 : ℝ)^21 ≤ (4859292625057/25000000000000 : ℝ)^17 := by
    have hnat : (531081909 : ℕ)^21*25000000000000^17 ≤ 4859292625057^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531081909 2000000000 4859292625057 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1515130897/2500000000 : ℝ), (-1716487377/5000000000 : ℝ), (531081909/2000000000 : ℝ)] ![(10773729273277/20000000000000 : ℝ), (26694183124897/100000000000000 : ℝ), (4859292625057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1515130897/2500000000 : ℝ)|^21 ≤ (10773729273277/20000000000000 : ℝ)^17
        have hw : |(1515130897/2500000000 : ℝ)|=(1515130897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1716487377/5000000000 : ℝ)|^21 ≤ (26694183124897/100000000000000 : ℝ)^17
        have hw : |(-1716487377/5000000000 : ℝ)|=(1716487377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531081909/2000000000 : ℝ)|^21 ≤ (4859292625057/25000000000000 : ℝ)^17
        have hw : |(531081909/2000000000 : ℝ)|=(531081909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322037 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188503781428927/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (41/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^41 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^41*1^8 ≤ 1^8*1^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2862052320966567/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2862052320966567/2500000000000000 : ℝ)^41 := by
      have hnat : (2 : ℕ)^8*2500000000000000^41 ≤ 2862052320966567^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2862052320966567 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2862052320966567/2500000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12390728191010903/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (12390728191010903/10000000000000000 : ℝ)^41 := by
      have hnat : (3 : ℕ)^8*10000000000000000^41 ≤ 12390728191010903^41*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12390728191010903 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12390728191010903/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (362052320966567/2500000000000000 : ℝ)) (beta := (188503781428927/2000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(362052320966567/2500000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(188503781428927/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-817786977/10000000000 : ℝ)*X 0 0+(-6883186943/10000000000 : ℝ)*X 0 1+(4018016919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2463271071/5000000000 : ℝ)*X 2 0+(-2999544089/10000000000 : ℝ)*X 2 1+(-4343754793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((7939391609/10000000000 : ℝ)*X 0 0+(-335450037/2500000000 : ℝ)*X 0 1+(1159219939/5000000000 : ℝ)*X 0 2+(7939391609/10000000000 : ℝ)*X 1 0+(-335450037/2500000000 : ℝ)*X 1 1+(1159219939/5000000000 : ℝ)*X 1 2+(7939391609/10000000000 : ℝ)*X 2 0+(-335450037/2500000000 : ℝ)*X 2 1+(1159219939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-693387473/10000000000 : ℝ)*X 0 0+(-250102281/312500000 : ℝ)*X 0 1+(1378128611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((599614539/1250000000 : ℝ)*X 1 0+(2877191811/10000000000 : ℝ)*X 1 1+(4586882889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4796918411/10000000000 : ℝ)*X 2 0+(-38801181/156250000 : ℝ)*X 2 1+(-246548973/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((378637331/500000000 : ℝ)*X 0 0+(-380385497/10000000000 : ℝ)*X 0 1+(3496463097/10000000000 : ℝ)*X 0 2+(378637331/500000000 : ℝ)*X 1 0+(-380385497/10000000000 : ℝ)*X 1 1+(3496463097/10000000000 : ℝ)*X 1 2+(378637331/500000000 : ℝ)*X 2 0+(-380385497/10000000000 : ℝ)*X 2 1+(3496463097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-152293787/10000000000 : ℝ)*X 0 0+(-6697642353/10000000000 : ℝ)*X 0 1+(1153989743/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4611359897/10000000000 : ℝ)*X 1 0+(784494527/2500000000 : ℝ)*X 1 1+(907472081/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((5618774517/10000000000 : ℝ)*X 2 0+(-2652627857/10000000000 : ℝ)*X 2 1+(-491003719/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((9999999871/10000000000 : ℝ)*X 1 0+(691/2500000000 : ℝ)*X 1 1+(691/2500000000 : ℝ)*X 1 2+(9999999871/10000000000 : ℝ)*X 2 0+(691/2500000000 : ℝ)*X 2 1+(691/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_17 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((4453166109/5000000000 : ℝ)*X 0 0+(-104399169/1000000000 : ℝ)*X 0 1+(593978853/5000000000 : ℝ)*X 0 2+(4453166109/5000000000 : ℝ)*X 1 0+(-104399169/1000000000 : ℝ)*X 1 1+(593978853/5000000000 : ℝ)*X 1 2+(4453166109/5000000000 : ℝ)*X 2 0+(-104399169/1000000000 : ℝ)*X 2 1+(593978853/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-198070509/10000000000 : ℝ)*X 0 0+(-1499845929/2000000000 : ℝ)*X 0 1+(3684480841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((5572997763/10000000000 : ℝ)*X 1 0+(559163667/2000000000 : ℝ)*X 1 1+(3846205893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2300173127/5000000000 : ℝ)*X 2 0+(-1531077519/5000000000 : ℝ)*X 2 1+(-1154392343/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((8937828917/10000000000 : ℝ)*X 0 0+(-399070453/10000000000 : ℝ)*X 0 1+(1684999429/10000000000 : ℝ)*X 0 2+(8937828917/10000000000 : ℝ)*X 1 0+(-399070453/10000000000 : ℝ)*X 1 1+(1684999429/10000000000 : ℝ)*X 1 2+(8937828917/10000000000 : ℝ)*X 2 0+(-399070453/10000000000 : ℝ)*X 2 1+(1684999429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((4443/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4443/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3415174765766284599117/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (199375455043/200000000000 : ℝ)*(base40) + (168799736769/125000000000 : ℝ)*(base49) + (95178879523/200000000000 : ℝ)*(base59) + (2135764064217/500000000000 : ℝ)*(major_s0_0) + (2135764064217/500000000000 : ℝ)*(major_s0_1) + (2135764064217/500000000000 : ℝ)*(major_s0_2) + (85378073/1000000000000 : ℝ)*(sp_s0_0) + (791200553087/125000000000 : ℝ)*(sp_s0_7) + (1265919109733/200000000000 : ℝ)*(sp_s0_8) + (1582383606361/250000000000 : ℝ)*(sp_s0_9) + (553335422617/250000000000 : ℝ)*(sp_s0_13) + (57687439/500000000000 : ℝ)*(sp_s0_15) + (844831/40000000000 : ℝ)*(sp_s0_21) + (176498099/1000000000000 : ℝ)*(sp_s0_23) + (553335422617/250000000000 : ℝ)*(f.failure) + (6329710923543/1000000000000 : ℝ)*(f.sum) + (8321374216961/625000000000000000000000000 : ℝ)*base62 + (1280065624794841/1000000000000000000000000000 : ℝ)*base65 + (630577526405159/1000000000000000000000000000 : ℝ)*base66 + (233603452716961/1250000000000000000000000000 : ℝ)*base68 + (982299273606361/5000000000000000000000000000 : ℝ)*base71 + (99891432305159/1000000000000000000000000000 : ℝ)*base73 + (226657150716961/1250000000000000000000000000 : ℝ)*base74 + (110330470216961/1250000000000000000000000000 : ℝ)*base76 + (14542021/312500000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (483/2500000000000000 : ℝ)*base87 + (483/2500000000000000 : ℝ)*base89 + (483/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-998/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-998/3125 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25008574694682659675931/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2413769044329/1000000000000 : ℝ)*(base40) + (42920576883/40000000000 : ℝ)*(base49) + (3349370911767/500000000000 : ℝ)*(major_s0_0) + (6698726574399/1000000000000 : ℝ)*(major_s0_1) + (6698726574399/1000000000000 : ℝ)*(major_s0_2) + (6925609/250000000000 : ℝ)*(sp_s0_0) + (15775173/1000000000000 : ℝ)*(sp_s0_6) + (150193923/1000000000000 : ℝ)*(sp_s0_8) + (9926399481483/1000000000000 : ℝ)*(sp_s0_14) + (2481569247499/250000000000 : ℝ)*(sp_s0_15) + (124080339799/12500000000 : ℝ)*(sp_s0_16) + (3049827/200000000000 : ℝ)*(sp_s0_17) + (3470936231421/1000000000000 : ℝ)*(sp_s0_20) + (70623801/1000000000000 : ℝ)*(sp_s0_27) + (694204526079/200000000000 : ℝ)*(f.failure) + (124080339799/12500000000 : ℝ)*(f.sum) + (175742552756767/1250000000000000000000000000 : ℝ)*base62 + (912153677439873/2000000000000000000000000000 : ℝ)*base64 + (1376430221960127/2000000000000000000000000000 : ℝ)*base67 + (586448860868233/2500000000000000000000000000 : ℝ)*base69 + (1962144184048253/10000000000000000000000000000 : ℝ)*base70 + (760384116884009/1000000000000000000000000000 : ℝ)*base73 + (698952202131767/2500000000000000000000000000 : ℝ)*base74 + (442141580231111/1250000000000000000000000000 : ℝ)*base76 + (381673638185629/400000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (621/2000000000000000 : ℝ)*base87 + (621/2000000000000000 : ℝ)*base89 + (621/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39033/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39033/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (81078706586175587805147/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2641617994807/1000000000000 : ℝ)*(base40) + (30000593789/20000000000 : ℝ)*(base49) + (261509947873/1000000000000 : ℝ)*(base59) + (6938143722479/1000000000000 : ℝ)*(major_s0_0) + (6938143722479/1000000000000 : ℝ)*(major_s0_1) + (6938143722479/1000000000000 : ℝ)*(major_s0_2) + (1777601/500000000000 : ℝ)*(sp_s0_0) + (41796483/500000000000 : ℝ)*(sp_s0_2) + (2300203/40000000000 : ℝ)*(sp_s0_7) + (20125823/250000000000 : ℝ)*(sp_s0_20) + (1028114158543/100000000000 : ℝ)*(sp_s0_21) + (10281202645707/1000000000000 : ℝ)*(sp_s0_22) + (10281119052741/1000000000000 : ℝ)*(sp_s0_23) + (3594998890707/1000000000000 : ℝ)*(sp_s0_27) + (3595079393999/1000000000000 : ℝ)*(f.failure) + (10281202645707/1000000000000 : ℝ)*(f.sum) + (211411900859593/1250000000000000000000000000 : ℝ)*base63 + (1216286046649967/2000000000000000000000000000 : ℝ)*base65 + (318322625350033/2000000000000000000000000000 : ℝ)*base66 + (155267331359593/2500000000000000000000000000 : ℝ)*base69 + (7904616893688207/10000000000000000000000000000 : ℝ)*base71 + (1031179610449967/2000000000000000000000000000 : ℝ)*base72 + (138016845109593/2500000000000000000000000000 : ℝ)*base75 + (1262304906109593/2500000000000000000000000000 : ℝ)*base77 + (760067953/2000000000000000000000 : ℝ)*base78 + (3299/10000000000000000 : ℝ)*base86 + (3299/10000000000000000 : ℝ)*base88 + (3299/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (4443/25000 : ℝ) ^ (41/8 : ℝ) ≤ (14285602476880403/100000000000000000000 : ℝ) := by
    have hpowers : (4443/25000 : ℝ)^41 ≤ (14285602476880403/100000000000000000000 : ℝ)^8 := by
      have hnat : (4443 : ℕ)^41*100000000000000000000^8 ≤ 14285602476880403^8*25000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4443 25000 14285602476880403 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4443/25000 : ℝ)) (X := (14285602476880403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100014285602476880403/100000000000000000000 : ℝ) ≤ (5000139363719573/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100014285602476880403/100000000000000000000 : ℝ)^8 ≤ (5000139363719573/5000000000000000 : ℝ)^41 := by
      have hnat : (100014285602476880403 : ℕ)^8*5000000000000000^41 ≤ 5000139363719573^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100014285602476880403 100000000000000000000 5000139363719573 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139363719573/5000000000000000 : ℝ)) (X := (100014285602476880403/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50014285602476880403/50000000000000000000 : ℝ) ≤ (10000557422836161/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50014285602476880403/50000000000000000000 : ℝ)^8 ≤ (10000557422836161/10000000000000000 : ℝ)^41 := by
      have hnat : (50014285602476880403 : ℕ)^8*10000000000000000^41 ≤ 10000557422836161^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014285602476880403 50000000000000000000 10000557422836161 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000557422836161/10000000000000000 : ℝ)) (X := (50014285602476880403/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(46454573191/296200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(55739079403/355440000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (4443/25000 : ℝ)) (alpha := (46454573191/296200000000000 : ℝ)) (beta := (55739079403/355440000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4443/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(46454573191/296200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(55739079403/355440000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (998/3125 : ℝ) ^ (41/8 : ℝ) ≤ (288029959262484753/100000000000000000000 : ℝ) := by
    have hpowers : (998/3125 : ℝ)^41 ≤ (288029959262484753/100000000000000000000 : ℝ)^8 := by
      have hnat : (998 : ℕ)^41*100000000000000000000^8 ≤ 288029959262484753^8*3125^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        998 3125 288029959262484753 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (998/3125 : ℝ)) (X := (288029959262484753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100288029959262484753/100000000000000000000 : ℝ) ≤ (10005613593525267/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (100288029959262484753/100000000000000000000 : ℝ)^8 ≤ (10005613593525267/10000000000000000 : ℝ)^41 := by
      have hnat : (100288029959262484753 : ℕ)^8*10000000000000000^41 ≤ 10005613593525267^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100288029959262484753 100000000000000000000 10005613593525267 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005613593525267/10000000000000000 : ℝ)) (X := (100288029959262484753/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50288029959262484753/50000000000000000000 : ℝ) ≤ (10011214225451657/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50288029959262484753/50000000000000000000 : ℝ)^8 ≤ (10011214225451657/10000000000000000 : ℝ)^41 := by
      have hnat : (50288029959262484753 : ℕ)^8*10000000000000000^41 ≤ 10011214225451657^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50288029959262484753 50000000000000000000 10011214225451657 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011214225451657/10000000000000000 : ℝ)) (X := (50288029959262484753/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(5613593525267/3193600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(560063192639/319360000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (998/3125 : ℝ)) (alpha := (5613593525267/3193600000000000 : ℝ)) (beta := (560063192639/319360000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (998/3125 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(5613593525267/3193600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(560063192639/319360000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (39033/100000 : ℝ) ^ (41/8 : ℝ) ≤ (402771427025079113/50000000000000000000 : ℝ) := by
    have hpowers : (39033/100000 : ℝ)^41 ≤ (402771427025079113/50000000000000000000 : ℝ)^8 := by
      have hnat : (39033 : ℕ)^41*50000000000000000000^8 ≤ 402771427025079113^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39033 100000 402771427025079113 50000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39033/100000 : ℝ)) (X := (402771427025079113/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50402771427025079113/50000000000000000000 : ℝ) ≤ (5007833600145513/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (50402771427025079113/50000000000000000000 : ℝ)^8 ≤ (5007833600145513/5000000000000000 : ℝ)^41 := by
      have hnat : (50402771427025079113 : ℕ)^8*5000000000000000^41 ≤ 5007833600145513^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50402771427025079113 50000000000000000000 5007833600145513 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007833600145513/5000000000000000 : ℝ)) (X := (50402771427025079113/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25402771427025079113/25000000000000000000 : ℝ) ≤ (156738030527243/156250000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (25402771427025079113/25000000000000000000 : ℝ)^8 ≤ (156738030527243/156250000000000 : ℝ)^41 := by
      have hnat : (25402771427025079113 : ℕ)^8*156250000000000^41 ≤ 156738030527243^41*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25402771427025079113 25000000000000000000 156738030527243 156250000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156738030527243/156250000000000 : ℝ)) (X := (25402771427025079113/25000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(7833600145513/1951650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7783376726263/1951650000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (39033/100000 : ℝ)) (alpha := (7833600145513/1951650000000000 : ℝ)) (beta := (7783376726263/1951650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (39033/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(7833600145513/1951650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7783376726263/1951650000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2108586583/10000000000 : ℝ)*X 0 0+(-2825382077/5000000000 : ℝ)*X 0 1+(4370871953/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1179910719/2500000000 : ℝ)*X 1 0+(136113939/400000000 : ℝ)*X 1 1+(2089881457/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4704210547/10000000000 : ℝ)*X 2 0+(-3410124551/10000000000 : ℝ)*X 2 1+(-4188700213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1515130897/2500000000 : ℝ)*X 0 0+(-1716487377/5000000000 : ℝ)*X 0 1+(531081909/2000000000 : ℝ)*X 0 2+(1515130897/2500000000 : ℝ)*X 1 0+(-1716487377/5000000000 : ℝ)*X 1 1+(531081909/2000000000 : ℝ)*X 1 2+(1515130897/2500000000 : ℝ)*X 2 0+(-1716487377/5000000000 : ℝ)*X 2 1+(531081909/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322037_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-42897/5000 : ℝ) < ((-19299/10000 : ℝ)*P 0+(-19299/10000 : ℝ)*P 1+(-19299/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-42897/5000 : ℝ) < (-678217415677247853256119067938429/80128135075000000000000000000000 : ℝ) := by norm_num
    linear_combination (169839/500000000000 : ℝ)*(base10) + (1547/12500000000 : ℝ)*(base21) + (45981/500000000000 : ℝ)*(base27) + (4549/62500000000 : ℝ)*(base33) + (69391483033/500000000000 : ℝ)*(base39) + (156042967019/250000000000 : ℝ)*(base40) + (213891324711/500000000000 : ℝ)*(base49) + (80447/500000000000 : ℝ)*(base59) + (120618745451/62500000000 : ℝ)*(major_s1_0) + (19299/10000 : ℝ)*(major_s1_1) + (19299/10000 : ℝ)*(major_s1_2) + (1410693288087/500000000000 : ℝ)*(sp_s1_0) + (705346710767/250000000000 : ℝ)*(sp_s1_1) + (705346679827/250000000000 : ℝ)*(sp_s1_2) + (499999954019/500000000000 : ℝ)*(sp_s1_6) + (705346728963/250000000000 : ℝ)*(f.sum) + (1460484863977541/8115611250000000000000000000 : ℝ)*base62 + (5399313555259/16263750000000000000000000 : ℝ)*base64 + (20617476687/77968750000000000000000 : ℝ)*base66 + (2640602084879/16263750000000000000000000 : ℝ)*base68 + (65516775966407159/240866137500000000000000000000 : ℝ)*base70 + (179207199391/1110750000000000000000000 : ℝ)*base73 + (22555493807/499000000000000000000000 : ℝ)*base75 + (9682430725659/18512500000000000000000000 : ℝ)*base76 + (72984013574641/173207578125000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p022_b019 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=37 := by omega
  rcases hc with rfl
  · exact collision_c322037 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b019 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
