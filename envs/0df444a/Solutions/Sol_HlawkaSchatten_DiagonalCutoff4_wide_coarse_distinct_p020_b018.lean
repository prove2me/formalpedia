-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b018
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:38:41.658657+00:00
-- url     : https://prove2.me/submissions/304e16bb-b689-43be-999e-818ee37f08dd

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
theorem collision_support_c320036_s0_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (420541/10000000000 : ℝ)*x 0 + (-5724087801/10000000000 : ℝ)*x 1 + (-5724087801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420541/10000000000 : ℝ)^41 ≤ (73104379/20000000000000 : ℝ)^33 := by
    have hnat : (420541 : ℕ)^41*20000000000000^33 ≤ 73104379^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420541 10000000000 73104379 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5724087801/10000000000 : ℝ)^41 ≤ (49999817232761/100000000000000 : ℝ)^33 := by
    have hnat : (5724087801 : ℕ)^41*100000000000000^33 ≤ 49999817232761^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5724087801 10000000000 49999817232761 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5724087801/10000000000 : ℝ)^41 ≤ (49999817232761/100000000000000 : ℝ)^33 := by
    have hnat : (5724087801 : ℕ)^41*100000000000000^33 ≤ 49999817232761^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5724087801 10000000000 49999817232761 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420541/10000000000 : ℝ), (-5724087801/10000000000 : ℝ), (-5724087801/10000000000 : ℝ)] ![(73104379/20000000000000 : ℝ), (49999817232761/100000000000000 : ℝ), (49999817232761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420541/10000000000 : ℝ)|^41 ≤ (73104379/20000000000000 : ℝ)^33
        have hw : |(420541/10000000000 : ℝ)|=(420541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5724087801/10000000000 : ℝ)|^41 ≤ (49999817232761/100000000000000 : ℝ)^33
        have hw : |(-5724087801/10000000000 : ℝ)|=(5724087801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5724087801/10000000000 : ℝ)|^41 ≤ (49999817232761/100000000000000 : ℝ)^33
        have hw : |(-5724087801/10000000000 : ℝ)|=(5724087801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1454638237/2500000000 : ℝ)*x 0 + (3222257059/10000000000 : ℝ)*x 1 + (-3222257059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1454638237/2500000000 : ℝ)^41 ≤ (12756761958373/25000000000000 : ℝ)^33 := by
    have hnat : (1454638237 : ℕ)^41*25000000000000^33 ≤ 12756761958373^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1454638237 2500000000 12756761958373 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3222257059/10000000000 : ℝ)^41 ≤ (12243238036869/50000000000000 : ℝ)^33 := by
    have hnat : (3222257059 : ℕ)^41*50000000000000^33 ≤ 12243238036869^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3222257059 10000000000 12243238036869 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3222257059/10000000000 : ℝ)^41 ≤ (12243238036869/50000000000000 : ℝ)^33 := by
    have hnat : (3222257059 : ℕ)^41*50000000000000^33 ≤ 12243238036869^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3222257059 10000000000 12243238036869 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1454638237/2500000000 : ℝ), (3222257059/10000000000 : ℝ), (-3222257059/10000000000 : ℝ)] ![(12756761958373/25000000000000 : ℝ), (12243238036869/50000000000000 : ℝ), (12243238036869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1454638237/2500000000 : ℝ)|^41 ≤ (12756761958373/25000000000000 : ℝ)^33
        have hw : |(1454638237/2500000000 : ℝ)|=(1454638237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3222257059/10000000000 : ℝ)|^41 ≤ (12243238036869/50000000000000 : ℝ)^33
        have hw : |(3222257059/10000000000 : ℝ)|=(3222257059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3222257059/10000000000 : ℝ)|^41 ≤ (12243238036869/50000000000000 : ℝ)^33
        have hw : |(-3222257059/10000000000 : ℝ)|=(3222257059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5818552947/10000000000 : ℝ)*x 0 + (-3222257059/10000000000 : ℝ)*x 1 + (161112853/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5818552947/10000000000 : ℝ)^41 ≤ (12756761955649/25000000000000 : ℝ)^33 := by
    have hnat : (5818552947 : ℕ)^41*25000000000000^33 ≤ 12756761955649^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5818552947 10000000000 12756761955649 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3222257059/10000000000 : ℝ)^41 ≤ (12243238036869/50000000000000 : ℝ)^33 := by
    have hnat : (3222257059 : ℕ)^41*50000000000000^33 ≤ 12243238036869^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3222257059 10000000000 12243238036869 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161112853/500000000 : ℝ)^41 ≤ (1224323804159/5000000000000 : ℝ)^33 := by
    have hnat : (161112853 : ℕ)^41*5000000000000^33 ≤ 1224323804159^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161112853 500000000 1224323804159 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5818552947/10000000000 : ℝ), (-3222257059/10000000000 : ℝ), (161112853/500000000 : ℝ)] ![(12756761955649/25000000000000 : ℝ), (12243238036869/50000000000000 : ℝ), (1224323804159/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5818552947/10000000000 : ℝ)|^41 ≤ (12756761955649/25000000000000 : ℝ)^33
        have hw : |(5818552947/10000000000 : ℝ)|=(5818552947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3222257059/10000000000 : ℝ)|^41 ≤ (12243238036869/50000000000000 : ℝ)^33
        have hw : |(-3222257059/10000000000 : ℝ)|=(3222257059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161112853/500000000 : ℝ)|^41 ≤ (1224323804159/5000000000000 : ℝ)^33
        have hw : |(161112853/500000000 : ℝ)|=(161112853/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (687191/250000000 : ℝ)*x 0 + (-217881399/312500000 : ℝ)*x 1 + (-4399004117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (687191/250000000 : ℝ)^41 ≤ (6581460691/10000000000000 : ℝ)^33 := by
    have hnat : (687191 : ℕ)^41*10000000000000^33 ≤ 6581460691^33*250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687191 250000000 6581460691 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217881399/312500000 : ℝ)^41 ≤ (1277701052199/2000000000000 : ℝ)^33 := by
    have hnat : (217881399 : ℕ)^41*2000000000000^33 ≤ 1277701052199^33*312500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217881399 312500000 1277701052199 2000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4399004117/10000000000 : ℝ)^41 ≤ (18024566384027/50000000000000 : ℝ)^33 := by
    have hnat : (4399004117 : ℕ)^41*50000000000000^33 ≤ 18024566384027^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4399004117 10000000000 18024566384027 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(687191/250000000 : ℝ), (-217881399/312500000 : ℝ), (-4399004117/10000000000 : ℝ)] ![(6581460691/10000000000000 : ℝ), (1277701052199/2000000000000 : ℝ), (18024566384027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(687191/250000000 : ℝ)|^41 ≤ (6581460691/10000000000000 : ℝ)^33
        have hw : |(687191/250000000 : ℝ)|=(687191/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217881399/312500000 : ℝ)|^41 ≤ (1277701052199/2000000000000 : ℝ)^33
        have hw : |(-217881399/312500000 : ℝ)|=(217881399/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4399004117/10000000000 : ℝ)|^41 ≤ (18024566384027/50000000000000 : ℝ)^33
        have hw : |(-4399004117/10000000000 : ℝ)|=(4399004117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3774729177/10000000000 : ℝ)*x 0 + (6288956543/10000000000 : ℝ)*x 1 + (-64177159/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3774729177/10000000000 : ℝ)^41 ≤ (596132300229/2000000000000 : ℝ)^33 := by
    have hnat : (3774729177 : ℕ)^41*2000000000000^33 ≤ 596132300229^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3774729177 10000000000 596132300229 2000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6288956543/10000000000 : ℝ)^41 ≤ (56201662410599/100000000000000 : ℝ)^33 := by
    have hnat : (6288956543 : ℕ)^41*100000000000000^33 ≤ 56201662410599^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6288956543 10000000000 56201662410599 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64177159/312500000 : ℝ)^41 ≤ (13991722566121/100000000000000 : ℝ)^33 := by
    have hnat : (64177159 : ℕ)^41*100000000000000^33 ≤ 13991722566121^33*312500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64177159 312500000 13991722566121 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3774729177/10000000000 : ℝ), (6288956543/10000000000 : ℝ), (-64177159/312500000 : ℝ)] ![(596132300229/2000000000000 : ℝ), (56201662410599/100000000000000 : ℝ), (13991722566121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3774729177/10000000000 : ℝ)|^41 ≤ (596132300229/2000000000000 : ℝ)^33
        have hw : |(3774729177/10000000000 : ℝ)|=(3774729177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6288956543/10000000000 : ℝ)|^41 ≤ (56201662410599/100000000000000 : ℝ)^33
        have hw : |(6288956543/10000000000 : ℝ)|=(6288956543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64177159/312500000 : ℝ)|^41 ≤ (13991722566121/100000000000000 : ℝ)^33
        have hw : |(-64177159/312500000 : ℝ)|=(64177159/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5014495293/10000000000 : ℝ)*x 0 + (-25640041/400000000 : ℝ)*x 1 + (6116054209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5014495293/10000000000 : ℝ)^41 ≤ (42418474006419/100000000000000 : ℝ)^33 := by
    have hnat : (5014495293 : ℕ)^41*100000000000000^33 ≤ 42418474006419^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014495293 10000000000 42418474006419 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25640041/400000000 : ℝ)^41 ≤ (1646578189147/50000000000000 : ℝ)^33 := by
    have hnat : (25640041 : ℕ)^41*50000000000000^33 ≤ 1646578189147^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25640041 400000000 1646578189147 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6116054209/10000000000 : ℝ)^41 ≤ (27144184802727/50000000000000 : ℝ)^33 := by
    have hnat : (6116054209 : ℕ)^41*50000000000000^33 ≤ 27144184802727^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6116054209 10000000000 27144184802727 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5014495293/10000000000 : ℝ), (-25640041/400000000 : ℝ), (6116054209/10000000000 : ℝ)] ![(42418474006419/100000000000000 : ℝ), (1646578189147/50000000000000 : ℝ), (27144184802727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5014495293/10000000000 : ℝ)|^41 ≤ (42418474006419/100000000000000 : ℝ)^33
        have hw : |(5014495293/10000000000 : ℝ)|=(5014495293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25640041/400000000 : ℝ)|^41 ≤ (1646578189147/50000000000000 : ℝ)^33
        have hw : |(-25640041/400000000 : ℝ)|=(25640041/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6116054209/10000000000 : ℝ)|^41 ≤ (27144184802727/50000000000000 : ℝ)^33
        have hw : |(6116054209/10000000000 : ℝ)|=(6116054209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (221712019/400000000 : ℝ)*x 0 + (-2277513169/10000000000 : ℝ)*x 1 + (-4399004117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221712019/400000000 : ℝ)^41 ≤ (9608000072313/20000000000000 : ℝ)^33 := by
    have hnat : (221712019 : ℕ)^41*20000000000000^33 ≤ 9608000072313^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221712019 400000000 9608000072313 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2277513169/10000000000 : ℝ)^41 ≤ (3182173371053/20000000000000 : ℝ)^33 := by
    have hnat : (2277513169 : ℕ)^41*20000000000000^33 ≤ 3182173371053^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277513169 10000000000 3182173371053 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4399004117/10000000000 : ℝ)^41 ≤ (18024566384027/50000000000000 : ℝ)^33 := by
    have hnat : (4399004117 : ℕ)^41*50000000000000^33 ≤ 18024566384027^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4399004117 10000000000 18024566384027 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(221712019/400000000 : ℝ), (-2277513169/10000000000 : ℝ), (-4399004117/10000000000 : ℝ)] ![(9608000072313/20000000000000 : ℝ), (3182173371053/20000000000000 : ℝ), (18024566384027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(221712019/400000000 : ℝ)|^41 ≤ (9608000072313/20000000000000 : ℝ)^33
        have hw : |(221712019/400000000 : ℝ)|=(221712019/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2277513169/10000000000 : ℝ)|^41 ≤ (3182173371053/20000000000000 : ℝ)^33
        have hw : |(-2277513169/10000000000 : ℝ)|=(2277513169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4399004117/10000000000 : ℝ)|^41 ≤ (18024566384027/50000000000000 : ℝ)^33
        have hw : |(-4399004117/10000000000 : ℝ)|=(4399004117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4786881/10000000000 : ℝ)*x 0 + (-138493211/312500000 : ℝ)*x 1 + (-1389594903/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4786881/10000000000 : ℝ)^41 ≤ (300107533/4000000000000 : ℝ)^33 := by
    have hnat : (4786881 : ℕ)^41*4000000000000^33 ≤ 300107533^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4786881 10000000000 300107533 4000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138493211/312500000 : ℝ)^41 ≤ (9095792057623/25000000000000 : ℝ)^33 := by
    have hnat : (138493211 : ℕ)^41*25000000000000^33 ≤ 9095792057623^33*312500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138493211 312500000 9095792057623 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389594903/2000000000 : ℝ)^41 ≤ (7951166133759/12500000000000 : ℝ)^33 := by
    have hnat : (1389594903 : ℕ)^41*12500000000000^33 ≤ 7951166133759^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389594903 2000000000 7951166133759 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4786881/10000000000 : ℝ), (-138493211/312500000 : ℝ), (-1389594903/2000000000 : ℝ)] ![(300107533/4000000000000 : ℝ), (9095792057623/25000000000000 : ℝ), (7951166133759/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4786881/10000000000 : ℝ)|^41 ≤ (300107533/4000000000000 : ℝ)^33
        have hw : |(4786881/10000000000 : ℝ)|=(4786881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138493211/312500000 : ℝ)|^41 ≤ (9095792057623/25000000000000 : ℝ)^33
        have hw : |(-138493211/312500000 : ℝ)|=(138493211/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1389594903/2000000000 : ℝ)|^41 ≤ (7951166133759/12500000000000 : ℝ)^33
        have hw : |(-1389594903/2000000000 : ℝ)|=(1389594903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (558311863/2500000000 : ℝ)*x 0 + (14667719/39062500 : ℝ)*x 1 + (-1233564737/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (558311863/2500000000 : ℝ)^41 ≤ (3881891246747/25000000000000 : ℝ)^33 := by
    have hnat : (558311863 : ℕ)^41*25000000000000^33 ≤ 3881891246747^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558311863 2500000000 3881891246747 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14667719/39062500 : ℝ)^41 ≤ (14806277870311/50000000000000 : ℝ)^33 := by
    have hnat : (14667719 : ℕ)^41*50000000000000^33 ≤ 14806277870311^33*39062500^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14667719 39062500 14806277870311 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1233564737/2000000000 : ℝ)^41 ≤ (5485987925811/10000000000000 : ℝ)^33 := by
    have hnat : (1233564737 : ℕ)^41*10000000000000^33 ≤ 5485987925811^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233564737 2000000000 5485987925811 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(558311863/2500000000 : ℝ), (14667719/39062500 : ℝ), (-1233564737/2000000000 : ℝ)] ![(3881891246747/25000000000000 : ℝ), (14806277870311/50000000000000 : ℝ), (5485987925811/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(558311863/2500000000 : ℝ)|^41 ≤ (3881891246747/25000000000000 : ℝ)^33
        have hw : |(558311863/2500000000 : ℝ)|=(558311863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14667719/39062500 : ℝ)|^41 ≤ (14806277870311/50000000000000 : ℝ)^33
        have hw : |(14667719/39062500 : ℝ)|=(14667719/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1233564737/2000000000 : ℝ)|^41 ≤ (5485987925811/10000000000000 : ℝ)^33
        have hw : |(-1233564737/2000000000 : ℝ)|=(1233564737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4048666259/5000000000 : ℝ)*x 0 + (-515597361/5000000000 : ℝ)*x 1 + (2415861357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4048666259/5000000000 : ℝ)^41 ≤ (76934625926023/100000000000000 : ℝ)^33 := by
    have hnat : (4048666259 : ℕ)^41*100000000000000^33 ≤ 76934625926023^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048666259 5000000000 76934625926023 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515597361/5000000000 : ℝ)^41 ≤ (5944981995199/100000000000000 : ℝ)^33 := by
    have hnat : (515597361 : ℕ)^41*100000000000000^33 ≤ 5944981995199^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515597361 5000000000 5944981995199 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2415861357/10000000000 : ℝ)^41 ≤ (17120392056387/100000000000000 : ℝ)^33 := by
    have hnat : (2415861357 : ℕ)^41*100000000000000^33 ≤ 17120392056387^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2415861357 10000000000 17120392056387 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4048666259/5000000000 : ℝ), (-515597361/5000000000 : ℝ), (2415861357/10000000000 : ℝ)] ![(76934625926023/100000000000000 : ℝ), (5944981995199/100000000000000 : ℝ), (17120392056387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4048666259/5000000000 : ℝ)|^41 ≤ (76934625926023/100000000000000 : ℝ)^33
        have hw : |(4048666259/5000000000 : ℝ)|=(4048666259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-515597361/5000000000 : ℝ)|^41 ≤ (5944981995199/100000000000000 : ℝ)^33
        have hw : |(-515597361/5000000000 : ℝ)|=(515597361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2415861357/10000000000 : ℝ)|^41 ≤ (17120392056387/100000000000000 : ℝ)^33
        have hw : |(2415861357/10000000000 : ℝ)|=(2415861357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_17 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4999999989/5000000000 : ℝ)*x 0 + (143/2000000000 : ℝ)*x 1 + (143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4999999989/5000000000 : ℝ)^41 ≤ (99999999726667/100000000000000 : ℝ)^33 := by
    have hnat : (4999999989 : ℕ)^41*100000000000000^33 ≤ 99999999726667^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999999989 5000000000 99999999726667 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (143/2000000000 : ℝ)^41 ≤ (3311/2500000000000 : ℝ)^33 := by
    have hnat : (143 : ℕ)^41*2500000000000^33 ≤ 3311^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143 2000000000 3311 2500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (143/2000000000 : ℝ)^41 ≤ (3311/2500000000000 : ℝ)^33 := by
    have hnat : (143 : ℕ)^41*2500000000000^33 ≤ 3311^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143 2000000000 3311 2500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4999999989/5000000000 : ℝ), (143/2000000000 : ℝ), (143/2000000000 : ℝ)] ![(99999999726667/100000000000000 : ℝ), (3311/2500000000000 : ℝ), (3311/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4999999989/5000000000 : ℝ)|^41 ≤ (99999999726667/100000000000000 : ℝ)^33
        have hw : |(4999999989/5000000000 : ℝ)|=(4999999989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(143/2000000000 : ℝ)|^41 ≤ (3311/2500000000000 : ℝ)^33
        have hw : |(143/2000000000 : ℝ)|=(143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(143/2000000000 : ℝ)|^41 ≤ (3311/2500000000000 : ℝ)^33
        have hw : |(143/2000000000 : ℝ)|=(143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7205974833/10000000000 : ℝ)*x 0 + (-114022043/625000000 : ℝ)*x 1 + (-1443667119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7205974833/10000000000 : ℝ)^41 ≤ (519976889701/781250000000 : ℝ)^33 := by
    have hnat : (7205974833 : ℕ)^41*781250000000^33 ≤ 519976889701^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7205974833 10000000000 519976889701 781250000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114022043/625000000 : ℝ)^41 ≤ (1509710497113/12500000000000 : ℝ)^33 := by
    have hnat : (114022043 : ℕ)^41*12500000000000^33 ≤ 1509710497113^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114022043 625000000 1509710497113 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1443667119/5000000000 : ℝ)^41 ≤ (1068263706383/5000000000000 : ℝ)^33 := by
    have hnat : (1443667119 : ℕ)^41*5000000000000^33 ≤ 1068263706383^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1443667119 5000000000 1068263706383 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7205974833/10000000000 : ℝ), (-114022043/625000000 : ℝ), (-1443667119/5000000000 : ℝ)] ![(519976889701/781250000000 : ℝ), (1509710497113/12500000000000 : ℝ), (1068263706383/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7205974833/10000000000 : ℝ)|^41 ≤ (519976889701/781250000000 : ℝ)^33
        have hw : |(7205974833/10000000000 : ℝ)|=(7205974833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114022043/625000000 : ℝ)|^41 ≤ (1509710497113/12500000000000 : ℝ)^33
        have hw : |(-114022043/625000000 : ℝ)|=(114022043/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1443667119/5000000000 : ℝ)|^41 ≤ (1068263706383/5000000000000 : ℝ)^33
        have hw : |(-1443667119/5000000000 : ℝ)|=(1443667119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8624151/10000000000 : ℝ)*x 0 + (-3675415093/5000000000 : ℝ)*x 1 + (-794540637/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8624151/10000000000 : ℝ)^41 ≤ (623619521/4000000000000 : ℝ)^33 := by
    have hnat : (8624151 : ℕ)^41*4000000000000^33 ≤ 623619521^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8624151 10000000000 623619521 4000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3675415093/5000000000 : ℝ)^41 ≤ (68223357818087/100000000000000 : ℝ)^33 := by
    have hnat : (3675415093 : ℕ)^41*100000000000000^33 ≤ 68223357818087^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3675415093 5000000000 68223357818087 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (794540637/2000000000 : ℝ)^41 ≤ (31761051688081/100000000000000 : ℝ)^33 := by
    have hnat : (794540637 : ℕ)^41*100000000000000^33 ≤ 31761051688081^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794540637 2000000000 31761051688081 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8624151/10000000000 : ℝ), (-3675415093/5000000000 : ℝ), (-794540637/2000000000 : ℝ)] ![(623619521/4000000000000 : ℝ), (68223357818087/100000000000000 : ℝ), (31761051688081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8624151/10000000000 : ℝ)|^41 ≤ (623619521/4000000000000 : ℝ)^33
        have hw : |(8624151/10000000000 : ℝ)|=(8624151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3675415093/5000000000 : ℝ)|^41 ≤ (68223357818087/100000000000000 : ℝ)^33
        have hw : |(-3675415093/5000000000 : ℝ)|=(3675415093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-794540637/2000000000 : ℝ)|^41 ≤ (31761051688081/100000000000000 : ℝ)^33
        have hw : |(-794540637/2000000000 : ℝ)|=(794540637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (239303629/312500000 : ℝ)*x 0 + (795953247/2500000000 : ℝ)*x 1 + (-764072753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239303629/312500000 : ℝ)^41 ≤ (35889889314387/50000000000000 : ℝ)^33 := by
    have hnat : (239303629 : ℕ)^41*50000000000000^33 ≤ 35889889314387^33*312500000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239303629 312500000 35889889314387 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (795953247/2500000000 : ℝ)^41 ≤ (24124037030411/100000000000000 : ℝ)^33 := by
    have hnat : (795953247 : ℕ)^41*100000000000000^33 ≤ 24124037030411^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795953247 2500000000 24124037030411 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764072753/10000000000 : ℝ)^41 ≤ (2048092164881/50000000000000 : ℝ)^33 := by
    have hnat : (764072753 : ℕ)^41*50000000000000^33 ≤ 2048092164881^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764072753 10000000000 2048092164881 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(239303629/312500000 : ℝ), (795953247/2500000000 : ℝ), (-764072753/10000000000 : ℝ)] ![(35889889314387/50000000000000 : ℝ), (24124037030411/100000000000000 : ℝ), (2048092164881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(239303629/312500000 : ℝ)|^41 ≤ (35889889314387/50000000000000 : ℝ)^33
        have hw : |(239303629/312500000 : ℝ)|=(239303629/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(795953247/2500000000 : ℝ)|^41 ≤ (24124037030411/100000000000000 : ℝ)^33
        have hw : |(795953247/2500000000 : ℝ)|=(795953247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-764072753/10000000000 : ℝ)|^41 ≤ (2048092164881/50000000000000 : ℝ)^33
        have hw : |(-764072753/10000000000 : ℝ)|=(764072753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_23 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (569711487/2000000000 : ℝ)*x 0 + (-5097248753/10000000000 : ℝ)*x 1 + (4364749763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (569711487/2000000000 : ℝ)^41 ≤ (4201872306561/20000000000000 : ℝ)^33 := by
    have hnat : (569711487 : ℕ)^41*20000000000000^33 ≤ 4201872306561^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569711487 2000000000 4201872306561 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5097248753/10000000000 : ℝ)^41 ≤ (43289935445179/100000000000000 : ℝ)^33 := by
    have hnat : (5097248753 : ℕ)^41*100000000000000^33 ≤ 43289935445179^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097248753 10000000000 43289935445179 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4364749763/10000000000 : ℝ)^41 ≤ (35700703013351/100000000000000 : ℝ)^33 := by
    have hnat : (4364749763 : ℕ)^41*100000000000000^33 ≤ 35700703013351^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364749763 10000000000 35700703013351 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(569711487/2000000000 : ℝ), (-5097248753/10000000000 : ℝ), (4364749763/10000000000 : ℝ)] ![(4201872306561/20000000000000 : ℝ), (43289935445179/100000000000000 : ℝ), (35700703013351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(569711487/2000000000 : ℝ)|^41 ≤ (4201872306561/20000000000000 : ℝ)^33
        have hw : |(569711487/2000000000 : ℝ)|=(569711487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5097248753/10000000000 : ℝ)|^41 ≤ (43289935445179/100000000000000 : ℝ)^33
        have hw : |(-5097248753/10000000000 : ℝ)|=(5097248753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4364749763/10000000000 : ℝ)|^41 ≤ (35700703013351/100000000000000 : ℝ)^33
        have hw : |(4364749763/10000000000 : ℝ)|=(4364749763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s0_27 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3563869807/5000000000 : ℝ)*x 0 + (-2462459387/10000000000 : ℝ)*x 1 + (-2380309957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3563869807/5000000000 : ℝ)^41 ≤ (65660439257039/100000000000000 : ℝ)^33 := by
    have hnat : (3563869807 : ℕ)^41*100000000000000^33 ≤ 65660439257039^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3563869807 5000000000 65660439257039 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2462459387/10000000000 : ℝ)^41 ≤ (4382906384821/25000000000000 : ℝ)^33 := by
    have hnat : (2462459387 : ℕ)^41*25000000000000^33 ≤ 4382906384821^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462459387 10000000000 4382906384821 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2380309957/10000000000 : ℝ)^41 ≤ (16807935197987/100000000000000 : ℝ)^33 := by
    have hnat : (2380309957 : ℕ)^41*100000000000000^33 ≤ 16807935197987^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2380309957 10000000000 16807935197987 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3563869807/5000000000 : ℝ), (-2462459387/10000000000 : ℝ), (-2380309957/10000000000 : ℝ)] ![(65660439257039/100000000000000 : ℝ), (4382906384821/25000000000000 : ℝ), (16807935197987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3563869807/5000000000 : ℝ)|^41 ≤ (65660439257039/100000000000000 : ℝ)^33
        have hw : |(3563869807/5000000000 : ℝ)|=(3563869807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2462459387/10000000000 : ℝ)|^41 ≤ (4382906384821/25000000000000 : ℝ)^33
        have hw : |(-2462459387/10000000000 : ℝ)|=(2462459387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2380309957/10000000000 : ℝ)|^41 ≤ (16807935197987/100000000000000 : ℝ)^33
        have hw : |(-2380309957/10000000000 : ℝ)|=(2380309957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s1_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-886720717/10000000000 : ℝ)*x 0 + (-5506313891/10000000000 : ℝ)*x 1 + (-5485541083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (886720717/10000000000 : ℝ)^41 ≤ (4928387879047/100000000000000 : ℝ)^33 := by
    have hnat : (886720717 : ℕ)^41*100000000000000^33 ≤ 4928387879047^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886720717 10000000000 4928387879047 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506313891/10000000000 : ℝ)^41 ≤ (1488981844873/3125000000000 : ℝ)^33 := by
    have hnat : (5506313891 : ℕ)^41*3125000000000^33 ≤ 1488981844873^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506313891 10000000000 1488981844873 3125000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5485541083/10000000000 : ℝ)^41 ≤ (11856048267451/25000000000000 : ℝ)^33 := by
    have hnat : (5485541083 : ℕ)^41*25000000000000^33 ≤ 11856048267451^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485541083 10000000000 11856048267451 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-886720717/10000000000 : ℝ), (-5506313891/10000000000 : ℝ), (-5485541083/10000000000 : ℝ)] ![(4928387879047/100000000000000 : ℝ), (1488981844873/3125000000000 : ℝ), (11856048267451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-886720717/10000000000 : ℝ)|^41 ≤ (4928387879047/100000000000000 : ℝ)^33
        have hw : |(-886720717/10000000000 : ℝ)|=(886720717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5506313891/10000000000 : ℝ)|^41 ≤ (1488981844873/3125000000000 : ℝ)^33
        have hw : |(-5506313891/10000000000 : ℝ)|=(5506313891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5485541083/10000000000 : ℝ)|^41 ≤ (11856048267451/25000000000000 : ℝ)^33
        have hw : |(-5485541083/10000000000 : ℝ)|=(5485541083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s1_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2730612971/5000000000 : ℝ)*x 0 + (341893629/1000000000 : ℝ)*x 1 + (-3431769369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2730612971/5000000000 : ℝ)^41 ≤ (23581580603247/50000000000000 : ℝ)^33 := by
    have hnat : (2730612971 : ℕ)^41*50000000000000^33 ≤ 23581580603247^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730612971 5000000000 23581580603247 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341893629/1000000000 : ℝ)^41 ≤ (1054277359277/4000000000000 : ℝ)^33 := by
    have hnat : (341893629 : ℕ)^41*4000000000000^33 ≤ 1054277359277^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341893629 1000000000 1054277359277 4000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3431769369/10000000000 : ℝ)^41 ≤ (26479904789717/100000000000000 : ℝ)^33 := by
    have hnat : (3431769369 : ℕ)^41*100000000000000^33 ≤ 26479904789717^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3431769369 10000000000 26479904789717 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2730612971/5000000000 : ℝ), (341893629/1000000000 : ℝ), (-3431769369/10000000000 : ℝ)] ![(23581580603247/50000000000000 : ℝ), (1054277359277/4000000000000 : ℝ), (26479904789717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2730612971/5000000000 : ℝ)|^41 ≤ (23581580603247/50000000000000 : ℝ)^33
        have hw : |(2730612971/5000000000 : ℝ)|=(2730612971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341893629/1000000000 : ℝ)|^41 ≤ (1054277359277/4000000000000 : ℝ)^33
        have hw : |(341893629/1000000000 : ℝ)|=(341893629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3431769369/10000000000 : ℝ)|^41 ≤ (26479904789717/100000000000000 : ℝ)^33
        have hw : |(-3431769369/10000000000 : ℝ)|=(3431769369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s1_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2719491157/5000000000 : ℝ)*x 0 + (-1715677363/5000000000 : ℝ)*x 1 + (1722117209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2719491157/5000000000 : ℝ)^41 ≤ (11731153598453/25000000000000 : ℝ)^33 := by
    have hnat : (2719491157 : ℕ)^41*25000000000000^33 ≤ 11731153598453^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719491157 5000000000 11731153598453 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1715677363/5000000000 : ℝ)^41 ≤ (13237964899037/50000000000000 : ℝ)^33 := by
    have hnat : (1715677363 : ℕ)^41*50000000000000^33 ≤ 13237964899037^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1715677363 5000000000 13237964899037 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1722117209/5000000000 : ℝ)^41 ≤ (1329972789629/5000000000000 : ℝ)^33 := by
    have hnat : (1722117209 : ℕ)^41*5000000000000^33 ≤ 1329972789629^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722117209 5000000000 1329972789629 5000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2719491157/5000000000 : ℝ), (-1715677363/5000000000 : ℝ), (1722117209/5000000000 : ℝ)] ![(11731153598453/25000000000000 : ℝ), (13237964899037/50000000000000 : ℝ), (1329972789629/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2719491157/5000000000 : ℝ)|^41 ≤ (11731153598453/25000000000000 : ℝ)^33
        have hw : |(2719491157/5000000000 : ℝ)|=(2719491157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1715677363/5000000000 : ℝ)|^41 ≤ (13237964899037/50000000000000 : ℝ)^33
        have hw : |(-1715677363/5000000000 : ℝ)|=(1715677363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1722117209/5000000000 : ℝ)|^41 ≤ (1329972789629/5000000000000 : ℝ)^33
        have hw : |(1722117209/5000000000 : ℝ)|=(1722117209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320036_s1_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5162399833/10000000000 : ℝ)*x 0 + (-44967001/125000000 : ℝ)*x 1 + (-3583788883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5162399833/10000000000 : ℝ)^41 ≤ (8795689901839/20000000000000 : ℝ)^33 := by
    have hnat : (5162399833 : ℕ)^41*20000000000000^33 ≤ 8795689901839^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162399833 10000000000 8795689901839 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44967001/125000000 : ℝ)^41 ≤ (14038271949077/50000000000000 : ℝ)^33 := by
    have hnat : (44967001 : ℕ)^41*50000000000000^33 ≤ 14038271949077^33*125000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44967001 125000000 14038271949077 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3583788883/10000000000 : ℝ)^41 ≤ (13972503290563/50000000000000 : ℝ)^33 := by
    have hnat : (3583788883 : ℕ)^41*50000000000000^33 ≤ 13972503290563^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3583788883 10000000000 13972503290563 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5162399833/10000000000 : ℝ), (-44967001/125000000 : ℝ), (-3583788883/10000000000 : ℝ)] ![(8795689901839/20000000000000 : ℝ), (14038271949077/50000000000000 : ℝ), (13972503290563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5162399833/10000000000 : ℝ)|^41 ≤ (8795689901839/20000000000000 : ℝ)^33
        have hw : |(5162399833/10000000000 : ℝ)|=(5162399833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44967001/125000000 : ℝ)|^41 ≤ (14038271949077/50000000000000 : ℝ)^33
        have hw : |(-44967001/125000000 : ℝ)|=(44967001/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3583788883/10000000000 : ℝ)|^41 ≤ (13972503290563/50000000000000 : ℝ)^33
        have hw : |(-3583788883/10000000000 : ℝ)|=(3583788883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320036 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (1059/625 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner0b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(970325846184823/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner1b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (5 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^5 ≤ (1 : ℝ)^1 := by
      have hnat : (1 : ℕ)^5*1^1 ≤ 1^1*1^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2a : (2 : ℝ) ≤ (11486983549970351/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (2 : ℝ)^1 ≤ (11486983549970351/10000000000000000 : ℝ)^5 := by
      have hnat : (2 : ℕ)^1*10000000000000000^5 ≤ 11486983549970351^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11486983549970351 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11486983549970351/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s0_corner2b : (3 : ℝ) ≤ (6228654698077587/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (3 : ℝ)^1 ≤ (6228654698077587/5000000000000000 : ℝ)^5 := by
      have hnat : (3 : ℕ)^1*5000000000000000^5 ≤ 6228654698077587^5*1^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6228654698077587 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6228654698077587/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1 : ℝ)) (alpha := (1486983549970351/10000000000000000 : ℝ)) (beta := (970325846184823/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1486983549970351/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(970325846184823/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((420541/10000000000 : ℝ)*X 0 0+(-5724087801/10000000000 : ℝ)*X 0 1+(-5724087801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1454638237/2500000000 : ℝ)*X 1 0+(3222257059/10000000000 : ℝ)*X 1 1+(-3222257059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5818552947/10000000000 : ℝ)*X 2 0+(-3222257059/10000000000 : ℝ)*X 2 1+(161112853/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((687191/250000000 : ℝ)*X 0 0+(-217881399/312500000 : ℝ)*X 0 1+(-4399004117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3774729177/10000000000 : ℝ)*X 1 0+(6288956543/10000000000 : ℝ)*X 1 1+(-64177159/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((5014495293/10000000000 : ℝ)*X 2 0+(-25640041/400000000 : ℝ)*X 2 1+(6116054209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((221712019/400000000 : ℝ)*X 0 0+(-2277513169/10000000000 : ℝ)*X 0 1+(-4399004117/10000000000 : ℝ)*X 0 2+(221712019/400000000 : ℝ)*X 1 0+(-2277513169/10000000000 : ℝ)*X 1 1+(-4399004117/10000000000 : ℝ)*X 1 2+(221712019/400000000 : ℝ)*X 2 0+(-2277513169/10000000000 : ℝ)*X 2 1+(-4399004117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((4786881/10000000000 : ℝ)*X 0 0+(-138493211/312500000 : ℝ)*X 0 1+(-1389594903/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((558311863/2500000000 : ℝ)*X 1 0+(14667719/39062500 : ℝ)*X 1 1+(-1233564737/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4048666259/5000000000 : ℝ)*X 2 0+(-515597361/5000000000 : ℝ)*X 2 1+(2415861357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((4999999989/5000000000 : ℝ)*X 1 0+(143/2000000000 : ℝ)*X 1 1+(143/2000000000 : ℝ)*X 1 2+(4999999989/5000000000 : ℝ)*X 2 0+(143/2000000000 : ℝ)*X 2 1+(143/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_17 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7205974833/10000000000 : ℝ)*X 0 0+(-114022043/625000000 : ℝ)*X 0 1+(-1443667119/5000000000 : ℝ)*X 0 2+(7205974833/10000000000 : ℝ)*X 1 0+(-114022043/625000000 : ℝ)*X 1 1+(-1443667119/5000000000 : ℝ)*X 1 2+(7205974833/10000000000 : ℝ)*X 2 0+(-114022043/625000000 : ℝ)*X 2 1+(-1443667119/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((8624151/10000000000 : ℝ)*X 0 0+(-3675415093/5000000000 : ℝ)*X 0 1+(-794540637/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((239303629/312500000 : ℝ)*X 1 0+(795953247/2500000000 : ℝ)*X 1 1+(-764072753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((569711487/2000000000 : ℝ)*X 2 0+(-5097248753/10000000000 : ℝ)*X 2 1+(4364749763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((3563869807/5000000000 : ℝ)*X 0 0+(-2462459387/10000000000 : ℝ)*X 0 1+(-2380309957/10000000000 : ℝ)*X 0 2+(3563869807/5000000000 : ℝ)*X 1 0+(-2462459387/10000000000 : ℝ)*X 1 1+(-2380309957/10000000000 : ℝ)*X 1 2+(3563869807/5000000000 : ℝ)*X 2 0+(-2462459387/10000000000 : ℝ)*X 2 1+(-2380309957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((17351/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17351/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9123074401582266412869/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3612141619/1000000000000 : ℝ)*(base1) + (50096992319/100000000000 : ℝ)*(base7) + (114581/50000000000 : ℝ)*(base25) + (471849483639/1000000000000 : ℝ)*(base39) + (278190160493/1000000000000 : ℝ)*(base50) + (1722124935171/1000000000000 : ℝ)*(major_s0_0) + (1722124935171/1000000000000 : ℝ)*(major_s0_1) + (1722124935171/1000000000000 : ℝ)*(major_s0_2) + (9777173/500000000000 : ℝ)*(sp_s0_0) + (1123751600511/500000000000 : ℝ)*(sp_s0_7) + (2243910613749/1000000000000 : ℝ)*(sp_s0_8) + (2243903128069/1000000000000 : ℝ)*(sp_s0_9) + (176843501141/125000000000 : ℝ)*(sp_s0_13) + (259703/50000000000 : ℝ)*(sp_s0_23) + (917390227557/1000000000000 : ℝ)*(f.failure) + (2243910613749/1000000000000 : ℝ)*(f.sum) + (2070492314115021/5000000000000000000000000000 : ℝ)*base63 + (5985813885109733/10000000000000000000000000000 : ℝ)*base64 + (4306705863109733/10000000000000000000000000000 : ℝ)*base66 + (4723764474115021/10000000000000000000000000000 : ℝ)*base69 + (139621848374339/1250000000000000000000000000 : ℝ)*base70 + (1161302552890267/10000000000000000000000000000 : ℝ)*base72 + (4843903730115021/10000000000000000000000000000 : ℝ)*base75 + (2620360615884979/10000000000000000000000000000 : ℝ)*base76 + (191923191/400000000000000000000 : ℝ)*base79 + (2499/2500000000000000 : ℝ)*base86 + (2499/2500000000000000 : ℝ)*base88 + (2499/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1619/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-1619/2500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (35470598285656847668791/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1192073811883/1000000000000 : ℝ)*(base7) + (518039/200000000000 : ℝ)*(base27) + (22694048279/125000000000 : ℝ)*(base40) + (5874583/1000000000000 : ℝ)*(base53) + (162107791059/100000000000 : ℝ)*(major_s0_0) + (162107331083/100000000000 : ℝ)*(major_s0_1) + (1621067436247/1000000000000 : ℝ)*(major_s0_2) + (174167/250000000000 : ℝ)*(sp_s0_0) + (10898751/1000000000000 : ℝ)*(sp_s0_1) + (852647603543/500000000000 : ℝ)*(sp_s0_14) + (852642502501/500000000000 : ℝ)*(sp_s0_15) + (53290680573/31250000000 : ℝ)*(sp_s0_16) + (4599761/1000000000000 : ℝ)*(sp_s0_17) + (513907602837/250000000000 : ℝ)*(sp_s0_20) + (43177959483/50000000000 : ℝ)*(f.failure) + (53290680573/31250000000 : ℝ)*(f.sum) + (210748698085973/10000000000000000000000000000 : ℝ)*base62 + (959255567479281/10000000000000000000000000000 : ℝ)*base64 + (432734847446691/1000000000000000000000000000 : ℝ)*base67 + (5409024561287303/10000000000000000000000000000 : ℝ)*base68 + (4812017669437809/10000000000000000000000000000 : ℝ)*base71 + (539499880302443/1000000000000000000000000000 : ℝ)*base72 + (616149628279867/1000000000000000000000000000 : ℝ)*base74 + (108472757008291/1000000000000000000000000000 : ℝ)*base76 + (43657639269469/125000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (47/62500000000000 : ℝ)*base87 + (31/125000000000000 : ℝ)*base88 + (31/125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13329/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-13329/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (89284284528125722461681/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1232007196197/1000000000000 : ℝ)*(base7) + (39936204393/125000000000 : ℝ)*(base39) + (10739207/1000000000000 : ℝ)*(base43) + (3979576229/125000000000 : ℝ)*(base50) + (184631881929/100000000000 : ℝ)*(major_s0_0) + (369254145587/200000000000 : ℝ)*(major_s0_1) + (923140733571/500000000000 : ℝ)*(major_s0_2) + (43877129/1000000000000 : ℝ)*(sp_s0_2) + (2670069/200000000000 : ℝ)*(sp_s0_7) + (9338037/250000000000 : ℝ)*(sp_s0_17) + (2013165786761/1000000000000 : ℝ)*(sp_s0_21) + (1006594938157/500000000000 : ℝ)*(sp_s0_22) + (2013135259977/1000000000000 : ℝ)*(sp_s0_23) + (2215536637461/1000000000000 : ℝ)*(sp_s0_27) + (196705888253/200000000000 : ℝ)*(f.failure) + (1006594938157/500000000000 : ℝ)*(f.sum) + (4745522553162027/10000000000000000000000000000 : ℝ)*base63 + (3700461410292933/5000000000000000000000000000 : ℝ)*base64 + (401319886426101/2000000000000000000000000000 : ℝ)*base66 + (465894945353421/5000000000000000000000000000 : ℝ)*base69 + (521178637928769/2500000000000000000000000000 : ℝ)*base70 + (151073827663567/1000000000000000000000000000 : ℝ)*base73 + (1287185496291037/2000000000000000000000000000 : ℝ)*base75 + (679735429412921/1000000000000000000000000000 : ℝ)*base76 + (899669376901033/2000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (329/500000000000000 : ℝ)*base87 + (329/500000000000000 : ℝ)*base89 + (329/500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (17351/50000 : ℝ) ^ (5 : ℝ) ≤ (201294782654897/40000000000000000 : ℝ) := by
    have hpowers : (17351/50000 : ℝ)^5 ≤ (201294782654897/40000000000000000 : ℝ)^1 := by
      have hnat : (17351 : ℕ)^5*40000000000000000^1 ≤ 201294782654897^1*50000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17351 50000 201294782654897 40000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17351/50000 : ℝ)) (X := (201294782654897/40000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0a : (40201294782654897/40000000000000000 : ℝ) ≤ (5005022270148089/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (40201294782654897/40000000000000000 : ℝ)^1 ≤ (5005022270148089/5000000000000000 : ℝ)^5 := by
      have hnat : (40201294782654897 : ℕ)^1*5000000000000000^5 ≤ 5005022270148089^5*40000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40201294782654897 40000000000000000 5005022270148089 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005022270148089/5000000000000000 : ℝ)) (X := (40201294782654897/40000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0b : (20201294782654897/20000000000000000 : ℝ) ≤ (2004009785009533/2000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (20201294782654897/20000000000000000 : ℝ)^1 ≤ (2004009785009533/2000000000000000 : ℝ)^5 := by
      have hnat : (20201294782654897 : ℕ)^1*2000000000000000^5 ≤ 2004009785009533^5*20000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20201294782654897 20000000000000000 2004009785009533 2000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004009785009533/2000000000000000 : ℝ)) (X := (20201294782654897/20000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(5022270148089/1735100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(10004384751487/3470200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (17351/50000 : ℝ)) (alpha := (5022270148089/1735100000000000 : ℝ)) (beta := (10004384751487/3470200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17351/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(5022270148089/1735100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(10004384751487/3470200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1619/2500 : ℝ) ^ (5 : ℝ) ≤ (11123315195444099/97656250000000000 : ℝ) := by
    have hpowers : (1619/2500 : ℝ)^5 ≤ (11123315195444099/97656250000000000 : ℝ)^1 := by
      have hnat : (1619 : ℕ)^5*97656250000000000^1 ≤ 11123315195444099^1*2500^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1619 2500 11123315195444099 97656250000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1619/2500 : ℝ)) (X := (11123315195444099/97656250000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1a : (108779565195444099/97656250000000000 : ℝ) ≤ (2043616736311829/2000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (108779565195444099/97656250000000000 : ℝ)^1 ≤ (2043616736311829/2000000000000000 : ℝ)^5 := by
      have hnat : (108779565195444099 : ℕ)^1*2000000000000000^5 ≤ 2043616736311829^5*97656250000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108779565195444099 97656250000000000 2043616736311829 2000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2043616736311829/2000000000000000 : ℝ)) (X := (108779565195444099/97656250000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1b : (59951440195444099/48828125000000000 : ℝ) ≤ (1302374629727269/1250000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (59951440195444099/48828125000000000 : ℝ)^1 ≤ (1302374629727269/1250000000000000 : ℝ)^5 := by
      have hnat : (59951440195444099 : ℕ)^1*1250000000000000^5 ≤ 1302374629727269^5*48828125000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59951440195444099 48828125000000000 1302374629727269 1250000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1302374629727269/1250000000000000 : ℝ)) (X := (59951440195444099/48828125000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(43616736311829/1295200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(200913356259007/6476000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (1619/2500 : ℝ)) (alpha := (43616736311829/1295200000000000 : ℝ)) (beta := (200913356259007/6476000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1619/2500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(43616736311829/1295200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(200913356259007/6476000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13329/20000 : ℝ) ^ (5 : ℝ) ≤ (13147339007825837427/100000000000000000000 : ℝ) := by
    have hpowers : (13329/20000 : ℝ)^5 ≤ (13147339007825837427/100000000000000000000 : ℝ)^1 := by
      have hnat : (13329 : ℕ)^5*100000000000000000000^1 ≤ 13147339007825837427^1*20000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13329 20000 13147339007825837427 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13329/20000 : ℝ)) (X := (13147339007825837427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2a : (113147339007825837427/100000000000000000000 : ℝ) ≤ (10250118091909183/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (113147339007825837427/100000000000000000000 : ℝ)^1 ≤ (10250118091909183/10000000000000000 : ℝ)^5 := by
      have hnat : (113147339007825837427 : ℕ)^1*10000000000000000^5 ≤ 10250118091909183^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113147339007825837427 100000000000000000000 10250118091909183 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10250118091909183/10000000000000000 : ℝ)) (X := (113147339007825837427/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2b : (63147339007825837427/50000000000000000000 : ℝ) ≤ (2619491651602537/2500000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (63147339007825837427/50000000000000000000 : ℝ)^1 ≤ (2619491651602537/2500000000000000 : ℝ)^5 := by
      have hnat : (63147339007825837427 : ℕ)^1*2500000000000000^5 ≤ 2619491651602537^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63147339007825837427 50000000000000000000 2619491651602537 2500000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2619491651602537/2500000000000000 : ℝ)) (X := (63147339007825837427/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(83372697303061/2221500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(15189900966731/444300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (13329/20000 : ℝ)) (alpha := (83372697303061/2221500000000000 : ℝ)) (beta := (15189900966731/444300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (13329/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(83372697303061/2221500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(15189900966731/444300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-886720717/10000000000 : ℝ)*X 0 0+(-5506313891/10000000000 : ℝ)*X 0 1+(-5485541083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2730612971/5000000000 : ℝ)*X 1 0+(341893629/1000000000 : ℝ)*X 1 1+(-3431769369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2719491157/5000000000 : ℝ)*X 2 0+(-1715677363/5000000000 : ℝ)*X 2 1+(1722117209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5162399833/10000000000 : ℝ)*X 0 0+(-44967001/125000000 : ℝ)*X 0 1+(-3583788883/10000000000 : ℝ)*X 0 2+(5162399833/10000000000 : ℝ)*X 1 0+(-44967001/125000000 : ℝ)*X 1 1+(-3583788883/10000000000 : ℝ)*X 1 2+(5162399833/10000000000 : ℝ)*X 2 0+(-44967001/125000000 : ℝ)*X 2 1+(-3583788883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320036_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-10329/1250 : ℝ) < ((-4693/2500 : ℝ)*P 0+(-4693/2500 : ℝ)*P 1+(-4693/2500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-10329/1250 : ℝ) < (-4286031121802823899796838302076987/520039617362500000000000000000000 : ℝ) := by norm_num
    linear_combination (587/125000000000 : ℝ)*(base8) + (9881/1000000000000 : ℝ)*(base10) + (13911/1000000000000 : ℝ)*(base21) + (11291/500000000000 : ℝ)*(base33) + (1139970291337/1000000000000 : ℝ)*(base39) + (569352683489/1000000000000 : ℝ)*(base40) + (70046555373/1000000000000 : ℝ)*(base50) + (6892225313/100000000000 : ℝ)*(base60) + (938599988709/500000000000 : ℝ)*(major_s1_0) + (4693/2500 : ℝ)*(major_s1_1) + (4693/2500 : ℝ)*(major_s1_2) + (1373623263803/500000000000 : ℝ)*(sp_s1_0) + (2747246519601/1000000000000 : ℝ)*(sp_s1_1) + (2747246505691/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2747246542183/1000000000000 : ℝ)*(f.sum) + (19030085705992033/35966085000000000000000000000 : ℝ)*base62 + (4848250457461/22215000000000000000000000 : ℝ)*base64 + (2417452607269/8095000000000000000000000 : ℝ)*base66 + (4997966928953/22215000000000000000000000 : ℝ)*base68 + (1999888097171594893/3854524650000000000000000000000 : ℝ)*base71 + (1606546373100527/1735100000000000000000000000 : ℝ)*base72 + (10876405494453/8095000000000000000000000 : ℝ)*base74 + (490823338180931/867550000000000000000000000 : ℝ)*base77 + (3875770455893816043/2809126900000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p020_b018 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 36 ≤ c.val) (hhi : c.val < 37)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=36 := by omega
  rcases hc with rfl
  · exact collision_c320036 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 36 ≤ c.val) (hhi : c.val < 37)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b018 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
