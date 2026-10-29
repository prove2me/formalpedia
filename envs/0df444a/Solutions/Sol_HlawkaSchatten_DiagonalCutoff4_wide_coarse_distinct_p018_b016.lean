-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b016
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:26:32.532474+00:00
-- url     : https://prove2.me/submissions/14dccef0-80a5-4b0f-8a39-1aa4910a59a7

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
theorem collision_support_c318036_s0_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (546319/5000000000 : ℝ)*x 0 + (-2871720223/5000000000 : ℝ)*x 1 + (-1148688089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546319/5000000000 : ℝ)^5 ≤ (22342171/2000000000000 : ℝ)^4 := by
    have hnat : (546319 : ℕ)^5*2000000000000^4 ≤ 22342171^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546319 5000000000 22342171 2000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2871720223/5000000000 : ℝ)^5 ≤ (49999441444663/100000000000000 : ℝ)^4 := by
    have hnat : (2871720223 : ℕ)^5*100000000000000^4 ≤ 49999441444663^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2871720223 5000000000 49999441444663 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1148688089/2000000000 : ℝ)^5 ≤ (49999441433781/100000000000000 : ℝ)^4 := by
    have hnat : (1148688089 : ℕ)^5*100000000000000^4 ≤ 49999441433781^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148688089 2000000000 49999441433781 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546319/5000000000 : ℝ), (-2871720223/5000000000 : ℝ), (-1148688089/2000000000 : ℝ)] ![(22342171/2000000000000 : ℝ), (49999441444663/100000000000000 : ℝ), (49999441433781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546319/5000000000 : ℝ)|^5 ≤ (22342171/2000000000000 : ℝ)^4
        have hw : |(546319/5000000000 : ℝ)|=(546319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2871720223/5000000000 : ℝ)|^5 ≤ (49999441444663/100000000000000 : ℝ)^4
        have hw : |(-2871720223/5000000000 : ℝ)|=(2871720223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1148688089/2000000000 : ℝ)|^5 ≤ (49999441433781/100000000000000 : ℝ)^4
        have hw : |(-1148688089/2000000000 : ℝ)|=(1148688089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2921938563/5000000000 : ℝ)*x 0 + (3240860477/10000000000 : ℝ)*x 1 + (-1620430239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2921938563/5000000000 : ℝ)^5 ≤ (25547378896999/50000000000000 : ℝ)^4 := by
    have hnat : (2921938563 : ℕ)^5*50000000000000^4 ≤ 25547378896999^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2921938563 5000000000 25547378896999 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3240860477/10000000000 : ℝ)^5 ≤ (3056577635813/12500000000000 : ℝ)^4 := by
    have hnat : (3240860477 : ℕ)^5*12500000000000^4 ≤ 3056577635813^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3240860477 10000000000 3056577635813 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1620430239/5000000000 : ℝ)^5 ≤ (4890524219187/20000000000000 : ℝ)^4 := by
    have hnat : (1620430239 : ℕ)^5*20000000000000^4 ≤ 4890524219187^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1620430239 5000000000 4890524219187 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2921938563/5000000000 : ℝ), (3240860477/10000000000 : ℝ), (-1620430239/5000000000 : ℝ)] ![(25547378896999/50000000000000 : ℝ), (3056577635813/12500000000000 : ℝ), (4890524219187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2921938563/5000000000 : ℝ)|^5 ≤ (25547378896999/50000000000000 : ℝ)^4
        have hw : |(2921938563/5000000000 : ℝ)|=(2921938563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3240860477/10000000000 : ℝ)|^5 ≤ (3056577635813/12500000000000 : ℝ)^4
        have hw : |(3240860477/10000000000 : ℝ)|=(3240860477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1620430239/5000000000 : ℝ)|^5 ≤ (4890524219187/20000000000000 : ℝ)^4
        have hw : |(-1620430239/5000000000 : ℝ)|=(1620430239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (46751017/80000000 : ℝ)*x 0 + (-1620430239/5000000000 : ℝ)*x 1 + (3240860479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46751017/80000000 : ℝ)^5 ≤ (12773689445767/25000000000000 : ℝ)^4 := by
    have hnat : (46751017 : ℕ)^5*25000000000000^4 ≤ 12773689445767^4*80000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46751017 80000000 12773689445767 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1620430239/5000000000 : ℝ)^5 ≤ (4890524219187/20000000000000 : ℝ)^4 := by
    have hnat : (1620430239 : ℕ)^5*20000000000000^4 ≤ 4890524219187^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1620430239 5000000000 4890524219187 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3240860479/10000000000 : ℝ)^5 ≤ (12226310552683/50000000000000 : ℝ)^4 := by
    have hnat : (3240860479 : ℕ)^5*50000000000000^4 ≤ 12226310552683^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3240860479 10000000000 12226310552683 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(46751017/80000000 : ℝ), (-1620430239/5000000000 : ℝ), (3240860479/10000000000 : ℝ)] ![(12773689445767/25000000000000 : ℝ), (4890524219187/20000000000000 : ℝ), (12226310552683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(46751017/80000000 : ℝ)|^5 ≤ (12773689445767/25000000000000 : ℝ)^4
        have hw : |(46751017/80000000 : ℝ)|=(46751017/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1620430239/5000000000 : ℝ)|^5 ≤ (4890524219187/20000000000000 : ℝ)^4
        have hw : |(-1620430239/5000000000 : ℝ)|=(1620430239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3240860479/10000000000 : ℝ)|^5 ≤ (12226310552683/50000000000000 : ℝ)^4
        have hw : |(3240860479/10000000000 : ℝ)|=(3240860479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (46720841/10000000000 : ℝ)*x 0 + (-1741566837/2500000000 : ℝ)*x 1 + (-17756683/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46720841/10000000000 : ℝ)^5 ≤ (61074274819/50000000000000 : ℝ)^4 := by
    have hnat : (46720841 : ℕ)^5*50000000000000^4 ≤ 61074274819^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46720841 10000000000 61074274819 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1741566837/2500000000 : ℝ)^5 ≤ (12728586188997/20000000000000 : ℝ)^4 := by
    have hnat : (1741566837 : ℕ)^5*20000000000000^4 ≤ 12728586188997^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741566837 2500000000 12728586188997 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17756683/40000000 : ℝ)^5 ≤ (18117460248669/50000000000000 : ℝ)^4 := by
    have hnat : (17756683 : ℕ)^5*50000000000000^4 ≤ 18117460248669^4*40000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17756683 40000000 18117460248669 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(46720841/10000000000 : ℝ), (-1741566837/2500000000 : ℝ), (-17756683/40000000 : ℝ)] ![(61074274819/50000000000000 : ℝ), (12728586188997/20000000000000 : ℝ), (18117460248669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(46720841/10000000000 : ℝ)|^5 ≤ (61074274819/50000000000000 : ℝ)^4
        have hw : |(46720841/10000000000 : ℝ)|=(46720841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1741566837/2500000000 : ℝ)|^5 ≤ (12728586188997/20000000000000 : ℝ)^4
        have hw : |(-1741566837/2500000000 : ℝ)|=(1741566837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17756683/40000000 : ℝ)|^5 ≤ (18117460248669/50000000000000 : ℝ)^4
        have hw : |(-17756683/40000000 : ℝ)|=(17756683/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (92781087/250000000 : ℝ)*x 0 + (808420117/1250000000 : ℝ)*x 1 + (-1959345669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92781087/250000000 : ℝ)^5 ≤ (28966719211801/100000000000000 : ℝ)^4 := by
    have hnat : (92781087 : ℕ)^5*100000000000000^4 ≤ 28966719211801^4*250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92781087 250000000 28966719211801 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (808420117/1250000000 : ℝ)^5 ≤ (14499361655807/25000000000000 : ℝ)^4 := by
    have hnat : (808420117 : ℕ)^5*25000000000000^4 ≤ 14499361655807^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808420117 1250000000 14499361655807 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1959345669/10000000000 : ℝ)^5 ≤ (13035834153379/100000000000000 : ℝ)^4 := by
    have hnat : (1959345669 : ℕ)^5*100000000000000^4 ≤ 13035834153379^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959345669 10000000000 13035834153379 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(92781087/250000000 : ℝ), (808420117/1250000000 : ℝ), (-1959345669/10000000000 : ℝ)] ![(28966719211801/100000000000000 : ℝ), (14499361655807/25000000000000 : ℝ), (13035834153379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(92781087/250000000 : ℝ)|^5 ≤ (28966719211801/100000000000000 : ℝ)^4
        have hw : |(92781087/250000000 : ℝ)|=(92781087/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(808420117/1250000000 : ℝ)|^5 ≤ (14499361655807/25000000000000 : ℝ)^4
        have hw : |(808420117/1250000000 : ℝ)|=(808420117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1959345669/10000000000 : ℝ)|^5 ≤ (13035834153379/100000000000000 : ℝ)^4
        have hw : |(-1959345669/10000000000 : ℝ)|=(1959345669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4917566723/10000000000 : ℝ)*x 0 + (-2245037/39062500 : ℝ)*x 1 + (1572267979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4917566723/10000000000 : ℝ)^5 ≤ (2573758796403/6250000000000 : ℝ)^4 := by
    have hnat : (4917566723 : ℕ)^5*6250000000000^4 ≤ 2573758796403^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4917566723 10000000000 2573758796403 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245037/39062500 : ℝ)^5 ≤ (281403396683/10000000000000 : ℝ)^4 := by
    have hnat : (2245037 : ℕ)^5*10000000000000^4 ≤ 281403396683^4*39062500^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245037 39062500 281403396683 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1572267979/2500000000 : ℝ)^5 ≤ (14001456319141/25000000000000 : ℝ)^4 := by
    have hnat : (1572267979 : ℕ)^5*25000000000000^4 ≤ 14001456319141^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572267979 2500000000 14001456319141 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4917566723/10000000000 : ℝ), (-2245037/39062500 : ℝ), (1572267979/2500000000 : ℝ)] ![(2573758796403/6250000000000 : ℝ), (281403396683/10000000000000 : ℝ), (14001456319141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4917566723/10000000000 : ℝ)|^5 ≤ (2573758796403/6250000000000 : ℝ)^4
        have hw : |(4917566723/10000000000 : ℝ)|=(4917566723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2245037/39062500 : ℝ)|^5 ≤ (281403396683/10000000000000 : ℝ)^4
        have hw : |(-2245037/39062500 : ℝ)|=(2245037/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1572267979/2500000000 : ℝ)|^5 ≤ (14001456319141/25000000000000 : ℝ)^4
        have hw : |(1572267979/2500000000 : ℝ)|=(1572267979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2809085501/5000000000 : ℝ)*x 0 + (-1103386873/5000000000 : ℝ)*x 1 + (-17756683/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2809085501/5000000000 : ℝ)^5 ≤ (48640014113091/100000000000000 : ℝ)^4 := by
    have hnat : (2809085501 : ℕ)^5*100000000000000^4 ≤ 48640014113091^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2809085501 5000000000 48640014113091 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103386873/5000000000 : ℝ)^5 ≤ (15125065380677/100000000000000 : ℝ)^4 := by
    have hnat : (1103386873 : ℕ)^5*100000000000000^4 ≤ 15125065380677^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103386873 5000000000 15125065380677 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17756683/40000000 : ℝ)^5 ≤ (18117460248669/50000000000000 : ℝ)^4 := by
    have hnat : (17756683 : ℕ)^5*50000000000000^4 ≤ 18117460248669^4*40000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17756683 40000000 18117460248669 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2809085501/5000000000 : ℝ), (-1103386873/5000000000 : ℝ), (-17756683/40000000 : ℝ)] ![(48640014113091/100000000000000 : ℝ), (15125065380677/100000000000000 : ℝ), (18117460248669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2809085501/5000000000 : ℝ)|^5 ≤ (48640014113091/100000000000000 : ℝ)^4
        have hw : |(2809085501/5000000000 : ℝ)|=(2809085501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103386873/5000000000 : ℝ)|^5 ≤ (15125065380677/100000000000000 : ℝ)^4
        have hw : |(-1103386873/5000000000 : ℝ)|=(1103386873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17756683/40000000 : ℝ)|^5 ≤ (18117460248669/50000000000000 : ℝ)^4
        have hw : |(-17756683/40000000 : ℝ)|=(17756683/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2501893/2500000000 : ℝ)*x 0 + (-2205693301/5000000000 : ℝ)*x 1 + (-1750047207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2501893/2500000000 : ℝ)^5 ≤ (4449906777/25000000000000 : ℝ)^4 := by
    have hnat : (2501893 : ℕ)^5*25000000000000^4 ≤ 4449906777^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501893 2500000000 4449906777 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205693301/5000000000 : ℝ)^5 ≤ (17975828008763/50000000000000 : ℝ)^4 := by
    have hnat : (2205693301 : ℕ)^5*50000000000000^4 ≤ 17975828008763^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205693301 5000000000 17975828008763 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1750047207/2500000000 : ℝ)^5 ≤ (16007636086177/25000000000000 : ℝ)^4 := by
    have hnat : (1750047207 : ℕ)^5*25000000000000^4 ≤ 16007636086177^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1750047207 2500000000 16007636086177 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2501893/2500000000 : ℝ), (-2205693301/5000000000 : ℝ), (-1750047207/2500000000 : ℝ)] ![(4449906777/25000000000000 : ℝ), (17975828008763/50000000000000 : ℝ), (16007636086177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2501893/2500000000 : ℝ)|^5 ≤ (4449906777/25000000000000 : ℝ)^4
        have hw : |(2501893/2500000000 : ℝ)|=(2501893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2205693301/5000000000 : ℝ)|^5 ≤ (17975828008763/50000000000000 : ℝ)^4
        have hw : |(-2205693301/5000000000 : ℝ)|=(2205693301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1750047207/2500000000 : ℝ)|^5 ≤ (16007636086177/25000000000000 : ℝ)^4
        have hw : |(-1750047207/2500000000 : ℝ)|=(1750047207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (285567337/1250000000 : ℝ)*x 0 + (758023909/2000000000 : ℝ)*x 1 + (-38440573/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (285567337/1250000000 : ℝ)^5 ≤ (15794218734841/100000000000000 : ℝ)^4 := by
    have hnat : (285567337 : ℕ)^5*100000000000000^4 ≤ 15794218734841^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285567337 1250000000 15794218734841 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (758023909/2000000000 : ℝ)^5 ≤ (14869149902387/50000000000000 : ℝ)^4 := by
    have hnat : (758023909 : ℕ)^5*50000000000000^4 ≤ 14869149902387^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758023909 2000000000 14869149902387 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38440573/62500000 : ℝ)^5 ≤ (6808435181489/12500000000000 : ℝ)^4 := by
    have hnat : (38440573 : ℕ)^5*12500000000000^4 ≤ 6808435181489^4*62500000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38440573 62500000 6808435181489 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(285567337/1250000000 : ℝ), (758023909/2000000000 : ℝ), (-38440573/62500000 : ℝ)] ![(15794218734841/100000000000000 : ℝ), (14869149902387/50000000000000 : ℝ), (6808435181489/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(285567337/1250000000 : ℝ)|^5 ≤ (15794218734841/100000000000000 : ℝ)^4
        have hw : |(285567337/1250000000 : ℝ)|=(285567337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(758023909/2000000000 : ℝ)|^5 ≤ (14869149902387/50000000000000 : ℝ)^4
        have hw : |(758023909/2000000000 : ℝ)|=(758023909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38440573/62500000 : ℝ)|^5 ≤ (6808435181489/12500000000000 : ℝ)^4
        have hw : |(-38440573/62500000 : ℝ)|=(38440573/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1628935589/2000000000 : ℝ)*x 0 + (-914107999/10000000000 : ℝ)*x 1 + (2491230387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1628935589/2000000000 : ℝ)^5 ≤ (38686763593163/50000000000000 : ℝ)^4 := by
    have hnat : (1628935589 : ℕ)^5*50000000000000^4 ≤ 38686763593163^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1628935589 2000000000 38686763593163 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914107999/10000000000 : ℝ)^5 ≤ (1256570602869/25000000000000 : ℝ)^4 := by
    have hnat : (914107999 : ℕ)^5*25000000000000^4 ≤ 1256570602869^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914107999 10000000000 1256570602869 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2491230387/10000000000 : ℝ)^5 ≤ (17600190387279/100000000000000 : ℝ)^4 := by
    have hnat : (2491230387 : ℕ)^5*100000000000000^4 ≤ 17600190387279^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491230387 10000000000 17600190387279 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1628935589/2000000000 : ℝ), (-914107999/10000000000 : ℝ), (2491230387/10000000000 : ℝ)] ![(38686763593163/50000000000000 : ℝ), (1256570602869/25000000000000 : ℝ), (17600190387279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1628935589/2000000000 : ℝ)|^5 ≤ (38686763593163/50000000000000 : ℝ)^4
        have hw : |(1628935589/2000000000 : ℝ)|=(1628935589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-914107999/10000000000 : ℝ)|^5 ≤ (1256570602869/25000000000000 : ℝ)^4
        have hw : |(-914107999/10000000000 : ℝ)|=(914107999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2491230387/10000000000 : ℝ)|^5 ≤ (17600190387279/100000000000000 : ℝ)^4
        have hw : |(2491230387/10000000000 : ℝ)|=(2491230387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (722213599/1000000000 : ℝ)*x 0 + (-363861863/2000000000 : ℝ)*x 1 + (-732042143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (722213599/1000000000 : ℝ)^5 ≤ (13315640851033/20000000000000 : ℝ)^4 := by
    have hnat : (722213599 : ℕ)^5*20000000000000^4 ≤ 13315640851033^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722213599 1000000000 13315640851033 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (363861863/2000000000 : ℝ)^5 ≤ (742614109167/6250000000000 : ℝ)^4 := by
    have hnat : (363861863 : ℕ)^5*6250000000000^4 ≤ 742614109167^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363861863 2000000000 742614109167 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (732042143/2500000000 : ℝ)^5 ≤ (1346248124103/6250000000000 : ℝ)^4 := by
    have hnat : (732042143 : ℕ)^5*6250000000000^4 ≤ 1346248124103^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732042143 2500000000 1346248124103 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(722213599/1000000000 : ℝ), (-363861863/2000000000 : ℝ), (-732042143/2500000000 : ℝ)] ![(13315640851033/20000000000000 : ℝ), (742614109167/6250000000000 : ℝ), (1346248124103/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(722213599/1000000000 : ℝ)|^5 ≤ (13315640851033/20000000000000 : ℝ)^4
        have hw : |(722213599/1000000000 : ℝ)|=(722213599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-363861863/2000000000 : ℝ)|^5 ≤ (742614109167/6250000000000 : ℝ)^4
        have hw : |(-363861863/2000000000 : ℝ)|=(363861863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-732042143/2500000000 : ℝ)|^5 ≤ (1346248124103/6250000000000 : ℝ)^4
        have hw : |(-732042143/2500000000 : ℝ)|=(732042143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (16149063/10000000000 : ℝ)*x 0 + (-7454616691/10000000000 : ℝ)*x 1 + (-971959781/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16149063/10000000000 : ℝ)^5 ≤ (16186545237/50000000000000 : ℝ)^4 := by
    have hnat : (16149063 : ℕ)^5*50000000000000^4 ≤ 16186545237^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16149063 10000000000 16186545237 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7454616691/10000000000 : ℝ)^5 ≤ (69267840255577/100000000000000 : ℝ)^4 := by
    have hnat : (7454616691 : ℕ)^5*100000000000000^4 ≤ 69267840255577^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7454616691 10000000000 69267840255577 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971959781/2500000000 : ℝ)^5 ≤ (7674946661737/25000000000000 : ℝ)^4 := by
    have hnat : (971959781 : ℕ)^5*25000000000000^4 ≤ 7674946661737^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971959781 2500000000 7674946661737 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16149063/10000000000 : ℝ), (-7454616691/10000000000 : ℝ), (-971959781/2500000000 : ℝ)] ![(16186545237/50000000000000 : ℝ), (69267840255577/100000000000000 : ℝ), (7674946661737/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16149063/10000000000 : ℝ)|^5 ≤ (16186545237/50000000000000 : ℝ)^4
        have hw : |(16149063/10000000000 : ℝ)|=(16149063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7454616691/10000000000 : ℝ)|^5 ≤ (69267840255577/100000000000000 : ℝ)^4
        have hw : |(-7454616691/10000000000 : ℝ)|=(7454616691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-971959781/2500000000 : ℝ)|^5 ≤ (7674946661737/25000000000000 : ℝ)^4
        have hw : |(-971959781/2500000000 : ℝ)|=(971959781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3836841713/5000000000 : ℝ)*x 0 + (811998307/2500000000 : ℝ)*x 1 + (-141799581/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3836841713/5000000000 : ℝ)^5 ≤ (71821562365057/100000000000000 : ℝ)^4 := by
    have hnat : (3836841713 : ℕ)^5*100000000000000^4 ≤ 71821562365057^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3836841713 5000000000 71821562365057 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (811998307/2500000000 : ℝ)^5 ≤ (490398224917/2000000000000 : ℝ)^4 := by
    have hnat : (811998307 : ℕ)^5*2000000000000^4 ≤ 490398224917^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811998307 2500000000 490398224917 2000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141799581/2000000000 : ℝ)^5 ≤ (365852637149/10000000000000 : ℝ)^4 := by
    have hnat : (141799581 : ℕ)^5*10000000000000^4 ≤ 365852637149^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141799581 2000000000 365852637149 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3836841713/5000000000 : ℝ), (811998307/2500000000 : ℝ), (-141799581/2000000000 : ℝ)] ![(71821562365057/100000000000000 : ℝ), (490398224917/2000000000000 : ℝ), (365852637149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3836841713/5000000000 : ℝ)|^5 ≤ (71821562365057/100000000000000 : ℝ)^4
        have hw : |(3836841713/5000000000 : ℝ)|=(3836841713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(811998307/2500000000 : ℝ)|^5 ≤ (490398224917/2000000000000 : ℝ)^4
        have hw : |(811998307/2500000000 : ℝ)|=(811998307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-141799581/2000000000 : ℝ)|^5 ≤ (365852637149/10000000000000 : ℝ)^4
        have hw : |(-141799581/2000000000 : ℝ)|=(141799581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1441031919/5000000000 : ℝ)*x 0 + (-5107882497/10000000000 : ℝ)*x 1 + (2193396651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1441031919/5000000000 : ℝ)^5 ≤ (21116867519829/100000000000000 : ℝ)^4 := by
    have hnat : (1441031919 : ℕ)^5*100000000000000^4 ≤ 21116867519829^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441031919 5000000000 21116867519829 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5107882497/10000000000 : ℝ)^5 ≤ (1727273515327/4000000000000 : ℝ)^4 := by
    have hnat : (5107882497 : ℕ)^5*4000000000000^4 ≤ 1727273515327^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5107882497 10000000000 1727273515327 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2193396651/5000000000 : ℝ)^5 ≤ (1428051783463/4000000000000 : ℝ)^4 := by
    have hnat : (2193396651 : ℕ)^5*4000000000000^4 ≤ 1428051783463^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193396651 5000000000 1428051783463 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1441031919/5000000000 : ℝ), (-5107882497/10000000000 : ℝ), (2193396651/5000000000 : ℝ)] ![(21116867519829/100000000000000 : ℝ), (1727273515327/4000000000000 : ℝ), (1428051783463/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1441031919/5000000000 : ℝ)|^5 ≤ (21116867519829/100000000000000 : ℝ)^4
        have hw : |(1441031919/5000000000 : ℝ)|=(1441031919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5107882497/10000000000 : ℝ)|^5 ≤ (1727273515327/4000000000000 : ℝ)^4
        have hw : |(-5107882497/10000000000 : ℝ)|=(5107882497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2193396651/5000000000 : ℝ)|^5 ≤ (1428051783463/4000000000000 : ℝ)^4
        have hw : |(2193396651/5000000000 : ℝ)|=(2193396651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s0_27 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1795077311/2500000000 : ℝ)*x 0 + (-123316749/500000000 : ℝ)*x 1 + (-2368466469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1795077311/2500000000 : ℝ)^5 ≤ (66096572030351/100000000000000 : ℝ)^4 := by
    have hnat : (1795077311 : ℕ)^5*100000000000000^4 ≤ 66096572030351^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795077311 2500000000 66096572030351 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123316749/500000000 : ℝ)^5 ≤ (17380612544117/100000000000000 : ℝ)^4 := by
    have hnat : (123316749 : ℕ)^5*100000000000000^4 ≤ 17380612544117^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123316749 500000000 17380612544117 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2368466469/10000000000 : ℝ)^5 ≤ (8261407701813/50000000000000 : ℝ)^4 := by
    have hnat : (2368466469 : ℕ)^5*50000000000000^4 ≤ 8261407701813^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2368466469 10000000000 8261407701813 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1795077311/2500000000 : ℝ), (-123316749/500000000 : ℝ), (-2368466469/10000000000 : ℝ)] ![(66096572030351/100000000000000 : ℝ), (17380612544117/100000000000000 : ℝ), (8261407701813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1795077311/2500000000 : ℝ)|^5 ≤ (66096572030351/100000000000000 : ℝ)^4
        have hw : |(1795077311/2500000000 : ℝ)|=(1795077311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123316749/500000000 : ℝ)|^5 ≤ (17380612544117/100000000000000 : ℝ)^4
        have hw : |(-123316749/500000000 : ℝ)|=(123316749/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2368466469/10000000000 : ℝ)|^5 ≤ (8261407701813/50000000000000 : ℝ)^4
        have hw : |(-2368466469/10000000000 : ℝ)|=(2368466469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-827762193/10000000000 : ℝ)*x 0 + (-1387994673/2500000000 : ℝ)*x 1 + (-86330241/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827762193/10000000000 : ℝ)^5 ≤ (887997982323/20000000000000 : ℝ)^4 := by
    have hnat : (827762193 : ℕ)^5*20000000000000^4 ≤ 887997982323^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827762193 10000000000 887997982323 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1387994673/2500000000 : ℝ)^5 ≤ (23962368504703/50000000000000 : ℝ)^4 := by
    have hnat : (1387994673 : ℕ)^5*50000000000000^4 ≤ 23962368504703^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387994673 2500000000 23962368504703 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86330241/156250000 : ℝ)^5 ≤ (47635273062709/100000000000000 : ℝ)^4 := by
    have hnat : (86330241 : ℕ)^5*100000000000000^4 ≤ 47635273062709^4*156250000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86330241 156250000 47635273062709 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-827762193/10000000000 : ℝ), (-1387994673/2500000000 : ℝ), (-86330241/156250000 : ℝ)] ![(887997982323/20000000000000 : ℝ), (23962368504703/50000000000000 : ℝ), (47635273062709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-827762193/10000000000 : ℝ)|^5 ≤ (887997982323/20000000000000 : ℝ)^4
        have hw : |(-827762193/10000000000 : ℝ)|=(827762193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1387994673/2500000000 : ℝ)|^5 ≤ (23962368504703/50000000000000 : ℝ)^4
        have hw : |(-1387994673/2500000000 : ℝ)|=(1387994673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86330241/156250000 : ℝ)|^5 ≤ (47635273062709/100000000000000 : ℝ)^4
        have hw : |(-86330241/156250000 : ℝ)|=(86330241/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1377723497/2500000000 : ℝ)*x 0 + (3422677343/10000000000 : ℝ)*x 1 + (-3439362851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377723497/2500000000 : ℝ)^5 ≤ (9496368668977/20000000000000 : ℝ)^4 := by
    have hnat : (1377723497 : ℕ)^5*20000000000000^4 ≤ 9496368668977^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377723497 2500000000 9496368668977 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3422677343/10000000000 : ℝ)^5 ≤ (13089632520583/50000000000000 : ℝ)^4 := by
    have hnat : (3422677343 : ℕ)^5*50000000000000^4 ≤ 13089632520583^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3422677343 10000000000 13089632520583 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3439362851/10000000000 : ℝ)^5 ≤ (26338891611169/100000000000000 : ℝ)^4 := by
    have hnat : (3439362851 : ℕ)^5*100000000000000^4 ≤ 26338891611169^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3439362851 10000000000 26338891611169 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377723497/2500000000 : ℝ), (3422677343/10000000000 : ℝ), (-3439362851/10000000000 : ℝ)] ![(9496368668977/20000000000000 : ℝ), (13089632520583/50000000000000 : ℝ), (26338891611169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377723497/2500000000 : ℝ)|^5 ≤ (9496368668977/20000000000000 : ℝ)^4
        have hw : |(1377723497/2500000000 : ℝ)|=(1377723497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3422677343/10000000000 : ℝ)|^5 ≤ (13089632520583/50000000000000 : ℝ)^4
        have hw : |(3422677343/10000000000 : ℝ)|=(3422677343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3439362851/10000000000 : ℝ)|^5 ≤ (26338891611169/100000000000000 : ℝ)^4
        have hw : |(-3439362851/10000000000 : ℝ)|=(3439362851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2741012197/5000000000 : ℝ)*x 0 + (-687773577/2000000000 : ℝ)*x 1 + (3455632321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2741012197/5000000000 : ℝ)^5 ≤ (11792780453543/25000000000000 : ℝ)^4 := by
    have hnat : (2741012197 : ℕ)^5*25000000000000^4 ≤ 11792780453543^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741012197 5000000000 11792780453543 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687773577/2000000000 : ℝ)^5 ≤ (26334153589237/100000000000000 : ℝ)^4 := by
    have hnat : (687773577 : ℕ)^5*100000000000000^4 ≤ 26334153589237^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687773577 2000000000 26334153589237 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3455632321/10000000000 : ℝ)^5 ≤ (26494724576741/100000000000000 : ℝ)^4 := by
    have hnat : (3455632321 : ℕ)^5*100000000000000^4 ≤ 26494724576741^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3455632321 10000000000 26494724576741 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2741012197/5000000000 : ℝ), (-687773577/2000000000 : ℝ), (3455632321/10000000000 : ℝ)] ![(11792780453543/25000000000000 : ℝ), (26334153589237/100000000000000 : ℝ), (26494724576741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2741012197/5000000000 : ℝ)|^5 ≤ (11792780453543/25000000000000 : ℝ)^4
        have hw : |(2741012197/5000000000 : ℝ)|=(2741012197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-687773577/2000000000 : ℝ)|^5 ≤ (26334153589237/100000000000000 : ℝ)^4
        have hw : |(-687773577/2000000000 : ℝ)|=(687773577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3455632321/10000000000 : ℝ)|^5 ≤ (26494724576741/100000000000000 : ℝ)^4
        have hw : |(3455632321/10000000000 : ℝ)|=(3455632321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318036_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (648589549/1250000000 : ℝ)*x 0 + (-3618621039/10000000000 : ℝ)*x 1 + (-900281341/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (648589549/1250000000 : ℝ)^5 ≤ (11009432305829/25000000000000 : ℝ)^4 := by
    have hnat : (648589549 : ℕ)^5*25000000000000^4 ≤ 11009432305829^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648589549 1250000000 11009432305829 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3618621039/10000000000 : ℝ)^5 ≤ (14032946975467/50000000000000 : ℝ)^4 := by
    have hnat : (3618621039 : ℕ)^5*50000000000000^4 ≤ 14032946975467^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3618621039 10000000000 14032946975467 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900281341/2500000000 : ℝ)^5 ≤ (27896376808511/100000000000000 : ℝ)^4 := by
    have hnat : (900281341 : ℕ)^5*100000000000000^4 ≤ 27896376808511^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900281341 2500000000 27896376808511 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(648589549/1250000000 : ℝ), (-3618621039/10000000000 : ℝ), (-900281341/2500000000 : ℝ)] ![(11009432305829/25000000000000 : ℝ), (14032946975467/50000000000000 : ℝ), (27896376808511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(648589549/1250000000 : ℝ)|^5 ≤ (11009432305829/25000000000000 : ℝ)^4
        have hw : |(648589549/1250000000 : ℝ)|=(648589549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3618621039/10000000000 : ℝ)|^5 ≤ (14032946975467/50000000000000 : ℝ)^4
        have hw : |(-3618621039/10000000000 : ℝ)|=(3618621039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-900281341/2500000000 : ℝ)|^5 ≤ (27896376808511/100000000000000 : ℝ)^4
        have hw : |(-900281341/2500000000 : ℝ)|=(900281341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318036 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (34269/20000 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((546319/5000000000 : ℝ)*X 0 0+(-2871720223/5000000000 : ℝ)*X 0 1+(-1148688089/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2921938563/5000000000 : ℝ)*X 1 0+(3240860477/10000000000 : ℝ)*X 1 1+(-1620430239/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((46751017/80000000 : ℝ)*X 2 0+(-1620430239/5000000000 : ℝ)*X 2 1+(3240860479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((46720841/10000000000 : ℝ)*X 0 0+(-1741566837/2500000000 : ℝ)*X 0 1+(-17756683/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((92781087/250000000 : ℝ)*X 1 0+(808420117/1250000000 : ℝ)*X 1 1+(-1959345669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4917566723/10000000000 : ℝ)*X 2 0+(-2245037/39062500 : ℝ)*X 2 1+(1572267979/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2809085501/5000000000 : ℝ)*X 0 0+(-1103386873/5000000000 : ℝ)*X 0 1+(-17756683/40000000 : ℝ)*X 0 2+(2809085501/5000000000 : ℝ)*X 1 0+(-1103386873/5000000000 : ℝ)*X 1 1+(-17756683/40000000 : ℝ)*X 1 2+(2809085501/5000000000 : ℝ)*X 2 0+(-1103386873/5000000000 : ℝ)*X 2 1+(-17756683/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((2501893/2500000000 : ℝ)*X 0 0+(-2205693301/5000000000 : ℝ)*X 0 1+(-1750047207/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((285567337/1250000000 : ℝ)*X 1 0+(758023909/2000000000 : ℝ)*X 1 1+(-38440573/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1628935589/2000000000 : ℝ)*X 2 0+(-914107999/10000000000 : ℝ)*X 2 1+(2491230387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((722213599/1000000000 : ℝ)*X 0 0+(-363861863/2000000000 : ℝ)*X 0 1+(-732042143/2500000000 : ℝ)*X 0 2+(722213599/1000000000 : ℝ)*X 1 0+(-363861863/2000000000 : ℝ)*X 1 1+(-732042143/2500000000 : ℝ)*X 1 2+(722213599/1000000000 : ℝ)*X 2 0+(-363861863/2000000000 : ℝ)*X 2 1+(-732042143/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((16149063/10000000000 : ℝ)*X 0 0+(-7454616691/10000000000 : ℝ)*X 0 1+(-971959781/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3836841713/5000000000 : ℝ)*X 1 0+(811998307/2500000000 : ℝ)*X 1 1+(-141799581/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1441031919/5000000000 : ℝ)*X 2 0+(-5107882497/10000000000 : ℝ)*X 2 1+(2193396651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1795077311/2500000000 : ℝ)*X 0 0+(-123316749/500000000 : ℝ)*X 0 1+(-2368466469/10000000000 : ℝ)*X 0 2+(1795077311/2500000000 : ℝ)*X 1 0+(-123316749/500000000 : ℝ)*X 1 1+(-2368466469/10000000000 : ℝ)*X 1 2+(1795077311/2500000000 : ℝ)*X 2 0+(-123316749/500000000 : ℝ)*X 2 1+(-2368466469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((37761/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37761/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3785028211493605063827/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9489085997/125000000000 : ℝ)*(base1) + (511278813461/1000000000000 : ℝ)*(base7) + (3014137/1000000000000 : ℝ)*(base25) + (61119300271/125000000000 : ℝ)*(base39) + (16178375511/62500000000 : ℝ)*(base50) + (839493037921/500000000000 : ℝ)*(major_s0_0) + (839493037921/500000000000 : ℝ)*(major_s0_1) + (839493037921/500000000000 : ℝ)*(major_s0_2) + (21140931/1000000000000 : ℝ)*(sp_s0_0) + (1110863690567/500000000000 : ℝ)*(sp_s0_7) + (2145835834089/1000000000000 : ℝ)*(sp_s0_8) + (2145824596753/1000000000000 : ℝ)*(sp_s0_9) + (338871134857/250000000000 : ℝ)*(sp_s0_13) + (10279/1250000000 : ℝ)*(sp_s0_23) + (920118413943/1000000000000 : ℝ)*(f.failure) + (2145835834089/1000000000000 : ℝ)*(f.sum) + (300115642497061/1250000000000000000000000000 : ℝ)*base63 + (108169940026269/2500000000000000000000000000 : ℝ)*base65 + (154457602276269/2500000000000000000000000000 : ℝ)*base67 + (131532314497061/2500000000000000000000000000 : ℝ)*base69 + (53860260802333/250000000000000000000000000 : ℝ)*base71 + (242631731723731/2500000000000000000000000000 : ℝ)*base73 + (277543260252939/2500000000000000000000000000 : ℝ)*base74 + (457644484497061/2500000000000000000000000000 : ℝ)*base77 + (999691037/2500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (1957/4000000000000000 : ℝ)*base87 + (1957/4000000000000000 : ℝ)*base89 + (1957/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8399/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-8399/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3974331594762306017679/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1177603814813/1000000000000 : ℝ)*(base7) + (435421/100000000000 : ℝ)*(base27) + (536801/250000000000 : ℝ)*(base39) + (9131648067/50000000000 : ℝ)*(base40) + (5234013/500000000000 : ℝ)*(base53) + (1638485300529/1000000000000 : ℝ)*(major_s0_0) + (1638485300529/1000000000000 : ℝ)*(major_s0_1) + (1638474832503/1000000000000 : ℝ)*(major_s0_2) + (135763/100000000000 : ℝ)*(sp_s0_0) + (3962803/200000000000 : ℝ)*(sp_s0_1) + (1706442949433/1000000000000 : ℝ)*(sp_s0_14) + (213303061631/125000000000 : ℝ)*(sp_s0_15) + (1706454775089/1000000000000 : ℝ)*(sp_s0_16) + (41510452569/20000000000 : ℝ)*(sp_s0_20) + (897923167847/1000000000000 : ℝ)*(f.failure) + (1706454775089/1000000000000 : ℝ)*(f.sum) + (166957330154489/625000000000000000000000000 : ℝ)*base63 + (2109564363331333/5000000000000000000000000000 : ℝ)*base64 + (1910531294119219/5000000000000000000000000000 : ℝ)*base66 + (2450779586621523/5000000000000000000000000000 : ℝ)*base69 + (39932820638559/312500000000000000000000000 : ℝ)*base70 + (3280035463880781/5000000000000000000000000000 : ℝ)*base72 + (3341329411114389/5000000000000000000000000000 : ℝ)*base75 + (2445432455885611/5000000000000000000000000000 : ℝ)*base76 + (844356043/10000000000000000000000 : ℝ)*base78 + (747/4000000000000000 : ℝ)*base86 + (747/4000000000000000 : ℝ)*base88 + (747/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8671/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8671/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (614194020038490265077/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (609392168711/500000000000 : ℝ)*(base7) + (76528077303/250000000000 : ℝ)*(base39) + (1366233/500000000000 : ℝ)*(base40) + (444513/100000000000 : ℝ)*(base43) + (41614609823/1000000000000 : ℝ)*(base50) + (371389613487/200000000000 : ℝ)*(major_s0_0) + (371388724461/200000000000 : ℝ)*(major_s0_1) + (371389613487/200000000000 : ℝ)*(major_s0_2) + (19341467/1000000000000 : ℝ)*(sp_s0_2) + (955343/200000000000 : ℝ)*(sp_s0_7) + (80005190767/40000000000 : ℝ)*(sp_s0_21) + (100006949551/50000000000 : ℝ)*(sp_s0_22) + (2000115204423/1000000000000 : ℝ)*(sp_s0_23) + (2236429531249/1000000000000 : ℝ)*(sp_s0_27) + (1017645193827/1000000000000 : ℝ)*(f.failure) + (100006949551/50000000000 : ℝ)*(f.sum) + (70156277287933/250000000000000000000000000 : ℝ)*base62 + (72795019571443/1000000000000000000000000000 : ℝ)*base65 + (264306037190329/1000000000000000000000000000 : ℝ)*base67 + (241248263598933/1000000000000000000000000000 : ℝ)*base68 + (32535535307251/100000000000000000000000000 : ℝ)*base71 + (198934445028557/1000000000000000000000000000 : ℝ)*base73 + (405881624052799/1000000000000000000000000000 : ℝ)*base74 + (212323311701067/1000000000000000000000000000 : ℝ)*base77 + (82387777609443/500000000000000000000000000 : ℝ)*base79 + (3273/4000000000000000 : ℝ)*base87 + (3273/4000000000000000 : ℝ)*base89 + (3273/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (37761/100000 : ℝ) ^ (39/8 : ℝ) ≤ (433567782324864447/50000000000000000000 : ℝ) := by
    have hpowers : (37761/100000 : ℝ)^39 ≤ (433567782324864447/50000000000000000000 : ℝ)^8 := by
      have hnat : (37761 : ℕ)^39*50000000000000000000^8 ≤ 433567782324864447^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37761 100000 433567782324864447 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37761/100000 : ℝ)) (X := (433567782324864447/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50433567782324864447/50000000000000000000 : ℝ) ≤ (2003545282293163/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (50433567782324864447/50000000000000000000 : ℝ)^8 ≤ (2003545282293163/2000000000000000 : ℝ)^39 := by
      have hnat : (50433567782324864447 : ℕ)^8*2000000000000000^39 ≤ 2003545282293163^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50433567782324864447 50000000000000000000 2003545282293163 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003545282293163/2000000000000000 : ℝ)) (X := (50433567782324864447/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25433567782324864447/25000000000000000000 : ℝ) ≤ (10035332102807547/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (25433567782324864447/25000000000000000000 : ℝ)^8 ≤ (10035332102807547/10000000000000000 : ℝ)^39 := by
      have hnat : (25433567782324864447 : ℕ)^8*10000000000000000^39 ≤ 10035332102807547^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25433567782324864447 25000000000000000000 10035332102807547 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10035332102807547/10000000000000000 : ℝ)) (X := (25433567782324864447/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3545282293163/755220000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4401422835433/944025000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (37761/100000 : ℝ)) (alpha := (3545282293163/755220000000000 : ℝ)) (beta := (4401422835433/944025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (37761/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3545282293163/755220000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4401422835433/944025000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8399/12500 : ℝ) ^ (39/8 : ℝ) ≤ (7196861575847124199/50000000000000000000 : ℝ) := by
    have hpowers : (8399/12500 : ℝ)^39 ≤ (7196861575847124199/50000000000000000000 : ℝ)^8 := by
      have hnat : (8399 : ℕ)^39*50000000000000000000^8 ≤ 7196861575847124199^8*12500^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8399 12500 7196861575847124199 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8399/12500 : ℝ)) (X := (7196861575847124199/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (57196861575847124199/50000000000000000000 : ℝ) ≤ (2055937618579441/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (57196861575847124199/50000000000000000000 : ℝ)^8 ≤ (2055937618579441/2000000000000000 : ℝ)^39 := by
      have hnat : (57196861575847124199 : ℕ)^8*2000000000000000^39 ≤ 2055937618579441^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57196861575847124199 50000000000000000000 2055937618579441 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2055937618579441/2000000000000000 : ℝ)) (X := (57196861575847124199/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (32196861575847124199/25000000000000000000 : ℝ) ≤ (10532662309113111/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (32196861575847124199/25000000000000000000 : ℝ)^8 ≤ (10532662309113111/10000000000000000 : ℝ)^39 := by
      have hnat : (32196861575847124199 : ℕ)^8*10000000000000000^39 ≤ 10532662309113111^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32196861575847124199 25000000000000000000 10532662309113111 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10532662309113111/10000000000000000 : ℝ)) (X := (32196861575847124199/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(55937618579441/1343840000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(126487108107953/3359600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (8399/12500 : ℝ)) (alpha := (55937618579441/1343840000000000 : ℝ)) (beta := (126487108107953/3359600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8399/12500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(55937618579441/1343840000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(126487108107953/3359600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (8671/12500 : ℝ) ^ (39/8 : ℝ) ≤ (16813222852988348799/100000000000000000000 : ℝ) := by
    have hpowers : (8671/12500 : ℝ)^39 ≤ (16813222852988348799/100000000000000000000 : ℝ)^8 := by
      have hnat : (8671 : ℕ)^39*100000000000000000000^8 ≤ 16813222852988348799^8*12500^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8671 12500 16813222852988348799 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8671/12500 : ℝ)) (X := (16813222852988348799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (116813222852988348799/100000000000000000000 : ℝ) ≤ (16131120674723/15625000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (116813222852988348799/100000000000000000000 : ℝ)^8 ≤ (16131120674723/15625000000000 : ℝ)^39 := by
      have hnat : (116813222852988348799 : ℕ)^8*15625000000000^39 ≤ 16131120674723^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116813222852988348799 100000000000000000000 16131120674723 15625000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16131120674723/15625000000000 : ℝ)) (X := (116813222852988348799/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (66813222852988348799/50000000000000000000 : ℝ) ≤ (10612655959267441/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (66813222852988348799/50000000000000000000 : ℝ)^8 ≤ (10612655959267441/10000000000000000 : ℝ)^39 := by
      have hnat : (66813222852988348799 : ℕ)^8*10000000000000000^39 ≤ 10612655959267441^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66813222852988348799 50000000000000000000 10612655959267441 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10612655959267441/10000000000000000 : ℝ)) (X := (66813222852988348799/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(506120674723/10838750000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(288738727444721/6936800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (8671/12500 : ℝ)) (alpha := (506120674723/10838750000000 : ℝ)) (beta := (288738727444721/6936800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8671/12500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(506120674723/10838750000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(288738727444721/6936800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-827762193/10000000000 : ℝ)*X 0 0+(-1387994673/2500000000 : ℝ)*X 0 1+(-86330241/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1377723497/2500000000 : ℝ)*X 1 0+(3422677343/10000000000 : ℝ)*X 1 1+(-3439362851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2741012197/5000000000 : ℝ)*X 2 0+(-687773577/2000000000 : ℝ)*X 2 1+(3455632321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((648589549/1250000000 : ℝ)*X 0 0+(-3618621039/10000000000 : ℝ)*X 0 1+(-900281341/2500000000 : ℝ)*X 0 2+(648589549/1250000000 : ℝ)*X 1 0+(-3618621039/10000000000 : ℝ)*X 1 1+(-900281341/2500000000 : ℝ)*X 1 2+(648589549/1250000000 : ℝ)*X 2 0+(-3618621039/10000000000 : ℝ)*X 2 1+(-900281341/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318036_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15897/2000 : ℝ) < ((-7299/4000 : ℝ)*P 0+(-7299/4000 : ℝ)*P 1+(-7299/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15897/2000 : ℝ) < (-41998136163515994159877497593811/5285910650000000000000000000000 : ℝ) := by norm_num
    linear_combination (196677/1000000000000 : ℝ)*(base8) + (41351/250000000000 : ℝ)*(base10) + (10813/500000000000 : ℝ)*(base21) + (514503/1000000000000 : ℝ)*(base33) + (1088798824251/1000000000000 : ℝ)*(base39) + (543561008101/1000000000000 : ℝ)*(base40) + (70043562163/1000000000000 : ℝ)*(base50) + (13687496331/200000000000 : ℝ)*(base60) + (1824749485497/1000000000000 : ℝ)*(major_s1_0) + (7299/4000 : ℝ)*(major_s1_1) + (7299/4000 : ℝ)*(major_s1_2) + (662108089513/250000000000 : ℝ)*(sp_s1_0) + (264843220563/100000000000 : ℝ)*(sp_s1_1) + (662108046001/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2648432720133/1000000000000 : ℝ)*(f.sum) + (11173094611908811/182069322500000000000000000000 : ℝ)*base63 + (3885807984283/10838750000000000000000000 : ℝ)*base65 + (699095651197/5249375000000000000000000 : ℝ)*base67 + (108407260181/2167750000000000000000000 : ℝ)*base68 + (371063568079687733/2182837540000000000000000000000 : ℝ)*base70 + (53232335919171/157337500000000000000000000 : ℝ)*base73 + (330104232193/2624687500000000000000000 : ℝ)*base75 + (105278683039703/251740000000000000000000000 : ℝ)*base76 + (1876924437943329003/2642955325000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p018_b016 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 36 ≤ c.val) (hhi : c.val < 37)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=36 := by omega
  rcases hc with rfl
  · exact collision_c318036 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 36 ≤ c.val) (hhi : c.val < 37)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b016 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
