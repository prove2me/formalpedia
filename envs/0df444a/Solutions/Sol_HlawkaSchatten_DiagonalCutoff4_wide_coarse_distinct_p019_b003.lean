-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p019_b003
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:32:16.84449+00:00
-- url     : https://prove2.me/submissions/195473aa-f58e-4480-8246-89d769c8964e

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
theorem collision_support_c319008_s0_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2070465983/5000000000 : ℝ)*x 0 + (-526520453/1250000000 : ℝ)*x 1 + (-203508399/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070465983/5000000000 : ℝ)^81 ≤ (4166345980999/12500000000000 : ℝ)^65 := by
    have hnat : (2070465983 : ℕ)^81*12500000000000^65 ≤ 4166345980999^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070465983 5000000000 4166345980999 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526520453/1250000000 : ℝ)^81 ≤ (2127922318131/6250000000000 : ℝ)^65 := by
    have hnat : (526520453 : ℕ)^81*6250000000000^65 ≤ 2127922318131^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526520453 1250000000 2127922318131 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203508399/500000000 : ℝ)^81 ≤ (1019452345533/3125000000000 : ℝ)^65 := by
    have hnat : (203508399 : ℕ)^81*3125000000000^65 ≤ 1019452345533^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203508399 500000000 1019452345533 3125000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2070465983/5000000000 : ℝ), (-526520453/1250000000 : ℝ), (-203508399/500000000 : ℝ)] ![(4166345980999/12500000000000 : ℝ), (2127922318131/6250000000000 : ℝ), (1019452345533/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2070465983/5000000000 : ℝ)|^81 ≤ (4166345980999/12500000000000 : ℝ)^65
        have hw : |(-2070465983/5000000000 : ℝ)|=(2070465983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-526520453/1250000000 : ℝ)|^81 ≤ (2127922318131/6250000000000 : ℝ)^65
        have hw : |(-526520453/1250000000 : ℝ)|=(526520453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-203508399/500000000 : ℝ)|^81 ≤ (1019452345533/3125000000000 : ℝ)^65
        have hw : |(-203508399/500000000 : ℝ)|=(203508399/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319008_s0_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (253804587/625000000 : ℝ)*x 0 + (1032935443/2500000000 : ℝ)*x 1 + (-4230516851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253804587/625000000 : ℝ)^81 ≤ (1301186692389/4000000000000 : ℝ)^65 := by
    have hnat : (253804587 : ℕ)^81*4000000000000^65 ≤ 1301186692389^65*625000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253804587 625000000 1301186692389 4000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032935443/2500000000 : ℝ)^81 ≤ (16619305792617/50000000000000 : ℝ)^65 := by
    have hnat : (1032935443 : ℕ)^81*50000000000000^65 ≤ 16619305792617^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032935443 2500000000 16619305792617 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230516851/10000000000 : ℝ)^81 ≤ (34231721086271/100000000000000 : ℝ)^65 := by
    have hnat : (4230516851 : ℕ)^81*100000000000000^65 ≤ 34231721086271^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230516851 10000000000 34231721086271 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(253804587/625000000 : ℝ), (1032935443/2500000000 : ℝ), (-4230516851/10000000000 : ℝ)] ![(1301186692389/4000000000000 : ℝ), (16619305792617/50000000000000 : ℝ), (34231721086271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(253804587/625000000 : ℝ)|^81 ≤ (1301186692389/4000000000000 : ℝ)^65
        have hw : |(253804587/625000000 : ℝ)|=(253804587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032935443/2500000000 : ℝ)|^81 ≤ (16619305792617/50000000000000 : ℝ)^65
        have hw : |(1032935443/2500000000 : ℝ)|=(1032935443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4230516851/10000000000 : ℝ)|^81 ≤ (34231721086271/100000000000000 : ℝ)^65
        have hw : |(-4230516851/10000000000 : ℝ)|=(4230516851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319008_s0_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4221431057/10000000000 : ℝ)*x 0 + (-2026206411/5000000000 : ℝ)*x 1 + (414929143/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4221431057/10000000000 : ℝ)^81 ≤ (2133758101671/6250000000000 : ℝ)^65 := by
    have hnat : (4221431057 : ℕ)^81*6250000000000^65 ≤ 2133758101671^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221431057 10000000000 2133758101671 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2026206411/5000000000 : ℝ)^81 ≤ (32445232793043/100000000000000 : ℝ)^65 := by
    have hnat : (2026206411 : ℕ)^81*100000000000000^65 ≤ 32445232793043^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026206411 5000000000 32445232793043 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414929143/1000000000 : ℝ)^81 ≤ (33414637560507/100000000000000 : ℝ)^65 := by
    have hnat : (414929143 : ℕ)^81*100000000000000^65 ≤ 33414637560507^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414929143 1000000000 33414637560507 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4221431057/10000000000 : ℝ), (-2026206411/5000000000 : ℝ), (414929143/1000000000 : ℝ)] ![(2133758101671/6250000000000 : ℝ), (32445232793043/100000000000000 : ℝ), (33414637560507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4221431057/10000000000 : ℝ)|^81 ≤ (2133758101671/6250000000000 : ℝ)^65
        have hw : |(4221431057/10000000000 : ℝ)|=(4221431057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2026206411/5000000000 : ℝ)|^81 ≤ (32445232793043/100000000000000 : ℝ)^65
        have hw : |(-2026206411/5000000000 : ℝ)|=(2026206411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(414929143/1000000000 : ℝ)|^81 ≤ (33414637560507/100000000000000 : ℝ)^65
        have hw : |(414929143/1000000000 : ℝ)|=(414929143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319008_s0_5 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-19/10000000000 : ℝ)*x 0 + (-19/10000000000 : ℝ)*x 1 + (-9999999999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19/10000000000 : ℝ)^81 ≤ (339/25000000000000 : ℝ)^65 := by
    have hnat : (19 : ℕ)^81*25000000000000^65 ≤ 339^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19 10000000000 339 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19/10000000000 : ℝ)^81 ≤ (339/25000000000000 : ℝ)^65 := by
    have hnat : (19 : ℕ)^81*25000000000000^65 ≤ 339^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19 10000000000 339 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9999999999/10000000000 : ℝ)^81 ≤ (99999999987539/100000000000000 : ℝ)^65 := by
    have hnat : (9999999999 : ℕ)^81*100000000000000^65 ≤ 99999999987539^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 99999999987539 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19/10000000000 : ℝ), (-19/10000000000 : ℝ), (-9999999999/10000000000 : ℝ)] ![(339/25000000000000 : ℝ), (339/25000000000000 : ℝ), (99999999987539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19/10000000000 : ℝ)|^81 ≤ (339/25000000000000 : ℝ)^65
        have hw : |(-19/10000000000 : ℝ)|=(19/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19/10000000000 : ℝ)|^81 ≤ (339/25000000000000 : ℝ)^65
        have hw : |(-19/10000000000 : ℝ)|=(19/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9999999999/10000000000 : ℝ)|^81 ≤ (99999999987539/100000000000000 : ℝ)^65
        have hw : |(-9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319008 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2070465983/5000000000 : ℝ)*X 0 0+(-526520453/1250000000 : ℝ)*X 0 1+(-203508399/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319008_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((253804587/625000000 : ℝ)*X 1 0+(1032935443/2500000000 : ℝ)*X 1 1+(-4230516851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319008_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4221431057/10000000000 : ℝ)*X 2 0+(-2026206411/5000000000 : ℝ)*X 2 1+(414929143/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319008_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_5 : ((-19/10000000000 : ℝ)*X 0 0+(-19/10000000000 : ℝ)*X 0 1+(-9999999999/10000000000 : ℝ)*X 0 2+(-19/10000000000 : ℝ)*X 1 0+(-19/10000000000 : ℝ)*X 1 1+(-9999999999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319008_s0_5 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-202641/25000 : ℝ) < ((-92547/50000 : ℝ)*P 0+(-92547/50000 : ℝ)*P 1+(-92547/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-202641/25000 : ℝ) < (-3969722862580104682248421533/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(base1) + (5839/25000000000 : ℝ)*(base15) + (928129/1000000000000 : ℝ)*(base17) + (1048562946723/1000000000000 : ℝ)*(base39) + (249755128453/500000000000 : ℝ)*(base40) + (63925132577/100000000000 : ℝ)*(base49) + (227389943397/500000000000 : ℝ)*(base50) + (248635681593/500000000000 : ℝ)*(base60) + (92547/50000 : ℝ)*(major_s0_0) + (92547/50000 : ℝ)*(major_s0_1) + (370188076121/200000000000 : ℝ)*(major_s0_2) + (113952559637/31250000000 : ℝ)*(sp_s0_0) + (529296149339/200000000000 : ℝ)*(sp_s0_1) + (82702559637/31250000000 : ℝ)*(sp_s0_2) + (76121/200000000000 : ℝ)*(sp_s0_5) + (82702559637/31250000000 : ℝ)*(f.sum) + (329609526583709/2000000000000000000000000000 : ℝ)*base62 + (551433395397313/2000000000000000000000000000 : ℝ)*base65 + (559691579/2000000000000000000000 : ℝ)*base67 + (977868951383709/2000000000000000000000000000 : ℝ)*base68 + (1770889016197313/2000000000000000000000000000 : ℝ)*base71 + (39591449/500000000000000000000 : ℝ)*base72 + (97143213/2500000000000000000000 : ℝ)*base75 + (1279011227/2500000000000000000000 : ℝ)*base77 + (3015981/250000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c319009_s0_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4155611403/10000000000 : ℝ)*x 0 + (4609229853/10000000000 : ℝ)*x 1 + (3644826169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4155611403/10000000000 : ℝ)^81 ≤ (6695614574399/20000000000000 : ℝ)^65 := by
    have hnat : (4155611403 : ℕ)^81*20000000000000^65 ≤ 6695614574399^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155611403 10000000000 6695614574399 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4609229853/10000000000 : ℝ)^81 ≤ (19045799099563/50000000000000 : ℝ)^65 := by
    have hnat : (4609229853 : ℕ)^81*50000000000000^65 ≤ 19045799099563^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4609229853 10000000000 19045799099563 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3644826169/10000000000 : ℝ)^81 ≤ (7107582227439/25000000000000 : ℝ)^65 := by
    have hnat : (3644826169 : ℕ)^81*25000000000000^65 ≤ 7107582227439^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3644826169 10000000000 7107582227439 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4155611403/10000000000 : ℝ), (4609229853/10000000000 : ℝ), (3644826169/10000000000 : ℝ)] ![(6695614574399/20000000000000 : ℝ), (19045799099563/50000000000000 : ℝ), (7107582227439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4155611403/10000000000 : ℝ)|^81 ≤ (6695614574399/20000000000000 : ℝ)^65
        have hw : |(4155611403/10000000000 : ℝ)|=(4155611403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4609229853/10000000000 : ℝ)|^81 ≤ (19045799099563/50000000000000 : ℝ)^65
        have hw : |(4609229853/10000000000 : ℝ)|=(4609229853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3644826169/10000000000 : ℝ)|^81 ≤ (7107582227439/25000000000000 : ℝ)^65
        have hw : |(3644826169/10000000000 : ℝ)|=(3644826169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5216882611/10000000000 : ℝ)*x 0 + (-2173108953/5000000000 : ℝ)*x 1 + (-1382515523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5216882611/10000000000 : ℝ)^81 ≤ (44447845153947/100000000000000 : ℝ)^65 := by
    have hnat : (5216882611 : ℕ)^81*100000000000000^65 ≤ 44447845153947^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216882611 10000000000 44447845153947 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173108953/5000000000 : ℝ)^81 ≤ (8850570348991/25000000000000 : ℝ)^65 := by
    have hnat : (2173108953 : ℕ)^81*25000000000000^65 ≤ 8850570348991^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173108953 5000000000 8850570348991 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1382515523/5000000000 : ℝ)^81 ≤ (10074936717417/50000000000000 : ℝ)^65 := by
    have hnat : (1382515523 : ℕ)^81*50000000000000^65 ≤ 10074936717417^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382515523 5000000000 10074936717417 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5216882611/10000000000 : ℝ), (-2173108953/5000000000 : ℝ), (-1382515523/5000000000 : ℝ)] ![(44447845153947/100000000000000 : ℝ), (8850570348991/25000000000000 : ℝ), (10074936717417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5216882611/10000000000 : ℝ)|^81 ≤ (44447845153947/100000000000000 : ℝ)^65
        have hw : |(5216882611/10000000000 : ℝ)|=(5216882611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2173108953/5000000000 : ℝ)|^81 ≤ (8850570348991/25000000000000 : ℝ)^65
        have hw : |(-2173108953/5000000000 : ℝ)|=(2173108953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1382515523/5000000000 : ℝ)|^81 ≤ (10074936717417/50000000000000 : ℝ)^65
        have hw : |(-1382515523/5000000000 : ℝ)|=(1382515523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5638463/5000000000 : ℝ)*x 0 + (-200718961/1250000000 : ℝ)*x 1 + (1146018223/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5638463/5000000000 : ℝ)^81 ≤ (21211732479/100000000000000 : ℝ)^65 := by
    have hnat : (5638463 : ℕ)^81*100000000000000^65 ≤ 21211732479^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5638463 5000000000 21211732479 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200718961/1250000000 : ℝ)^81 ≤ (2047307431243/20000000000000 : ℝ)^65 := by
    have hnat : (200718961 : ℕ)^81*20000000000000^65 ≤ 2047307431243^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200718961 1250000000 2047307431243 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146018223/1250000000 : ℝ)^81 ≤ (5608890693523/6250000000000 : ℝ)^65 := by
    have hnat : (1146018223 : ℕ)^81*6250000000000^65 ≤ 5608890693523^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146018223 1250000000 5608890693523 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5638463/5000000000 : ℝ), (-200718961/1250000000 : ℝ), (1146018223/1250000000 : ℝ)] ![(21211732479/100000000000000 : ℝ), (2047307431243/20000000000000 : ℝ), (5608890693523/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5638463/5000000000 : ℝ)|^81 ≤ (21211732479/100000000000000 : ℝ)^65
        have hw : |(-5638463/5000000000 : ℝ)|=(5638463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200718961/1250000000 : ℝ)|^81 ≤ (2047307431243/20000000000000 : ℝ)^65
        have hw : |(-200718961/1250000000 : ℝ)|=(200718961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1146018223/1250000000 : ℝ)|^81 ≤ (5608890693523/6250000000000 : ℝ)^65
        have hw : |(1146018223/1250000000 : ℝ)|=(1146018223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4075518207/10000000000 : ℝ)*x 0 + (-1056165579/2000000000 : ℝ)*x 1 + (373525459/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4075518207/10000000000 : ℝ)^81 ≤ (32675921484231/100000000000000 : ℝ)^65 := by
    have hnat : (4075518207 : ℕ)^81*100000000000000^65 ≤ 32675921484231^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4075518207 10000000000 32675921484231 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056165579/2000000000 : ℝ)^81 ≤ (11281947038901/25000000000000 : ℝ)^65 := by
    have hnat : (1056165579 : ℕ)^81*25000000000000^65 ≤ 11281947038901^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056165579 2000000000 11281947038901 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373525459/1250000000 : ℝ)^81 ≤ (11098145168977/50000000000000 : ℝ)^65 := by
    have hnat : (373525459 : ℕ)^81*50000000000000^65 ≤ 11098145168977^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373525459 1250000000 11098145168977 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4075518207/10000000000 : ℝ), (-1056165579/2000000000 : ℝ), (373525459/1250000000 : ℝ)] ![(32675921484231/100000000000000 : ℝ), (11281947038901/25000000000000 : ℝ), (11098145168977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4075518207/10000000000 : ℝ)|^81 ≤ (32675921484231/100000000000000 : ℝ)^65
        have hw : |(-4075518207/10000000000 : ℝ)|=(4075518207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1056165579/2000000000 : ℝ)|^81 ≤ (11281947038901/25000000000000 : ℝ)^65
        have hw : |(-1056165579/2000000000 : ℝ)|=(1056165579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(373525459/1250000000 : ℝ)|^81 ≤ (11098145168977/50000000000000 : ℝ)^65
        have hw : |(373525459/1250000000 : ℝ)|=(373525459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3383732729/10000000000 : ℝ)*x 0 + (280431931/500000000 : ℝ)*x 1 + (33338293/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3383732729/10000000000 : ℝ)^81 ≤ (25915230757941/100000000000000 : ℝ)^65 := by
    have hnat : (3383732729 : ℕ)^81*100000000000000^65 ≤ 25915230757941^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3383732729 10000000000 25915230757941 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280431931/500000000 : ℝ)^81 ≤ (1520154667099/3125000000000 : ℝ)^65 := by
    have hnat : (280431931 : ℕ)^81*3125000000000^65 ≤ 1520154667099^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280431931 500000000 1520154667099 3125000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33338293/100000000 : ℝ)^81 ≤ (5087963977081/20000000000000 : ℝ)^65 := by
    have hnat : (33338293 : ℕ)^81*20000000000000^65 ≤ 5087963977081^65*100000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33338293 100000000 5087963977081 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3383732729/10000000000 : ℝ), (280431931/500000000 : ℝ), (33338293/100000000 : ℝ)] ![(25915230757941/100000000000000 : ℝ), (1520154667099/3125000000000 : ℝ), (5087963977081/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3383732729/10000000000 : ℝ)|^81 ≤ (25915230757941/100000000000000 : ℝ)^65
        have hw : |(3383732729/10000000000 : ℝ)|=(3383732729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280431931/500000000 : ℝ)|^81 ≤ (1520154667099/3125000000000 : ℝ)^65
        have hw : |(280431931/500000000 : ℝ)|=(280431931/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33338293/100000000 : ℝ)|^81 ≤ (5087963977081/20000000000000 : ℝ)^65
        have hw : |(33338293/100000000 : ℝ)|=(33338293/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6224566703/10000000000 : ℝ)*x 0 + (-4185974713/10000000000 : ℝ)*x 1 + (-335938483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6224566703/10000000000 : ℝ)^81 ≤ (2215584334963/4000000000000 : ℝ)^65 := by
    have hnat : (6224566703 : ℕ)^81*4000000000000^65 ≤ 2215584334963^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6224566703 10000000000 2215584334963 4000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4185974713/10000000000 : ℝ)^81 ≤ (8445792120019/25000000000000 : ℝ)^65 := by
    have hnat : (4185974713 : ℕ)^81*25000000000000^65 ≤ 8445792120019^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185974713 10000000000 8445792120019 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (335938483/2000000000 : ℝ)^81 ≤ (10827223128971/100000000000000 : ℝ)^65 := by
    have hnat : (335938483 : ℕ)^81*100000000000000^65 ≤ 10827223128971^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335938483 2000000000 10827223128971 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6224566703/10000000000 : ℝ), (-4185974713/10000000000 : ℝ), (-335938483/2000000000 : ℝ)] ![(2215584334963/4000000000000 : ℝ), (8445792120019/25000000000000 : ℝ), (10827223128971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6224566703/10000000000 : ℝ)|^81 ≤ (2215584334963/4000000000000 : ℝ)^65
        have hw : |(6224566703/10000000000 : ℝ)|=(6224566703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4185974713/10000000000 : ℝ)|^81 ≤ (8445792120019/25000000000000 : ℝ)^65
        have hw : |(-4185974713/10000000000 : ℝ)|=(4185974713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-335938483/2000000000 : ℝ)|^81 ≤ (10827223128971/100000000000000 : ℝ)^65
        have hw : |(-335938483/2000000000 : ℝ)|=(335938483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-577623/500000000 : ℝ)*x 0 + (-246300631/2000000000 : ℝ)*x 1 + (4701819761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (577623/500000000 : ℝ)^81 ≤ (21859513779/100000000000000 : ℝ)^65 := by
    have hnat : (577623 : ℕ)^81*100000000000000^65 ≤ 21859513779^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577623 500000000 21859513779 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246300631/2000000000 : ℝ)^81 ≤ (735432360681/10000000000000 : ℝ)^65 := by
    have hnat : (246300631 : ℕ)^81*10000000000000^65 ≤ 735432360681^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246300631 2000000000 735432360681 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4701819761/5000000000 : ℝ)^81 ≤ (9262381686097/10000000000000 : ℝ)^65 := by
    have hnat : (4701819761 : ℕ)^81*10000000000000^65 ≤ 9262381686097^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4701819761 5000000000 9262381686097 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-577623/500000000 : ℝ), (-246300631/2000000000 : ℝ), (4701819761/5000000000 : ℝ)] ![(21859513779/100000000000000 : ℝ), (735432360681/10000000000000 : ℝ), (9262381686097/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-577623/500000000 : ℝ)|^81 ≤ (21859513779/100000000000000 : ℝ)^65
        have hw : |(-577623/500000000 : ℝ)|=(577623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246300631/2000000000 : ℝ)|^81 ≤ (735432360681/10000000000000 : ℝ)^65
        have hw : |(-246300631/2000000000 : ℝ)|=(246300631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4701819761/5000000000 : ℝ)|^81 ≤ (9262381686097/10000000000000 : ℝ)^65
        have hw : |(4701819761/5000000000 : ℝ)|=(4701819761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4891634899/10000000000 : ℝ)*x 0 + (-4035001857/10000000000 : ℝ)*x 1 + (54162961/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4891634899/10000000000 : ℝ)^81 ≤ (20510769562341/50000000000000 : ℝ)^65 := by
    have hnat : (4891634899 : ℕ)^81*50000000000000^65 ≤ 20510769562341^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4891634899 10000000000 20510769562341 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4035001857/10000000000 : ℝ)^81 ≤ (16135805995673/50000000000000 : ℝ)^65 := by
    have hnat : (4035001857 : ℕ)^81*50000000000000^65 ≤ 16135805995673^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035001857 10000000000 16135805995673 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54162961/156250000 : ℝ)^81 ≤ (2670684886741/10000000000000 : ℝ)^65 := by
    have hnat : (54162961 : ℕ)^81*10000000000000^65 ≤ 2670684886741^65*156250000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54162961 156250000 2670684886741 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4891634899/10000000000 : ℝ), (-4035001857/10000000000 : ℝ), (54162961/156250000 : ℝ)] ![(20510769562341/50000000000000 : ℝ), (16135805995673/50000000000000 : ℝ), (2670684886741/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4891634899/10000000000 : ℝ)|^81 ≤ (20510769562341/50000000000000 : ℝ)^65
        have hw : |(-4891634899/10000000000 : ℝ)|=(4891634899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4035001857/10000000000 : ℝ)|^81 ≤ (16135805995673/50000000000000 : ℝ)^65
        have hw : |(-4035001857/10000000000 : ℝ)|=(4035001857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54162961/156250000 : ℝ)|^81 ≤ (2670684886741/10000000000000 : ℝ)^65
        have hw : |(54162961/156250000 : ℝ)|=(54162961/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1141147263/2000000000 : ℝ)*x 0 + (1983322433/5000000000 : ℝ)*x 1 + (1302752721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1141147263/2000000000 : ℝ)^81 ≤ (49696623674221/100000000000000 : ℝ)^65 := by
    have hnat : (1141147263 : ℕ)^81*100000000000000^65 ≤ 49696623674221^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141147263 2000000000 49696623674221 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1983322433/5000000000 : ℝ)^81 ≤ (7897937344883/25000000000000 : ℝ)^65 := by
    have hnat : (1983322433 : ℕ)^81*25000000000000^65 ≤ 7897937344883^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983322433 5000000000 7897937344883 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1302752721/5000000000 : ℝ)^81 ≤ (18711626932297/100000000000000 : ℝ)^65 := by
    have hnat : (1302752721 : ℕ)^81*100000000000000^65 ≤ 18711626932297^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302752721 5000000000 18711626932297 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1141147263/2000000000 : ℝ), (1983322433/5000000000 : ℝ), (1302752721/5000000000 : ℝ)] ![(49696623674221/100000000000000 : ℝ), (7897937344883/25000000000000 : ℝ), (18711626932297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1141147263/2000000000 : ℝ)|^81 ≤ (49696623674221/100000000000000 : ℝ)^65
        have hw : |(1141147263/2000000000 : ℝ)|=(1141147263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1983322433/5000000000 : ℝ)|^81 ≤ (7897937344883/25000000000000 : ℝ)^65
        have hw : |(1983322433/5000000000 : ℝ)|=(1983322433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1302752721/5000000000 : ℝ)|^81 ≤ (18711626932297/100000000000000 : ℝ)^65
        have hw : |(1302752721/5000000000 : ℝ)|=(1302752721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_16 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1440239017/2500000000 : ℝ)*x 0 + (-4588513929/10000000000 : ℝ)*x 1 + (-1802809089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1440239017/2500000000 : ℝ)^81 ≤ (50296686953929/100000000000000 : ℝ)^65 := by
    have hnat : (1440239017 : ℕ)^81*100000000000000^65 ≤ 50296686953929^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1440239017 2500000000 50296686953929 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4588513929/10000000000 : ℝ)^81 ≤ (18939187065251/50000000000000 : ℝ)^65 := by
    have hnat : (4588513929 : ℕ)^81*50000000000000^65 ≤ 18939187065251^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4588513929 10000000000 18939187065251 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1802809089/10000000000 : ℝ)^81 ≤ (11824938901193/100000000000000 : ℝ)^65 := by
    have hnat : (1802809089 : ℕ)^81*100000000000000^65 ≤ 11824938901193^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802809089 10000000000 11824938901193 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1440239017/2500000000 : ℝ), (-4588513929/10000000000 : ℝ), (-1802809089/10000000000 : ℝ)] ![(50296686953929/100000000000000 : ℝ), (18939187065251/50000000000000 : ℝ), (11824938901193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1440239017/2500000000 : ℝ)|^81 ≤ (50296686953929/100000000000000 : ℝ)^65
        have hw : |(1440239017/2500000000 : ℝ)|=(1440239017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4588513929/10000000000 : ℝ)|^81 ≤ (18939187065251/50000000000000 : ℝ)^65
        have hw : |(-4588513929/10000000000 : ℝ)|=(4588513929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1802809089/10000000000 : ℝ)|^81 ≤ (11824938901193/100000000000000 : ℝ)^65
        have hw : |(-1802809089/10000000000 : ℝ)|=(1802809089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-8487877/10000000000 : ℝ)*x 0 + (-56058029/500000000 : ℝ)*x 1 + (9470294093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8487877/10000000000 : ℝ)^81 ≤ (14887136077/100000000000000 : ℝ)^65 := by
    have hnat : (8487877 : ℕ)^81*100000000000000^65 ≤ 14887136077^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8487877 10000000000 14887136077 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56058029/500000000 : ℝ)^81 ≤ (3271221128063/50000000000000 : ℝ)^65 := by
    have hnat : (56058029 : ℕ)^81*50000000000000^65 ≤ 3271221128063^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56058029 500000000 3271221128063 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9470294093/10000000000 : ℝ)^81 ≤ (9344267060207/10000000000000 : ℝ)^65 := by
    have hnat : (9470294093 : ℕ)^81*10000000000000^65 ≤ 9344267060207^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9470294093 10000000000 9344267060207 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8487877/10000000000 : ℝ), (-56058029/500000000 : ℝ), (9470294093/10000000000 : ℝ)] ![(14887136077/100000000000000 : ℝ), (3271221128063/50000000000000 : ℝ), (9344267060207/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8487877/10000000000 : ℝ)|^81 ≤ (14887136077/100000000000000 : ℝ)^65
        have hw : |(-8487877/10000000000 : ℝ)|=(8487877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56058029/500000000 : ℝ)|^81 ≤ (3271221128063/50000000000000 : ℝ)^65
        have hw : |(-56058029/500000000 : ℝ)|=(56058029/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9470294093/10000000000 : ℝ)|^81 ≤ (9344267060207/10000000000000 : ℝ)^65
        have hw : |(9470294093/10000000000 : ℝ)|=(9470294093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-208079609/500000000 : ℝ)*x 0 + (-1170478063/2500000000 : ℝ)*x 1 + (3561255919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208079609/500000000 : ℝ)^81 ≤ (16769062727079/50000000000000 : ℝ)^65 := by
    have hnat : (208079609 : ℕ)^81*50000000000000^65 ≤ 16769062727079^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208079609 500000000 16769062727079 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1170478063/2500000000 : ℝ)^81 ≤ (9710390581089/25000000000000 : ℝ)^65 := by
    have hnat : (1170478063 : ℕ)^81*25000000000000^65 ≤ 9710390581089^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170478063 2500000000 9710390581089 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3561255919/10000000000 : ℝ)^81 ≤ (6905078050063/25000000000000 : ℝ)^65 := by
    have hnat : (3561255919 : ℕ)^81*25000000000000^65 ≤ 6905078050063^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3561255919 10000000000 6905078050063 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208079609/500000000 : ℝ), (-1170478063/2500000000 : ℝ), (3561255919/10000000000 : ℝ)] ![(16769062727079/50000000000000 : ℝ), (9710390581089/25000000000000 : ℝ), (6905078050063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208079609/500000000 : ℝ)|^81 ≤ (16769062727079/50000000000000 : ℝ)^65
        have hw : |(-208079609/500000000 : ℝ)|=(208079609/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1170478063/2500000000 : ℝ)|^81 ≤ (9710390581089/25000000000000 : ℝ)^65
        have hw : |(-1170478063/2500000000 : ℝ)|=(1170478063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3561255919/10000000000 : ℝ)|^81 ≤ (6905078050063/25000000000000 : ℝ)^65
        have hw : |(3561255919/10000000000 : ℝ)|=(3561255919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1735738717/5000000000 : ℝ)*x 0 + (4529106091/10000000000 : ℝ)*x 1 + (440269371/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1735738717/5000000000 : ℝ)^81 ≤ (6688830555193/25000000000000 : ℝ)^65 := by
    have hnat : (1735738717 : ℕ)^81*25000000000000^65 ≤ 6688830555193^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735738717 5000000000 6688830555193 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4529106091/10000000000 : ℝ)^81 ≤ (7453643924997/20000000000000 : ℝ)^65 := by
    have hnat : (4529106091 : ℕ)^81*20000000000000^65 ≤ 7453643924997^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529106091 10000000000 7453643924997 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440269371/1000000000 : ℝ)^81 ≤ (17988229067653/50000000000000 : ℝ)^65 := by
    have hnat : (440269371 : ℕ)^81*50000000000000^65 ≤ 17988229067653^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440269371 1000000000 17988229067653 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1735738717/5000000000 : ℝ), (4529106091/10000000000 : ℝ), (440269371/1000000000 : ℝ)] ![(6688830555193/25000000000000 : ℝ), (7453643924997/20000000000000 : ℝ), (17988229067653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1735738717/5000000000 : ℝ)|^81 ≤ (6688830555193/25000000000000 : ℝ)^65
        have hw : |(1735738717/5000000000 : ℝ)|=(1735738717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4529106091/10000000000 : ℝ)|^81 ≤ (7453643924997/20000000000000 : ℝ)^65
        have hw : |(4529106091/10000000000 : ℝ)|=(4529106091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(440269371/1000000000 : ℝ)|^81 ≤ (17988229067653/50000000000000 : ℝ)^65
        have hw : |(440269371/1000000000 : ℝ)|=(440269371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s0_23 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2746384337/5000000000 : ℝ)*x 0 + (-3500851361/10000000000 : ℝ)*x 1 + (-3347140307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2746384337/5000000000 : ℝ)^81 ≤ (47395808843927/100000000000000 : ℝ)^65 := by
    have hnat : (2746384337 : ℕ)^81*100000000000000^65 ≤ 47395808843927^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746384337 5000000000 47395808843927 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3500851361/10000000000 : ℝ)^81 ≤ (27037732565823/100000000000000 : ℝ)^65 := by
    have hnat : (3500851361 : ℕ)^81*100000000000000^65 ≤ 27037732565823^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3500851361 10000000000 27037732565823 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3347140307/10000000000 : ℝ)^81 ≤ (12783229286011/50000000000000 : ℝ)^65 := by
    have hnat : (3347140307 : ℕ)^81*50000000000000^65 ≤ 12783229286011^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3347140307 10000000000 12783229286011 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2746384337/5000000000 : ℝ), (-3500851361/10000000000 : ℝ), (-3347140307/10000000000 : ℝ)] ![(47395808843927/100000000000000 : ℝ), (27037732565823/100000000000000 : ℝ), (12783229286011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2746384337/5000000000 : ℝ)|^81 ≤ (47395808843927/100000000000000 : ℝ)^65
        have hw : |(2746384337/5000000000 : ℝ)|=(2746384337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3500851361/10000000000 : ℝ)|^81 ≤ (27037732565823/100000000000000 : ℝ)^65
        have hw : |(-3500851361/10000000000 : ℝ)|=(3500851361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3347140307/10000000000 : ℝ)|^81 ≤ (12783229286011/50000000000000 : ℝ)^65
        have hw : |(-3347140307/10000000000 : ℝ)|=(3347140307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s1_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-207059387/500000000 : ℝ)*x 0 + (-1035296933/2500000000 : ℝ)*x 1 + (4141187731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207059387/500000000 : ℝ)^81 ≤ (16666666693383/50000000000000 : ℝ)^65 := by
    have hnat : (207059387 : ℕ)^81*50000000000000^65 ≤ 16666666693383^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207059387 500000000 16666666693383 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035296933/2500000000 : ℝ)^81 ≤ (33333333306521/100000000000000 : ℝ)^65 := by
    have hnat : (1035296933 : ℕ)^81*100000000000000^65 ≤ 33333333306521^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035296933 2500000000 33333333306521 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4141187731/10000000000 : ℝ)^81 ≤ (33333333296491/100000000000000 : ℝ)^65 := by
    have hnat : (4141187731 : ℕ)^81*100000000000000^65 ≤ 33333333296491^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141187731 10000000000 33333333296491 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207059387/500000000 : ℝ), (-1035296933/2500000000 : ℝ), (4141187731/10000000000 : ℝ)] ![(16666666693383/50000000000000 : ℝ), (33333333306521/100000000000000 : ℝ), (33333333296491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207059387/500000000 : ℝ)|^81 ≤ (16666666693383/50000000000000 : ℝ)^65
        have hw : |(-207059387/500000000 : ℝ)|=(207059387/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035296933/2500000000 : ℝ)|^81 ≤ (33333333306521/100000000000000 : ℝ)^65
        have hw : |(-1035296933/2500000000 : ℝ)|=(1035296933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4141187731/10000000000 : ℝ)|^81 ≤ (33333333296491/100000000000000 : ℝ)^65
        have hw : |(4141187731/10000000000 : ℝ)|=(4141187731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s1_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (207059387/500000000 : ℝ)*x 0 + (1035296933/2500000000 : ℝ)*x 1 + (4141187731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207059387/500000000 : ℝ)^81 ≤ (16666666693383/50000000000000 : ℝ)^65 := by
    have hnat : (207059387 : ℕ)^81*50000000000000^65 ≤ 16666666693383^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207059387 500000000 16666666693383 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035296933/2500000000 : ℝ)^81 ≤ (33333333306521/100000000000000 : ℝ)^65 := by
    have hnat : (1035296933 : ℕ)^81*100000000000000^65 ≤ 33333333306521^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035296933 2500000000 33333333306521 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4141187731/10000000000 : ℝ)^81 ≤ (33333333296491/100000000000000 : ℝ)^65 := by
    have hnat : (4141187731 : ℕ)^81*100000000000000^65 ≤ 33333333296491^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141187731 10000000000 33333333296491 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207059387/500000000 : ℝ), (1035296933/2500000000 : ℝ), (4141187731/10000000000 : ℝ)] ![(16666666693383/50000000000000 : ℝ), (33333333306521/100000000000000 : ℝ), (33333333296491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207059387/500000000 : ℝ)|^81 ≤ (16666666693383/50000000000000 : ℝ)^65
        have hw : |(207059387/500000000 : ℝ)|=(207059387/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035296933/2500000000 : ℝ)|^81 ≤ (33333333306521/100000000000000 : ℝ)^65
        have hw : |(1035296933/2500000000 : ℝ)|=(1035296933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4141187731/10000000000 : ℝ)|^81 ≤ (33333333296491/100000000000000 : ℝ)^65
        have hw : |(4141187731/10000000000 : ℝ)|=(4141187731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319009_s1_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (207059387/500000000 : ℝ)*x 0 + (-1035296933/2500000000 : ℝ)*x 1 + (-4141187731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207059387/500000000 : ℝ)^81 ≤ (16666666693383/50000000000000 : ℝ)^65 := by
    have hnat : (207059387 : ℕ)^81*50000000000000^65 ≤ 16666666693383^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207059387 500000000 16666666693383 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035296933/2500000000 : ℝ)^81 ≤ (33333333306521/100000000000000 : ℝ)^65 := by
    have hnat : (1035296933 : ℕ)^81*100000000000000^65 ≤ 33333333306521^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035296933 2500000000 33333333306521 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4141187731/10000000000 : ℝ)^81 ≤ (33333333296491/100000000000000 : ℝ)^65 := by
    have hnat : (4141187731 : ℕ)^81*100000000000000^65 ≤ 33333333296491^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141187731 10000000000 33333333296491 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207059387/500000000 : ℝ), (-1035296933/2500000000 : ℝ), (-4141187731/10000000000 : ℝ)] ![(16666666693383/50000000000000 : ℝ), (33333333306521/100000000000000 : ℝ), (33333333296491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207059387/500000000 : ℝ)|^81 ≤ (16666666693383/50000000000000 : ℝ)^65
        have hw : |(207059387/500000000 : ℝ)|=(207059387/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035296933/2500000000 : ℝ)|^81 ≤ (33333333306521/100000000000000 : ℝ)^65
        have hw : |(-1035296933/2500000000 : ℝ)|=(1035296933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4141187731/10000000000 : ℝ)|^81 ≤ (33333333296491/100000000000000 : ℝ)^65
        have hw : |(-4141187731/10000000000 : ℝ)|=(4141187731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319009 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base6 : ((-1 : ℝ)*T) ≤ (-1 : ℝ) := by
    linarith only [f.Tone]
  have base7 : ((1 : ℝ)*T) ≤ (17037/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((4155611403/10000000000 : ℝ)*X 1 0+(4609229853/10000000000 : ℝ)*X 1 1+(3644826169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5216882611/10000000000 : ℝ)*X 2 0+(-2173108953/5000000000 : ℝ)*X 2 1+(-1382515523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((-5638463/5000000000 : ℝ)*X 0 0+(-200718961/1250000000 : ℝ)*X 0 1+(1146018223/1250000000 : ℝ)*X 0 2+(-5638463/5000000000 : ℝ)*X 1 0+(-200718961/1250000000 : ℝ)*X 1 1+(1146018223/1250000000 : ℝ)*X 1 2+(-5638463/5000000000 : ℝ)*X 2 0+(-200718961/1250000000 : ℝ)*X 2 1+(1146018223/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-4075518207/10000000000 : ℝ)*X 0 0+(-1056165579/2000000000 : ℝ)*X 0 1+(373525459/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3383732729/10000000000 : ℝ)*X 1 0+(280431931/500000000 : ℝ)*X 1 1+(33338293/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((6224566703/10000000000 : ℝ)*X 2 0+(-4185974713/10000000000 : ℝ)*X 2 1+(-335938483/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-577623/500000000 : ℝ)*X 0 0+(-246300631/2000000000 : ℝ)*X 0 1+(4701819761/5000000000 : ℝ)*X 0 2+(-577623/500000000 : ℝ)*X 1 0+(-246300631/2000000000 : ℝ)*X 1 1+(4701819761/5000000000 : ℝ)*X 1 2+(-577623/500000000 : ℝ)*X 2 0+(-246300631/2000000000 : ℝ)*X 2 1+(4701819761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-4891634899/10000000000 : ℝ)*X 0 0+(-4035001857/10000000000 : ℝ)*X 0 1+(54162961/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1141147263/2000000000 : ℝ)*X 1 0+(1983322433/5000000000 : ℝ)*X 1 1+(1302752721/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1440239017/2500000000 : ℝ)*X 2 0+(-4588513929/10000000000 : ℝ)*X 2 1+(-1802809089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-8487877/10000000000 : ℝ)*X 0 0+(-56058029/500000000 : ℝ)*X 0 1+(9470294093/10000000000 : ℝ)*X 0 2+(-8487877/10000000000 : ℝ)*X 1 0+(-56058029/500000000 : ℝ)*X 1 1+(9470294093/10000000000 : ℝ)*X 1 2+(-8487877/10000000000 : ℝ)*X 2 0+(-56058029/500000000 : ℝ)*X 2 1+(9470294093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-208079609/500000000 : ℝ)*X 0 0+(-1170478063/2500000000 : ℝ)*X 0 1+(3561255919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1735738717/5000000000 : ℝ)*X 1 0+(4529106091/10000000000 : ℝ)*X 1 1+(440269371/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2746384337/5000000000 : ℝ)*X 2 0+(-3500851361/10000000000 : ℝ)*X 2 1+(-3347140307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((21009/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21009/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11875468637288223121953/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21301477077/200000000000 : ℝ)*(base1) + (451540125179/1000000000000 : ℝ)*(base7) + (49954648401/500000000000 : ℝ)*(base50) + (168579308269/200000000000 : ℝ)*(base54) + (78506934237/100000000000 : ℝ)*(base60) + (2786774669767/1000000000000 : ℝ)*(major_s0_0) + (2786774669767/1000000000000 : ℝ)*(major_s0_1) + (971939064211/500000000000 : ℝ)*(major_s0_2) + (6881161/125000000000 : ℝ)*(sp_s0_6) + (979506654293/250000000000 : ℝ)*(sp_s0_7) + (3811519231787/1000000000000 : ℝ)*(sp_s0_8) + (2968609900169/1000000000000 : ℝ)*(sp_s0_9) + (1007680828117/1000000000000 : ℝ)*(sp_s0_13) + (24981/1953125000 : ℝ)*(sp_s0_16) + (376399919739/250000000000 : ℝ)*(f.failure) + (3811519231787/1000000000000 : ℝ)*(f.sum) + (1811959822553281/10000000000000000000000000000 : ℝ)*base62 + (2657496466007083/5000000000000000000000000000 : ℝ)*base65 + (2653843522945951/10000000000000000000000000000 : ℝ)*base66 + (2176448858236319/5000000000000000000000000000 : ℝ)*base68 + (804535485094809/10000000000000000000000000000 : ℝ)*base71 + (537147038945951/10000000000000000000000000000 : ℝ)*base72 + (38566228080643/10000000000000000000000000000 : ℝ)*base74 + (483498102919357/10000000000000000000000000000 : ℝ)*base76 + (2151016834445951/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (2267/12500000000000000 : ℝ)*base86 + (2267/12500000000000000 : ℝ)*base88 + (2267/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-62999/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-62999/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (35605030155881877281583/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13462917083/15625000000 : ℝ)*(base1) + (913416087311/1000000000000 : ℝ)*(base7) + (152969990993/250000000000 : ℝ)*(base40) + (1321353/250000000000 : ℝ)*(base50) + (293820400329/250000000000 : ℝ)*(base54) + (260078421833/500000000000 : ℝ)*(base60) + (177971657713/62500000000 : ℝ)*(major_s0_0) + (177971657713/62500000000 : ℝ)*(major_s0_1) + (1672264922093/1000000000000 : ℝ)*(major_s0_2) + (10791531/125000000000 : ℝ)*(sp_s0_9) + (4499553349927/1000000000000 : ℝ)*(sp_s0_14) + (727585331323/200000000000 : ℝ)*(sp_s0_15) + (2462558723051/1000000000000 : ℝ)*(sp_s0_16) + (414940439559/1000000000000 : ℝ)*(sp_s0_20) + (384608161719/250000000000 : ℝ)*(f.failure) + (727585331323/200000000000 : ℝ)*(f.sum) + (4513301440531729/10000000000000000000000000000 : ℝ)*base62 + (5634153956736629/10000000000000000000000000000 : ℝ)*base65 + (193591683650011/625000000000000000000000000 : ℝ)*base67 + (7147247687775297/10000000000000000000000000000 : ℝ)*base68 + (562480778493061/10000000000000000000000000000 : ℝ)*base71 + (302419644775011/625000000000000000000000000 : ℝ)*base73 + (164877161265223/625000000000000000000000000 : ℝ)*base75 + (261653982890223/625000000000000000000000000 : ℝ)*base76 + (40823773087511/312500000000000000000000000 : ℝ)*base79 + (8293/12500000000000000 : ℝ)*base87 + (8293/12500000000000000 : ℝ)*base89 + (4207/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(19849/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(19849/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (57299279553362556223797/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55109806277/20000000000 : ℝ)*(base1) + (304423426287/250000000000 : ℝ)*(base7) + (1204884040419/1000000000000 : ℝ)*(base40) + (515004790539/1000000000000 : ℝ)*(base50) + (215060236021/1000000000000 : ℝ)*(base60) + (2846369254911/1000000000000 : ℝ)*(major_s0_0) + (2846369254911/1000000000000 : ℝ)*(major_s0_1) + (2846369254911/1000000000000 : ℝ)*(major_s0_2) + (35636749/1000000000000 : ℝ)*(sp_s0_1) + (1249669/50000000000 : ℝ)*(sp_s0_2) + (22895561/500000000000 : ℝ)*(sp_s0_9) + (1554724079977/250000000000 : ℝ)*(sp_s0_21) + (3463370369309/1000000000000 : ℝ)*(sp_s0_22) + (692667044311/200000000000 : ℝ)*(sp_s0_23) + (768898304351/500000000000 : ℝ)*(f.failure) + (1731703003029/500000000000 : ℝ)*(f.sum) + (1144143482806619/5000000000000000000000000000 : ℝ)*base62 + (2473886046044183/10000000000000000000000000000 : ℝ)*base65 + (7179708682044183/10000000000000000000000000000 : ℝ)*base66 + (2049625155806619/10000000000000000000000000000 : ℝ)*base68 + (2534576291574599/5000000000000000000000000000 : ℝ)*base70 + (58195798955817/10000000000000000000000000000 : ℝ)*base73 + (2059597218806619/10000000000000000000000000000 : ℝ)*base74 + (4382650176193381/10000000000000000000000000000 : ℝ)*base76 + (1768206982544183/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (3003/25000000000000000 : ℝ)*base86 + (3003/25000000000000000 : ℝ)*base88 + (3003/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (21009/50000 : ℝ) ^ (79/16 : ℝ) ≤ (138264972822030937/10000000000000000000 : ℝ) := by
    have hpowers : (21009/50000 : ℝ)^79 ≤ (138264972822030937/10000000000000000000 : ℝ)^16 := by
      have hnat : (21009 : ℕ)^79*10000000000000000000^16 ≤ 138264972822030937^16*50000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21009 50000 138264972822030937 10000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21009/50000 : ℝ)) (X := (138264972822030937/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (10138264972822030937/10000000000000000000 : ℝ) ≤ (5013924957872361/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (10138264972822030937/10000000000000000000 : ℝ)^16 ≤ (5013924957872361/5000000000000000 : ℝ)^79 := by
      have hnat : (10138264972822030937 : ℕ)^16*5000000000000000^79 ≤ 5013924957872361^79*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10138264972822030937 10000000000000000000 5013924957872361 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013924957872361/5000000000000000 : ℝ)) (X := (10138264972822030937/10000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5138264972822030937/5000000000000000000 : ℝ) ≤ (5027699284488149/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (5138264972822030937/5000000000000000000 : ℝ)^16 ≤ (5027699284488149/5000000000000000 : ℝ)^79 := by
      have hnat : (5138264972822030937 : ℕ)^16*5000000000000000^79 ≤ 5027699284488149^79*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5138264972822030937 5000000000000000000 5027699284488149 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027699284488149/5000000000000000 : ℝ)) (X := (5138264972822030937/5000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(13924957872361/2100900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3443581653947/525225000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (21009/50000 : ℝ)) (alpha := (13924957872361/2100900000000000 : ℝ)) (beta := (3443581653947/525225000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (21009/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(13924957872361/2100900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3443581653947/525225000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (62999/100000 : ℝ) ^ (79/16 : ℝ) ≤ (5107165481567939539/50000000000000000000 : ℝ) := by
    have hpowers : (62999/100000 : ℝ)^79 ≤ (5107165481567939539/50000000000000000000 : ℝ)^16 := by
      have hnat : (62999 : ℕ)^79*50000000000000000000^16 ≤ 5107165481567939539^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62999 100000 5107165481567939539 50000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62999/100000 : ℝ)) (X := (5107165481567939539/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (55107165481567939539/50000000000000000000 : ℝ) ≤ (10198928462442853/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (55107165481567939539/50000000000000000000 : ℝ)^16 ≤ (10198928462442853/10000000000000000 : ℝ)^79 := by
      have hnat : (55107165481567939539 : ℕ)^16*10000000000000000^79 ≤ 10198928462442853^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55107165481567939539 50000000000000000000 10198928462442853 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10198928462442853/10000000000000000 : ℝ)) (X := (55107165481567939539/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (30107165481567939539/25000000000000000000 : ℝ) ≤ (5191828712850443/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (30107165481567939539/25000000000000000000 : ℝ)^16 ≤ (5191828712850443/5000000000000000 : ℝ)^79 := by
      have hnat : (30107165481567939539 : ℕ)^16*5000000000000000^79 ≤ 5191828712850443^79*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30107165481567939539 25000000000000000000 5191828712850443 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5191828712850443/5000000000000000 : ℝ)) (X := (30107165481567939539/25000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(198928462442853/6299900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(184728963258033/6299900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (62999/100000 : ℝ)) (alpha := (198928462442853/6299900000000000 : ℝ)) (beta := (184728963258033/6299900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (62999/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(198928462442853/6299900000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(184728963258033/6299900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (19849/50000 : ℝ) ^ (79/16 : ℝ) ≤ (130566003440023897/12500000000000000000 : ℝ) := by
    have hpowers : (19849/50000 : ℝ)^79 ≤ (130566003440023897/12500000000000000000 : ℝ)^16 := by
      have hnat : (19849 : ℕ)^79*12500000000000000000^16 ≤ 130566003440023897^16*50000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19849 50000 130566003440023897 12500000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19849/50000 : ℝ)) (X := (130566003440023897/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (12630566003440023897/12500000000000000000 : ℝ) ≤ (2505266859299281/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (12630566003440023897/12500000000000000000 : ℝ)^16 ≤ (2505266859299281/2500000000000000 : ℝ)^79 := by
      have hnat : (12630566003440023897 : ℕ)^16*2500000000000000^79 ≤ 2505266859299281^79*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12630566003440023897 12500000000000000000 2505266859299281 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505266859299281/2500000000000000 : ℝ)) (X := (12630566003440023897/12500000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (6380566003440023897/6250000000000000000 : ℝ) ≤ (10041961910928873/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (6380566003440023897/6250000000000000000 : ℝ)^16 ≤ (10041961910928873/10000000000000000 : ℝ)^79 := by
      have hnat : (6380566003440023897 : ℕ)^16*10000000000000000^79 ≤ 10041961910928873^79*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6380566003440023897 6250000000000000000 10041961910928873 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10041961910928873/10000000000000000 : ℝ)) (X := (6380566003440023897/6250000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(5266859299281/992450000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(20894473731749/3969800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (19849/50000 : ℝ)) (alpha := (5266859299281/992450000000000 : ℝ)) (beta := (20894473731749/3969800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (19849/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(5266859299281/992450000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(20894473731749/3969800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-207059387/500000000 : ℝ)*X 0 0+(-1035296933/2500000000 : ℝ)*X 0 1+(4141187731/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((207059387/500000000 : ℝ)*X 1 0+(1035296933/2500000000 : ℝ)*X 1 1+(4141187731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((207059387/500000000 : ℝ)*X 2 0+(-1035296933/2500000000 : ℝ)*X 2 1+(-4141187731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319009_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-202641/25000 : ℝ) < ((-92547/50000 : ℝ)*P 0+(-92547/50000 : ℝ)*P 1+(-92547/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-202641/25000 : ℝ) < (-115036813818171937486389372537/14489770000000000000000000000 : ℝ) := by norm_num
    linear_combination (136096634907/500000000000 : ℝ)*(base1) + (58929199867/1000000000000 : ℝ)*(base3) + (668877530319/1000000000000 : ℝ)*(base6) + (447/500000000000 : ℝ)*(base13) + (650419811103/1000000000000 : ℝ)*(base40) + (302120949447/500000000000 : ℝ)*(base50) + (68751696187/1000000000000 : ℝ)*(base59) + (39278845147/62500000000 : ℝ)*(base60) + (92547/50000 : ℝ)*(major_s1_0) + (92547/50000 : ℝ)*(major_s1_1) + (92547/50000 : ℝ)*(major_s1_2) + (314154396183/100000000000 : ℝ)*(sp_s1_0) + (2928279899929/1000000000000 : ℝ)*(sp_s1_1) + (286935069291/100000000000 : ℝ)*(sp_s1_2) + (286935069291/100000000000 : ℝ)*(f.sum) + (37297828723117/72448850000000000000000000 : ℝ)*base63 + (862730612589/4962250000000000000000000 : ℝ)*base64 + (11708424331773/62999000000000000000000000 : ℝ)*base67 + (70973335679248027/9924500000000000000000000 : ℝ)*base68 + (79154035873177079/347506367500000000000000000000 : ℝ)*base70 + (24939621406297/70030000000000000000000000 : ℝ)*base72 + (1003700203617/3149950000000000000000000 : ℝ)*base75 + (225310324509/1750750000000000000000000 : ℝ)*base77 + (41859294724215837/441181997000000000000000000000 : ℝ)*base79 + (447/62500000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p019_b003 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 8 ≤ c.val) (hhi : c.val < 10)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=8 ∨ c=9 := by omega
  rcases hc with rfl|rfl
  · exact collision_c319008 p hpa (by linarith only [hpb]) X hX
  · exact collision_c319009 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (c : Fin 88) (hlo : 8 ≤ c.val) (hhi : c.val < 10)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p019_b003 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
