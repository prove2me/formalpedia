-- Prove2me | solution 1 for OAI.Balanced.Selection.Process.exists_uniformConcentratedPath_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:17:22.74809+00:00
-- url     : https://prove2.me/submissions/53ad7f97-b4b5-47a8-9b6e-d20e300b268d

import Mathlib
import Definitions.Def_OAIQ63Br003

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_BernoulliTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Finset

namespace Balanced
open scoped _root_.Balanced

variable {Index Sample : Type*}

lemma esymm_cons_succ (x : ℝ) (s : Multiset ℝ) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map,
    Multiset.sum_map_mul_left]

lemma factorial_mul_esymm_le_sum_pow (s : Multiset ℝ)
    (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) :
    (k.factorial : ℝ) * s.esymm k ≤ s.sum ^ k := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
      cases k <;> simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | @cons x s ih =>
      have hx : 0 ≤ x := hs x (by simp)
      have hs' : ∀ y ∈ s, 0 ≤ y := fun y hy => hs y (by simp [hy])
      have hsum : 0 ≤ s.sum := Multiset.sum_nonneg hs'
      cases k with
      | zero => simp [Multiset.esymm]
      | succ k =>
          rw [esymm_cons_succ, Multiset.sum_cons]
          have h₁ := ih hs' (k + 1)
          have h₂ := mul_le_mul_of_nonneg_left (ih hs' k)
            (mul_nonneg (Nat.cast_nonneg (k + 1)) hx)
          have hb := pow_add_mul_le_add_pow hsum (by positivity : 0 ≤ 2 * s.sum + x) (k + 1)
          simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h₁ ⊢
          simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at hb h₂
          rw [add_comm x s.sum]
          nlinarith [hb]

lemma sum_prod_powersetCard_le (s : Finset Index) (p : Index → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (k : ℕ) :
    (∑ t ∈ s.powersetCard k, ∏ i ∈ t, p i) ≤ (∑ i ∈ s, p i) ^ k / k.factorial := by
  have h := factorial_mul_esymm_le_sum_pow (s.val.map p) (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    exact hp i hi) k
  rw [Finset.esymm_map_val] at h
  simp only [Finset.sum_map_val] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < k.factorial)).2
  simpa [mul_comm] using h

lemma pow_div_factorial_le_exp_ratio (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) (hk : 0 < k) :
    μ ^ k / k.factorial ≤ (Real.exp 1 * μ / k) ^ k := by
  have hk₀ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  calc
    μ ^ k / k.factorial = (μ / k) ^ k * ((k : ℝ) ^ k / k.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ (μ / k) ^ k * Real.exp (k : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k)
        (pow_nonneg (div_nonneg hμ (Nat.cast_nonneg k)) k)
    _ = (Real.exp 1 * μ / k) ^ k := by
      rw [show Real.exp (k : ℝ) = Real.exp 1 ^ k by simp [← Real.exp_nat_mul],
        ← mul_pow]
      congr 1
      ring

open MeasureTheory ProbabilityTheory

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_BoundedDriftCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

lemma condExp_exp_le_of_abs_le [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Y : Ω → ℝ} {a : ℝ}
    (ha : 0 < a) (hY : StronglyMeasurable[mΩ] Y)
    (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ a) (hzero : μ[Y | m] =ᵐ[μ] 0) (θ : ℝ) :
    μ[fun ω ↦ exp (θ * Y ω) | m] ≤ᵐ[μ]
      fun _ ↦ exp (a ^ 2 * θ ^ 2 / 2) := by
  have hIcc : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (-a) a := by
    filter_upwards [hb] with ω hω using abs_le.mp hω
  have hYi : Integrable Y μ := Integrable.of_mem_Icc (-a) a (hY.measurable.aemeasurable (μ := μ)) hIcc
  have hEi : Integrable (fun ω ↦ exp (θ * Y ω)) μ :=
    integrable_exp_mul_of_mem_Icc (hY.measurable.aemeasurable (μ := μ)) hIcc
  let b : ℝ := sinh (a * θ) / a
  have hlin : Integrable (fun ω ↦ cosh (a * θ) + b * Y ω) μ :=
    (integrable_const _).add (hYi.const_mul b)
  have hpoint : (fun ω ↦ exp (θ * Y ω)) ≤ᵐ[μ]
      fun ω ↦ cosh (a * θ) + b * Y ω := by
    filter_upwards [hb] with ω hω
    have hdiv : |Y ω / a| ≤ 1 := by
      rw [abs_div, abs_of_pos ha, div_le_one ha]
      exact hω
    have he := exp_mul_le_cosh_add_mul_sinh hdiv (a * θ)
    convert he using 1
    · congr 1
      field_simp
    · dsimp [b]
      ring
  have hmono := condExp_mono (m := m) hEi hlin hpoint
  have hlinear : μ[fun ω ↦ cosh (a * θ) + b * Y ω | m] =ᵐ[μ]
      fun _ ↦ cosh (a * θ) := by
    have hAdd := condExp_add (integrable_const (cosh (a * θ))) (hYi.const_mul b) m
    have hMul := condExp_smul (μ := μ) b Y m
    filter_upwards [hAdd, hMul, hzero] with ω hA hM hZ
    change μ[fun ω ↦ b * Y ω | m] ω = b * μ[Y | m] ω at hM
    change μ[Y | m] ω = 0 at hZ
    simp only [Pi.add_def] at hA
    simpa only [condExp_const hm, hM, hZ, mul_zero, add_zero] using hA
  filter_upwards [hmono, hlinear] with ω hM hL
  rw [hL] at hM
  exact hM.trans (by simpa only [mul_pow] using cosh_le_exp_half_sq (a * θ))

lemma subGaussian_add_of_bounded_difference [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X Y : Ω → ℝ} {c : ℝ≥0} {a : ℝ}
    (hX : HasSubgaussianMGF X c μ) (hXm : StronglyMeasurable[m] X)
    (ha : 0 < a) (hY : StronglyMeasurable[mΩ] Y)
    (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ a) (hzero : μ[Y | m] =ᵐ[μ] 0) :
    HasSubgaussianMGF (X + Y) (c + NNReal.mk (a ^ 2) (sq_nonneg a)) μ := by
  have hEY (θ : ℝ) : Integrable (fun ω ↦ exp (θ * Y ω)) μ := by
    apply integrable_exp_mul_of_mem_Icc (hY.measurable.aemeasurable (μ := μ))
    filter_upwards [hb] with ω hω using abs_le.mp hω
  have hProd (θ : ℝ) : Integrable
      ((fun ω ↦ exp (θ * X ω)) * fun ω ↦ exp (θ * Y ω)) μ := by
    apply (hX.integrable_exp_mul θ).mul_bdd (hEY θ).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    calc
      θ * Y ω ≤ |θ * Y ω| := le_abs_self _
      _ = |θ| * |Y ω| := abs_mul _ _
      _ ≤ |θ| * a := mul_le_mul_of_nonneg_left hω (abs_nonneg _)
  refine ⟨?_, ?_⟩
  · intro θ
    simpa only [Pi.add_apply, mul_add, exp_add, Pi.mul_def] using hProd θ
  · intro θ
    have hPull := condExp_mul_of_stronglyMeasurable_left
      (f := fun ω ↦ exp (θ * X ω)) (g := fun ω ↦ exp (θ * Y ω))
      (by exact continuous_exp.comp_stronglyMeasurable (hXm.const_mul θ))
      (hProd θ) (hEY θ)
    have hPullInt : Integrable
        ((fun ω ↦ exp (θ * X ω)) * μ[fun ω ↦ exp (θ * Y ω) | m]) μ :=
      integrable_condExp.congr hPull
    have hcond := condExp_exp_le_of_abs_le hm ha hY hb hzero θ
    calc
      mgf (X + Y) μ θ = ∫ ω, exp (θ * X ω) * exp (θ * Y ω) ∂μ := by
        simp only [mgf, Pi.add_apply, mul_add, exp_add]
      _ = ∫ ω, exp (θ * X ω) * μ[fun ω ↦ exp (θ * Y ω) | m] ω ∂μ := by
        change (∫ ω, ((fun ω ↦ exp (θ * X ω)) * fun ω ↦ exp (θ * Y ω)) ω ∂μ) = _
        rw [← integral_condExp hm]
        exact integral_congr_ae hPull
      _ ≤ ∫ ω, exp (θ * X ω) * exp (a ^ 2 * θ ^ 2 / 2) ∂μ := by
        apply integral_mono_ae hPullInt ((hX.integrable_exp_mul θ).mul_const _)
        filter_upwards [hcond] with ω hω
        exact mul_le_mul_of_nonneg_left hω (exp_nonneg _)
      _ = mgf X μ θ * exp (a ^ 2 * θ ^ 2 / 2) := by rw [integral_mul_const]; rfl
      _ ≤ exp ((c : ℝ) * θ ^ 2 / 2) * exp (a ^ 2 * θ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right (hX.mgf_le θ) (exp_nonneg _)
      _ = exp (((c + NNReal.mk (a ^ 2) (sq_nonneg a) : ℝ≥0) : ℝ) * θ ^ 2 / 2) := by
        rw [← exp_add]
        congr 1
        change (c : ℝ) * θ ^ 2 / 2 + a ^ 2 * θ ^ 2 / 2 = ((c : ℝ) + a ^ 2) * θ ^ 2 / 2
        ring

lemma subGaussian_sum_of_bounded_differences [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (n : ℕ)
    (hY : ∀ j < n, StronglyMeasurable[ℱ (j + 1)] (Y j))
    (hb : ∀ j < n, ∀ᵐ ω ∂μ, |Y j ω| ≤ a)
    (hzero : ∀ j < n, μ[Y j | ℱ j] =ᵐ[μ] 0) :
    HasSubgaussianMGF (fun ω ↦ ∑ j ∈ Finset.range n, Y j ω)
      ((n : ℝ≥0) * NNReal.mk (a ^ 2) (sq_nonneg a)) μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun j hj ↦ hY j (by omega))
      (fun j hj ↦ hb j (by omega)) (fun j hj ↦ hzero j (by omega))
    have hsum : StronglyMeasurable[ℱ n] (fun ω ↦ ∑ j ∈ Finset.range n, Y j ω) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      exact (hY j (by omega)).mono (ℱ.mono (by omega))
    have hnext := subGaussian_add_of_bounded_difference (ℱ.le n) hprev hsum ha
      ((hY n (by omega)).mono (ℱ.le (n + 1))) (hb n (by omega)) (hzero n (by omega))
    simpa only [Finset.sum_range_succ, Pi.add_def, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul] using hnext

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CenteredIncrements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {Y : Ω → ℝ} {L : ℝ}

theorem integrable_of_abs_le (hY : AEMeasurable Y μ)
    (hbound : ∀ᵐ ω ∂μ, |Y ω| ≤ L) : Integrable Y μ := by
  apply Integrable.of_mem_Icc (-L) L hY
  filter_upwards [hbound] with ω hω using abs_le.mp hω

omit [IsFiniteMeasure μ] in

theorem abs_sub_condExp_le (hbound : ∀ᵐ ω ∂μ, |Y ω| ≤ L) :
    ∀ᵐ ω ∂μ, |Y ω - μ[Y | m] ω| ≤ 2 * L := by
  have hc := ae_bdd_abs_condExp_of_ae_bdd_abs (m := m) hbound
  filter_upwards [hbound, hc] with ω hω hcω
  calc
    |Y ω - μ[Y | m] ω| ≤ |Y ω| + |μ[Y | m] ω| := abs_sub _ _
    _ ≤ L + L := add_le_add hω hcω
    _ = 2 * L := by ring

theorem condExp_sub_condExp_eq_zero (hm : m ≤ mΩ) (hYi : Integrable Y μ) :
    μ[fun ω ↦ Y ω - μ[Y | m] ω | m] =ᵐ[μ] 0 := by
  have hsub := condExp_sub hYi (integrable_condExp (f := Y) (m := m)) m
  have hfix : μ[μ[Y | m] | m] = μ[Y | m] :=
    condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp integrable_condExp
  simpa only [Pi.sub_def, hfix, sub_self] using hsub

variable {X : ℕ → Ω → ℝ} {ℱ : Filtration ℕ mΩ}

omit [IsFiniteMeasure μ] in

theorem stronglyMeasurable_centered_increment_of_measurable (j : ℕ)
    (hj : StronglyMeasurable[ℱ j] (X j))
    (hj1 : StronglyMeasurable[ℱ (j + 1)] (X (j + 1))) :
    StronglyMeasurable[ℱ (j + 1)] (fun ω ↦ X (j + 1) ω - X j ω -
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω) := by
  exact (hj1.sub (hj.mono (ℱ.mono (Nat.le_succ j)))).sub
    (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_succ j)))

theorem sum_centered_increments_eq (X : ℕ → Ω → ℝ) (ℱ : Filtration ℕ mΩ)
    (μ : Measure Ω) (t : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range t, (X (j + 1) ω - X j ω -
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω)) =
    X t ω - X 0 ω - ∑ j ∈ Finset.range t,
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω := by
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun j ↦ X j ω)]

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SubGaussianTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X : Ω → ℝ} {c : ℝ≥0}

lemma subGaussian_abs_tail [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (2 * c)) := by
  have hset : {ω | u ≤ |X ω|} = {ω | u ≤ X ω} ∪ {ω | u ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    rw [le_abs]
  rw [hset]
  calc
    μ.real ({ω | u ≤ X ω} ∪ {ω | u ≤ -X ω}) ≤
        μ.real {ω | u ≤ X ω} + μ.real {ω | u ≤ -X ω} := measureReal_union_le _ _
    _ ≤ exp (-u ^ 2 / (2 * c)) + exp (-u ^ 2 / (2 * c)) :=
      add_le_add (h.measure_ge_le hu) (h.neg.measure_ge_le hu)
    _ = _ := by ring

lemma subGaussian_mono_parameter (h : HasSubgaussianMGF X c μ)
    {d : ℝ≥0} (hcd : c ≤ d) : HasSubgaussianMGF X d μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le θ := (h.mgf_le θ).trans (by
    apply exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (c : ℝ) ≤ d from hcd) (sq_nonneg θ))
      (by norm_num))

lemma subGaussian_abs_tail_of_parameter_le [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) {v u : ℝ} (hv : 0 ≤ v)
    (hcv : (c : ℝ) ≤ v) (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (2 * v)) := by
  exact subGaussian_abs_tail
    (subGaussian_mono_parameter h (d := ⟨v, hv⟩) hcv) hu

lemma subGaussian_abs_tail_horizon [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) {t T : ℕ} (htT : t ≤ T)
    {L u : ℝ} (hct : (c : ℝ) ≤ 4 * t * L ^ 2) (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (8 * T * L ^ 2)) := by
  have hv : 0 ≤ 4 * (T : ℝ) * L ^ 2 := by positivity
  have hcv : (c : ℝ) ≤ 4 * (T : ℝ) * L ^ 2 := hct.trans (by
    gcongr)
  have hb := subGaussian_abs_tail_of_parameter_le h hv hcv hu
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_BoundedDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal

namespace Balanced
open scoped _root_.Balanced

universe u

theorem boundedDriftConcentration_proof : BoundedDriftConcentration.{u} := by
  intro Ω mΩ μ hμ ℱ X T L hT hL hX hbound u hu t ht
  let Y : ℕ → Ω → ℝ := fun j ω ↦ X (j + 1) ω - X j ω -
    μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω
  have hmeas (j : ℕ) (hj : j < t) : StronglyMeasurable[ℱ (j + 1)] (Y j) := by
    exact stronglyMeasurable_centered_increment_of_measurable j
      (hX j (by omega)) (hX (j + 1) (by omega))
  have hb (j : ℕ) (hj : j < t) : ∀ᵐ ω ∂μ, |Y j ω| ≤ 2 * L :=
    abs_sub_condExp_le (hbound j (by omega))
  have hz (j : ℕ) (hj : j < t) : μ[Y j | ℱ j] =ᵐ[μ] 0 := by
    apply condExp_sub_condExp_eq_zero (ℱ.le j)
    apply integrable_of_abs_le
      ((((hX (j + 1) (by omega)).mono (ℱ.le (j + 1))).sub
        ((hX j (by omega)).mono (ℱ.le j))).measurable.aemeasurable)
      (hbound j (by omega))
  have hmgf := subGaussian_sum_of_bounded_differences
    (μ := μ) (ℱ := ℱ) (Y := Y) (by positivity : 0 < 2 * L) t hmeas hb hz
  have hp : (((t : ℝ≥0) * ⟨(2 * L) ^ 2, sq_nonneg (2 * L)⟩ : ℝ≥0) : ℝ)
      ≤ 4 * (t : ℝ) * L ^ 2 := by
    change (t : ℝ) * (2 * L) ^ 2 ≤ 4 * (t : ℝ) * L ^ 2
    nlinarith
  have htail := subGaussian_abs_tail_horizon hmgf ht hp hu.le
  simpa only [Y, sum_centered_increments_eq] using htail

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_DriftUnionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Real Filter
open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}

lemma measureReal_le_of_ae_imp {A B : Set Ω}
    (h : ∀ᵐ ω ∂μ, ω ∈ A → ω ∈ B) : μ.real A ≤ μ.real B := by
  exact ENNReal.toReal_mono (measure_ne_top μ B) (measure_mono_ae h)

theorem upper_tail_of_accumulated_drift_bound
    (X : ℕ → Ω → ℝ) (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
    (hX : ∀ j ≤ T, StronglyMeasurable[ℱ j] (X j))
    (hbound : ∀ j < T, ∀ᵐ ω ∂μ, |X (j + 1) ω - X j ω| ≤ L)
    (u : ℝ) (hu : 0 < u) (t : ℕ) (ht : t ≤ T) (D : ℝ)
    (hD : ∀ᵐ ω ∂μ, (∑ j ∈ Finset.range t,
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω) ≤ D) :
    μ.real {ω | D + u ≤ X t ω - X 0 ω} ≤
      2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  apply le_trans (measureReal_le_of_ae_imp ?_)
    (boundedDriftConcentration_proof μ ℱ X T L hT hL hX hbound u hu t ht)
  filter_upwards [hD] with ω hd hω
  exact (by linarith : u ≤ X t ω - X 0 ω - ∑ j ∈ Finset.range t,
    μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω).trans (le_abs_self _)

theorem abs_tail_of_accumulated_drift_bound
    (X : ℕ → Ω → ℝ) (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
    (hX : ∀ j ≤ T, StronglyMeasurable[ℱ j] (X j))
    (hbound : ∀ j < T, ∀ᵐ ω ∂μ, |X (j + 1) ω - X j ω| ≤ L)
    (u : ℝ) (hu : 0 < u) (t : ℕ) (ht : t ≤ T) (D : ℝ)
    (hD : ∀ᵐ ω ∂μ, |∑ j ∈ Finset.range t,
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω| ≤ D) :
    μ.real {ω | D + u ≤ |X t ω - X 0 ω|} ≤
      2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  apply le_trans (measureReal_le_of_ae_imp ?_)
    (boundedDriftConcentration_proof μ ℱ X T L hT hL hX hbound u hu t ht)
  filter_upwards [hD] with ω hd hω
  have htriangle := abs_add_le (X t ω - X 0 ω - ∑ j ∈ Finset.range t,
    μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω)
    (∑ j ∈ Finset.range t, μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω)
  simp only [sub_add_cancel] at htriangle
  linarith

theorem simultaneous_upper_tail_of_drift_bound
    {ι : Type*} [Fintype ι] (X : ι → ℕ → Ω → ℝ)
    (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
    (hX : ∀ i j, j ≤ T → StronglyMeasurable[ℱ j] (X i j))
    (hbound : ∀ i j, j < T → ∀ᵐ ω ∂μ, |X i (j + 1) ω - X i j ω| ≤ L)
    (u : ℝ) (hu : 0 < u) (D : ι → ℕ → ℝ)
    (hD : ∀ i t, t ≤ T → ∀ᵐ ω ∂μ, (∑ j ∈ Finset.range t,
      μ[fun ω ↦ X i (j + 1) ω - X i j ω | ℱ j] ω) ≤ D i t) :
    μ.real {ω | ∃ i t, t ≤ T ∧ D i t + u ≤ X i t ω - X i 0 ω} ≤
      2 * Fintype.card ι * (T + 1 : ℕ) * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  let E : ι × Fin (T + 1) → Set Ω := fun p ↦
    {ω | D p.1 p.2 + u ≤ X p.1 p.2 ω - X p.1 0 ω}
  have heq : {ω | ∃ i t, t ≤ T ∧ D i t + u ≤ X i t ω - X i 0 ω} = ⋃ p, E p := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, t, ht, hω⟩
      exact ⟨⟨i, ⟨t, Nat.lt_succ_iff.mpr ht⟩⟩, hω⟩
    · rintro ⟨⟨i, t⟩, hω⟩
      exact ⟨i, t, Nat.lt_succ_iff.mp t.isLt, hω⟩
  rw [heq]
  calc
    μ.real (⋃ p, E p) ≤ ∑ p, μ.real (E p) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _p : ι × Fin (T + 1), 2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact upper_tail_of_accumulated_drift_bound (X p.1) T L hT hL
        (hX p.1) (hbound p.1) u hu p.2 (Nat.lt_succ_iff.mp p.2.isLt)
        (D p.1 p.2) (hD p.1 p.2 (Nat.lt_succ_iff.mp p.2.isLt))
    _ = _ := by simp; ring

theorem simultaneous_abs_tail_of_drift_bound
    {ι : Type*} [Fintype ι] (X : ι → ℕ → Ω → ℝ)
    (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
    (hX : ∀ i j, j ≤ T → StronglyMeasurable[ℱ j] (X i j))
    (hbound : ∀ i j, j < T → ∀ᵐ ω ∂μ, |X i (j + 1) ω - X i j ω| ≤ L)
    (u : ℝ) (hu : 0 < u) (D : ι → ℕ → ℝ)
    (hD : ∀ i t, t ≤ T → ∀ᵐ ω ∂μ, |∑ j ∈ Finset.range t,
      μ[fun ω ↦ X i (j + 1) ω - X i j ω | ℱ j] ω| ≤ D i t) :
    μ.real {ω | ∃ i t, t ≤ T ∧ D i t + u ≤ |X i t ω - X i 0 ω|} ≤
      2 * Fintype.card ι * (T + 1 : ℕ) * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  let E : ι × Fin (T + 1) → Set Ω := fun p ↦
    {ω | D p.1 p.2 + u ≤ |X p.1 p.2 ω - X p.1 0 ω|}
  have heq : {ω | ∃ i t, t ≤ T ∧ D i t + u ≤ |X i t ω - X i 0 ω|} = ⋃ p, E p := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, t, ht, hω⟩
      exact ⟨⟨i, ⟨t, Nat.lt_succ_iff.mpr ht⟩⟩, hω⟩
    · rintro ⟨⟨i, t⟩, hω⟩
      exact ⟨i, t, Nat.lt_succ_iff.mp t.isLt, hω⟩
  rw [heq]
  calc
    μ.real (⋃ p, E p) ≤ ∑ p, μ.real (E p) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _p : ι × Fin (T + 1), 2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact abs_tail_of_accumulated_drift_bound (X p.1) T L hT hL
        (hX p.1) (hbound p.1) u hu p.2 (Nat.lt_succ_iff.mp p.2.isLt)
        (D p.1 p.2) (hD p.1 p.2 (Nat.lt_succ_iff.mp p.2.isLt))
    _ = _ := by simp; ring

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteHistory
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

namespace Balanced.FiniteHistory

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma measurable_stepObservable (n : ℕ) (f : Prefix S n → S → ℝ) :
    Measurable (stepObservable n f) := by
  have hm : Measurable (fun ω : Path S => (frestrictLe n ω, ω (n + 1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  exact (measurable_of_countable (Function.uncurry f)).comp hm

lemma integrable_stepObservable (n : ℕ) (f : Prefix S n → S → ℝ)
    (ν : Measure (Path S)) [IsFiniteMeasure ν] : Integrable (stepObservable n f) ν := by
  have hmap : Measurable (fun ω : Path S => (frestrictLe n ω, ω (n + 1))) :=
    (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  have hi : Integrable (Function.uncurry f)
      (ν.map (fun ω : Path S => (frestrictLe n ω, ω (n + 1)))) := .of_finite
  exact hi.comp_measurable hmap

lemma map_next_traj (step : ℕ → S → PMF S) (n : ℕ) (h : Prefix S n) :
    (Kernel.traj (X := fun _ => S) (historyKernel step) n h).map (fun ω : Path S => ω (n + 1)) =
      (step n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure := by
  rw [← Kernel.map_apply _ (measurable_pi_apply (n + 1)), Kernel.map_traj_succ_self]
  rfl

lemma integral_stepObservable_traj (step : ℕ → S → PMF S) (n : ℕ)
    (h : Prefix S n) (f : Prefix S n → S → ℝ) :
    (∫ ω, stepObservable n f ω ∂Kernel.traj (X := fun _ => S) (historyKernel step) n h) =
      ∑ s, (step n (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) s).toReal * f h s := by
  rw [Kernel.integral_traj h (measurable_stepObservable n f).stronglyMeasurable.aestronglyMeasurable]
  have hfreeze (ω : Path S) :
      stepObservable n f (Function.updateFinset ω (Finset.Iic n) h) = f h (ω (n + 1)) := by
    have hp : frestrictLe n (Function.updateFinset ω (Finset.Iic n) h) = h := by
      funext j
      simp [frestrictLe, Function.updateFinset, j.property]
    simp [stepObservable, hp, Function.updateFinset]
  simp_rw [hfreeze]
  rw [← integral_map (measurable_pi_apply (n + 1)).aemeasurable
    (measurable_of_countable (f h)).stronglyMeasurable.aestronglyMeasurable,
    map_next_traj, PMF.integral_eq_sum]
  rfl

theorem condExp_stepObservable (step : ℕ → S → PMF S) (s₀ : S)
    (n : ℕ) (f : Prefix S n → S → ℝ) :
    (pathLaw step s₀)[stepObservable n f | filtration n] =ᵐ[pathLaw step s₀]
      fun ω => ∑ s, (step n (ω n) s).toReal * f (frestrictLe n ω) s := by
  have h := Kernel.condExp_traj (X := fun _ => S) (κ := historyKernel step) (Nat.zero_le n)
    (x₀ := fun _ => s₀) (integrable_stepObservable n f (pathLaw step s₀))
  filter_upwards [h] with ω hω
  change (pathLaw step s₀)[stepObservable n f | filtration n] ω = _ at hω ⊢
  rw [hω, integral_stepObservable_traj]
  rfl

theorem map_prefix_pathLaw (step : ℕ → S → PMF S) (s₀ : S) (n : ℕ) :
    (pathLaw step s₀).map (frestrictLe n) =
      Kernel.partialTraj (X := fun _ => S) (historyKernel step) 0 n (fun _ => s₀) :=
  Kernel.traj_map_frestrictLe_apply (X := fun _ => S) (κ := historyKernel step) 0 n (fun _ => s₀)

theorem map_prefix_next_pathLaw (step : ℕ → S → PMF S) (s₀ : S) (n : ℕ) :
    (pathLaw step s₀).map (fun ω : Path S => (frestrictLe n ω, ω (n + 1))) =
      ((pathLaw step s₀).map (frestrictLe n)) ⊗ₘ historyKernel step n := by
  rw [map_prefix_pathLaw]
  exact (Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ => S) (κ := historyKernel step) (x₀ := fun _ => s₀) (Nat.zero_le n)).symm

end Balanced.FiniteHistory

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteHistoryInvariant
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter Finset Preorder
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.FiniteHistory

variable {S : Type*} [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

theorem ae_pmf_nonzero (p : PMF S) : ∀ᵐ s ∂p.toMeasure, p s ≠ 0 := by
  rw [ae_iff]
  change p.toMeasure p.supportᶜ = 0
  exact (p.toMeasure_apply_eq_zero_iff MeasurableSet.of_discrete).2
    disjoint_compl_right

theorem ae_initial_state (step : ℕ → S → PMF S) (s₀ : S) :
    ∀ᵐ ω ∂pathLaw step s₀, ω 0 = s₀ := by
  have hp : (pathLaw step s₀).map (frestrictLe 0) =
      Measure.dirac (fun _ : Iic 0 ↦ s₀) := by
    rw [map_prefix_pathLaw, Kernel.partialTraj_self, Kernel.id_apply]
  have hi : ∀ᵐ h ∂(pathLaw step s₀).map (frestrictLe 0),
      h ⟨0, mem_Iic.mpr le_rfl⟩ = s₀ := by
    rw [hp]
    exact (ae_dirac_iff MeasurableSet.of_discrete).2 rfl
  exact ae_of_ae_map (by fun_prop) hi

theorem ae_step_support (step : ℕ → S → PMF S) (s₀ : S) (n : ℕ) :
    ∀ᵐ ω ∂pathLaw step s₀, step n (ω n) (ω (n + 1)) ≠ 0 := by
  have hp : ∀ᵐ z ∂((pathLaw step s₀).map (frestrictLe n)) ⊗ₘ historyKernel step n,
      step n (z.1 ⟨n, mem_Iic.mpr le_rfl⟩) z.2 ≠ 0 := by
    apply Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete
    apply Eventually.of_forall
    intro h
    exact ae_pmf_nonzero (step n (h ⟨n, mem_Iic.mpr le_rfl⟩))
  rw [← map_prefix_next_pathLaw] at hp
  exact ae_of_ae_map (f := fun ω : Path S ↦ (frestrictLe n ω, ω (n + 1)))
    (by fun_prop) hp

theorem ae_all_invariant (step : ℕ → S → PMF S) (s₀ : S)
    (P : ℕ → S → Prop) (h₀ : P 0 s₀)
    (hstep : ∀ n s t, step n s t ≠ 0 → P n s → P (n + 1) t) :
    ∀ᵐ ω ∂pathLaw step s₀, ∀ n, P n (ω n) := by
  filter_upwards [ae_initial_state step s₀,
    ae_all_iff.2 (fun n ↦ ae_step_support step s₀ n)] with ω hi hs
  intro n
  induction n with
  | zero => simpa only [hi] using h₀
  | succ n ih => exact hstep n (ω n) (ω (n + 1)) (hs n) ih

end Balanced.FiniteHistory

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_LogTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace BalancedRyser

theorem polynomial_mul_ratio_pow_le_inv
    (q r B : ℕ) (C : ℝ) (hq : 0 < q) (hBpos : 0 < B)
    (hC : 0 ≤ C) (hlog : Real.log (q : ℝ) ≤ (B : ℝ))
    (hlarge : C * Real.exp ((r : ℝ) + 1) ≤ (B : ℝ)) :
    (q : ℝ) ^ r * (C / (B : ℝ)) ^ B ≤ (q : ℝ)⁻¹ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hbase : C / (B : ℝ) ≤ Real.exp (-((r : ℝ) + 1)) := by
    rw [Real.exp_neg]
    apply (div_le_iff₀ hBR).2
    simpa [div_eq_mul_inv, mul_comm] using
      ((le_div_iff₀ (Real.exp_pos ((r : ℝ) + 1))).2 hlarge)
  have hpow : (C / (B : ℝ)) ^ B ≤
      Real.exp (-((r : ℝ) + 1)) ^ B :=
    pow_le_pow_left₀ (div_nonneg hC hBR.le) hbase B
  calc
    (q : ℝ) ^ r * (C / (B : ℝ)) ^ B
        ≤ (q : ℝ) ^ r * Real.exp (-((r : ℝ) + 1)) ^ B :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg hqR.le _)
    _ = Real.exp ((r : ℝ) * Real.log (q : ℝ) - ((r : ℝ) + 1) * B) := by
      have hqpow : (q : ℝ) ^ r = Real.exp ((r : ℝ) * Real.log (q : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hqR]
      rw [hqpow, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log (q : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith
    _ = (q : ℝ)⁻¹ := by rw [Real.exp_neg, Real.exp_log hqR]

end BalancedRyser

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_RescaledDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {X Y : Ω → ℝ}

theorem rescaled_increment_identity {x y a b : ℝ} (hb : b ≠ 0) :
    y / b - x / a = ((y - x) + x * (1 - b / a)) / b := by
  field_simp
  ring

theorem abs_rescaled_increment_le
    {x y a b L Q δ smin : ℝ}
    (hjump : |y - x| ≤ L) (hx : |x| ≤ Q)
    (hscale : |1 - b / a| ≤ δ) (hsmin : 0 < smin) (hb : smin ≤ b) :
    |y / b - x / a| ≤ (L + Q * δ) / smin := by
  have hbpos : 0 < b := hsmin.trans_le hb
  have hL : 0 ≤ L := (abs_nonneg _).trans hjump
  have hQ : 0 ≤ Q := (abs_nonneg _).trans hx
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hscale
  rw [rescaled_increment_identity hbpos.ne', abs_div, abs_of_pos hbpos]
  calc
    |y - x + x * (1 - b / a)| / b
        ≤ (|y - x| + |x| * |1 - b / a|) / b := by
          gcongr
          simpa only [abs_mul] using abs_add_le (y - x) (x * (1 - b / a))
    _ ≤ (L + Q * δ) / b := by gcongr
    _ ≤ (L + Q * δ) / smin :=
      div_le_div_of_nonneg_left (add_nonneg hL (mul_nonneg hQ hδ)) hsmin hb

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SimultaneousDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators Topology

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem selection_azuma_exponent {q C : ℝ} (hq : 0 < q) (hC : 0 < C) :
    (q ^ ((4 : ℝ) / 5) / 2) ^ 2 /
      (8 * (3 * q) * (C * q ^ ((1 : ℝ) / 8)) ^ 2) =
      q ^ ((7 : ℝ) / 20) / (96 * C ^ 2) := by
  have h80 : (q ^ ((4 : ℝ) / 5)) ^ 2 = q ^ ((8 : ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    norm_num
  have h18 : (q ^ ((1 : ℝ) / 8)) ^ 2 = q ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    norm_num
  have hfactor : q ^ ((8 : ℝ) / 5) = q ^ ((7 : ℝ) / 20) * q * q ^ ((1 : ℝ) / 4) := by
    calc
      _ = q ^ (((7 : ℝ) / 20 + 1) + (1 : ℝ) / 4) := by norm_num
      _ = _ := by rw [Real.rpow_add hq, Real.rpow_add hq, Real.rpow_one]
  have hqp : q ^ ((1 : ℝ) / 4) ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  rw [div_pow, mul_pow, h80, h18, hfactor]
  field_simp
  ring

theorem tendsto_nat_pow_mul_exp_neg_rpow (m : ℕ) {r c : ℝ}
    (hr : 0 < r) (hc : 0 < c) :
    Tendsto (fun q : ℕ ↦ (q : ℝ) ^ m * exp (-c * (q : ℝ) ^ r)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((m : ℝ) / r) c hc).comp
    ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  congr 1
  change (q : ℝ) ^ m = ((q : ℝ) ^ r) ^ ((m : ℝ) / r)
  have he : r * ((m : ℝ) / r) = (m : ℝ) := by field_simp
  rw [← Real.rpow_mul (Nat.cast_nonneg q), he, Real.rpow_natCast]

theorem tendsto_selection_simultaneous_error (A : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun q : ℕ ↦ A * (q : ℝ) ^ 3 * exp (-c * (q : ℝ) ^ ((7 : ℝ) / 20)))
      atTop (𝓝 0) := by
  simpa only [mul_zero, mul_assoc] using
    (tendsto_nat_pow_mul_exp_neg_rpow 3 (by norm_num : 0 < (7 : ℝ) / 20) hc).const_mul A

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_TailProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.TailProduct

open scoped BigOperators

theorem neg_log_one_sub_le_twice {x : ℝ} (hx : 0 ≤ x) (hhalf : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hp : 0 < 1 - x := by linarith
  have hi : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    apply (sub_le_iff_le_add).2
    apply (inv_le_iff_one_le_mul₀ hp).2
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hl
  exact hl.trans hi

end Balanced.TailProduct

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ThinningTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace Balanced.BernoulliTail

lemma tendsto_polynomial_mul_ratio_tail (B : ℕ → ℕ)
    (hB : Tendsto (fun q => (B q : ℝ)) atTop atTop)
    (hlog : ∀ᶠ q : ℕ in atTop, Real.log (q : ℝ) ≤ (B q : ℝ))
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ r * (C / (B q : ℝ)) ^ B q)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun q => by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hlog,
      hB.eventually (eventually_gt_atTop 0),
      hB.eventually (eventually_ge_atTop (C * Real.exp ((r : ℝ) + 1)))]
      with q hq hl hpos hlarge
    have hBn : 0 < B q := by exact_mod_cast hpos
    exact BalancedRyser.polynomial_mul_ratio_pow_le_inv q r (B q) C hq hBn hC hl hlarge
  · exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

lemma rpow_lt_thinningCutoff (β : ℝ) (q : ℕ) :
    (q : ℝ) ^ β < (thinningCutoff β q : ℝ) := by
  simpa [thinningCutoff] using Nat.lt_floor_add_one ((q : ℝ) ^ β)

lemma tendsto_thinningCutoff_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun q : ℕ => (thinningCutoff β q : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun q => (rpow_lt_thinningCutoff β q).le)
  exact (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop

lemma eventually_log_le_thinningCutoff {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ q : ℕ in atTop, Real.log (q : ℝ) ≤ (thinningCutoff β q : ℝ) := by
  have h := ((isLittleO_log_rpow_atTop hβ).comp_tendsto
    tendsto_natCast_atTop_atTop).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h] with q hq
  have hnorm : |Real.log (q : ℝ)| ≤ (q : ℝ) ^ β := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) β)] using hq
  exact (le_abs_self _).trans (hnorm.trans (rpow_lt_thinningCutoff β q).le)

lemma tendsto_polynomial_mul_thinning_tail {β : ℝ} (hβ : 0 < β)
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ r *
      (C / (thinningCutoff β q : ℝ)) ^ thinningCutoff β q) atTop (𝓝 0) :=
  tendsto_polynomial_mul_ratio_tail (thinningCutoff β)
    (tendsto_thinningCutoff_atTop hβ) (eventually_log_le_thinningCutoff hβ) r C hC

end Balanced.BernoulliTail

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionCensoring
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] [Fintype V] in
theorem mem_currentVertices_update_iff (G : Input I V) (S : State I V)
    (i : I) (w v : V) (flags : V → Bool) :
    v ∈ currentVertices G (update G S i w flags) ↔
      v ∈ currentVertices G S ∧ ¬ G.graph.Adj w v ∧
        flags v = false ∧ G.slot v ≠ i := by
  simp only [currentVertices, update, survivors, Finset.mem_filter,
    Finset.mem_erase]
  tauto

omit [Fintype I] [Fintype V] in

theorem currentVertices_update_subset (G : Input I V) (S : State I V)
    (i : I) (w : V) (flags : V → Bool) :
    currentVertices G (update G S i w flags) ⊆ currentVertices G S := by
  intro v hv
  exact (mem_currentVertices_update_iff G S i w v flags).mp hv |>.1

theorem exceptional_not_mem_currentVertices_update
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : State I V) {i : I} {w v : V} (flags : V → Bool)
    (hw : w ∈ domain G S i) (hex : w ∈ G.exceptional v) :
    v ∉ currentVertices G (update G S i w flags) := by
  intro hv
  obtain ⟨_, hconflict, _, hslot⟩ :=
    (mem_currentVertices_update_iff G S i w v flags).mp hv
  have hwi : G.slot w = i := (Finset.mem_filter.mp hw).2
  rcases hG.2.2.2.2.2.2.2 v w hex with hadj | heq
  · exact hconflict hadj.symm
  · exact hslot (heq.trans hwi)

omit [Fintype I] in
theorem postcheck_of_performedResult_some {q : ℕ} {G : Input I V}
    {S S' : State I V} {r : Noise I V}
    (h : performedResult q G S r = some S') :
    Postcheck q G S r.2.1 r.2.2 := by
  by_contra hn
  simp [performedResult, hn] at h

omit [Fintype I] in
theorem update_eq_of_performedResult_some {q : ℕ} {G : Input I V}
    {S S' : State I V} {r : Noise I V}
    (h : performedResult q G S r = some S') :
    update G S r.1 r.2.1 r.2.2 = S' := by
  simpa [performedResult, postcheck_of_performedResult_some h] using h

theorem relevant_successor_uncensored
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    {S S' : State I V} {r : Noise I V} {v : V}
    (hw : r.2.1 ∈ domain G S r.1)
    (hout : performedResult q G S r = some S')
    (hv : v ∈ currentVertices G S') :
    r.2.1 ∉ G.exceptional v ∧
      (((thinned G S r.2.1 r.2.2) ∩ neighbors G v).card : ℝ) ≤
        (q : ℝ) ^ (1 / 8 : ℝ) := by
  have heq := update_eq_of_performedResult_some hout
  have hv' : v ∈ currentVertices G (update G S r.1 r.2.1 r.2.2) := heq ▸ hv
  refine ⟨fun hex => exceptional_not_mem_currentVertices_update hG S r.2.2 hw hex hv', ?_⟩
  exact (postcheck_of_performedResult_some hout).2 v
    (currentVertices_update_subset G S r.1 r.2.1 r.2.2 hv')

omit [Fintype I] in

theorem domain_loss_le_conflicts_add_thinning (G : Input I V) (S : State I V)
    {i : I} (hi : i ∈ S.remaining) (w : V) (flags : V → Bool) :
    ((domain G S i).card : ℝ) -
      (((survivors G S w flags) ∩ domain G S i).card : ℝ) ≤
      (((neighbors G w) ∩ domain G S i).card : ℝ) +
        (((thinned G S w flags) ∩ domain G S i).card : ℝ) := by
  have hcover : domain G S i ⊆
      (survivors G S w flags ∩ domain G S i) ∪
      (neighbors G w ∩ domain G S i) ∪
      (thinned G S w flags ∩ domain G S i) := by
    intro u hu
    have hua : u ∈ S.alive := (Finset.mem_filter.mp hu).1
    have hui : G.slot u = i := (Finset.mem_filter.mp hu).2
    have huc : u ∈ currentVertices G S := by simp [currentVertices, hua, hui, hi]
    by_cases hadj : G.graph.Adj w u
    · simp [hu, neighbors, hadj]
    · cases hflag : flags u <;> simp [hu, survivors, thinned, huc, hadj, hflag]
  have hc := (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hc' : ((domain G S i).card : ℝ) ≤
      (((survivors G S w flags) ∩ domain G S i).card : ℝ) +
      (((neighbors G w) ∩ domain G S i).card : ℝ) +
      (((thinned G S w flags) ∩ domain G S i).card : ℝ) := by
    exact_mod_cast hc
  linarith

theorem domain_loss_le_two_mul_rpow
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : State I V) {i : I} (hi : i ∈ S.remaining) (w : V) (flags : V → Bool)
    (hthin : (((thinned G S w flags) ∩ domain G S i).card : ℝ) ≤
      (q : ℝ) ^ (1 / 8 : ℝ)) :
    ((domain G S i).card : ℝ) -
      (((survivors G S w flags) ∩ domain G S i).card : ℝ) ≤
      2 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  have hsub : (neighbors G w) ∩ domain G S i ⊆
      (neighbors G w) ∩ slotVertices G i := by
    intro u hu
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hu).1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp (Finset.mem_inter.mp hu).2).2⟩⟩
  have hc : (((neighbors G w) ∩ domain G S i).card : ℝ) ≤
      (q : ℝ) ^ (1 / 8 : ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hG.2.2.2.2.1 w i)
  have hloss := domain_loss_le_conflicts_add_thinning G S hi w flags
  linarith

omit [Fintype I] in

theorem degree_loss_le_three_counts (G : Input I V) (S : State I V)
    (i : I) (w v : V) (flags : V → Bool) :
    (degree G S v : ℝ) - (degree G (update G S i w flags) v : ℝ) ≤
      (((neighbors G v) ∩ neighbors G w).card : ℝ) +
      (((thinned G S w flags) ∩ neighbors G v).card : ℝ) +
      (((neighbors G v) ∩ slotVertices G i).card : ℝ) := by
  have hcover : neighbors G v ∩ currentVertices G S ⊆
      (neighbors G v ∩ currentVertices G (update G S i w flags)) ∪
      (neighbors G v ∩ neighbors G w) ∪
      (thinned G S w flags ∩ neighbors G v) ∪
      (neighbors G v ∩ slotVertices G i) := by
    intro u hu
    obtain ⟨huv, huc⟩ := Finset.mem_inter.mp hu
    by_cases hadj : G.graph.Adj w u
    · have huw : u ∈ neighbors G w := by simp [neighbors, hadj]
      simp [huv, huw]
    · by_cases hslot : G.slot u = i
      · simp [huv, slotVertices, hslot]
      · cases hflag : flags u
        · have hun : u ∈ currentVertices G (update G S i w flags) :=
            (mem_currentVertices_update_iff G S i w u flags).mpr
              ⟨huc, hadj, hflag, hslot⟩
          simp [huv, hun]
        · have hut : u ∈ thinned G S w flags := by
            simp [thinned, huc, hadj, hflag]
          simp [huv, hut]
  have hc := (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
  have hc' : (degree G S v : ℝ) ≤
      (degree G (update G S i w flags) v : ℝ) +
      (((neighbors G v) ∩ neighbors G w).card : ℝ) +
      (((thinned G S w flags) ∩ neighbors G v).card : ℝ) +
      (((neighbors G v) ∩ slotVertices G i).card : ℝ) := by
    exact_mod_cast hc
  linarith

theorem degree_loss_le_three_mul_rpow
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : State I V) (i : I) (w v : V) (flags : V → Bool)
    (hex : w ∉ G.exceptional v)
    (hthin : (((thinned G S w flags) ∩ neighbors G v).card : ℝ) ≤
      (q : ℝ) ^ (1 / 8 : ℝ)) :
    (degree G S v : ℝ) - (degree G (update G S i w flags) v : ℝ) ≤
      3 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  have hconflict := hG.2.2.2.2.2.2.1 v w hex
  have hslot := hG.2.2.2.2.1 v i
  have hloss := degree_loss_le_three_counts G S i w v flags
  linarith

omit [Fintype I] in

theorem degree_update_le (G : Input I V) (S : State I V)
    (i : I) (w v : V) (flags : V → Bool) :
    degree G (update G S i w flags) v ≤ degree G S v := by
  apply Finset.card_le_card
  exact Finset.inter_subset_inter_left (currentVertices_update_subset G S i w flags)

theorem abs_degree_update_sub_le_three_mul_rpow
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : State I V) (i : I) (w v : V) (flags : V → Bool)
    (hex : w ∉ G.exceptional v)
    (hthin : (((thinned G S w flags) ∩ neighbors G v).card : ℝ) ≤
      (q : ℝ) ^ (1 / 8 : ℝ)) :
    |(degree G (update G S i w flags) v : ℝ) - (degree G S v : ℝ)| ≤
      3 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  rw [abs_sub_comm, abs_of_nonneg
    (sub_nonneg.mpr (Nat.cast_le.mpr (degree_update_le G S i w v flags)))]
  exact degree_loss_le_three_mul_rpow hG S i w v flags hex hthin

omit [Fintype I] [Fintype V] in

theorem domain_update_eq_survivors_inter_domain (G : Input I V) (S : State I V)
    {i j : I} (hij : j ≠ i) (w : V) (flags : V → Bool) :
    domain G (update G S i w flags) j = survivors G S w flags ∩ domain G S j := by
  ext v
  simp only [domain, update, survivors, currentVertices, Finset.mem_filter,
    Finset.mem_inter]
  constructor
  · rintro ⟨⟨⟨⟨ha, hr⟩, hc, hf⟩, hne⟩, heq⟩
    exact ⟨⟨⟨ha, hr⟩, hc, hf⟩, ha, heq⟩
  · rintro ⟨⟨⟨ha, hr⟩, hc, hf⟩, _, heq⟩
    exact ⟨⟨⟨⟨ha, hr⟩, hc, hf⟩, fun h => hij (heq.symm.trans h)⟩, heq⟩

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical

namespace Balanced.SelectionThinning

noncomputable section

variable {V Ω : Type*} [Fintype V] [Fintype Ω]

lemma thinning_false_mass (rate : V → ℝ) (u : V) :
    (∑ b : V → Bool, if b u = false then thinningMass rate b else 0) = 1 - rate u := by
  have hprod (b : V → Bool) :
      (if b u = false then thinningMass rate b else 0) =
        ∏ v, bitMass (rate v) (b v) *
          (if v = u then (if b v = false then 1 else 0) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    by_cases h : b u = false <;> simp [h, thinningMass]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun v (b : Bool) => bitMass (rate v) b *
    (if v = u then (if b = false then 1 else 0) else 1))]
  have hsum (v : V) :
      (∑ b : Bool, bitMass (rate v) b *
        (if v = u then (if b = false then 1 else 0) else 1)) =
      if v = u then 1 - rate v else 1 := by
    by_cases h : v = u <;> simp [h, bitMass]
  simp_rw [hsum]
  simp

lemma equal_survival {α r : ℝ} (hr : r < 1) :
    (1 - r) * (1 - thinningRate α r) = 1 - α := by
  unfold thinningRate
  have hden : 1 - r ≠ 0 := by linarith
  field_simp
  ring

lemma surviving_event_mass (p : Ω → ℝ) (rate : V → ℝ)
    (E : Ω → Prop) (u : V) :
    (∑ ω, ∑ b : V → Bool,
      if E ω ∧ b u = false then jointMass p rate ω b else 0) =
      eventMass p E * (1 - rate u) := by
  have hinner (ω : Ω) :
      (∑ b : V → Bool, if E ω ∧ b u = false then jointMass p rate ω b else 0) =
      (if E ω then p ω else 0) * (1 - rate u) := by
    by_cases h : E ω
    · simp only [h, true_and, jointMass, ite_true]
      calc
        _ = ∑ b : V → Bool, p ω * (if b u = false then thinningMass rate b else 0) := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : b u = false <;> simp [hb]
        _ = p ω * ∑ b : V → Bool, (if b u = false then thinningMass rate b else 0) :=
          (Finset.mul_sum ..).symm
        _ = _ := by rw [thinning_false_mass]
    · simp [h]
  simp_rw [hinner]
  exact (Finset.sum_mul ..).symm

lemma eventMass_compl (p : Ω → ℝ) (hp : ∑ ω, p ω = 1) (E : Ω → Prop) :
    eventMass p (fun ω => ¬ E ω) = 1 - eventMass p E := by
  have h (ω : Ω) : (if ¬ E ω then p ω else 0) = p ω - (if E ω then p ω else 0) := by
    by_cases h : E ω <;> simp [h]
  unfold eventMass
  calc
    _ = ∑ ω, (p ω - (if E ω then p ω else 0)) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases he : E ω <;> simp [he]
    _ = _ := by rw [Finset.sum_sub_distrib, hp]

end
end Balanced.SelectionThinning

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionProcessLaw
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotMeasurableSingletonClass _root_.OAI.Balanced.Selection.Process.snapshotMeasurableSpace _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

theorem transitionWeight_eq_draw_pushforward (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Option (State I V)) :
    transitionWeight p q t G before out =
      ∑ draw, if advance q G before draw = out then drawStepWeight p q t G before draw else 0 := by
  cases before with
  | none =>
    by_cases ho : out = none <;> simp [transitionWeight, advance, drawStepWeight, ho, eq_comm]
  | some S =>
    by_cases hp : Precheck p q t G S
    · simp [transitionWeight, stepWeight, drawStepWeight, advance, hp, Fintype.sum_option]
    · by_cases ho : out = none <;>
        simp [transitionWeight, stepWeight, drawStepWeight, advance, hp, ho, Fintype.sum_option, eq_comm]

theorem snapshotPMF_apply_real (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) :
    (snapshotPMF p q t G before out).toReal = snapshotWeight p q t G before out :=
  ENNReal.toReal_ofReal (snapshotWeight_nonnegative p q t G before out)

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped MeasureTheory ProbabilityTheory BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

theorem condExp_snapshot_step (p : Parameters) (q : ℕ) (G : Input I V) (t : ℕ)
    (f : FiniteHistory.Prefix (Snapshot I V) t → Snapshot I V → ℝ) :
    (snapshotPathLaw p q G)[FiniteHistory.stepObservable t f | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ out, snapshotWeight p q t G (ω t) out * f (frestrictLe t ω) out := by
  have h := FiniteHistory.condExp_stepObservable
    (fun n => snapshotPMF p q n G) (initialSnapshot (I := I) (V := V)) t f
  simpa only [snapshotPathLaw, snapshotFiltration, snapshotPMF_apply_real] using h

theorem sum_snapshotWeight_response (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Snapshot I V) (f : Snapshot I V → ℝ) :
    (∑ out, snapshotWeight p q t G before out * f out) =
      ∑ draw, drawStepWeight p q t G before.1 draw *
        f (advance q G before.1 draw, draw) := by
  simp only [Snapshot, Fintype.sum_prod_type, snapshotWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro draw _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem condExp_retained_draw (p : Parameters) (q : ℕ) (G : Input I V) (t : ℕ)
    (f : FiniteHistory.Prefix (Snapshot I V) t → Option (Noise I V) → ℝ) :
    (snapshotPathLaw p q G)[
      FiniteHistory.stepObservable t (fun h out => f h out.2) | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ draw, drawStepWeight p q t G (ω t).1 draw *
          f (frestrictLe t ω) draw := by
  have h := condExp_snapshot_step p q G t (fun h out => f h out.2)
  filter_upwards [h] with ω hω
  rw [hω, sum_snapshotWeight_response]

theorem sum_drawStepWeight_of_precheck (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (f : Option (Noise I V) → ℝ) :
    (∑ draw, drawStepWeight p q t G (some S) draw * f draw) =
      ∑ r : Noise I V, noiseWeight p q G S r * f (some r) := by
  simp [Fintype.sum_option, drawStepWeight, hp]

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionState
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotMeasurableSingletonClass _root_.OAI.Balanced.Selection.Process.snapshotMeasurableSpace _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

private theorem exists_positive_of_sum_positive {α : Type*} [Fintype α]
    (f : α → ℝ) (h : 0 < ∑ a, f a) : ∃ a, 0 < f a := by
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge (Finset.sum_nonpos (fun a _ => hn a))) h

theorem initialState_invariant (G : Input I V) : StateInvariant G initialState := by
  simp [StateInvariant, initialState]

omit [Fintype I] [Fintype V] in
theorem update_invariant (G : Input I V) (S : State I V) (hS : StateInvariant G S)
    (i : I) (w : V) (_hi : i ∈ S.remaining) (hw : w ∈ domain G S i)
    (flags : V → Bool) : StateInvariant G (update G S i w flags) := by
  have hwalive : w ∈ S.alive := (Finset.mem_filter.mp hw).1
  have hwslot : G.slot w = i := (Finset.mem_filter.mp hw).2
  have halive {v : V} (hv : v ∈ (update G S i w flags).alive) :
      v ∈ S.alive ∧ ¬ G.graph.Adj w v := by
    have hsurv := (Finset.mem_filter.mp hv).1
    have hc := Finset.mem_filter.mp hsurv
    exact ⟨(Finset.mem_filter.mp hc.1).1, hc.2.1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hsurv := (Finset.mem_filter.mp hv).1
    have hneq := (Finset.mem_filter.mp hv).2
    have hcurrent := (Finset.mem_filter.mp hsurv).1
    exact Finset.mem_erase.mpr ⟨hneq, (Finset.mem_filter.mp hcurrent).2⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simp [update]
    · simp [update, hj, hS.2.1 j]
  · intro j v hrec
    by_cases hj : j = i
    · subst j
      have heq : w = v := by simpa only [update, Function.update_self, Option.some.injEq] using hrec
      simpa only [← heq] using hwslot
    · exact hS.2.2.1 j v (by simpa [update, hj] using hrec)
  · intro j k v u hjrec hkrec hjk
    by_cases hj : j = i
    · subst j
      have hk : k ≠ i := Ne.symm hjk
      have hv : w = v := by simpa only [update, Function.update_self, Option.some.injEq] using hjrec
      have hkold : S.recorded k = some u := by simpa [update, hk] using hkrec
      intro hadj
      exact hS.2.2.2.2 k u hkold w hwalive (by simpa only [hv] using hadj.symm)
    · by_cases hk : k = i
      · subst k
        have hu : w = u := by simpa only [update, Function.update_self, Option.some.injEq] using hkrec
        have hjold : S.recorded j = some v := by simpa [update, hj] using hjrec
        simpa only [hu] using hS.2.2.2.2 j v hjold w hwalive
      · exact hS.2.2.2.1 j k v u (by simpa [update, hj] using hjrec)
          (by simpa [update, hk] using hkrec) hjk
  · intro j u hrec v hv
    by_cases hj : j = i
    · subst j
      have hu : w = u := by simpa only [update, Function.update_self, Option.some.injEq] using hrec
      simpa only [hu] using (halive hv).2
    · exact hS.2.2.2.2 j u (by simpa [update, hj] using hrec) v (halive hv).1

theorem positive_stepWeight_exists_update (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V)
    (hpos : 0 < stepWeight p q t G S (some S')) :
    ∃ r : Noise I V, r.1 ∈ S.remaining ∧ r.2.1 ∈ domain G S r.1 ∧
      update G S r.1 r.2.1 r.2.2 = S' := by
  by_cases hp : Precheck p q t G S
  · simp only [stepWeight, hp, ite_true] at hpos
    obtain ⟨r, hr⟩ := exists_positive_of_sum_positive _ hpos
    split at hr
    · rename_i hresult
      have hvalid : r.1 ∈ S.remaining ∧ r.2.1 ∈ domain G S r.1 := by
        by_contra h
        simp only [noiseWeight, drawWeight, h, ite_false, zero_mul, lt_self_iff_false] at hr
      have hup : update G S r.1 r.2.1 r.2.2 = S' := by
        unfold performedResult at hresult
        split at hresult
        · exact Option.some.inj hresult
        · contradiction
      exact ⟨r, hvalid.1, hvalid.2, hup⟩
    · exact False.elim (lt_irrefl 0 hr)
  · simp [stepWeight, hp] at hpos

theorem positive_stepWeight_invariant (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (hS : StateInvariant G S)
    (hpos : 0 < stepWeight p q t G S (some S')) : StateInvariant G S' := by
  obtain ⟨r, hi, hw, hup⟩ := positive_stepWeight_exists_update p q t G S S' hpos
  rw [← hup]
  exact update_invariant G S hS r.1 r.2.1 hi hw r.2.2

theorem positive_stepWeight_card (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (hpos : 0 < stepWeight p q t G S (some S')) :
    S'.remaining.card + 1 = S.remaining.card := by
  obtain ⟨r, hi, _, hup⟩ := positive_stepWeight_exists_update p q t G S S' hpos
  rw [← hup]
  exact Finset.card_erase_add_one hi

theorem sum_snapshotWeight_state (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Snapshot I V) (out : Option (State I V)) :
    (∑ draw, snapshotWeight p q t G before (out, draw)) =
      transitionWeight p q t G before.1 out := by
  rw [transitionWeight_eq_draw_pushforward]
  apply Finset.sum_congr rfl
  intro draw _
  simp only [snapshotWeight, eq_comm]

theorem positive_snapshotWeight_transition (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) (hp : 0 < snapshotWeight p q t G before out) :
    0 < transitionWeight p q t G before.1 out.1 := by
  rw [← sum_snapshotWeight_state p q t G before out.1]
  apply hp.trans_le
  exact Finset.single_le_sum (fun draw _ =>
    snapshotWeight_nonnegative p q t G before (out.1, draw)) (Finset.mem_univ out.2)

theorem positive_snapshotWeight_invariant (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (draw draw' : Option (Noise I V))
    (hS : StateInvariant G S)
    (hp : 0 < snapshotWeight p q t G (some S, draw) (some S', draw')) :
    StateInvariant G S' := by
  exact positive_stepWeight_invariant p q t G S S' hS
    (positive_snapshotWeight_transition p q t G _ _ hp)

theorem positive_snapshotWeight_card (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (draw draw' : Option (Noise I V))
    (hp : 0 < snapshotWeight p q t G (some S, draw) (some S', draw')) :
    S'.remaining.card + 1 = S.remaining.card := by
  exact positive_stepWeight_card p q t G S S'
    (positive_snapshotWeight_transition p q t G _ _ hp)

omit [Fintype I] in

theorem snapshotWeight_none_some (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (draw draw' : Option (Noise I V)) :
    snapshotWeight p q t G (none, draw) (some S, draw') = 0 := by
  simp [snapshotWeight, advance]

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionHistoryInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter

namespace Balanced.Selection.Process

variable {I V : Type*} [Fintype I] [Fintype V]

theorem ae_snapshot_state_invariant (p : Parameters) (q : ℕ) (G : Input I V) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t S, (ω t).1 = some S →
      StateInvariant G S ∧ S.remaining.card + t = Fintype.card I := by
  classical
  apply FiniteHistory.ae_all_invariant (fun t => snapshotPMF p q t G)
    initialSnapshot
    (fun t snap => ∀ S, snap.1 = some S →
      StateInvariant G S ∧ S.remaining.card + t = Fintype.card I)
  · intro S hS
    have heq : S = initialState := (Option.some.inj hS).symm
    subst S
    exact ⟨initialState_invariant G, by simp [initialState]⟩
  · intro t before out hpos hbefore S hout
    have hp : 0 < snapshotWeight p q t G before out := by
      have hn : snapshotWeight p q t G before out ≠ 0 := by
        intro hz
        apply hpos
        change ENNReal.ofReal (snapshotWeight p q t G before out) = 0
        rw [hz, ENNReal.ofReal_zero]
      exact lt_of_le_of_ne (snapshotWeight_nonnegative p q t G before out) (Ne.symm hn)
    obtain ⟨before, draw⟩ := before
    obtain ⟨out, draw'⟩ := out
    dsimp only at hout
    subst out
    cases before with
    | none =>
        rw [snapshotWeight_none_some] at hp
        exact False.elim (lt_irrefl 0 hp)
    | some S₀ =>
        obtain ⟨hinv, hcard⟩ := hbefore S₀ rfl
        refine ⟨positive_snapshotWeight_invariant p q t G S₀ S draw draw' hinv hp, ?_⟩
        have hstep := positive_snapshotWeight_card p q t G S₀ S draw draw' hp
        omega

theorem ae_snapshot_remaining_card (p : Parameters) (q : ℕ) (G : Input I V) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t S, (ω t).1 = some S →
      S.remaining.card = Fintype.card I - t := by
  filter_upwards [ae_snapshot_state_invariant p q G] with ω hω
  intro t S hS
  have h := (hω t S hS).2
  omega

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionAuxiliaryTracks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem domainTrack_succ_sub (p : Parameters) (q t : ℕ) (G : Input I V)
    (i : I) (ω : FiniteHistory.Path (Snapshot I V)) :
    domainTrack p q G i (t + 1) ω - domainTrack p q G i t ω =
      domainTrackIncrement p q t G i (ω t).1 (ω (t + 1)).2 := by
  simp [domainTrack, Finset.sum_range_succ]

theorem degreeTrack_succ_sub (p : Parameters) (q t : ℕ) (G : Input I V)
    (v : V) (ω : FiniteHistory.Path (Snapshot I V)) :
    degreeTrack p q G v (t + 1) ω - degreeTrack p q G v t ω =
      degreeTrackIncrement p q t G v (ω t).1 (ω (t + 1)).2 := by
  simp [degreeTrack, Finset.sum_range_succ]

omit [Fintype I] in

theorem positive_snapshot_surviving_step (p : Parameters) (q t : ℕ)
    (G : Input I V) (before out : Snapshot I V) (S' : State I V)
    (hout : out.1 = some S') (hpos : 0 < snapshotWeight p q t G before out) :
    ∃ S r, before.1 = some S ∧ out.2 = some r ∧ Precheck p q t G S ∧
      r.1 ∈ S.remaining ∧ r.2.1 ∈ domain G S r.1 ∧
      performedResult q G S r = some S' := by
  have hadv : out.1 = advance q G before.1 out.2 := by
    by_contra h
    simp [snapshotWeight, h] at hpos
  have hdraw : 0 < drawStepWeight p q t G before.1 out.2 := by
    simpa only [snapshotWeight, hadv, ite_true] using hpos
  cases hb : before.1 with
  | none => simp [hb, advance] at hadv; rw [hout] at hadv; contradiction
  | some S =>
    cases hd : out.2 with
    | none => simp [hd, advance] at hadv; rw [hout] at hadv; contradiction
    | some r =>
      have hpre : Precheck p q t G S := by
        by_contra h
        simp [hb, hd, drawStepWeight, h] at hdraw
      have hn : 0 < noiseWeight p q G S r := by
        simpa [hb, hd, drawStepWeight, hpre] using hdraw
      have hr : r.1 ∈ S.remaining ∧ r.2.1 ∈ domain G S r.1 := by
        by_contra h
        simp [noiseWeight, drawWeight, h] at hn
      exact ⟨S, r, rfl, rfl, hpre, hr.1, hr.2, by
        simpa only [hb, hd, advance, hout] using hadv.symm⟩

theorem ae_snapshot_positive_steps (p : Parameters) (q : ℕ) (G : Input I V) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t,
      0 < snapshotWeight p q t G (ω t) (ω (t + 1)) := by
  apply ae_all_iff.2
  intro t
  have hs := FiniteHistory.ae_step_support (fun n => snapshotPMF p q n G)
    (initialSnapshot (I := I) (V := V)) t
  filter_upwards [hs] with ω hω
  have hn : snapshotWeight p q t G (ω t) (ω (t + 1)) ≠ 0 := by
    intro hz
    apply hω
    change ENNReal.ofReal (snapshotWeight p q t G (ω t) (ω (t + 1))) = 0
    rw [hz, ENNReal.ofReal_zero]
  exact lt_of_le_of_ne (snapshotWeight_nonnegative p q t G _ _) (Ne.symm hn)

theorem domainTrack_agreement_of_positive_steps (p : Parameters) (q : ℕ)
    (G : Input I V) (i : I) (ω : FiniteHistory.Path (Snapshot I V))
    (hzero : ω 0 = initialSnapshot)
    (hstep : ∀ t, 0 < snapshotWeight p q t G (ω t) (ω (t + 1))) :
    ∀ t S, (ω t).1 = some S → i ∈ S.remaining →
      domainTrack p q G i t ω = (domain G S i).card / p.sizeScale q t := by
  intro t
  induction t with
  | zero =>
      intro S hS _
      have heq : S = initialState := by
        simpa only [hzero, initialSnapshot, Option.some.injEq] using hS.symm
      subst S
      simp [Parameters.sizeScale]
  | succ t ih =>
      intro S' hS' hi'
      obtain ⟨S, r, hS, hr, hpre, hri, hrw, hout⟩ :=
        positive_snapshot_surviving_step p q t G (ω t) (ω (t + 1)) S' hS' (hstep t)
      have hup := update_eq_of_performedResult_some hout
      have himem : i ∈ S.remaining.erase r.1 := by
        simpa only [← hup, update] using hi'
      obtain ⟨hine, hi⟩ := Finset.mem_erase.mp himem
      have hthin := (postcheck_of_performedResult_some hout).1 i hi
      have hnum : censoredDomainNumerator q G S r i = (domain G S' i).card := by
        rw [censoredDomainNumerator, ite_eq_right (not_lt_of_ge hthin), ← hup,
          domain_update_eq_survivors_inter_domain G S hine]
      have hprev := ih S hS hi
      have hinc := domainTrack_succ_sub p q t G i ω
      simp only [domainTrackIncrement, hS, hr, hi, ite_true, hnum] at hinc
      linarith

theorem degreeTrack_agreement_of_positive_steps (p : Parameters) (q : ℕ)
    (G : Input I V) (hG : GraphBounds G q p.c p.C) (v : V)
    (ω : FiniteHistory.Path (Snapshot I V)) (hzero : ω 0 = initialSnapshot)
    (hstep : ∀ t, 0 < snapshotWeight p q t G (ω t) (ω (t + 1))) :
    ∀ t S, (ω t).1 = some S → v ∈ currentVertices G S →
      degreeTrack p q G v t ω =
        (degree G S v : ℝ) / p.degreeScale q (Fintype.card I) t := by
  intro t
  induction t with
  | zero =>
      intro S hS _
      have heq : S = initialState := by
        simpa only [hzero, initialSnapshot, Option.some.injEq] using hS.symm
      subst S
      have hn : (Fintype.card I : ℝ) ≠ 0 := by
        rw [hG.1]
        positivity
      simp [Parameters.degreeScale, Parameters.sizeScale, hn]
  | succ t ih =>
      intro S' hS' hv'
      obtain ⟨S, r, hS, hr, hpre, hri, hrw, hout⟩ :=
        positive_snapshot_surviving_step p q t G (ω t) (ω (t + 1)) S' hS' (hstep t)
      have hup := update_eq_of_performedResult_some hout
      have hv : v ∈ currentVertices G S := by
        apply currentVertices_update_subset G S r.1 r.2.1 r.2.2
        simpa only [hup] using hv'
      have hunc := relevant_successor_uncensored hG hrw hout hv'
      have hnum : censoredDegreeNumerator q G S r v = (degree G S' v : ℝ) := by
        rw [censoredDegreeNumerator, ite_eq_right (not_or.mpr
          ⟨hunc.1, not_lt_of_ge hunc.2⟩), hup]
      have hprev := ih S hS hv
      have hinc := degreeTrack_succ_sub p q t G v ω
      simp only [degreeTrackIncrement, hS, hr, hv, ite_true, hnum] at hinc
      linarith

theorem ae_domainTrack_agreement (p : Parameters) (q : ℕ) (G : Input I V) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ i t S,
      (ω t).1 = some S → i ∈ S.remaining →
      domainTrack p q G i t ω = (domain G S i).card / p.sizeScale q t := by
  filter_upwards [FiniteHistory.ae_initial_state (fun t => snapshotPMF p q t G)
    (initialSnapshot (I := I) (V := V)), ae_snapshot_positive_steps p q G] with ω hz hs
  exact fun i => domainTrack_agreement_of_positive_steps p q G i ω hz hs

theorem ae_degreeTrack_agreement (p : Parameters) (q : ℕ) (G : Input I V)
    (hG : GraphBounds G q p.c p.C) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ v t S,
      (ω t).1 = some S → v ∈ currentVertices G S →
      degreeTrack p q G v t ω =
        (degree G S v : ℝ) / p.degreeScale q (Fintype.card I) t := by
  filter_upwards [FiniteHistory.ae_initial_state (fun t => snapshotPMF p q t G)
    (initialSnapshot (I := I) (V := V)), ae_snapshot_positive_steps p q G] with ω hz hs
  exact fun v => degreeTrack_agreement_of_positive_steps p q G hG v ω hz hs

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionAuxiliaryDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators

namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem measurable_snapshot_prefix_response (t : ℕ)
    (f : FiniteHistory.Prefix (Snapshot I V) t → ℝ) :
    Measurable[snapshotFiltration t] (fun ω => f (frestrictLe t ω)) := by
  have hr : Measurable[snapshotFiltration (I := I) (V := V) t] (frestrictLe t) := by
    rw [measurable_iff_comap_le]
    change MeasurableSpace.comap (frestrictLe t) MeasurableSpace.pi ≤
      Filtration.piLE (X := fun _ : ℕ => Snapshot I V) t
    rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_of_countable f).comp hr

theorem stronglyMeasurable_retained_increment (t : ℕ)
    (f : Option (State I V) → Option (Noise I V) → ℝ) :
    StronglyMeasurable[snapshotFiltration (t + 1)]
      (fun ω : FiniteHistory.Path (Snapshot I V) => f (ω t).1 (ω (t + 1)).2) := by
  exact (measurable_snapshot_prefix_response (t + 1)
    (fun h => f (h ⟨t, Finset.mem_Iic.mpr (Nat.le_succ t)⟩).1
      (h ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩).2)).stronglyMeasurable

theorem stronglyMeasurable_domainTrack (p : Parameters) (q : ℕ) (G : Input I V)
    (i : I) (t : ℕ) :
    StronglyMeasurable[snapshotFiltration t] (domainTrack p q G i t) := by
  induction t with
  | zero =>
      have heq : domainTrack p q G i 0 = fun _ => ((domain G initialState i).card : ℝ) :=
        funext (domainTrack_zero p q G i)
      rw [heq]
      exact stronglyMeasurable_const
  | succ t ih =>
      have hsum := (ih.mono (snapshotFiltration.mono (Nat.le_succ t))).add
        (stronglyMeasurable_retained_increment t (domainTrackIncrement p q t G i))
      convert hsum using 1
      all_goals try with_reducible_and_instances rfl
      funext ω
      have h := domainTrack_succ_sub p q t G i ω
      change domainTrack p q G i (t + 1) ω =
        domainTrack p q G i t ω + domainTrackIncrement p q t G i (ω t).1 (ω (t + 1)).2
      linarith

theorem stronglyMeasurable_degreeTrack (p : Parameters) (q : ℕ) (G : Input I V)
    (v : V) (t : ℕ) :
    StronglyMeasurable[snapshotFiltration t] (degreeTrack p q G v t) := by
  induction t with
  | zero =>
      have heq : degreeTrack p q G v 0 = fun _ => (degree G initialState v : ℝ) :=
        funext (degreeTrack_zero p q G v)
      rw [heq]
      exact stronglyMeasurable_const
  | succ t ih =>
      have hsum := (ih.mono (snapshotFiltration.mono (Nat.le_succ t))).add
        (stronglyMeasurable_retained_increment t (degreeTrackIncrement p q t G v))
      convert hsum using 1
      all_goals try with_reducible_and_instances rfl
      funext ω
      have h := degreeTrack_succ_sub p q t G v ω
      change degreeTrack p q G v (t + 1) ω =
        degreeTrack p q G v t ω + degreeTrackIncrement p q t G v (ω t).1 (ω (t + 1)).2
      linarith

theorem condExp_current_retained_response (p : Parameters) (q t : ℕ) (G : Input I V)
    (f : Option (State I V) → Option (Noise I V) → ℝ) :
    (snapshotPathLaw p q G)[fun ω => f (ω t).1 (ω (t + 1)).2 | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ draw, drawStepWeight p q t G (ω t).1 draw * f (ω t).1 draw := by
  exact condExp_retained_draw p q G t
    (fun h draw => f (h ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1 draw)

theorem condExp_domainTrack_increment (p : Parameters) (q t : ℕ) (G : Input I V)
    (i : I) :
    (snapshotPathLaw p q G)[fun ω =>
      domainTrack p q G i (t + 1) ω - domainTrack p q G i t ω | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ draw, drawStepWeight p q t G (ω t).1 draw *
          domainTrackIncrement p q t G i (ω t).1 draw := by
  simp_rw [domainTrack_succ_sub]
  exact condExp_current_retained_response p q t G (domainTrackIncrement p q t G i)

theorem condExp_degreeTrack_increment (p : Parameters) (q t : ℕ) (G : Input I V)
    (v : V) :
    (snapshotPathLaw p q G)[fun ω =>
      degreeTrack p q G v (t + 1) ω - degreeTrack p q G v t ω | snapshotFiltration t]
      =ᵐ[snapshotPathLaw p q G]
        fun ω => ∑ draw, drawStepWeight p q t G (ω t).1 draw *
          degreeTrackIncrement p q t G v (ω t).1 draw := by
  simp_rw [degreeTrack_succ_sub]
  exact condExp_current_retained_response p q t G (degreeTrackIncrement p q t G v)

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced.SelectionScales

private theorem rate_bounds {P : ℝ} {q : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) :
    0 ≤ P / q ∧ P / q ≤ 1 / 2 := by
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  constructor
  · exact div_nonneg hP hqR.le
  · apply (div_le_iff₀ hqR).2
    linarith

theorem domain_bounds {P : ℝ} {q t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) (ht : t ≤ 3 * q) :
    Real.exp (-6 * P) ≤ domain P q t ∧ domain P q t ≤ 1 := by
  obtain ⟨hx, hxhalf⟩ := rate_bounds hP hq hPq
  have hbase : 0 < 1 - P / q := by linarith
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have htR : (t : ℝ) ≤ 3 * q := by exact_mod_cast ht
  constructor
  · rw [domain, ← Real.exp_log (pow_pos hbase t)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    have hlog := Balanced.TailProduct.neg_log_one_sub_le_twice hx hxhalf
    have hmul := mul_le_mul_of_nonneg_left (show -2 * (P / q) ≤
        Real.log (1 - P / q) by linarith) (Nat.cast_nonneg t)
    have htime := mul_le_mul_of_nonpos_right htR (show -2 * (P / q) ≤ 0 by linarith)
    have heq : (3 * (q : ℝ)) * (-2 * (P / q)) = -6 * P := by
      field_simp
      ring
    rw [heq] at htime
    exact htime.trans hmul
  · exact pow_le_one₀ hbase.le (by linarith) (n := t)

theorem domain_pos {P : ℝ} {q t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) :
    0 < domain P q t := by
  obtain ⟨_, hx⟩ := rate_bounds hP hq hPq
  exact pow_pos (by linarith) t

theorem degree_bounds {P a : ℝ} {q n t : ℕ}
    (hP : 0 ≤ P) (ha : 0 ≤ a) (hq : 0 < q) (hn : 0 < n)
    (hPq : 2 * P ≤ q) (hnq : n ≤ 3 * q) (htn : t ≤ n)
    (hremain : a * q ≤ (n - t : ℕ)) :
    Real.exp (-6 * P) * a / 3 ≤ degree P q n t ∧ degree P q n t ≤ 1 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnqR : (n : ℝ) ≤ 3 * q := by exact_mod_cast hnq
  have hremn : ((n - t : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n t
  have hratio : a / 3 ≤ (n - t : ℕ) / (n : ℝ) := by
    apply (le_div_iff₀ hnR).2
    have hprod := mul_le_mul_of_nonneg_left hnqR ha
    nlinarith
  have hratio_one : (n - t : ℕ) / (n : ℝ) ≤ 1 := by
    exact (div_le_one hnR).2 hremn
  have hratio_nonneg : 0 ≤ (n - t : ℕ) / (n : ℝ) := by positivity
  obtain ⟨hdr, hdu⟩ := domain_bounds hP hq hPq (htn.trans hnq)
  change Real.exp (-6 * P) * a / 3 ≤ domain P q t * (n - t : ℕ) / n ∧ _
  rw [mul_div_assoc, mul_div_assoc]
  constructor
  · exact mul_le_mul hdr hratio (by positivity) (domain_pos hP hq hPq).le
  · change domain P q t * (n - t : ℕ) / n ≤ 1
    rw [mul_div_assoc]
    calc
      domain P q t * ((n - t : ℕ) / (n : ℝ)) ≤ 1 * 1 :=
        mul_le_mul hdu hratio_one hratio_nonneg (by norm_num)
      _ = 1 := by ring

theorem domain_succ (P : ℝ) (q t : ℕ) :
    domain P q (t + 1) = (1 - P / q) * domain P q t := by
  simp only [domain, pow_succ, mul_comm]

theorem degree_succ {P : ℝ} {q n t : ℕ} (ht : t < n) :
    degree P q n (t + 1) =
      ((1 - P / q) * (1 - 1 / (n - t : ℕ))) * degree P q n t := by
  have htn : t ≤ n := ht.le
  have htn' : t + 1 ≤ n := ht
  have hrem : (n - t : ℕ) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt ht)
  have hremR : ((n - t : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hrem
  have hstep : ((n - (t + 1) : ℕ) : ℝ) = (n - t : ℕ) - 1 := by
    rw [Nat.cast_sub htn', Nat.cast_sub htn, Nat.cast_add, Nat.cast_one]
    ring
  simp only [degree, domain_succ, hstep]
  field_simp

theorem domain_ratio {P : ℝ} {q t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) :
    domain P q (t + 1) / domain P q t = 1 - P / q := by
  rw [domain_succ, mul_div_cancel_right₀ _ (domain_pos hP hq hPq).ne']

theorem degree_pos {P : ℝ} {q n t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) (ht : t < n) :
    0 < degree P q n t := by
  have hs := domain_pos (t := t) hP hq hPq
  have hh : 0 < ((n - t : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt ht)
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_le t |>.trans_lt ht)
  exact div_pos (mul_pos hs hh) hn

theorem degree_ratio {P : ℝ} {q n t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) (ht : t < n) :
    degree P q n (t + 1) / degree P q n t =
      (1 - P / q) * (1 - 1 / (n - t : ℕ)) := by
  rw [degree_succ ht, mul_div_cancel_right₀ _ (degree_pos hP hq hPq ht).ne']

theorem domain_relative_change {P : ℝ} {q t : ℕ}
    (hP : 0 ≤ P) (hq : 0 < q) (hPq : 2 * P ≤ q) :
    |1 - domain P q (t + 1) / domain P q t| = P / q := by
  rw [domain_ratio hP hq hPq, sub_sub_cancel]
  exact abs_of_nonneg (rate_bounds hP hq hPq).1

theorem degree_relative_change_le {P a : ℝ} {q n t : ℕ}
    (hP : 0 ≤ P) (ha : 0 < a) (hq : 0 < q) (hPq : 2 * P ≤ q)
    (ht : t < n) (hremain : a * q ≤ (n - t : ℕ)) :
    |1 - degree P q n (t + 1) / degree P q n t| ≤ (P + 1 / a) / q := by
  obtain ⟨hx, hxh⟩ := rate_bounds hP hq hPq
  have hx1 : P / q ≤ 1 := by linarith
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hh : 0 < ((n - t : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt ht)
  have hy : 0 ≤ 1 / ((n - t : ℕ) : ℝ) := by positivity
  have hxy := mul_le_mul_of_nonneg_right hx1 hy
  have hnon : 0 ≤ 1 - (1 - P / q) * (1 - 1 / (n - t : ℕ)) := by
    nlinarith
  have hyle : 1 / ((n - t : ℕ) : ℝ) ≤ (1 / a) / q := by
    rw [div_div]
    exact one_div_le_one_div_of_le (mul_pos ha hqR) hremain
  rw [degree_ratio hP hq hPq ht, abs_of_nonneg hnon]
  calc
    1 - (1 - P / q) * (1 - 1 / (n - t : ℕ)) ≤
        P / q + 1 / (n - t : ℕ) := by nlinarith [mul_nonneg hx hy]
    _ ≤ P / q + (1 / a) / q := by linarith [hyle]
    _ = (P + 1 / a) / q := by ring

end Balanced.SelectionScales

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionProcessScales
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process.Parameters

noncomputable section

variable {p : Parameters}

theorem Pstar_pos (hp : p.Admissible) : 0 < p.Pstar := by
  have hc := hp.1
  have hC := hp.2.1
  unfold Pstar
  positivity

theorem a_bounds (hp : p.Admissible) : 0 < p.a ∧ p.a < 1 := by
  exact ⟨hp.2.2.2.2.1, lt_of_lt_of_le hp.2.2.2.2.2 (min_le_left _ _)⟩

theorem tailSlots_le_order (hp : p.Admissible) (q : ℕ) : p.tailSlots q ≤ q := by
  unfold tailSlots
  apply Nat.ceil_le.mpr
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  nlinarith [(a_bounds hp).2]

theorem remaining_ge (hp : p.Admissible) {q n t : ℕ} (hqn : q ≤ n)
    (ht : t ≤ p.lastMainTime q n) : p.a * q ≤ ((n - t : ℕ) : ℝ) := by
  have htail : p.tailSlots q ≤ n := (tailSlots_le_order hp q).trans hqn
  have hrem : p.tailSlots q ≤ n - t := by
    unfold lastMainTime at ht
    omega
  exact (Nat.le_ceil (p.a * q)).trans (by exact_mod_cast hrem)

theorem source_scale_bounds (hp : p.Admissible) {q n t : ℕ}
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hn : n = 2 * (q + 1))
    (ht : t ≤ p.lastMainTime q n) :
    p.smin ≤ p.sizeScale q t ∧ p.sizeScale q t ≤ 1 ∧
      p.smin * p.a / 3 ≤ p.degreeScale q n t ∧ p.degreeScale q n t ≤ 1 := by
  have hqpos : 0 < q := by omega
  have hnpos : 0 < n := by omega
  have hnq : n ≤ 3 * q := by omega
  have hqn : q ≤ n := by omega
  have htn : t ≤ n := ht.trans (Nat.sub_le _ _)
  obtain ⟨hslo, hshi⟩ := SelectionScales.domain_bounds (Pstar_pos hp).le hqpos hPq
    (htn.trans hnq)
  obtain ⟨hblo, hbhi⟩ := SelectionScales.degree_bounds (Pstar_pos hp).le
    (a_bounds hp).1.le hqpos hnpos hPq hnq htn (remaining_ge hp hqn ht)
  exact ⟨hslo, hshi, hblo, hbhi⟩

theorem source_relative_changes (hp : p.Admissible) {q n t : ℕ}
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hn : n = 2 * (q + 1))
    (ht : t + 1 ≤ p.lastMainTime q n) :
    |1 - p.sizeScale q (t + 1) / p.sizeScale q t| = p.Pstar / q ∧
    |1 - p.degreeScale q n (t + 1) / p.degreeScale q n t| ≤
      (p.Pstar + 1 / p.a) / q := by
  have hqpos : 0 < q := by omega
  have hqn : q ≤ n := by omega
  have htn : t < n := (Nat.lt_of_succ_le ht).trans_le (Nat.sub_le _ _)
  constructor
  · exact SelectionScales.domain_relative_change (Pstar_pos hp).le hqpos hPq
  · exact SelectionScales.degree_relative_change_le (Pstar_pos hp).le
      (a_bounds hp).1 hqpos hPq htn (remaining_ge hp hqn (by omega))

theorem source_size_increment_le (hp : p.Admissible) {q n t : ℕ}
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hn : n = 2 * (q + 1))
    (ht : t + 1 ≤ p.lastMainTime q n) {x y L Q : ℝ}
    (hjump : |y - x| ≤ L) (hsize : |x| ≤ Q * q) :
    |y / p.sizeScale q (t + 1) - x / p.sizeScale q t| ≤
      (L + Q * p.Pstar) / p.smin := by
  have hs := (source_scale_bounds hp hq hPq hn ht).1
  have hrel := (source_relative_changes hp hq hPq hn ht).1.le
  have hbound := Balanced.abs_rescaled_increment_le hjump hsize hrel
    (Real.exp_pos (-6 * p.Pstar)) hs
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hnum : Q * (q : ℝ) * (p.Pstar / q) = Q * p.Pstar := by field_simp
  simpa only [hnum, smin] using hbound

theorem source_degree_increment_le (hp : p.Admissible) {q n t : ℕ}
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hn : n = 2 * (q + 1))
    (ht : t + 1 ≤ p.lastMainTime q n) {x y L Q : ℝ}
    (hjump : |y - x| ≤ L) (hsize : |x| ≤ Q * q) :
    |y / p.degreeScale q n (t + 1) - x / p.degreeScale q n t| ≤
      (L + Q * (p.Pstar + 1 / p.a)) / (p.smin * p.a / 3) := by
  have hs := (source_scale_bounds hp hq hPq hn ht).2.2.1
  have hrel := (source_relative_changes hp hq hPq hn ht).2
  have hlo : 0 < p.smin * p.a / 3 := by
    have hsmin : 0 < p.smin := Real.exp_pos _
    have ha := (a_bounds hp).1
    positivity
  have hbound := Balanced.abs_rescaled_increment_le hjump hsize hrel hlo hs
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hnum : Q * (q : ℝ) * ((p.Pstar + 1 / p.a) / q) =
      Q * (p.Pstar + 1 / p.a) := by field_simp
  simpa only [hnum, SelectionScales.domain] using hbound

theorem eventually_scale_regime (p : Parameters) :
    ∀ᶠ q : ℕ in Filter.atTop, 2 ≤ q ∧ 2 * p.Pstar ≤ q := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * p.Pstar)
  apply Filter.eventually_atTop.mpr
  refine ⟨max 2 N, fun q hq => ?_⟩
  constructor
  · exact (le_max_left _ _).trans hq
  · have hNq : N ≤ q := (le_max_right _ _).trans hq
    exact hN.trans (by exact_mod_cast hNq)

end
end Balanced.Selection.Process.Parameters

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionCensoredJumps
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process.CensoredJumps

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in

theorem domain_subset_slotVertices (G : Input I V) (S : State I V) (i : I) :
    domain G S i ⊆ slotVertices G i := by
  intro v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩

theorem domain_card_le_order {G : Input I V} {q : ℕ} {c C : ℝ}
    (hG : GraphBounds G q c C) (S : State I V) (i : I) :
    ((domain G S i).card : ℝ) ≤ q := by
  exact (Nat.cast_le.mpr (Finset.card_le_card (domain_subset_slotVertices G S i))).trans
    (Nat.cast_le.mpr (hG.2.2.1 i).2)

theorem current_degree_le_budget {G : Input I V} {q : ℕ} {c C : ℝ}
    (hG : GraphBounds G q c C) (S : State I V) (v : V) :
    (degree G S v : ℝ) ≤ C * q := by
  exact (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)).trans
    (hG.2.2.2.1 v)

theorem abs_censoredDomainCount_sub_le
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : State I V) {i : I} (hi : i ∈ S.remaining) (w : V) (flags : V → Bool) :
    |(censoredDomainCount q G S i w flags : ℝ) - ((domain G S i).card : ℝ)| ≤
      2 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  unfold censoredDomainCount
  split_ifs with hthin
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr
      (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)))]
    exact domain_loss_le_two_mul_rpow hG S hi w flags hthin
  · simp only [sub_self, abs_zero]
    positivity

theorem abs_censoredDegreeCount_sub_le
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : State I V) (i : I) (w v : V) (flags : V → Bool) :
    |(censoredDegreeCount q G S i w v flags : ℝ) - (degree G S v : ℝ)| ≤
      3 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  unfold censoredDegreeCount
  split_ifs with hgood
  · exact abs_degree_update_sub_le_three_mul_rpow hG S i w v flags hgood.1 hgood.2
  · simp only [sub_self, abs_zero]
    positivity

theorem abs_rescaled_censoredDomainCount_sub_le
    {p : Parameters} (hp : p.Admissible) {G : Input I V} {q t : ℕ}
    (hG : GraphBounds G q p.c p.C) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) {i : I} (hi : i ∈ S.remaining) (w : V) (flags : V → Bool) :
    |(censoredDomainCount q G S i w flags : ℝ) / p.sizeScale q (t + 1) -
        ((domain G S i).card : ℝ) / p.sizeScale q t| ≤
      (2 * (q : ℝ) ^ (1 / 8 : ℝ) + p.Pstar) / p.smin := by
  have hsize : |((domain G S i).card : ℝ)| ≤ 1 * (q : ℝ) := by
    have hnon : 0 ≤ ((domain G S i).card : ℝ) := Nat.cast_nonneg _
    rw [abs_of_nonneg hnon, one_mul]
    exact domain_card_le_order hG S i
  simpa only [one_mul] using Parameters.source_size_increment_le hp hq hPq hG.1 ht
    (abs_censoredDomainCount_sub_le hG S hi w flags) hsize

theorem abs_rescaled_censoredDegreeCount_sub_le
    {p : Parameters} (hp : p.Admissible) {G : Input I V} {q t : ℕ}
    (hG : GraphBounds G q p.c p.C) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (i : I) (w v : V) (flags : V → Bool) :
    |(censoredDegreeCount q G S i w v flags : ℝ) / p.degreeScale q (Fintype.card I) (t + 1) -
        (degree G S v : ℝ) / p.degreeScale q (Fintype.card I) t| ≤
      (3 * (q : ℝ) ^ (1 / 8 : ℝ) + p.C * (p.Pstar + 1 / p.a)) /
        (p.smin * p.a / 3) := by
  have hsize : |(degree G S v : ℝ)| ≤ p.C * q := by
    have hnon : 0 ≤ (degree G S v : ℝ) := Nat.cast_nonneg _
    rw [abs_of_nonneg hnon]
    exact current_degree_le_budget hG S v
  exact Parameters.source_degree_increment_le hp hq hPq hG.1 ht
    (abs_censoredDegreeCount_sub_le hG S i w v flags) hsize

end
end Balanced.Selection.Process.CensoredJumps

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionAuxiliaryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] [Fintype V] in

theorem censoredDomainNumerator_eq_count (q : ℕ) (G : Input I V)
    (S : State I V) (r : Noise I V) (i : I) :
    censoredDomainNumerator q G S r i =
      (CensoredJumps.censoredDomainCount q G S i r.2.1 r.2.2 : ℝ) := by
  by_cases h : (((thinned G S r.2.1 r.2.2) ∩ domain G S i).card : ℝ) ≤
      (q : ℝ) ^ (1 / 8 : ℝ)
  · simp only [censoredDomainNumerator, CensoredJumps.censoredDomainCount,
      ite_eq_right (not_lt.mpr h), ite_eq_left h]
  · simp only [censoredDomainNumerator, CensoredJumps.censoredDomainCount,
      ite_eq_left (lt_of_not_ge h), ite_eq_right h]

omit [Fintype I] in

theorem censoredDegreeNumerator_eq_count (q : ℕ) (G : Input I V)
    (S : State I V) (r : Noise I V) (v : V) :
    censoredDegreeNumerator q G S r v =
      (CensoredJumps.censoredDegreeCount q G S r.1 r.2.1 v r.2.2 : ℝ) := by
  by_cases he : r.2.1 ∈ G.exceptional v
  · simp [censoredDegreeNumerator, CensoredJumps.censoredDegreeCount, he]
  · by_cases h : (((thinned G S r.2.1 r.2.2) ∩ neighbors G v).card : ℝ) ≤
        (q : ℝ) ^ (1 / 8 : ℝ)
    · simp only [censoredDegreeNumerator, CensoredJumps.censoredDegreeCount, he, false_or,
        not_false_eq_true, true_and, ite_eq_right (not_lt.mpr h), ite_eq_left h]
    · simp only [censoredDegreeNumerator, CensoredJumps.censoredDegreeCount, he, false_or,
        not_false_eq_true, true_and, ite_eq_left (lt_of_not_ge h), ite_eq_right h]

theorem abs_domainTrackIncrement_le {p : Parameters} (hp : p.Admissible)
    {G : Input I V} {q t : ℕ} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I)) (i : I)
    (before : Option (State I V)) (draw : Option (Noise I V)) :
    |domainTrackIncrement p q t G i before draw| ≤
      (2 * (q : ℝ) ^ (1 / 8 : ℝ) + p.Pstar) / p.smin := by
  have hnon : 0 ≤ (2 * (q : ℝ) ^ (1 / 8 : ℝ) + p.Pstar) / p.smin := by
    have hP := (Parameters.Pstar_pos hp).le
    have hs := (Real.exp_pos (-6 * p.Pstar)).le
    change 0 ≤ (2 * (q : ℝ) ^ (1 / 8 : ℝ) + p.Pstar) / Real.exp (-6 * p.Pstar)
    positivity
  cases before with
  | none => simpa [domainTrackIncrement] using hnon
  | some S =>
    cases draw with
    | none => simpa [domainTrackIncrement] using hnon
    | some r =>
      by_cases hi : i ∈ S.remaining
      · simpa only [domainTrackIncrement, hi, ite_true, censoredDomainNumerator_eq_count] using
          CensoredJumps.abs_rescaled_censoredDomainCount_sub_le hp hG hq hPq ht S hi r.2.1 r.2.2
      · simpa [domainTrackIncrement, hi] using hnon

theorem abs_degreeTrackIncrement_le {p : Parameters} (hp : p.Admissible)
    {G : Input I V} {q t : ℕ} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I)) (v : V)
    (before : Option (State I V)) (draw : Option (Noise I V)) :
    |degreeTrackIncrement p q t G v before draw| ≤
      (3 * (q : ℝ) ^ (1 / 8 : ℝ) + p.C * (p.Pstar + 1 / p.a)) /
        (p.smin * p.a / 3) := by
  have hnon : 0 ≤
      (3 * (q : ℝ) ^ (1 / 8 : ℝ) + p.C * (p.Pstar + 1 / p.a)) /
        (p.smin * p.a / 3) := by
    have hP := (Parameters.Pstar_pos hp).le
    have hC := hp.2.1.le
    have ha := (Parameters.a_bounds hp).1.le
    change 0 ≤ (3 * (q : ℝ) ^ (1 / 8 : ℝ) + p.C * (p.Pstar + 1 / p.a)) /
      (Real.exp (-6 * p.Pstar) * p.a / 3)
    positivity
  cases before with
  | none => simpa [degreeTrackIncrement] using hnon
  | some S =>
    cases draw with
    | none => simpa [degreeTrackIncrement] using hnon
    | some r =>
      by_cases hv : v ∈ currentVertices G S
      · simpa only [degreeTrackIncrement, hv, ite_true, censoredDegreeNumerator_eq_count] using
          CensoredJumps.abs_rescaled_censoredDegreeCount_sub_le hp hG hq hPq ht S r.1 r.2.1 v r.2.2
      · simpa [degreeTrackIncrement, hv] using hnon

theorem abs_domainTrack_succ_sub_le {p : Parameters} (hp : p.Admissible)
    {G : Input I V} {q t : ℕ} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (i : I) (ω : FiniteHistory.Path (Snapshot I V)) :
    |domainTrack p q G i (t + 1) ω - domainTrack p q G i t ω| ≤
      (2 * (q : ℝ) ^ (1 / 8 : ℝ) + p.Pstar) / p.smin := by
  rw [domainTrack_succ_sub]
  exact abs_domainTrackIncrement_le hp hG hq hPq ht i _ _

theorem abs_degreeTrack_succ_sub_le {p : Parameters} (hp : p.Admissible)
    {G : Input I V} {q t : ℕ} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (v : V) (ω : FiniteHistory.Path (Snapshot I V)) :
    |degreeTrack p q G v (t + 1) ω - degreeTrack p q G v t ω| ≤
      (3 * (q : ℝ) ^ (1 / 8 : ℝ) + p.C * (p.Pstar + 1 / p.a)) /
        (p.smin * p.a / 3) := by
  rw [degreeTrack_succ_sub]
  exact abs_degreeTrackIncrement_le hp hG hq hPq ht v _ _

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionProcessThinning
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical

namespace Balanced.Selection.Process

noncomputable section

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in
lemma flagsWeight_eq_thinningMass (p : Parameters) (q : ℕ) (G : Input I V)
    (S : State I V) (flags : V → Bool) :
    flagsWeight p q G S flags =
      SelectionThinning.thinningMass (thinningRate p q G S) flags := rfl

omit [Fintype I] in

lemma sum_drawWeight_adj_vertex (G : Input I V) (S : State I V) (i : I) (u : V) :
    (∑ w : V, if G.graph.Adj u w then drawWeight G S i w else 0) =
      if i ∈ S.remaining then
        (((neighbors G u) ∩ domain G S i).card : ℝ) *
          ((S.remaining.card : ℝ) * (domain G S i).card)⁻¹ else 0 := by
  by_cases hi : i ∈ S.remaining
  · rw [ite_eq_left hi]
    calc
      _ = ∑ w : V, if w ∈ neighbors G u ∩ domain G S i then
          ((S.remaining.card : ℝ) * (domain G S i).card)⁻¹ else 0 := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases ha : G.graph.Adj u w <;> by_cases hd : w ∈ domain G S i <;>
          simp [hi, ha, hd, drawWeight, neighbors]
      _ = _ := by
        rw [← Finset.sum_filter]
        have hfilter : (Finset.univ.filter (fun w : V => w ∈ neighbors G u ∩ domain G S i)) =
            neighbors G u ∩ domain G S i := by ext; simp
        rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  · simp [drawWeight, hi]

lemma drawWeight_conflict_mass (G : Input I V) (S : State I V) (u : V) :
    SelectionThinning.eventMass (fun iw : I × V => drawWeight G S iw.1 iw.2)
      (fun iw => G.graph.Adj u iw.2) = hazard G S u := by
  unfold SelectionThinning.eventMass
  rw [Fintype.sum_prod_type]
  simp_rw [sum_drawWeight_adj_vertex]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  unfold hazard
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp [div_eq_mul_inv, mul_comm, mul_assoc]

lemma drawWeight_pair_sum (G : Input I V) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty) :
    (∑ iw : I × V, drawWeight G S iw.1 iw.2) = 1 := by
  rw [Fintype.sum_prod_type]
  exact sum_drawWeight G S hS hdom

lemma performed_survival_mass (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (u : V)
    (hu : u ∈ currentVertices G S) :
    (∑ r : Noise I V, if u ∈ survivors G S r.2.1 r.2.2 then
      noiseWeight p q G S r else 0) = 1 - p.alpha q := by
  have hnorm := drawWeight_pair_sum G S hp.1 (fun i hi => (hp.2.2.2.1 i hi).1)
  have hbad : SelectionThinning.eventMass
      (fun iw : I × V => drawWeight G S iw.1 iw.2)
      (fun iw => G.graph.Adj iw.2 u) = hazard G S u := by
    simpa only [SimpleGraph.adj_comm] using drawWeight_conflict_mass G S u
  have hs := SelectionThinning.surviving_event_mass
    (fun iw : I × V => drawWeight G S iw.1 iw.2) (thinningRate p q G S)
    (fun iw => ¬ G.graph.Adj iw.2 u) u
  rw [SelectionThinning.eventMass_compl _ hnorm, hbad] at hs
  have hrate : thinningRate p q G S u =
      SelectionThinning.thinningRate (p.alpha q) (hazard G S u) := by
    simp [thinningRate, hu, SelectionThinning.thinningRate]
  rw [hrate, SelectionThinning.equal_survival
    (lt_of_le_of_lt (hp.2.2.2.2 u hu) hp.2.2.1)] at hs
  simp only [Noise, Fintype.sum_prod_type] at hs ⊢
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr (by ext; simp)
  intro i _
  apply Finset.sum_congr (by ext; simp)
  intro w _
  apply Finset.sum_congr (by ext; simp)
  intro flags _
  by_cases he : ¬ G.graph.Adj w u ∧ flags u = false <;>
    simp [survivors, hu, he, noiseWeight, SelectionThinning.jointMass,
      flagsWeight_eq_thinningMass]

lemma drawWeight_slot_mass (G : Input I V) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty)
    (j : I) (hj : j ∈ S.remaining) :
    SelectionThinning.eventMass (fun iw : I × V => drawWeight G S iw.1 iw.2)
      (fun iw => iw.1 = j) = (S.remaining.card : ℝ)⁻¹ := by
  unfold SelectionThinning.eventMass
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i : I, if i = j then (∑ w : V, drawWeight G S i w) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = j <;> simp [hi]
    _ = ∑ w : V, drawWeight G S j w := by simp
    _ = _ := by rw [sum_drawWeight_vertex G S hS hdom, ite_eq_left hj]

omit [Fintype I] [Fintype V] in
lemma drawWeight_eq_zero_of_same_slot_conflict (G : Input I V) (S : State I V)
    (hwithin : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (i : I) (w u : V) (hi : i = G.slot u) (ha : G.graph.Adj w u) :
    drawWeight G S i w = 0 := by
  unfold drawWeight
  split_ifs with hd
  · have hw : G.slot w = i := (Finset.mem_filter.mp hd.2).2
    exact (hwithin w u (hw.trans hi) ha).elim
  · rfl

lemma drawWeight_survives_slot_mass (G : Input I V) (S : State I V)
    (hS : S.remaining.Nonempty) (hdom : ∀ i ∈ S.remaining, (domain G S i).Nonempty)
    (hwithin : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (u : V) (hu : G.slot u ∈ S.remaining) :
    SelectionThinning.eventMass (fun iw : I × V => drawWeight G S iw.1 iw.2)
      (fun iw => ¬ G.graph.Adj iw.2 u ∧ iw.1 ≠ G.slot u) =
      1 - hazard G S u - (S.remaining.card : ℝ)⁻¹ := by
  have hbad : SelectionThinning.eventMass
      (fun iw : I × V => drawWeight G S iw.1 iw.2)
      (fun iw => G.graph.Adj iw.2 u) = hazard G S u := by
    simpa only [SimpleGraph.adj_comm] using drawWeight_conflict_mass G S u
  calc
    _ = (∑ iw : I × V, drawWeight G S iw.1 iw.2) -
        SelectionThinning.eventMass (fun iw : I × V => drawWeight G S iw.1 iw.2)
          (fun iw => G.graph.Adj iw.2 u) -
        SelectionThinning.eventMass (fun iw : I × V => drawWeight G S iw.1 iw.2)
          (fun iw => iw.1 = G.slot u) := by
      unfold SelectionThinning.eventMass
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro iw _
      by_cases ha : G.graph.Adj iw.2 u <;> by_cases hi : iw.1 = G.slot u
      · have hz := drawWeight_eq_zero_of_same_slot_conflict G S hwithin iw.1 iw.2 u hi ha
        rw [hi] at hz
        simp [ha, hi, hz]
      all_goals simp [ha, hi]
    _ = _ := by
      rw [drawWeight_pair_sum G S hS hdom, hbad, drawWeight_slot_mass G S hS hdom _ hu]

lemma performed_post_survival_mass_le (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S)
    (hwithin : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (u : V) (hu : u ∈ currentVertices G S) :
    (∑ r : Noise I V, if u ∈ (update G S r.1 r.2.1 r.2.2).alive then
      noiseWeight p q G S r else 0) ≤
      (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) := by
  have hslot : G.slot u ∈ S.remaining := (Finset.mem_filter.mp hu).2
  have hs := SelectionThinning.surviving_event_mass
    (fun iw : I × V => drawWeight G S iw.1 iw.2) (thinningRate p q G S)
    (fun iw => ¬ G.graph.Adj iw.2 u ∧ iw.1 ≠ G.slot u) u
  rw [drawWeight_survives_slot_mass G S hp.1
    (fun i hi => (hp.2.2.2.1 i hi).1) hwithin u hslot] at hs
  have hrate : thinningRate p q G S u =
      SelectionThinning.thinningRate (p.alpha q) (hazard G S u) := by
    simp [thinningRate, hu, SelectionThinning.thinningRate]
  have heq := SelectionThinning.equal_survival (α := p.alpha q)
    (lt_of_le_of_lt (hp.2.2.2.2 u hu) hp.2.2.1)
  rw [← hrate] at heq
  have hmir := (thinningRate_bounds_of_precheck p q t G S hp u).2
  have hmul : 0 ≤ (S.remaining.card : ℝ)⁻¹ *
      (p.alpha q - thinningRate p q G S u) := mul_nonneg (by positivity) (sub_nonneg.mpr hmir)
  have hbound : (1 - hazard G S u - (S.remaining.card : ℝ)⁻¹) *
      (1 - thinningRate p q G S u) ≤
      (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) := by nlinarith
  have hfinal := hs.trans_le hbound
  simp only [Noise, Fintype.sum_prod_type] at hfinal ⊢
  convert hfinal using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr (by ext; simp)
  intro i _
  apply Finset.sum_congr (by ext; simp)
  intro w _
  apply Finset.sum_congr (by ext; simp)
  intro flags _
  have hm : u ∈ (update G S i w flags).alive ↔
      (¬ G.graph.Adj w u ∧ i ≠ G.slot u) ∧ flags u = false := by
    simp [update, survivors, hu, ne_comm, and_comm, and_assoc]
  simp only [hm]
  by_cases he : (¬ G.graph.Adj w u ∧ i ≠ G.slot u) ∧ flags u = false <;>
    simp [he, noiseWeight, SelectionThinning.jointMass, flagsWeight_eq_thinningMass]

lemma performed_count_eq_sum (p : Parameters) (q : ℕ) (G : Input I V)
    (S : State I V) (C : Finset V) (A : Noise I V → Finset V) :
    (∑ r : Noise I V, noiseWeight p q G S r * ((C ∩ A r).card : ℝ)) =
      ∑ u ∈ C, ∑ r : Noise I V, if u ∈ A r then noiseWeight p q G S r else 0 := by
  calc
    _ = ∑ r : Noise I V, ∑ u ∈ C,
        if u ∈ A r then noiseWeight p q G S r else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      have hfilter : C ∩ A r = C.filter (fun u => u ∈ A r) := by ext; simp
      rw [hfilter, ← Finset.sum_boole (fun u => u ∈ A r) C, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : u ∈ A r <;> simp [h]
    _ = _ := Finset.sum_comm

lemma performed_survivor_count (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (C : Finset V)
    (hC : C ⊆ currentVertices G S) :
    (∑ r : Noise I V, noiseWeight p q G S r *
      ((C ∩ survivors G S r.2.1 r.2.2).card : ℝ)) =
        (1 - p.alpha q) * C.card := by
  rw [performed_count_eq_sum]
  calc
    _ = ∑ _u ∈ C, (1 - p.alpha q) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact performed_survival_mass p q t G S hp u (hC hu)
    _ = _ := by simp [mul_comm]; ring

lemma performed_alive_count_le (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S)
    (hwithin : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (C : Finset V) (hC : C ⊆ currentVertices G S) :
    (∑ r : Noise I V, noiseWeight p q G S r *
      ((C ∩ (update G S r.1 r.2.1 r.2.2).alive).card : ℝ)) ≤
        (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) * C.card := by
  rw [performed_count_eq_sum]
  calc
    _ ≤ ∑ _u ∈ C, ((1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact performed_post_survival_mass_le p q t G S hp hwithin u (hC hu)
    _ = _ := by simp [mul_comm]

omit [Fintype I] [Fintype V] in
lemma currentVertices_update (G : Input I V) (S : State I V) (i : I)
    (w : V) (flags : V → Bool) :
    currentVertices G (update G S i w flags) = (update G S i w flags).alive := by
  ext u
  simp only [currentVertices, update, Finset.mem_filter, survivors, Finset.mem_erase]
  aesop

lemma performed_degree_le (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S)
    (hwithin : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) (v : V) :
    (∑ r : Noise I V, noiseWeight p q G S r *
      (degree G (update G S r.1 r.2.1 r.2.2) v : ℝ)) ≤
        (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) * degree G S v := by
  have h := performed_alive_count_le p q t G S hp hwithin
    (neighbors G v ∩ currentVertices G S) Finset.inter_subset_right
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro r _
  congr 2
  unfold degree
  rw [currentVertices_update]
  congr 1
  ext u
  simp only [Finset.mem_inter, update, Finset.mem_filter, survivors]
  aesop
  all_goals rfl

omit [Fintype I] [Fintype V] in
lemma domain_subset_currentVertices (G : Input I V) (S : State I V)
    (i : I) (hi : i ∈ S.remaining) : domain G S i ⊆ currentVertices G S := by
  intro u hu
  rcases Finset.mem_filter.mp hu with ⟨hu, hslot⟩
  exact Finset.mem_filter.mpr ⟨hu, hslot ▸ hi⟩

lemma performed_domain_size (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (hp : Precheck p q t G S) (i : I) (hi : i ∈ S.remaining) :
    (∑ r : Noise I V, noiseWeight p q G S r *
      ((domain G S i ∩ survivors G S r.2.1 r.2.2).card : ℝ)) =
        (1 - p.alpha q) * (domain G S i).card :=
  performed_survivor_count p q t G S hp (domain G S i)
    (domain_subset_currentVertices G S i hi)

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionCensoredMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem finite_censor_mean_error {A : Type*} [Fintype A]
    (w X : A → ℝ) (N : ℝ) (B : A → Prop)
    (hw : ∀ a, 0 ≤ w a) (hX : ∀ a, 0 ≤ X a ∧ X a ≤ N) :
    0 ≤ (∑ a, w a * (if B a then N else X a)) - ∑ a, w a * X a ∧
      (∑ a, w a * (if B a then N else X a)) - ∑ a, w a * X a ≤
        N * (∑ a, if B a then w a else 0) := by
  have heq : (∑ a, w a * (if B a then N else X a)) - ∑ a, w a * X a =
      ∑ a, w a * ((if B a then N else X a) - X a) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [heq]
  constructor
  · apply Finset.sum_nonneg
    intro a _
    apply mul_nonneg (hw a)
    split_ifs
    · exact sub_nonneg.mpr (hX a).2
    · exact sub_nonneg.mpr le_rfl
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    by_cases h : B a
    · simp only [h, ite_true]
      have hm := mul_le_mul_of_nonneg_left (show N - X a ≤ N by linarith [(hX a).1]) (hw a)
      simpa only [mul_comm N] using hm
    · simp [h]

theorem censoredDomain_mean_error {p : Parameters} {q t : ℕ}
    {G : Input I V} (hG : GraphBounds G q p.c p.C) (S : State I V)
    (hpre : Precheck p q t G S) (i : I) (hi : i ∈ S.remaining) :
    0 ≤ (∑ r : Noise I V, noiseWeight p q G S r * censoredDomainNumerator q G S r i) -
        (1 - p.alpha q) * (domain G S i).card ∧
      (∑ r : Noise I V, noiseWeight p q G S r * censoredDomainNumerator q G S r i) -
        (1 - p.alpha q) * (domain G S i).card ≤
          (q : ℝ) * domainOverflowMass p q G S i := by
  have hraw := performed_domain_size p q t G S hpre i hi
  rw [show (fun r : Noise I V =>
      noiseWeight p q G S r * ((domain G S i ∩ survivors G S r.2.1 r.2.2).card : ℝ)) =
      (fun r : Noise I V =>
      noiseWeight p q G S r * ((survivors G S r.2.1 r.2.2 ∩ domain G S i).card : ℝ)) by
        funext r; rw [Finset.inter_comm]] at hraw
  have herr := finite_censor_mean_error (noiseWeight p q G S)
    (fun r : Noise I V => ((survivors G S r.2.1 r.2.2 ∩ domain G S i).card : ℝ))
    (domain G S i).card
    (fun r : Noise I V => (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ domain G S i).card : ℝ))
    (noiseWeight_nonnegative_of_precheck p q t G S hpre)
    (fun r => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)⟩)
  change 0 ≤ (∑ r, noiseWeight p q G S r * censoredDomainNumerator q G S r i) -
      (∑ r, noiseWeight p q G S r * ((survivors G S r.2.1 r.2.2 ∩ domain G S i).card : ℝ)) ∧
    (∑ r, noiseWeight p q G S r * censoredDomainNumerator q G S r i) -
      (∑ r, noiseWeight p q G S r * ((survivors G S r.2.1 r.2.2 ∩ domain G S i).card : ℝ)) ≤
        (domain G S i).card * domainOverflowMass p q G S i at herr
  rw [hraw] at herr
  refine ⟨herr.1, herr.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right (CensoredJumps.domain_card_le_order hG S i)
  apply Finset.sum_nonneg
  intro r _
  split
  · exact noiseWeight_nonnegative_of_precheck p q t G S hpre r
  · exact le_rfl

theorem censoredDegree_mean_le {p : Parameters} {q t : ℕ}
    {G : Input I V} (hG : GraphBounds G q p.c p.C) (S : State I V)
    (hpre : Precheck p q t G S) (v : V) :
    (∑ r : Noise I V, noiseWeight p q G S r * censoredDegreeNumerator q G S r v) ≤
      (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) * degree G S v +
        p.C * q * degreeCensorMass p q G S v := by
  have hraw := performed_degree_le p q t G S hpre hG.2.1 v
  have herr := (finite_censor_mean_error (noiseWeight p q G S)
    (fun r : Noise I V => (degree G (update G S r.1 r.2.1 r.2.2) v : ℝ))
    (degree G S v : ℝ)
    (fun r : Noise I V => r.2.1 ∈ G.exceptional v ∨ (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ neighbors G v).card : ℝ))
    (noiseWeight_nonnegative_of_precheck p q t G S hpre)
    (fun r => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (degree_update_le G S r.1 r.2.1 v r.2.2)⟩)).2
  have herr' : (∑ r, noiseWeight p q G S r * censoredDegreeNumerator q G S r v) -
      (∑ r, noiseWeight p q G S r * (degree G (update G S r.1 r.2.1 r.2.2) v : ℝ)) ≤
      (degree G S v : ℝ) * degreeCensorMass p q G S v := by
    convert herr using 1 <;> congr 1
    · apply Finset.sum_congr rfl
      intro r _
      unfold censoredDegreeNumerator
      split_ifs <;> rfl
    · unfold degreeCensorMass
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> rfl
  have hm : (degree G S v : ℝ) * degreeCensorMass p q G S v ≤
      p.C * q * degreeCensorMass p q G S v := by
    apply mul_le_mul_of_nonneg_right (CensoredJumps.current_degree_le_budget hG S v)
    apply Finset.sum_nonneg
    intro r _
    split
    · exact noiseWeight_nonnegative_of_precheck p q t G S hpre r
    · exact le_rfl
  linarith

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionAuxiliaryMeanBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem finite_weighted_rescaled_mean {A : Type*} [Fintype A]
    (w Y : A → ℝ) (x a b : ℝ) (hw : ∑ r, w r = 1) (hb : b ≠ 0) :
    (∑ r, w r * (Y r / b - x / a)) =
      ((∑ r, w r * Y r) - (b / a) * x) / b := by
  simp_rw [mul_sub, ← mul_div_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    ← Finset.sum_mul, hw, one_mul]
  field_simp

theorem domain_scale_ratio (p : Parameters) {q t : ℕ}
    (hscale : p.sizeScale q t ≠ 0) :
    p.sizeScale q (t + 1) / p.sizeScale q t = 1 - p.alpha q := by
  unfold Parameters.sizeScale at *
  rw [pow_succ, mul_div_cancel_left₀ _ hscale]

theorem domainTrack_noise_drift_bound {p : Parameters} (hp : p.Admissible)
    {q t : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (hpre : Precheck p q t G S) (i : I) (hi : i ∈ S.remaining) :
    |∑ r : Noise I V, noiseWeight p q G S r *
      domainTrackIncrement p q t G i (some S) (some r)| ≤
        (q : ℝ) * domainOverflowMass p q G S i / p.smin := by
  have hsn := (Parameters.source_scale_bounds hp hq hPq hG.1 ht).1
  have hso := (Parameters.source_scale_bounds hp hq hPq hG.1 (by omega : t ≤
    p.lastMainTime q (Fintype.card I))).1
  have hsmin : 0 < p.smin := Real.exp_pos _
  have hn : 0 < p.sizeScale q (t + 1) := hsmin.trans_le hsn
  have ho : 0 < p.sizeScale q t := hsmin.trans_le hso
  have hw := sum_noiseWeight p q G S hpre.1 (fun i hi => (hpre.2.2.2.1 i hi).1)
  have he := censoredDomain_mean_error hG S hpre i hi
  simp only [domainTrackIncrement, hi, ite_true]
  rw [finite_weighted_rescaled_mean _ _ _ _ _ hw hn.ne', domain_scale_ratio p ho.ne',
    abs_div, abs_of_pos hn, abs_of_nonneg he.1]
  exact (div_le_div_of_nonneg_right he.2 hn.le).trans
    (div_le_div_of_nonneg_left (he.1.trans he.2) hsmin hsn)

omit [Fintype V] in

theorem degree_scale_ratio_of_card {p : Parameters} (hp : p.Admissible)
    {q t : ℕ} (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (_hG : Fintype.card I = 2 * (q + 1))
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (hcard : S.remaining.card = Fintype.card I - t) :
    p.degreeScale q (Fintype.card I) (t + 1) / p.degreeScale q (Fintype.card I) t =
      (1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹) := by
  have htn : t < Fintype.card I :=
    (Nat.lt_of_succ_le ht).trans_le (Nat.sub_le _ _)
  have h := SelectionScales.degree_ratio (Parameters.Pstar_pos hp).le
    (show 0 < q by omega) hPq htn
  simpa only [Parameters.degreeScale, Parameters.sizeScale, Parameters.alpha,
    SelectionScales.degree, SelectionScales.domain, hcard, one_div] using h

theorem degreeTrack_noise_drift_bound {p : Parameters} (hp : p.Admissible)
    {q t : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (hpre : Precheck p q t G S)
    (hcard : S.remaining.card = Fintype.card I - t) (v : V)
    (hv : v ∈ currentVertices G S) :
    (∑ r : Noise I V, noiseWeight p q G S r *
      degreeTrackIncrement p q t G v (some S) (some r)) ≤
        p.C * q * degreeCensorMass p q G S v / (p.smin * p.a / 3) := by
  have hsn := (Parameters.source_scale_bounds hp hq hPq hG.1 ht).2.2.1
  have hmin : 0 < p.smin * p.a / 3 := by
    have hs : 0 < p.smin := Real.exp_pos _
    have ha := (Parameters.a_bounds hp).1
    positivity
  have hn : 0 < p.degreeScale q (Fintype.card I) (t + 1) := hmin.trans_le hsn
  have hw := sum_noiseWeight p q G S hpre.1 (fun i hi => (hpre.2.2.2.1 i hi).1)
  have he := censoredDegree_mean_le hG S hpre v
  have hmass : 0 ≤ degreeCensorMass p q G S v := by
    apply Finset.sum_nonneg
    intro r _
    split
    · exact noiseWeight_nonnegative_of_precheck p q t G S hpre r
    · exact le_rfl
  simp only [degreeTrackIncrement, hv, ite_true]
  rw [finite_weighted_rescaled_mean _ _ _ _ _ hw hn.ne',
    degree_scale_ratio_of_card hp hq hPq hG.1 ht S hcard]
  apply (div_le_div_of_nonneg_right (by linarith :
    (∑ r, noiseWeight p q G S r * censoredDegreeNumerator q G S r v) -
      ((1 - p.alpha q) * (1 - (S.remaining.card : ℝ)⁻¹)) * degree G S v ≤
        p.C * q * degreeCensorMass p q G S v) hn.le).trans
  exact div_le_div_of_nonneg_left
    (mul_nonneg (mul_nonneg hp.2.1.le (Nat.cast_nonneg q)) hmass) hmin hsn

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionAuxiliaryConditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem ae_domainTrack_conditional_drift_of_mass {p : Parameters} (hp : p.Admissible)
    {q t : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (i : I) {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ S : State I V, Precheck p q t G S → i ∈ S.remaining →
      domainOverflowMass p q G S i ≤ ε) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      |(snapshotPathLaw p q G)[fun ω =>
        domainTrack p q G i (t + 1) ω - domainTrack p q G i t ω |
          snapshotFiltration t] ω| ≤ (q : ℝ) * ε / p.smin := by
  have hbound : 0 ≤ (q : ℝ) * ε / p.smin := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg q) hε) (Real.exp_pos _).le
  filter_upwards [condExp_domainTrack_increment p q t G i] with ω hω
  rw [hω]
  cases hstate : (ω t).1 with
  | none => simpa [domainTrackIncrement] using hbound
  | some S =>
      by_cases hpre : Precheck p q t G S
      · rw [sum_drawStepWeight_of_precheck p q t G S hpre]
        by_cases hi : i ∈ S.remaining
        · exact (domainTrack_noise_drift_bound hp hG hq hPq ht S hpre i hi).trans
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hmass S hpre hi) (Nat.cast_nonneg q))
              (Real.exp_pos _).le)
        · simpa [domainTrackIncrement, hi] using hbound
      · simpa [Fintype.sum_option, drawStepWeight, hpre, domainTrackIncrement]
          using hbound

theorem ae_degreeTrack_conditional_drift_of_mass {p : Parameters} (hp : p.Admissible)
    {q t : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (v : V) {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ S : State I V, Precheck p q t G S →
      S.remaining.card = Fintype.card I - t → v ∈ currentVertices G S →
      degreeCensorMass p q G S v ≤ ε) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      (snapshotPathLaw p q G)[fun ω =>
        degreeTrack p q G v (t + 1) ω - degreeTrack p q G v t ω |
          snapshotFiltration t] ω ≤ p.C * q * ε / (p.smin * p.a / 3) := by
  have hmin : 0 < p.smin * p.a / 3 := by
    have hs : 0 < p.smin := Real.exp_pos _
    have ha := (Parameters.a_bounds hp).1
    positivity
  have hcoeff : 0 ≤ p.C * q := mul_nonneg hp.2.1.le (Nat.cast_nonneg q)
  have hbound : 0 ≤ p.C * q * ε / (p.smin * p.a / 3) :=
    div_nonneg (mul_nonneg hcoeff hε) hmin.le
  filter_upwards [condExp_degreeTrack_increment p q t G v,
    ae_snapshot_remaining_card p q G] with ω hω hcard
  rw [hω]
  cases hstate : (ω t).1 with
  | none => simpa [degreeTrackIncrement] using hbound
  | some S =>
      by_cases hpre : Precheck p q t G S
      · rw [sum_drawStepWeight_of_precheck p q t G S hpre]
        by_cases hv : v ∈ currentVertices G S
        · exact (degreeTrack_noise_drift_bound hp hG hq hPq ht S hpre
            (hcard t S hstate) v hv).trans
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hmass S hpre (hcard t S hstate) hv) hcoeff) hmin.le)
        · simpa [degreeTrackIncrement, hv] using hbound
      · simpa [Fintype.sum_option, drawStepWeight, hpre, degreeTrackIncrement]
          using hbound

theorem ae_domainTrack_accumulated_drift_of_mass {p : Parameters} (hp : p.Admissible)
    {q T t : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (hT : T ≤ p.lastMainTime q (Fintype.card I)) (ht : t ≤ T)
    (i : I) {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ j < T, ∀ S : State I V, Precheck p q j G S → i ∈ S.remaining →
      domainOverflowMass p q G S i ≤ ε) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      |∑ j ∈ Finset.range t, (snapshotPathLaw p q G)[fun ω =>
        domainTrack p q G i (j + 1) ω - domainTrack p q G i j ω |
          snapshotFiltration j] ω| ≤ (t : ℝ) * ((q : ℝ) * ε / p.smin) := by
  have hstep : ∀ j ∈ Finset.range t, ∀ᵐ ω ∂snapshotPathLaw p q G,
      |(snapshotPathLaw p q G)[fun ω =>
        domainTrack p q G i (j + 1) ω - domainTrack p q G i j ω |
          snapshotFiltration j] ω| ≤ (q : ℝ) * ε / p.smin := by
    intro j hj
    have hjt := Finset.mem_range.mp hj
    exact ae_domainTrack_conditional_drift_of_mass hp hG hq hPq (by omega)
      i hε (hmass j (by omega))
  filter_upwards [ae_all_iff.2 (fun j => ae_all_iff.2 (hstep j))] with ω hω
  calc
    _ ≤ ∑ j ∈ Finset.range t, |(snapshotPathLaw p q G)[fun ω =>
        domainTrack p q G i (j + 1) ω - domainTrack p q G i j ω |
          snapshotFiltration j] ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range t, (q : ℝ) * ε / p.smin :=
      Finset.sum_le_sum hω
    _ = _ := by simp

theorem ae_degreeTrack_accumulated_drift_of_mass {p : Parameters} (hp : p.Admissible)
    {q T t : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (hT : T ≤ p.lastMainTime q (Fintype.card I)) (ht : t ≤ T)
    (v : V) {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ j < T, ∀ S : State I V, Precheck p q j G S →
      S.remaining.card = Fintype.card I - j →
      v ∈ currentVertices G S → degreeCensorMass p q G S v ≤ ε) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      (∑ j ∈ Finset.range t, (snapshotPathLaw p q G)[fun ω =>
        degreeTrack p q G v (j + 1) ω - degreeTrack p q G v j ω |
          snapshotFiltration j] ω) ≤
            (t : ℝ) * (p.C * q * ε / (p.smin * p.a / 3)) := by
  have hstep : ∀ j ∈ Finset.range t, ∀ᵐ ω ∂snapshotPathLaw p q G,
      (snapshotPathLaw p q G)[fun ω =>
        degreeTrack p q G v (j + 1) ω - degreeTrack p q G v j ω |
          snapshotFiltration j] ω ≤ p.C * q * ε / (p.smin * p.a / 3) := by
    intro j hj
    have hjt := Finset.mem_range.mp hj
    exact ae_degreeTrack_conditional_drift_of_mass hp hG hq hPq (by omega)
      v hε (hmass j (by omega))
  filter_upwards [ae_all_iff.2 (fun j => ae_all_iff.2 (hstep j))] with ω hω
  calc
    _ ≤ ∑ _j ∈ Finset.range t, p.C * q * ε / (p.smin * p.a / 3) :=
      Finset.sum_le_sum hω
    _ = _ := by simp

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionAuxiliaryConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem domainTrackJumpBound_pos {p : Parameters} (hp : p.Admissible) (q : ℕ) :
    0 < domainTrackJumpBound p q := by
  have hP := Parameters.Pstar_pos hp
  have hs : 0 < p.smin := Real.exp_pos _
  have hq : 0 ≤ (q : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  unfold domainTrackJumpBound
  positivity

theorem degreeTrackJumpBound_pos {p : Parameters} (hp : p.Admissible) (q : ℕ) :
    0 < degreeTrackJumpBound p q := by
  have hP := Parameters.Pstar_pos hp
  have hs : 0 < p.smin := Real.exp_pos _
  have ha := (Parameters.a_bounds hp).1
  have hC := hp.2.1
  have hq : 0 ≤ (q : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  unfold degreeTrackJumpBound
  positivity

theorem simultaneous_domainTrack_tail_of_mass {p : Parameters} (hp : p.Admissible)
    {q T : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hTpos : 1 ≤ T)
    (hT : T ≤ p.lastMainTime q (Fintype.card I))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ i j, j < T → ∀ S : State I V, Precheck p q j G S →
      i ∈ S.remaining → domainOverflowMass p q G S i ≤ ε)
    (u : ℝ) (hu : 0 < u) :
    (snapshotPathLaw p q G).real {ω | ∃ i t, t ≤ T ∧
      (t : ℝ) * ((q : ℝ) * ε / p.smin) + u ≤
        |domainTrack p q G i t ω - domainTrack p q G i 0 ω|} ≤
      2 * Fintype.card I * (T + 1 : ℕ) *
        Real.exp (-u ^ 2 / (8 * (T : ℝ) * (domainTrackJumpBound p q) ^ 2)) := by
  apply simultaneous_abs_tail_of_drift_bound
    (μ := snapshotPathLaw p q G) (ℱ := snapshotFiltration)
    (domainTrack p q G) T (domainTrackJumpBound p q) hTpos
    (domainTrackJumpBound_pos hp q)
  · intro i t _
    exact stronglyMeasurable_domainTrack p q G i t
  · intro i j hj
    exact Filter.Eventually.of_forall (fun ω =>
      abs_domainTrack_succ_sub_le hp hG hq hPq (by omega) i ω)
  · exact hu
  · intro i t ht
    exact ae_domainTrack_accumulated_drift_of_mass hp hG hq hPq hT ht i hε
      (fun j hj => hmass i j hj)

theorem simultaneous_degreeTrack_tail_of_mass {p : Parameters} (hp : p.Admissible)
    {q T : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hTpos : 1 ≤ T)
    (hT : T ≤ p.lastMainTime q (Fintype.card I))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ v j, j < T → ∀ S : State I V, Precheck p q j G S →
      S.remaining.card = Fintype.card I - j →
      v ∈ currentVertices G S → degreeCensorMass p q G S v ≤ ε)
    (u : ℝ) (hu : 0 < u) :
    (snapshotPathLaw p q G).real {ω | ∃ v t, t ≤ T ∧
      (t : ℝ) * (p.C * q * ε / (p.smin * p.a / 3)) + u ≤
        degreeTrack p q G v t ω - degreeTrack p q G v 0 ω} ≤
      2 * Fintype.card V * (T + 1 : ℕ) *
        Real.exp (-u ^ 2 / (8 * (T : ℝ) * (degreeTrackJumpBound p q) ^ 2)) := by
  apply simultaneous_upper_tail_of_drift_bound
    (μ := snapshotPathLaw p q G) (ℱ := snapshotFiltration)
    (degreeTrack p q G) T (degreeTrackJumpBound p q) hTpos
    (degreeTrackJumpBound_pos hp q)
  · intro v t _
    exact stronglyMeasurable_degreeTrack p q G v t
  · intro v j hj
    exact Filter.Eventually.of_forall (fun ω =>
      abs_degreeTrack_succ_sub_le hp hG hq hPq (by omega) v ω)
  · exact hu
  · intro v t ht
    exact ae_degreeTrack_accumulated_drift_of_mass hp hG hq hPq hT ht v hε
      (fun j hj => hmass v j hj)

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionCensorProbability
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype V] in

theorem sum_drawWeight_over_slots (G : Input I V) (S : State I V) (w : V) :
    (∑ i : I, drawWeight G S i w) =
      if w ∈ currentVertices G S then
        ((S.remaining.card : ℝ) * (domain G S (G.slot w)).card)⁻¹ else 0 := by
  rw [Finset.sum_eq_single (G.slot w)]
  · simp only [drawWeight, domain, currentVertices, Finset.mem_filter]
    by_cases ha : w ∈ S.alive <;> by_cases hr : G.slot w ∈ S.remaining <;>
      simp [ha, hr]
  · intro i _ hi
    have hslot : G.slot w ≠ i := Ne.symm hi
    simp [drawWeight, domain, hslot]
  · simp

omit [Fintype V] in

theorem sum_drawWeight_over_slots_le (G : Input I V) (S : State I V)
    (L : ℝ) (hL : 0 < L) (hS : S.remaining.Nonempty)
    (hdom : ∀ i ∈ S.remaining, L ≤ ((domain G S i).card : ℝ)) (w : V) :
    (∑ i : I, drawWeight G S i w) ≤ 1 / ((S.remaining.card : ℝ) * L) := by
  have hcard : (0 : ℝ) < S.remaining.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  rw [sum_drawWeight_over_slots]
  split_ifs with hw
  · have hslot : G.slot w ∈ S.remaining := (Finset.mem_filter.mp hw).2
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (mul_pos hcard hL)
      (mul_le_mul_of_nonneg_left (hdom _ hslot) hcard.le)
  · positivity

theorem drawWeight_event_le_card_div (G : Input I V) (S : State I V)
    (A : Finset V) (L : ℝ) (hL : 0 < L) (hS : S.remaining.Nonempty)
    (hdom : ∀ i ∈ S.remaining, L ≤ ((domain G S i).card : ℝ)) :
    (∑ i : I, ∑ w : V, if w ∈ A then drawWeight G S i w else 0) ≤
      (A.card : ℝ) / ((S.remaining.card : ℝ) * L) := by
  rw [Finset.sum_comm]
  have hswap (w : V) :
      (∑ i : I, if w ∈ A then drawWeight G S i w else 0) =
        if w ∈ A then ∑ i : I, drawWeight G S i w else 0 := by
    by_cases hw : w ∈ A <;> simp [hw]
  simp_rw [hswap]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  calc
    (∑ w ∈ A, ∑ i : I, drawWeight G S i w) ≤
        ∑ _w ∈ A, 1 / ((S.remaining.card : ℝ) * L) := by
      exact Finset.sum_le_sum fun w _ =>
        sum_drawWeight_over_slots_le G S L hL hS hdom w
    _ = (A.card : ℝ) / ((S.remaining.card : ℝ) * L) := by
      simp [div_eq_mul_inv]

theorem noiseWeight_vertex_event_eq_drawWeight (p : Parameters) (q : ℕ)
    (G : Input I V) (S : State I V) (A : Finset V) :
    (∑ r : Noise I V, if r.2.1 ∈ A then noiseWeight p q G S r else 0) =
      ∑ i : I, ∑ w : V, if w ∈ A then drawWeight G S i w else 0 := by
  simp only [Noise, Fintype.sum_prod_type, noiseWeight]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w ∈ A
  · simp only [hw, ite_true, ← Finset.mul_sum, sum_flagsWeight, mul_one]
  · simp [hw]

theorem exceptional_noise_mass_le
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (p : Parameters) (S : State I V) (v : V)
    (L : ℝ) (hL : 0 < L) (hS : S.remaining.Nonempty)
    (hdom : ∀ i ∈ S.remaining, L ≤ ((domain G S i).card : ℝ)) :
    (∑ r : Noise I V, if r.2.1 ∈ G.exceptional v then noiseWeight p q G S r else 0) ≤
      (q : ℝ) ^ (1 / 8 : ℝ) / ((S.remaining.card : ℝ) * L) := by
  rw [noiseWeight_vertex_event_eq_drawWeight]
  exact (drawWeight_event_le_card_div G S (G.exceptional v) L hL hS hdom).trans
    (div_le_div_of_nonneg_right (hG.2.2.2.2.2.1 v)
      (mul_nonneg (Nat.cast_nonneg _) hL.le))

theorem exceptional_noise_mass_le_source_bound
    {G : Input I V} {q t : ℕ} (p : Parameters) (hp : p.Admissible)
    (hq : 0 < q) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (v : V) (hpre : Precheck p q t G S)
    (hscale : p.smin ≤ p.sizeScale q t)
    (hremaining : p.a * (q : ℝ) ≤ (S.remaining.card : ℝ)) :
    (∑ r : Noise I V, if r.2.1 ∈ G.exceptional v then noiseWeight p q G S r else 0) ≤
      2 * (q : ℝ) ^ (1 / 8 : ℝ) / (p.a * p.smin * p.c * (q : ℝ) ^ 2) := by
  have hc : 0 < p.c := hp.1
  have ha : 0 < p.a := hp.2.2.2.2.1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmin : 0 < p.smin := Real.exp_pos _
  let L : ℝ := p.smin * p.c * q / 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hdom : ∀ i ∈ S.remaining, L ≤ ((domain G S i).card : ℝ) := by
    intro i hi
    apply le_trans _ (hpre.2.2.2.1 i hi).2
    dsimp [L]
    gcongr
  have hprob := exceptional_noise_mass_le hG p S v L hL hpre.1 hdom
  calc
    (∑ r : Noise I V, if r.2.1 ∈ G.exceptional v then noiseWeight p q G S r else 0) ≤
        (q : ℝ) ^ (1 / 8 : ℝ) / ((S.remaining.card : ℝ) * L) := hprob
    _ ≤ (q : ℝ) ^ (1 / 8 : ℝ) / ((p.a * q) * L) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (mul_pos (mul_pos ha hqR) hL)
        (mul_le_mul_of_nonneg_right hremaining hL.le)
    _ = 2 * (q : ℝ) ^ (1 / 8 : ℝ) / (p.a * p.smin * p.c * (q : ℝ) ^ 2) := by
      dsimp [L]
      field_simp

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionFlagTail
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical

namespace Balanced.SelectionThinning

noncomputable section
variable {V : Type*} [Fintype V]

theorem thinning_true_cylinder (rate : V → ℝ) (A : Finset V) :
    (∑ b : V → Bool, if ∀ v ∈ A, b v = true then thinningMass rate b else 0) =
      ∏ v ∈ A, rate v := by
  have hprod (b : V → Bool) :
      (if ∀ v ∈ A, b v = true then thinningMass rate b else 0) =
        ∏ v, bitMass (rate v) (b v) *
          (if v ∈ A then (if b v = true then 1 else 0) else 1) := by
    by_cases hb : ∀ v ∈ A, b v = true
    · rw [ite_eq_left hb]
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ A
      · simp [hv, hb v hv]
      · simp [hv]
    · rw [ite_eq_right hb]
      obtain ⟨v, hv⟩ := not_forall.mp hb
      obtain ⟨hv, hflag⟩ := Classical.not_imp.mp hv
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp [hv, hflag]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun v (b : Bool) =>
    bitMass (rate v) b * (if v ∈ A then (if b = true then 1 else 0) else 1))]
  have hsum (v : V) :
      (∑ b : Bool, bitMass (rate v) b *
        (if v ∈ A then (if b = true then 1 else 0) else 1)) =
      if v ∈ A then rate v else 1 := by
    by_cases hv : v ∈ A <;> simp [hv, bitMass]
  simp_rw [hsum]
  simp

theorem thinning_count_tail (rate : V → ℝ)
    (hrate : ∀ v, 0 ≤ rate v ∧ rate v ≤ 1) (A : Finset V) (k : ℕ) :
    (∑ b : V → Bool,
      if k ≤ (A.filter (fun v => b v = true)).card then thinningMass rate b else 0) ≤
      (∑ v ∈ A, rate v) ^ k / k.factorial := by
  have hm (b : V → Bool) := thinningMass_nonneg rate hrate b
  calc
    _ ≤ ∑ b : V → Bool, ∑ T ∈ A.powersetCard k,
        if ∀ v ∈ T, b v = true then thinningMass rate b else 0 := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : k ≤ (A.filter (fun v => b v = true)).card
      · rw [ite_eq_left hb]
        obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hb
        have hTA : T ∈ A.powersetCard k :=
          Finset.mem_powersetCard.mpr ⟨hT.trans (Finset.filter_subset _ _), hcard⟩
        have htrue : ∀ v ∈ T, b v = true := fun v hv =>
          (Finset.mem_filter.mp (hT hv)).2
        calc
          thinningMass rate b =
              (if ∀ v ∈ T, b v = true then thinningMass rate b else 0) := by
                rw [ite_eq_left htrue]
          _ ≤ _ := Finset.single_le_sum (s := A.powersetCard k)
            (f := fun T : Finset V => if ∀ v ∈ T, b v = true then thinningMass rate b else 0)
            (fun T _ => by split <;> first | exact hm b | exact le_rfl) hTA
      · rw [ite_eq_right hb]
        exact Finset.sum_nonneg (fun T _ => by split <;> first | exact hm b | exact le_rfl)
    _ = ∑ T ∈ A.powersetCard k, ∏ v ∈ T, rate v := by
      rw [Finset.sum_comm]
      simp_rw [thinning_true_cylinder]
    _ ≤ _ := Balanced.sum_prod_powersetCard_le A rate (fun v _ => (hrate v).1) k

end
end Balanced.SelectionThinning

namespace Balanced.Selection.Process

noncomputable section
variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] [Fintype V] in

theorem thinned_inter_subset_true (G : Input I V) (S : State I V)
    (w : V) (flags : V → Bool) (A : Finset V) :
    thinned G S w flags ∩ A ⊆ A.filter (fun v => flags v = true) := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hv, hA⟩
  exact Finset.mem_filter.mpr ⟨hA, (Finset.mem_filter.mp hv).2.2⟩

omit [Fintype I] in

theorem flags_thinned_tail_le (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hpre : Precheck p q t G S)
    (w : V) (A : Finset V) (m : ℝ)
    (hmean : ∑ v ∈ A, thinningRate p q G S v ≤ m) :
    (∑ flags : V → Bool,
      if (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S w flags ∩ A).card : ℝ)
      then flagsWeight p q G S flags else 0) ≤
      (Real.exp 1 * m / (BernoulliTail.thinningCutoff (1 / 8) q : ℝ)) ^
        BernoulliTail.thinningCutoff (1 / 8) q := by
  let k := BernoulliTail.thinningCutoff (1 / 8) q
  have hrate (v : V) : 0 ≤ thinningRate p q G S v ∧ thinningRate p q G S v ≤ 1 := by
    have h := thinningRate_bounds_of_precheck p q t G S hpre v
    exact ⟨h.1, h.2.trans hpre.2.2.1.le⟩
  have hm : 0 ≤ m := (Finset.sum_nonneg (fun v _ => (hrate v).1)).trans hmean
  calc
    _ ≤ ∑ flags : V → Bool,
        if k ≤ (A.filter (fun v => flags v = true)).card then
          SelectionThinning.thinningMass (thinningRate p q G S) flags else 0 := by
      apply Finset.sum_le_sum
      intro flags _
      by_cases hf : (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S w flags ∩ A).card : ℝ)
      · have hk : k ≤ (A.filter (fun v => flags v = true)).card := by
          have hsmall : k ≤ (thinned G S w flags ∩ A).card := by
            apply Nat.succ_le_iff.mpr
            exact (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg q) _)).mpr hf
          exact hsmall.trans (Finset.card_le_card (thinned_inter_subset_true G S w flags A))
        simp only [hf, ite_true, hk]
        rfl
      · rw [ite_eq_right hf]
        split
        · exact SelectionThinning.thinningMass_nonneg _ hrate flags
        · exact le_rfl
    _ ≤ (∑ v ∈ A, thinningRate p q G S v) ^ k / k.factorial :=
      SelectionThinning.thinning_count_tail _ hrate A k
    _ ≤ m ^ k / k.factorial := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (Finset.sum_nonneg (fun v _ => (hrate v).1)) hmean k
    _ ≤ _ := Balanced.pow_div_factorial_le_exp_ratio m hm k (by
      dsimp [k, BernoulliTail.thinningCutoff]
      omega)

theorem noise_thinned_tail_le (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hpre : Precheck p q t G S)
    (A : Finset V) (m : ℝ)
    (hmean : ∑ v ∈ A, thinningRate p q G S v ≤ m) :
    (∑ r : Noise I V,
      if (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S r.2.1 r.2.2 ∩ A).card : ℝ)
      then noiseWeight p q G S r else 0) ≤
      (Real.exp 1 * m / (BernoulliTail.thinningCutoff (1 / 8) q : ℝ)) ^
        BernoulliTail.thinningCutoff (1 / 8) q := by
  let ε := (Real.exp 1 * m / (BernoulliTail.thinningCutoff (1 / 8) q : ℝ)) ^
    BernoulliTail.thinningCutoff (1 / 8) q
  simp only [Noise, Fintype.sum_prod_type]
  calc
    _ = ∑ i : I, ∑ w : V, drawWeight G S i w *
        (∑ flags : V → Bool,
          if (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S w flags ∩ A).card : ℝ)
          then flagsWeight p q G S flags else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro flags _
      split <;> simp_all [noiseWeight]
    _ ≤ ∑ i : I, ∑ w : V, drawWeight G S i w * ε := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_left (flags_thinned_tail_le p q t G S hpre w A m hmean)
        (drawWeight_nonnegative G S i w)
    _ = ε := by
      simp_rw [← Finset.sum_mul]
      rw [sum_drawWeight G S hpre.1 (fun i hi => (hpre.2.2.2.1 i hi).1), one_mul]

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionPostcheckTail
attribute [-instance] _root_.OAI.Balanced.Selection.Process.snapshotPathLaw_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical

namespace Balanced.Selection.Process

noncomputable section

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in

theorem flag_mean_le_card_mul_alpha (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hpre : Precheck p q t G S) (A : Finset V) :
    (∑ v ∈ A, thinningRate p q G S v) ≤ (A.card : ℝ) * p.alpha q := by
  calc
    _ ≤ ∑ _v ∈ A, p.alpha q := Finset.sum_le_sum
      (fun v _ => (thinningRate_bounds_of_precheck p q t G S hpre v).2)
    _ = _ := by simp

theorem domain_flag_mean_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) (i : I) :
    (∑ v ∈ domain G S i, thinningRate p q G S v) ≤ postcheckMean p := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hP : 0 ≤ p.Pstar := by
    have h := hpre.2.1
    simpa using (le_div_iff₀ hqR).mp h
  have hdom : ((domain G S i).card : ℝ) ≤ q := by
    apply le_trans _ (show ((slotVertices G i).card : ℝ) ≤ q by exact_mod_cast (hG.2.2.1 i).2)
    exact_mod_cast Finset.card_le_card (show domain G S i ⊆ slotVertices G i from by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩)
  calc
    _ ≤ ((domain G S i).card : ℝ) * p.alpha q :=
      flag_mean_le_card_mul_alpha p q t G S hpre _
    _ ≤ (q : ℝ) * p.alpha q := mul_le_mul_of_nonneg_right hdom hpre.2.1
    _ = p.Pstar := by unfold Parameters.alpha; field_simp
    _ ≤ postcheckMean p := by
      unfold postcheckMean
      simpa using mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) p.C) hP

theorem neighbor_flag_mean_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) (v : V) :
    (∑ u ∈ neighbors G v, thinningRate p q G S u) ≤ postcheckMean p := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hP : 0 ≤ p.Pstar := by
    have h := hpre.2.1
    simpa using (le_div_iff₀ hqR).mp h
  calc
    _ ≤ ((neighbors G v).card : ℝ) * p.alpha q :=
      flag_mean_le_card_mul_alpha p q t G S hpre _
    _ ≤ (p.C * q) * p.alpha q :=
      mul_le_mul_of_nonneg_right (hG.2.2.2.1 v) hpre.2.1
    _ = p.Pstar * p.C := by unfold Parameters.alpha; field_simp
    _ ≤ postcheckMean p :=
      mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) p.C) hP

end
end Balanced.Selection.Process

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionCensorMassBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Balanced.Selection.Process

variable {I V : Type*} [Fintype I] [Fintype V]

theorem noise_domain_overflow_mass_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) (i : I) :
    (∑ r : Noise I V,
      if (q : ℝ) ^ (1 / 8 : ℝ) <
          ((thinned G S r.2.1 r.2.2 ∩ domain G S i).card : ℝ)
      then noiseWeight p q G S r else 0) ≤ postcheckTail p q := by
  exact noise_thinned_tail_le p q t G S hpre (domain G S i) (postcheckMean p)
    (domain_flag_mean_le p q t hq G hG S hpre i)

theorem noise_degree_censor_mass_le (p : Parameters) (hp : p.Admissible)
    (q t : ℕ) (hq : 0 < q) (G : Input I V)
    (hG : GraphBounds G q p.c p.C) (S : State I V)
    (hpre : Precheck p q t G S) (v : V)
    (hscale : p.smin ≤ p.sizeScale q t)
    (hremaining : p.a * (q : ℝ) ≤ (S.remaining.card : ℝ)) :
    (∑ r : Noise I V,
      if r.2.1 ∈ G.exceptional v ∨ (q : ℝ) ^ (1 / 8 : ℝ) <
          ((thinned G S r.2.1 r.2.2 ∩ neighbors G v).card : ℝ)
      then noiseWeight p q G S r else 0) ≤
      2 * (q : ℝ) ^ (1 / 8 : ℝ) /
        (p.a * p.smin * p.c * (q : ℝ) ^ 2) + postcheckTail p q := by
  calc
    _ ≤ (∑ r : Noise I V,
          if r.2.1 ∈ G.exceptional v then noiseWeight p q G S r else 0) +
        (∑ r : Noise I V,
          if (q : ℝ) ^ (1 / 8 : ℝ) <
              ((thinned G S r.2.1 r.2.2 ∩ neighbors G v).card : ℝ)
          then noiseWeight p q G S r else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro r _
      have hn := noiseWeight_nonnegative_of_precheck p q t G S hpre r
      by_cases he : r.2.1 ∈ G.exceptional v <;>
        by_cases ht : (q : ℝ) ^ (1 / 8 : ℝ) <
          ((thinned G S r.2.1 r.2.2 ∩ neighbors G v).card : ℝ) <;>
        simp only [he, ht, true_or, false_or, ite_true, ite_false] <;> linarith
    _ ≤ _ := add_le_add
      (exceptional_noise_mass_le_source_bound p hp hq hG S v hpre hscale hremaining)
      (noise_thinned_tail_le p q t G S hpre (neighbors G v) (postcheckMean p)
        (neighbor_flag_mean_le p q t hq G hG S hpre v))

theorem noise_degree_censor_mass_le_source (p : Parameters) (hp : p.Admissible)
    (q t : ℕ) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (ht : t ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (hpre : Precheck p q t G S)
    (hcard : S.remaining.card + t = Fintype.card I) (v : V) :
    (∑ r : Noise I V,
      if r.2.1 ∈ G.exceptional v ∨ (q : ℝ) ^ (1 / 8 : ℝ) <
          ((thinned G S r.2.1 r.2.2 ∩ neighbors G v).card : ℝ)
      then noiseWeight p q G S r else 0) ≤
      2 * (q : ℝ) ^ (1 / 8 : ℝ) /
        (p.a * p.smin * p.c * (q : ℝ) ^ 2) + postcheckTail p q := by
  apply noise_degree_censor_mass_le p hp q t (by omega) G hG S hpre v
  · exact (Parameters.source_scale_bounds hp hq hPq hG.1 ht).1
  · have hrem := Parameters.remaining_ge hp (show q ≤ Fintype.card I by
      have hn := hG.1
      omega) ht
    have heq : S.remaining.card = Fintype.card I - t := by omega
    simpa only [heq] using hrem

theorem domainOverflowMass_le_postcheckTail (p : Parameters) (q t : ℕ)
    (hq : 0 < q) (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) (i : I) :
    domainOverflowMass p q G S i ≤ postcheckTail p q :=
  noise_domain_overflow_mass_le p q t hq G hG S hpre i

theorem degreeCensorMass_le_source (p : Parameters) (hp : p.Admissible)
    (q t : ℕ) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (ht : t ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (hpre : Precheck p q t G S)
    (hcard : S.remaining.card + t = Fintype.card I) (v : V) :
    degreeCensorMass p q G S v ≤
      2 * (q : ℝ) ^ (1 / 8 : ℝ) /
        (p.a * p.smin * p.c * (q : ℝ) ^ 2) + postcheckTail p q :=
  noise_degree_censor_mass_le_source p hp q t hq hPq G hG ht S hpre hcard v

theorem tendsto_polynomial_mul_postcheckTail (p : Parameters) (hp : p.Admissible)
    (r : ℕ) :
    Filter.Tendsto (fun q : ℕ => (q : ℝ) ^ r * postcheckTail p q)
      Filter.atTop (nhds 0) := by
  have hm : 0 ≤ postcheckMean p :=
    mul_nonneg (Parameters.Pstar_pos hp).le
      ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 p.C))
  exact BernoulliTail.tendsto_polynomial_mul_thinning_tail
    (by norm_num : (0 : ℝ) < 1 / 8) r (Real.exp 1 * postcheckMean p)
    (mul_nonneg (Real.exp_pos 1).le hm)

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionTrueCountConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem abs_count_error_le_of_rescaled {x x₀ s A : ℝ}
    (hs : 0 < s) (hsone : s ≤ 1) (h : |x / s - x₀| ≤ A) :
    |x - s * x₀| ≤ A := by
  have he : x - s * x₀ = s * (x / s - x₀) := by field_simp
  rw [he, abs_mul, abs_of_pos hs]
  exact (mul_le_of_le_one_left (abs_nonneg _) hsone).trans h

theorem count_upper_error_le_of_rescaled {x x₀ s A : ℝ}
    (hs : 0 < s) (hsone : s ≤ 1) (hA : 0 ≤ A) (h : x / s - x₀ ≤ A) :
    x ≤ s * x₀ + A := by
  have he : x - s * x₀ = s * (x / s - x₀) := by field_simp
  have hu : x - s * x₀ ≤ A := by
    rw [he]
    exact (mul_le_mul_of_nonneg_left h hs.le).trans
      (mul_le_of_le_one_left hA hsone)
  linarith

theorem ae_true_counts_of_track_bounds {p : Parameters} (hp : p.Admissible)
    {q T : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (hT : T ≤ p.lastMainTime q (Fintype.card I))
    (A : ℝ) (hA : 0 ≤ A) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      (∀ i t, t ≤ T → |domainTrack p q G i t ω - domainTrack p q G i 0 ω| ≤ A) →
      (∀ v t, t ≤ T → degreeTrack p q G v t ω - degreeTrack p q G v 0 ω ≤ A) →
      ∀ t S, t ≤ T → (ω t).1 = some S →
        (∀ i ∈ S.remaining,
          |((domain G S i).card : ℝ) - p.sizeScale q t * (domain G initialState i).card| ≤ A) ∧
        (∀ v ∈ currentVertices G S,
          (degree G S v : ℝ) ≤
            p.degreeScale q (Fintype.card I) t * degree G initialState v + A) := by
  filter_upwards [ae_domainTrack_agreement p q G, ae_degreeTrack_agreement p q G hG]
    with ω hdom hdeg
  intro hdomBound hdegBound t S ht hS
  have hscale := Parameters.source_scale_bounds hp hq hPq hG.1 (ht.trans hT)
  have hs : 0 < p.sizeScale q t := (Real.exp_pos _).trans_le hscale.1
  have hb : 0 < p.degreeScale q (Fintype.card I) t := by
    have hsmin : 0 < p.smin := Real.exp_pos _
    have ha := (Parameters.a_bounds hp).1
    have hmin : 0 < p.smin * p.a / 3 := by positivity
    exact hmin.trans_le hscale.2.2.1
  constructor
  · intro i hi
    apply abs_count_error_le_of_rescaled hs hscale.2.1
    simpa only [hdom i t S hS hi, domainTrack_zero] using hdomBound i t ht
  · intro v hv
    apply count_upper_error_le_of_rescaled hb hscale.2.2.2 hA
    simpa only [hdeg v t S hS hv, degreeTrack_zero] using hdegBound v t ht

theorem true_count_failure_probability_le {p : Parameters} (hp : p.Admissible)
    {q T : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hTpos : 1 ≤ T)
    (hT : T ≤ p.lastMainTime q (Fintype.card I))
    {εd εv : ℝ} (hεd : 0 ≤ εd) (hεv : 0 ≤ εv)
    (hmassd : ∀ i j, j < T → ∀ S : State I V, Precheck p q j G S →
      i ∈ S.remaining → domainOverflowMass p q G S i ≤ εd)
    (hmassv : ∀ v j, j < T → ∀ S : State I V, Precheck p q j G S →
      S.remaining.card = Fintype.card I - j →
      v ∈ currentVertices G S → degreeCensorMass p q G S v ≤ εv)
    (u A : ℝ) (hu : 0 < u) (hA : 0 ≤ A)
    (hDd : ∀ t ≤ T, (t : ℝ) * ((q : ℝ) * εd / p.smin) + u ≤ A)
    (hDv : ∀ t ≤ T, (t : ℝ) * (p.C * q * εv / (p.smin * p.a / 3)) + u ≤ A) :
    (snapshotPathLaw p q G).real {ω | ¬ (∀ t S, t ≤ T → (ω t).1 = some S →
      (∀ i ∈ S.remaining,
        |((domain G S i).card : ℝ) - p.sizeScale q t * (domain G initialState i).card| ≤ A) ∧
      (∀ v ∈ currentVertices G S, (degree G S v : ℝ) ≤
        p.degreeScale q (Fintype.card I) t * degree G initialState v + A))} ≤
      2 * Fintype.card I * (T + 1 : ℕ) *
        Real.exp (-u ^ 2 / (8 * (T : ℝ) * (domainTrackJumpBound p q) ^ 2)) +
      2 * Fintype.card V * (T + 1 : ℕ) *
        Real.exp (-u ^ 2 / (8 * (T : ℝ) * (degreeTrackJumpBound p q) ^ 2)) := by
  let E := {ω | ∃ i t, t ≤ T ∧ (t : ℝ) * ((q : ℝ) * εd / p.smin) + u ≤
    |domainTrack p q G i t ω - domainTrack p q G i 0 ω|}
  let F := {ω | ∃ v t, t ≤ T ∧ (t : ℝ) *
    (p.C * q * εv / (p.smin * p.a / 3)) + u ≤
      degreeTrack p q G v t ω - degreeTrack p q G v 0 ω}
  have hsub : (snapshotPathLaw p q G).real {ω | ¬ (∀ t S, t ≤ T → (ω t).1 = some S →
      (∀ i ∈ S.remaining,
        |((domain G S i).card : ℝ) - p.sizeScale q t * (domain G initialState i).card| ≤ A) ∧
      (∀ v ∈ currentVertices G S, (degree G S v : ℝ) ≤
        p.degreeScale q (Fintype.card I) t * degree G initialState v + A))} ≤
      (snapshotPathLaw p q G).real (E ∪ F) := by
    apply measureReal_le_of_ae_imp
    filter_upwards [ae_true_counts_of_track_bounds hp hG hq hPq hT A hA] with ω hω
    intro hbad
    by_contra hgood
    have hne : ω ∉ E := fun h => hgood (Or.inl h)
    have hnf : ω ∉ F := fun h => hgood (Or.inr h)
    apply hbad (hω ?_ ?_)
    · intro i t ht
      by_contra h
      exact hne ⟨i, t, ht, (hDd t ht).trans (le_of_lt (lt_of_not_ge h))⟩
    · intro v t ht
      by_contra h
      exact hnf ⟨v, t, ht, (hDv t ht).trans (le_of_lt (lt_of_not_ge h))⟩
  exact hsub.trans ((measureReal_union_le E F).trans
    (add_le_add (simultaneous_domainTrack_tail_of_mass hp hG hq hPq hTpos hT
      hεd hmassd u hu) (simultaneous_degreeTrack_tail_of_mass hp hG hq hPq hTpos hT
      hεv hmassv u hu)))

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionConcentrationAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace Balanced.Selection.Process

theorem trackJumpCoefficient_pos {p : Parameters} (hp : p.Admissible) :
    0 < trackJumpCoefficient p := by
  have hP := Parameters.Pstar_pos hp
  have hs : 0 < p.smin := Real.exp_pos _
  have ha := (Parameters.a_bounds hp).1
  have hC := hp.2.1
  unfold trackJumpCoefficient
  positivity

theorem trackJumpBounds_le {p : Parameters} (hp : p.Admissible) {q : ℕ} (hq : 1 ≤ q) :
    domainTrackJumpBound p q ≤ trackJumpCoefficient p * (q : ℝ) ^ (1 / 8 : ℝ) ∧
    degreeTrackJumpBound p q ≤ trackJumpCoefficient p * (q : ℝ) ^ (1 / 8 : ℝ) := by
  have hP := Parameters.Pstar_pos hp
  have hs : 0 < p.smin := Real.exp_pos _
  have ha := (Parameters.a_bounds hp).1
  have hC := hp.2.1
  have hb : 0 < p.smin * p.a / 3 := by positivity
  have hpow : 1 ≤ (q : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hq) (by norm_num)
  have hcoef : 0 < p.C * (p.Pstar + 1 / p.a) := by positivity
  have hd : (2 + p.Pstar) / p.smin ≤ trackJumpCoefficient p := by
    unfold trackJumpCoefficient
    exact le_add_of_nonneg_right (by positivity)
  have hv : (3 + p.C * (p.Pstar + 1 / p.a)) / (p.smin * p.a / 3) ≤
      trackJumpCoefficient p := by
    unfold trackJumpCoefficient
    exact le_add_of_nonneg_left (by positivity)
  constructor
  · calc
      domainTrackJumpBound p q ≤
          (2 + p.Pstar) / p.smin * (q : ℝ) ^ (1 / 8 : ℝ) := by
        unfold domainTrackJumpBound
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hs.le
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hd (by positivity)
  · calc
      degreeTrackJumpBound p q ≤
          (3 + p.C * (p.Pstar + 1 / p.a)) / (p.smin * p.a / 3) *
            (q : ℝ) ^ (1 / 8 : ℝ) := by
        unfold degreeTrackJumpBound
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hb.le
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hv (by positivity)

theorem source_azuma_exp_le {q T : ℕ} {L K : ℝ}
    (hq : 0 < q) (hT : 1 ≤ T) (hTq : T ≤ 3 * q)
    (hL : 0 < L) (hK : 0 < K) (hLK : L ≤ K * (q : ℝ) ^ (1 / 8 : ℝ)) :
    Real.exp (-((q : ℝ) ^ (4 / 5 : ℝ) / 2) ^ 2 /
      (8 * (T : ℝ) * L ^ 2)) ≤
      Real.exp (-((q : ℝ) ^ (7 / 20 : ℝ) / (96 * K ^ 2))) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hTR : 0 < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  have hTqR : (T : ℝ) ≤ 3 * q := by exact_mod_cast hTq
  have hden : 8 * (T : ℝ) * L ^ 2 ≤
      8 * (3 * (q : ℝ)) * (K * (q : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := by
    gcongr
  have hdiv := div_le_div_of_nonneg_left
    (sq_nonneg ((q : ℝ) ^ (4 / 5 : ℝ) / 2))
    (by positivity : 0 < 8 * (T : ℝ) * L ^ 2) hden
  rw [selection_azuma_exponent hqR hK] at hdiv
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg hdiv

theorem tendsto_trackConcentrationError {p : Parameters} (hp : p.Admissible) :
    Tendsto (trackConcentrationError p) atTop (𝓝 0) := by
  have hK := trackJumpCoefficient_pos hp
  have hc : 0 < 1 / (96 * (trackJumpCoefficient p) ^ 2) := by positivity
  convert tendsto_selection_simultaneous_error 48 hc using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  unfold trackConcentrationError
  congr 2
  ring

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionSourceConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace Balanced.Selection.Process
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

theorem postcheckTail_nonneg_of_admissible {p : Parameters} (hp : p.Admissible) (q : ℕ) :
    0 ≤ postcheckTail p q := by
  have hP := Parameters.Pstar_pos hp
  have hC := hp.2.1
  unfold postcheckTail postcheckMean
  positivity

theorem sourceDegreeCensorBound_nonneg {p : Parameters} (hp : p.Admissible) (q : ℕ) :
    0 ≤ sourceDegreeCensorBound p q := by
  have he := postcheckTail_nonneg_of_admissible hp q
  have hs : 0 < p.smin := Real.exp_pos _
  have ha := (Parameters.a_bounds hp).1
  have hc := hp.1
  unfold sourceDegreeCensorBound
  positivity

theorem eventually_small_power_error (A B : ℝ) :
    ∀ᶠ q : ℕ in atTop,
      A * (q : ℝ) ^ (1 / 8 : ℝ) + B ≤ (q : ℝ) ^ (4 / 5 : ℝ) / 2 := by
  have h₁ := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 27 / 40)).comp
    tendsto_natCast_atTop_atTop
  have h₂ := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp
    tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun q : ℕ => A * (q : ℝ) ^ (-(27 / 40 : ℝ)) +
      B * (q : ℝ) ^ (-(4 / 5 : ℝ))) atTop (𝓝 0) := by
    simpa using (h₁.const_mul A).add (h₂.const_mul B)
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_gt_atTop (0 : ℕ)] with q hq hqpos
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hp : 0 < (q : ℝ) ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hqr _
  have he : (A * (q : ℝ) ^ (1 / 8 : ℝ) + B) / (q : ℝ) ^ (4 / 5 : ℝ) =
      A * (q : ℝ) ^ (-(27 / 40 : ℝ)) + B * (q : ℝ) ^ (-(4 / 5 : ℝ)) := by
    rw [add_div, mul_div_assoc, ← Real.rpow_sub hqr]
    norm_num
    rw [Real.rpow_neg hqr.le, div_eq_mul_inv]
  have hdiv : (A * (q : ℝ) ^ (1 / 8 : ℝ) + B) / (q : ℝ) ^ (4 / 5 : ℝ) ≤ 1 / 2 :=
    he.trans_le hq.le
  have h := (div_le_iff₀ hp).mp hdiv
  linarith

theorem tendsto_domain_drift_budget {p : Parameters} (hp : p.Admissible) :
    Tendsto (fun q : ℕ => (3 * (q : ℝ)) * ((q : ℝ) * postcheckTail p q / p.smin))
      atTop (𝓝 0) := by
  convert (tendsto_polynomial_mul_postcheckTail p hp 2).const_mul (3 / p.smin) using 1
  · funext q
    ring
  · simp

theorem eventually_source_drift_budgets {p : Parameters} (hp : p.Admissible) :
    ∀ᶠ q : ℕ in atTop,
      (3 * (q : ℝ)) * ((q : ℝ) * postcheckTail p q / p.smin) ≤
        (q : ℝ) ^ (4 / 5 : ℝ) / 2 ∧
      (3 * (q : ℝ)) * (p.C * q * sourceDegreeCensorBound p q / (p.smin * p.a / 3)) ≤
        (q : ℝ) ^ (4 / 5 : ℝ) / 2 := by
  let b := p.smin * p.a / 3
  let A := 6 * p.C / (p.a * p.smin * p.c * b)
  have hs : 0 < p.smin := Real.exp_pos _
  have ha := (Parameters.a_bounds hp).1
  have hc := hp.1
  have hb : 0 < b := by dsimp [b]; positivity
  have htail : Tendsto (fun q : ℕ => (3 * p.C / b) * ((q : ℝ) ^ 2 * postcheckTail p q))
      atTop (𝓝 0) := by
    simpa using (tendsto_polynomial_mul_postcheckTail p hp 2).const_mul (3 * p.C / b)
  filter_upwards [(tendsto_domain_drift_budget hp).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    htail.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_small_power_error 0 1, eventually_small_power_error A 1,
    eventually_gt_atTop (0 : ℕ)] with q hd ht hsmall hlarge hq
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  constructor
  · exact hd.le.trans (by simpa using hsmall)
  · have he : (3 * (q : ℝ)) *
        (p.C * q * sourceDegreeCensorBound p q / (p.smin * p.a / 3)) =
        A * (q : ℝ) ^ (1 / 8 : ℝ) +
          (3 * p.C / b) * ((q : ℝ) ^ 2 * postcheckTail p q) := by
        dsimp [sourceDegreeCensorBound, A, b]
        field_simp
        ring
    rw [he]
    linarith

theorem card_vertices_le_slots_mul_order {q : ℕ} {G : Input I V}
    {c C : ℝ} (hG : GraphBounds G q c C) : Fintype.card V ≤ Fintype.card I * q := by
  classical
  have he : Fintype.card V = ∑ i : I, (slotVertices G i).card := by
    simpa only [Finset.card_univ, slotVertices] using
      (Finset.card_eq_sum_card_fiberwise (f := G.slot)
        (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _))
  rw [he]
  calc
    _ ≤ ∑ _i : I, q := Finset.sum_le_sum (fun i _ => (hG.2.2.1 i).2)
    _ = _ := by simp

theorem source_track_tail_sum_le_error {p : Parameters} (hp : p.Admissible)
    {q T : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hT : 1 ≤ T) (hTq : T ≤ 3 * q) :
    2 * Fintype.card I * (T + 1 : ℕ) *
        Real.exp (-((q : ℝ) ^ (4 / 5 : ℝ) / 2) ^ 2 /
          (8 * (T : ℝ) * (domainTrackJumpBound p q) ^ 2)) +
      2 * Fintype.card V * (T + 1 : ℕ) *
        Real.exp (-((q : ℝ) ^ (4 / 5 : ℝ) / 2) ^ 2 /
          (8 * (T : ℝ) * (degreeTrackJumpBound p q) ^ 2)) ≤
      trackConcentrationError p q := by
  let E := Real.exp (-((q : ℝ) ^ (7 / 20 : ℝ) /
    (96 * (trackJumpCoefficient p) ^ 2)))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hdom := source_azuma_exp_le (by omega : 0 < q) hT hTq
    (domainTrackJumpBound_pos hp q) (trackJumpCoefficient_pos hp)
    (trackJumpBounds_le hp (by omega : 1 ≤ q)).1
  have hdeg := source_azuma_exp_le (by omega : 0 < q) hT hTq
    (degreeTrackJumpBound_pos hp q) (trackJumpCoefficient_pos hp)
    (trackJumpBounds_le hp (by omega : 1 ≤ q)).2
  have hn : (Fintype.card I : ℝ) ≤ 3 * q := by
    exact_mod_cast (show Fintype.card I ≤ 3 * q by rw [hG.1]; omega)
  have hm : (Fintype.card V : ℝ) ≤ 3 * (q : ℝ) ^ 2 := by
    have h := card_vertices_le_slots_mul_order hG
    have hnN : Fintype.card I ≤ 3 * q := by rw [hG.1]; omega
    have h' := h.trans (Nat.mul_le_mul_right q hnN)
    exact_mod_cast (by simpa [pow_two, Nat.mul_assoc] using h')
  have ht : ((T + 1 : ℕ) : ℝ) ≤ 4 * q := by
    exact_mod_cast (show T + 1 ≤ 4 * q by omega)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hc : 2 * (Fintype.card I : ℝ) * (T + 1 : ℕ) +
      2 * (Fintype.card V : ℝ) * (T + 1 : ℕ) ≤ 48 * (q : ℝ) ^ 3 := by
    calc
      _ ≤ 2 * (3 * (q : ℝ)) * (4 * q) +
          2 * (3 * (q : ℝ) ^ 2) * (4 * q) := by gcongr
      _ ≤ _ := by nlinarith [sq_nonneg (q : ℝ),
        mul_nonneg (sq_nonneg (q : ℝ)) (sub_nonneg.mpr hqR)]
  calc
    _ ≤ (2 * (Fintype.card I : ℝ) * (T + 1 : ℕ) +
        2 * (Fintype.card V : ℝ) * (T + 1 : ℕ)) * E := by
      rw [add_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hdom (by positivity))
        (mul_le_mul_of_nonneg_left hdeg (by positivity))
    _ ≤ 48 * (q : ℝ) ^ 3 * E := mul_le_mul_of_nonneg_right hc hE
    _ = _ := rfl

theorem source_true_count_failure_probability_le {p : Parameters} (hp : p.Admissible)
    {q : ℕ} {G : Input I V} (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (hDd : (3 * (q : ℝ)) * ((q : ℝ) * postcheckTail p q / p.smin) ≤
      (q : ℝ) ^ (4 / 5 : ℝ) / 2)
    (hDv : (3 * (q : ℝ)) * (p.C * q * sourceDegreeCensorBound p q /
      (p.smin * p.a / 3)) ≤ (q : ℝ) ^ (4 / 5 : ℝ) / 2) :
    (snapshotPathLaw p q G).real {ω | ¬ (∀ t S,
      t ≤ p.lastMainTime q (Fintype.card I) → (ω t).1 = some S →
      (∀ i ∈ S.remaining,
        |((domain G S i).card : ℝ) - p.sizeScale q t * (domain G initialState i).card| ≤
          (q : ℝ) ^ (4 / 5 : ℝ)) ∧
      (∀ v ∈ currentVertices G S, (degree G S v : ℝ) ≤
        p.degreeScale q (Fintype.card I) t * degree G initialState v +
          (q : ℝ) ^ (4 / 5 : ℝ)))} ≤ trackConcentrationError p q := by
  let T := p.lastMainTime q (Fintype.card I)
  have hTq : T ≤ 3 * q := by
    exact (Nat.sub_le _ _).trans (by rw [hG.1]; omega)
  have hTpos : 1 ≤ T := by
    have hh := Parameters.tailSlots_le_order hp q
    dsimp [T, Parameters.lastMainTime]
    rw [hG.1]
    omega
  have hs : 0 < p.smin := Real.exp_pos _
  have ha := (Parameters.a_bounds hp).1
  have hb : 0 < p.smin * p.a / 3 := by positivity
  have he := postcheckTail_nonneg_of_admissible hp q
  have hev := sourceDegreeCensorBound_nonneg hp q
  apply (true_count_failure_probability_le hp hG hq hPq hTpos le_rfl he hev
    (fun i j _ S hpre _ => domainOverflowMass_le_postcheckTail p q j (by omega) G hG S hpre i)
    (fun v j hj S hpre hcard _ => degreeCensorMass_le_source p hp q j hq hPq G hG
      (by omega) S hpre (by have hn := Nat.sub_le (Fintype.card I) (p.tailSlots q); dsimp [T, Parameters.lastMainTime] at hj; omega) v)
    ((q : ℝ) ^ (4 / 5 : ℝ) / 2) ((q : ℝ) ^ (4 / 5 : ℝ))
    (by positivity) (by positivity) ?_ ?_).trans
      (source_track_tail_sum_le_error hp hG hq hTpos hTq)
  · intro t ht
    have htR : (t : ℝ) ≤ 3 * q := by exact_mod_cast ht.trans hTq
    have hh := (mul_le_mul_of_nonneg_right htR (div_nonneg
      (mul_nonneg (Nat.cast_nonneg q) he) hs.le)).trans hDd
    linarith
  · intro t ht
    have htR : (t : ℝ) ≤ 3 * q := by exact_mod_cast ht.trans hTq
    have hh := (mul_le_mul_of_nonneg_right htR (div_nonneg
      (mul_nonneg (mul_nonneg hp.2.1.le (Nat.cast_nonneg q)) hev) hb.le)).trans hDv
    linarith

theorem exists_source_concentration_threshold {p : Parameters} (hp : p.Admissible) :
    ∃ Q : ℕ, ∀ q ≥ Q,
      2 ≤ q ∧ 2 * p.Pstar ≤ q ∧
      (3 * (q : ℝ)) * ((q : ℝ) * postcheckTail p q / p.smin) ≤
        (q : ℝ) ^ (4 / 5 : ℝ) / 2 ∧
      (3 * (q : ℝ)) * (p.C * q * sourceDegreeCensorBound p q / (p.smin * p.a / 3)) ≤
        (q : ℝ) ^ (4 / 5 : ℝ) / 2 := by
  apply Filter.eventually_atTop.1
  filter_upwards [Parameters.eventually_scale_regime p,
    eventually_source_drift_budgets hp] with q hq hd
  exact ⟨hq.1, hq.2, hd.1, hd.2⟩

end Balanced.Selection.Process

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_SelectionConcentrationUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace Balanced.Selection.Process
universe u v w
attribute [local instance] Classical.propDecidable

theorem exists_uniformConcentratedPath_estimate_oai (p : Parameters) (hp : p.Admissible) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ q : ℕ in atTop,
        ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
        ∀ G : Input I V, GraphBounds G q p.c p.C →
          (snapshotPathLaw p q G).real {ω | ¬ FirstAbort.ConcentratedPath p q G
            (p.lastMainTime q (Fintype.card I)) ω} ≤ ε q := by
  refine ⟨trackConcentrationError p, tendsto_trackConcentrationError hp, ?_⟩
  obtain ⟨Q, hQ⟩ := exists_source_concentration_threshold hp
  filter_upwards [eventually_ge_atTop Q] with q hq
  obtain ⟨hq2, hPq, hDd, hDv⟩ := hQ q hq
  intro I V _ _ G hG
  have h := source_true_count_failure_probability_le hp hG hq2 hPq hDd hDv
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, FirstAbort.ConcentratedPath,
    FirstAbort.StateConcentration, domain, degree, initialState, currentVertices, slotVertices,
    Finset.mem_univ, Finset.filter_true, Finset.inter_univ]
  apply not_congr
  constructor
  · intro h t S ht hS
    exact h t ht S hS
  · intro h t ht S hS
    exact h t S ht hS
end Balanced.Selection.Process

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.Balanced.Selection.Process.exists_uniformConcentratedPath_estimate_oai.{u, v} := @OAI.Balanced.Selection.Process.exists_uniformConcentratedPath_estimate_oai.{u, v}
