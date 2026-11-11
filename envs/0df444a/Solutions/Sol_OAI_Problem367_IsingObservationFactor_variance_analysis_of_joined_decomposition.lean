-- Prove2me | solution 1 for OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:48:37.64971+00:00
-- url     : https://prove2.me/submissions/09d22c72-aa6a-497f-a178-a9b20c53873d

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_IsingContinuousCopyCoefficients_response_row_energy
import Theorems.Thm_OAI_Problem367_IsingCopyEnergy_copy_row_energy_integrable
import Theorems.Thm_OAI_Problem367_IsingCopySquareDensity_integral_integral_stopped_noise_add_drift_eq_actual
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_actual_variance_analysis_of_common_local_square
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_ae_horizon_stopped_continuousDifference_bound
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_continuousPosterior_initial_zero
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_isLocalizingSequence_commonPosteriorExit

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_Attenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma lipschitzWith_tanh_response : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_tanh_response x).differentiableAt
  · intro x
    have h : |deriv Real.tanh x| ≤ 1 := by
      rw [(hasDerivAt_tanh_response x).deriv,
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt (Real.tanh_sq_lt_one x)))]
      nlinarith [sq_nonneg (Real.tanh x)]
    exact_mod_cast h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_DiscrepancyEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Problem367.DiscrepancyEnergy

theorem integral_timePrimitive
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {E : ℝ → Ω → ℝ} {T t : ℝ} (ht : t ∈ Icc 0 T)
    (hE : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    (∫ ω, (∫ s in (0 : ℝ)..t, E s ω) ∂μ) =
      ∫ s in (0 : ℝ)..t, ∫ ω, E s ω ∂μ := by
  have hEt : Integrable (fun p : ℝ × Ω => E p.1 p.2)
      ((volume.restrict (Ioc 0 t)).prod μ) :=
    hE.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)) le_rfl)
  simp only [intervalIntegral.integral_of_le ht.1]
  exact (integral_integral_swap (f := E) hEt).symm

end Problem367.DiscrepancyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_DiscrepancyRowEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Problem367.DiscrepancyEnergy

theorem summable_sq_sub {ι : Type*} {c c' : ι → ℝ}
    (hc : Summable (fun i => (c i) ^ 2))
    (hc' : Summable (fun i => (c' i) ^ 2)) :
    Summable (fun i => (c i - c' i) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ ((hc.add hc').mul_left 2)
  intro i
  nlinarith [sq_nonneg (c i + c' i)]

theorem tsum_sq_sub_le {ι : Type*} {c c' : ι → ℝ}
    (hc : Summable (fun i => (c i) ^ 2))
    (hc' : Summable (fun i => (c' i) ^ 2)) :
    (∑' i, (c i - c' i) ^ 2) ≤ 2 * ((∑' i, (c i) ^ 2) + ∑' i, (c' i) ^ 2) := by
  calc
    (∑' i, (c i - c' i) ^ 2) ≤ ∑' i, 2 * ((c i) ^ 2 + (c' i) ^ 2) := by
      exact Summable.tsum_le_tsum (fun i => by nlinarith [sq_nonneg (c i + c' i)])
        (summable_sq_sub hc hc') ((hc.add hc').mul_left 2)
    _ = _ := by rw [tsum_mul_left, hc.tsum_add hc']

theorem integrable_sq_difference_row
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {c c' : ι → Ω → ℝ}
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hc' : ∀ i, AEStronglyMeasurable (c' i) μ)
    (hA : Integrable (fun ω => ∑' i, (c i ω) ^ 2) μ)
    (hA' : Integrable (fun ω => ∑' i, (c' i ω) ^ 2) μ)
    (hsum : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2) ∧
      Summable (fun i => (c' i ω) ^ 2)) :
    Integrable (fun ω => ∑' i, (c i ω - c' i ω) ^ 2) μ := by
  apply ((hA.add hA').const_mul 2).mono'
    (AEStronglyMeasurable.tsum (fun i => ((hc i).sub (hc' i)).pow 2))
  filter_upwards [hsum] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => sq_nonneg _))]
  exact tsum_sq_sub_le hω.1 hω.2

end Problem367.DiscrepancyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_DriftSquareEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Problem367.DiscrepancyEnergy

theorem primitive_sq_eq_two_integral
    {b : ℝ → ℝ} {a t : ℝ} (hb : IntervalIntegrable b volume a t) :
    (∫ s in a..t, b s) ^ 2 =
      2 * ∫ s in a..t, (∫ u in a..s, b u) * b s := by
  let A : ℝ → ℝ := fun s => ∫ u in a..s, b u
  have hA : AbsolutelyContinuousOnInterval A a t :=
    hb.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have h := hA.integral_deriv_mul_eq_sub hA
  have heq : (∫ s in a..t, deriv A s * A s + A s * deriv A s) =
      ∫ s in a..t, 2 * (A s * b s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hb.ae_hasDerivAt_integral] with s hs hst
    have hd : deriv A s = b s :=
      (hs (uIoc_subset_uIcc hst) a (by simp)).deriv
    rw [hd]
    ring
  rw [heq, intervalIntegral.integral_const_mul] at h
  simpa only [A, intervalIntegral.integral_same, mul_zero, sub_zero, pow_two] using h.symm

theorem ae_timePrimitive_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {b : ℝ → Ω → ℝ} {T t : ℝ} (ht : t ∈ Icc 0 T)
    (hb : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    ∀ᵐ ω ∂μ, (∫ s in (0 : ℝ)..t, b s ω) ^ 2 =
      2 * ∫ s in (0 : ℝ)..t, (∫ u in (0 : ℝ)..s, b u ω) * b s ω := by
  have hbt : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 t)).prod μ) :=
    hb.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)) le_rfl)
  filter_upwards [hbt.prod_left_ae] with ω hω
  exact primitive_sq_eq_two_integral
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr hω)

theorem integral_timePrimitive_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {b : ℝ → Ω → ℝ} {T t : ℝ} (ht : t ∈ Icc 0 T)
    (hb : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hAb : Integrable (fun p : ℝ × Ω =>
      (∫ u in (0 : ℝ)..p.1, b u p.2) * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    (∫ ω, (∫ s in (0 : ℝ)..t, b s ω) ^ 2 ∂μ) =
      2 * ∫ s in (0 : ℝ)..t, ∫ ω, (∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ := by
  rw [integral_congr_ae (ae_timePrimitive_sq ht hb), integral_const_mul]
  congr 1
  exact integral_timePrimitive ht hAb

theorem integrable_timePrimitive_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {b : ℝ → Ω → ℝ} {T t : ℝ} (ht : t ∈ Icc 0 T)
    (hb : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hAb : Integrable (fun p : ℝ × Ω =>
      (∫ u in (0 : ℝ)..p.1, b u p.2) * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    Integrable (fun ω => (∫ s in (0 : ℝ)..t, b s ω) ^ 2) μ := by
  have hAbt : Integrable (fun p : ℝ × Ω =>
      (∫ u in (0 : ℝ)..p.1, b u p.2) * b p.1 p.2)
      ((volume.restrict (Ioc 0 t)).prod μ) :=
    hAb.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right ht.2)) le_rfl)
  have hI : Integrable (fun ω => ∫ s in (0 : ℝ)..t,
      (∫ u in (0 : ℝ)..s, b u ω) * b s ω) μ := by
    simpa only [intervalIntegral.integral_of_le ht.1] using hAbt.integral_prod_right
  exact (hI.const_mul 2).congr ((ae_timePrimitive_sq ht hb).mono (fun ω hω => hω.symm))

end Problem367.DiscrepancyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NNRealArtanhFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.NNRealArtanhFormula

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

lemma martingale_realExtension {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) :
    Martingale (fun t : ℝ => M t.toNNReal) (realFiltration F) μ :=
  ⟨fun _ => hM.stronglyMeasurable _, fun _ _ h => hM.condExp_ae_eq (Real.toNNReal_mono h)⟩

lemma toNNReal_mem_Icc {T : ℝ≥0} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    t.toNNReal ∈ Set.Icc (0 : ℝ≥0) T := by
  constructor
  · exact bot_le
  · simpa only [Real.toNNReal_coe] using Real.toNNReal_mono ht.2

end Problem367.NNRealArtanhFormula

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressivePrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem continuous_nnreal_primitive_of_integrable_horizons
    (f : ℝ → ℝ) (hf : ∀ n : ℕ, IntervalIntegrable f volume 0 (n : ℝ)) :
    Continuous (fun t : ℝ≥0 => ∫ u in (0 : ℝ)..(t : ℝ), f u) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  have hcont : Continuous (fun s : ℝ≥0 => ∫ u in (0 : ℝ)..min (s : ℝ) (n : ℝ), f u) := by
    apply (intervalIntegral.continuousOn_primitive_interval' (hf n)
      (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc 0 (n : ℝ))).comp_continuous
        (NNReal.continuous_coe.min continuous_const)
    intro s
    rw [Set.uIcc_of_le (Nat.cast_nonneg n)]
    exact ⟨le_min s.coe_nonneg (Nat.cast_nonneg n), min_le_right _ _⟩
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [NNReal.continuous_coe.continuousAt.eventually (gt_mem_nhds hn)] with s hs
  simp only [min_eq_left hs.le]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressiveTimePrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.innovationPath_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

theorem isStronglyProgressive_nnrealTimePrimitive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
    {a : ℝ≥0 → Ω → ℝ} (ha : IsStronglyProgressive F a) :
    IsStronglyProgressive F (nnrealTimePrimitive a) := by
  intro T
  have hi : StronglyMeasurable[Subtype.instMeasurableSpace.prod (F T)]
      (fun p : Iic T × Ω => ∫ r : ℝ,
        if 0 < r ∧ r ≤ ((p.1 : ℝ≥0) : ℝ) then a (min r.toNNReal T) p.2 else 0) := by
    have hc := stronglyMeasurable_clipped_nnreal_process ha T
    let : MeasurableSpace Ω := F T
    have hf : StronglyMeasurable (fun q : (Iic T × Ω) × ℝ =>
        a (min q.2.toNNReal T) q.1.2) :=
      hc.comp_measurable (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    have hs : MeasurableSet {q : (Iic T × Ω) × ℝ |
        0 < q.2 ∧ q.2 ≤ ((q.1.1 : ℝ≥0) : ℝ)} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd
          (measurable_subtype_coe.comp (measurable_subtype_coe.comp
            (measurable_fst.comp measurable_fst))))
    have hu : StronglyMeasurable (Function.uncurry (fun p : Iic T × Ω => fun r : ℝ =>
        if 0 < r ∧ r ≤ ((p.1 : ℝ≥0) : ℝ) then a (min r.toNNReal T) p.2 else 0)) := by
      exact hf.piecewise hs stronglyMeasurable_zero
    exact hu.integral_prod_right
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rw [nnrealTimePrimitive, intervalIntegral.integral_of_le (p.1 : ℝ≥0).coe_nonneg,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  by_cases hr : r ∈ Ioc (0 : ℝ) (p.1 : ℝ≥0)
  · have hrt : r.toNNReal ≤ T :=
      (by simpa using Real.toNNReal_mono hr.2 : r.toNNReal ≤ (p.1 : ℝ≥0)).trans p.1.2
    simp only [Set.indicator_of_mem hr, Set.mem_Ioc] at hr ⊢
    rw [ite_eq_left hr, min_eq_left hrt]
  · simp only [Set.indicator_of_notMem hr]
    exact (ite_eq_right hr).symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_DriftEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Problem367.MartingaleDriftEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem condExp_mul_past_eq [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M : I → Ω → ℝ} (hM : Martingale M ℱ μ) {s t : I} (hst : s ≤ t)
    {H : Ω → ℝ} (hH : StronglyMeasurable[ℱ s] H)
    (hprod : Integrable (fun ω => M t ω * H ω) μ) :
    μ[(fun ω => M t ω * H ω) | ℱ s] =ᵐ[μ] fun ω => M s ω * H ω := by
  change μ[M t * H | ℱ s] =ᵐ[μ] fun ω => M s ω * H ω
  have hp : Integrable (M t * H) μ := hprod
  have hCE := condExp_mul_of_stronglyMeasurable_right hH hp (hM.integrable t)
  filter_upwards [hCE, hM.condExp_ae_eq hst] with ω hce hm
  simpa only [Pi.mul_apply, hm] using hce

theorem integrable_mul_past [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M : I → Ω → ℝ} (hM : Martingale M ℱ μ) {s t : I} (hst : s ≤ t)
    {H : Ω → ℝ} (hH : StronglyMeasurable[ℱ s] H)
    (hprod : Integrable (fun ω => M t ω * H ω) μ) :
    Integrable (fun ω => M s ω * H ω) μ :=
  integrable_condExp.congr (condExp_mul_past_eq hM hst hH hprod)

theorem integral_abs_mul_past_le [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M : I → Ω → ℝ} (hM : Martingale M ℱ μ) {s t : I} (hst : s ≤ t)
    {H : Ω → ℝ} (hH : StronglyMeasurable[ℱ s] H)
    (hprod : Integrable (fun ω => M t ω * H ω) μ) :
    (∫ ω, |M s ω * H ω| ∂μ) ≤ ∫ ω, |M t ω * H ω| ∂μ := by
  calc
    (∫ ω, |M s ω * H ω| ∂μ) =
        ∫ ω, |μ[(fun ω => M t ω * H ω) | ℱ s] ω| ∂μ := by
      apply integral_congr_ae
      filter_upwards [condExp_mul_past_eq hM hst hH hprod] with ω hω
      rw [hω]
    _ ≤ ∫ ω, |M t ω * H ω| ∂μ := integral_abs_condExp_le _

theorem integral_mul_past_eq [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M : I → Ω → ℝ} (hM : Martingale M ℱ μ) {s t : I} (hst : s ≤ t)
    {H : Ω → ℝ} (hH : StronglyMeasurable[ℱ s] H)
    (hprod : Integrable (fun ω => M t ω * H ω) μ) :
    (∫ ω, M t ω * H ω ∂μ) = ∫ ω, M s ω * H ω ∂μ := by
  have hp : Integrable (H * M t) μ := by
    change Integrable (fun ω => H ω * M t ω) μ
    simpa only [mul_comm] using hprod
  have hCE := condExp_mul_of_stronglyMeasurable_left hH hp (hM.integrable t)
  calc
    (∫ ω, M t ω * H ω ∂μ) = ∫ ω, μ[H * M t | ℱ s] ω ∂μ := by
      simpa only [Pi.mul_apply, mul_comm] using (integral_condExp (ℱ.le s) (f := H * M t)).symm
    _ = ∫ ω, M s ω * H ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [hCE, hM.condExp_ae_eq hst] with ω hce hm
      simpa only [Pi.mul_apply, hm, mul_comm] using hce

theorem integral_martingale_mul_timeIntegral [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M b : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hM : Martingale M ℱ μ) (hb : StronglyAdapted ℱ b)
    (hcross : Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    (∫ ω, M T ω * (∫ s in (0 : ℝ)..T, b s ω) ∂μ) =
      ∫ s in (0 : ℝ)..T, ∫ ω, M s ω * b s ω ∂μ := by
  calc
    (∫ ω, M T ω * (∫ s in (0 : ℝ)..T, b s ω) ∂μ) =
        ∫ ω, (∫ s in (0 : ℝ)..T, M T ω * b s ω) ∂μ := by
      simp only [intervalIntegral.integral_const_mul]
    _ = ∫ s in (0 : ℝ)..T, ∫ ω, M T ω * b s ω ∂μ :=
      DiscrepancyEnergy.integral_timePrimitive ⟨hT, le_rfl⟩ hcross
    _ = ∫ s in (0 : ℝ)..T, ∫ ω, M s ω * b s ω ∂μ := by
      apply intervalIntegral.integral_congr_ae
      have hint : ∀ᵐ s : ℝ, s ∈ Ioc 0 T →
          Integrable (fun ω => M T ω * b s ω) μ :=
        (ae_restrict_iff' measurableSet_Ioc).1 hcross.prod_right_ae
      filter_upwards [hint] with s hs hmem
      have hst : s ∈ Ioc 0 T := by simpa only [uIoc_of_le hT] using hmem
      exact integral_mul_past_eq hM hst.2 (hb s) (hs hst)

theorem integrable_martingale_mul_timeIntegral [SFinite μ]
    {M b : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hcross : Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    Integrable (fun ω => M T ω * (∫ s in (0 : ℝ)..T, b s ω)) μ := by
  have h := hcross.integral_prod_right
  simpa only [← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_const_mul] using h

theorem integrable_diagonal_mul_of_terminal [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M b : ℝ → Ω → ℝ} {T : ℝ}
    (hM : Martingale M ℱ μ) (hb : StronglyAdapted ℱ b)
    (hmeas : AEStronglyMeasurable (fun p : ℝ × Ω => M p.1 p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hcross : Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    Integrable (fun p : ℝ × Ω => M p.1 p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ) := by
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [hcross.prod_right_ae, ae_restrict_mem measurableSet_Ioc] with s hs hmem
    exact integrable_mul_past hM hmem.2 (hb s) hs
  · apply hcross.integral_norm_prod_left.mono' hmeas.norm.integral_prod_right'
    filter_upwards [hcross.prod_right_ae, ae_restrict_mem measurableSet_Ioc] with s hs hmem
    simpa only [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] using
      integral_abs_mul_past_le hM hmem.2 (hb s) hs

theorem integral_sq_martingale_add_timeIntegral [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M b : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hM : Martingale M ℱ μ) (hb : StronglyAdapted ℱ b)
    (hM2 : Integrable (fun ω => (M T ω) ^ 2) μ)
    (hbInt : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hcross : Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hmeas : AEStronglyMeasurable (fun p : ℝ × Ω => M p.1 p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hAb : Integrable (fun p : ℝ × Ω =>
      (∫ u in (0 : ℝ)..p.1, b u p.2) * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ)) :
    Integrable (fun ω => (M T ω + ∫ s in (0 : ℝ)..T, b s ω) ^ 2) μ ∧
    (∫ ω, (M T ω + ∫ s in (0 : ℝ)..T, b s ω) ^ 2 ∂μ) =
      (∫ ω, (M T ω) ^ 2 ∂μ) +
        2 * ∫ s in (0 : ℝ)..T,
          ∫ ω, (M s ω + ∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ := by
  have hA2 := DiscrepancyEnergy.integrable_timePrimitive_sq ⟨hT, le_rfl⟩ hbInt hAb
  have hMA := integrable_martingale_mul_timeIntegral hT hcross
  have hdiag := integrable_diagonal_mul_of_terminal hM hb hmeas hcross
  have hpoly : (fun ω => (M T ω + ∫ s in (0 : ℝ)..T, b s ω) ^ 2) =
      (fun ω => (M T ω) ^ 2 + 2 * (M T ω * (∫ s in (0 : ℝ)..T, b s ω)) +
        (∫ s in (0 : ℝ)..T, b s ω) ^ 2) := by
    funext ω
    ring
  have hsum : (∫ s in (0 : ℝ)..T,
      ∫ ω, (M s ω + ∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ) =
      (∫ s in (0 : ℝ)..T, ∫ ω, M s ω * b s ω ∂μ) +
      (∫ s in (0 : ℝ)..T,
        ∫ ω, (∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ) := by
    simp only [intervalIntegral.integral_of_le hT]
    calc
      (∫ s in Ioc 0 T, ∫ ω,
          (M s ω + ∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ) =
          ∫ s in Ioc 0 T, (∫ ω, M s ω * b s ω ∂μ) +
            ∫ ω, (∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hdiag.prod_right_ae, hAb.prod_right_ae] with s hs hAs
        simp only [add_mul]
        exact integral_add hs hAs
      _ = _ := integral_add hdiag.integral_prod_left hAb.integral_prod_left
  constructor
  · rw [hpoly]
    exact (hM2.add (hMA.const_mul 2)).add hA2
  · have hfirst : Integrable (fun ω => (M T ω) ^ 2 +
        2 * (M T ω * (∫ s in (0 : ℝ)..T, b s ω))) μ :=
      hM2.add (hMA.const_mul 2)
    rw [hpoly, integral_add hfirst hA2,
      integral_add hM2 (hMA.const_mul 2), integral_const_mul,
      integral_martingale_mul_timeIntegral hT hM hb hcross,
      DiscrepancyEnergy.integral_timePrimitive_sq ⟨hT, le_rfl⟩ hbInt hAb, hsum]
    ring

end Problem367.MartingaleDriftEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_BoundedMartingaleDriftEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Problem367.MartingaleDriftEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem stronglyMeasurable_timePrimitive {b : ℝ → Ω → ℝ}
    (hb : StronglyMeasurable (fun p : ℝ × Ω => b p.1 p.2)) :
    StronglyMeasurable (fun p : ℝ × Ω => ∫ s in (0 : ℝ)..p.1, b s p.2) := by
  have hf : StronglyMeasurable (fun p : (ℝ × Ω) × ℝ => b p.2 p.1.2) :=
    hb.comp_measurable (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hpos : MeasurableSet {p : (ℝ × Ω) × ℝ | 0 < p.2 ∧ p.2 ≤ p.1.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
  have hneg : MeasurableSet {p : (ℝ × Ω) × ℝ | p.1.1 < p.2 ∧ p.2 ≤ 0} :=
    (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hp := (hf.indicator hpos).integral_prod_right' (ν := volume)
  have hn := (hf.indicator hneg).integral_prod_right' (ν := volume)
  convert hp.sub hn using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  simp only [intervalIntegral]
  congr 1 <;> symm
  · simpa only [Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioc] using
      (integral_indicator (μ := volume) (f := fun s => b s p.2)
        (s := Ioc 0 p.1) measurableSet_Ioc)
  · simpa only [Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioc] using
      (integral_indicator (μ := volume) (f := fun s => b s p.2)
        (s := Ioc p.1 0) measurableSet_Ioc)

theorem ae_norm_martingale_le_of_bounded_process
    {M b : ℝ → Ω → ℝ} {T C D : ℝ} (hT : 0 ≤ T)
    (hX : ∀ᵐ ω ∂μ, |M T ω + ∫ s in (0 : ℝ)..T, b s ω| ≤ C)
    (hA : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |∫ s in (0 : ℝ)..t, b s ω| ≤ D) :
    ∀ᵐ ω ∂μ, ‖M T ω‖ ≤ C + D := by
  filter_upwards [hX, hA] with ω hω hAω
  have hAT := hAω T ⟨hT, le_rfl⟩
  rw [Real.norm_eq_abs]
  calc
    |M T ω| = |(M T ω + ∫ s in (0 : ℝ)..T, b s ω) -
        (∫ s in (0 : ℝ)..T, b s ω)| := by ring_nf
    _ ≤ |M T ω + ∫ s in (0 : ℝ)..T, b s ω| +
        |∫ s in (0 : ℝ)..T, b s ω| := abs_sub _ _
    _ ≤ C + D := add_le_add hω hAT

theorem mixed_integrability_of_bounded_process [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M b : ℝ → Ω → ℝ} {T C D : ℝ} (hT : 0 ≤ T)
    (hM : Martingale M ℱ μ)
    (hbMeas : StronglyMeasurable (fun p : ℝ × Ω => b p.1 p.2))
    (hbInt : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hX : ∀ᵐ ω ∂μ, |M T ω + ∫ s in (0 : ℝ)..T, b s ω| ≤ C)
    (hA : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |∫ s in (0 : ℝ)..t, b s ω| ≤ D) :
    Integrable (fun p : ℝ × Ω => M T p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ) ∧
    Integrable (fun p : ℝ × Ω =>
      (∫ s in (0 : ℝ)..p.1, b s p.2) * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ) := by
  have hMt : StronglyMeasurable (M T) := (hM.stronglyAdapted T).mono (ℱ.le T)
  have hMb := ae_norm_martingale_le_of_bounded_process hT hX hA
  constructor
  · exact hbInt.bdd_mul hMt.comp_snd.aestronglyMeasurable
      (Measure.quasiMeasurePreserving_snd.ae hMb)
  · apply hbInt.bdd_mul (stronglyMeasurable_timePrimitive hbMeas).aestronglyMeasurable
    have hAp : ∀ᵐ p ∂((volume.restrict (Ioc 0 T)).prod μ),
        ∀ t ∈ Icc 0 T, |∫ s in (0 : ℝ)..t, b s p.2| ≤ D :=
      Measure.quasiMeasurePreserving_snd.ae hA
    have hmem : ∀ᵐ p ∂((volume.restrict (Ioc 0 T)).prod μ), p.1 ∈ Ioc 0 T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hAp, hmem] with p hp hpt
    simpa only [Real.norm_eq_abs] using hp p.1 ⟨hpt.1.le, hpt.2⟩

theorem integral_sq_of_bounded_process [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} {M b : ℝ → Ω → ℝ} {T C D : ℝ} (hT : 0 ≤ T)
    (hM : Martingale M ℱ μ) (hb : StronglyAdapted ℱ b)
    (hbMeas : StronglyMeasurable (fun p : ℝ × Ω => b p.1 p.2))
    (hbInt : Integrable (fun p : ℝ × Ω => b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hmeas : AEStronglyMeasurable (fun p : ℝ × Ω => M p.1 p.2 * b p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hX : ∀ᵐ ω ∂μ, |M T ω + ∫ s in (0 : ℝ)..T, b s ω| ≤ C)
    (hA : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |∫ s in (0 : ℝ)..t, b s ω| ≤ D) :
    Integrable (fun ω => (M T ω + ∫ s in (0 : ℝ)..T, b s ω) ^ 2) μ ∧
    (∫ ω, (M T ω + ∫ s in (0 : ℝ)..T, b s ω) ^ 2 ∂μ) =
      (∫ ω, (M T ω) ^ 2 ∂μ) +
        2 * ∫ s in (0 : ℝ)..T,
          ∫ ω, (M s ω + ∫ u in (0 : ℝ)..s, b u ω) * b s ω ∂μ := by
  obtain ⟨hcross, hAb⟩ := mixed_integrability_of_bounded_process hT hM hbMeas hbInt hX hA
  have hM2 : Integrable (fun ω => (M T ω) ^ 2) μ := by
    apply Integrable.of_bound
      (((hM.stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable.pow 2) ((C + D) ^ 2)
    filter_upwards [ae_norm_martingale_le_of_bounded_process hT hX hA] with ω hω
    change ‖(M T ω) ^ 2‖ ≤ (C + D) ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      (M T ω) ^ 2 = |M T ω| ^ 2 := (sq_abs _).symm
      _ ≤ (C + D) ^ 2 := pow_le_pow_left₀ (abs_nonneg _)
        (by simpa only [Real.norm_eq_abs] using hω) 2
  exact integral_sq_martingale_add_timeIntegral hT hM hb hM2 hbInt hcross hmeas hAb

end Problem367.MartingaleDriftEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_NNRealBoundedDriftEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace Problem367.NNRealBoundedDriftEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] {F : Filtration ℝ≥0 mΩ}

theorem stronglyMeasurable_realExtension {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStronglyProgressive F X) :
    StronglyMeasurable (fun p : ℝ × Ω => X p.1.toNNReal p.2) :=
  (stronglyMeasurable_joint_of_isStronglyProgressive hX).comp_measurable
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

theorem integral_sq_of_bounded_process
    {M b : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {C D : ℝ}
    (hM : Martingale M F μ)
    (hprogM : IsStronglyProgressive F M) (hprogb : IsStronglyProgressive F b)
    (hbInt : Integrable (fun p : ℝ × Ω => b p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ))
    (hX : ∀ᵐ ω ∂μ, |M T ω + nnrealTimePrimitive b T ω| ≤ C)
    (hA : ∀ᵐ ω ∂μ, ∀ t ≤ T, |nnrealTimePrimitive b t ω| ≤ D) :
    Integrable (fun ω => (M T ω + nnrealTimePrimitive b T ω) ^ 2) μ ∧
      (∫ ω, (M T ω + nnrealTimePrimitive b T ω) ^ 2 ∂μ) =
        (∫ ω, M T ω ^ 2 ∂μ) +
          2 * ∫ s in (0 : ℝ)..(T : ℝ), ∫ ω,
            (M s.toNNReal ω + nnrealTimePrimitive b s.toNNReal ω) *
              b s.toNNReal ω ∂μ := by
  have hF := NNRealArtanhFormula.martingale_realExtension hM
  have hb : StronglyAdapted (NNRealArtanhFormula.realFiltration F)
      (fun t : ℝ => b t.toNNReal) := fun t => hprogb.stronglyAdapted t.toNNReal
  have hA' : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) (T : ℝ),
      |∫ s in (0 : ℝ)..t, b s.toNNReal ω| ≤ D := by
    filter_upwards [hA] with ω hω
    intro t ht
    have h := hω t.toNNReal (NNRealArtanhFormula.toNNReal_mem_Icc ht).2
    simpa only [nnrealTimePrimitive, Real.coe_toNNReal t ht.1] using h
  have h := MartingaleDriftEnergy.integral_sq_of_bounded_process T.coe_nonneg
    hF hb (stronglyMeasurable_realExtension hprogb) hbInt
    ((stronglyMeasurable_realExtension hprogM).mul
      (stronglyMeasurable_realExtension hprogb)).aestronglyMeasurable
    (by simpa only [Real.toNNReal_coe, nnrealTimePrimitive] using hX) hA'
  simp only [Real.toNNReal_coe] at h
  refine ⟨h.1, h.2.trans ?_⟩
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le T.coe_nonneg] at hs
  simp only [nnrealTimePrimitive, Real.coe_toNNReal s hs.1]

theorem integral_sq_of_bounded_process_compensated
    {M b q : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {C D : ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - nnrealTimePrimitive q t ω) F μ)
    (hprogM : IsStronglyProgressive F M) (hprogb : IsStronglyProgressive F b)
    (hbInt : Integrable (fun p : ℝ × Ω => b p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ))
    (hqInt : Integrable (fun p : ℝ × Ω => q p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ))
    (hX : ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω + nnrealTimePrimitive b t ω| ≤ C)
    (hA : ∀ᵐ ω ∂μ, ∀ t ≤ T, |nnrealTimePrimitive b t ω| ≤ D) :
    Integrable (fun ω => (M T ω + nnrealTimePrimitive b T ω) ^ 2) μ ∧
      (∫ ω, (M T ω + nnrealTimePrimitive b T ω) ^ 2 ∂μ) =
        (∫ ω, M 0 ω ^ 2 ∂μ) + ∫ s in (0 : ℝ)..(T : ℝ), ∫ ω,
          q s.toNNReal ω + 2 *
            ((M s.toNNReal ω + nnrealTimePrimitive b s.toNNReal ω) *
              b s.toNNReal ω) ∂μ := by
  obtain ⟨hInt, hsq⟩ := integral_sq_of_bounded_process hM hprogM hprogb hbInt
    (hX.mono (fun ω hω => hω T le_rfl)) hA
  have hqp : Integrable (nnrealTimePrimitive q T) μ := by
    change Integrable (fun ω => ∫ s in (0 : ℝ)..(T : ℝ), q s.toNNReal ω) μ
    simpa only [intervalIntegral.integral_of_le T.coe_nonneg] using
      hqInt.integral_prod_right
  have hM2 : Integrable (fun ω => M T ω ^ 2) μ := by
    have hi := (hQ.integrable T).add hqp
    exact hi.congr (Eventually.of_forall (fun ω => sub_add_cancel _ _))
  have he := hQ.setIntegral_eq (show (0 : ℝ≥0) ≤ T from zero_le) MeasurableSet.univ
  simp only [Measure.restrict_univ] at he
  have hz (ω : Ω) : nnrealTimePrimitive q 0 ω = 0 := by simp [nnrealTimePrimitive]
  simp only [hz, sub_zero] at he
  rw [integral_sub hM2 hqp] at he
  have hqmean : (∫ ω, nnrealTimePrimitive q T ω ∂μ) =
      ∫ s in (0 : ℝ)..(T : ℝ), ∫ ω, q s.toNNReal ω ∂μ :=
    DiscrepancyEnergy.integral_timePrimitive ⟨T.coe_nonneg, le_rfl⟩ hqInt
  have henergy := stronglyMeasurable_realExtension
    (hprogM.add (isStronglyProgressive_nnrealTimePrimitive hprogb))
  have hprod : Integrable (fun p : ℝ × Ω =>
      (M p.1.toNNReal p.2 + nnrealTimePrimitive b p.1.toNNReal p.2) *
        b p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ) := by
    apply hbInt.bdd_mul henergy.aestronglyMeasurable
    have hbound : ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ),
        ∀ t ≤ T, |M t p.2 + nnrealTimePrimitive b t p.2| ≤ C :=
      Measure.quasiMeasurePreserving_snd.ae hX
    have hmem : ∀ᵐ p ∂((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ),
        p.1 ∈ Ioc (0 : ℝ) (T : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hbound, hmem] with p hp hpt
    simpa only [Real.norm_eq_abs] using hp p.1.toNNReal
      (NNRealArtanhFormula.toNNReal_mem_Icc ⟨hpt.1.le, hpt.2⟩).2
  have hadd : (∫ s in (0 : ℝ)..(T : ℝ), ∫ ω,
      q s.toNNReal ω + 2 *
        ((M s.toNNReal ω + nnrealTimePrimitive b s.toNNReal ω) * b s.toNNReal ω) ∂μ) =
      (∫ s in (0 : ℝ)..(T : ℝ), ∫ ω, q s.toNNReal ω ∂μ) +
        2 * ∫ s in (0 : ℝ)..(T : ℝ), ∫ ω,
          (M s.toNNReal ω + nnrealTimePrimitive b s.toNNReal ω) * b s.toNNReal ω ∂μ := by
    simp only [intervalIntegral.integral_of_le T.coe_nonneg]
    calc
      _ = ∫ s in Ioc (0 : ℝ) (T : ℝ),
          (∫ ω, q s.toNNReal ω ∂μ) + 2 * ∫ ω,
            (M s.toNNReal ω + nnrealTimePrimitive b s.toNNReal ω) * b s.toNNReal ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hqInt.prod_right_ae, hprod.prod_right_ae] with s hs hp
        rw [integral_add hs (hp.const_mul 2), integral_const_mul]
      _ = _ := by
        rw [integral_add hqInt.integral_prod_left (hprod.integral_prod_left.const_mul 2),
          integral_const_mul]
  refine ⟨hInt, ?_⟩
  rw [hadd, hsq]
  change (∫ ω, M 0 ω ^ 2 ∂μ) =
    (∫ ω, M T ω ^ 2 ∂μ) - (∫ ω, nnrealTimePrimitive q T ω ∂μ) at he
  rw [hqmean] at he
  linarith

end Problem367.NNRealBoundedDriftEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ProgressiveIsingCovariance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open PlantedSymmetry

local instance progressiveIsingCovarianceNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

lemma continuous_finiteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) (n : ℕ) :
    Continuous (finiteGibbsPairMean beta v w n) := by
  apply (FinitePosterior.continuous_fieldMean _ _ _).comp
  exact continuous_pi (fun u => continuous_apply u.1)

lemma measurable_infiniteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsPairMean beta v w) := by
  have hm : StronglyMeasurable (fun y =>
      limUnder atTop (fun n => finiteGibbsPairMean beta v w n y)) :=
    StronglyMeasurable.limUnder
      (fun n => (continuous_finiteGibbsPairMean beta v w n).measurable.stronglyMeasurable)
  exact measurable_const.max (measurable_const.min hm.measurable)

lemma measurable_infiniteGibbsCovariance {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsCovariance beta v w) :=
  (measurable_infiniteGibbsPairMean beta v w).sub
    ((measurable_infiniteGibbsSpinMean beta v).mul
      (measurable_infiniteGibbsSpinMean beta w))

lemma measurable_infiniteGibbsResponse {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsResponse beta v w) :=
  (measurable_infiniteGibbsCovariance beta v w).div
    (measurable_const.sub ((measurable_infiniteGibbsSpinMean beta v).pow_const 2))

lemma measurable_infiniteGibbsResponseRow {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    Measurable (infiniteGibbsResponseRow beta v) := by
  exact (StronglyMeasurable.tsum (fun w =>
    ((measurable_infiniteGibbsResponse beta v w).pow_const 2).stronglyMeasurable)).measurable

theorem isStronglyProgressive_infiniteGibbsResponseRow
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (beta : ℝ) (v : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i)) :
    IsStronglyProgressive F
      (fun t omega => infiniteGibbsResponseRow beta v (fun i => X i t omega)) := by
  intro t
  let : MeasurableSpace Ω := F t
  exact ((measurable_infiniteGibbsResponseRow beta v).comp
    (Measurable.of_eval (fun vertex => (hX vertex t).measurable))).stronglyMeasurable

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ShiftedFieldVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {G : Ω → ℝ} {beta : ℝ}

lemma continuous_responseAttenuation {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    Continuous (responseAttenuation theta) := by
  have ht := lipschitzWith_tanh_response.continuous
  exact (continuous_const.sub (ht.pow 2)).div
    (continuous_const.sub (continuous_const.mul (ht.pow 2)))
    (fun z => ne_of_gt (attenuation_denominator_pos hθ z))

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ContinuousModification
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367
namespace ContinuousModification

variable {T Ω : Type*}

theorem isStronglyProgressive_sampledLimit [Preorder T] [MeasurableSpace T]
    [mΩ : MeasurableSpace Ω] (ℱ : Filtration T mΩ)
    {q : T → ℕ → T} {F : T → Ω → ℝ}
    (hF : ∀ n, IsStronglyProgressive ℱ (fun t ω => F (q t n) ω)) :
    IsStronglyProgressive ℱ (sampledLimit q F) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  exact StronglyMeasurable.limUnder (fun n => hF n t)

end ContinuousModification
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RoundedStoppingTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.RoundedStoppingTimes

private theorem mesh_pos (n : ℕ) : (0 : ℝ≥0) < n + 1 := by positivity

theorem le_round (n : ℕ) (t : ℝ≥0) : t ≤ round n t := by
  rw [round, le_div_iff₀ (mesh_pos n)]
  exact Nat.le_ceil _

theorem round_le_add (n : ℕ) (t : ℝ≥0) :
    round n t ≤ t + 1 / (n + 1 : ℝ≥0) := by
  rw [round, div_le_iff₀ (mesh_pos n), add_mul,
    div_mul_cancel₀ _ (ne_of_gt (mesh_pos n))]
  exact (Nat.ceil_lt_add_one zero_le).le

theorem round_le_iff (n : ℕ) (s t : ℝ≥0) :
    round n s ≤ t ↔ s ≤ (⌊t * (n + 1 : ℝ≥0)⌋₊ : ℝ≥0) / (n + 1 : ℝ≥0) := by
  rw [round, div_le_iff₀ (mesh_pos n), ← Nat.le_floor_iff zero_le,
    Nat.ceil_le, le_div_iff₀ (mesh_pos n)]

theorem floor_div_le (n : ℕ) (t : ℝ≥0) :
    (⌊t * (n + 1 : ℝ≥0)⌋₊ : ℝ≥0) / (n + 1 : ℝ≥0) ≤ t := by
  rw [div_le_iff₀ (mesh_pos n)]
  exact Nat.floor_le zero_le

theorem tendsto_round (t : ℝ≥0) : Tendsto (fun n => round n t) atTop (𝓝 t) := by
  have hu : Tendsto (fun n : ℕ => t + 1 / (n + 1 : ℝ≥0)) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => le_round n t) (fun n => round_le_add n t)

theorem roundTop_le_iff (n : ℕ) (s : WithTop ℝ≥0) (t : ℝ≥0) :
    roundTop n s ≤ t ↔
      s ≤ (((⌊t * (n + 1 : ℝ≥0)⌋₊ : ℝ≥0) / (n + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) := by
  cases s with
  | top => simp only [roundTop_top, WithTop.top_le_iff, WithTop.coe_ne_top]
  | coe s => simpa only [roundTop_coe, WithTop.coe_le_coe] using round_le_iff n s t

theorem countable_range_roundTop (n : ℕ) : (Set.range (roundTop n)).Countable := by
  refine ((Set.countable_range (fun k : ℕ =>
    ((k : ℝ≥0) / (n + 1 : ℝ≥0) : WithTop ℝ≥0))).insert ⊤).mono ?_
  rintro _ ⟨t, rfl⟩
  cases t with
  | top => exact Set.mem_insert _ _
  | coe t =>
    exact Set.mem_insert_of_mem _ ⟨⌈t * (n + 1 : ℝ≥0)⌉₊, rfl⟩

variable {Ω : Type*} {m : MeasurableSpace Ω} {F : Filtration ℝ≥0 m}

theorem isStoppingTime_roundTop {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (n : ℕ) : IsStoppingTime F (fun ω => roundTop n (τ ω)) := by
  intro t
  simp only [roundTop_le_iff]
  exact F.mono (floor_div_le n t) _ (hτ _)

theorem countable_range_roundTop_comp (τ : Ω → WithTop ℝ≥0) (n : ℕ) :
    (Set.range (fun ω => roundTop n (τ ω))).Countable :=
  (countable_range_roundTop n).mono (Set.range_comp_subset_range _ _)

theorem tendsto_min_roundTop_untopA (t : ℝ≥0) (s : WithTop ℝ≥0) :
    Tendsto (fun n => (min (t : WithTop ℝ≥0) (roundTop n s)).untopA)
      atTop (𝓝 (min (t : WithTop ℝ≥0) s).untopA) := by
  cases s with
  | top => simp
  | coe s =>
    simpa only [roundTop_coe, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe] using
      (tendsto_const_nhds.min (tendsto_round s) :
        Tendsto (fun n => min t (round n s)) atTop (𝓝 (min t s)))

theorem exists_countable_range_approximation {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) :
    ∃ τn : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsStoppingTime F (τn n)) ∧
      (∀ n, (Set.range (τn n)).Countable) ∧
      (∀ (ω : Ω) (t : ℝ≥0), Tendsto (fun n => (min (t : WithTop ℝ≥0) (τn n ω)).untopA)
        atTop (𝓝 (min (t : WithTop ℝ≥0) (τ ω)).untopA)) := by
  exact ⟨fun n ω => roundTop n (τ ω), isStoppingTime_roundTop hτ,
    countable_range_roundTop_comp τ, fun ω t => tendsto_min_roundTop_untopA t (τ ω)⟩

end Problem367.RoundedStoppingTimes

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ContinuousOptionalStopping
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ContinuousOptionalStopping

theorem countable_range_const {Ω α : Type*} (a : α) :
    (range (fun _ : Ω => a)).Countable := by
  apply (countable_singleton a).mono
  rintro x ⟨ω, rfl⟩
  exact mem_singleton a

theorem countable_range_min {Ω α : Type*} [LinearOrder α] {f g : Ω → α}
    (hf : (range f).Countable) (hg : (range g).Countable) :
    (range (fun ω => min (f ω) (g ω))).Countable := by
  apply (hf.union hg).mono
  rintro x ⟨ω, rfl⟩
  rcases le_total (f ω) (g ω) with h | h
  · exact Or.inl ⟨ω, min_eq_left h |>.symm⟩
  · exact Or.inr ⟨ω, min_eq_right h |>.symm⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

theorem integrable_stoppedValue_of_countable
    (hM : Martingale M F μ) (hτ : IsStoppingTime F τ)
    (hcount : (range τ).Countable) {T : ℝ≥0} (hT : ∀ ω, τ ω ≤ T) :
    Integrable (stoppedValue M τ) μ := by
  exact integrable_condExp.congr
    (hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hT hcount).symm

theorem integral_stoppedValue_of_countable
    (hM : Martingale M F μ) (hτ : IsStoppingTime F τ)
    (hcount : (range τ).Countable) {T : ℝ≥0} (hT : ∀ ω, τ ω ≤ T) :
    (∫ ω, stoppedValue M τ ω ∂μ) = ∫ ω, M T ω ∂μ := by
  rw [integral_congr_ae
    (hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hT hcount)]
  exact integral_condExp hτ.measurableSpace_le

theorem martingale_stoppedProcess_of_countable
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hτ : IsStoppingTime F τ) (hcount : (range τ).Countable) :
    Martingale (stoppedProcess M τ) F μ := by
  have had := hprog.stronglyAdapted_stoppedProcess hτ
  have hint (t : ℝ≥0) : Integrable (stoppedProcess M τ t) μ := by
    exact integrable_stoppedValue_of_countable hM ((isStoppingTime_const F t).min hτ)
      (countable_range_min (countable_range_const _) hcount) (fun _ => min_le_left _ _)
  refine ⟨had, ?_⟩
  intro s t hst
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hint t)
    (fun A hA _ => (hint s).integrableOn) ?_ (had s).aestronglyMeasurable).symm
  intro A hA hAfin
  classical
  let ν : Ω → WithTop ℝ≥0 := Aᶜ.piecewise (fun _ => s) (fun _ => t)
  have hν : IsStoppingTime F ν := isStoppingTime_piecewise_const hst hA.compl
  have hνcount : (range ν).Countable := by
    apply (Set.to_countable ({(s : WithTop ℝ≥0), (t : WithTop ℝ≥0)} : Set (WithTop ℝ≥0))).mono
    rintro value ⟨sample, rfl⟩
    change ν sample = (s : WithTop ℝ≥0) ∨ ν sample = (t : WithTop ℝ≥0)
    by_cases hsample : sample ∈ A
    · right
      simp only [ν, Set.piecewise, mem_compl_iff, hsample, not_true_eq_false, ite_false, if_false]
    · left
      simp only [ν, Set.piecewise, mem_compl_iff, hsample, not_false_eq_true, ite_true, if_true]
  have hνle (ω : Ω) : ν ω ≤ t := by
    by_cases hω : ω ∈ A
    · simp only [ν, Set.piecewise, mem_compl_iff, hω, not_true_eq_false, ite_false, if_false]
      exact le_rfl
    · simp only [ν, Set.piecewise, mem_compl_iff, hω, not_false_eq_true, ite_true, if_true]
      exact WithTop.coe_le_coe.mpr hst
  let π : Ω → WithTop ℝ≥0 := fun ω => min (ν ω) (τ ω)
  have hπ := hν.min hτ
  have hπcount := countable_range_min hνcount hcount
  have hmeanπ := integral_stoppedValue_of_countable hM hπ hπcount
    (fun ω => (min_le_left _ _).trans (hνle ω))
  have hmeans := integral_stoppedValue_of_countable hM ((isStoppingTime_const F s).min hτ)
    (countable_range_min (countable_range_const _) hcount)
    (fun ω => (min_le_left _ _).trans (WithTop.coe_le_coe.mpr hst))
  have hpiece : stoppedValue M π =
      A.piecewise (stoppedProcess M τ t) (stoppedProcess M τ s) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [π, ν, Set.piecewise, hω, stoppedValue, stoppedProcess]
  change (∫ ω, stoppedValue M π ω ∂μ) = ∫ ω, M t ω ∂μ at hmeanπ
  have hmean : (∫ ω, stoppedValue M π ω ∂μ) = ∫ ω, stoppedProcess M τ s ω ∂μ :=
    hmeanπ.trans hmeans.symm
  rw [hpiece, integral_piecewise (F.le s A hA) (hint t).integrableOn
    (hint s).integrableOn] at hmean
  have hsplit := integral_add_compl (F.le s A hA) (hint s)
  linarith

theorem martingale_stoppedProcess_of_approximation
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
    (hτ : IsStoppingTime F τ) (τn : ℕ → Ω → WithTop ℝ≥0)
    (hτn : ∀ n, IsStoppingTime F (τn n))
    (hcount : ∀ n, (range (τn n)).Countable)
    (htime : ∀ (ω : Ω) (t : ℝ≥0), Tendsto
      (fun n => (min (t : WithTop ℝ≥0) (τn n ω)).untopA) atTop
      (𝓝 ((min (t : WithTop ℝ≥0) (τ ω)).untopA))) :
    Martingale (stoppedProcess M τ) F μ := by
  have had := hprog.stronglyAdapted_stoppedProcess hτ
  have hMn (n : ℕ) : Martingale (stoppedProcess M (τn n)) F μ :=
    martingale_stoppedProcess_of_countable hM hprog (hτn n) (hcount n)
  have hbound (T : ℝ≥0) (g : Ω → ℝ)
      (hg : ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
      (σ : Ω → WithTop ℝ≥0) :
      ∀ᵐ ω ∂μ, ‖stoppedProcess M σ T ω‖ ≤ g ω := by
    filter_upwards [hg] with ω hω
    exact hω _ (WithTop.untopA_le (min_le_left _ _))
  have hint (t : ℝ≥0) : Integrable (stoppedProcess M τ t) μ := by
    obtain ⟨g, hg, hgb⟩ := hdom t
    exact hg.mono' ((had t).mono (F.le t)).aestronglyMeasurable (hbound t g hgb τ)
  have hlim (t : ℝ≥0) (A : Set Ω) :
      Tendsto (fun n => ∫ ω in A, stoppedProcess M (τn n) t ω ∂μ) atTop
        (𝓝 (∫ ω in A, stoppedProcess M τ t ω ∂μ)) := by
    obtain ⟨g, hg, hgb⟩ := hdom t
    apply tendsto_integral_of_dominated_convergence g
      (fun n => ((hMn n).integrable t).aestronglyMeasurable.restrict) hg.restrict
      (fun n => ae_restrict_of_ae (hbound t g hgb (τn n)))
    filter_upwards [ae_restrict_of_ae hc] with ω hcω
    exact (hcω.tendsto _).comp (htime ω t)
  refine ⟨had, ?_⟩
  intro s t hst
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hint t)
    (fun A hA _ => (hint s).integrableOn) ?_ (had s).aestronglyMeasurable).symm
  intro A hA hAfin
  exact tendsto_nhds_unique (hlim s A)
    (Filter.Tendsto.congr (fun n => ((hMn n).setIntegral_eq hst hA).symm) (hlim t A))

theorem martingale_stoppedProcess_of_continuous_dominated
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
    (hτ : IsStoppingTime F τ) : Martingale (stoppedProcess M τ) F μ := by
  obtain ⟨τn, hτn, hcount, htime⟩ :=
    RoundedStoppingTimes.exists_countable_range_approximation hτ
  exact martingale_stoppedProcess_of_approximation hM hprog hc hdom hτ τn hτn hcount htime

end Problem367.ContinuousOptionalStopping

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_IntegrableTimePrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
  {a : ℝ≥0 → Ω → ℝ}

theorem ae_intervalIntegrable_horizons_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ)) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ,
      IntervalIntegrable (fun r : ℝ => a r.toNNReal ω) volume 0 (n : ℝ) := by
  apply ae_all_iff.mpr
  intro n
  filter_upwards [(ha n).prod_left_ae] with ω hω
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mpr hω

theorem ae_continuous_nnrealTimePrimitive_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ)) :
    ∀ᵐ ω ∂μ, Continuous (fun t => nnrealTimePrimitive a t ω) := by
  filter_upwards [ae_intervalIntegrable_horizons_of_joint ha] with ω hω
  exact continuous_nnreal_primitive_of_integrable_horizons _ hω

omit [MeasurableSpace Ω] in
theorem nnrealTimePrimitive_nonneg {ω : Ω}
    (ha : ∀ t, 0 ≤ a t ω) (t : ℝ≥0) : 0 ≤ nnrealTimePrimitive a t ω :=
  intervalIntegral.integral_nonneg_of_forall t.coe_nonneg (fun r => ha r.toNNReal)

theorem ae_monotone_nnrealTimePrimitive_of_joint
    (ha : ∀ n : ℕ, Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (n : ℝ))).prod μ))
    (hnonneg : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ a t ω) :
    ∀ᵐ ω ∂μ, Monotone (fun t => nnrealTimePrimitive a t ω) := by
  filter_upwards [ae_intervalIntegrable_horizons_of_joint ha, hnonneg] with ω hi hp
  intro s t hst
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
  have hit : IntervalIntegrable (fun r : ℝ => a r.toNNReal ω) volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mp (hi n)).mono_set
        (Ioc_subset_Ioc le_rfl hn))
  exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg hst
    (Filter.Eventually.of_forall (fun r => hp r.toNNReal)) hit

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressiveVersionPushforward
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ProgressiveVersionPushforward
open ContinuousModification

lemma leftTime_le (t : ℝ≥0) (n : ℕ) : leftTime t n ≤ t := by
  simpa only [leftTime, Real.toNNReal_coe] using Real.toNNReal_mono (dyadicLeft_le t n)

lemma measurable_leftTime (n : ℕ) : Measurable (fun t => leftTime t n) := by
  unfold leftTime dyadicLeft
  fun_prop

lemma progressive_version {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : IsStronglyProgressive F M) : IsStronglyProgressive F (version M) := by
  apply isStronglyProgressive_sampledLimit F
  intro n
  apply hM.comp _ (fun t _ => leftTime_le t n)
  intro T
  exact ((measurable_leftTime n).comp measurable_fst.subtype_val).stronglyMeasurable

end Problem367.ProgressiveVersionPushforward

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_PredictableMeshApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PredictableMesh

theorem mem_mesh_Ioc {n : ℕ} {t : ℝ≥0} (ht : 0 < t) :
    t ∈ Ioc (left n t)
      (point n (⌈(n + 1 : ℕ) * t⌉₊ - 1 + 1)) := by
  have hN : (0 : ℝ≥0) < (n + 1 : ℕ) := by positivity
  have hc : 1 ≤ ⌈(n + 1 : ℕ) * t⌉₊ :=
    Nat.one_le_ceil_iff.mpr (mul_pos hN ht)
  have hh := (Nat.ceil_eq_iff (show ⌈(n + 1 : ℕ) * t⌉₊ ≠ 0 by omega)).mp rfl
  constructor
  · apply (div_lt_iff₀ hN).2
    simpa only [mul_comm] using hh.1
  · dsimp [point]
    rw [Nat.sub_add_cancel hc]
    apply (le_div_iff₀ hN).2
    simpa only [mul_comm] using hh.2

theorem left_le (n : ℕ) (t : ℝ≥0) : left n t ≤ t := by
  by_cases ht : t = 0
  · simp [ht]
  · exact (mem_mesh_Ioc (n := n) (pos_iff_ne_zero.mpr ht)).1.le

theorem le_left_add_width (n : ℕ) (t : ℝ≥0) :
    t ≤ left n t + 1 / (n + 1 : ℕ) := by
  by_cases ht : t = 0
  · simp [ht]
  · have h := (mem_mesh_Ioc (n := n) (pos_iff_ne_zero.mpr ht)).2
    simpa only [point, left, Nat.cast_add, Nat.cast_one, add_div] using h

theorem tendsto_left (t : ℝ≥0) : Tendsto (fun n => left n t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => show ‖(left n t : ℝ) - (t : ℝ)‖ ≤ 1 / ((n : ℝ) + 1) from ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : (left n t : ℝ) ≤ (t : ℝ) := left_le n t
  have hu := le_left_add_width n t
  have hu' : (t : ℝ) ≤ (left n t : ℝ) + 1 / ((n : ℝ) + 1) := by
    exact_mod_cast hu
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hl)]
  linarith

end Problem367.PredictableMesh

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_SquareMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Problem367.MartingaleSquareMaximal

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Preorder ι]
  {μ : Measure Ω} {F : Filtration ι mΩ} {M : ι → Ω → ℝ}

theorem submartingale_sq (hM : Martingale M F μ)
    (h2 : ∀ t, MemLp (M t) 2 μ) :
    Submartingale (fun t ω => M t ω ^ 2) F μ := by
  refine ⟨fun t => (hM.stronglyMeasurable t).pow 2, ?_, fun t => (h2 t).integrable_sq⟩
  intro s t hst
  have hint : Integrable (fun ω => ‖M t ω‖ ^ (2 : ℝ)) μ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using (h2 t).integrable_sq
  have hj := Integrable.norm_condExp_rpow_le (m := F s) (by norm_num : (1 : ℝ) ≤ 2) hint
  have hj' : (fun ω => μ[M t | F s] ω ^ 2) ≤ᵐ[μ]
      μ[(fun ω => M t ω ^ 2) | F s] := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hj
  filter_upwards [hj', hM.condExp_ae_eq hst] with ω hω heq
  simpa only [heq] using hω

theorem integral_sq_le [IsFiniteMeasure μ]
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    {s t : ι} (hst : s ≤ t) :
    (∫ ω, M s ω ^ 2 ∂μ) ≤ ∫ ω, M t ω ^ 2 ∂μ := by
  have hs := submartingale_sq hM h2
  calc
    _ ≤ ∫ ω, μ[(fun ω => M t ω ^ 2) | F s] ω ∂μ :=
      integral_mono_ae (h2 s).integrable_sq integrable_condExp (hs.2.1 s t hst)
    _ = _ := integral_condExp (F.le s)

end Problem367.MartingaleSquareMaximal

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StrongMaximal
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Finset
open scoped NNReal ENNReal Topology

namespace Problem367.MartingaleStrongMaximal

theorem self_le_runningMax (x : ℕ → ℝ) (n : ℕ) : x n ≤ runningMax x n := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_right _ _

theorem runningMax_mono (x : ℕ → ℝ) : Monotone (runningMax x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

theorem le_runningMax (x : ℕ → ℝ) {i n : ℕ} (h : i ≤ n) : x i ≤ runningMax x n :=
  (self_le_runningMax x i).trans (runningMax_mono x h)

theorem runningMax_sq_le_twice (x : ℕ → ℝ) (n : ℕ) :
    runningMax x n ^ 2 ≤ 2 * runningMax x n * x n -
      2 * ∑ k ∈ range n, runningMax x k * (x (k + 1) - x k) := by
  induction n with
  | zero =>
    simp only [sum_range_zero, mul_zero, sub_zero, runningMax_zero]
    nlinarith [sq_nonneg (x 0)]
  | succ n ih =>
    rw [sum_range_succ, runningMax_succ]
    rcases le_total (x (n + 1)) (runningMax x n) with h | h
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right h]
      nlinarith [sq_nonneg (x (n + 1) - runningMax x n)]

theorem runningMax_sq_le_four (x : ℕ → ℝ) (n : ℕ) :
    runningMax x n ^ 2 ≤ 4 * x n ^ 2 -
      4 * ∑ k ∈ range n, runningMax x k * (x (k + 1) - x k) := by
  have h := runningMax_sq_le_twice x n
  nlinarith [sq_nonneg (runningMax x n - 2 * x n)]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem runningMax_memLp {X : ℕ → Ω → ℝ} (h2 : ∀ n, MemLp (X n) 2 μ) (n : ℕ) :
    MemLp (fun ω => runningMax (fun k => X k ω) n) 2 μ := by
  induction n with
  | zero => exact h2 0
  | succ n ih => exact ih.sup (h2 (n + 1))

theorem runningMax_stronglyAdapted {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX : StronglyAdapted F X) :
    StronglyAdapted F (fun n ω => runningMax (fun k => X k ω) n) := by
  intro n
  induction n with
  | zero => exact hX 0
  | succ n ih =>
    let : MeasurableSpace Ω := F (n + 1)
    have hi : StronglyMeasurable[F (n + 1)]
        (fun ω => runningMax (fun k => X k ω) n) := ih.mono (F.mono (Nat.le_succ n))
    exact hi.sup (hX (n + 1))

theorem integral_mul_sub_nonneg [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} (hX : Submartingale X F μ)
    (n : ℕ) {H : Ω → ℝ} (hH : StronglyMeasurable[F n] H)
    (hHnonneg : ∀ ω, 0 ≤ H ω)
    (hprod : Integrable (fun ω => H ω * (X (n + 1) ω - X n ω)) μ) :
    0 ≤ ∫ ω, H ω * (X (n + 1) ω - X n ω) ∂μ := by
  have hpull := condExp_mul_of_stronglyMeasurable_left hH hprod
    ((hX.integrable (n + 1)).sub (hX.integrable n))
  rw [← integral_condExp (F.le n)]
  apply integral_nonneg_of_ae
  filter_upwards [hpull, hX.condExp_sub_nonneg (Nat.le_succ n)] with ω hp hn
  change 0 ≤ μ[H * (fun ω => X (n + 1) ω - X n ω) | F n] ω
  rw [hp]
  exact mul_nonneg (hHnonneg ω) hn

theorem finite_submartingale_maximal_sq [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX : Submartingale X F μ) (h2 : ∀ n, MemLp (X n) 2 μ)
    (hnonneg : ∀ n ω, 0 ≤ X n ω) (n : ℕ) :
    (∫ ω, runningMax (fun k => X k ω) n ^ 2 ∂μ) ≤
      4 * ∫ ω, X n ω ^ 2 ∂μ := by
  have hmax2 := runningMax_memLp h2
  have hmaxA := runningMax_stronglyAdapted hX.stronglyAdapted
  have hprod (k : ℕ) : Integrable (fun ω =>
      runningMax (fun j => X j ω) k * (X (k + 1) ω - X k ω)) μ :=
    (hmax2 k).integrable_mul ((h2 (k + 1)).sub (h2 k))
  have hsum : Integrable (fun ω => ∑ k ∈ range n,
      runningMax (fun j => X j ω) k * (X (k + 1) ω - X k ω)) μ :=
    integrable_finsetSum _ (fun k _ => hprod k)
  have hbound := integral_mono (hmax2 n).integrable_sq
    (((h2 n).integrable_sq.const_mul 4).sub (hsum.const_mul 4))
    (fun ω => runningMax_sq_le_four (fun k => X k ω) n)
  simp only [Pi.sub_apply] at hbound
  rw [integral_sub ((h2 n).integrable_sq.const_mul 4) (hsum.const_mul 4),
    integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun k _ => hprod k)] at hbound
  have hsum_nonneg : 0 ≤ ∑ k ∈ range n, ∫ ω,
      runningMax (fun j => X j ω) k * (X (k + 1) ω - X k ω) ∂μ := by
    apply sum_nonneg
    intro k hk
    exact integral_mul_sub_nonneg hX k (hmaxA k)
      (fun ω => (hnonneg k ω).trans (self_le_runningMax (fun j => X j ω) k)) (hprod k)
  linarith

theorem submartingale_abs {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) : Submartingale (fun n ω => |M n ω|) F μ := by
  refine ⟨fun n => ?_, ?_, fun n => (hM.integrable n).abs⟩
  · simpa only [Real.norm_eq_abs] using (hM.stronglyMeasurable n).norm
  · intro i j hij
    have hj := norm_condExp_le (m := F i) (μ := μ) (M j)
    filter_upwards [hj, hM.condExp_ae_eq hij] with ω hω heq
    simpa only [Real.norm_eq_abs, heq] using hω

theorem finite_martingale_maximal_sq [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    (∫ ω, runningMax (fun k => |M k ω|) n ^ 2 ∂μ) ≤
      4 * ∫ ω, M n ω ^ 2 ∂μ := by
  simpa only [sq_abs] using finite_submartingale_maximal_sq (submartingale_abs hM)
    (fun n => (h2 n).norm) (fun n ω => abs_nonneg (M n ω)) n

theorem runningMax_le {x : ℕ → ℝ} {n : ℕ} {a : ℝ}
    (h : ∀ k ≤ n, x k ≤ a) : runningMax x n ≤ a := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ n ih =>
    exact max_le (ih (fun k hk => h k (hk.trans (Nat.le_succ n)))) (h (n + 1) le_rfl)

theorem sampled_martingale_maximal_sq [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (q : ℕ → ι) (hq : Monotone q) (n : ℕ) {T : ι} (hT : q n ≤ T) :
    (∫ ω, runningMax (fun k => |M (q k) ω|) n ^ 2 ∂μ) ≤
      4 * ∫ ω, M T ω ^ 2 ∂μ := by
  let G : Filtration ℕ mΩ := ⟨fun k => F (q k),
    fun _ _ h => F.mono (hq h), fun k => F.le (q k)⟩
  have hMq : Martingale (fun k => M (q k)) G μ :=
    ⟨fun k => hM.stronglyMeasurable (q k), fun i j hij => hM.condExp_ae_eq (hq hij)⟩
  exact (finite_martingale_maximal_sq hMq (fun k => h2 (q k)) n).trans
    (mul_le_mul_of_nonneg_left (MartingaleSquareMaximal.integral_sq_le hM h2 hT)
      (by norm_num))

theorem dyadicPoint_mono (n : ℕ) : Monotone (dyadicPoint n) := by
  intro i j hij
  dsimp [dyadicPoint]
  gcongr

theorem dyadicPoint_double (n k : ℕ) :
    dyadicPoint (n + 1) (2 * k) = dyadicPoint n k := by
  simp only [dyadicPoint, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem dyadicPoint_le_iff {n k : ℕ} {T : ℝ≥0} :
    dyadicPoint n k ≤ T ↔ k ≤ dyadicCount n T := by
  have hp : (0 : ℝ≥0) < (2 ^ n : ℕ) := by positivity
  rw [dyadicPoint, div_le_iff₀ hp, dyadicCount, Nat.le_floor_iff (by positivity)]
  rw [mul_comm]

theorem dyadicPoint_eq_mesh (n k : ℕ) :
    dyadicPoint n k = PredictableMesh.point (2 ^ n - 1) k := by
  have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  simp only [dyadicPoint, PredictableMesh.point, Nat.sub_add_cancel hn]

omit mΩ in
theorem gridMax_nonneg (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    0 ≤ gridMax M T n ω :=
  (abs_nonneg _).trans (self_le_runningMax
    (fun k => |M (dyadicPoint n k) ω|) (dyadicCount n T))

omit mΩ in
theorem gridMax_mono (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    Monotone (fun n => gridMax M T n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  apply runningMax_le
  intro k hk
  have ht : dyadicPoint (n + 1) (2 * k) ≤ T := by
    rw [dyadicPoint_double]
    exact dyadicPoint_le_iff.mpr hk
  have hb := le_runningMax (fun j => |M (dyadicPoint (n + 1) j) ω|)
    (dyadicPoint_le_iff.mp ht)
  simpa only [dyadicPoint_double, gridMax] using hb

theorem gridMax_memLp {M : ℝ≥0 → Ω → ℝ} (h2 : ∀ t, MemLp (M t) 2 μ)
    (T : ℝ≥0) (n : ℕ) : MemLp (gridMax M T n) 2 μ :=
  runningMax_memLp (fun k => (h2 (dyadicPoint n k)).norm) _

theorem gridMax_integral_sq_le [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, gridMax M T n ω ^ 2 ∂μ) ≤ 4 * ∫ ω, M T ω ^ 2 ∂μ :=
  sampled_martingale_maximal_sq hM h2 (dyadicPoint n) (dyadicPoint_mono n) _
    (dyadicPoint_le_iff.mpr le_rfl)

omit mΩ in

theorem supremumSq_eq_iSup_gridMax {M : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => M t ω)) (T : ℝ≥0) :
    supremumSq M T ω = ⨆ n : ℕ, ENNReal.ofReal (gridMax M T n ω ^ 2) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    have hp : Tendsto (fun n : ℕ => 2 ^ n - 1) atTop atTop :=
      (tendsto_sub_atTop_nat 1).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
        (M (PredictableMesh.left (2 ^ n - 1) t) ω ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (M t ω ^ 2))) :=
      ENNReal.tendsto_ofReal (((hc.tendsto t).comp
        ((PredictableMesh.tendsto_left t).comp hp)).pow 2)
    apply le_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro n
    apply le_iSup_of_le n
    apply ENNReal.ofReal_le_ofReal
    rw [← sq_abs (M (PredictableMesh.left (2 ^ n - 1) t) ω)]
    apply (sq_le_sq₀ (abs_nonneg _) (gridMax_nonneg M T n ω)).mpr
    let k := ⌈((2 ^ n - 1 + 1 : ℕ) : ℝ≥0) * t⌉₊ - 1
    have heq : dyadicPoint n k = PredictableMesh.left (2 ^ n - 1) t :=
      dyadicPoint_eq_mesh n k
    have ht : dyadicPoint n k ≤ T := by
      rw [heq]
      exact (PredictableMesh.left_le _ t).trans t.property
    have hb := le_runningMax (fun j => |M (dyadicPoint n j) ω|)
      (dyadicPoint_le_iff.mp ht)
    simpa only [heq, gridMax] using hb
  · apply iSup_le
    intro n
    have hmax : ∃ k ≤ dyadicCount n T,
        gridMax M T n ω = |M (dyadicPoint n k) ω| := by
      dsimp only [gridMax]
      generalize dyadicCount n T = N
      induction N with
      | zero => exact ⟨0, le_rfl, rfl⟩
      | succ N ih =>
        obtain ⟨k, hk, heq⟩ := ih
        rcases le_total |M (dyadicPoint n (N + 1)) ω|
          (runningMax (fun k => |M (dyadicPoint n k) ω|) N) with h | h
        · exact ⟨k, hk.trans (Nat.le_succ N), (max_eq_left h).trans heq⟩
        · exact ⟨N + 1, le_rfl, max_eq_right h⟩
    obtain ⟨k, hk, heq⟩ := hmax
    rw [heq, sq_abs]
    exact le_iSup_of_le ⟨dyadicPoint n k, dyadicPoint_le_iff.mpr hk⟩ le_rfl

theorem continuous_martingale_maximal_sq [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    (∫⁻ ω, supremumSq M T ω ∂μ) ≤
      ENNReal.ofReal (4 * ∫ ω, M T ω ^ 2 ∂μ) := by
  have heq : supremumSq M T =ᵐ[μ]
      (fun ω => ⨆ n : ℕ, ENNReal.ofReal (gridMax M T n ω ^ 2)) := by
    filter_upwards [hc] with ω hω
    exact supremumSq_eq_iSup_gridMax hω T
  rw [lintegral_congr_ae heq, lintegral_iSup']
  · apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (gridMax_memLp h2 T n).integrable_sq
      (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (gridMax_integral_sq_le hM h2 T n)
  · intro n
    exact ((gridMax_memLp h2 T n).aestronglyMeasurable.pow 2).aemeasurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun ω n m hnm =>
      ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (gridMax_nonneg M T n ω)
        (gridMax_nonneg M T m ω)).mpr (gridMax_mono M T ω hnm))

theorem supremumSq_aemeasurable {M : ℝ≥0 → Ω → ℝ}
    (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    AEMeasurable (supremumSq M T) μ := by
  have hg : AEMeasurable
      (fun ω => ⨆ n : ℕ, ENNReal.ofReal (gridMax M T n ω ^ 2)) μ :=
    AEMeasurable.iSup (fun n =>
      ((gridMax_memLp h2 T n).aestronglyMeasurable.pow 2).aemeasurable.ennreal_ofReal)
  apply hg.congr
  filter_upwards [hc] with ω hω
  exact (supremumSq_eq_iSup_gridMax hω T).symm

theorem ae_supremumSq_lt_top [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, supremumSq M T ω < ∞ :=
  ae_lt_top' (supremumSq_aemeasurable h2 hc T)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (continuous_martingale_maximal_sq hM h2 hc T))

theorem integrable_maximalSquare [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    Integrable (maximalSquare M T) μ :=
  integrable_toReal_of_lintegral_ne_top (supremumSq_aemeasurable h2 hc T)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (continuous_martingale_maximal_sq hM h2 hc T))

theorem ae_all_sq_le_maximalSquare [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, M t ω ^ 2 ≤ maximalSquare M T ω := by
  filter_upwards [ae_supremumSq_lt_top hM h2 hc T] with ω hω
  intro t ht
  have hle : ENNReal.ofReal (M t ω ^ 2) ≤ supremumSq M T ω :=
    le_iSup_of_le ⟨t, ht⟩ le_rfl
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), maximalSquare] using
    ENNReal.toReal_mono hω.ne hle

end Problem367.MartingaleStrongMaximal

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_RightContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367

theorem martingale_rightCont_of_L1_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X F P)
    (hcont : ∀ s, Tendsto (fun t => eLpNorm (X t - X s) 1 P)
      (𝓝[>] s) (𝓝 0)) :
    Martingale X F.rightCont P := by
  have had : StronglyAdapted F.rightCont X :=
    fun s => (hX.stronglyAdapted s).mono (F.le_rightCont s)
  refine ⟨had, ?_⟩
  intro s t hst
  rcases hst.eq_or_lt with rfl | hst
  · exact (condExp_of_stronglyMeasurable (F.rightCont.le s) (had s)
      (hX.integrable s)).eventuallyEq
  · apply (ae_eq_condExp_of_forall_setIntegral_eq (F.rightCont.le s)
      (hX.integrable t) (fun A hA _ => (hX.integrable s).integrableOn) ?_
      (had s).aestronglyMeasurable).symm
    intro A hA hAfin
    have hlim := tendsto_setIntegral_of_L1' (X s) (hX.integrable s).aestronglyMeasurable
      (Eventually.of_forall hX.integrable) (hcont s) A
    have heq : ∀ᶠ u in 𝓝[>] s, (∫ ω in A, X u ω ∂P) = ∫ ω in A, X t ω ∂P := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hst).filter_mono nhdsWithin_le_nhds]
        with u hsu hut
      have hFu : F.rightCont s ≤ F u := by
        rw [F.rightCont_eq]
        exact iInf₂_le u hsu
      exact hX.setIntegral_eq hut.le (hFu A hA)
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (heq.mono (fun _ h => h.symm)))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_DominatedMartingaleRightContinuation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ENNReal

namespace Problem367.DominatedMartingaleRightContinuation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

omit [IsFiniteMeasure μ] in
theorem tendsto_L1_of_ae_continuous_dominated
    (hint : ∀ t, Integrable (M t) μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω) (s : ℝ≥0) :
    Tendsto (fun t => eLpNorm (M t - M s) 1 μ) (𝓝 s) (𝓝 0) := by
  obtain ⟨g, hg, hgb⟩ := hdom (s + 1)
  have hcont : ContinuousAt (fun t => ∫ ω, ‖M t ω - M s ω‖ ∂μ) s := by
    apply continuousAt_of_dominated
      (Eventually.of_forall (fun t => ((hint t).sub (hint s)).aestronglyMeasurable.norm))
      (bound := fun ω => 2 * g ω)
    · filter_upwards [eventually_lt_nhds (lt_add_one s)] with t ht
      filter_upwards [hgb] with ω hω
      have hst : s ≤ s + 1 := le_add_of_nonneg_right zero_le
      have hb := (norm_sub_le (M t ω) (M s ω)).trans
        (add_le_add (hω t ht.le) (hω s hst))
      simpa only [Pi.sub_apply, norm_norm, two_mul] using hb
    · exact hg.const_mul 2
    · filter_upwards [hc] with ω hω
      exact (hω.sub continuous_const).norm.continuousAt
  have heq (t : ℝ≥0) : eLpNorm (M t - M s) 1 μ =
      ENNReal.ofReal (∫ ω, ‖M t ω - M s ω‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hint t).sub (hint s))]
    rfl
  simp_rw [heq]
  simpa only [Function.comp_def, sub_self, norm_zero, integral_zero, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.continuousAt.comp hcont).tendsto

theorem martingale_rightCont_of_ae_continuous_dominated
    (hM : Martingale M F μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω) :
    Martingale M F.rightCont μ := by
  apply Problem367.martingale_rightCont_of_L1_rightContinuous hM
  intro s
  exact (tendsto_L1_of_ae_continuous_dominated hM.integrable hc hdom s).mono_left
    nhdsWithin_le_nhds

theorem isStronglyProgressive_mono_filtration
    {G : Filtration ℝ≥0 mΩ} (hFG : F ≤ G) (hM : IsStronglyProgressive F M) :
    IsStronglyProgressive G M := by
  intro t
  exact (hM t).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (hFG t)))

theorem martingale_stoppedProcess_rightCont
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (stoppedProcess M τ) F.rightCont μ :=
  ContinuousOptionalStopping.martingale_stoppedProcess_of_continuous_dominated
    (martingale_rightCont_of_ae_continuous_dominated hM hc hdom)
    (isStronglyProgressive_mono_filtration F.le_rightCont hprog) hc hdom hτ

end Problem367.DominatedMartingaleRightContinuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedTimePrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace Problem367.StoppedTimePrimitive

theorem integral_indicator_min (a : ℝ → ℝ) (t u : ℝ≥0) :
    (∫ r in (0 : ℝ)..(t : ℝ), if r ≤ u then a r else 0) =
      ∫ r in (0 : ℝ)..(min t u : ℝ≥0), a r := by
  rcases le_total t u with h | h
  · rw [min_eq_left h]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le t.coe_nonneg] at hr
    exact ite_eq_left (hr.2.trans h)
  · rw [min_eq_right h]
    exact intervalIntegral.integral_indicator ⟨u.coe_nonneg, h⟩

theorem stoppedProcess_primitive {Ω : Type*} (a : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess (nnrealTimePrimitive a) τ t ω =
      nnrealTimePrimitive (stopDensity a τ) t ω := by
  cases hτ : τ ω with
  | top => simp only [stoppedProcess, nnrealTimePrimitive, stopDensity, hτ, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe, le_top, ite_true, if_true]
  | coe u =>
    simp only [stoppedProcess, hτ, ← WithTop.coe_min, WithTop.untopA,
      WithTop.untopD_coe, nnrealTimePrimitive, stopDensity, WithTop.coe_le_coe,
      Real.toNNReal_le_iff_le_coe]
    exact (integral_indicator_min (fun r => a r.toNNReal ω) t u).symm

theorem stopTime_eq_iff_le {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    (min (t : WithTop ℝ≥0) (τ ω)).untopA = t ↔ (t : WithTop ℝ≥0) ≤ τ ω := by
  cases hτ : τ ω with
  | top => simp only [min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe, le_top]
  | coe u => simp only [← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, min_eq_left_iff, WithTop.coe_le_coe]

theorem isStronglyProgressive_stopDensity {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {a : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (ha : IsStronglyProgressive F a) (hτ : IsStoppingTime F τ) :
    IsStronglyProgressive F (stopDensity a τ) := by
  intro T
  let : MeasurableSpace Ω := F T
  have hs : MeasurableSet {p : Iic T × Ω | ((p.1 : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2} := by
    simp only [← stopTime_eq_iff_le]
    exact measurableSet_eq_fun (isStronglyProgressive_min_stopping_time hτ T).measurable
      measurable_fst.subtype_val
  exact (ha T).piecewise hs stronglyMeasurable_const

end Problem367.StoppedTimePrimitive

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_StoppingTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PosteriorStoppingTimes

theorem exists_earlier_nnrat {f : ℝ≥0 → ℝ} {t : ℝ≥0} {r : ℝ}
    (hc : ContinuousAt f t) (ht : 0 < t) (hr : r < f t) :
    ∃ q : ℚ≥0, (q : ℝ≥0) < t ∧ r < f (q : ℝ≥0) := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hc (f t - r) (sub_pos.mpr hr)
  have htR : (0 : ℝ) < t := ht
  have hlo : max (0 : ℝ) ((t : ℝ) - δ) < t :=
    max_lt htR (sub_lt_self _ hδ)
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hlo
  have hq0 : 0 ≤ q := Rat.cast_nonneg.mp (le_of_lt ((le_max_left _ _).trans_lt hqlo))
  let qn : ℚ≥0 := ⟨q, hq0⟩
  have hqn : ((qn : ℝ≥0) : ℝ) = (q : ℝ) := by
    norm_cast
  have hqt : (qn : ℝ≥0) < t := by exact_mod_cast (hqn ▸ hqhi)
  refine ⟨qn, hqt, ?_⟩
  have hd : dist (qn : ℝ≥0) t < δ := by
    rw [NNReal.dist_eq, hqn, abs_of_neg (sub_neg.mpr hqhi)]
    have := (le_max_right (0 : ℝ) ((t : ℝ) - δ)).trans_lt hqlo
    linarith
  have hsmall := hcont hd
  rw [Real.dist_eq] at hsmall
  have hleft := (abs_lt.mp hsmall).1
  linarith

theorem abs_le_of_le_rationalExit {Ω : Type*} {M : ℝ≥0 → Ω → ℝ}
    {r : ℝ} {ω : Ω} (hc : Continuous (fun t => M t ω))
    (hzero : |M 0 ω| ≤ r) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ rationalExit M r ω) : |M t ω| ≤ r := by
  by_cases ht0 : t = 0
  · simpa [ht0] using hzero
  by_contra hbound
  obtain ⟨q, hqt, hq⟩ := exists_earlier_nnrat hc.abs.continuousAt
    (pos_iff_ne_zero.mpr ht0) (lt_of_not_ge hbound)
  have hexit : rationalExit M r ω ≤ ((q : ℝ≥0) : WithTop ℝ≥0) := by
    exact (iInf_le (fun p : ℚ≥0 => if r < |M (p : ℝ≥0) ω| then
      ((p : ℝ≥0) : WithTop ℝ≥0) else ⊤) q).trans
        (by simp only [hq, ite_true, if_true, le_refl])
  have hle : t ≤ (q : ℝ≥0) := WithTop.coe_le_coe.mp (ht.trans hexit)
  exact (not_lt_of_ge hle) hqt

end Problem367.PosteriorStoppingTimes

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_CompensatorStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PosteriorCompensatorStopping

open PosteriorStoppingTimes

theorem abs_stoppedProcess_le_of_le_exit {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}
    {τ : Ω → WithTop ℝ≥0} {ω : Ω} {r : ℝ}
    (hc : Continuous (fun t => X t ω)) (hzero : |X 0 ω| ≤ r)
    (hτ : τ ω ≤ rationalExit X r ω) (t : ℝ≥0) :
    |stoppedProcess X τ t ω| ≤ r := by
  let s : WithTop ℝ≥0 := min (t : WithTop ℝ≥0) (τ ω)
  have hsne : s ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hsne
  have huτ : (u : WithTop ℝ≥0) ≤ rationalExit X r ω := by
    rw [hu]
    exact (min_le_right _ _).trans hτ
  change |X s.untopA ω| ≤ r
  rw [← hu]
  exact abs_le_of_le_rationalExit hc hzero huτ

end Problem367.PosteriorCompensatorStopping

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ConditionalCopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingConditionalCopyBounds

open PlantedSymmetry IsingObservationInnovation WienerSampler

theorem progressive_leftObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.1 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_fst.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.1 v).continuous)

theorem progressive_rightObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.2 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_snd.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.2 v).continuous)

end Problem367.IsingConditionalCopyBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationComparison
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable [IsProbabilityMeasure μ]

theorem kernel_graphLaw :
    ((observationLaw μ).map (innovationMap beta)) ⊗ₘ kernel beta μ =
      IsingConditionalCopyBounds.graphLaw beta μ :=
  ObservableDisintegration.compProd_kernel (observationLaw μ)
    (measurable_innovationMap beta)

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ContinuousPosteriorInterior
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

theorem isStronglyProgressive_artanh
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) :
    IsStronglyProgressive F (fun t ω => Real.artanh (m t ω)) := by
  have ha : Measurable Real.artanh := by
    unfold Real.artanh
    fun_prop
  intro t
  let : MeasurableSpace Ω := F t
  exact (ha.comp (hm t).measurable).stronglyMeasurable

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalPosteriorStops
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy PosteriorCompensatorStopping

lemma artanh_continuousPosterior {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) :
    Real.artanh (continuousPosterior beta v t x) = continuousField beta v t x :=
  Real.artanh_tanh _

lemma copyProjection_measurePreserving
    {d : ℕ} (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (j : Bool) :
    MeasurePreserving (projection (d := d) j) (copies beta μ) (observationLaw μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_innovationMap <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨hl, hr⟩ := IsingConditionalCopyBounds.measurePreserving_observation_copies
    (beta := beta) (μ := μ) (rho := (observationLaw μ).map (innovationMap beta))
    (eta := kernel beta μ) kernel_graphLaw
  cases j
  · exact hr
  · exact hl

lemma copyResponseEnergy_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) (j : Bool) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (copyResponseEnergy beta v j) := by
  cases j
  · exact isStronglyProgressive_infiniteGibbsResponseRow _ beta v _
      IsingConditionalCopyBounds.progressive_rightObservation
  · exact isStronglyProgressive_infiniteGibbsResponseRow _ beta v _
      IsingConditionalCopyBounds.progressive_leftObservation

 theorem copyResponseEnergy_integrable
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (j : Bool) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Joint d => copyResponseEnergy beta v j p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (copies beta μ)) :=
  (copy_row_energy_integrable hμ hb v j T.coe_nonneg).2.1

 theorem commonResponseCompensator_continuous
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (v : TreeVertex d) :
    ∀ᵐ q ∂copies beta μ, Continuous (fun t => commonResponseCompensator beta v t q) := by
  apply ae_continuous_nnrealTimePrimitive_of_joint
  intro n
  have hi := (copyResponseEnergy_integrable hμ hb v true (n : ℝ≥0)).add
    (copyResponseEnergy_integrable hμ hb v false (n : ℝ≥0))
  exact hi

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousRootResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}

lemma continuous_siteRootResponse (hb : 0 ≤ beta) (v : TreeVertex d) :
    Continuous (siteRootResponse hb v) := by
  unfold siteRootResponse
  apply Continuous.const_mul
  apply continuous_finsetProd
  intro i hi
  exact (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).comp
    (continuous_fst.comp ((continuous_cavityFromSites
      (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta)).comp
      ((continuous_apply _).prodMk (continuous_apply _))))

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CommonStopBounds
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy PosteriorCompensatorStopping

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

lemma copyResponseDriftDifference_progressive (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (copyResponseDriftDifference beta v) := by
  have hl := isStronglyProgressive_infiniteGibbsSpinMean
    ContinuousCopyBrownian.joinedFiltration beta v _
    IsingConditionalCopyBounds.progressive_leftObservation
  have hr := isStronglyProgressive_infiniteGibbsSpinMean
    ContinuousCopyBrownian.joinedFiltration beta v _
    IsingConditionalCopyBounds.progressive_rightObservation
  exact (hl.mul (copyResponseEnergy_progressive beta v true)).sub
    (hr.mul (copyResponseEnergy_progressive beta v false))

lemma copyResponseEnergy_nonneg (beta : ℝ) (v : TreeVertex d) (j : Bool)
    (t : ℝ≥0) (q : Joint d) : 0 ≤ copyResponseEnergy beta v j t q :=
  tsum_nonneg (fun _ => sq_nonneg _)

theorem abs_copyResponseDriftDifference_le (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (q : Joint d) :
    |copyResponseDriftDifference beta v t q| ≤
      copyResponseEnergy beta v true t q + copyResponseEnergy beta v false t q := by
  have hl : |posterior beta v t q.2.1| ≤ 1 := posterior_norm_le_one beta v t q.2.1
  have hr : |posterior beta v t q.2.2| ≤ 1 := posterior_norm_le_one beta v t q.2.2
  unfold copyResponseDriftDifference
  calc
    _ ≤ |posterior beta v t q.2.1 * copyResponseEnergy beta v true t q| +
        |posterior beta v t q.2.2 * copyResponseEnergy beta v false t q| := abs_sub _ _
    _ = |posterior beta v t q.2.1| * copyResponseEnergy beta v true t q +
        |posterior beta v t q.2.2| * copyResponseEnergy beta v false t q := by
      rw [abs_mul, abs_mul, abs_of_nonneg (copyResponseEnergy_nonneg beta v true t q),
        abs_of_nonneg (copyResponseEnergy_nonneg beta v false t q)]
    _ ≤ _ := add_le_add
      (mul_le_of_le_one_left (copyResponseEnergy_nonneg beta v true t q) hl)
      (mul_le_of_le_one_left (copyResponseEnergy_nonneg beta v false t q) hr)

theorem copyResponseDriftDifference_integrable
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Joint d => copyResponseDriftDifference beta v p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (copies beta μ)) := by
  have hm := (stronglyMeasurable_joint_of_isStronglyProgressive
    (copyResponseDriftDifference_progressive beta v)).comp_measurable
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  apply ((copyResponseEnergy_integrable hμ hb v true T).add
    (copyResponseEnergy_integrable hμ hb v false T)).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall (fun p => abs_copyResponseDriftDifference_le beta v p.1.toNNReal p.2)

theorem ae_all_abs_driftPrimitive_le_commonResponseCompensator
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) :
    ∀ᵐ q ∂copies beta μ, ∀ t : ℝ≥0,
      |nnrealTimePrimitive (copyResponseDriftDifference beta v) t q| ≤
        commonResponseCompensator beta v t q := by
  have hiB := ae_intervalIntegrable_horizons_of_joint
    (μ := copies beta μ) (a := copyResponseDriftDifference beta v)
    (fun n => by simpa only [NNReal.coe_natCast] using
      copyResponseDriftDifference_integrable hμ hb v (n : ℝ≥0))
  have hiE := ae_intervalIntegrable_horizons_of_joint
    (μ := copies beta μ)
    (a := fun t q => copyResponseEnergy beta v true t q + copyResponseEnergy beta v false t q)
    (fun n => by
      have hi := (copyResponseEnergy_integrable hμ hb v true (n : ℝ≥0)).add
        (copyResponseEnergy_integrable hμ hb v false (n : ℝ≥0))
      exact hi)
  filter_upwards [hiB, hiE] with q hB hE
  intro t
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
  have hrestrict {f : ℝ → ℝ} (hi : IntervalIntegrable f volume 0 (n : ℝ)) :
      IntervalIntegrable f volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mp hi).mono_set
        (Ioc_subset_Ioc le_rfl hn))
  unfold nnrealTimePrimitive commonResponseCompensator
  calc
    _ ≤ ∫ s in (0 : ℝ)..(t : ℝ), |copyResponseDriftDifference beta v s.toNNReal q| :=
      intervalIntegral.abs_integral_le_integral_abs t.coe_nonneg
    _ ≤ _ := intervalIntegral.integral_mono t.coe_nonneg (hrestrict (hB n)).abs
      (hrestrict (hE n)) (fun s => abs_copyResponseDriftDifference_le beta v s.toNNReal q)

theorem ae_all_abs_commonResponseCompensator_stopped_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (n : ℕ) {τ : Joint d → WithTop ℝ≥0}
    (hτ : ∀ q, τ q ≤ commonPosteriorExit beta v n q) :
    ∀ᵐ q ∂copies beta μ, ∀ t : ℝ≥0,
      |stoppedProcess (commonResponseCompensator beta v)
        τ t q| ≤ (n : ℝ) + 1 := by
  filter_upwards [commonResponseCompensator_continuous hμ hb v] with q hc
  intro t
  apply abs_stoppedProcess_le_of_le_exit hc
    (by simp [commonResponseCompensator, nnrealTimePrimitive] <;> positivity) _ t
  exact (hτ q).trans ((min_le_left _ _).trans (min_le_right _ _))

theorem ae_all_abs_stoppedDriftPrimitive_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (n : ℕ) {τ : Joint d → WithTop ℝ≥0}
    (hτ : ∀ q, τ q ≤ commonPosteriorExit beta v n q) :
    ∀ᵐ q ∂copies beta μ, ∀ t : ℝ≥0,
      |stoppedProcess (nnrealTimePrimitive (copyResponseDriftDifference beta v))
        τ t q| ≤ (n : ℝ) + 1 := by
  filter_upwards [ae_all_abs_driftPrimitive_le_commonResponseCompensator hμ hb v,
    ae_all_abs_commonResponseCompensator_stopped_le hμ hb v n hτ] with q hB hE
  intro t
  exact (hB _).trans ((le_abs_self _).trans (hE t))

theorem ae_all_abs_cutoffDriftPrimitive_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) (n : ℕ) {τ : Joint d → WithTop ℝ≥0}
    (hτ : ∀ q, τ q ≤ commonPosteriorExit beta v n q) :
    ∀ᵐ q ∂copies beta μ, ∀ t : ℝ≥0,
      |nnrealTimePrimitive
        (StoppedTimePrimitive.stopDensity (copyResponseDriftDifference beta v)
          τ) t q| ≤ (n : ℝ) + 1 := by
  filter_upwards [ae_all_abs_stoppedDriftPrimitive_le hμ hb v n hτ] with q hq
  intro t
  rw [← StoppedTimePrimitive.stoppedProcess_primitive]
  exact hq t

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousCopyCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingContinuousCopyCoefficients
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}

lemma field_progressive (j : Bool) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : Joint d) => continuousField beta v t (projection j q)) := by
  have hobs (i : TreeVertex d) : IsStronglyProgressive
      ContinuousCopyBrownian.joinedFiltration
      (fun t (q : Joint d) => projection j q i t) := by
    cases j
    · exact IsingConditionalCopyBounds.progressive_rightObservation i
    · exact IsingConditionalCopyBounds.progressive_leftObservation i
  have hraw := isStronglyProgressive_artanh _
    (isStronglyProgressive_infiniteGibbsSpinMean _ beta v _ hobs)
  exact ProgressiveVersionPushforward.progressive_version hraw

lemma response_progressive (hb : 0 ≤ beta) (j : Bool) (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration (response hb j v) := by
  intro T
  let : MeasurableSpace (Joint d) := ContinuousCopyBrownian.joinedFiltration T
  exact ((continuous_siteRootResponse hb v).measurable.comp
    (Measurable.of_eval (fun vertex => (field_progressive j vertex T).measurable))).stronglyMeasurable

end Problem367.IsingContinuousCopyCoefficients

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalLocalSquare
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy

 theorem continuousField_initial_zero
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    continuousField beta v 0 =ᵐ[observationLaw μ] 0 := by
  filter_upwards [continuousPosterior_initial_zero hd hμ hb hcrit v] with x hx
  have he := artanh_continuousPosterior beta v 0 x
  rw [hx] at he
  simpa only [Pi.zero_apply, Real.artanh_zero] using he.symm

 theorem continuousDifference_initial_zero
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    continuousDifference beta v 0 =ᵐ[copies beta μ] 0 := by
  have h0 := continuousField_initial_zero hd hμ hb hcrit v
  filter_upwards [(copyProjection_measurePreserving beta μ true).quasiMeasurePreserving.ae h0,
    (copyProjection_measurePreserving beta μ false).quasiMeasurePreserving.ae h0] with q hl hr
  change continuousField beta v 0 q.2.1 - continuousField beta v 0 q.2.2 = 0
  change continuousField beta v 0 q.2.1 = 0 at hl
  change continuousField beta v 0 q.2.2 = 0 at hr
  rw [hl, hr, sub_self]

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_L2CompensatedSquareStopping
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.L2CompensatedSquareStopping

open MartingaleStrongMaximal DominatedMartingaleRightContinuation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))

include hM h2 hcM

theorem exists_integrable_horizon_envelope (T : ℝ≥0) :
    ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω := by
  refine ⟨fun ω => maximalSquare M T ω + 1,
    (integrable_maximalSquare hM h2 hcM T).add (integrable_const _), ?_⟩
  filter_upwards [ae_all_sq_le_maximalSquare hM h2 hcM T] with ω hω
  intro t ht
  have habs : |M t ω| ≤ M t ω ^ 2 + 1 := by
    nlinarith [sq_nonneg (|M t ω| - 1 / 2), sq_abs (M t ω)]
  exact habs.trans (add_le_add (hω t ht) le_rfl)

theorem martingale_stoppedProcess_rightCont
    (hprogM : IsStronglyProgressive F M)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (stoppedProcess M τ) F.rightCont μ :=
  DominatedMartingaleRightContinuation.martingale_stoppedProcess_rightCont
    hM hprogM hcM (exists_integrable_horizon_envelope hM h2 hcM) hτ

variable
    (hA0 : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ A t ω)
    (hAmono : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    (hAint : ∀ t, Integrable (A t) μ)

include hA0 hAmono hAint

theorem exists_integrable_compensatedSquare_envelope (T : ℝ≥0) :
    ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω ^ 2 - A t ω| ≤ g ω := by
  refine ⟨fun ω => maximalSquare M T ω + A T ω,
    (integrable_maximalSquare hM h2 hcM T).add (hAint T), ?_⟩
  filter_upwards [ae_all_sq_le_maximalSquare hM h2 hcM T, hA0, hAmono]
    with ω hω ha hm
  intro t ht
  calc
    |M t ω ^ 2 - A t ω| ≤ |M t ω ^ 2| + |A t ω| := abs_sub _ _
    _ = M t ω ^ 2 + A t ω := by
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (ha t)]
    _ ≤ maximalSquare M T ω + A T ω := add_le_add (hω t ht) (hm ht)

variable (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)

include hcA hQ

theorem stopped_compensatedSquare_rightCont
    (hprogM : IsStronglyProgressive F M) (hprogA : IsStronglyProgressive F A)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (fun t ω => stoppedProcess M τ t ω ^ 2 - stoppedProcess A τ t ω)
      F.rightCont μ := by
  have hprog : IsStronglyProgressive F (fun t ω => M t ω ^ 2 - A t ω) := by
    intro t
    exact ((hprogM t).pow 2).sub (hprogA t)
  have hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω ^ 2 - A t ω) := by
    filter_upwards [hcM, hcA] with ω hm ha
    exact (hm.pow 2).sub ha
  exact DominatedMartingaleRightContinuation.martingale_stoppedProcess_rightCont
    hQ hprog hc
    (exists_integrable_compensatedSquare_envelope hM h2 hcM hA0 hAmono hAint) hτ

end Problem367.L2CompensatedSquareStopping

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_L2CompensatedDensityStopping
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.L2CompensatedDensityStopping

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M q : ℝ≥0 → Ω → ℝ}

theorem integrable_density_on_horizon
    (hq : ∀ N : ℕ, Integrable (fun p : ℝ × Ω => q p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (N : ℝ))).prod μ))
    (T : ℝ≥0) :
    Integrable (fun p : ℝ × Ω => q p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
  exact (hq N).mono_measure (Measure.prod_mono
    (Measure.restrict_mono (Ioc_subset_Ioc le_rfl hN) le_rfl) le_rfl)

theorem integrable_stopped_density_on_horizon
    (hprogq : IsStronglyProgressive F q)
    (hq : ∀ N : ℕ, Integrable (fun p : ℝ × Ω => q p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (N : ℝ))).prod μ))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ)
    (T : ℝ≥0) :
    Integrable (fun p : ℝ × Ω =>
      StoppedTimePrimitive.stopDensity q τ p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod μ) := by
  have hp := StoppedTimePrimitive.isStronglyProgressive_stopDensity
    (DominatedMartingaleRightContinuation.isStronglyProgressive_mono_filtration
      F.le_rightCont hprogq) hτ
  have hm : StronglyMeasurable (fun p : ℝ × Ω =>
      StoppedTimePrimitive.stopDensity q τ p.1.toNNReal p.2) :=
    (stronglyMeasurable_joint_of_isStronglyProgressive hp).comp_measurable
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  apply (integrable_density_on_horizon hq T).mono hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  unfold StoppedTimePrimitive.stopDensity
  split_ifs <;> simp only [le_refl, norm_zero, norm_nonneg]

theorem stopped_martingale_and_compensated_density
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hprogM : IsStronglyProgressive F M)
    (hprogq : IsStronglyProgressive F q)
    (hq0 : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ q t ω)
    (hq : ∀ N : ℕ, Integrable (fun p : ℝ × Ω => q p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (N : ℝ))).prod μ))
    (hQ : Martingale (fun t ω => M t ω ^ 2 - nnrealTimePrimitive q t ω) F μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F.rightCont τ) :
    Martingale (stoppedProcess M τ) F.rightCont μ ∧
      Martingale (fun t ω => stoppedProcess M τ t ω ^ 2 -
        nnrealTimePrimitive (StoppedTimePrimitive.stopDensity q τ) t ω)
        F.rightCont μ := by
  have hA0 : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ nnrealTimePrimitive q t ω :=
    hq0.mono (fun ω hω t => nnrealTimePrimitive_nonneg hω t)
  have hAmono : ∀ᵐ ω ∂μ, Monotone (fun t => nnrealTimePrimitive q t ω) :=
    ae_monotone_nnrealTimePrimitive_of_joint hq hq0
  have hAint (t : ℝ≥0) : Integrable (nnrealTimePrimitive q t) μ :=
    nnrealTimePrimitive_integrable (integrable_density_on_horizon hq t)
  have hcA : ∀ᵐ ω ∂μ, Continuous (fun t => nnrealTimePrimitive q t ω) :=
    ae_continuous_nnrealTimePrimitive_of_joint hq
  refine ⟨L2CompensatedSquareStopping.martingale_stoppedProcess_rightCont
    hM h2 hcM hprogM hτ, ?_⟩
  have hs := L2CompensatedSquareStopping.stopped_compensatedSquare_rightCont
    hM h2 hcM hA0 hAmono hAint hcA hQ hprogM
    (isStronglyProgressive_nnrealTimePrimitive hprogq) hτ
  simpa only [StoppedTimePrimitive.stoppedProcess_primitive] using hs

end Problem367.L2CompensatedDensityStopping

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_StoppedSquareAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy IsingContinuousCopyCoefficients

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

lemma copyResponseNoiseEnergy_progressive (hb : 0 ≤ beta) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (copyResponseNoiseEnergy (d := d) hb) := by
  intro T
  let : MeasurableSpace (Joint d) := ContinuousCopyBrownian.joinedFiltration T
  exact StronglyMeasurable.tsum (fun v =>
    ((response_progressive hb true v T).sub (response_progressive hb false v T)).pow 2)

lemma copyResponseNoiseEnergy_nonneg (hb : 0 ≤ beta) (t : ℝ≥0) (z : Joint d) :
    0 ≤ copyResponseNoiseEnergy hb t z := tsum_nonneg (fun _ => sq_nonneg _)

lemma copyResponseNoiseEnergy_integrable (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Joint d => copyResponseNoiseEnergy hb p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)) := by
  obtain ⟨hl, hil⟩ := response_row_energy hd hμ hb hcrit true T
  obtain ⟨hr, hir⟩ := response_row_energy hd hμ hb hcrit false T
  exact DiscrepancyEnergy.integrable_sq_difference_row
    (fun v => (NNRealBoundedDriftEnergy.stronglyMeasurable_realExtension
      (response_progressive hb true v)).aestronglyMeasurable)
    (fun v => (NNRealBoundedDriftEnergy.stronglyMeasurable_realExtension
      (response_progressive hb false v)).aestronglyMeasurable)
    hil hir (hl.and hr)

theorem stopped_difference_energy_of_representation
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {M : ℝ≥0 → Joint d → ℝ}
    (hM : Martingale M ContinuousCopyBrownian.joinedFiltration (copies beta μ))
    (h2 : ∀ t, MemLp (M t) 2 (copies beta μ))
    (hcM : ∀ᵐ z ∂copies beta μ, Continuous (fun t => M t z))
    (hpM : IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration M)
    (hQ : Martingale (fun t z => M t z ^ 2 -
      nnrealTimePrimitive (copyResponseNoiseEnergy hb) t z)
      ContinuousCopyBrownian.joinedFiltration (copies beta μ))
    (hrep : ∀ᵐ z ∂copies beta μ, ∀ t,
      continuousDifference beta (ConnectedHull.root d) t z = M t z +
        nnrealTimePrimitive (copyResponseDriftDifference beta (ConnectedHull.root d)) t z)
    (n : ℕ) {τ : Joint d → WithTop ℝ≥0}
    (hτ : IsStoppingTime ContinuousCopyBrownian.joinedFiltration.rightCont τ)
    (hle : ∀ z, τ z ≤ commonPosteriorExit beta (ConnectedHull.root d) n z)
    (T : ℝ≥0) :
    (∫ z, (stoppedProcess (continuousDifference beta (ConnectedHull.root d)) τ T z) ^ 2
      ∂copies beta μ) =
      ∫ s in (0 : ℝ)..(T : ℝ), ∫ z,
        StoppedTimePrimitive.stopDensity (copyResponseNoiseEnergy hb) τ s.toNNReal z +
          2 * (stoppedProcess (continuousDifference beta (ConnectedHull.root d)) τ s.toNNReal z *
            StoppedTimePrimitive.stopDensity
              (copyResponseDriftDifference beta (ConnectedHull.root d)) τ s.toNNReal z)
        ∂copies beta μ := by
  let b := copyResponseDriftDifference beta (ConnectedHull.root d)
  let q := copyResponseNoiseEnergy (d := d) hb
  have hbi (N : ℕ) : Integrable (fun p : ℝ × Joint d => b p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (N : ℝ))).prod (copies beta μ)) := by
    simpa only [NNReal.coe_natCast] using
      copyResponseDriftDifference_integrable hμ hb (ConnectedHull.root d) (N : ℝ≥0)
  have hqi (N : ℕ) : Integrable (fun p : ℝ × Joint d => q p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (N : ℝ))).prod (copies beta μ)) := by
    simpa only [NNReal.coe_natCast] using
      copyResponseNoiseEnergy_integrable hd hμ hb hcrit (N : ℝ≥0)
  have hpb := copyResponseDriftDifference_progressive beta (ConnectedHull.root d)
  have hpq := copyResponseNoiseEnergy_progressive (d := d) hb
  obtain ⟨hMs, hQs⟩ := L2CompensatedDensityStopping.stopped_martingale_and_compensated_density
    hM h2 hcM hpM hpq (Eventually.of_forall (fun z t => copyResponseNoiseEnergy_nonneg hb t z))
    hqi hQ hτ
  have hMps := (DominatedMartingaleRightContinuation.isStronglyProgressive_mono_filtration
    ContinuousCopyBrownian.joinedFiltration.le_rightCont hpM).stoppedProcess hτ
  have hbps := StoppedTimePrimitive.isStronglyProgressive_stopDensity
    (DominatedMartingaleRightContinuation.isStronglyProgressive_mono_filtration
      ContinuousCopyBrownian.joinedFiltration.le_rightCont hpb) hτ
  have hsrep : ∀ᵐ z ∂copies beta μ, ∀ t,
      stoppedProcess (continuousDifference beta (ConnectedHull.root d)) τ t z =
        stoppedProcess M τ t z + nnrealTimePrimitive (StoppedTimePrimitive.stopDensity b τ) t z := by
    filter_upwards [hrep] with z hz
    intro t
    rw [← StoppedTimePrimitive.stoppedProcess_primitive]
    exact hz _
  have hX : ∀ᵐ z ∂copies beta μ, ∀ t ≤ T,
      |stoppedProcess M τ t z + nnrealTimePrimitive (StoppedTimePrimitive.stopDensity b τ) t z| ≤
        2 * (T : ℝ) + 2 * (d : ℝ) * beta := by
    filter_upwards [hsrep, ae_horizon_stopped_continuousDifference_bound
      hd hμ hb hcrit (ConnectedHull.root d) τ T] with z hz hbound
    intro t ht
    rw [← hz t]
    exact hbound t ht
  have hA : ∀ᵐ z ∂copies beta μ, ∀ t ≤ T,
      |nnrealTimePrimitive (StoppedTimePrimitive.stopDensity b τ) t z| ≤ (n : ℝ) + 1 :=
    (ae_all_abs_cutoffDriftPrimitive_le hμ hb (ConnectedHull.root d) n hle).mono
      (fun z hz t _ => hz t)
  obtain ⟨_, hsq⟩ := NNRealBoundedDriftEnergy.integral_sq_of_bounded_process_compensated
    hMs hQs hMps hbps
    (L2CompensatedDensityStopping.integrable_stopped_density_on_horizon hpb hbi hτ T)
    (L2CompensatedDensityStopping.integrable_stopped_density_on_horizon hpq hqi hτ T) hX hA
  have hzM : stoppedProcess M τ 0 =ᵐ[copies beta μ] 0 := by
    filter_upwards [hrep, continuousDifference_initial_zero hd hμ hb hcrit (ConnectedHull.root d)]
      with z hz hzero
    have hz0 := hz 0
    simp only [nnrealTimePrimitive, NNReal.coe_zero, intervalIntegral.integral_same, add_zero] at hz0
    rw [stoppedProcess_eq_of_le (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ z from zero_le)]
    exact hz0.symm.trans hzero
  have hzint : (∫ z, stoppedProcess M τ 0 z ^ 2 ∂copies beta μ) = 0 := by
    calc
      _ = ∫ _z, (0 : ℝ) ∂copies beta μ := integral_congr_ae
        (hzM.mono (fun z hz => by simp only [hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0)]))
      _ = 0 := integral_zero _ _
  rw [hzint, zero_add] at hsq
  calc
    _ = ∫ z, (stoppedProcess M τ T z +
        nnrealTimePrimitive (StoppedTimePrimitive.stopDensity b τ) T z) ^ 2 ∂copies beta μ :=
      integral_congr_ae (hsrep.mono (fun z hz => congrArg (fun r : ℝ => r ^ 2) (hz T)))
    _ = _ := hsq.trans (by
      apply intervalIntegral.integral_congr
      intro s hs
      apply integral_congr_ae
      filter_upwards [hsrep] with z hz
      rw [← hz s.toNNReal])

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ActualVarianceAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem variance_analysis_of_joined_decomposition_oai
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (S : IsingJoinedResponseIntegrals.IntegralSystem hb μ)
    (hrep : ∀ᵐ z ∂copies beta μ, ∀ t,
      continuousDifference beta (ConnectedHull.root d) t z =
        (S.total true t z - S.total false t z) +
          nnrealTimePrimitive (copyResponseDriftDifference beta (ConnectedHull.root d)) t z)
    (T : ℝ≥0) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ z,
      (field beta (ConnectedHull.root d) t.toNNReal z.2.1 -
        field beta (ConnectedHull.root d) t.toNNReal z.2.2) ^ 2 ∂copies beta μ) 0 T ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      deriv (fun s : ℝ => ∫ z,
        (field beta (ConnectedHull.root d) s.toNNReal z.2.1 -
          field beta (ConnectedHull.root d) s.toNNReal z.2.2) ^ 2 ∂copies beta μ) t =
        ∫ z, density beta (ConnectedHull.root d) t z ∂copies beta μ) := by
  have hM := (S.total_martingale true).sub (S.total_martingale false)
  have h2 (t : ℝ≥0) := (S.total_memLp true t).sub (S.total_memLp false t)
  have hc : ∀ᵐ z ∂copies beta μ, Continuous (fun t => S.total true t z - S.total false t z) := by
    filter_upwards [S.total_continuous true, S.total_continuous false] with z hl hr
    exact hl.sub hr
  have hp := (S.total_predictable true).isStronglyProgressive.sub
    (S.total_predictable false).isStronglyProgressive
  have hQ : Martingale (fun t z => (S.total true t z - S.total false t z) ^ 2 -
      nnrealTimePrimitive (copyResponseNoiseEnergy hb) t z)
      ContinuousCopyBrownian.joinedFiltration (copies beta μ) :=
    S.difference_compensatedSquare
  apply actual_variance_analysis_of_common_local_square hd hμ hb hcrit (ConnectedHull.root d) T
  intro n t ht
  have hs := stopped_difference_energy_of_representation hd hμ hb hcrit hM h2 hc hp hQ hrep n
    ((isLocalizingSequence_commonPosteriorExit hd hμ hb hcrit (ConnectedHull.root d)).isStoppingTime n)
    (fun _ => le_rfl) t
  apply hs.trans
  have hnoise : IsingCopySquareDensity.noise (d := d) hb = copyResponseNoiseEnergy hb := by
    funext s z
    rfl
  have hdrift : IsingCopySquareDensity.drift (d := d) beta =
      copyResponseDriftDifference beta (ConnectedHull.root d) := by
    funext s z
    rfl
  simpa only [hnoise, hdrift, mul_assoc] using
    IsingCopySquareDensity.integral_integral_stopped_noise_add_drift_eq_actual
      hd hμ hb hcrit (commonPosteriorExit beta (ConnectedHull.root d) n) t

end Problem367.IsingObservationFactor

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition_oai := @OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition_oai
