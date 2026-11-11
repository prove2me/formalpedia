-- Prove2me | solution 1 for OAI.Problem367.IsingObservationFactor.actual_variance_analysis
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:47:58.497846+00:00
-- url     : https://prove2.me/submissions/b1fcf361-96bb-48ac-b9ea-d3ef7364f06b

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_BrownianArrayFiltration_exists_global_continuous_spatial_integral_compensatedSquare
import Theorems.Thm_OAI_Problem367_IsingInnovation_exists_continuous_posterior
import Theorems.Thm_OAI_Problem367_IsingJoinedResponseIntegrals_exists_integrals
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_canonical_field_eq_normalized_integral
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_continuousRootResponse_hasSum_timeEnergy
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_copied_difference_decomposition
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_variance_analysis_of_joined_decomposition

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_UniformGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianGrid

lemma integral_sq_sub_le_two {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y Z : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P) :
    (∫ ω, (X ω - Y ω) ^ 2 ∂P) ≤
      2 * (∫ ω, (X ω - Z ω) ^ 2 ∂P) + 2 * (∫ ω, (Y ω - Z ω) ^ 2 ∂P) := by
  have hXY : Integrable (fun ω => (X ω - Y ω) ^ 2) P := (hX.sub hY).integrable_sq
  have hXZ : Integrable (fun ω => (X ω - Z ω) ^ 2) P := (hX.sub hZ).integrable_sq
  have hYZ : Integrable (fun ω => (Y ω - Z ω) ^ 2) P := (hY.sub hZ).integrable_sq
  calc
    _ ≤ ∫ ω, 2 * (X ω - Z ω) ^ 2 + 2 * (Y ω - Z ω) ^ 2 ∂P := by
      apply integral_mono hXY ((hXZ.const_mul 2).add (hYZ.const_mul 2))
      intro ω
      change (X ω - Y ω) ^ 2 ≤ 2 * (X ω - Z ω) ^ 2 + 2 * (Y ω - Z ω) ^ 2
      nlinarith [sq_nonneg (X ω + Y ω - 2 * Z ω)]
    _ = _ := by
      rw [integral_add (hXZ.const_mul 2) (hYZ.const_mul 2), integral_const_mul, integral_const_mul]

end Problem367.BrownianGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_ContinuousRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter TopologicalSpace

namespace Problem367

theorem ae_eq_of_dense_evaluations
    {Ω T E I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [TopologicalSpace T] [TopologicalSpace E] [T2Space E] [Countable I]
    (e : I → T) (he : DenseRange e) {f g : Ω → T → E}
    (hf : ∀ᵐ ω ∂μ, Continuous (f ω)) (hg : ∀ᵐ ω ∂μ, Continuous (g ω))
    (hfg : ∀ i, ∀ᵐ ω ∂μ, f ω (e i) = g ω (e i)) : f =ᵐ[μ] g := by
  have hall : ∀ᵐ ω ∂μ, ∀ i, f ω (e i) = g ω (e i) :=
    ae_all_iff.mpr hfg
  filter_upwards [hf, hg, hall] with ω hfω hgω hω
  exact he.equalizer hfω hgω (funext hω)

theorem ae_eq_of_continuous_of_evaluation_ae_eq
    {Ω T E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    [TopologicalSpace E] [T2Space E] {f g : Ω → T → E}
    (hf : ∀ᵐ ω ∂μ, Continuous (f ω)) (hg : ∀ᵐ ω ∂μ, Continuous (g ω))
    (hfg : ∀ t, ∀ᵐ ω ∂μ, f ω t = g ω t) : f =ᵐ[μ] g := by
  exact ae_eq_of_dense_evaluations (TopologicalSpace.denseSeq T)
    (TopologicalSpace.denseRange_denseSeq T) hf hg (fun _ => hfg _)

theorem ae_eq_of_integral_sq_sub_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hInt : Integrable (fun ω => (f ω - g ω) ^ 2) μ)
    (hzero : (∫ ω, (f ω - g ω) ^ 2 ∂μ) = 0) : f =ᵐ[μ] g := by
  have h := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (f ω - g ω))
    hInt).mp hzero
  filter_upwards [h] with ω hω
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hω)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_IntegralProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianGrid

theorem ae_eq_of_mean_square_limits
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {I J : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hI : MemLp I 2 P) (hJ : MemLp J 2 P)
    (hlimI : Tendsto (fun n => ∫ ω, (X n ω - I ω) ^ 2 ∂P) atTop (𝓝 0))
    (hlimJ : Tendsto (fun n => ∫ ω, (X n ω - J ω) ^ 2 ∂P) atTop (𝓝 0)) :
    I =ᵐ[P] J := by
  have hb (n : ℕ) : (∫ ω, (I ω - J ω) ^ 2 ∂P) ≤
      2 * (∫ ω, (X n ω - I ω) ^ 2 ∂P) + 2 * (∫ ω, (X n ω - J ω) ^ 2 ∂P) := by
    simpa only [sub_sq_comm] using integral_sq_sub_le_two hI hJ (hX n)
  have hz : (∫ ω, (I ω - J ω) ^ 2 ∂P) ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds
      (show Tendsto (fun n => 2 * (∫ ω, (X n ω - I ω) ^ 2 ∂P) +
        2 * (∫ ω, (X n ω - J ω) ^ 2 ∂P)) atTop (𝓝 0) from ?_)
      (Filter.Eventually.of_forall hb)
    simpa only [mul_zero, add_zero] using (hlimI.const_mul 2).add (hlimJ.const_mul 2)
  exact ae_eq_of_integral_sq_sub_eq_zero (hI.sub hJ).integrable_sq
    (le_antisymm hz (integral_nonneg (fun ω => sq_nonneg _)))

end Problem367.BrownianGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_IntegralTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal Topology

namespace Problem367.BrownianGrid

theorem integral_sq_sub_comp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) {X I : Ω → ℝ}
    (hX : AEStronglyMeasurable X P) (hI : AEStronglyMeasurable I P) :
    (∫ ω, (X (φ ω) - I (φ ω)) ^ 2 ∂Q) =
      ∫ ω, (X ω - I ω) ^ 2 ∂P := by
  have hm : AEStronglyMeasurable (fun ω => (X ω - I ω) ^ 2) (Q.map φ) := by
    rw [hφ.map_eq]
    exact (hX.sub hI).pow 2
  simpa only [hφ.map_eq] using (integral_map hφ.aemeasurable hm).symm

theorem meanSquare_limit_comp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) {X : ℕ → Ω → ℝ} {I : Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) P) (hI : AEStronglyMeasurable I P)
    (hlim : Tendsto (fun n => ∫ ω, (X n ω - I ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (X n (φ ω) - I (φ ω)) ^ 2 ∂Q) atTop (𝓝 0) := by
  have heq : (fun n => ∫ ω, (X n (φ ω) - I (φ ω)) ^ 2 ∂Q) =
      (fun n => ∫ ω, (X n ω - I ω) ^ 2 ∂P) :=
    funext (fun n => integral_sq_sub_comp hφ (hX n) hI)
  rw [heq]
  exact hlim

end Problem367.BrownianGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_PredictableL2Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem367.PredictableL2

theorem inner_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  simp only [hfω, hgω, Real.inner_apply]

theorem norm_toLp_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp]
  simp only [sq]

theorem toLp_finsetSum {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) (s : Finset ι) :
    (memLp_finsetSum s (fun i _ => hf i)).toLp (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, (hf i).toLp (f i) := by
  apply Lp.ext
  apply (MemLp.coeFn_toLp _).trans
  apply Filter.EventuallyEq.symm
  apply (Lp.coeFn_fun_finsetSum s (fun i => (hf i).toLp (f i))).trans
  have heq : ∀ᵐ ω ∂μ, ∀ i ∈ s, (hf i).toLp (f i) ω = f i ω :=
    (Filter.eventually_all_finite s.finite_toSet).mpr (fun i _ => (hf i).coeFn_toLp)
  filter_upwards [heq] with ω hω
  exact Finset.sum_congr rfl (fun i hi => hω i hi)

theorem tendsto_integral_sq_error_of_hasSum
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ)
    (hYsum : HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y)) :
    Tendsto (fun s : Finset ι => ∫ ω, ((∑ i ∈ s, f i ω) - Y ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have h := ((hYsum.sub_const (hY.toLp Y)).norm).pow 2
  change Tendsto _ atTop _ at h
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  calc
    _ = ‖((memLp_finsetSum s (fun i _ => hf i)).sub hY).toLp
        ((fun ω => ∑ i ∈ s, f i ω) - Y)‖ ^ 2 :=
      (norm_toLp_sq ((memLp_finsetSum s (fun i _ => hf i)).sub hY)).symm
    _ = _ := by
      change ‖(memLp_finsetSum s (fun i _ => hf i)).toLp
        (fun ω => ∑ i ∈ s, f i ω) - hY.toLp Y‖ ^ 2 = _
      rw [toLp_finsetSum]

end Problem367.PredictableL2

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FilteringRepresentationClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.FilteringRepresentationClosure

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem tendsto_toLp_of_integral_sq_error
    {α : Type*} {l : Filter α} {F : α → Ω → ℝ} {Y : Ω → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (hY : MemLp Y 2 μ)
    (hlim : Tendsto (fun n => ∫ ω, (F n ω - Y ω) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun n => (hF n).toLp (F n)) l (𝓝 (hY.toLp Y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have heq (n : α) : (∫ ω, (F n ω - Y ω) ^ 2 ∂μ) =
      ‖(hF n).toLp (F n) - hY.toLp Y‖ ^ 2 := by
    exact (PredictableL2.norm_toLp_sq ((hF n).sub hY)).symm
  have h := hlim.sqrt
  simpa only [heq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

end RandomVariables

end Problem367.FilteringRepresentationClosure

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_MeanSquareDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.BrownianGrid

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}

theorem meanSquare_limit_comp_iff
    {α : Type*} {l : Filter α}
    (hφ : MeasurePreserving φ Q P) {X : α → Ω → ℝ} {I : Ω → ℝ}
    (hX : ∀ a, AEStronglyMeasurable (X a) P)
    (hI : AEStronglyMeasurable I P) :
    Tendsto (fun a => ∫ ω, (X a (φ ω) - I (φ ω)) ^ 2 ∂Q) l (𝓝 0) ↔
      Tendsto (fun a => ∫ ω, (X a ω - I ω) ^ 2 ∂P) l (𝓝 0) := by
  have heq : (fun a => ∫ ω, (X a (φ ω) - I (φ ω)) ^ 2 ∂Q) =
      (fun a => ∫ ω, (X a ω - I ω) ^ 2 ∂P) :=
    funext (fun a => integral_sq_sub_comp hφ (hX a) hI)
  rw [heq]

end Problem367.BrownianGrid

namespace Problem367.PredictableL2

theorem hasSum_toLp_iff_meanSquare
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 P)
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y) ↔
      Tendsto (fun s : Finset ι => ∫ ω,
        ((∑ i ∈ s, f i ω) - Y ω) ^ 2 ∂P) atTop (𝓝 0) := by
  constructor
  · exact tendsto_integral_sq_error_of_hasSum f hf hY
  · intro hlim
    have h := FilteringRepresentationClosure.tendsto_toLp_of_integral_sq_error
      (fun s : Finset ι => memLp_finsetSum s (fun i _ => hf i)) hY hlim
    change Tendsto (fun s : Finset ι => ∑ i ∈ s, (hf i).toLp (f i))
      atTop (𝓝 (hY.toLp Y))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext s
    exact (toLp_finsetSum f hf s).symm

end Problem367.PredictableL2

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_MeanSquarePullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.PredictableL2

theorem hasSum_toLp_comp_measurePreserving
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P)
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 P)
    {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (hsum : HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y)) :
    HasSum (fun i => ((hf i).comp_measurePreserving hφ).toLp (f i ∘ φ))
      ((hY.comp_measurePreserving hφ).toLp (Y ∘ φ)) := by
  apply (hasSum_toLp_iff_meanSquare (fun i => f i ∘ φ)
    (fun i => (hf i).comp_measurePreserving hφ)
    (hY.comp_measurePreserving hφ)).mpr
  exact (BrownianGrid.meanSquare_limit_comp_iff hφ
    (fun s : Finset ι => (memLp_finsetSum s (fun i _ => hf i)).aestronglyMeasurable)
    hY.aestronglyMeasurable).mpr
    (tendsto_integral_sq_error_of_hasSum f hf hY hsum)

end Problem367.PredictableL2

end

end OAI
end

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_PosteriorField
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367

open PlantedSymmetry

theorem HasFreeIsingLaw.brownian_past_posterior_field_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    let ρ := μ.prod (Measure.infinitePi ν)
    let m := ρ[fun p => spinSign (p.1 v) |
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
        inferInstance]
    ∀ᵐ p ∂ρ, m p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (m p) - ((t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))| ≤
        (d : ℝ) * beta := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun ω i => B i t (ω i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hspin : Measurable (fun sigma : TreeVertex d → IsingSpin => spinSign (sigma v)) :=
    hsign.comp (measurable_pi_apply v)
  have hspini : Integrable (fun sigma : TreeVertex d → IsingSpin => spinSign (sigma v)) μ := by
    apply Integrable.of_bound hspin.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro sigma
    cases hs : sigma v <;> norm_num [spinSign, hs]
  have hpull := condExp_comp_measurePreserving_comap hT
    (hspin.comp measurable_fst).stronglyMeasurable
    (integrable_plantedSpin (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) v)
    (observationSigma_le (TreeVertex d) t)
  have hpast := TerminalSufficiency.condExp_planted_infinite_past_eq_terminal
    μ ν hB hmB (fun sigma i => spinSign (sigma i))
    (fun sigma => spinSign (sigma v))
    (Measurable.of_eval (fun i => hsign.comp (measurable_pi_apply i))) hspin hspini t
  have hb := hμ.gaussian_posterior_field_bound hbeta t v
  rw [← hT.map_eq] at hb
  have hb' := ae_of_ae_map hT.measurable.aemeasurable hb
  rw [hT.map_eq] at hb'
  dsimp only
  filter_upwards [hpast, hpull, hb'] with p hpast hpull hb
  change _ = posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v (T p)
    at hpull
  have hsame : (observationSigma (TreeVertex d) (t : ℝ)).comap T =
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) inferInstance := by
    rw [observationSigma, MeasurableSpace.comap_comp]
    rfl
  rw [hsame] at hpull
  simp only [Function.comp_def, T, Prod.map_fst, id_eq] at hpull
  rw [hpast, hpull]
  exact hb

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_EnergyRiemannApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367.EnergyRiemann

theorem point_end (T : ℝ) {n : ℕ} (hn : 0 < n) : point T n n = T := by
  dsimp [point]
  field_simp

theorem point_step (T : ℝ) (n i : ℕ) :
    point T n (i + 1) - point T n i = T / n := by
  simp only [point, Nat.cast_add, Nat.cast_one]
  ring

theorem point_mono {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : Monotone (point T n) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

end Problem367.EnergyRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_RandomRiemannCompensator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace Problem367.RandomRiemann

theorem partition_error_le {f : ℝ → ℝ} (hf : Continuous f)
    {τ : ℕ → ℝ} (hτ : Monotone τ) (n : ℕ) {ε : ℝ}
    (hmod : ∀ i < n, ∀ x ∈ Icc (τ i) (τ (i + 1)), |f (τ i) - f x| ≤ ε) :
    |partitionSum f τ n - ∫ x in τ 0..τ n, f x| ≤ ε * (τ n - τ 0) := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := τ) (n := n) (fun i _ => hf.intervalIntegrable _ _)
  have heq : partitionSum f τ n - (∫ x in τ 0..τ n, f x) =
      ∑ i ∈ Finset.range n, ∫ x in τ i..τ (i + 1), f (τ i) - f x := by
    rw [partitionSum, ← hsplit, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ Finset.range n, |∫ x in τ i..τ (i + 1), f (τ i) - f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, ε * (τ (i + 1) - τ i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle := hτ (Nat.le_succ i)
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := τ i) (b := τ (i + 1)) (C := ε)
        (f := fun x => f (τ i) - f x) (fun x hx => ?_)
      · simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)] using h
      · rw [uIoc_of_le hle] at hx
        exact hmod i (Finset.mem_range.mp hi) x ⟨hx.1.le, hx.2⟩
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]

theorem stoppedPoint_mono {T : ℝ} (hT : 0 ≤ T) (t : ℝ) (n : ℕ) :
    Monotone (stoppedPoint T t n) := fun _ _ hij =>
  min_le_min_left t (EnergyRiemann.point_mono hT n hij)

theorem stoppedPoint_zero (T : ℝ) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    stoppedPoint T t n 0 = 0 := by simp [stoppedPoint, ht]

theorem stoppedPoint_end (T t : ℝ) {n : ℕ} (hn : 0 < n) :
    stoppedPoint T t n n = min t T := by rw [stoppedPoint, EnergyRiemann.point_end T hn]

theorem stoppedPoint_step_le {T : ℝ} (hT : 0 ≤ T) (t : ℝ) (n i : ℕ) :
    stoppedPoint T t n (i + 1) - stoppedPoint T t n i ≤ T / n := by
  have hle := EnergyRiemann.point_mono hT n (Nat.le_succ i)
  have hstep := EnergyRiemann.point_step T n i
  unfold stoppedPoint
  by_cases hi : EnergyRiemann.point T n i ≤ t
  · rw [min_eq_right hi]
    exact (sub_le_sub_right (min_le_right t _) _).trans_eq hstep
  · have ht : t ≤ EnergyRiemann.point T n i := le_of_not_ge hi
    rw [min_eq_left ht, min_eq_left (ht.trans hle), sub_self]
    positivity

theorem stoppedSum_eq_partitionSum {T : ℝ} (hT : 0 ≤ T)
    (f : ℝ → ℝ) (t : ℝ) (n : ℕ) :
    stoppedSum f T t n = partitionSum f (stoppedPoint T t n) n := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hit : EnergyRiemann.point T n i ≤ t
  · simp only [stoppedPoint, min_eq_right hit]
  · have ht : t ≤ EnergyRiemann.point T n i := le_of_not_ge hit
    have ht' := ht.trans (EnergyRiemann.point_mono hT n (Nat.le_succ i))
    simp only [stoppedPoint, min_eq_left ht, min_eq_left ht', sub_self, zero_mul]

theorem tendsto_stoppedSum {f : ℝ → ℝ} (hf : Continuous f)
    {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) :
    Tendsto (stoppedSum f T t) atTop (𝓝 (∫ x in (0 : ℝ)..min t T, f x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (T + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Icc (0 : ℝ) T) hf.continuousOn
  obtain ⟨δ, hδ, hδmod⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  have hwidth : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, T / (n : ℝ) < δ := hwidth.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 1)).exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hmesh, hnpos⟩ := hN n hn
  have hn' : 0 < n := hnpos
  have hmem (i : ℕ) (hi : i ≤ n) : stoppedPoint T t n i ∈ Icc (0 : ℝ) T := by
    constructor
    · rw [← stoppedPoint_zero T ht n]
      exact stoppedPoint_mono hT t n (Nat.zero_le i)
    · exact (stoppedPoint_mono hT t n hi).trans
        ((stoppedPoint_end T t hn').le.trans (min_le_right t T))
  have he := partition_error_le hf (stoppedPoint_mono hT t n) n (ε := η) ?_
  · rw [stoppedPoint_zero T ht, stoppedPoint_end T t hn',
      ← stoppedSum_eq_partitionSum hT] at he
    change |stoppedSum f T t n - ∫ x in (0 : ℝ)..min t T, f x| < ε
    calc
      _ ≤ η * (min t T - 0) := he
      _ ≤ η * T := by gcongr; simp
      _ < ε := by
        dsimp [η]
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ (by linarith : 0 < T + 1)).mpr
        nlinarith
  · intro i hi x hx
    have hleft := hmem i hi.le
    have hright := hmem (i + 1) (Nat.succ_le_of_lt hi)
    have hxT : x ∈ Icc (0 : ℝ) T := ⟨hleft.1.trans hx.1, hx.2.trans hright.2⟩
    have hdist : dist (stoppedPoint T t n i) x < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.1)]
      have hstep := stoppedPoint_step_le hT t n i
      linarith [hx.2]
    exact (hδmod _ hleft x hxT hdist).le

end Problem367.RandomRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_SelectedCompensator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.SelectedCompensator

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem coe_uniformGrid (T : ℝ≥0) (n i : ℕ) :
    (BrownianGrid.uniformGrid T n i : ℝ) = EnergyRiemann.point T n i := by
  simp only [BrownianGrid.uniformGrid, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_natCast, EnergyRiemann.point]
  ring

omit mΩ in
theorem squareSum_eq_stoppedSum (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    squareSum H T n t = fun ω => RandomRiemann.stoppedSum
      (fun s => (H s.toNNReal ω) ^ 2) T t n := by
  funext ω
  unfold squareSum RandomRiemann.stoppedSum RandomRiemann.stoppedPoint
  apply Finset.sum_congr rfl
  intro i hi
  simp only [← coe_uniformGrid, Real.toNNReal_coe]

omit mΩ in
theorem selected_eq_integral_of_continuous {H : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun s => H s ω)) (T t : ℝ≥0) :
    selected H T t ω = ∫ s in (0 : ℝ)..min (t : ℝ) T, (H s.toNNReal ω) ^ 2 := by
  apply Filter.Tendsto.limUnder_eq
  have hcR : Continuous (fun s : ℝ => (H s.toNNReal ω) ^ 2) := by fun_prop
  have h := RandomRiemann.tendsto_stoppedSum hcR T.coe_nonneg t.coe_nonneg
  simpa only [squareSum_eq_stoppedSum, Function.comp_apply, Pi.pow_apply] using h

end Problem367.SelectedCompensator

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NonnegativeSeriesL1
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.NonnegativeSeriesL1

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}

theorem integrable_tsum_of_nonnegative
    {f : ι → Ω → ℝ} (hf : ∀ i, Integrable (f i) μ)
    (hn : ∀ i ω, 0 ≤ f i ω) (hs : Summable (fun i => ∫ ω, f i ω ∂μ)) :
    (∀ᵐ ω ∂μ, Summable (fun i => f i ω)) ∧
      Integrable (fun ω => ∑' i, f i ω) μ ∧
      (∫ ω, ∑' i, f i ω ∂μ) = ∑' i, ∫ ω, f i ω ∂μ := by
  have hm (i : ι) : AEMeasurable (fun ω => ENNReal.ofReal (f i ω)) μ :=
    (hf i).aemeasurable.ennreal_ofReal
  have hfin : (∫⁻ ω, ∑' i, ENNReal.ofReal (f i ω) ∂μ) < ∞ := by
    rw [lintegral_tsum hm]
    calc
      (∑' i, ∫⁻ ω, ENNReal.ofReal (f i ω) ∂μ) =
          ∑' i, ENNReal.ofReal (∫ ω, f i ω ∂μ) := by
        apply tsum_congr
        intro i
        exact (ofReal_integral_eq_lintegral_ofReal (hf i)
          (Eventually.of_forall (hn i))).symm
      _ < ∞ := hs.tsum_ofReal_lt_top
  have hae : ∀ᵐ ω ∂μ, Summable (fun i => f i ω) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin.ne] with ω hω
    simpa only [ENNReal.toReal_ofReal (hn _ _)] using ENNReal.summable_toReal hω.ne
  have hint : Integrable (fun ω => ∑' i, f i ω) μ := by
    have h := integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hm) hfin.ne
    simpa only [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top),
      ENNReal.toReal_ofReal (hn _ _)] using h
  refine ⟨hae, hint, ?_⟩
  exact (integral_tsum_of_summable_integral_norm hf
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _ _)] using hs)).symm

end Problem367.NonnegativeSeriesL1

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_SpatialPrimitive
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

omit mΩ in
theorem nonnegativeCompensator_eq_integral_of_continuous
    {H : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (fun t => H t ω)) (t : ℝ≥0) :
    nonnegativeCompensator H t ω = ∫ s in (0 : ℝ)..(t : ℝ), (H s.toNNReal ω) ^ 2 := by
  unfold nonnegativeCompensator BrownianIntegralProcess.globalCompensator
  rw [SelectedCompensator.selected_eq_integral_of_continuous hc, min_self]
  exact max_eq_left (intervalIntegral.integral_nonneg t.coe_nonneg (fun s _ => sq_nonneg _))

theorem summable_integral_sq_of_integer
    {h : ι → ℝ≥0 → ℝ} (hc : ∀ a, Continuous (h a))
    (hs : ∀ N : ℕ, Summable (fun a => ∫ s in (0 : ℝ)..(N : ℝ), (h a s.toNNReal) ^ 2))
    (t : ℝ≥0) : Summable (fun a => ∫ s in (0 : ℝ)..(t : ℝ), (h a s.toNNReal) ^ 2) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (t : ℝ)
  apply Summable.of_nonneg_of_le
    (fun a => intervalIntegral.integral_nonneg t.coe_nonneg (fun s _ => sq_nonneg _))
    (fun a => ?_) (hs N)
  have hf : Continuous (fun s : ℝ => (h a s.toNNReal) ^ 2) := by fun_prop
  exact intervalIntegral.integral_mono_interval le_rfl t.coe_nonneg hN
    (Eventually.of_forall (fun s => sq_nonneg _)) (hf.intervalIntegrable _ _)

theorem integral_spatial_sq_tsum [Countable ι]
    {h : ι → ℝ≥0 → ℝ} (hc : ∀ a, Continuous (h a))
    (hs : ∀ N : ℕ, Summable (fun a => ∫ s in (0 : ℝ)..(N : ℝ), (h a s.toNNReal) ^ 2))
    (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => ∑' a, (h a s.toNNReal) ^ 2) volume 0 (t : ℝ) ∧
      (∫ s in (0 : ℝ)..(t : ℝ), ∑' a, (h a s.toNNReal) ^ 2) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), (h a s.toNNReal) ^ 2 := by
  have hi (a : ι) : Integrable (fun s : ℝ => (h a s.toNNReal) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) := by
    have hf : Continuous (fun s : ℝ => (h a s.toNNReal) ^ 2) := by fun_prop
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mp
      (hf.intervalIntegrable _ _)
  have hsum : Summable (fun a => ∫ s in Set.Ioc (0 : ℝ) (t : ℝ), (h a s.toNNReal) ^ 2) := by
    simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using
      summable_integral_sq_of_integer hc hs t
  obtain ⟨_, hint, heq⟩ := NonnegativeSeriesL1.integrable_tsum_of_nonnegative
    hi (fun a s => sq_nonneg _) hsum
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr hint,
    by simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using heq⟩

theorem ae_spatialCompensator_eq_primitive [Countable ι]
    {H : ι → ℝ≥0 → Ω → ℝ}
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hs : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Summable (fun a => nonnegativeCompensator (H a) (N : ℝ≥0) ω)) :
    ∀ᵐ ω ∂P,
      (∀ t, spatialCompensator H t ω = nnrealTimePrimitive (spatialSquareDensity H) t ω) ∧
      Continuous (fun t => nnrealTimePrimitive (spatialSquareDensity H) t ω) ∧
      (∀ t : ℝ≥0, IntervalIntegrable (fun s : ℝ => spatialSquareDensity H s.toNNReal ω)
        volume 0 (t : ℝ)) := by
  filter_upwards [ae_all_iff.mpr hc, ae_all_iff.mpr hs] with ω hcω hsω
  have hsum (N : ℕ) : Summable (fun a => ∫ s in (0 : ℝ)..(N : ℝ), (H a s.toNNReal ω) ^ 2) := by
    simpa only [nonnegativeCompensator_eq_integral_of_continuous (hcω _),
      NNReal.coe_natCast] using hsω N
  have hi (t : ℝ≥0) := integral_spatial_sq_tsum hcω hsum t
  refine ⟨?_, ?_, fun t => (hi t).1⟩
  · intro t
    change (∑' a, nonnegativeCompensator (H a) t ω) =
      ∫ s in (0 : ℝ)..(t : ℝ), ∑' a, (H a s.toNNReal ω) ^ 2
    rw [(hi t).2]
    exact tsum_congr (fun a => nonnegativeCompensator_eq_integral_of_continuous (hcω a) t)
  · exact continuous_nnreal_primitive_of_integrable_horizons _
      (fun N => by simpa only [NNReal.coe_natCast, spatialSquareDensity] using (hi (N : ℝ≥0)).1)

theorem spatialSquareDensity_isStronglyProgressive [Countable ι]
    {F : Filtration ℝ≥0 mΩ} {H : ι → ℝ≥0 → Ω → ℝ}
    (hH : ∀ a, IsStronglyProgressive F (H a)) :
    IsStronglyProgressive F (spatialSquareDensity H) := by
  intro t
  have hm (a : ι) := (hH a t).pow 2
  let : MeasurableSpace Ω := F t
  exact StronglyMeasurable.tsum hm

theorem compensatedSquare_spatial_primitive [Countable ι]
    {F : Filtration ℝ≥0 mΩ} {H : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hH : ∀ a, IsStronglyProgressive F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hs : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Summable (fun a => nonnegativeCompensator (H a) (N : ℝ≥0) ω))
    (hY : StronglyAdapted F Y)
    (hQ : Martingale (fun t ω => Y t ω ^ 2 - spatialCompensator H t ω) F P) :
    Martingale (fun t ω => Y t ω ^ 2 - nnrealTimePrimitive (spatialSquareDensity H) t ω) F P := by
  apply hQ.congr (fun t => ((hY t).pow 2).sub
    (stronglyAdapted_nnrealTimePrimitive (spatialSquareDensity_isStronglyProgressive hH) t))
  intro t
  filter_upwards [ae_spatialCompensator_eq_primitive hc hs] with ω hω
  change Y t ω ^ 2 - spatialCompensator H t ω =
    Y t ω ^ 2 - nnrealTimePrimitive (spatialSquareDensity H) t ω
  rw [hω.1 t]

end Problem367.BrownianArrayFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_GaussianVector
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace Problem367.ConditionalGaussianVector

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

section ArbitraryArray

variable {ι : Type*}

theorem infinite_product_gaussian_law_and_indep_of_condExp_linear_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → ι → ℝ} (hX : Measurable[mΩ] X)
    (v : ι → ℝ≥0)
    (hchar : ∀ (I : Finset ι) (a : I → ℝ),
      P[(fun ω => Complex.exp (((∑ i : I, a i * X ω i : ℝ) : ℂ) * Complex.I)) | m] =ᵐ[P]
        fun _ => Complex.exp (-((∑ i : I, (v i : ℝ) * (a i) ^ 2 : ℝ) : ℂ) / 2))
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    HasLaw X (Measure.infinitePi (fun i => gaussianReal 0 (v i))) P ∧
      iIndepFun (fun i ω => X ω i) P ∧ IndepFun X Y P := by
  classical
  have hfinite (I : Finset ι) :
      HasLaw (fun ω (i : I) => X ω i) (Measure.pi (fun i : I => gaussianReal 0 (v i))) P ∧
        IndepFun (fun ω (i : I) => X ω i) Y P :=
    product_gaussian_law_and_indep_of_condExp_linear_character hm
      (by fun_prop) (fun i : I => v i) (hchar I) hY
  have hcoordinate (i : ι) : HasLaw (fun ω => X ω i) (gaussianReal 0 (v i)) P := by
    let j : ({i} : Finset ι) := ⟨i, Finset.mem_singleton_self i⟩
    exact (measurePreserving_eval (fun k : ({i} : Finset ι) => gaussianReal 0 (v k)) j).fun_comp_hasLaw (hfinite {i}).1
  have hind : iIndepFun (fun i ω => X ω i) P := by
    apply iIndepFun_iff_finset.mpr
    intro I
    exact (iIndepFun_iff_hasLaw_pi_pi (fun i : I => hcoordinate i)).mpr (hfinite I).1
  refine ⟨hind.hasLaw_infinitePi hcoordinate hX.aemeasurable, hind, ?_⟩
  exact IndepFun.process_indepFun (fun i => (measurable_pi_apply i).comp hX)
    (hY.mono hm le_rfl) (fun I => (hfinite I).2)

end ArbitraryArray

end Problem367.ConditionalGaussianVector

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

theorem measurable_sampledLimit_at [MeasurableSpace Ω]
    {q : T → ℕ → T} {F : T → Ω → ℝ} (t : T)
    (hF : ∀ n, Measurable (F (q t n))) : Measurable (sampledLimit q F t) := by
  exact (StronglyMeasurable.limUnder (fun n => (hF n).stronglyMeasurable)).measurable

theorem ae_all_eq_of_continuous_modification [TopologicalSpace T] [MeasurableSpace Ω]
    {μ : Measure Ω} {q : T → ℕ → T} {F G : T → Ω → ℝ}
    {S : Set T} (hS : S.Countable)
    (hqS : ∀ t n, q t n ∈ S)
    (hq : ∀ t, Tendsto (q t) atTop (𝓝 t))
    (hFG : ∀ s ∈ S, F s =ᵐ[μ] G s)
    (hG : ∀ᵐ ω ∂μ, Continuous (fun t => G t ω)) :
    ∀ᵐ ω ∂μ, ∀ t, sampledLimit q F t ω = G t ω := by
  let : Countable S := hS.to_subtype
  have hEq : ∀ᵐ ω ∂μ, ∀ s : S, F s ω = G s ω :=
    ae_all_iff.mpr (fun s => hFG s s.property)
  filter_upwards [hEq, hG] with ω hEqω hGω
  intro t
  have hseq : (fun n => F (q t n) ω) = (fun n => G (q t n) ω) :=
    funext (fun n => hEqω ⟨q t n, hqS t n⟩)
  unfold sampledLimit
  rw [hseq]
  exact ((hGω.tendsto t).comp (hq t)).limUnder_eq

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FilteredFutureIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.FilteredFutureIndependence

variable {Ω A B C : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  {P : Measure Ω} [IsProbabilityMeasure P]

theorem indepFun_pair_right {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXY : IndepFun X Y P) (hXYZ : IndepFun (fun ω => (X ω, Y ω)) Z P) :
    IndepFun X (fun ω => (Y ω, Z ω)) P := by
  have hYZ : IndepFun Y Z P := hXYZ.comp measurable_snd measurable_id
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable
    (hY.prodMk hZ).aemeasurable]
  have h := congrArg (fun μ : Measure ((A × B) × C) =>
    μ.map MeasurableEquiv.prodAssoc)
    (hXYZ.map_prod_eq_prod_map_map (hX.prodMk hY).aemeasurable hZ.aemeasurable)
  rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable
    ((hX.prodMk hY).prodMk hZ),
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, Measure.prodAssoc_prod] at h
  rw [hYZ.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable]
  exact h

variable {T E : Type*} [LinearOrder T] [MeasurableSpace E]
  [AddCommGroup E] [MeasurableAdd₂ E] [MeasurableSub₂ E]
  {F : Filtration T mΩ} {X : T → Ω → E}

theorem indepFun_finite_future
    (hX : ∀ t, Measurable[F t] (X t))
    (hind : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (F s) P)
    (s : T) {Y : Ω → A} (hY : Measurable[F s] Y)
    (I : Finset (Set.Ici s)) :
    IndepFun Y (fun ω (t : I) => X t.val.val ω - X s ω) P := by
  classical
  have hXm (t : T) : Measurable (X t) := (hX t).mono (F.le t) le_rfl
  have hYm : Measurable Y := hY.mono (F.le s) le_rfl
  induction I using Finset.induction_on_max with
  | empty =>
      have heq : (fun ω (t : (∅ : Finset (Set.Ici s))) =>
          X t.val.val ω - X s ω) = (fun _ : Ω => fun _ :
            (∅ : Finset (Set.Ici s)) => (0 : E)) := by
        funext ω t
        exact False.elim (Finset.notMem_empty _ t.property)
      rw [heq]
      exact indepFun_const_right Y _
  | insert t I hlt ih =>
      rcases I.eq_empty_or_nonempty with rfl | hI
      · have hi : IndepFun Y (fun ω => X t.val ω - X s ω) P :=
          indep_of_indep_of_le_left (hind s t.val t.property).symm hY.comap_le
        have hcomp := hi.comp measurable_id
          (Measurable.of_eval (fun _ : ↥(insert t (∅ : Finset (Set.Ici s))) =>
            measurable_id))
        change IndepFun Y (fun ω (_ : ↥(insert t (∅ : Finset (Set.Ici s)))) =>
          X t.val ω - X s ω) P at hcomp
        convert hcomp using 1
        all_goals try with_reducible_and_instances rfl
        funext ω u
        have hu : u.val = t :=
          (Finset.mem_insert.mp u.property).resolve_right (Finset.notMem_empty _)
        simp only [hu]
      · let r : Set.Ici s := I.max' hI
        have hrI : r ∈ I := Finset.max'_mem I hI
        have hrt : r.val ≤ t.val := (hlt r hrI).le
        have hIr (u : I) : u.val.val ≤ r.val := I.le_max' u.val u.property
        let V : Ω → (I → E) := fun ω u => X u.val.val ω - X s ω
        let D : Ω → E := fun ω => X t.val ω - X r.val ω
        have hV : Measurable[F r.val] V := by
          let : MeasurableSpace Ω := F r.val
          exact Measurable.of_eval (fun index : I =>
            ((hX index.val.val).mono (F.mono (hIr index)) le_rfl).sub
              ((hX s).mono (F.mono r.property) le_rfl))
        have hYV : Measurable[F r.val] (fun ω => (Y ω, V ω)) :=
          (hY.mono (F.mono r.property) le_rfl).prodMk hV
        have hYVD : IndepFun (fun ω => (Y ω, V ω)) D P :=
          indep_of_indep_of_le_left (hind r.val t.val hrt).symm hYV.comap_le
        have hvd := indepFun_pair_right hYm (hV.mono (F.le r.val) le_rfl)
          ((hXm t.val).sub (hXm r.val)) ih hYVD
        let assemble : (I → E) × E → (↥(insert t I) → E) := fun q u =>
          if h : u.val = t then q.1 ⟨r, hrI⟩ + q.2
          else q.1 ⟨u.val, (Finset.mem_insert.mp u.property).resolve_left h⟩
        have ha : Measurable assemble := by
          apply Measurable.of_eval
          intro u
          dsimp [assemble]
          split_ifs
          · exact ((measurable_pi_apply _).comp measurable_fst).add measurable_snd
          · exact (measurable_pi_apply _).comp measurable_fst
        have hh := hvd.comp measurable_id ha
        change IndepFun Y (fun ω => assemble (V ω, D ω)) P at hh
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        funext ω u
        dsimp [assemble, V, D]
        split_ifs with hu
        · rw [hu]
          abel
        · rfl

theorem indepFun_future
    (hX : ∀ t, Measurable[F t] (X t))
    (hind : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (F s) P)
    (s : T) {Y : Ω → A} (hY : Measurable[F s] Y) :
    IndepFun Y (fun ω (t : Set.Ici s) => X t.val ω - X s ω) P := by
  exact IndepFun.indepFun_process (P := P)
    (Y := fun (t : Set.Ici s) ω => X t.val ω - X s ω)
    (hY.mono (F.le s) le_rfl)
    (fun (t : Set.Ici s) => ((hX t.val).mono (F.le t.val) le_rfl).sub
      ((hX s).mono (F.le s) le_rfl))
    (indepFun_finite_future hX hind s hY)

theorem indep_future
    (hX : ∀ t, Measurable[F t] (X t))
    (hind : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (F s) P)
    (s : T) :
    Indep (F s) (MeasurableSpace.comap
      (fun ω (t : Set.Ici s) => X t.val ω - X s ω) inferInstance) P := by
  let : MeasurableSpace Ω := F s
  have h := indepFun_future (mΩ := mΩ) hX hind s (Y := id)
    (show Measurable[F s, F s] (id : Ω → Ω) from measurable_id)
  change Indep ((F s).comap id) _ P at h
  simpa only [MeasurableSpace.comap_id] using h

end Problem367.FilteredFutureIndependence

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

attribute [local instance] OAI.Problem367.ProgressiveVersionPushforward.instMeasurableSpaceContinuousMapNNRealReal_solutions
local instance instBorelSpaceContinuousMapNNRealReal_solutions : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma leftTime_le (t : ℝ≥0) (n : ℕ) : leftTime t n ≤ t := by
  simpa only [leftTime, Real.toNNReal_coe] using Real.toNNReal_mono (dyadicLeft_le t n)

lemma tendsto_leftTime (t : ℝ≥0) : Tendsto (leftTime t) atTop (𝓝 t) := by
  change Tendsto (fun n => (dyadicLeft (t : ℝ) n).toNNReal) atTop (𝓝 t)
  simpa only [ Function.comp_def, Real.toNNReal_coe] using
    continuous_real_toNNReal.continuousAt.tendsto.comp (tendsto_dyadicLeft (t : ℝ))

lemma leftTime_mem_range (t : ℝ≥0) (n : ℕ) : leftTime t n ∈ range gridTime :=
  ⟨(⌊(2 : ℝ)^n * (t : ℝ)⌋, n), rfl⟩

lemma denseRange_gridTime : DenseRange gridTime := by
  intro t
  exact mem_closure_of_tendsto (tendsto_leftTime t)
    (Eventually.of_forall (leftTime_mem_range t))

lemma measurable_leftTime (n : ℕ) : Measurable (fun t => leftTime t n) := by
  unfold leftTime dyadicLeft
  fun_prop

lemma measurable_version {Ω : Type*} [MeasurableSpace Ω]
    {M : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (M t)) (t : ℝ≥0) :
    Measurable (version M t) :=
  measurable_sampledLimit_at t (fun n => hm (leftTime t n))

lemma progressive_version {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : IsStronglyProgressive F M) : IsStronglyProgressive F (version M) := by
  apply isStronglyProgressive_sampledLimit F
  intro n
  apply hM.comp _ (fun t _ => leftTime_le t n)
  intro T
  exact ((measurable_leftTime n).comp measurable_fst.subtype_val).stronglyMeasurable

lemma version_eq_of_grid {Ω : Type*} {M : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (f : C(ℝ≥0, ℝ)) (h : ∀ p, M (gridTime p) ω = f (gridTime p)) :
    ∀ t, version M t ω = f t := by
  intro t
  have he : (fun n => M (leftTime t n) ω) = fun n => f (leftTime t n) := by
    funext n
    exact h (⌊(2 : ℝ)^n * (t : ℝ)⌋, n)
  unfold version sampledLimit
  rw [he]
  exact ((f.continuous.tendsto t).comp (tendsto_leftTime t)).limUnder_eq

lemma ae_all_version_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {M G : ℝ≥0 → Ω → ℝ} (he : ∀ t, M t =ᵐ[μ] G t)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => G t ω)) :
    ∀ᵐ ω ∂μ, ∀ t, version M t ω = G t ω := by
  apply ae_all_eq_of_continuous_modification (Set.countable_range gridTime)
    leftTime_mem_range tendsto_leftTime (fun t _ => he t) hc

lemma measurableEmbedding_gridEval : MeasurableEmbedding
    (fun f : C(ℝ≥0, ℝ) => fun p : ℤ × ℕ => f (gridTime p)) := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval (fun _ => (continuous_eval_const _).measurable)
  · intro f g h
    apply ContinuousMap.coe_injective
    exact denseRange_gridTime.equalizer f.continuous g.continuous h

theorem continuous_progressive_version_of_pullback
    {Ω Ξ : Type*} [MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    {μ : Measure Ω} {φ : Ω → Ξ} (hφ : Measurable φ)
    {F : Filtration ℝ≥0 mΞ} {M : ℝ≥0 → Ξ → ℝ}
    (hM : IsStronglyProgressive F M)
    {G : ℝ≥0 → Ω → ℝ}
    (hcG : ∀ᵐ ω ∂μ, Continuous (fun t => G t ω))
    (heG : ∀ t, G t =ᵐ[μ] fun ω => M t (φ ω)) :
    IsStronglyProgressive F (version M) ∧
      (∀ᵐ x ∂μ.map φ, Continuous (fun t => version M t x)) ∧
      (∀ t, version M t =ᵐ[μ.map φ] M t) := by
  have hm (t : ℝ≥0) : Measurable (M t) :=
    ((hM.stronglyAdapted t).mono (F.le t)).measurable
  let samples : Ξ → (ℤ × ℕ → ℝ) := fun x p => M (gridTime p) x
  let encode : C(ℝ≥0, ℝ) → (ℤ × ℕ → ℝ) := fun f p => f (gridTime p)
  have hms : Measurable samples := Measurable.of_eval (fun point => hm (gridTime point))
  have hgoodSet : MeasurableSet {x : Ξ | samples x ∈ range encode} :=
    measurableEmbedding_gridEval.measurableSet_range.preimage hms
  have hgoodPullback : ∀ᵐ ω ∂μ, samples (φ ω) ∈ range encode := by
    have heGrid : ∀ᵐ ω ∂μ, ∀ p : ℤ × ℕ, G (gridTime p) ω = M (gridTime p) (φ ω) :=
      ae_all_iff.mpr (fun p => heG (gridTime p))
    filter_upwards [hcG, heGrid] with ω hc he
    exact ⟨⟨fun t => G t ω, hc⟩, funext he⟩
  have hgood : ∀ᵐ x ∂μ.map φ, samples x ∈ range encode :=
    (ae_map_iff hφ.aemeasurable hgoodSet).mpr hgoodPullback
  have hid : ∀ᵐ ω ∂μ, ∀ t, version M t (φ ω) = G t ω :=
    ae_all_version_eq (fun t => (heG t).symm) hcG
  refine ⟨progressive_version hM, ?_, ?_⟩
  · filter_upwards [hgood] with x hx
    obtain ⟨f, hf⟩ := hx
    have he := version_eq_of_grid f (fun p => (congrFun hf p).symm)
    simpa only [he] using f.continuous
  · intro t
    apply (ae_map_iff hφ.aemeasurable
      (measurableSet_eq_fun (measurable_version hm t) (hm t))).mpr
    filter_upwards [hid, heG t] with ω hi he
    exact (hi t).trans he

end Problem367.ProgressiveVersionPushforward

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ProgressiveIsingPosterior
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

attribute [local instance] OAI.Problem367.progressiveIsingPosteriorNonemptyIsingSpin
theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_field_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      let y := fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
      infiniteGibbsSpinMean beta v y ∈ Set.Ioo (-1 : ℝ) 1 ∧
        |Real.artanh (infiniteGibbsSpinMean beta v y) - y v| ≤ (d : ℝ) * beta := by
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB t v,
    hμ.brownian_past_posterior_field_bound hbeta ν hB hmB t v] with p heq hb
  dsimp only
  rw [heq]
  exact hb

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_InteriorLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal Topology

namespace Problem367.PosteriorInteriorLocalization

theorem field_bound_iff_tanh_bounds {m X K : ℝ} :
    (m ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh m - X| ≤ K) ↔
      (Real.tanh (X - K) ≤ m ∧ m ≤ Real.tanh (X + K)) := by
  constructor
  · rintro ⟨hm, hb⟩
    constructor
    · apply (Real.artanh_le_artanh_iff
        ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩ hm).mp
      rw [Real.artanh_tanh]
      linarith [(abs_le.mp hb).1]
    · apply (Real.artanh_le_artanh_iff hm
        ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).mp
      rw [Real.artanh_tanh]
      linarith [(abs_le.mp hb).2]
  · intro hb
    have h := posterior_field_limit_of_tanh_bounds
      (u := fun _ : ℕ => m) tendsto_const_nhds (fun _ => hb)
    exact ⟨h.1, h.2.1⟩

private theorem continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_tanh_response t).continuousAt

theorem ae_all_field_bound_of_continuous
    {T Ω : Type*} [TopologicalSpace T] [SeparableSpace T]
    [MeasurableSpace Ω] {P : Measure Ω} {M X : T → Ω → ℝ} {K : ℝ}
    (hM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hb : ∀ t, ∀ᵐ ω ∂P,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K) :
    ∀ᵐ ω ∂P, ∀ t,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense T
  let : Countable S := hSc.to_subtype
  have hS : ∀ᵐ ω ∂P, ∀ t : S,
      M t ω ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K :=
    ae_all_iff.mpr (fun t => hb t)
  filter_upwards [hM, hX, hS] with ω hMω hXω hSω
  have hall : ∀ t, Real.tanh (X t ω - K) ≤ M t ω ∧
      M t ω ≤ Real.tanh (X t ω + K) := by
    refine isClosed_property hSd.denseRange_val
      (p := fun t => Real.tanh (X t ω - K) ≤ M t ω ∧
        M t ω ≤ Real.tanh (X t ω + K)) ?_ ?_
    · exact (isClosed_le (continuous_tanh.comp (hXω.sub continuous_const)) hMω).inter
        (isClosed_le hMω (continuous_tanh.comp (hXω.add continuous_const)))
    · intro t
      exact field_bound_iff_tanh_bounds.mp (hSω t)
  exact fun t => field_bound_iff_tanh_bounds.mpr (hall t)

theorem continuous_artanh_of_interior
    {T : Type*} [TopologicalSpace T] {m : T → ℝ}
    (hm : Continuous m) (hi : ∀ t, m t ∈ Set.Ioo (-1 : ℝ) 1) :
    Continuous (fun t => Real.artanh (m t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_artanh_interval (hi t)).continuousAt.comp (hm.continuousAt)

end Problem367.PosteriorInteriorLocalization

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_InnovationIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.innovationPath_apply _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]
  {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
  (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
  (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
  (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))

private theorem spin_bound (v : TreeVertex d) :
    ∀ᵐ sigma ∂μ, |ArrayPosteriorStationarity.spinArray sigma v| ≤ (1 : ℝ≥0) := by
  apply Filter.Eventually.of_forall
  intro sigma
  cases hs : sigma v <;> norm_num [ArrayPosteriorStationarity.spinArray, spinSign, hs]

include hμ hB hcB

theorem innovation_martingale (v : TreeVertex d) :
    Martingale (innovation beta B v) (ArrayPosteriorStationarity.filtration B hmB)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  exact preBrownian_array_innovation_martingale_of_progressive_posterior
    μ (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB)
    ArrayPosteriorStationarity.measurable_spinArray v (spin_bound v)
    (posterior_progressive beta B hmB hcB v)
    (fun t => posterior_eq_condExp hμ ν hB hmB t v)

theorem innovation_increment_law_and_indep
    {E : Type*} [mE : MeasurableSpace E] {Y : State d A → E}
    (s t : ℝ≥0) (hst : s ≤ t)
    (hY : Measurable[ArrayPosteriorStationarity.filtration B hmB s] Y) :
    HasLaw (fun q v => innovation beta B v t q - innovation beta B v s q)
      (Measure.infinitePi (fun _ : TreeVertex d => gaussianReal 0 (t - s)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) ∧
    iIndepFun (fun v q => innovation beta B v t q - innovation beta B v s q)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) ∧
    IndepFun (fun q v => innovation beta B v t q - innovation beta B v s q) Y
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  apply ConditionalGaussianVector.infinite_product_gaussian_law_and_indep_of_condExp_linear_character
    (ArrayPosteriorStationarity.filtration B hmB |>.le s) _
    (fun _ : TreeVertex d => t - s) _ hY
  · apply Measurable.of_eval
    intro v
    exact ((innovation_martingale hμ ν hB hmB hcB v).stronglyMeasurable t).measurable.mono
      (ArrayPosteriorStationarity.filtration B hmB |>.le t) le_rfl |>.sub
        (((innovation_martingale hμ ν hB hmB hcB v).stronglyMeasurable s).measurable.mono
          (ArrayPosteriorStationarity.filtration B hmB |>.le s) le_rfl)
  · intro I a
    have h := ArrayInnovationLaw.conditional_weighted_character μ
      (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray (fun v => spin_bound v)
      (posterior_progressive beta B hmB hcB)
      (fun v t => posterior_eq_condExp hμ ν hB hmB t v) I s t hst a
    have heq : ConditionalCharacteristic.character
        (fun q => ∑ i : I, a i * (innovation beta B i.1 t q - innovation beta B i.1 s q)) 1 =
        (fun q => Complex.exp (((∑ i : I, a i *
          (innovation beta B i.1 t q - innovation beta B i.1 s q) : ℝ) : ℂ) * Complex.I)) := by
      funext q
      simp [ConditionalCharacteristic.character]
    change (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))[
      ConditionalCharacteristic.character
        (fun q => ∑ i : I, a i * (innovation beta B i.1 t q - innovation beta B i.1 s q)) 1 |
        ArrayPosteriorStationarity.filtration B hmB s] =ᵐ[_] _ at h
    rw [heq] at h
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow] using h

theorem innovation_increment_indep_filtration (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun q v => innovation beta B v t q - innovation beta B v s q) inferInstance)
      (ArrayPosteriorStationarity.filtration B hmB s)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have h := (innovation_increment_law_and_indep hμ ν hB hmB hcB
    (mE := ArrayPosteriorStationarity.filtration B hmB s)
    (Y := id) s t hst measurable_id).2.2
  change Indep _ ((ArrayPosteriorStationarity.filtration B hmB s).comap id) _ at h
  simpa only [MeasurableSpace.comap_id] using h

theorem innovation_future_indep_filtration (s : ℝ≥0) :
    Indep (ArrayPosteriorStationarity.filtration B hmB s)
      (MeasurableSpace.comap
        (fun q (t : Set.Ici s) v => innovation beta B v t.val q - innovation beta B v s q)
        inferInstance)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  apply FilteredFutureIndependence.indep_future
    (X := fun t q v => innovation beta B v t q)
  · intro t
    let : MeasurableSpace (State d A) := ArrayPosteriorStationarity.filtration B hmB t
    exact Measurable.of_eval (fun v =>
      (innovation_martingale hμ ν hB hmB hcB v).stronglyAdapted.adapted t)
  · exact innovation_increment_indep_filtration hμ ν hB hmB hcB

omit hB hmB hcB ν in

theorem uniformInnovation_future_indep_filtration (s : ℝ≥0) :
    Indep (uniformObservationFiltration d s)
      (MeasurableSpace.comap
        (fun q (t : Set.Ici s) v => uniformInnovation beta q v t.val -
          uniformInnovation beta q v s) inferInstance)
      (μ.prod (labelMeasure d)) := by
  exact innovation_future_indep_filtration hμ uniform01
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
    (fun t => WienerSampler.measurable_sample_eval.comp
      (measurable_const.prodMk measurable_id))
    (fun u => (WienerSampler.sample u).continuous) s

end Problem367.IsingInnovation

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

section Copies

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable {rho : Measure (Paths d)} [IsProbabilityMeasure rho]
variable {eta : Kernel (Paths d) (Paths d)} [IsMarkovKernel eta]

theorem ae_innovationMap_copies (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta),
      innovationMap beta q.2.1 = q.1 ∧ innovationMap beta q.2.2 = q.1 := by
  have hgraph : ∀ᵐ q : Paths d × Paths d ∂rho ⊗ₘ eta,
      innovationMap beta q.2 = q.1 := by
    rw [hjoint, graphLaw]
    apply (ae_map_iff
      ((measurable_innovationMap beta).prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun
        ((measurable_innovationMap beta).comp measurable_snd) measurable_fst)).mpr
    exact Filter.Eventually.of_forall (fun _ => rfl)
  have hleft := (measurePreserving_conditionalCopy_fst rho eta).quasiMeasurePreserving.ae hgraph
  have hright := (measurePreserving_conditionalCopy_snd rho eta).quasiMeasurePreserving.ae hgraph
  filter_upwards [hleft, hright] with q hl hr
  exact ⟨hl, hr⟩

end Copies

end Problem367.IsingConditionalCopyBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

theorem filtration_eq_comap_past (d : ℕ) (t : ℝ≥0) :
    filtration d t = MeasurableSpace.comap (past t) inferInstance :=
  arrayNaturalFiltration_eq_comap evaluation measurable_evaluation t

theorem filtration_comap_uniformObservation (d : ℕ) (t : ℝ≥0)
    (hm : ∀ s, Measurable (fun u => WienerSampler.sample u s)) :
    (filtration d t).comap uniformObservation =
      ArrayPosteriorStationarity.filtration
        (fun s u => WienerSampler.sample u s) hm t := by
  rw [filtration_eq_comap_past, MeasurableSpace.comap_comp]
  unfold ArrayPosteriorStationarity.filtration arrayObservationFiltration
  rw [arrayNaturalFiltration_eq_comap]
  rfl

end Problem367.IsingObservationInnovation

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

theorem HasFreeIsingLaw.continuous_posterior_all_time_field_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ v, IsBrownianReal (B v) (ν v))
    (hmB : ∀ v t, Measurable (B v t))
    {m : TreeVertex d → ℝ≥0 →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ}
    (hcm : ∀ v, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), Continuous (fun t => m v t p))
    (hversion : ∀ v t, m v t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (fun p => infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ v,
      (∀ t, m v t p ∈ Set.Ioo (-1 : ℝ) 1 ∧
        |Real.artanh (m v t p) - ((t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))| ≤
          (d : ℝ) * beta) ∧
      Continuous (fun t => Real.artanh (m v t p)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  apply ae_all_iff.mpr
  intro v
  have hX : ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Continuous (fun t : ℝ≥0 => (t : ℝ) * spinSign (p.1 v) + B v t (p.2 v)) := by
    have hnoise := (planted_noise_coordinate_measurePreserving μ ν v).quasiMeasurePreserving.ae
      (hB v).cont
    filter_upwards [hnoise] with p hp
    exact (continuous_subtype_val.mul continuous_const).add hp
  have hb : ∀ t, ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      m v t p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (m v t p) - ((t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))| ≤
        (d : ℝ) * beta := by
    intro t
    filter_upwards [hversion v t,
      hμ.infiniteGibbsSpinMean_brownian_field_bound hbeta ν
        (fun i => (hB i).toIsPreBrownianReal) hmB t v] with p hp hb
    rw [hp]
    exact hb
  filter_upwards [hcm v,
    PosteriorInteriorLocalization.ae_all_field_bound_of_continuous (hcm v) hX hb]
      with p hp hb
  exact ⟨hb, PosteriorInteriorLocalization.continuous_artanh_of_interior hp
    (fun t => (hb t).1)⟩

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalContinuousFields
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

lemma field_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (field beta v) :=
  isStronglyProgressive_artanh (filtration d) (posterior_progressive beta v)

lemma continuousField_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousField beta v) :=
  ProgressiveVersionPushforward.progressive_version (field_progressive beta v)

theorem continuousField_modification
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    (∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousField beta v t x)) ∧
      (∀ t, continuousField beta v t =ᵐ[observationLaw μ] field beta v t) := by
  let B : ℝ≥0 → ℝ → ℝ := fun t u => WienerSampler.sample u t
  have hmB (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample
  have hcB (u : ℝ) : Continuous (fun t => B t u) := (WienerSampler.sample u).continuous
  obtain ⟨Z, hZ⟩ := Classical.axiomOfChoice
    (fun w : TreeVertex d => IsingInnovation.exists_continuous_posterior
      hd hμ hb hcrit uniform01 WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
      hmB hcB w)
  have hcont (w : TreeVertex d) : ∀ᵐ q ∂μ.prod (labelMeasure d),
      Continuous (fun t => Z w t q) := (hZ w).2.2.1
  have hver (w : TreeVertex d) (t : ℝ≥0) : Z w t =ᵐ[μ.prod (labelMeasure d)]
      (fun q => infiniteGibbsSpinMean beta w
        (fun i => (t : ℝ) * spinSign (q.1 i) + B t (q.2 i))) := by
    filter_upwards [(hZ w).2.2.2.2.2 t] with q hq
    refine hq.trans ?_
    change infiniteGibbsSpinMean beta w
      (fun i => B t (q.2 i) + (t : ℝ) * spinSign (q.1 i)) = _
    apply congrArg (infiniteGibbsSpinMean beta w)
    funext i
    exact add_comm _ _
  have hfields := hμ.continuous_posterior_all_time_field_bound hb
    (fun _ : TreeVertex d => uniform01) (fun _ => WienerSampler.sample_isBrownianReal)
    (fun _ => hmB) hcont hver
  have hc : ∀ᵐ q ∂μ.prod (labelMeasure d),
      Continuous (fun t => Real.artanh (Z v t q)) :=
    hfields.mono (fun q hq => (hq v).2)
  have he (t : ℝ≥0) : (fun q => Real.artanh (Z v t q)) =ᵐ[μ.prod (labelMeasure d)]
      (fun q => field beta v t (uniformObservation q)) := by
    filter_upwards [hver v t] with q hq
    change Real.artanh (Z v t q) = Real.artanh
      (infiniteGibbsSpinMean beta v
        (fun i => B t (q.2 i) + (t : ℝ) * spinSign (q.1 i)))
    apply congrArg Real.artanh
    refine hq.trans ?_
    apply congrArg (infiniteGibbsSpinMean beta v)
    funext i
    exact add_comm _ _
  exact (ProgressiveVersionPushforward.continuous_progressive_version_of_pullback
    measurable_uniformObservation (field_progressive beta v) hc he).2

end Problem367.IsingObservationFactor

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

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousRootResponse
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply
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

lemma siteRootResponse_mem_Icc (hb : 0 ≤ beta) (v : TreeVertex d)
    (H : TreeVertex d → ℝ) :
    0 ≤ siteRootResponse hb v H ∧ siteRootResponse hb v H ≤ 1 := by
  have hp0 : 0 ≤ ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
      (CavityArray.field (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta)
        H (ConnectedHull.takeVertex v (i + 1)) (ConnectedHull.takeVertex v i)) :=
    Finset.prod_nonneg fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le
  have hp1 : (∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
      (CavityArray.field (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta)
        H (ConnectedHull.takeVertex v (i + 1)) (ConnectedHull.takeVertex v i))) ≤ 1 :=
    Finset.prod_le_one
      (fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le)
      (fun i _ => responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le _)
  have ht0 := pow_nonneg (tanh_nonneg_of_beta_nonneg hb) v.1.length
  have ht1 : Real.tanh beta ^ v.1.length ≤ 1 :=
    pow_le_one₀ (tanh_nonneg_of_beta_nonneg hb) (Real.tanh_lt_one beta).le
  exact ⟨mul_nonneg ht0 hp0, (mul_le_mul ht1 hp1 hp0 (by norm_num)).trans_eq (one_mul 1)⟩

lemma continuousRootResponse_progressive (hb : 0 ≤ beta) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousRootResponse hb v) := by
  intro t
  let : MeasurableSpace (Paths d) := filtration d t
  exact ((continuous_siteRootResponse hb v).measurable.comp
    (Measurable.of_eval (fun i => (continuousField_progressive beta i t).measurable))).stronglyMeasurable

lemma continuousRootResponse_abs_le_one (hb : 0 ≤ beta) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : |continuousRootResponse hb v t x| ≤ 1 := by
  obtain ⟨h0, h1⟩ := siteRootResponse_mem_Icc hb v (fun i => continuousField beta i t x)
  exact (abs_of_nonneg h0).trans_le h1

theorem continuousRootResponse_continuous_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    ∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousRootResponse hb v t x) := by
  have hc (i : TreeVertex d) := (continuousField_modification hd hμ hb hcrit i).1
  filter_upwards [ae_all_iff.mpr hc] with x hx
  exact (continuous_siteRootResponse hb v).comp (continuous_pi hx)

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedIntegralAssociativity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedIntegralAssociativity

open BrownianGrid BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stoppedUniformSum_memLp [IsFiniteMeasure P]
    {M K : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hM2 : ∀ t, MemLp (M t) 2 P) (hK : StronglyAdapted F K)
    {D : ℝ} (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    MemLp (stoppedUniformSum M K T n t) 2 P := by
  apply memLp_finsetSum
  intro i hi
  exact BrownianGrid.memLp_compose_of_bounded
    ((hM2 (min t (uniformGrid T n (i + 1)))).sub (hM2 (min t (uniformGrid T n i))))
    ((hK _).mono (F.le _)).aestronglyMeasurable (hbK.mono (fun ω hω => hω _))

end Problem367.StoppedIntegralAssociativity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

private theorem indep_map_of_comap {Ω E : Type*}
    [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    {P : Measure Ω} {f : Ω → E} (hf : Measurable f)
    {m n : MeasurableSpace E} (hm : m ≤ mE) (hn : n ≤ mE)
    (h : Indep (m.comap f) (n.comap f) P) :
    Indep m n (@Measure.map Ω E mΩ mE f P) := by
  rw [Indep_iff]
  intro A B hA hB
  rw [Measure.map_apply (μ := P) hf ((hm A hA).inter (hn B hB)),
    Measure.map_apply (μ := P) hf (hm A hA), Measure.map_apply (μ := P) hf (hn B hB)]
  exact (Indep_iff _ _ _).mp h _ _
    ((comap_measurable (m := m) f) hA) ((comap_measurable (m := n) f) hB)

theorem measurable_futureInnovation {d : ℕ} (beta : ℝ) (s : ℝ≥0) :
    Measurable (futureInnovation (d := d) beta s) := by
  apply Measurable.of_eval
  intro t
  apply Measurable.of_eval
  intro v
  exact ((measurable_evaluation v t.val).comp (measurable_innovationMap beta)).sub
    ((measurable_evaluation v s).comp (measurable_innovationMap beta))

theorem innovationMap_stronglyAdapted {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    StronglyAdapted (filtration d) (fun t x => innovationMap beta x v t) := by
  exact (arrayNaturalFiltration_stronglyAdapted evaluation measurable_evaluation v).sub
    (stronglyAdapted_nnrealTimePrimitive (posterior_progressive beta v))

theorem innovationMap_isBrownianReal {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    IsBrownianReal (fun t x => innovationMap beta x v t) (observationLaw μ) := by
  have hpath : HasLaw (fun x => innovationMap beta x v)
      WienerSampler.wienerMeasure (observationLaw μ) := by
    refine ⟨((measurable_pi_apply v).comp (measurable_innovationMap beta)).aemeasurable, ?_⟩
    rw [show (fun x => innovationMap beta x v) =
      (fun y : Paths d => y v) ∘ innovationMap beta from rfl,
      ← Measure.map_map (measurable_pi_apply v) (measurable_innovationMap beta),
      map_innovationMap_observationLaw hμ, Measure.infinitePi_map_eval]
  exact { hasLaw := fun I => (WienerSampler.coordinate_isBrownianReal.hasLaw I).comp hpath
          cont := Filter.Eventually.of_forall (fun x => (innovationMap beta x v).continuous) }

theorem innovationMap_future_indep_filtration {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (s : ℝ≥0) :
    Indep (filtration d s)
      (MeasurableSpace.comap (futureInnovation beta s) inferInstance)
      (observationLaw μ) := by
  change Indep _ _ ((μ.prod (labelMeasure d)).map (uniformObservation (d := d)))
  refine indep_map_of_comap (P := μ.prod (labelMeasure d))
    (f := uniformObservation) measurable_uniformObservation (filtration d |>.le s)
    (measurable_futureInnovation beta s).comap_le ?_
  have h := IsingInnovation.uniformInnovation_future_indep_filtration hμ s
  rw [MeasurableSpace.comap_comp]
  rw [filtration_comap_uniformObservation d s
    (fun t => WienerSampler.measurable_sample_eval.comp
      (measurable_const.prodMk measurable_id))]
  exact h

theorem innovationMap_increment_indep_filtration {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun x v => innovationMap beta x v t - innovationMap beta x v s) inferInstance)
      (filtration d s) (observationLaw μ) := by
  apply (indep_of_indep_of_le_right (innovationMap_future_indep_filtration hμ s) ?_).symm
  exact ((measurable_pi_apply (⟨t, hst⟩ : Set.Ici s)).comp
    (comap_measurable (futureInnovation beta s))).comap_le

end Problem367.IsingObservationInnovation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalResponseIntegrals
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationInnovation

theorem innovationMap_increments_indep
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (s t : ℝ≥0)
    {v w : TreeVertex d} (hvw : v ≠ w) :
    IndepFun (fun x : Paths d => innovationMap beta x v t - innovationMap beta x v s)
      (fun x => innovationMap beta x w t - innovationMap beta x w s)
      (observationLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hp : MeasurePreserving (innovationMap beta) (observationLaw μ)
      (Measure.infinitePi (fun _ : TreeVertex d => WienerSampler.wienerMeasure)) :=
    ⟨measurable_innovationMap beta, map_innovationMap_observationLaw hμ⟩
  apply indepFun_comp_measurePreserving hp
    ((measurable_evaluation v t).sub (measurable_evaluation v s))
    ((measurable_evaluation w t).sub (measurable_evaluation w s))
  exact (iIndepFun_infinitePi (P := fun _ : TreeVertex d => WienerSampler.wienerMeasure)
    (fun _ => (continuous_eval_const t).measurable.sub
      (continuous_eval_const s).measurable)).indepFun hvw

end Problem367.IsingObservationInnovation

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation BrownianArrayFiltration

theorem exists_canonical_root_response_integrals
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    ∃ (I : TreeVertex d → ℝ≥0 → Paths d → ℝ) (Y : ℝ≥0 → Paths d → ℝ)
      (hI2 : ∀ a t, MemLp (I a t) 2 (observationLaw μ))
      (hY2 : ∀ t, MemLp (Y t) 2 (observationLaw μ)),
      (∀ a, IsStronglyPredictable (filtration d) (I a) ∧
        Martingale (I a) (filtration d) (observationLaw μ) ∧
        (∀ᵐ x ∂observationLaw μ, Continuous (fun t => I a t x))) ∧
      (∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ x,
          (BrownianIntegralProcess.stoppedUniformSum
            (fun s x => innovationMap beta x a s) (continuousRootResponse hb a)
            N n t x - I a t x) ^ 2 ∂observationLaw μ) atTop (𝓝 0)) ∧
      IsStronglyPredictable (filtration d) Y ∧
      Martingale Y (filtration d) (observationLaw μ) ∧
      (∀ᵐ x ∂observationLaw μ, Continuous (fun t => Y t x)) ∧
      Y 0 =ᵐ[observationLaw μ] 0 ∧
      (∀ t, (∫ x, Y t x ^ 2 ∂observationLaw μ) =
        ∑' a, ∫ s in (0 : ℝ)..(t : ℝ), ∫ x,
          continuousRootResponse hb a s.toNNReal x ^ 2 ∂observationLaw μ) ∧
      (∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t))) ∧
      (∀ T : ℝ≥0, Tendsto (fun q : Finset (TreeVertex d) =>
        ∫ x, MartingaleStrongMaximal.maximalSquare
          (MartingaleSpatialLimit.finiteSum I q - Y) T x ∂observationLaw μ)
          atTop (𝓝 0)) ∧
      Martingale (fun t x => Y t x ^ 2 -
        nnrealTimePrimitive (spatialSquareDensity (continuousRootResponse hb)) t x)
        (filtration d) (observationLaw μ) ∧
      (∀ t, Integrable
        (nnrealTimePrimitive (spatialSquareDensity (continuousRootResponse hb)) t)
        (observationLaw μ)) ∧
      (∀ᵐ x ∂observationLaw μ, Continuous (fun t =>
        nnrealTimePrimitive (spatialSquareDensity (continuousRootResponse hb)) t x)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hc (a : TreeVertex d) := continuousRootResponse_continuous_ae hd hμ hb hcrit a
  have henergy (N : ℕ) : Summable (fun a =>
      ∫ s in (0 : ℝ)..(N : ℝ), ∫ x,
        continuousRootResponse hb a s.toNNReal x ^ 2 ∂observationLaw μ) := by
    simpa only [NNReal.coe_natCast] using
      (continuousRootResponse_hasSum_timeEnergy hd hμ hb hcrit (N : ℝ≥0)).summable
  obtain ⟨I, Y, hI2, hY2, hI, hIlim, hYp, hYM, hYc, hY0,
      hYiso, hYsum, hYmax, hQ, hAint, hAsum⟩ :=
    exists_global_continuous_spatial_integral_compensatedSquare
      (B := fun a s x => innovationMap beta x a s)
      (F := filtration d) (H := continuousRootResponse hb)
      (fun a => (innovationMap_isBrownianReal hμ a).toIsPreBrownianReal)
      (innovationMap_stronglyAdapted beta)
      (innovationMap_increment_indep_filtration hμ)
      (fun s t _ _ _ hab => innovationMap_increments_indep hμ s t hab)
      (fun a => (innovationMap_isBrownianReal hμ a).cont)
      (fun a => (continuousRootResponse_progressive hb a).stronglyAdapted) hc
      (C := fun _ => 1) (fun _ => by norm_num)
      (fun a => Eventually.of_forall (fun x t => continuousRootResponse_abs_le_one hb a t x))
      henergy
  have hs (N : ℕ) := hAsum (N : ℝ≥0)
  have heq := ae_spatialCompensator_eq_primitive hc hs
  have hpQ := compensatedSquare_spatial_primitive
    (fun a => continuousRootResponse_progressive hb a) hc hs hYM.stronglyAdapted hQ
  refine ⟨I, Y, hI2, hY2, hI, hIlim, hYp, hYM, hYc, hY0,
    hYiso, hYsum, hYmax, hpQ, ?_, ?_⟩
  · intro t
    apply (hAint t).congr
    filter_upwards [heq] with x hx
    exact hx.1 t
  · filter_upwards [heq] with x hx
    exact hx.2.1

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyIntegralLimits
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy BrownianIntegralProcess

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
  [IsProbabilityMeasure μ]

theorem ae_innovationMap_projection (j : Bool) :
    ∀ᵐ q ∂copies beta μ, innovationMap beta (projection j q) = q.1 := by
  have h := IsingConditionalCopyBounds.ae_innovationMap_copies
    (beta := beta) (μ := μ)
    (rho := (observationLaw μ).map (innovationMap beta))
    (eta := kernel beta μ) kernel_graphLaw
  filter_upwards [h] with q hq
  cases j
  · exact hq.2
  · exact hq.1

theorem stoppedUniformSum_copy_eq_ae (j : Bool) (v : TreeVertex d)
    (H : ℝ≥0 → Paths d → ℝ) :
    ∀ᵐ q ∂copies beta μ, ∀ (T : ℝ≥0) (n : ℕ) (t : ℝ≥0),
      stoppedUniformSum (fun s (p : Joint d) => p.1 v s)
        (fun s p => H s (projection j p)) T n t q =
      stoppedUniformSum (fun s x => innovationMap beta x v s) H T n t
        (projection j q) := by
  filter_upwards [ae_innovationMap_projection (beta := beta) (μ := μ) j] with q hq
  intro T n t
  simp only [stoppedUniformSum, StoppedSimpleIntegral.intervalSum, hq]

theorem tendsto_stoppedUniformSum_copy (j : Bool) (v : TreeVertex d)
    {H I : ℝ≥0 → Paths d → ℝ}
    (hH : ∀ s, StronglyMeasurable (H s)) (T t : ℝ≥0)
    (hI : AEStronglyMeasurable (I t) (observationLaw μ))
    (hlim : Tendsto (fun n => ∫ x,
      (stoppedUniformSum (fun s x => innovationMap beta x v s) H T n t x - I t x) ^ 2
        ∂observationLaw μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ q,
      (stoppedUniformSum (fun s (p : Joint d) => p.1 v s)
        (fun s p => H s (projection j p)) T n t q - I t (projection j q)) ^ 2
          ∂copies beta μ) atTop (𝓝 0) := by
  have hB (s : ℝ≥0) : Measurable (fun x : Paths d => innovationMap beta x v s) :=
    (continuous_eval_const s).measurable.comp
      ((measurable_pi_apply v).comp (measurable_innovationMap beta))
  have hm (n : ℕ) : AEStronglyMeasurable
      (stoppedUniformSum (fun s x => innovationMap beta x v s) H T n t)
      (observationLaw μ) := by
    apply Measurable.aestronglyMeasurable
    unfold stoppedUniformSum StoppedSimpleIntegral.intervalSum
    exact Finset.measurable_sum _ (fun i _ =>
      (hH _).measurable.mul ((hB _).sub (hB _)))
  have hp := BrownianGrid.meanSquare_limit_comp
    (copyProjection_measurePreserving beta μ j) hm hI hlim
  have heq (n : ℕ) :
      (∫ q, (stoppedUniformSum (fun s (p : Joint d) => p.1 v s)
        (fun s p => H s (projection j p)) T n t q - I t (projection j q)) ^ 2
          ∂copies beta μ) =
      ∫ q, (stoppedUniformSum (fun s x => innovationMap beta x v s) H T n t
        (projection j q) - I t (projection j q)) ^ 2 ∂copies beta μ := by
    apply integral_congr_ae
    filter_upwards [stoppedUniformSum_copy_eq_ae (beta := beta) (μ := μ) j v H] with q hq
    rw [hq T n t]
  simpa only [heq] using hp

theorem integer_stoppedUniformSum_limits_copy (j : Bool) (v : TreeVertex d)
    {H I : ℝ≥0 → Paths d → ℝ}
    (hH : StronglyAdapted (filtration d) H)
    (hI : ∀ t, MemLp (I t) 2 (observationLaw μ))
    (hlim : ∀ N : ℕ, 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ x,
        (stoppedUniformSum (fun s x => innovationMap beta x v s) H N n t x - I t x) ^ 2
          ∂observationLaw μ) atTop (𝓝 0)) :
    ∀ N : ℕ, 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ q,
        (stoppedUniformSum (fun s (p : Joint d) => p.1 v s)
          (fun s p => H s (projection j p)) N n t q - I t (projection j q)) ^ 2
            ∂copies beta μ) atTop (𝓝 0) := by
  intro N hN t ht
  exact tendsto_stoppedUniformSum_copy j v (fun s => (hH s).mono ((filtration d).le s))
    N t (hI t).aestronglyMeasurable (hlim N hN t ht)

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyResponseIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy BrownianIntegralProcess

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
  [IsProbabilityMeasure μ]

private theorem response_stoppedUniformSum_memLp
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (a : TreeVertex d) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    MemLp (stoppedUniformSum (fun s x => innovationMap beta x a s)
      (continuousRootResponse hb a) T n t) 2 (observationLaw μ) := by
  apply StoppedIntegralAssociativity.stoppedUniformSum_memLp
    (fun s => ((innovationMap_isBrownianReal hμ a).toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval s).memLp_two)
    (continuousRootResponse_progressive hb a).stronglyAdapted
  exact Eventually.of_forall (fun x s => continuousRootResponse_abs_le_one hb a s x)

private theorem response_stoppedUniformSum_copy_memLp
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (j : Bool) (a : TreeVertex d) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    MemLp (stoppedUniformSum (fun s (p : Joint d) => p.1 a s)
      (fun s p => continuousRootResponse hb a s (projection j p)) T n t)
      2 (copies beta μ) := by
  have hp := copyProjection_measurePreserving beta μ j
  apply ((response_stoppedUniformSum_memLp hμ hb a T n t).comp_measurePreserving hp).ae_eq
  filter_upwards [stoppedUniformSum_copy_eq_ae (beta := beta) (μ := μ)
    j a (continuousRootResponse hb a)] with q hq
  exact (hq T n t).symm

theorem rootResponse_integral_eq_copy
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (j : Bool) (a : TreeVertex d)
    {I : ℝ≥0 → Paths d → ℝ} {J : ℝ≥0 → Joint d → ℝ}
    (hI2 : ∀ t, MemLp (I t) 2 (observationLaw μ))
    (hJ2 : ∀ t, MemLp (J t) 2 (copies beta μ))
    (hIlim : ∀ N : ℕ, 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ x,
        (stoppedUniformSum (fun s x => innovationMap beta x a s)
          (continuousRootResponse hb a) N n t x - I t x) ^ 2
            ∂observationLaw μ) atTop (𝓝 0))
    (hJlim : ∀ N : ℕ, 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ q,
        (stoppedUniformSum (fun s (p : Joint d) => p.1 a s)
          (fun s p => continuousRootResponse hb a s (projection j p)) N n t q -
            J t q) ^ 2 ∂copies beta μ) atTop (𝓝 0))
    (t : ℝ≥0) :
    (fun q => I t (projection j q)) =ᵐ[copies beta μ] J t := by
  obtain ⟨N, hN⟩ := exists_nat_ge t
  have ht : t ≤ ((N + 1 : ℕ) : ℝ≥0) :=
    hN.trans (by exact_mod_cast Nat.le_succ N)
  have hp := copyProjection_measurePreserving beta μ j
  exact BrownianGrid.ae_eq_of_mean_square_limits
    (fun n => response_stoppedUniformSum_copy_memLp hμ hb j a ((N + 1 : ℕ) : ℝ≥0) n t)
    ((hI2 t).comp_measurePreserving hp) (hJ2 t)
    (integer_stoppedUniformSum_limits_copy j a
      (continuousRootResponse_progressive hb a).stronglyAdapted
      hI2 hIlim (N + 1) (Nat.succ_pos N) t ht)
    (hJlim (N + 1) (Nat.succ_pos N) t ht)

theorem rootResponse_sum_eq_copy
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (j : Bool)
    {I : TreeVertex d → ℝ≥0 → Paths d → ℝ} {Y : ℝ≥0 → Paths d → ℝ}
    {J : TreeVertex d → ℝ≥0 → Joint d → ℝ} {Z : ℝ≥0 → Joint d → ℝ}
    (hI2 : ∀ a t, MemLp (I a t) 2 (observationLaw μ))
    (hY2 : ∀ t, MemLp (Y t) 2 (observationLaw μ))
    (hJ2 : ∀ a t, MemLp (J a t) 2 (copies beta μ))
    (hZ2 : ∀ t, MemLp (Z t) 2 (copies beta μ))
    (hIlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ x,
        (stoppedUniformSum (fun s x => innovationMap beta x a s)
          (continuousRootResponse hb a) N n t x - I a t x) ^ 2
            ∂observationLaw μ) atTop (𝓝 0))
    (hJlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ q,
        (stoppedUniformSum (fun s (p : Joint d) => p.1 a s)
          (fun s p => continuousRootResponse hb a s (projection j p)) N n t q -
            J a t q) ^ 2 ∂copies beta μ) atTop (𝓝 0))
    (hsumI : ∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t)))
    (hsumJ : ∀ t, HasSum (fun a => (hJ2 a t).toLp (J a t)) ((hZ2 t).toLp (Z t)))
    (t : ℝ≥0) :
    (fun q => Y t (projection j q)) =ᵐ[copies beta μ] Z t := by
  have hp := copyProjection_measurePreserving beta μ j
  have hs := PredictableL2.hasSum_toLp_comp_measurePreserving hp
    (fun a => I a t) (fun a => hI2 a t) (hY2 t) (hsumI t)
  have hs' : HasSum
      (fun a => ((hI2 a t).comp_measurePreserving hp).toLp (I a t ∘ projection j))
      ((hZ2 t).toLp (Z t)) := by
    apply (hsumJ t).congr_fun
    intro a
    exact MemLp.toLp_congr _ _
      (rootResponse_integral_eq_copy hμ hb j a (hI2 a) (hJ2 a)
        (hIlim a) (hJlim a) t)
  exact (MemLp.toLp_eq_toLp_iff ((hY2 t).comp_measurePreserving hp) (hZ2 t)).mp
    (hs.unique hs')

theorem rootResponse_sum_eq_copy_all_times
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {I : TreeVertex d → ℝ≥0 → Paths d → ℝ} {Y : ℝ≥0 → Paths d → ℝ}
    {J : Bool → TreeVertex d → ℝ≥0 → Joint d → ℝ}
    {Z : Bool → ℝ≥0 → Joint d → ℝ}
    (hI2 : ∀ a t, MemLp (I a t) 2 (observationLaw μ))
    (hY2 : ∀ t, MemLp (Y t) 2 (observationLaw μ))
    (hJ2 : ∀ j a t, MemLp (J j a t) 2 (copies beta μ))
    (hZ2 : ∀ j t, MemLp (Z j t) 2 (copies beta μ))
    (hcY : ∀ᵐ x ∂observationLaw μ, Continuous (fun t => Y t x))
    (hcZ : ∀ j, ∀ᵐ q ∂copies beta μ, Continuous (fun t => Z j t q))
    (hIlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ x,
        (stoppedUniformSum (fun s x => innovationMap beta x a s)
          (continuousRootResponse hb a) N n t x - I a t x) ^ 2
            ∂observationLaw μ) atTop (𝓝 0))
    (hJlim : ∀ j a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ q,
        (stoppedUniformSum (fun s (p : Joint d) => p.1 a s)
          (fun s p => continuousRootResponse hb a s (projection j p)) N n t q -
            J j a t q) ^ 2 ∂copies beta μ) atTop (𝓝 0))
    (hsumI : ∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t)))
    (hsumJ : ∀ j t,
      HasSum (fun a => (hJ2 j a t).toLp (J j a t)) ((hZ2 j t).toLp (Z j t))) :
    ∀ᵐ q ∂copies beta μ, ∀ j t, Y t (projection j q) = Z j t q := by
  have he (j : Bool) : (fun q t => Y t (projection j q)) =ᵐ[copies beta μ]
      (fun q t => Z j t q) := by
    have hp := copyProjection_measurePreserving beta μ j
    have hcY' : ∀ᵐ q ∂copies beta μ,
        Continuous (fun t => Y t (projection j q)) := by
      apply ae_of_ae_map (p := fun x => Continuous (fun t => Y t x)) hp.aemeasurable
      simpa only [hp.map_eq] using hcY
    exact ae_eq_of_continuous_of_evaluation_ae_eq hcY' (hcZ j)
      (rootResponse_sum_eq_copy hμ hb j hI2 hY2 (hJ2 j) (hZ2 j)
        hIlim (hJlim j) hsumI (hsumJ j))
  filter_upwards [ae_all_iff.mpr he] with q hq
  intro j t
  exact congrFun (hq j) t

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

theorem actual_variance_analysis_oai
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (T : ℝ≥0) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ z,
      (field beta (ConnectedHull.root d) t.toNNReal z.2.1 -
        field beta (ConnectedHull.root d) t.toNNReal z.2.2) ^ 2 ∂copies beta μ) 0 T ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      deriv (fun s : ℝ => ∫ z,
        (field beta (ConnectedHull.root d) s.toNNReal z.2.1 -
          field beta (ConnectedHull.root d) s.toNNReal z.2.2) ^ 2 ∂copies beta μ) t =
        ∫ z, density beta (ConnectedHull.root d) t z ∂copies beta μ) := by
  obtain ⟨I, Y, hI2, hY2, hI, hIlim, _hYp, hYM, hYc, _hY0,
      _hYiso, hYsum, _hYmax, _hQ, _hAint, _hAc⟩ :=
    exists_canonical_root_response_integrals hd hμ hb hcrit
  obtain ⟨S⟩ := IsingJoinedResponseIntegrals.exists_integrals hd hμ hb hcrit
  have hfield := canonical_field_eq_normalized_integral hd hμ hb hcrit
    (fun a => (hI a).2.1) hYM hI2 hY2 (fun a => (hI a).2.2) hYc hYsum hIlim
  have hcopy := rootResponse_sum_eq_copy_all_times hμ hb
    hI2 hY2 S.channel_memLp S.total_memLp hYc S.total_continuous
    hIlim S.channel_limit hYsum S.total_sum
  have hrep := copied_difference_decomposition hμ hb (ConnectedHull.root d)
    hfield (fun j => hcopy.mono (fun z hz => hz j))
  exact variance_analysis_of_joined_decomposition hd hμ hb hcrit S hrep T

end Problem367.IsingObservationFactor

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingObservationFactor.actual_variance_analysis_oai := @OAI.Problem367.IsingObservationFactor.actual_variance_analysis_oai
