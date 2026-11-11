-- Prove2me | solution 1 for OAI.Problem367.IsingObservationFactor.canonical_stopped_field_eq_of_integral_limits
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:47:28.627551+00:00
-- url     : https://prove2.me/submissions/527e5001-4b92-45db-9e30-be6e1f915966

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_IsingInnovation_exists_continuous_posterior
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_canonicalPosteriorExit_localizing
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_canonical_artanh_decomposition
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_continuousPosterior_initial_zero
import Theorems.Thm_OAI_Problem367_StoppedRowNormalization_stopped_row_normalization

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayFiltrationIntegral
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem coordinate_increment_indep_past {s t : ℝ≥0}
    (hind : Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (a : ι) :
    Indep (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance)
      (F s) P := by
  have hm : Measurable[
      MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance]
      (fun ω => B a t ω - B a s ω) :=
    (measurable_pi_apply a).comp (show Measurable[
      MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance]
      (fun ω a => B a t ω - B a s ω) from measurable_iff_comap_le.mpr le_rfl)
  exact indep_of_indep_of_le_left hind hm.comap_le

end Problem367.BrownianArrayFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_PredictableMeshApproximation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PredictableMesh

theorem left_eq_of_mem_Ioc {n k : ℕ} {t : ℝ≥0}
    (ht : t ∈ Ioc (point n k) (point n (k + 1))) :
    left n t = point n k := by
  have hN : (0 : ℝ≥0) < (n + 1 : ℕ) := by positivity
  have hc : ⌈(n + 1 : ℕ) * t⌉₊ = k + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).2
    constructor
    · have := (div_lt_iff₀ hN).1 ht.1
      simpa only [mul_comm, Nat.succ_sub_one] using this
    · have := (le_div_iff₀ hN).1 ht.2
      simpa only [mul_comm, Nat.succ_sub_one] using this
  change point n (⌈(n + 1 : ℕ) * t⌉₊ - 1) = point n k
  rw [hc, Nat.add_sub_cancel]

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

theorem sample_isStronglyPredictable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) (n : ℕ) : IsStronglyPredictable F (sample u n) := by
  apply Measurable.stronglyMeasurable
  intro s hs
  have heq : (Function.uncurry (sample u n)) ⁻¹' s =
      ({0} ×ˢ (u 0 ⁻¹' s)) ∪
        ⋃ k : ℕ, (Ioc (point n k) (point n (k + 1))) ×ˢ (u (point n k) ⁻¹' s) := by
    ext ⟨t, ω⟩
    simp only [mem_preimage, Function.uncurry_apply_pair, mem_union, mem_prod,
      mem_singleton_iff, mem_iUnion]
    constructor
    · intro h
      by_cases ht : t = 0
      · exact Or.inl ⟨ht, by simpa [ht, sample] using h⟩
      · exact Or.inr ⟨⌈(n + 1 : ℕ) * t⌉₊ - 1,
          mem_mesh_Ioc (pos_iff_ne_zero.mpr ht), h⟩
    · rintro (⟨ht, h⟩ | ⟨k, ht, h⟩)
      · simpa [ht, sample] using h
      · simpa only [sample, left_eq_of_mem_Ioc ht] using h
  rw [heq]
  apply MeasurableSet.union
  · exact measurableSet_predictable_singleton_bot_prod ((hu 0).measurable hs)
  · exact MeasurableSet.iUnion fun k =>
      measurableSet_predictable_Ioc_prod _ _ ((hu (point n k)).measurable hs)

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_ContinuousSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PredictableMesh

theorem repair_isStronglyPredictable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) : IsStronglyPredictable F (repair u) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact StronglyMeasurable.limUnder (fun n => sample_isStronglyPredictable hu n)

theorem repair_eq_of_continuousOn {Ω : Type*} {u : ℝ≥0 → Ω → ℝ}
    {T : ℝ≥0} {ω : Ω} (hc : ContinuousOn (fun t => u t ω) (Iic T))
    {t : ℝ≥0} (ht : t ≤ T) : repair u t ω = u t ω := by
  apply Filter.Tendsto.limUnder_eq
  apply (hc t ht).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_left t, Filter.Eventually.of_forall
    (fun n => (left_le n t).trans ht)⟩

end Problem367.PredictableMesh

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_IntegralAssociativityLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367.SimpleIntegral

section Limits

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem coarseTransform_memLp (K : ℕ → Ω → ℝ)
    (hK : ∀ j, AEStronglyMeasurable (K j) μ) (C : ℕ → ℝ)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, |K j ω| ≤ C j)
    {M : ℕ → Ω → ℝ} (hM : ∀ j, MemLp (M j) 2 μ) (n : ℕ) :
    MemLp (coarseTransform K M n) 2 μ := by
  exact memLp_finsetSum _ fun j _ =>
    bounded_mul_memLp (hK j) (hbound j) ((hM (j + 1)).sub (hM j))

end Limits
end Problem367.SimpleIntegral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ContinuousAssociativity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianContinuousAssociativity

open BrownianGrid BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B H K : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem uniformSum_memLp {M : ℝ≥0 → Ω → ℝ}
    (hM2 : ∀ t, MemLp (M t) 2 P) (hK : StronglyAdapted F K)
    {D : ℝ} (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (T : ℝ≥0) (n : ℕ) : MemLp (uniformSum M K T n) 2 P := by
  exact SimpleIntegral.coarseTransform_memLp (fun j => K (uniformGrid T n j))
    (fun j => ((hK _).mono (F.le _)).aestronglyMeasurable) (fun _ => D)
    (fun j => hbK.mono (fun ω hω => hω _)) (fun j => hM2 _) n

end Problem367.BrownianContinuousAssociativity

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ClippedArtanhWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.ClippedArtanhWeight

theorem continuous_clip (r : ℝ) : Continuous (clip r) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_clip_le {r : ℝ} (hr : 0 ≤ r) (x : ℝ) : |clip r x| ≤ r := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clip_eq_of_abs_le {r x : ℝ} (hx : |x| ≤ r) : clip r x = x := by
  have h := abs_le.mp hx
  simp only [clip, min_eq_right h.2, max_eq_right h.1]

theorem denominator_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    0 < 1 - clip r x ^ 2 := by
  have hs : clip r x ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (clip r x)) hr0).mpr (abs_clip_le hr0 x)
  nlinarith

theorem weight_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    0 < weight r x :=
  div_pos zero_lt_one (denominator_pos hr0 hr1 x)

theorem abs_weight_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    |weight r x| ≤ 1 / (1 - r ^ 2) := by
  rw [abs_of_pos (weight_pos hr0 hr1 x)]
  have hs : clip r x ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (clip r x)) hr0).mpr (abs_clip_le hr0 x)
  exact one_div_le_one_div_of_le (by nlinarith) (by linarith)

theorem continuous_weight {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (weight r) :=
  continuous_const.div (continuous_const.sub ((continuous_clip r).pow 2))
    (fun x => (denominator_pos hr0 hr1 x).ne')

theorem weight_eq_of_abs_le {r x : ℝ} (hx : |x| ≤ r) :
    weight r x = 1 / (1 - x ^ 2) := by
  rw [weight, clip_eq_of_abs_le hx]

theorem weight_mul_covariance_eq {r m C R : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hm : |m| ≤ r)
    (hC : C = (1 - m ^ 2) * R) : weight r m * C = R := by
  have hd : 1 - m ^ 2 ≠ 0 := by
    simpa only [clip_eq_of_abs_le hm] using (denominator_pos hr0 hr1 m).ne'
  rw [weight_eq_of_abs_le hm, hC]
  field_simp

end Problem367.ClippedArtanhWeight

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

end Problem367.DominatedMartingaleRightContinuation

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

theorem radius_nonneg (n : ℕ) : 0 ≤ radius n := by
  have hp : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hi : ((n : ℝ) + 2)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_one hp]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact sub_nonneg.mpr hi

theorem radius_lt_one (n : ℕ) : radius n < 1 := by
  have hp : (0 : ℝ) < ((n : ℝ) + 2)⁻¹ := by positivity
  unfold radius
  linarith

end Problem367.PosteriorInteriorLocalization

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

theorem threshold_nonneg (n : ℕ) : 0 ≤ threshold n :=
  PosteriorInteriorLocalization.radius_nonneg n

theorem threshold_lt_one (n : ℕ) : threshold n < 1 :=
  PosteriorInteriorLocalization.radius_lt_one n

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

theorem jointExit_le_posteriorExit {Ω : Type*} (M A : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ω : Ω) : jointExit M A n ω ≤ posteriorExit M n ω := min_le_left _ _

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

theorem abs_stopped_posterior_le {Ω : Type*} {M A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => M t ω)) (hzero : M 0 ω = 0) (n : ℕ) (t : ℝ≥0) :
    |stoppedProcess M (jointExit M A n) t ω| ≤ threshold n := by
  apply abs_stoppedProcess_le_of_le_exit hc
    (by simpa only [hzero, abs_zero] using threshold_nonneg n) _ t
  exact (jointExit_le_posteriorExit M A n ω).trans (min_le_left _ _)

end Problem367.PosteriorCompensatorStopping

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ContinuousPosterior
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem posterior_martingale
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) :
    Martingale (posterior beta B v) (ArrayPosteriorStationarity.filtration B hmB)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  have h := martingale_condExp (fun q : State d A => spinSign (q.1 v))
    (ArrayPosteriorStationarity.filtration B hmB)
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
  exact h.congr (posterior_progressive beta B hmB hcB v).stronglyAdapted
    (fun t => (posterior_eq_condExp hμ ν hB hmB t v).symm)

end Problem367.IsingInnovation

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationFactor
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
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

variable {d : ℕ}

theorem posterior_mem_Ioo_ae {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (t : ℝ≥0) :
    ∀ᵐ x ∂observationLaw μ, posterior beta v t x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hm : Measurable (posterior beta v t) :=
    (measurable_infiniteGibbsSpinMean beta v).comp
      (Measurable.of_eval fun i => measurable_evaluation i t)
  apply (ae_map_iff measurable_uniformObservation.aemeasurable (hm measurableSet_Ioo)).mpr
  have hb := hμ.infiniteGibbsSpinMean_brownian_field_bound hbeta
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ t => (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample)
    t v
  filter_upwards [hb] with q hq
  change infiniteGibbsSpinMean beta v
    (fun i => WienerSampler.sample (q.2 i) t + (t : ℝ) * spinSign (q.1 i)) ∈ _
  simpa only [add_comm] using hq.1

theorem tanh_field_eq_posterior_ae {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (t : ℝ≥0) :
    (fun x => Real.tanh (field beta v t x)) =ᵐ[observationLaw μ] posterior beta v t := by
  filter_upwards [posterior_mem_Ioo_ae hμ hbeta v t] with x hx
  exact Real.tanh_artanh hx

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationPosteriorTransport
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingObservationInnovation

theorem measurePreserving_uniformObservation {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) :
    MeasurePreserving (uniformObservation (d := d))
      (μ.prod (labelMeasure d)) (observationLaw μ) :=
  ⟨measurable_uniformObservation, rfl⟩

end Problem367.IsingObservationInnovation

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

private lemma continuous_real_tanh : Continuous Real.tanh :=
  lipschitzWith_tanh_response.continuous

lemma continuousPosterior_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousPosterior beta v) := by
  intro T
  exact continuous_real_tanh.comp_stronglyMeasurable (continuousField_progressive beta v T)

 theorem continuousPosterior_modification
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    (∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousPosterior beta v t x)) ∧
      (∀ t, continuousPosterior beta v t =ᵐ[observationLaw μ] posterior beta v t) := by
  obtain ⟨hc, he⟩ := continuousField_modification hd hμ hb hcrit v
  refine ⟨hc.mono (fun x hx => continuous_real_tanh.comp hx), fun t => ?_⟩
  filter_upwards [he t, tanh_field_eq_posterior_ae hμ hb v t] with x hx ht
  exact (congrArg Real.tanh hx).trans ht

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_Pushforward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set

namespace Problem367.MartingalePushforward

 theorem martingale_of_pullback
    {ι Ω Ξ : Type*} [Preorder ι] [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {φ : Ω → Ξ} (hφ : MeasurePreserving φ μ ν)
    {F : Filtration ι mΩ} {G : Filtration ι mΞ}
    (hpast : ∀ t, (G t).comap φ ≤ F t)
    {X : ι → Ξ → ℝ} (hX : StronglyAdapted G X)
    (hM : Martingale (fun t ω => X t (φ ω)) F μ) : Martingale X G ν := by
  have hm (t : ι) : AEStronglyMeasurable (X t) ν :=
    ((hX t).mono (G.le t)).aestronglyMeasurable
  have hi (t : ι) : Integrable (X t) ν :=
    (hφ.integrable_comp (hm t)).mp (hM.integrable t)
  refine ⟨hX, fun s t hst => ?_⟩
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (G.le s) (hi t)
    (fun A _ _ => (hi s).integrableOn) _ (hX s).aestronglyMeasurable
  intro A hA _
  have hpre : MeasurableSet[F s] (φ ⁻¹' A) :=
    hpast s _ ((comap_measurable (m := G s) φ) hA)
  have he (u : ι) : (∫ x in A, X u x ∂ν) = ∫ ω in φ ⁻¹' A, X u (φ ω) ∂μ := by
    rw [← hφ.map_eq]
    exact setIntegral_map (G.le s _ hA) (by simpa only [hφ.map_eq] using hm u)
      hφ.measurable.aemeasurable
  rw [he s, he t]
  exact hM.setIntegral_eq hst hpre

end Problem367.MartingalePushforward

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalMartingales
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
open IsingObservationInnovation

 theorem canonical_posterior_martingale
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    Martingale (posterior beta v) (filtration d) (observationLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  let B : ℝ≥0 → ℝ → ℝ := fun t u => WienerSampler.sample u t
  have hmB (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample
  apply MartingalePushforward.martingale_of_pullback (measurePreserving_uniformObservation μ)
    (F := ArrayPosteriorStationarity.filtration B hmB)
    (fun t => (filtration_comap_uniformObservation d t hmB).le)
    (posterior_progressive beta v).stronglyAdapted
  exact IsingInnovation.posterior_martingale hμ uniform01
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal hmB
    (fun u => (WienerSampler.sample u).continuous) v

 theorem continuousPosterior_martingale
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    Martingale (continuousPosterior beta v) (filtration d) (observationLaw μ) :=
  (canonical_posterior_martingale hμ v).congr
    (continuousPosterior_progressive beta v).stronglyAdapted
    (fun t => ((continuousPosterior_modification hd hμ hb hcrit v).2 t).symm)

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

private lemma continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr (fun z => (hasDerivAt_tanh_response z).continuousAt)

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

lemma continuousRootCovariance_progressive (hb : 0 ≤ beta) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (continuousRootCovariance hb v) := by
  intro t
  have hf := continuousField_progressive beta (ConnectedHull.root d) t
  exact (stronglyMeasurable_const.sub
    ((continuous_tanh.comp_stronglyMeasurable hf).pow 2)).mul
      (continuousRootResponse_progressive hb v t)

lemma continuousRootCovariance_abs_le_one (hb : 0 ≤ beta) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : |continuousRootCovariance hb v t x| ≤ 1 := by
  have h0 := (sub_pos.mpr (Real.tanh_sq_lt_one
    (continuousField beta (ConnectedHull.root d) t x))).le
  have h1 : 1 - Real.tanh (continuousField beta (ConnectedHull.root d) t x) ^ 2 ≤ 1 :=
    sub_le_self _ (sq_nonneg _)
  rw [continuousRootCovariance, abs_mul, abs_of_nonneg h0]
  exact (mul_le_mul h1 (continuousRootResponse_abs_le_one hb v t x)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)

theorem continuousRootCovariance_continuous_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    ∀ᵐ x ∂observationLaw μ, Continuous (fun t => continuousRootCovariance hb v t x) := by
  filter_upwards [(continuousField_modification hd hμ hb hcrit (ConnectedHull.root d)).1,
    continuousRootResponse_continuous_ae hd hμ hb hcrit v] with x hf hr
  exact (continuous_const.sub ((continuous_tanh.comp hf).pow 2)).mul hr

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_RandomEvaluation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.MartingaleRandomEvaluation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem stronglyMeasurable_random_evaluation
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hp : IsStronglyProgressive F M) {τ : Ω → ℝ≥0} (hτ : Measurable τ)
    {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    StronglyMeasurable (fun ω => M (τ ω) ω) := by
  have hm : StronglyMeasurable (fun p : Iic T × Ω => M p.1 p.2) :=
    (hp T).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le T)))
  let τ' : Ω → Iic T := fun ω => ⟨τ ω, hbound ω⟩
  have ht : Measurable τ' := hτ.subtype_mk
  exact hm.comp_measurable (ht.prodMk measurable_id)

theorem aestronglyMeasurable_random_evaluation
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : StronglyAdapted F M)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    AEStronglyMeasurable (fun ω => M (τ ω) ω) P := by
  have hm := stronglyMeasurable_random_evaluation
    (PredictableMesh.repair_isStronglyPredictable hM).isStronglyProgressive hτ hbound
  apply hm.aestronglyMeasurable.congr
  filter_upwards [hc] with ω hω
  exact PredictableMesh.repair_eq_of_continuousOn (T := τ ω) hω.continuousOn le_rfl

theorem integrable_sq_random_evaluation [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (h2 : ∀ t, MemLp (M t) 2 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => M (τ ω) ω ^ 2) P := by
  apply (MartingaleStrongMaximal.integrable_maximalSquare hM h2 hc T).mono'
    ((aestronglyMeasurable_random_evaluation hM.stronglyAdapted hc hτ hbound).pow 2)
  filter_upwards [MartingaleStrongMaximal.ae_all_sq_le_maximalSquare hM h2 hc T] with ω hω
  change ‖M (τ ω) ω ^ 2‖ ≤ _
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (M (τ ω) ω))] using
    hω (τ ω) (hbound ω)

theorem memLp_random_evaluation [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (h2 : ∀ t, MemLp (M t) 2 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) {T : ℝ≥0} (hbound : ∀ ω, τ ω ≤ T) :
    MemLp (fun ω => M (τ ω) ω) 2 P :=
  (memLp_two_iff_integrable_sq
    (aestronglyMeasurable_random_evaluation hM.stronglyAdapted hc hτ hbound)).mpr
      (integrable_sq_random_evaluation hM h2 hc hτ hbound)

end Problem367.MartingaleRandomEvaluation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedMartingaleL2
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedMartingaleL2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M L : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

theorem measurable_cappedTime (hτ : IsStoppingTime F τ) (t : ℝ≥0) :
    Measurable (fun ω => (min (t : WithTop ℝ≥0) (τ ω)).untopA) :=
  WithTop.measurable_untopA.comp (measurable_const.min (hτ.measurable.mono hτ.measurableSpace_le le_rfl))

theorem memLp_stoppedProcess_two
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hτ : IsStoppingTime F τ) (t : ℝ≥0) :
    MemLp (stoppedProcess M τ t) 2 μ :=
  MartingaleRandomEvaluation.memLp_random_evaluation hM h2 hc
    (measurable_cappedTime hτ t) (fun _ => WithTop.untopA_le (min_le_left _ _))

end Problem367.StoppedMartingaleL2

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedIntegralLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.StoppedIntegralLocality

variable {Ω : Type*}

theorem uniformSum_stopped_congr (M H K : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0) (n : ℕ) (ω : Ω)
    (hlocal : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω → H t ω = K t ω) :
    BrownianGrid.uniformSum (stoppedProcess M τ) H T n ω =
      BrownianGrid.uniformSum (stoppedProcess M τ) K T n ω := by
  unfold BrownianGrid.uniformSum BrownianGrid.integralSum
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  by_cases ht : (BrownianGrid.uniformGrid T n i : WithTop ℝ≥0) ≤ τ ω
  · rw [hlocal _ ht]
  · have ha : τ ω ≤ (BrownianGrid.uniformGrid T n i : WithTop ℝ≥0) :=
      le_of_not_ge ht
    have hab : (BrownianGrid.uniformGrid T n i : WithTop ℝ≥0) ≤
        (BrownianGrid.uniformGrid T n (i + 1) : WithTop ℝ≥0) := by
      exact_mod_cast BrownianGrid.uniformGrid_mono T n (Nat.le_succ i)
    rw [stoppedProcess_eq_of_ge ha, stoppedProcess_eq_of_ge (ha.trans hab)]
    simp only [sub_self, mul_zero]

end Problem367.StoppedIntegralLocality

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalClippedWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.ClippedArtanhWeight
open ArtanhMartingaleFormula PosteriorCompensatorStopping PosteriorStoppingTimes

theorem weight_eq_stopped_before_exit {Ω : Type*}
    {M A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => M t ω)) (hzero : M 0 ω = 0)
    (n : ℕ) (t : ℝ≥0) (ht : (t : WithTop ℝ≥0) ≤ jointExit M A n ω) :
    weight (threshold n) (M t ω) =
      firstWeight (stoppedProcess M (jointExit M A n) t ω) := by
  have hb := abs_stopped_posterior_le (A := A) hc hzero n t
  rw [stoppedProcess_eq_of_le ht] at hb ⊢
  exact weight_eq_of_abs_le hb

end Problem367.ClippedArtanhWeight

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation ArtanhMartingaleFormula
open PosteriorStoppingTimes PosteriorCompensatorStopping

lemma canonicalClippedWeight_progressive {d : ℕ} (beta : ℝ) (n : ℕ) :
    IsStronglyProgressive (filtration d) (canonicalClippedWeight beta n) := by
  intro T
  exact (ClippedArtanhWeight.continuous_weight (threshold_nonneg n) (threshold_lt_one n)).comp_stronglyMeasurable
    (continuousPosterior_progressive beta (ConnectedHull.root d) T)

lemma canonicalClippedWeight_bound {d : ℕ} (beta : ℝ) (n : ℕ)
    (t : ℝ≥0) (x : Paths d) :
    |canonicalClippedWeight beta n t x| ≤ 1 / (1 - threshold n ^ 2) :=
  ClippedArtanhWeight.abs_weight_le (threshold_nonneg n) (threshold_lt_one n) _

theorem canonicalClippedWeight_continuous_ae
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (n : ℕ) :
    ∀ᵐ x ∂observationLaw μ, Continuous (fun t => canonicalClippedWeight beta n t x) := by
  filter_upwards [(continuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d)).1]
    with x hx
  exact (ClippedArtanhWeight.continuous_weight (threshold_nonneg n) (threshold_lt_one n)).comp hx

theorem canonicalClippedWeight_mul_covariance_before_exit
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (n : ℕ) :
    ∀ᵐ x ∂observationLaw μ, ∀ t : ℝ≥0,
      (t : WithTop ℝ≥0) ≤ canonicalPosteriorExit beta (ConnectedHull.root d) n x →
      ∀ w, canonicalClippedWeight beta n t x * continuousRootCovariance hb w t x =
        continuousRootResponse hb w t x := by
  filter_upwards [(continuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d)).1,
    continuousPosterior_initial_zero hd hμ hb hcrit (ConnectedHull.root d)] with x hc hz
  intro t ht w
  have hm := abs_stopped_posterior_le
    (A := canonicalCovarianceCompensator beta (ConnectedHull.root d)) hc hz n t
  change (t : WithTop ℝ≥0) ≤ jointExit
    (continuousPosterior beta (ConnectedHull.root d))
    (canonicalCovarianceCompensator beta (ConnectedHull.root d)) n x at ht
  rw [stoppedProcess_eq_of_le ht] at hm
  exact ClippedArtanhWeight.weight_mul_covariance_eq (threshold_nonneg n) (threshold_lt_one n) hm rfl

theorem canonicalClippedWeight_uniformSum_eq
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (n : ℕ) (T : ℝ≥0) (k : ℕ) :
    let M := continuousPosterior beta (ConnectedHull.root d)
    let τ := canonicalPosteriorExit beta (ConnectedHull.root d) n
    BrownianGrid.uniformSum (stoppedProcess M τ) (canonicalClippedWeight beta n) T k
      =ᵐ[observationLaw μ]
        BrownianGrid.uniformSum (stoppedProcess M τ)
          (fun t x => firstWeight (stoppedProcess M τ t x)) T k := by
  filter_upwards [(continuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d)).1,
    continuousPosterior_initial_zero hd hμ hb hcrit (ConnectedHull.root d)] with x hc hz
  apply StoppedIntegralLocality.uniformSum_stopped_congr
  intro t ht
  exact ClippedArtanhWeight.weight_eq_stopped_before_exit hc hz n t ht

end Problem367.IsingObservationFactor

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_L2MartingaleRightContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.DominatedMartingaleRightContinuation

theorem martingale_rightCont_of_ae_continuous_memLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) :
    Martingale M F.rightCont μ := by
  apply martingale_rightCont_of_ae_continuous_dominated hM hc
  intro T
  refine ⟨fun ω => 1 + MartingaleStrongMaximal.maximalSquare M T ω,
    (integrable_const 1).add (MartingaleStrongMaximal.integrable_maximalSquare hM hM2 hc T), ?_⟩
  filter_upwards [MartingaleStrongMaximal.ae_all_sq_le_maximalSquare hM hM2 hc T] with ω hω
  intro t ht
  apply abs_le.mpr
  have hsq := hω t ht
  constructor <;> nlinarith [sq_nonneg (M t ω - 1), sq_nonneg (M t ω + 1)]

end Problem367.DominatedMartingaleRightContinuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CanonicalNormalizedField
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation BrownianGrid
open DominatedMartingaleRightContinuation

theorem canonical_stopped_field_eq_of_integral_limits_oai
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {I J : TreeVertex d → ℝ≥0 → Paths d → ℝ} {Z : ℝ≥0 → Paths d → ℝ}
    (hIp : ∀ a, IsStronglyProgressive (filtration d) (I a))
    (hIM : ∀ a, Martingale (I a) (filtration d) (observationLaw μ))
    (hJM : ∀ a, Martingale (J a) (filtration d) (observationLaw μ))
    (hZM : Martingale Z (filtration d) (observationLaw μ))
    (hI2 : ∀ a t, MemLp (I a t) 2 (observationLaw μ))
    (hJ2 : ∀ a t, MemLp (J a t) 2 (observationLaw μ))
    (hZ2 : ∀ t, MemLp (Z t) 2 (observationLaw μ))
    (hcI : ∀ a, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => I a t x))
    (hcJ : ∀ a, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J a t x))
    (hcZ : ∀ᵐ x ∂observationLaw μ, Continuous (fun t => Z t x))
    (n : ℕ) (T : ℝ≥0)
    (hsumI : HasSum (fun a => (hI2 a T).toLp (I a T))
      ((posterior_memLp beta μ (ConnectedHull.root d) T 2).toLp
        (posterior beta (ConnectedHull.root d) T)))
    (hsumJ : HasSum (fun a => (hJ2 a T).toLp (J a T)) ((hZ2 T).toLp (Z T)))
    (hIlim : ∀ a, Tendsto (fun k => ∫ x,
      (uniformSum (fun t x => innovationMap beta x a t)
        (continuousRootCovariance hb a) T k x - I a T x) ^ 2 ∂observationLaw μ)
      atTop (𝓝 0))
    (hJlim : ∀ a, Tendsto (fun k => ∫ x,
      (uniformSum (fun t x => innovationMap beta x a t)
        (continuousRootResponse hb a) T k x - J a T x) ^ 2 ∂observationLaw μ)
      atTop (𝓝 0)) :
    let τ := canonicalPosteriorExit beta (ConnectedHull.root d) n
    stoppedProcess (continuousField beta (ConnectedHull.root d)) τ T =ᵐ[observationLaw μ]
      (fun x => stoppedProcess Z τ T x +
        stoppedProcess (nnrealTimePrimitive (canonicalResponseDrift beta (ConnectedHull.root d))) τ T x) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let M := continuousPosterior beta (ConnectedHull.root d)
  let τ := canonicalPosteriorExit beta (ConnectedHull.root d) n
  let K := canonicalClippedWeight (d := d) beta n
  have hM := continuousPosterior_martingale hd hμ hb hcrit (ConnectedHull.root d)
  have hcM := (continuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d)).1
  have hM2 (t : ℝ≥0) : MemLp (M t) 2 (observationLaw μ) :=
    MemLp.ae_eq ((continuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d)).2 t).symm
      (posterior_memLp beta μ (ConnectedHull.root d) t 2)
  have hsumM : HasSum (fun a => (hI2 a T).toLp (I a T)) ((hM2 T).toLp (M T)) := by
    have he := (posterior_memLp beta μ (ConnectedHull.root d) T 2).toLp_congr (hM2 T)
      ((continuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d)).2 T).symm
    exact he ▸ hsumI
  have hτ : IsStoppingTime (filtration d).rightCont τ :=
    (canonicalPosteriorExit_localizing hd hμ hb hcrit (ConnectedHull.root d)).isStoppingTime n
  have hk : 0 ≤ 1 / (1 - PosteriorStoppingTimes.threshold n ^ 2) := by
    apply one_div_nonneg.mpr
    nlinarith [PosteriorStoppingTimes.threshold_nonneg n,
      PosteriorStoppingTimes.threshold_lt_one n]
  have hbK : ∀ᵐ x ∂observationLaw μ, ∀ t, |K t x| ≤
      1 / (1 - PosteriorStoppingTimes.threshold n ^ 2) :=
    Eventually.of_forall (fun x t => canonicalClippedWeight_bound beta n t x)
  have hK := (canonicalClippedWeight_progressive (d := d) beta n).stronglyAdapted
  have hnorm := StoppedRowNormalization.stopped_row_normalization
    (fun a => (innovationMap_isBrownianReal hμ a).toIsPreBrownianReal)
    (innovationMap_stronglyAdapted beta)
    (fun a s t hst => BrownianArrayFiltration.coordinate_increment_indep_past
      (B := fun a t x => innovationMap beta x a t) (F := filtration d)
      (innovationMap_increment_indep_filtration hμ s t hst) a)
    (fun a => (innovationMap_isBrownianReal hμ a).cont)
    (fun a => (continuousRootCovariance_progressive hb a).stronglyAdapted)
    (fun a => (continuousRootResponse_progressive hb a).stronglyAdapted) hK
    (continuousRootCovariance_continuous_ae hd hμ hb hcrit)
    (canonicalClippedWeight_continuous_ae hd hμ hb hcrit n)
    (c := fun _ => 1) (r := fun _ => 1) (fun _ => by norm_num) hk
    (fun a => Eventually.of_forall (fun x t => continuousRootCovariance_abs_le_one hb a t x))
    (fun a => Eventually.of_forall (fun x t => continuousRootResponse_abs_le_one hb a t x)) hbK
    hIM hJM hM hZM hI2 hJ2 hM2 hZ2 hcI hcJ hcM hcZ hIp
    (continuousPosterior_progressive beta (ConnectedHull.root d)) T hsumM hsumJ hIlim hJlim hτ
    (fun a => (canonicalClippedWeight_mul_covariance_before_exit hd hμ hb hcrit n).mono
      (fun x hx t ht => hx t ht a))
  obtain ⟨L, hmL, hL2, hlimL, hfield⟩ :=
    canonical_artanh_decomposition hd hμ hb hcrit (ConnectedHull.root d) n T
  have hlimL' : Tendsto (fun k => ∫ x,
      (uniformSum (stoppedProcess M τ) K T k x - L x) ^ 2 ∂observationLaw μ)
      atTop (𝓝 0) := by
    apply hlimL.congr
    intro k
    apply integral_congr_ae
    filter_upwards [canonicalClippedWeight_uniformSum_eq hd hμ hb hcrit n T k] with x hx
    rw [hx]
  have hMs2 (t : ℝ≥0) := StoppedMartingaleL2.memLp_stoppedProcess_two
    (martingale_rightCont_of_ae_continuous_memLp_two hM hM2 hcM) hM2 hcM hτ t
  have hZs2 := StoppedMartingaleL2.memLp_stoppedProcess_two
    (martingale_rightCont_of_ae_continuous_memLp_two hZM hZ2 hcZ) hZ2 hcZ hτ T
  have heq := ae_eq_of_mean_square_limits
    (fun k => BrownianContinuousAssociativity.uniformSum_memLp hMs2 hK hbK T k)
    hL2 hZs2 hlimL' hnorm
  filter_upwards [hfield, heq] with x hx he
  exact hx.trans (congrArg (fun z => z +
    stoppedProcess (nnrealTimePrimitive (canonicalResponseDrift beta (ConnectedHull.root d))) τ T x) he)

end Problem367.IsingObservationFactor

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingObservationFactor.canonical_stopped_field_eq_of_integral_limits_oai := @OAI.Problem367.IsingObservationFactor.canonical_stopped_field_eq_of_integral_limits_oai
