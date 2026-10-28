-- Prove2me | solution 1 for OAI.CoulombBarrier.exists_actual_selected_data_constants
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:57:33.69972+00:00
-- url     : https://prove2.me/submissions/7f1556e8-8b48-466e-9338-ee11034ebd2f

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_exists_actual_fullAnnulus_inverse_constant
import Theorems.Thm_OAI_CoulombAtom_exists_actual_own_probability_tail_tilt_state
import Theorems.Thm_OAI_CoulombAtom_exists_own_state_exterior_number
import Theorems.Thm_OAI_CoulombBarrier_actual_outward_barrier_given_state_eventually

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_QuantumRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_QuantumRawLaw_scope

open MeasureTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CoulombAtom

attribute [local irreducible] graphComponent fermionGraphValue

lemma graphRawLaw_probability {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) : IsProbabilityMeasure (graphRawLaw F) := by
  constructor
  rw [graphRawLaw_univ, hn, ENNReal.ofReal_one]

end CoulombAtom

end Work_QuantumRawLaw_scope

open MeasureTheory Filter Set
open scoped ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UnorderedObservations
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UnorderedObservations_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation

lemma unorderedConfiguration_measurable {N : ℕ} :
    Measurable (unorderedConfiguration (N := N)) := measurable_quotient_mk''

lemma physicalObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (physicalObservedConfiguration (N := N) ell k) := by
  apply Measurable.of_eval
  intro i
  apply (Continuous.measurable (by fun_prop : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → Space))).comp
  apply Measurable.of_eval
  intro a
  exact (((EuclideanSpace.proj a : Space →L[ℝ] ℝ).measurable.comp
    ((measurable_pi_apply i).comp measurable_fst)).add
    (((measurable_pi_apply (k,i,a)).comp measurable_snd).const_mul _))

lemma unorderedObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (unorderedObservedConfiguration (N := N) ell k) :=
  unorderedConfiguration_measurable.comp (physicalObservedConfiguration_measurable ell k)

lemma observationInformation_le {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    observationInformation (N := N) ell j ≤
      (inferInstance : MeasurableSpace (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))) := by
  apply iSup_le
  intro k
  split_ifs
  · exact (unorderedObservedConfiguration_measurable ell k).comap_le
  · exact bot_le

end CoulombAtom

end Work_UnorderedObservations_scope

open MeasureTheory Set Filter Metric
open scoped BigOperators NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OriginalPosteriorKernel
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma originalDatum_measurable {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    Measurable (originalDatum (N := N) ell j) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap id (observationInformation ell j) ≤ _
  simpa only [MeasurableSpace.comap_id] using (observationInformation_le (N := N) ell j)

lemma originalDatum_comap {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    MeasurableSpace.comap (originalDatum (N := N) ell j) inferInstance =
      observationInformation ell j := MeasurableSpace.comap_id

lemma kernelPosteriorTest_eq {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, g (z.1 i)) (physicalObservationLaw μ K)) :
    posteriorTestValue μ ell j g =ᵐ[physicalObservationLaw μ K]
      fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z) := by
  have h := condExp_ae_eq_integral_condDistrib (originalDatum_measurable (N := N) ell j)
    measurable_fst.aemeasurable
    ((Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))).stronglyMeasurable) hi
  simpa only [originalDatum_comap,posteriorTestValue,kernelPosteriorTest,originalRawKernel,Function.comp_def] using h

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterWidth
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Metric
open scoped NNReal

lemma masterWidth_upper {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hs : 0 < s)
    (x : Space) : masterWidth c₁ r₀ s x ≤ c₁*masterBaseDistance r₀ x*s^masterExponent := by
  have hD : 0 < masterBaseDistance r₀ x := hr.trans_le (le_max_right _ _)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_min hD.le hs.le) (min_le_right _ _) masterExponent_nonneg)
    (mul_nonneg hc hD.le)

lemma masterWidth_lower {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hrs : r₀ ≤ s)
    (x : Space) : c₁*r₀^(1+masterExponent) ≤ masterWidth c₁ r₀ s x := by
  have hD : r₀ ≤ masterBaseDistance r₀ x := le_max_right _ _
  rw [Real.rpow_one_add' hr.le (by linarith [masterExponent_pos])]
  simpa only [masterWidth,mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hD (Real.rpow_le_rpow hr.le (le_min hD hrs) masterExponent_nonneg)
      (Real.rpow_nonneg hr.le _) (hr.le.trans hD)) hc

open Set Metric
open scoped NNReal

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_LocalWidthKernel
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped NNReal ContDiff

lemma masterKernel_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ masterKernel c₁ r₀ s g x y := sq_nonneg _

lemma masterKernel_mass {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hgn : ∫ z, (g z)^2 = 1) (x : Space) :
    ∫ y, masterKernel c₁ r₀ s g x y = 1 := by
  unfold masterKernel
  rw [integral_sub_right_eq_self (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) x,
    scaledRealPacket_mass (masterWidth_pos hc hr hs x) g,hgn]

lemma masterKernel_joint_continuous {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Continuous (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2) := by
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have ht := (masterWidth_lipschitz hc.le hr hs).continuous.comp (continuous_fst : Continuous (Prod.fst : Space × Space → Space))
  have hi := ht.inv₀ (fun p => (masterWidth_pos hc hr hs p.1).ne')
  exact (hi.pow 3).mul ((hg.pow 2).comp (hi.smul (continuous_snd.sub continuous_fst)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterKernelFubini
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

open CoulombAnalysis

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombObservation ProbabilityTheory

lemma kernelPosteriorTest_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun x : Configuration N => ∑ i, g (x i)) μ) :
    Integrable (fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z))
      (physicalObservationLaw μ K) := by
  have he : (physicalObservationLaw μ K).map Prod.fst = μ := by
    simp [physicalObservationLaw,Measure.map_fst_prod]
  have hf : Measurable (fun x : Configuration N => ∑ i, g (x i)) :=
    Finset.measurable_sum Finset.univ (fun i _ => hg.comp (measurable_pi_apply i))
  have hi0 : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => ∑ i, g (z.1 i))
      (physicalObservationLaw μ K) := by
    apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [he]
  exact integrable_condExp.congr (kernelPosteriorTest_eq μ ell j hg hi0)

lemma kernelPosteriorTest_mean {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun x : Configuration N => ∑ i, g (x i)) μ) :
    (∫ z, kernelPosteriorTest μ ell j g (originalDatum ell j z) ∂physicalObservationLaw μ K) =
      ∫ x, ∑ i, g (x i) ∂μ := by
  have he : (physicalObservationLaw μ K).map Prod.fst = μ := by
    simp [physicalObservationLaw,Measure.map_fst_prod]
  have hf : Measurable (fun x : Configuration N => ∑ i, g (x i)) :=
    Finset.measurable_sum Finset.univ (fun i _ => hg.comp (measurable_pi_apply i))
  have hi0 : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => ∑ i, g (z.1 i))
      (physicalObservationLaw μ K) := by
    apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [he]
  rw [←integral_congr_ae (kernelPosteriorTest_eq μ ell j hg hi0)]
  rw [posteriorTestValue,integral_condExp (observationInformation_le ell j)]
  exact (integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable).symm.trans (by rw [he])

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_Average
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators
open CoulombAnalysis CoulombPDE CoulombAtom
section Average
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma average_continuous {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (hc : ∀ᵐ sample ∂P, Continuous (u sample)) : Continuous (fun x => ∫ sample, u sample x ∂P) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨C,hC⟩ := hb (closedBall x 1) (isCompact_closedBall x 1)
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => C)
  · exact Eventually.of_forall fun y =>
      (hu.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds x (by norm_num : (0:ℝ)<1)] with y hy
    exact Eventually.of_forall fun sample => hC sample y (ball_subset_closedBall hy)
  · exact integrable_const C
  · exact hc.mono fun _ h => h.continuousAt

end Average

open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators

open CoulombAnalysis CoulombPDE CoulombAtom

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_MasterJointPosterior
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma jointMasterPosterior_nonneg {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (c₁ r₀ s : ℝ) (g : Space → ℝ)
    (z : OriginalDatum N K ell j) (y : Space) :
    0 ≤ jointMasterPosterior μ ell j c₁ r₀ s g z y :=
  integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => masterKernel_nonneg c₁ r₀ s g (x i) y))

lemma jointMasterPosterior_measurable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2) := by
  have hm := (masterKernel_joint_continuous hc hr hs hg).measurable
  have h : StronglyMeasurable (fun p : (OriginalDatum N K ell j × Space) × Configuration N =>
      ∑ i, masterKernel c₁ r₀ s g (p.2 i) p.1.2) :=
    (Finset.measurable_sum _ (fun i _ => hm.comp
      (((measurable_pi_apply i).comp measurable_snd).prodMk measurable_fst.snd))).stronglyMeasurable
  exact (h.integral_kernel_prod_right' (κ := (originalRawKernel μ ell j).comap Prod.fst measurable_fst)).measurable

lemma masterKernel_integrable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hgn : ∫ z, (g z)^2 = 1) (x : Space) :
    Integrable (masterKernel c₁ r₀ s g x) := by
  by_contra h
  have hm := masterKernel_mass hc hr hs hgn x
  rw [integral_undef h] at hm
  norm_num at hm

lemma masterConfigurationKernel_integrable {N : ℕ} (ν : Measure (Configuration N)) [IsFiniteMeasure ν]
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1) :
    Integrable (fun p : Configuration N × Space => ∑ i, masterKernel c₁ r₀ s g (p.1 i) p.2)
      (ν.prod volume) := by
  have hm := (masterKernel_joint_continuous hc hr hs hg).measurable
  apply (integrable_prod_iff ((Finset.measurable_sum _ (fun i _ => hm.comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd))).aestronglyMeasurable)).mpr
  refine ⟨ae_of_all _ (fun x => integrable_finsetSum _ (fun i _ => masterKernel_integrable hc hr hs hgn (x i))),?_⟩
  have he (x : Configuration N) :
      (∫ y, ‖∑ i, masterKernel c₁ r₀ s g (x i) y‖) = (N:ℝ) := by
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun i _ => masterKernel_nonneg c₁ r₀ s g (x i) _))]
    rw [integral_finsetSum _ (fun i _ => masterKernel_integrable hc hr hs hgn (x i))]
    simp only [masterKernel_mass hc hr hs hgn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  change Integrable (fun x : Configuration N => ∫ y, ‖∑ i, masterKernel c₁ r₀ s g (x i) y‖) ν
  simpa only [he] using (integrable_const (N:ℝ) : Integrable (fun _ : Configuration N => (N:ℝ)) ν)

lemma jointMasterPosterior_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1)
    (z : OriginalDatum N K ell j) :
    Integrable (jointMasterPosterior μ ell j c₁ r₀ s g z) :=
  (masterConfigurationKernel_integrable (originalRawKernel μ ell j z) hc hr hs hg hgn).integral_prod_right

lemma jointMasterPosterior_mass {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1)
    (z : OriginalDatum N K ell j) :
    ∫ y, jointMasterPosterior μ ell j c₁ r₀ s g z y = (N:ℝ) := by
  change (∫ y, ∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) y ∂originalRawKernel μ ell j z) = _
  rw [←integral_integral_swap (masterConfigurationKernel_integrable (originalRawKernel μ ell j z) hc hr hs hg hgn)]
  have he (x : Configuration N) : (∫ y, ∑ i, masterKernel c₁ r₀ s g (x i) y) = (N:ℝ) := by
    rw [integral_finsetSum _ (fun i _ => masterKernel_integrable hc hr hs hgn (x i))]
    simp [masterKernel_mass hc hr hs hgn]
  simp_rw [he]
  simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierMasterRegularityBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierMasterRegularity_barrier_scope

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators ContDiff Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation

lemma masterKernel_global_bound {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) {g : Space → ℝ}
    (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖masterKernel c₁ r₀ s g x y‖ ≤ C := by
  have hc2 : HasCompactSupport (fun x => (g x)^2) := hcg.mul_left
  obtain ⟨z,hz⟩ := (hg.pow 2).norm.exists_forall_ge_of_hasCompactSupport hc2.norm
  let δ := c₁*r₀^(1+masterExponent)
  have hδ : 0 < δ := mul_pos hc (Real.rpow_pos_of_pos hr _)
  refine ⟨δ⁻¹^3*‖(g z)^2‖,by positivity,fun x y => ?_⟩
  have hi : (masterWidth c₁ r₀ s x)⁻¹ ≤ δ⁻¹ := by
    apply inv_anti₀ hδ
    exact masterWidth_lower hc.le hr hrs x
  rw [masterKernel,scaledRealPacket_sq (masterWidth_pos hc hr hs x),norm_mul,
    Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (masterWidth_pos hc hr hs x).le) 3)]
  exact mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr (masterWidth_pos hc hr hs x).le) hi 3)
    (hz _) (norm_nonneg _) (by positivity)

attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma masterConfigurationDensity_measurable {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry (masterConfigurationDensity (N := N) c₁ r₀ s g)) := by
  have hm (i : Fin N) : Measurable (fun p : Configuration N × Space =>
      masterKernel c₁ r₀ s g (p.1 i) p.2) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.comp
      (f := fun p : Configuration N × Space => (p.1 i,p.2))
      (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)
  exact Finset.measurable_sum Finset.univ (fun i _ => hm i)

lemma masterConfigurationDensity_continuous {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g)
    (z : Configuration N) : Continuous (masterConfigurationDensity c₁ r₀ s g z) := by
  have ht (i : Fin N) : Continuous (fun y : Space => masterKernel c₁ r₀ s g (z i) y) :=
    (masterKernel_joint_continuous hc hr hs hg).comp
      (f := fun y : Space => (z i,y)) (continuous_const.prodMk continuous_id)
  exact continuous_finsetSum Finset.univ (fun i _ => ht i)

lemma masterConfigurationDensity_bound {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z y, ‖masterConfigurationDensity (N := N) c₁ r₀ s g z y‖ ≤ C := by
  obtain ⟨C,hCn,hC⟩ := masterKernel_global_bound hc hr hs hrs hg hcg
  refine ⟨N*C,by positivity,fun z y => ?_⟩
  calc
    _ ≤ ∑ i : Fin N, ‖masterKernel c₁ r₀ s g (z i) y‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, C := Finset.sum_le_sum (fun i _ => hC (z i) y)
    _ = N*C := by simp

lemma masterConfigurationDensity_deterministicBound {N : ℕ} {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    DeterministicLocalBound (masterConfigurationDensity (N := N) c₁ r₀ s g) := by
  obtain ⟨C,_,hC⟩ := masterConfigurationDensity_bound (N := N) hc hr hs hrs hg hcg
  exact fun _ _ => ⟨C,fun z y _ => hC z y⟩

lemma jointMasterPosterior_continuous {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (d : OriginalDatum N K ell j) :
    Continuous (jointMasterPosterior μ ell j c₁ r₀ s g d) := by
  exact average_continuous (masterConfigurationDensity_measurable hc hr hs hg)
    (masterConfigurationDensity_deterministicBound hc hr hs hrs hg hcg)
    (Eventually.of_forall (masterConfigurationDensity_continuous hc hr hs hg))

lemma jointMasterPosterior_global_bound {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d y, ‖jointMasterPosterior μ ell j c₁ r₀ s g d y‖ ≤ C := by
  obtain ⟨C,hCn,hC⟩ := masterConfigurationDensity_bound (N := N) hc hr hs hrs hg hcg
  refine ⟨C,hCn,fun d y => ?_⟩
  calc
    _ ≤ ∫ _ : Configuration N, C ∂originalRawKernel μ ell j d :=
      norm_integral_le_of_norm_le (integrable_const C) (Eventually.of_forall fun z => hC z y)
    _ = C := by simp

end CoulombBarrier

end Work_BarrierMasterRegularity_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierObservationTowerBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma originalMasterField_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry (originalMasterField μ ell j c₁ r₀ s g)) :=
  (jointMasterPosterior_measurable μ ell j hc hr hs hg).comp
    (((originalDatum_measurable ell j).comp measurable_fst).prodMk measurable_snd)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BoundedL1PotentialBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma bounded_coulomb_majorant {ρ : TFSpace → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x z : TFSpace) :
    ρ z/‖x-z‖ ≤ M*truncatedCoulomb 1 (x-z)+ρ z := by
  by_cases hd : ‖x-z‖ < 1
  · rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hd)]
    have hh := mul_le_mul_of_nonneg_right (hb z) (inv_nonneg.mpr (norm_nonneg (x-z)))
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    linarith [hn z]
  · rw [truncatedCoulomb,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hd),mul_zero,zero_add]
    have hd' : 1 ≤ ‖x-z‖ := le_of_not_gt hd
    exact (div_le_self (hn z) hd')

lemma bounded_invSquare_majorant {ρ : TFSpace → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x z : TFSpace) :
    ρ z*‖x-z‖⁻¹^2 ≤ M*truncatedInvSquare 1 (x-z)+ρ z := by
  by_cases hd : ‖x-z‖ < 1
  · rw [truncatedInvSquare,indicator_of_mem (mem_ball_zero_iff.mpr hd)]
    have hh := mul_le_mul_of_nonneg_right (hb z) (sq_nonneg ‖x-z‖⁻¹)
    linarith [hn z]
  · rw [truncatedInvSquare,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hd),mul_zero,zero_add]
    have hi : ‖x-z‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_not_gt hd)
    have hi0 := inv_nonneg.mpr (norm_nonneg (x-z))
    have hs : ‖x-z‖⁻¹^2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hs (hn z)).trans_eq (mul_one _)

lemma bounded_L1_potential_integrable {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x : TFSpace) :
    Integrable (fun z => ρ z/‖x-z‖) := by
  have hk : Integrable (fun z => truncatedCoulomb 1 (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable 1)
  apply ((hk.const_mul M).add hi).mono' (hm.div (measurable_const.sub measurable_id).norm).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z/‖x-z‖‖ ≤ M*truncatedCoulomb 1 (x-z)+ρ z
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (norm_nonneg _))]
    exact bounded_coulomb_majorant hM hn hb x z

lemma bounded_L1_potential_difference {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x y : TFSpace) :
    |tfPotential ρ x-tfPotential ρ y| ≤ (4*Real.pi*M+∫ z, ρ z)*‖x-y‖ := by
  have hpi (w : TFSpace) := bounded_L1_potential_integrable hm hi hM hn hb w
  let A (w z : TFSpace) := M*truncatedInvSquare 1 (w-z)+ρ z
  have hk (w : TFSpace) : Integrable (fun z => truncatedInvSquare 1 (w-z)) :=
    (tfSubMap_preserving w).integrable_comp (truncatedInvSquare_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedInvSquare_integrable 1)
  have hAi (w : TFSpace) : Integrable (A w) := ((hk w).const_mul M).add hi
  have hAm (w : TFSpace) : (∫ z, A w z) = 4*Real.pi*M+∫ z, ρ z := by
    dsimp only [A]
    rw [integral_add ((hk w).const_mul M) hi,integral_const_mul,integral_sub_left_eq_self,
      truncatedInvSquare_integral (by norm_num : (0:ℝ) < 1)]
    ring
  have he : (∫ z, ρ z/‖x-z‖-ρ z/‖y-z‖) = tfPotential ρ x-tfPotential ρ y :=
    integral_sub (hpi x) (hpi y)
  rw [←he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ z, (‖x-y‖/2)*(A x z+A y z) := by
      apply integral_mono_ae ((hpi x).sub (hpi y)).abs (((hAi x).add (hAi y)).const_mul _)
      filter_upwards [volume.ae_ne x,volume.ae_ne y] with z hzx hzy
      change |ρ z/‖x-z‖-ρ z/‖y-z‖| ≤ _
      rw [div_eq_mul_inv,div_eq_mul_inv,←mul_sub,abs_mul,abs_of_nonneg (hn z)]
      calc
        _ ≤ ρ z*(‖x-y‖*(‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2) :=
          mul_le_mul_of_nonneg_left (coulomb_inv_difference hzx hzy) (hn z)
        _ = (‖x-y‖/2)*(ρ z*‖x-z‖⁻¹^2+ρ z*‖y-z‖⁻¹^2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
          (bounded_invSquare_majorant hM hn hb x z) (bounded_invSquare_majorant hM hn hb y z)) (by positivity)
    _ = _ := by
      rw [integral_const_mul,integral_add (hAi x) (hAi y),hAm,hAm]
      ring

lemma bounded_L1_potential_lipschitz {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) :
    LipschitzWith ⟨4*Real.pi*M+∫ z, ρ z,add_nonneg (by positivity) (integral_nonneg hn)⟩ (tfPotential ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖tfPotential ρ x-tfPotential ρ y‖ ≤ (4*Real.pi*M+∫ z, ρ z)*‖x-y‖
  simpa only [Real.norm_eq_abs] using bounded_L1_potential_difference hm hi hM hn hb x y

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ActualPosteriorCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma jointMasterPosterior_potential_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun z : OriginalDatum N K ell j =>
      tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g z) y) := by
  have hm : Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2 / ‖y-p.2‖) :=
    (jointMasterPosterior_measurable μ ell j hc hr hs hg).div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_InverseThresholdLimitBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma localTFResponse_rescale {a : ℝ} (ha : 0 < a) (h : ℝ) :
    a^6*localTFResponse h = localTFResponse (a^4*h) := by
  have he : max (a^4*h) 0 = a^4*max h 0 := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg ha.le _),mul_zero]
  have hT := tfKinetic_pos
  unfold localTFResponse
  rw [he,mul_div_assoc,Real.mul_rpow (pow_nonneg ha.le _) (by positivity),
    ←Real.rpow_natCast a 4,←Real.rpow_mul ha.le]
  norm_num

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PosteriorSubmeanBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

open CoulombAnalysis CoulombObservation CoulombBarrier

open MeasureTheory Set Metric

open CoulombAnalysis CoulombObservation CoulombBarrier

lemma originalQueryDensity_bounded_L1 {N K : ℕ} (F : fermionGraph N)
    (r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ),
      Measurable (originalQueryDensity F r j c₁ r₀ s z) ∧
      Integrable (originalQueryDensity F r j c₁ r₀ s z) ∧
      (∀ y, 0 ≤ originalQueryDensity F r j c₁ r₀ s z y) ∧
      (∀ y, originalQueryDensity F r j c₁ r₀ s z y ≤ M) := by
  let ell := fun k : Fin K => dyadicObservationWidth r k
  have hm := originalMasterField_measurable (graphRawLaw F) ell j hc hr₀ hs
    canonicalRealPacket_smooth.continuous
  obtain ⟨M,hM,hb⟩ := jointMasterPosterior_global_bound (graphRawLaw F) ell j hc hr₀ hs hrs
    canonicalRealPacket_smooth.continuous canonicalRealPacket_compact
  refine ⟨M,hM,fun z => ⟨?_,?_,?_,?_⟩⟩
  · exact hm.comp ((measurable_const (a := z)).prodMk measurable_id)
  · exact jointMasterPosterior_integrable (graphRawLaw F) ell j hc hr₀ hs
      canonicalRealPacket_smooth.continuous canonicalRealPacket_normalized (originalDatum ell j z)
  · exact jointMasterPosterior_nonneg (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)
  · intro y
    apply (le_abs_self _).trans
    change |jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket (originalDatum ell j z) y| ≤ M
    simpa only [Real.norm_eq_abs] using hb (originalDatum ell j z) y

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_OriginalFieldOscillationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OriginalFieldOscillation_barrier_scope

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma originalQueryField_continuousOn_punctured {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :
    ContinuousOn (originalQueryField F Z lam r j c₁ r₀ s z) {0}ᶜ := by
  obtain ⟨M,hM,hρ⟩ := originalQueryDensity_bounded_L1 F r j hc hr₀ hs hrs
  have hp := (bounded_L1_potential_lipschitz (hρ z).1 (hρ z).2.1 hM
    (hρ z).2.2.1 (hρ z).2.2.2).continuous
  apply ((continuousOn_const.div continuous_norm.continuousOn ?_).sub continuousOn_const).sub hp.continuousOn
  intro x hx
  exact norm_ne_zero_iff.mpr hx

end CoulombAtom

end Work_OriginalFieldOscillation_barrier_scope

open MeasureTheory Filter Set Metric

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierRetainedComparisonBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierRetainedComparison_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma pow_four_three_halves {d : ℝ} (hd : 0 ≤ d) :
    (d^4)^(3/2:ℝ) = d^6 := by
  rw [←Real.rpow_natCast d 4,←Real.rpow_mul hd]
  norm_num

lemma scaled_positive_reaction {d u : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u) :
    (d^4*u)^(3/2:ℝ) = d^6*u^(3/2:ℝ) := by
  rw [Real.mul_rpow (by positivity) hu,pow_four_three_halves hd]

end Work_BarrierRetainedComparison_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology ContDiff

open CoulombAnalysis CoulombPDE CoulombAtom

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitialLipschitzBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma DeterministicLocalLipschitz.locallyLipschitz {Ω : Type*} {u : Ω → TFSpace → ℝ}
    (h : DeterministicLocalLipschitz u) (sample : Ω) : LocallyLipschitz (u sample) := by
  intro x
  obtain ⟨K,t,ht,hL⟩ := h x
  exact ⟨K,t,ht,hL sample⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_Error
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma compactBound_integrable_prod {p : Ω → TFSpace → ℝ}
    (hm : Measurable (Function.uncurry p)) (hb : DeterministicLocalBound p)
    {R : ℝ} (hs : ∀ sample x, R < ‖x‖ → p sample x = 0) :
    Integrable (Function.uncurry p) (P.prod volume) := by
  obtain ⟨C,hC⟩ := hb (closedBall 0 R) (isCompact_closedBall 0 R)
  have hi : Integrable ((closedBall (0 : TFSpace) R).indicator (fun _ => C)) volume :=
    (integrableOn_const (C := C) (isCompact_closedBall (0 : TFSpace) R).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  apply (hi.comp_snd P).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : z.2 ∈ closedBall (0 : TFSpace) R
    · rw [indicator_of_mem hz]
      exact hC z.1 z.2 hz
    · rw [indicator_of_notMem hz,Function.uncurry_apply_pair,
        hs z.1 z.2 (lt_of_not_ge (by simpa only [mem_closedBall,dist_zero_right] using hz)),norm_zero]

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierNuclearScaleBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierNuclearScale_barrier_scope

open Filter
open scoped Topology

namespace CoulombAtom
open CoulombObservation

lemma nuclear_radius_relation {Z ε : ℝ} (hZ : 0 < Z) :
    Z*(ε*Z^(-1/3:ℝ))^3 = ε^3 := by
  rw [mul_pow,←Real.rpow_natCast (Z^(-1/3:ℝ)) 3,←Real.rpow_mul hZ.le]
  norm_num [Real.rpow_neg_one]
  field_simp

end CoulombAtom

end Work_BarrierNuclearScale_barrier_scope

open Filter Set
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitialInvariantBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierInitialInvariant_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma IsNuclearBarrier.locallyLipschitz_offset {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ a p : Ω → TFSpace → ℝ} {Z k B C r T η : ℝ}
    (h : IsNuclearBarrier P μ Z k B C r T η a p) (sample : Ω) :
    LocallyLipschitz (a sample) := h.uniform_lipschitz_offset.locallyLipschitz sample

end Work_BarrierInitialInvariant_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma nonneg_bounded_deterministicBound {Ω : Type*} {p : Ω → TFSpace → ℝ}
    (hn : ∀ sample x, 0 ≤ p sample x) {L : ℝ} (hb : ∀ sample x, p sample x ≤ L) :
    DeterministicLocalBound p := fun _ _ => ⟨L,fun sample x _ => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hn sample x)] using hb sample x⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierOriginalForgettingBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory
open scoped Topology BigOperators

open CoulombAtom CoulombAnalysis

lemma barrierErrorExponent_one_le : 1 ≤ barrierErrorExponent := by
  norm_num [barrierErrorExponent,masterExponent]

lemma barrierErrorExponent_pos : 0 < barrierErrorExponent := lt_of_lt_of_le (by norm_num) barrierErrorExponent_one_le

lemma total_barrier_budget_tendsto_zero {ι : Type*} {F : Filter ι}
    {s : ι → ℝ} (hs : Tendsto s F (𝓝 0)) (C : ℝ) :
    Tendsto (fun j => 5184*(s j)^32+C*(s j)^barrierErrorExponent) F (𝓝 0) := by
  have h₁ := (hs.pow 32).const_mul 5184
  have h₂ := (hs.rpow_const (Or.inr barrierErrorExponent_pos.le)).const_mul C
  simpa only [zero_pow (by norm_num : (32:ℕ) ≠ 0),
    Real.zero_rpow barrierErrorExponent_pos.ne',mul_zero,zero_add] using h₁.add h₂

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierQuantitativeStepBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierQuantitativeStep_barrier_scope

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

lemma IsNuclearBarrier.mono_cap {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ a p : Ω → TFSpace → ℝ} {Z k B C C' r T η : ℝ}
    (old : IsNuclearBarrier P μ Z k B C r T η a p) (hC : C ≤ C') :
    IsNuclearBarrier P μ Z k B C' r T η a p := by
  refine { old with upper := fun sample x hx => (old.upper sample x hx).trans ?_ }
  exact div_le_div_of_nonneg_right hC (pow_nonneg (norm_nonneg _) _)

end Work_BarrierQuantitativeStep_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom CoulombAnalysis

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_NuclearDilationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombPDE

lemma tfPotential_dilation {b : ℝ} (hb : 0 < b) (ρ : TFSpace → ℝ) (x : TFSpace) :
    tfPotential (tfDilation b ρ) x = b^4*tfPotential ρ (b • x) := by
  have he (y : TFSpace) : tfDilation b ρ y/‖x-y‖ =
      b^7*(ρ (b • y)/‖b • x-b • y‖) := by
    rw [tfDilation,←smul_sub,norm_smul,Real.norm_of_nonneg hb.le]
    field_simp
  simp only [tfPotential,he,integral_const_mul]
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun y : TFSpace => ρ y/‖b • x-y‖) b (hR := hb.le),space_finrank]
  simp only [smul_eq_mul]
  field_simp

lemma nuclearField_dilation {b : ℝ} (hb : 0 < b) (Z : ℝ) (x : TFSpace) :
    b^4*nuclearField Z (b • x) = nuclearField (b^3*Z) x := by
  simp only [nuclearField,norm_smul,Real.norm_of_nonneg hb.le]
  field_simp

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CorrectionPotentialSmallBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

lemma bounded_compact_mass_le {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {L S : ℝ} (_hL : 0 ≤ L) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ L)
    (hs : ∀ z, S < ‖z‖ → ρ z = 0) :
    Integrable ρ ∧ (∫ z, ρ z) ≤ volume.real (closedBall (0:TFSpace) S)*L := by
  have hmajor : ∀ z, ρ z ≤ (closedBall (0:TFSpace) S).indicator (fun _ => L) z := by
    intro z
    by_cases hz : ‖z‖ ≤ S
    · rw [indicator_of_mem (mem_closedBall_zero_iff.mpr hz)]
      exact hb z
    · rw [indicator_of_notMem (by simpa only [mem_closedBall_zero_iff] using hz),hs z (lt_of_not_ge hz)]
  have hI : Integrable ((closedBall (0:TFSpace) S).indicator (fun _ => L)) :=
    (integrableOn_const (C := L) measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  have hρ : Integrable ρ := hI.mono' hm.aestronglyMeasurable (ae_of_all _ fun z => by
    simpa only [Real.norm_of_nonneg (hn z)] using hmajor z)
  refine ⟨hρ,(integral_mono hρ hI hmajor).trans_eq ?_⟩
  rw [integral_indicator measurableSet_closedBall,setIntegral_const,smul_eq_mul]

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_SelectedBarrierTransferBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma scaled_screened_field_eq {s : ℝ} (hs : 0 < s) (Z : ℝ)
    (μ : TFSpace → ℝ) (x : TFSpace) :
    s^4*(nuclearField Z (s • x)-tfPotential μ (s • x)) =
      nuclearField (s^3*Z) x-tfPotential (tfDilation s μ) x := by
  rw [mul_sub,nuclearField_dilation hs,tfPotential_dilation hs]

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierDataSelectionBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierDataSelection_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma select_small_masses {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f g : Ω → ℝ}
    (hf : Integrable f P) (hg : Integrable g P)
    (hfn : ∀ sample, 0 ≤ f sample) (hgn : ∀ sample, 0 ≤ g sample)
    {A : Set Ω} (hA : MeasurableSet A) {W : Ω → Prop} (hW : ∀ᵐ sample ∂P, W sample)
    {η τ δ : ℝ} (hδ : 0 < δ) (hfm : (∫ sample, f sample ∂P) ≤ η)
    (hgm : (∫ sample, g sample ∂P) ≤ τ) (hbudget : η+τ/δ+P.real Aᶜ < 1) :
    ∃ sample, sample ∈ A ∧ W sample ∧ f sample < 1 ∧ g sample < δ := by
  let cost : Ω → ℝ := fun sample => f sample+g sample/δ+Aᶜ.indicator (fun _ => (1:ℝ)) sample
  have hi : Integrable (Aᶜ.indicator (fun _ : Ω => (1:ℝ))) P :=
    (integrable_const _).indicator hA.compl
  have hfg : Integrable (fun sample => f sample+g sample/δ) P := hf.add (hg.div_const δ)
  have hc : Integrable cost P := hfg.add hi
  have hcm : (∫ sample, cost sample ∂P) < 1 := by
    change (∫ sample, f sample+g sample/δ+Aᶜ.indicator (fun _ => (1:ℝ)) sample ∂P) < 1
    rw [integral_add hfg hi,integral_add hf (hg.div_const δ),
      integral_div,integral_indicator hA.compl,setIntegral_const,smul_eq_mul,mul_one]
    have hh := div_le_div_of_nonneg_right hgm hδ.le
    linarith
  obtain ⟨sample,hω,hcω⟩ := exists_notMem_null_le_integral hc (show P {sample | ¬ W sample} = 0 by
    simpa only [ae_iff] using hW)
  have hsmall : cost sample < 1 := hcω.trans_lt hcm
  have hgn' : 0 ≤ g sample/δ := div_nonneg (hgn sample) hδ.le
  have hin : 0 ≤ Aᶜ.indicator (fun _ => (1:ℝ)) sample := indicator_nonneg (fun _ _ => by norm_num) _
  have hmA : sample ∈ A := by
    by_contra hh
    have hi' : Aᶜ.indicator (fun _ : Ω => (1:ℝ)) sample = 1 := indicator_of_mem hh _
    dsimp only [cost] at hsmall
    rw [hi'] at hsmall
    linarith [hfn sample]
  refine ⟨sample,hmA,not_not.mp hω,?_,?_⟩
  · dsimp only [cost] at hsmall
    linarith
  · apply (div_lt_one hδ).mp
    dsimp only [cost] at hsmall
    linarith [hfn sample]

lemma IsNuclearBarrier.integrable_error_mass {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ a p : Ω → TFSpace → ℝ}
    {Z k B C r T η : ℝ} (old : IsNuclearBarrier P μ Z k B C r T η a p) :
    Integrable (fun sample => ∫ x, p sample x) P := by
  obtain ⟨L,hL⟩ := old.bounded_error
  exact (compactBound_integrable_prod old.measurable_error
    (nonneg_bounded_deterministicBound old.nonneg_error hL) old.support_error).integral_prod_left

theorem IsNuclearBarrier.select_data {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ a p : Ω → TFSpace → ℝ}
    {Z k B C r T η : ℝ} (old : IsNuclearBarrier P μ Z k B C r T η a p)
    {g : Ω → ℝ} (hg : Integrable g P) (hgn : ∀ sample, 0 ≤ g sample)
    {A : Set Ω} (hA : MeasurableSet A) {τ δ : ℝ} (hδ : 0 < δ)
    (hgm : (∫ sample, g sample ∂P) ≤ τ) (hbudget : η+τ/δ+P.real Aᶜ < 1) :
    ∃ sample, sample ∈ A ∧
      WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a sample x)
        (fun x => innerSource r (μ sample) (p sample) x+
          outerCoefficient r x*reaction k (nuclearField Z x+a sample x)) ∧
      (∫ x, p sample x) < 1 ∧ g sample < δ := by
  exact select_small_masses old.integrable_error_mass hg
    (fun sample => integral_nonneg (old.nonneg_error sample)) hgn hA old.weak hδ old.mass hgm hbudget

end Work_BarrierDataSelection_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SelectionNumerics
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter Set Metric
open scoped Topology
namespace CoulombAnalysis
open CoulombAtom

lemma tfDilation_exterior_mass {s : ℝ} (hs : 0 < s) (R : ℝ) (μ : TFSpace → ℝ) :
    (∫ x in {x : TFSpace | R < ‖x‖}, tfDilation s μ x) =
      s^3*(∫ x in {x : TFSpace | s*R < ‖x‖}, μ x) := by
  have hE : MeasurableSet {x : TFSpace | R < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  have hEs : MeasurableSet {x : TFSpace | s*R < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  rw [←integral_indicator hE,←integral_indicator hEs,←tfDilation_mass hs]
  congr 1
  funext x
  have hx : s*R < ‖s • x‖ ↔ R < ‖x‖ := by
    rw [norm_smul,Real.norm_of_nonneg hs.le,mul_lt_mul_iff_right₀ hs]
  change {x : TFSpace | R < ‖x‖}.indicator (tfDilation s μ) x = s^6*{x : TFSpace | s*R < ‖x‖}.indicator μ (s • x)
  by_cases hh : R < ‖x‖
  · rw [indicator_of_mem (show x ∈ {x : TFSpace | R < ‖x‖} from hh),
      indicator_of_mem (show s • x ∈ {x : TFSpace | s*R < ‖x‖} from hx.mpr hh)]
    rfl
  · rw [indicator_of_notMem (show x ∉ {x : TFSpace | R < ‖x‖} from hh),
      indicator_of_notMem (show s • x ∉ {x : TFSpace | s*R < ‖x‖} from fun h => hh (hx.mp h)),mul_zero]

end CoulombAnalysis
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma selectedDyadicIndex_spec {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t) :
    (2:ℝ)^(selectedDyadicIndex r t)*r ≤ t ∧
      t < 2*((2:ℝ)^(selectedDyadicIndex r t)*r) := by
  have h : ∃ J : ℕ, (2:ℝ)^J*r ≤ t ∧ t < 2*((2:ℝ)^J*r) := by
    obtain ⟨J,hJ,hJ'⟩ := exists_nat_pow_near ((one_le_div hr).mpr hrt) (by norm_num : (1:ℝ) < 2)
    refine ⟨J,(le_div_iff₀ hr).mp hJ,?_⟩
    have hh := (div_lt_iff₀ hr).mp hJ'
    rw [pow_succ] at hh
    nlinarith only [hh]
  simpa only [selectedDyadicIndex,dite_eq_left h] using Classical.choose_spec h

lemma selectedDyadicIndex_radius {r s l : ℝ} (hr : 0 < r) (hs : 0 < s) (hl : 1 ≤ l)
    (hrs : r ≤ s/l) :
    let u := (2:ℝ)^(selectedDyadicIndex r (s/l))*r
    0 < u ∧ u ≤ s ∧ 1/(2*l) ≤ u/s ∧ u/s ≤ l⁻¹ ∧ s*l ≤ (2*l^2)*u := by
  let u := (2:ℝ)^(selectedDyadicIndex r (s/l))*r
  have hspec := selectedDyadicIndex_spec hr hrs
  have hlp : 0 < l := zero_lt_one.trans_le hl
  have hu : 0 < u := mul_pos (pow_pos (by norm_num) _) hr
  have hlu : l*u ≤ s := by nlinarith [(le_div_iff₀ hlp).mp hspec.1]
  have hslu : s < 2*l*u := by nlinarith [(div_lt_iff₀ hlp).mp hspec.2]
  refine ⟨hu,?_,?_,?_,?_⟩
  · exact hspec.1.trans (div_le_self hs.le hl)
  · apply (le_div_iff₀ hs).mpr
    have hh : s/(2*l) ≤ u := (div_le_iff₀ (show 0 < 2*l by positivity)).mpr (by nlinarith only [hslu])
    simpa only [u,one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  · exact (div_le_iff₀ hs).mpr (by simpa only [one_div,mul_comm,div_eq_mul_inv] using hspec.1)
  · nlinarith [mul_nonneg hlp.le (sub_nonneg.mpr hslu.le)]

lemma fixed_target_nuclear_radius_eventually {ι : Type*} {F : Filter ι} {Z s : ι → ℝ}
    (hZ : ∀ i, 0 < Z i) (hs : ∀ i, 0 < s i)
    (hscale : Tendsto (fun i => Z i*(s i)^3) F atTop)
    {ε l : ℝ} (hε : 0 < ε) (hl : 0 < l) :
    ∀ᶠ i in F, ε*(Z i)^(-1/3:ℝ) ≤ s i/l := by
  filter_upwards [hscale.eventually_ge_atTop (ε^3*l^3)] with i hi
  apply (pow_le_pow_iff_left₀
    (mul_nonneg hε.le (Real.rpow_nonneg (hZ i).le _))
    (div_nonneg (hs i).le hl.le) (by norm_num : 3 ≠ 0)).mp
  apply (mul_le_mul_iff_right₀ (hZ i)).mp
  rw [nuclear_radius_relation (hZ i),div_pow,←mul_div_assoc]
  exact (le_div_iff₀ (pow_pos hl 3)).mpr hi

end CoulombBarrier

end

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_GraphWeightIntegral
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter
open scoped BigOperators
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

lemma graph_weight_integrable {N : ℕ} (F : fermionGraph N)
    (w : Configuration N → ℝ) (hm : Measurable w) {A : ℝ} (hb : ∀ x, ‖w x‖ ≤ A) :
    Integrable w (graphRawLaw F) :=
  Integrable.of_bound hm.aestronglyMeasurable A (ae_of_all _ hb)

end
open MeasureTheory Filter
open scoped BigOperators
attribute [local irreducible] graphComponent fermionGraph weakGraph FermionMultiplier.apply

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_OriginalTFScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma scaled_priced_field {s : ℝ} (hs : 0 < s) (Z : ℝ) (μ : TFSpace → ℝ) (x : TFSpace) :
    s^4*(Z/‖s • x‖-1/s^4-tfPotential μ (s • x)) =
      nuclearField (s^3*Z) x-tfPotential (tfDilation s μ) x-1 := by
  have hh := scaled_screened_field_eq hs Z μ x
  unfold nuclearField at hh ⊢
  have hone : s^4*(1/s^4) = 1 := mul_one_div_cancel (pow_ne_zero _ hs.ne')
  nlinarith only [hh,hone]

lemma rpow_max_scale {s H : ℝ} (hs : 0 ≤ s) :
    s^6*(max H 0)^(3/2:ℝ) = (max (s^4*H) 0)^(3/2:ℝ) := by
  rw [←scaled_positive_reaction hs (le_max_right H 0)]
  congr 1
  rcases le_total H 0 with hH | hH
  · rw [max_eq_right hH,max_eq_right (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hs 4) hH),mul_zero]
  · rw [max_eq_left hH,max_eq_left (mul_nonneg (pow_nonneg hs 4) hH)]

lemma original_TF_scale {s Z k ε C : ℝ} {μ : TFSpace → ℝ} {x : TFSpace}
    (hs : 0 < s) (hx : x ≠ 0)
    (hcap : ‖s • x‖^4*(Z/‖s • x‖-1/s^4-tfPotential μ (s • x)) ≤ C)
    (hTF : |μ (s • x)-k*(max (Z/‖s • x‖-1/s^4-tfPotential μ (s • x)) 0)^(3/2:ℝ)| ≤ ε/‖s • x‖^6) :
    nuclearField (s^3*Z) x-tfPotential (tfDilation s μ) x ≤ 1+C/‖x‖^4 ∧
    |tfDilation s μ x-k*(max (nuclearField (s^3*Z) x-tfPotential (tfDilation s μ) x-1) 0)^(3/2:ℝ)| ≤ ε/‖x‖^6 := by
  have hnorm : ‖s • x‖ = s*‖x‖ := by rw [norm_smul,Real.norm_of_nonneg hs.le]
  have hsf := scaled_priced_field hs Z μ x
  let H := Z/‖s • x‖-1/s^4-tfPotential μ (s • x)
  constructor
  · have hh : ‖x‖^4*(s^4*H) ≤ C := by simpa only [hnorm,mul_pow,mul_assoc,mul_left_comm,mul_comm,H] using hcap
    have hdiv : s^4*H ≤ C/‖x‖^4 := (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hx) 4)).mpr (by nlinarith only [hh])
    dsimp only [H] at hdiv
    rw [hsf] at hdiv
    linarith
  · have hh := mul_le_mul_of_nonneg_left hTF (pow_nonneg hs.le 6)
    have hrhs : s^6*(ε/‖s • x‖^6) = ε/‖x‖^6 := by rw [hnorm,mul_pow]; field_simp
    rw [hrhs,←abs_of_nonneg (pow_nonneg hs.le 6),←abs_mul] at hh
    change |s^6*(μ (s • x)-k*(max H 0)^(3/2:ℝ))| ≤ _ at hh
    rw [mul_sub,show s^6*(k*(max H 0)^(3/2:ℝ)) = k*(s^6*(max H 0)^(3/2:ℝ)) by ring,
      rpow_max_scale hs.le] at hh
    dsimp only [H] at hh
    rw [hsf] at hh
    exact hh

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TinyProbabilityFloorBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombBarrier

lemma tinyProbabilityFloor_pos {Z u : ℝ} (hZ : 0 ≤ Z) (hu : 0 < u) :
    0 < tinyProbabilityFloor Z u := by unfold tinyProbabilityFloor; positivity

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_OwnProbabilityRareCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OwnProbabilityRareCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma originalQueryField_info_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (y : Space) :
    Measurable[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      (fun z => originalQueryField F Z lam r j c₁ r₀ s z y) :=
  measurable_const.sub (jointMasterPosterior_potential_measurable (graphRawLaw F)
    (fun k : Fin K => dyadicObservationWidth r k) j y hc hr₀ hs canonicalRealPacket_smooth.continuous)

end Work_OwnProbabilityRareCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_InverseNetEventsBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

lemma originalQueryDensity_info_measurable {N K : ℕ} (F : fermionGraph N)
    (r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (y : Space) :
    Measurable[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      (fun z => originalQueryDensity F r j c₁ r₀ s z y) := by
  exact (jointMasterPosterior_measurable (graphRawLaw F)
    (fun k : Fin K => dyadicObservationWidth r k) j hc hr₀ hs
    canonicalRealPacket_smooth.continuous).comp (measurable_id.prodMk measurable_const)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_SelectedScreenedProfileBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfDensityCoefficient_pos : 0 < tfDensityCoefficient := by
  unfold tfDensityCoefficient
  have hh := tfKinetic_pos
  positivity
end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellTelescoping
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped BigOperators
open CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

lemma rawExteriorCount_nonneg {N : ℕ} (r : ℝ) (x : Configuration N) : 0 ≤ rawExteriorCount r x := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> norm_num
lemma rawExteriorCount_le {N : ℕ} (r : ℝ) (x : Configuration N) : rawExteriorCount r x ≤ N := by
  calc _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
       _ = _ := by simp
lemma rawExteriorCount_measurable {N : ℕ} (r : ℝ) : Measurable (rawExteriorCount (N := N) r) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.ite (measurableSet_le measurable_const (continuous_norm.measurable.comp (measurable_pi_apply i))) measurable_const
lemma rawExteriorCount_integrable {N : ℕ} (F : fermionGraph N) (r : ℝ) :
    Integrable (rawExteriorCount r) (graphRawLaw F) :=
  graph_weight_integrable F _ (rawExteriorCount_measurable r) (fun x => by
    rw [Real.norm_of_nonneg (rawExteriorCount_nonneg r x)]; exact rawExteriorCount_le r x)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_MasterExteriorStatistic
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter Set Metric
open scoped BigOperators
open CoulombObservation

lemma masterWidth_le_half_bound {c r₀ s R : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/2)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hrR : r₀ ≤ R)
    {x : Space} (hx : ‖x‖ ≤ R) : masterWidth c r₀ s x ≤ R/2 := by
  have hpow : s^masterExponent ≤ 1 := Real.rpow_le_one hs.le hs1 masterExponent_nonneg
  have hbase : masterBaseDistance r₀ x ≤ R := max_le hx hrR
  have hp : 0 ≤ masterBaseDistance r₀ x := (norm_nonneg x).trans (le_max_left _ _)
  calc
    _ ≤ c*masterBaseDistance r₀ x*s^masterExponent := masterWidth_upper hc hr hs x
    _ ≤ c*masterBaseDistance r₀ x*1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hc hp)
    _ ≤ R/2 := by nlinarith [hr.le.trans hrR]

lemma masterKernel_zero_outer {c r₀ s R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1/2)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hrR : r₀ ≤ R)
    {g : Space → ℝ} (hgs : tsupport g ⊆ ball 0 1)
    {x y : Space} (hx : ‖x‖ ≤ R) (hy : 2*R < ‖y‖) : masterKernel c r₀ s g x y = 0 := by
  have hb := masterWidth_le_half_bound hc.le hc1 hr hs hs1 hrR hx
  have hn : ‖y‖ ≤ ‖y-x‖+‖x‖ := norm_le_norm_sub_add y x
  have he : scaledRealPacket (masterWidth c r₀ s x) g (y-x) = 0 := by
    by_contra hh
    have hv := scaledRealPacket_support (masterWidth_pos hc hr hs x) hgs hh
    linarith [hr.le.trans hrR]
  simp only [masterKernel,he,zero_pow (by norm_num : (2:ℕ) ≠ 0)]

lemma masterTailTest_nonneg (c r₀ s R : ℝ) (g : Space → ℝ) (x : Space) :
    0 ≤ masterTailTest c r₀ s R g x :=
  integral_nonneg (fun y => masterKernel_nonneg c r₀ s g x y)

lemma masterTailTest_measurable {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (R : ℝ) {g : Space → ℝ} (hg : Continuous g) : Measurable (masterTailTest c r₀ s R g) :=
  (masterKernel_joint_continuous hc hr hs hg).measurable.stronglyMeasurable.integral_prod_right.measurable

lemma masterTailTest_le_one {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (R : ℝ) {g : Space → ℝ} (hgn : ∫ z, (g z)^2 = 1) (x : Space) :
    masterTailTest c r₀ s R g x ≤ 1 :=
  (setIntegral_le_integral (masterKernel_integrable hc hr hs hgn x)
    (ae_of_all _ (fun y => masterKernel_nonneg c r₀ s g x y))).trans_eq
      (masterKernel_mass hc hr hs hgn x)

lemma masterTailTest_zero_inner {c r₀ s R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1/2)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hrR : r₀ ≤ R)
    {g : Space → ℝ} (hgs : tsupport g ⊆ ball 0 1) {x : Space} (hx : ‖x‖ ≤ R) :
    masterTailTest c r₀ s (2*R) g x = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  exact masterKernel_zero_outer hc hc1 hr hs hs1 hrR hgs hx hy

lemma masterTailTest_count_le {c r₀ s R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1/2)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hrR : r₀ ≤ R)
    {g : Space → ℝ} (hgs : tsupport g ⊆ ball 0 1) (hgn : ∫ z, (g z)^2 = 1)
    {N : ℕ} (x : Configuration N) :
    (∑ i, masterTailTest c r₀ s (2*R) g (x i)) ≤ rawExteriorCount R x := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : R ≤ ‖x i‖
  · rw [ite_eq_left hi]
    exact masterTailTest_le_one hc hr hs _ hgn _
  · rw [ite_eq_right hi, masterTailTest_zero_inner hc hc1 hr hs hs1 hrR hgs (le_of_not_ge hi)]

open MeasureTheory Filter Set Metric
open scoped BigOperators
open CoulombObservation

lemma masterTailTest_graph_integrable {N : ℕ} (F : fermionGraph N)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (R : ℝ) {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1) :
    Integrable (fun x : Configuration N => ∑ i, masterTailTest c r₀ s R g (x i)) (graphRawLaw F) := by
  apply graph_weight_integrable F _
    (Finset.measurable_sum _ (fun i _ => (masterTailTest_measurable hc hr hs R hg).comp (measurable_pi_apply i)))
  intro x
  change ‖∑ i, masterTailTest c r₀ s R g (x i)‖ ≤ (N:ℝ)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => masterTailTest_nonneg c r₀ s R g (x i)))]
  calc
    _ ≤ ∑ i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => masterTailTest_le_one hc hr hs R hgn (x i))
    _ = N := by simp

lemma jointMasterPosterior_tail {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (R : ℝ) {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1)
    (z : OriginalDatum N K ell j) :
    (∫ y in {y : Space | R < ‖y‖}, jointMasterPosterior μ ell j c r₀ s g z y) =
      kernelPosteriorTest μ ell j (masterTailTest c r₀ s R g) z := by
  have hi := masterConfigurationKernel_integrable (originalRawKernel μ ell j z) hc hr hs hg hgn
  have hi' : Integrable (fun p : Configuration N × Space => ∑ i, masterKernel c r₀ s g (p.1 i) p.2)
      ((originalRawKernel μ ell j z).prod (volume.restrict {y : Space | R < ‖y‖})) :=
    hi.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  change (∫ y in {y : Space | R < ‖y‖}, ∫ x, ∑ i, masterKernel c r₀ s g (x i) y
    ∂originalRawKernel μ ell j z) = _
  rw [←integral_integral_swap hi']
  unfold kernelPosteriorTest masterTailTest
  apply integral_congr_ae
  exact ae_of_all _ (fun x => integral_finsetSum _ (fun i _ =>
    (masterKernel_integrable hc hr hs hgn (x i)).integrableOn))

lemma original_master_tail_integrable {N K : ℕ} (F : fermionGraph N)
    (ell : Fin K → ℝ) (j : ℕ) {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (R : ℝ) {g : Space → ℝ} (hg : Continuous g) (hgn : ∫ z, (g z)^2 = 1) :
    Integrable (fun z => ∫ y in {y : Space | R < ‖y‖},
      jointMasterPosterior (graphRawLaw F) ell j c r₀ s g (originalDatum ell j z) y)
      (physicalObservationLaw (graphRawLaw F) K) := by
  simp_rw [jointMasterPosterior_tail _ ell j hc hr hs R hg hgn]
  exact kernelPosteriorTest_integrable _ ell j (masterTailTest_measurable hc hr hs R hg)
    (masterTailTest_graph_integrable F hc hr hs R hg hgn)

lemma original_master_tail_mean_le {N K : ℕ} (F : fermionGraph N)
    (ell : Fin K → ℝ) (j : ℕ) {c r₀ s R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1/2)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hrR : r₀ ≤ R)
    {g : Space → ℝ} (hg : Continuous g) (hgs : tsupport g ⊆ ball 0 1)
    (hgn : ∫ z, (g z)^2 = 1) :
    (∫ z, (∫ y in {y : Space | 2*R < ‖y‖},
      jointMasterPosterior (graphRawLaw F) ell j c r₀ s g (originalDatum ell j z) y)
      ∂physicalObservationLaw (graphRawLaw F) K) ≤
      ∫ x, rawExteriorCount R x ∂graphRawLaw F := by
  simp_rw [jointMasterPosterior_tail _ ell j hc hr hs (2*R) hg hgn]
  rw [kernelPosteriorTest_mean _ ell j (masterTailTest_measurable hc hr hs (2*R) hg)
    (masterTailTest_graph_integrable F hc hr hs (2*R) hg hgn)]
  exact integral_mono (masterTailTest_graph_integrable F hc hr hs (2*R) hg hgn)
    (rawExteriorCount_integrable F R) (masterTailTest_count_le hc hc1 hr hs hs1 hrR hgs hgn)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellAbsorptionNumerics
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply FermionLipschitzMultiplier.apply oneBodySquareTotal
  formEnergy energy sectorExcessOperator fermionGraphValue shellBiasMultiplier
  rawFormPair formMass weightedMass oneBodyGradientError corePriceExcess shellMeanField innerScale

lemma actualShellRadius_ge : 16 ≤ actualShellRadius := le_max_left _ _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExteriorScreenNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

lemma exteriorGradientConstant_nonneg : 0 ≤ exteriorGradientConstant := by unfold exteriorGradientConstant; positivity

lemma actualScreenRadius_ge : actualShellRadius ≤ actualScreenRadius := le_max_left _ _
lemma actualScreenRadius_ge16 : 16 ≤ actualScreenRadius := actualShellRadius_ge.trans actualScreenRadius_ge
lemma actualScreenRadius_pos : 0 < actualScreenRadius := lt_of_lt_of_le (by norm_num) actualScreenRadius_ge16

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator graphRawLaw

lemma actualScreenConstant_nonneg : 0 ≤ actualScreenConstant := by
  have hC := (Classical.choose_spec (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one)).1
  have hn := exteriorGradientConstant_nonneg
  have hr := actualScreenRadius_pos
  unfold actualScreenConstant
  positivity

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] graphRawLaw physicalObservationLaw jointMasterPosterior

theorem selected_data_of_events {Z s r c l B C T η δ : ℝ} {N K : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hr : 0 < r) (hrs : r ≤ s)
    (hc : 0 < c) (hc1 : c ≤ 1/2) (_ : 1 ≤ l) (hδ : 0 < δ)
    (F : fermionGraph N) (hFn : ‖fermionGraphValue N F‖^2 = 1) (j : ℕ)
    {u : ℝ} (hu : 0 < u) (hul : 1/(2*l) ≤ u/s) (huh : u/s ≤ l⁻¹)
    (hcover : s*l ≤ (2*l^2)*u)
    (htail : (∫ x, rawExteriorCount (2*(actualScreenRadius*s)) x ∂graphRawLaw F) ≤ actualScreenConstant/s)
    {a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ}
    (hbar : IsNuclearBarrier (physicalObservationLaw (graphRawLaw F) K)
      (originalQueryDensity F r j c r s) Z tfDensityCoefficient B C u T η a p)
    {G : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hG : MeasurableSet G)
    (hcomp : ∀ q ∈ G, ∀ y, u ≤ ‖y‖ → ‖y‖ ≤ (2*l^2)*u →
      (‖y‖^4*originalQueryField F Z (1/s^4) r j c r s q y ≤ actualInverseCap) ∧
      |originalQueryDensity F r j c r s q y-tfDensityCoefficient*
        (max (originalQueryField F Z (1/s^4) r j c r s q y) 0)^(3/2:ℝ)| < l⁻¹^8/‖y‖^6)
    (hbudget : η+(actualScreenConstant*s^2)/δ+(physicalObservationLaw (graphRawLaw F) K).real Gᶜ < 1) :
    Nonempty (SelectedQuantumData Z N s l δ B C selectedTailRadius) := by
  let := graphRawLaw_probability F hFn
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let μ := originalQueryDensity (K := K) F r j c r s
  let g : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → ℝ :=
    fun q => s^3*(∫ y in {y : TFSpace | s*selectedTailRadius < ‖y‖}, μ q y)
  have hgi : Integrable g (physicalObservationLaw (graphRawLaw F) K) :=
    (original_master_tail_integrable F ell j hc hr hs (s*selectedTailRadius)
      canonicalRealPacket_smooth.continuous canonicalRealPacket_normalized).const_mul _
  have hμn : ∀ q x, 0 ≤ μ q x := fun q x => jointMasterPosterior_nonneg _ _ _ _ _ _ _ _ _
  have hgn : ∀ q, 0 ≤ g q := fun q => mul_nonneg (pow_nonneg hs.le 3) (integral_nonneg (hμn q))
  have hrR : r ≤ 2*(actualScreenRadius*s) := by
    have hR := actualScreenRadius_ge16
    nlinarith only [hrs,hs,hR]
  have htailmean := (original_master_tail_mean_le F ell j hc hc1 hr hs hs1 hrR
    canonicalRealPacket_smooth.continuous canonicalRealPacket_support canonicalRealPacket_normalized).trans htail
  have hgm : (∫ q, g q ∂physicalObservationLaw (graphRawLaw F) K) ≤ actualScreenConstant*s^2 := by
    rw [show (∫ q, g q ∂physicalObservationLaw (graphRawLaw F) K) =
      s^3*(∫ q, (∫ y in {y : TFSpace | s*selectedTailRadius < ‖y‖}, μ q y)
        ∂physicalObservationLaw (graphRawLaw F) K) from integral_const_mul _ _]
    have hrad : s*selectedTailRadius = 2*(2*(actualScreenRadius*s)) := by unfold selectedTailRadius; ring
    change s^3*(∫ q, (∫ y in {y : TFSpace | s*selectedTailRadius < ‖y‖}, μ q y)
      ∂physicalObservationLaw (graphRawLaw F) K) ≤ _
    rw [hrad]
    convert mul_le_mul_of_nonneg_left htailmean (pow_nonneg hs.le 3) using 1 <;>
      try rfl
    field_simp
  obtain ⟨q,hq,hw,hpint,hgq⟩ := hbar.select_data hgi hgn hG hδ hgm hbudget
  obtain ⟨M,hM,hMb⟩ := jointMasterPosterior_global_bound (graphRawLaw F) ell j hc hr hs hrs
    canonicalRealPacket_smooth.continuous canonicalRealPacket_compact
  have hμm : Measurable (μ q) :=
    (jointMasterPosterior_measurable (graphRawLaw F) ell j hc hr hs canonicalRealPacket_smooth.continuous).comp
      (measurable_const.prodMk measurable_id)
  have hμi : Integrable (μ q) := jointMasterPosterior_integrable (graphRawLaw F) ell j hc hr hs
    canonicalRealPacket_smooth.continuous canonicalRealPacket_normalized _
  have hpm : Measurable (p q) := hbar.measurable_error.comp (measurable_const.prodMk measurable_id)
  obtain ⟨L,hL⟩ := hbar.bounded_error
  have hpb : ∀ x, p q x ≤ max L 0 := fun x => (hL _ _).trans (le_max_left _ _)
  have hpi : Integrable (p q) := (bounded_compact_mass_le hpm (le_max_right L 0)
    (hbar.nonneg_error q) hpb (hbar.support_error q)).1
  have scaled (x : TFSpace) (hxl : u/s ≤ ‖x‖) (hxh : ‖x‖ ≤ l) := by
    have hx : x ≠ 0 := norm_pos_iff.mp ((div_pos hu hs).trans_le hxl)
    have hnorm : ‖s • x‖ = s*‖x‖ := by rw [norm_smul,Real.norm_of_nonneg hs.le]
    have hyl : u ≤ ‖s • x‖ := by rw [hnorm]; nlinarith [(div_le_iff₀ hs).mp hxl]
    have hyh : ‖s • x‖ ≤ (2*l^2)*u := by rw [hnorm]; exact (mul_le_mul_of_nonneg_left hxh hs.le).trans hcover
    have hh := hcomp q hq (s • x) hyl hyh
    exact original_TF_scale hs hx hh.1 hh.2.le
  refine ⟨⟨u,a q,μ q,p q,hu,hul,huh,(hbar.locallyLipschitz_offset q).continuous,
    hμm,hμi,hμn q,⟨M,hM,?_⟩,?_,hpm,hpi,hbar.nonneg_error q,⟨max L 0,le_max_right _ _,hpb⟩,
    hbar.support_error q,hpint.le,hw,hbar.lower q,hbar.upper q,?_,?_,?_⟩⟩
  · intro x
    exact (le_abs_self _).trans (by simpa only [μ,originalQueryDensity,ell,Real.norm_eq_abs] using hMb _ x)
  · exact jointMasterPosterior_mass (graphRawLaw F) ell j hc hr hs
      canonicalRealPacket_smooth.continuous canonicalRealPacket_normalized _
  · intro x hxl hxh; exact (scaled x hxl hxh).2
  · intro x hxl hxh; exact (scaled x hxl hxh).1
  · rw [tfDilation_exterior_mass hs]
    exact hgq.le
end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_FullAnnulusNormalization
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma localTFResponse_eq_coefficient {h : ℝ} (hh : 0 ≤ h) :
    localTFResponse h = (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹*h^(3/2:ℝ) := by
  rw [localTFResponse,max_eq_left hh,Real.div_rpow hh (mul_pos (by norm_num) tfKinetic_pos).le]
  ring

lemma localTFResponse_div_radius_four {b : ℝ} (hb : 0 < b) (h : ℝ) :
    localTFResponse (h/b^4) = localTFResponse h/b^6 := by
  have ht := localTFResponse_rescale hb (h/b^4)
  have he : b^4*(h/b^4) = h := by field_simp
  rw [he] at ht
  exact (eq_div_iff (pow_ne_zero 6 hb.ne')).mpr (by linarith)

lemma inverseComparisonAt_of_cell {y : Space} {H μ lo hi xi C : ℝ}
    (hlo : 0 ≤ lo)
    (hcap : (localCellRadius y)^4*H ≤ C)
    (hinv : ∀ h ∈ Icc (lo/100000^4) (hi/100000^4),
      (localTFResponse h < (localCellRadius y)^6*μ → h-xi/100000^4 ≤ (localCellRadius y)^4*H) ∧
      ((localCellRadius y)^6*μ < localTFResponse h → (localCellRadius y)^4*H ≤ h+xi/100000^4)) :
    InverseComparisonAt ‖y‖ H μ (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹ lo hi xi (100000^4*C) := by
  have hcap' : ‖y‖^4*H ≤ 100000^4*C := by
    dsimp [localCellRadius] at hcap
    rw [div_pow,div_mul_eq_mul_div] at hcap
    simpa [mul_comm] using (div_le_iff₀ (by norm_num : (0:ℝ) < 100000^4)).mp hcap
  refine ⟨hcap',?_,?_⟩
  · intro h hh ht
    have hh' : h/100000^4 ∈ Icc (lo/100000^4) (hi/100000^4) :=
      ⟨div_le_div_of_nonneg_right hh.1 (by positivity),div_le_div_of_nonneg_right hh.2 (by positivity)⟩
    have hr := localTFResponse_div_radius_four (by norm_num : (0:ℝ) < 100000) h
    rw [localTFResponse_eq_coefficient (hlo.trans hh.1)] at hr
    have hf := (hinv _ hh').1
    simp only [localCellRadius,div_pow,div_mul_eq_mul_div] at hf
    rw [hr] at hf
    have hz := hf ((div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ) < 100000^6)).mpr ht)
    rw [←sub_div] at hz
    exact (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 100000^4)).mp hz
  · intro h hh ht
    have hh' : h/100000^4 ∈ Icc (lo/100000^4) (hi/100000^4) :=
      ⟨div_le_div_of_nonneg_right hh.1 (by positivity),div_le_div_of_nonneg_right hh.2 (by positivity)⟩
    have hr := localTFResponse_div_radius_four (by norm_num : (0:ℝ) < 100000) h
    rw [localTFResponse_eq_coefficient (hlo.trans hh.1)] at hr
    have hf := (hinv _ hh').2
    simp only [localCellRadius,div_pow,div_mul_eq_mul_div] at hf
    rw [hr] at hf
    have hz := hf ((div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ) < 100000^6)).mpr ht)
    rw [←add_div] at hz
    exact (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 100000^4)).mp hz

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ContinuousUniversalEvent
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open Set MeasureTheory

theorem measurableSet_forall_closed_parameter
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [TopologicalSpace.SeparableSpace X]
    {P : Ω → X → Prop} (hm : ∀ x, MeasurableSet {ω | P ω x})
    (hc : ∀ ω, IsClosed {x | P ω x}) : MeasurableSet {ω | ∀ x, P ω x} := by
  obtain ⟨D,hD,hd⟩ := TopologicalSpace.exists_countable_dense X
  have he : {ω | ∀ x, P ω x} = ⋂ x ∈ D, {ω | P ω x} := by
    ext ω
    simp only [mem_ofPred_eq,mem_iInter]
    constructor
    · intro h x _
      exact h x
    · intro h x
      exact closure_minimal h (hc ω) (hd x)
  rw [he]
  exact MeasurableSet.biInter hD (fun x _ => hm x)

open Set MeasureTheory
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma inverseComparisonAt_closed {X : Type*} [TopologicalSpace X]
    {d H μ : X → ℝ} (hd : Continuous d) (hH : Continuous H) (hμ : Continuous μ)
    (κ lo hi xi C : ℝ) : IsClosed {x | InverseComparisonAt (d x) (H x) (μ x) κ lo hi xi C} := by
  have hf := (hd.pow 4).mul hH
  have hr := (hd.pow 6).mul hμ
  have h₀ := isClosed_le hf continuous_const (g := fun _ => C)
  have h₁ := isClosed_iInter (fun h : Icc lo hi =>
    (isClosed_le hr continuous_const (g := fun _ => κ*(h:ℝ)^(3/2:ℝ))).union
      (isClosed_le continuous_const hf (f := fun _ => (h:ℝ)-xi)))
  have h₂ := isClosed_iInter (fun h : Icc lo hi =>
    (isClosed_le continuous_const hr (f := fun _ => κ*(h:ℝ)^(3/2:ℝ))).union
      (isClosed_le hf continuous_const (g := fun _ => (h:ℝ)+xi)))
  convert h₀.inter (h₁.inter h₂) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_iInter,mem_union,mem_ofPred_eq,InverseComparisonAt,
    imp_iff_not_or,not_lt,Subtype.forall,Pi.mul_apply,Pi.pow_apply]

lemma inverseComparisonAt_measurable {Ω : Type*} [MeasurableSpace Ω]
    {H μ : Ω → ℝ} (hH : Measurable H) (hμ : Measurable μ)
    (d κ lo hi xi C : ℝ) : MeasurableSet {q | InverseComparisonAt d (H q) (μ q) κ lo hi xi C} := by
  have hf := hH.const_mul (d^4)
  have hr := hμ.const_mul (d^6)
  have h₀ := measurableSet_le hf measurable_const (g := fun _ => C)
  have ht : Continuous (fun h : Icc lo hi => κ*(h:ℝ)^(3/2:ℝ)) :=
    ((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/2)).comp continuous_subtype_val).const_mul κ
  have h₁ : MeasurableSet {q | ∀ h : Icc lo hi,
      d^6*μ q ≤ κ*(h:ℝ)^(3/2:ℝ) ∨ (h:ℝ)-xi ≤ d^4*H q} := by
    apply measurableSet_forall_closed_parameter
    · intro h
      exact (measurableSet_le hr measurable_const).union (measurableSet_le measurable_const hf)
    · intro q
      exact (isClosed_le continuous_const ht).union
        (isClosed_le (continuous_subtype_val.sub continuous_const) continuous_const)
  have h₂ : MeasurableSet {q | ∀ h : Icc lo hi,
      κ*(h:ℝ)^(3/2:ℝ) ≤ d^6*μ q ∨ d^4*H q ≤ (h:ℝ)+xi} := by
    apply measurableSet_forall_closed_parameter
    · intro h
      exact (measurableSet_le measurable_const hr).union (measurableSet_le hf measurable_const)
    · intro q
      exact (isClosed_le ht continuous_const).union
        (isClosed_le continuous_const (continuous_subtype_val.add_const xi))
  convert h₀.inter (h₁.inter h₂) using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  simp only [mem_inter_iff,mem_ofPred_eq,InverseComparisonAt,imp_iff_not_or,not_lt,Subtype.forall]

lemma original_inverse_fullAnnulus_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) {c₁ r₀ s u B κ lo hi xi C : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s) (hu : 0 < u) :
    MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      {q | ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
        InverseComparisonAt ‖y‖
          (originalQueryField F Z lam r j c₁ r₀ s q y)
          (originalQueryDensity F r j c₁ r₀ s q y) κ lo hi xi C} := by
  let Y := {y : Space // u ≤ ‖y‖ ∧ ‖y‖ ≤ B*u}
  have he : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      {q | ∀ y : Y, InverseComparisonAt ‖(y:Space)‖
        (originalQueryField F Z lam r j c₁ r₀ s q y)
        (originalQueryDensity F r j c₁ r₀ s q y) κ lo hi xi C} := by
    apply @measurableSet_forall_closed_parameter _ Y
      (observationInformation (fun k : Fin K => dyadicObservationWidth r k) j) _ _
    · intro y
      exact @inverseComparisonAt_measurable _
        (observationInformation (fun k : Fin K => dyadicObservationWidth r k) j) _ _
        (originalQueryField_info_measurable F Z lam r j hc hr hs y)
        (originalQueryDensity_info_measurable F r j hc hr hs y) _ _ _ _ _ _
    · intro q
      have hfield : Continuous (fun y : Y => originalQueryField F Z lam r j c₁ r₀ s q y) := by
        apply (originalQueryField_continuousOn_punctured F Z lam r j hc hr hs hrs q).comp_continuous
          continuous_subtype_val
        intro y
        change (y:Space) ≠ 0
        exact norm_pos_iff.mp (hu.trans_le y.property.1)
      have hden : Continuous (fun y : Y => originalQueryDensity F r j c₁ r₀ s q y) :=
        (jointMasterPosterior_continuous (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j hc hr hs hrs
          canonicalRealPacket_smooth.continuous canonicalRealPacket_compact
          (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j q)).comp continuous_subtype_val
      exact inverseComparisonAt_closed continuous_subtype_val.norm hfield hden _ _ _ _ _
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  simp only [mem_ofPred_eq,Subtype.forall,Y]
  simp only [and_imp]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FullAnnulusGoodEvent
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom
open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local instance] physicalObservationLaw_probability

theorem exists_actual_fullAnnulus_good_constant {B c₁ lo hi xi : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        ∃ G : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
          MeasurableSet[observationInformation
            (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] G ∧
          (physicalObservationLaw (graphRawLaw (F i)) (K i)).real Gᶜ ≤ C*u^25 ∧
          ∀ q ∈ G, ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
            InverseComparisonAt ‖y‖
              (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y)
              (originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y)
              (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹ lo hi xi
              (100000^4*(16*(tfPatchCapConstant+3))) := by
  have hp : (0:ℝ) < 100000^4 := by norm_num
  obtain ⟨C,hC,hresult⟩ := exists_actual_fullAnnulus_inverse_constant hB hc hcL
    (div_le_div_of_nonneg_right hlh hp.le) (div_pos hxi hp)
    (lo := lo/100000^4) (hi := hi/100000^4)
    (by rw [←mul_div_assoc]; exact (div_lt_div_iff_of_pos_right hp).mpr hlo)
  refine ⟨C,hC,?_⟩
  intro ι l r₀ s Z lam N K F δ hδ hs hr hF
  have he := hresult hδ hs hr hF
  filter_upwards [he,hr,hF,hs.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hie hri hFi hsi
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := hjs.trans hsi.le
  have hrs : r₀ i ≤ s i := (le_mul_of_one_le_left hri.le (one_le_pow₀ (by norm_num))).trans hjs
  have hsp : 0 < s i := hu.trans_le hjs
  obtain ⟨E,hE,hpE,hqE⟩ := hie j hjs
  let G : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)) :=
    {q | ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
      InverseComparisonAt ‖y‖
        (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y)
        (originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y)
        (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹ lo hi xi
        (100000^4*(16*(tfPatchCapConstant+3)))}
  have hG : MeasurableSet[observationInformation
      (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] G :=
    original_inverse_fullAnnulus_measurable (F i) (Z i) (lam i) (r₀ i) j hc hri hsp hrs hu
  have hae : Gᶜ ≤ᵐ[physicalObservationLaw (graphRawLaw (F i)) (K i)] E := by
    filter_upwards [hqE] with q hq
    intro hqG
    by_contra hqnot
    apply hqG
    intro y hyl hyh
    have hh := hq hqnot
    exact inverseComparisonAt_of_cell (by linarith) (hh.2 y hyl hyh) (hh.1 y hyl hyh)
  let := graphRawLaw_probability (F i) hFi.2.2.1
  refine ⟨G,hG,?_,fun q hq => hq⟩
  calc
    _ ≤ (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
    _ ≤ C*u^37 := hpE
    _ ≤ C*u^25 := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hu.le hu1 (by norm_num)) hC.le

end CoulombAtom

open Set Filter MeasureTheory Metric
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_OutwardBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter Set Metric
open scoped Topology

theorem inverse_height_squeeze {u v lo hi xi C : ℝ}
    (hv : 0 ≤ v) (hlo : 0 ≤ lo) (hlh : lo < hi) (hxi : 0 ≤ xi)
    (hcap : u ≤ C) (hgap : C+xi < hi)
    (hhigh : ∀ h ∈ Icc lo hi, h < v → h-xi ≤ u)
    (hlow : ∀ h ∈ Icc lo hi, v < h → u ≤ h+xi) :
    v < hi ∧ |v-max u 0| ≤ lo+xi := by
  have hvhi : v < hi := by
    by_contra hn
    have hb : max lo (C+xi) < hi := max_lt hlh hgap
    obtain ⟨h,hh₁,hh₂⟩ := exists_between hb
    have hvh : h < v := hh₂.trans_le (le_of_not_gt hn)
    have hh := hhigh h ⟨(le_max_left _ _).trans hh₁.le,hh₂.le⟩ hvh
    have hCh : C+xi < h := (le_max_right _ _).trans_lt hh₁
    linarith
  have hlower : v ≤ max u 0+lo+xi := by
    by_cases hvlo : v ≤ lo
    · linarith [le_max_right u 0]
    · have hvlo' : lo < v := lt_of_not_ge hvlo
      by_cases hvu : v ≤ u+xi
      · linarith [le_max_left u 0]
      · have hmax : max lo (u+xi) < v := max_lt hvlo' (lt_of_not_ge hvu)
        obtain ⟨h,hh₁,hh₂⟩ := exists_between hmax
        have hh := hhigh h ⟨(le_max_left _ _).trans hh₁.le,(hh₂.trans hvhi).le⟩ hh₂
        have huh : u+xi < h := (le_max_right _ _).trans_lt hh₁
        linarith
  have hupper : max u 0 ≤ v+lo+xi := by
    apply max_le _ (by linarith)
    have hu : u ≤ max v lo+xi := by
      by_contra hn
      have hmaxu : max v lo < u-xi := by linarith [lt_of_not_ge hn]
      have hmaxhi : max v lo < hi := max_lt hvhi hlh
      obtain ⟨h,hh₁,hh₂⟩ := exists_between (lt_min hmaxu hmaxhi)
      have hh := hlow h ⟨(le_max_right _ _).trans hh₁.le,(lt_min_iff.mp hh₂).2.le⟩
        ((le_max_left _ _).trans_lt hh₁)
      linarith [(lt_min_iff.mp hh₂).1]
    have hm : max v lo ≤ v+lo := max_le (by linarith) (by linarith)
    linarith
  exact ⟨hvhi,abs_le.mpr ⟨by linarith,by linarith⟩⟩

lemma rpow_inverse_three_halves {x : ℝ} (hx : 0 ≤ x) :
    (x^(2/3:ℝ))^(3/2:ℝ) = x := by
  rw [←Real.rpow_mul hx]
  norm_num

theorem inverse_comparison_density_height {d H μ k lo hi xi C : ℝ}
    (hμ : 0 ≤ μ) (hk : 0 < k)
    (hlo : 0 ≤ lo) (hlh : lo < hi) (hxi : 0 ≤ xi) (hgap : C+xi < hi)
    (hinv : InverseComparisonAt d H μ k lo hi xi C) :
    let v := (d^6*μ/k)^(2/3:ℝ)
    v < hi ∧ |v-max (d^4*H) 0| ≤ lo+xi := by
  let v := (d^6*μ/k)^(2/3:ℝ)
  have hx : 0 ≤ d^6*μ/k := by positivity
  have hv : 0 ≤ v := Real.rpow_nonneg hx _
  have he : k*v^(3/2:ℝ) = d^6*μ := by
    dsimp only [v]
    rw [rpow_inverse_three_halves hx]
    field_simp
  apply inverse_height_squeeze hv hlo hlh hxi hinv.1 hgap
  · intro t ht htv
    apply hinv.2.1 t ht
    rw [←he]
    exact mul_lt_mul_of_pos_left
      (Real.rpow_lt_rpow (hlo.trans ht.1) htv (by norm_num)) hk
  · intro t ht hvt
    apply hinv.2.2 t ht
    rw [←he]
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hv hvt (by norm_num)) hk

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SelectionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

section
open MeasureTheory Filter Set
open scoped Topology
open CoulombAtom CoulombAnalysis

lemma selectedTailThreshold_pos {s : ℝ} (hs : 0 < s) : 0 < selectedTailThreshold s :=
  mul_pos (by linarith [actualScreenConstant_nonneg]) hs
lemma selectedTail_ratio {s : ℝ} (hs : 0 < s) :
    (actualScreenConstant*s^2)/selectedTailThreshold s ≤ s := by
  apply (div_le_iff₀ (selectedTailThreshold_pos hs)).mpr
  unfold selectedTailThreshold
  nlinarith only [sq_nonneg s]

lemma selection_budget_eventually {ι : Type*} {F : Filter ι} {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) (hs0 : Tendsto s F (𝓝 0)) (D A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ i in F, ∀ u : ℝ, 0 ≤ u → u ≤ s i →
      5184*(s i)^32+D*(s i)^barrierErrorExponent+
        (actualScreenConstant*(s i)^2)/selectedTailThreshold (s i)+A*u^25 < 1 := by
  have hh : Tendsto (fun i => 5184*(s i)^32+D*(s i)^barrierErrorExponent+s i+A*(s i)^25) F (𝓝 0) := by
    have ha := (hs0.pow 25).const_mul A
    simpa only [zero_pow (by norm_num : (25:ℕ) ≠ 0),mul_zero,add_zero] using
      ((total_barrier_budget_tendsto_zero hs0 D).add hs0).add ha
  filter_upwards [hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi u hu hus
  have hratio := selectedTail_ratio (hs i)
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu hus 25) hA
  linarith

lemma price_scale_inverse {s : ℝ} (hs : 0 < s) : s^(-4:ℝ) = 1/s^4 := by
  rw [Real.rpow_neg hs.le,show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast,one_div]

end
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local instance] physicalObservationLaw_probability

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_dInverseLocalTF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter Set Metric
open scoped Topology

theorem exists_inverse_local_tf_parameters {k C hi ε : ℝ}
    (hk : 0 < k) (hC : 0 ≤ C) (hhi : C+1 < hi) (hε : 0 < ε) :
    ∃ lo xi : ℝ, 0 < lo ∧ 0 < xi ∧ lo < hi ∧ C+xi < hi ∧
      ∀ {d H μ : ℝ}, 0 < d → 0 ≤ μ →
        InverseComparisonAt d H μ k lo hi xi C →
        |μ-k*(max H 0)^(3/2:ℝ)| < ε/d^6 := by
  let f : ℝ → ℝ := fun t => k*t^(3/2:ℝ)
  have hf : Continuous f := continuous_const.mul
    (continuous_id.rpow_const (fun _ => Or.inr (by norm_num)))
  have huc : UniformContinuousOn f (Icc 0 hi) := isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ,hδ,hδf⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  let t : ℝ := min δ 1/4
  have ht : 0 < t := div_pos (lt_min hδ (by norm_num)) (by norm_num)
  have ht1 : t ≤ 1/4 := div_le_div_of_nonneg_right (min_le_right δ 1) (by norm_num)
  have htδ : 2*t < δ := by
    have hh := min_le_left δ 1
    dsimp only [t]
    nlinarith [lt_min hδ (by norm_num : (0:ℝ) < 1)]
  have hh : t < hi := by linarith
  have hgap : C+t < hi := by linarith
  refine ⟨t,t,ht,ht,hh,hgap,?_⟩
  intro d H μ hd hμ hinv
  let v := (d^6*μ/k)^(2/3:ℝ)
  have hs := inverse_comparison_density_height hμ hk ht.le hh ht.le hgap hinv
  have hvn : 0 ≤ v := Real.rpow_nonneg (by positivity) _
  have hvhi : v < hi := hs.1
  have humem : max (d^4*H) 0 ∈ Icc 0 hi :=
    ⟨le_max_right _ _,max_le (hinv.1.trans (by linarith)) (by linarith)⟩
  have hdv : dist v (max (d^4*H) 0) < δ := by
    rw [Real.dist_eq]
    exact hs.2.trans_lt (by linarith)
  have he := hδf v ⟨hvn,hvhi.le⟩ _ humem hdv
  have hvpow : f v = d^6*μ := by
    dsimp only [f,v]
    rw [rpow_inverse_three_halves (by positivity)]
    field_simp
  have hscale : max (d^4*H) 0 = d^4*max H 0 := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg hd.le 4),mul_zero]
  have huval : f (max (d^4*H) 0) = d^6*(k*(max H 0)^(3/2:ℝ)) := by
    dsimp only [f]
    rw [hscale,scaled_positive_reaction hd.le (le_max_right H 0)]
    ring
  rw [Real.dist_eq,hvpow,huval,←mul_sub,abs_mul,abs_of_pos (pow_pos hd 6)] at he
  exact (lt_div_iff₀ (pow_pos hd 6)).mpr (by nlinarith)

lemma InverseComparisonAt.mono_tolerance {d H μ k lo hi xi xi' C : ℝ}
    (h : InverseComparisonAt d H μ k lo hi xi C) (hxi : xi ≤ xi') :
    InverseComparisonAt d H μ k lo hi xi' C := by
  refine ⟨h.1,?_,?_⟩
  · intro t ht hm
    linarith [h.2.1 t ht hm]
  · intro t ht hm
    linarith [h.2.2 t ht hm]

 theorem exists_inverse_local_tf_admissible_parameters {k C hi ε : ℝ}
    (hk : 0 < k) (hC : 0 ≤ C) (hhi : C+1 < hi) (hε : 0 < ε) :
    ∃ lo xi : ℝ, 0 < lo ∧ 0 < xi ∧ 16*xi < lo ∧ lo < hi ∧ C+xi < hi ∧
      ∀ {d H μ : ℝ}, 0 < d → 0 ≤ μ →
        InverseComparisonAt d H μ k lo hi xi C →
        |μ-k*(max H 0)^(3/2:ℝ)| < ε/d^6 := by
  obtain ⟨lo,xi,hlo,hxi,hlh,hgap,hTF⟩ := exists_inverse_local_tf_parameters hk hC hhi hε
  let xi' := min xi (lo/32)
  have hxi' : 0 < xi' := lt_min hxi (by positivity)
  have hle : xi' ≤ xi := min_le_left _ _
  have h16 : 16*xi' < lo := by
    have hh : xi' ≤ lo/32 := min_le_right _ _
    linarith
  exact ⟨lo,xi',hlo,hxi',h16,hlh,(by linarith : C+xi' < hi),
    fun hd hμ hinv => hTF hd hμ (hinv.mono_tolerance hle)⟩

end CoulombBarrier

open MeasureTheory Filter Set
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_AnnularTFAndCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local instance] physicalObservationLaw_probability

 theorem exists_actual_annular_TF_cap_constant {B c ε : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c) (hcL : c < (10*(100000:ℝ))⁻¹) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        ∃ G : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
          MeasurableSet[observationInformation
            (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] G ∧
          (physicalObservationLaw (graphRawLaw (F i)) (K i)).real Gᶜ ≤ C*u^25 ∧
          ∀ q ∈ G, ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
            (‖y‖^4*originalQueryField (F i) (Z i) (lam i) (r₀ i) j c (r₀ i) (s i) q y ≤ actualInverseCap) ∧
            |originalQueryDensity (F i) (r₀ i) j c (r₀ i) (s i) q y -
              tfDensityCoefficient*(max
                (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c (r₀ i) (s i) q y) 0)^(3/2:ℝ)|
              < ε/‖y‖^6 := by
  have hcap : 0 ≤ actualInverseCap := by
    have hh := tfPatchCapConstant_pos
    unfold actualInverseCap
    positivity
  obtain ⟨lo,xi,hlo,hxi,hsmall,hlh,hgap,hTF⟩ :=
    exists_inverse_local_tf_admissible_parameters tfDensityCoefficient_pos hcap
      (hi := actualInverseCap+2) (by linarith) hε
  obtain ⟨C,hC,hresult⟩ := exists_actual_fullAnnulus_good_constant hB hc hcL hlh.le hxi hsmall
  refine ⟨C,hC,?_⟩
  intro ι l r₀ s Z lam N K F δ hδ hs hr hF
  have hgood := hresult hδ hs hr hF
  filter_upwards [hgood,hr] with i hi hri
  intro j hjs
  obtain ⟨G,hG,hprob,hcomp⟩ := hi j hjs
  refine ⟨G,hG,hprob,?_⟩
  intro q hq y hyl hyh
  have hy : 0 < ‖y‖ := (mul_pos (pow_pos (by norm_num) _) hri).trans_le hyl
  exact ⟨(hcomp q hq y hyl hyh).1,
    hTF hy (jointMasterPosterior_nonneg _ _ _ _ _ _ _ _ _) (hcomp q hq y hyl hyh)⟩

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SelectedData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

section
open MeasureTheory Filter Set Metric
open scoped Topology
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphRawLaw physicalObservationLaw jointMasterPosterior

theorem exists_actual_selected_data_constants_oai :
    ∃ B C : ℝ, 0 < B ∧ 0 ≤ C ∧
      ∀ {ι : Type*} {f : Filter ι} (Z : ι → ℕ) (s : ι → ℝ) (N : ι → ℕ),
        (∀ i, 1 ≤ Z i) → (∀ i, 0 < s i) → Tendsto s f (𝓝 0) →
        Tendsto (fun i => (Z i:ℝ)*(s i)^3) f atTop →
        (∀ i, PriceMinimizes (energy (Z i)) ((s i)^(-4:ℝ)) (N i)) →
        ∀ l : ℝ, 1 ≤ l → ∀ᶠ i in f,
          Nonempty (SelectedQuantumData (Z i) (N i) (s i) l (selectedTailThreshold (s i)) B C selectedTailRadius) := by
  classical
  let c : ℝ := 1/2000000
  have hc : 0 < c := by norm_num [c]
  have hcL : c < (10*(100000:ℝ))⁻¹ := by norm_num [c]
  have hc1 : c ≤ 1/2 := by norm_num [c]
  obtain ⟨ε,B,C,M,D,hε,hε1,hB,hM,hD,hbar⟩ := actual_outward_barrier_given_state_eventually hc hcL
  refine ⟨B,max C 0,hB,le_max_right _ _,?_⟩
  intro ι f Z s N hZ hs hs0 hscale hN l hl
  have hlp : 0 < l := zero_lt_one.trans_le hl
  let r : ι → ℝ := fun i => ε*(Z i:ℝ)^(-1/3:ℝ)
  let J : ι → ℕ := fun i => selectedDyadicIndex (r i) (s i/l)
  let K : ι → ℕ := fun i => J i+1
  have hZp (i) : 0 < (Z i:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hZ i))
  have hr (i) : 0 < r i := mul_pos hε (Real.rpow_pos_of_pos (hZp i) _)
  let p₀ (i) : Fin (K i+1) → ℝ := fun j => tinyProbabilityFloor (Z i) ((2:ℝ)^j.val*r i)
  have hp₀ (i) (j : Fin (K i+1)) : 0 < p₀ i j :=
    tinyProbabilityFloor_pos (by positivity) (mul_pos (pow_pos (by norm_num) _) (hr i))
  have hstate (i) : ∃ F : fermionGraph (N i),
      OwnProbabilityTailTiltState (Z i) ((s i)^(-4:ℝ)) (r i) (K i) (p₀ i) 1 F ∧
      (s i ≤ 1 → actualScreenRadius*s i ≤ 1 →
        (∫ x, rawExteriorCount (2*(actualScreenRadius*s i)) x ∂graphRawLaw F) ≤ actualScreenConstant/s i) := by
    by_cases hh : s i ≤ 1 ∧ actualScreenRadius*s i ≤ 1
    · obtain ⟨F,hF,hFt⟩ := exists_own_state_exterior_number (Nat.cast_nonneg (Z i)) (hs i) hh.1 hh.2 (hr i)
        (by simpa only [price_scale_inverse (hs i)] using hN i) (K i) (p₀ i) (hp₀ i)
      exact ⟨F,by simpa only [price_scale_inverse (hs i)] using hF,fun _ _ => hFt⟩
    · obtain ⟨F,hF⟩ := exists_actual_own_probability_tail_tilt_state (Nat.cast_nonneg (Z i)) (hr i)
        (hN i) (K i) (p₀ i) (hp₀ i) zero_lt_one
      exact ⟨F,hF,fun hs1 hRs => (hh ⟨hs1,hRs⟩).elim⟩
  choose F hF hFt using hstate
  have hbar' := hbar Z s N K hZ hs hs0 hscale hN F hF
  have hQB : 1 ≤ 2*l^2 := by nlinarith [sq_nonneg (l-1)]
  have htol : 0 < l⁻¹^8 := pow_pos (inv_pos.mpr hlp) _
  obtain ⟨A,hA,hgood⟩ := exists_actual_annular_TF_cap_constant hQB hc hcL htol
  have hgood' := hgood (r₀ := r) (s := s) (Z := fun i => (Z i:ℝ))
    (lam := fun i => (s i)^(-4:ℝ)) (N := N) (K := K) (F := F)
    zero_le_one hs0 (Eventually.of_forall hr)
    (Eventually.of_forall (fun i => ⟨Nat.cast_nonneg (Z i),Real.rpow_pos_of_pos (hs i) _,hF i⟩))
  have hrt := fixed_target_nuclear_radius_eventually hZp hs hscale hε hlp
  have hbud := selection_budget_eventually hs hs0 D A hA.le
  have hsmall := hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  have hRs : ∀ᶠ i in f, actualScreenRadius*s i < 1 := by
    have hh : Tendsto (fun i => actualScreenRadius*s i) f (𝓝 0) := by
      simpa only [mul_zero] using hs0.const_mul actualScreenRadius
    exact hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hbar',hgood',hrt,hbud,hsmall,hRs] with i hbi hgi hri hbudi hsi hRsi
  have hrad := selectedDyadicIndex_radius (hr i) (hs i) hl hri
  let j : Fin (K i) := ⟨J i,Nat.lt_succ_self _⟩
  obtain ⟨a,p,hbp⟩ := hbi (J i) (Nat.le_succ _) hrad.2.1
  obtain ⟨G,hG,hprob,hcomp⟩ := hgi j hrad.2.1
  have hGm : MeasurableSet G := (observationInformation_le _ _) _ hG
  have hrs : r i ≤ s i := hri.trans (div_le_self (hs i).le hl)
  apply selected_data_of_events (hs i) hsi.le (hr i) hrs hc hc1 hl
    (selectedTailThreshold_pos (hs i)) (F i) (hF i).1 (J i)
    hrad.1 hrad.2.2.1 hrad.2.2.2.1 hrad.2.2.2.2 (hFt i hsi.le hRsi.le)
    (hbp.mono_cap (le_max_left C 0)) hGm
  · intro q hq y hyl hyh
    simpa only [price_scale_inverse (hs i)] using hcomp q hq y hyl hyh
  · exact lt_of_le_of_lt (add_le_add le_rfl hprob) (hbudi _ hrad.1.le hrad.2.1)

end
open MeasureTheory Filter Set Metric
open scoped Topology
open CoulombAtom CoulombAnalysis

end CoulombBarrier

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CoulombBarrier.exists_actual_selected_data_constants_oai.{u_1} := @OAI.CoulombBarrier.exists_actual_selected_data_constants_oai.{u_1}
