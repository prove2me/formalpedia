-- Prove2me | solution 1 for OAI.DirectionalTransience.actual_finite_stage_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:03:38.950318+00:00
-- url     : https://prove2.me/submissions/0c1359d0-df15-49ae-8af0-518267fbcf3b

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal004
import Definitions.Def_OAIQ242Bal007
import Theorems.Thm_OAI_DirectionalTransience_actual_cell_no_success
import Theorems.Thm_OAI_DirectionalTransience_fresh_budget_threat_bound

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentRandomTestBound
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma independent_random_test_bound {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → A) (V : Ω → B) (hU : Measurable U) (hV : Measurable V)
    (hind : IndepFun U V μ) (E : Set A) (hE : MeasurableSet E)
    (G : Set (A × B)) (hG : MeasurableSet G) (c : ℝ≥0∞)
    (hbound : ∀ a ∈ E, (μ.map V) {b | (a,b) ∈ G} ≤ c) :
    μ {ω | U ω ∈ E ∧ (U ω,V ω) ∈ G} ≤ c*μ (U ⁻¹' E) := by
  let K : Set (A × B) := (E ×ˢ Set.univ) ∩ G
  have hK : MeasurableSet K := (hE.prod MeasurableSet.univ).inter hG
  have he : {ω | U ω ∈ E ∧ (U ω,V ω) ∈ G} = (fun ω => (U ω,V ω)) ⁻¹' K := by
    ext ω; simp [K]
  rw [he,← Measure.map_apply (hU.prodMk hV) hK,hind.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable,
    Measure.prod_apply hK]
  calc
    _ ≤ ∫⁻ a, E.indicator (fun _ => c) a ∂μ.map U := by
      apply lintegral_mono
      intro a
      change (μ.map V) (Prod.mk a ⁻¹' K) ≤ E.indicator (fun _ => c) a
      by_cases ha : a ∈ E
      · have he' : Prod.mk a ⁻¹' K = {b | (a,b) ∈ G} := by ext b; simp [K,ha]
        rw [he',Set.indicator_of_mem ha]
        exact hbound a ha
      · have he' : Prod.mk a ⁻¹' K = ∅ := by ext b; simp [K,ha]
        simp [he',ha]
    _ = c*μ (U ⁻¹' E) := by
      rw [lintegral_indicator hE,lintegral_const,Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter,Measure.map_apply hU hE]

lemma fresh_rows_random_test_bound {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] {S T : Set (Lattice d)} (hST : Disjoint S T)
    (U : Environment d → A) (V : Environment d → B)
    (hU : @Measurable _ _ (rowSigma S) _ U) (hV : @Measurable _ _ (rowSigma T) _ V)
    (E : Set A) (hE : MeasurableSet E) (G : Set (A × B)) (hG : MeasurableSet G) (c : ℝ≥0∞)
    (hbound : ∀ a ∈ E, ((environmentLaw ν).map V) {b | (a,b) ∈ G} ≤ c) :
    environmentLaw ν {ω | U ω ∈ E ∧ (U ω,V ω) ∈ G} ≤ c*environmentLaw ν (U ⁻¹' E) :=
  independent_random_test_bound (environmentLaw ν) U V
    (hU.mono (rowSigma_le S) le_rfl) (hV.mono (rowSigma_le T) le_rfl)
    (indepFun_of_disjoint_rows ν hST U V hU hV) E hE G hG c hbound

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordDepartures
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma fresh_rows_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    {f g : Environment d → ℝ}
    (hf : @Measurable _ _ (rowSigma S) _ f)
    (hg : @Measurable _ _ (rowSigma T) _ g) :
    (∫ ω, f ω * g ω ∂environmentLaw ν) =
      (∫ ω, f ω ∂environmentLaw ν) * (∫ ω, g ω ∂environmentLaw ν) := by
  have hi : IndepFun f g (environmentLaw ν) := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    exact (Indep_iff _ _ _).mp (environment_indep_rows ν hST) _ _ (hf hs) (hg ht)
  exact hi.integral_fun_mul_eq_mul_integral
    (hf.mono (rowSigma_le S) le_rfl).aestronglyMeasurable
    (hg.mono (rowSigma_le T) le_rfl).aestronglyMeasurable

lemma wordWeight_nonneg {d : ℕ} (ω : Environment d) (x : Lattice d)
    (w : List (Direction d)) : 0 ≤ wordWeight ω x w := by
  induction w generalizing x with
  | nil => simp [wordWeight]
  | cons e w ih => exact mul_nonneg (NNReal.coe_nonneg _) (ih _)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_CoordinateStrip
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.recordCount_zero _root_.OAI.DirectionalTransience.regenerationTimes_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma abs_step_le_one {d : ℕ} (e : Direction d) (i : Fin d) :
    |step e i| ≤ (1 : ℤ) := by
  simp only [step]
  split_ifs <;> norm_num

lemma nearestNeighborPrefix_bound {d : ℕ} (f : Path d) (n : ℕ)
    (hf : NearestNeighborPrefix f n) {k : ℕ} (hk : k ≤ n) :
    f k ∈ LatticeBall (f 0) k := by
  induction k with
  | zero => simp [LatticeBall]
  | succ k ih =>
    obtain ⟨e, he⟩ := hf k (by omega)
    intro i
    rw [he]
    have hb := ih (by omega) i
    change |f k i + step e i - f 0 i| ≤ ((k + 1 : ℕ) : ℤ)
    calc
      _ = |(f k i - f 0 i) + step e i| := by congr 1; ring
      _ ≤ |f k i - f 0 i| + |step e i| := abs_add_le _ _
      _ ≤ (k : ℤ) + 1 := add_le_add hb (abs_step_le_one e i)
      _ = _ := by norm_cast

lemma edgeWeight_eq_zero_of_not_neighbor {d : ℕ} (ω : Environment d) (x y : Lattice d)
    (h : ¬ ∃ e : Direction d, y = x + step e) : edgeWeight ω x y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e _
  exact ite_eq_right (fun he => h ⟨e, he⟩)

lemma quenched_pathCylinder_locality {d : ℕ} (ω η : Environment d) (x : Lattice d)
    (n : ℕ) (hωη : Set.EqOn ω η (LatticeBall x n)) (f : Path d) :
    quenchedKernel (ω, x) (pathCylinder f n) =
      quenchedKernel (η, x) (pathCylinder f n) := by
  classical
  by_cases hstart : f 0 = x
  · rw [quenched_pathCylinder _ _ _ hstart, quenched_pathCylinder _ _ _ hstart]
    by_cases hpath : NearestNeighborPrefix f n
    · apply Finset.prod_congr rfl
      intro k hk
      have hn := (Finset.mem_range.mp hk).le
      have hb := nearestNeighborPrefix_bound f n hpath hn
      have hmem : f k ∈ LatticeBall x n := by
        intro i
        have h := hb i
        rw [hstart] at h
        exact h.trans (by exact_mod_cast hn)
      simp only [edgeWeight, hωη hmem]
    · unfold NearestNeighborPrefix at hpath
      push Not at hpath
      obtain ⟨k, hk, hbad⟩ := hpath
      have hbad' : ¬ ∃ e : Direction d, f (k + 1) = f k + step e := by
        simpa using hbad
      rw [Finset.prod_eq_zero (Finset.mem_range.mpr hk)
        (edgeWeight_eq_zero_of_not_neighbor ω _ _ hbad'),
        Finset.prod_eq_zero (Finset.mem_range.mpr hk)
        (edgeWeight_eq_zero_of_not_neighbor η _ _ hbad')]
  · rw [quenched_pathCylinder_zero _ _ _ hstart, quenched_pathCylinder_zero _ _ _ hstart]

lemma quenched_prefix_locality {d : ℕ} (ω η : Environment d) (x : Lattice d)
    (n : ℕ) (hωη : Set.EqOn ω η (LatticeBall x n))
    (C : Set ((i : Finset.Iic n) → Lattice d)) :
    quenchedKernel (ω, x) ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C) =
      quenchedKernel (η, x) ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C) := by
  have hm (f : (i : Finset.Iic n) → Lattice d) (_ : f ∈ C) :
      MeasurableSet ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f}) :=
    (Preorder.measurable_frestrictLe n) (measurableSet_singleton f)
  rw [← tsum_measure_preimage_singleton C.to_countable hm,
    ← tsum_measure_preimage_singleton C.to_countable hm]
  apply tsum_congr
  intro f
  rw [restrict_prefix_fiber]
  exact quenched_pathCylinder_locality ω η x n hωη _

lemma noDropFinite_measurable {d : ℕ} (ℓ : Vector d) (x : Lattice d) (n : ℕ) :
    Measurable (noDropFinite ℓ x n) :=
  (Kernel.measurable_coe _ (measurableSet_stayUntil _ n)).comp
    (measurable_id.prodMk measurable_const)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClippedInverse
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.recordCount_zero _root_.OAI.DirectionalTransience.regenerationTimes_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma quenched_stayUntil_ball_locality {d : ℕ} (ω η : Environment d) (x : Lattice d)
    (S : Set (Lattice d)) (n : ℕ) (hωη : Set.EqOn ω η (LatticeBall x n)) :
    quenchedKernel (ω, x) (StayUntil S n) = quenchedKernel (η, x) (StayUntil S n) := by
  let C : Set ((i : Finset.Iic n) → Lattice d) := {f | ∀ i, f i ∈ S}
  have hC : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C = StayUntil S n := by
    ext X
    exact ⟨fun h i hi => h ⟨i, Finset.mem_Iic.mpr hi⟩,
      fun h i => h i (Finset.mem_Iic.mp i.2)⟩
  rw [← hC]
  exact quenched_prefix_locality ω η x n hωη C

lemma noDropFinite_measurable_ball {d : ℕ} (ℓ : Vector d) (x : Lattice d) (n : ℕ) :
    @Measurable _ _ (rowSigma (LatticeBall x n)) _ (noDropFinite ℓ x n) := by
  apply measurable_of_row_locality _ (noDropFinite_measurable ℓ x n) _ x
    (by simp [LatticeBall])
  intro ω η h
  exact quenched_stayUntil_ball_locality ω η x _ n h

lemma noDropFinite_translation {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Lattice d) (n : ℕ) :
    noDropFinite ℓ x n ω = noDropFinite ℓ 0 n (fun a => ω (x + a)) := by
  let S : Set (Lattice d) := {y | dot (realPosition (0 : Lattice d)) ℓ ≤ dot (realPosition y) ℓ}
  have hm : Measurable (fun X : Path d => fun j => X j - x) := by fun_prop
  have h := congrArg (fun μ : Measure (Path d) => μ (StayUntil S n))
    (quenched_translation ω x 0)
  rw [Measure.map_apply hm (measurableSet_stayUntil S n)] at h
  have he : (fun X : Path d => fun j => X j - x) ⁻¹' StayUntil S n =
      StayUntil {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ} n := by
    ext X
    simp only [StayUntil, S, Set.mem_preimage, Set.mem_ofPred_eq, dot_realPosition_sub]
    simp only [dot, realPosition, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero]
    constructor <;> intro h j hj <;> have hh := h j hj <;> linarith
  simpa only [he, add_zero, noDropFinite] using h

lemma noDropQuenched_le_finite {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) (n : ℕ) : noDropQuenched ℓ x ω ≤ noDropFinite ℓ x n ω :=
  measure_mono (fun _ h i _ => h i)

lemma noDropFinite_tendsto {d : ℕ} (ℓ : Vector d) (x : Lattice d) (ω : Environment d) :
    Tendsto (fun n => noDropFinite ℓ x n ω) atTop (𝓝 (noDropQuenched ℓ x ω)) := by
  let S : Set (Lattice d) := {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ}
  have he : (⋂ n, StayUntil S n) = NoDrop ℓ x := by
    ext X
    exact ⟨fun h i => Set.mem_iInter.mp h i i le_rfl,
      fun h => Set.mem_iInter.mpr fun _ i _ => h i⟩
  have h := tendsto_measure_iInter_atTop
    (μ := quenchedKernel (ω, x)) (s := fun n => StayUntil S n)
    (fun n => (measurableSet_stayUntil S n).nullMeasurableSet)
    (fun _ _ hmn _ h j hj => h j (hj.trans hmn)) ⟨0, measure_ne_top _ _⟩
  simpa only [he, Function.comp_def, noDropFinite, noDropQuenched] using h

lemma clippedInverse_measurable (δ lam : ℝ) : Measurable (clippedInverse δ lam) :=
  (measurable_id.ennreal_toReal.max measurable_const).pow_const _

lemma clippedInverse_bounds (lam : ℝ) {δ : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam)
    (q : ℝ≥0∞) : 0 ≤ clippedInverse δ lam q ∧ clippedInverse δ lam q ≤ δ ^ (-lam) := by
  exact ⟨Real.rpow_nonneg (hδ.le.trans (le_max_right _ _)) _,
    Real.rpow_le_rpow_of_nonpos hδ (le_max_right _ _) (neg_nonpos.mpr hlam)⟩

lemma clippedInverse_antitone {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam)
    {q r : ℝ≥0∞} (hr : r ≠ ∞) (hqr : q ≤ r) :
    clippedInverse δ lam r ≤ clippedInverse δ lam q := by
  apply Real.rpow_le_rpow_of_nonpos (hδ.trans_le (le_max_right _ _))
    (max_le_max (ENNReal.toReal_mono hr hqr) le_rfl) (neg_nonpos.mpr hlam)

lemma clippedInverse_tendsto {α : Type*} {l : Filter α} {f : α → ℝ≥0∞}
    {q : ℝ≥0∞} (hq : q ≠ ∞) {δ : ℝ} (hδ : 0 < δ) (lam : ℝ)
    (hf : Tendsto f l (𝓝 q)) :
    Tendsto (fun a => clippedInverse δ lam (f a)) l (𝓝 (clippedInverse δ lam q)) :=
  (((ENNReal.tendsto_toReal hq).comp hf).max tendsto_const_nhds).rpow_const
    (Or.inl (ne_of_gt (hδ.trans_le (le_max_right _ _))))

lemma noDrop_clipped_inverse_L1 {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam) :
    Tendsto (fun n => ∫ ω, |clippedInverse δ lam (noDropQuenched ℓ x ω) -
      clippedInverse δ lam (noDropFinite ℓ x n ω)| ∂environmentLaw ν) atTop (𝓝 0) := by
  have hm (n : ℕ) := ((clippedInverse_measurable δ lam).comp (measurable_noDropQuenched ℓ x)).sub
    ((clippedInverse_measurable δ lam).comp (noDropFinite_measurable ℓ x n))
  have ht := tendsto_integral_of_dominated_convergence
    (μ := environmentLaw ν) (f := fun _ => (0 : ℝ))
    (fun _ => δ ^ (-lam)) (fun n => (hm n).abs.aestronglyMeasurable)
    (integrable_const _) (fun n => ?_) (Filter.Eventually.of_forall fun ω => ?_)
  · simpa using ht
  · exact Filter.Eventually.of_forall fun ω => by
      have hq := clippedInverse_bounds lam hδ hlam (noDropQuenched ℓ x ω)
      have hn := clippedInverse_bounds lam hδ hlam (noDropFinite ℓ x n ω)
      have hle := clippedInverse_antitone hδ hlam (measure_ne_top _ _)
        (noDropQuenched_le_finite ℓ x ω n)
      change clippedInverse δ lam (noDropFinite ℓ x n ω) ≤
        clippedInverse δ lam (noDropQuenched ℓ x ω) at hle
      simp only [Real.norm_eq_abs, abs_abs, Pi.sub_apply, Function.comp_apply]
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      linarith
  · have h := clippedInverse_tendsto (measure_ne_top _ _) hδ lam (noDropFinite_tendsto ℓ x ω)
    simpa only [noDropQuenched, sub_self, abs_zero, Pi.sub_apply, Function.comp_apply] using
      ((tendsto_const_nhds (x := clippedInverse δ lam (noDropQuenched ℓ x ω))).sub h).abs

lemma fresh_rows_prod {d : ℕ} {ι : Type*} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (s : Finset ι) (S : ι → Set (Lattice d)) (f : ι → Environment d → ℝ)
    (hS : (s : Set ι).Pairwise (fun i j => Disjoint (S i) (S j)))
    (hf : ∀ i ∈ s, @Measurable _ _ (rowSigma (S i)) _ (f i)) :
    (∫ ω, ∏ i ∈ s, f i ω ∂environmentLaw ν) =
      ∏ i ∈ s, ∫ ω, f i ω ∂environmentLaw ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hp : (s : Set ι).Pairwise (fun i j => Disjoint (S i) (S j)) :=
      hS.mono (by intro i hi; exact Finset.mem_insert_of_mem hi)
    have hm : @Measurable _ _ (rowSigma (⋃ i ∈ s, S i)) _
        (fun ω => ∏ i ∈ s, f i ω) := by
      apply Finset.measurable_fun_prod
      intro i hi
      exact (hf i (Finset.mem_insert_of_mem hi)).mono
        (rowSigma_mono (Set.subset_iUnion₂_of_subset i hi Set.Subset.rfl)) le_rfl
    have hd : Disjoint (S a) (⋃ i ∈ s, S i) := by
      apply Set.disjoint_iUnion_right.mpr
      intro i
      apply Set.disjoint_iUnion_right.mpr
      intro hi
      exact hS (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)
        (ne_of_mem_of_not_mem hi ha).symm
    simp only [Finset.prod_insert ha]
    rw [fresh_rows_factor ν hd (hf a (Finset.mem_insert_self _ _)) hm,
      ih hp (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma nonneg_prod_le_const {ι : Type*} (s : Finset ι) (f : ι → ℝ) {B : ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ B) :
    0 ≤ ∏ i ∈ s, f i ∧ ∏ i ∈ s, f i ≤ B ^ s.card := by
  refine ⟨Finset.prod_nonneg (fun i hi => (hf i hi).1), ?_⟩
  simpa only [Finset.prod_const] using
    Finset.prod_le_prod (fun i hi => (hf i hi).1) (fun i hi => (hf i hi).2)

lemma prod_difference_bound {ι : Type*} (s : Finset ι) (f g : ι → ℝ) {B : ℝ}
    (hB : 1 ≤ B) (hf : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ f i ∧ f i ≤ B) :
    (∏ i ∈ s, f i) ≤ (∏ i ∈ s, g i) + B ^ s.card * ∑ i ∈ s, (f i - g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hft i (hi : i ∈ s) := hf i (Finset.mem_insert_of_mem hi)
    have ih := ih hft
    have hP := nonneg_prod_le_const s g (fun i hi =>
      ⟨(hft i hi).1, (hft i hi).2.1.trans (hft i hi).2.2⟩)
    have hsum : 0 ≤ ∑ i ∈ s, (f i - g i) := by
      exact Finset.sum_nonneg fun i hi => sub_nonneg.mpr (hft i hi).2.1
    have hdiff : 0 ≤ f a - g a := sub_nonneg.mpr hfa.2.1
    have hb : 0 ≤ B ^ s.card := pow_nonneg (zero_le_one.trans hB) _
    have hbn : B ^ s.card ≤ B ^ s.card * B :=
      le_mul_of_one_le_right hb hB
    simp only [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      pow_succ]
    calc
      f a * (∏ i ∈ s, f i) ≤
          f a * ((∏ i ∈ s, g i) + B ^ s.card * ∑ i ∈ s, (f i - g i)) :=
        mul_le_mul_of_nonneg_left ih (hfa.1.trans hfa.2.1)
      _ = g a * (∏ i ∈ s, g i) + (f a - g a) * (∏ i ∈ s, g i) +
          f a * (B ^ s.card * ∑ i ∈ s, (f i - g i)) := by ring
      _ ≤ g a * (∏ i ∈ s, g i) + (f a - g a) * B ^ s.card +
          B * (B ^ s.card * ∑ i ∈ s, (f i - g i)) := by
        gcongr
        · exact hP.2
        · exact hfa.2.2
      _ ≤ g a * (∏ i ∈ s, g i) + (f a - g a) * (B ^ s.card * B) +
          B * (B ^ s.card * ∑ i ∈ s, (f i - g i)) := by
        gcongr
      _ = _ := by ring

lemma clipped_inverse_integral_translation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x : Lattice d) (δ lam : ℝ) :
    (∫ ω, clippedInverse δ lam (noDropQuenched ℓ x ω) ∂environmentLaw ν) =
      ∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν := by
  conv_lhs => enter [2, ω]; rw [noDropQuenched_translation ℓ ω x]
  have h := integral_map (μ := environmentLaw ν)
    (show AEMeasurable (fun ω : Environment d => fun a => ω (x + a)) (environmentLaw ν) from
      (by fun_prop : Measurable (fun ω : Environment d => fun a => ω (x + a))).aemeasurable)
    (((clippedInverse_measurable δ lam).comp (measurable_noDropQuenched ℓ 0)).aestronglyMeasurable)
  rw [environment_translation] at h
  exact h.symm

lemma clipped_inverse_finite_integral_translation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x : Lattice d) (δ lam : ℝ) (n : ℕ) :
    (∫ ω, clippedInverse δ lam (noDropFinite ℓ x n ω) ∂environmentLaw ν) =
      ∫ ω, clippedInverse δ lam (noDropFinite ℓ 0 n ω) ∂environmentLaw ν := by
  conv_lhs => enter [2, ω]; rw [noDropFinite_translation ℓ ω x n]
  have h := integral_map (μ := environmentLaw ν)
    (show AEMeasurable (fun ω : Environment d => fun a => ω (x + a)) (environmentLaw ν) from
      (by fun_prop : Measurable (fun ω : Environment d => fun a => ω (x + a))).aemeasurable)
    (((clippedInverse_measurable δ lam).comp (noDropFinite_measurable ℓ 0 n)).aestronglyMeasurable)
  rw [environment_translation] at h
  exact h.symm

lemma integrable_of_nonneg_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ a, 0 ≤ f a ∧ f a ≤ B) : Integrable f μ := by
  exact (MemLp.of_bound (p := 1) hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hb a).1] using (hb a).2)).integrable le_rfl

lemma clipped_inverse_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {f : Environment d → ℝ≥0∞} (hf : Measurable f) {δ lam : ℝ}
    (hδ : 0 < δ) (hlam : 0 ≤ lam) :
    Integrable (fun ω => clippedInverse δ lam (f ω)) (environmentLaw ν) :=
  integrable_of_nonneg_bound _ ((clippedInverse_measurable δ lam).comp hf)
    (fun _ => clippedInverse_bounds lam hδ hlam _)

lemma clipped_inverse_integral_gap {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam) (n : ℕ) :
    (∫ ω, clippedInverse δ lam (noDropQuenched ℓ x ω) -
      clippedInverse δ lam (noDropFinite ℓ x n ω) ∂environmentLaw ν) =
    ∫ ω, |clippedInverse δ lam (noDropQuenched ℓ 0 ω) -
      clippedInverse δ lam (noDropFinite ℓ 0 n ω)| ∂environmentLaw ν := by
  have hi y := clipped_inverse_integrable ν (measurable_noDropQuenched ℓ y) hδ hlam
  have hj y := clipped_inverse_integrable ν (noDropFinite_measurable ℓ y n) hδ hlam
  rw [integral_sub (hi x) (hj x), clipped_inverse_integral_translation,
    clipped_inverse_finite_integral_translation, ← integral_sub (hi 0) (hj 0)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => (abs_of_nonneg (sub_nonneg.mpr
    (clippedInverse_antitone hδ hlam (measure_ne_top _ _)
      (noDropQuenched_le_finite ℓ 0 ω n)))).symm

lemma separated_clipped_inverse_product {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x : Fin k → Lattice d,
      (Pairwise fun i j => Disjoint (LatticeBall (x i) n) (LatticeBall (x j) n)) →
      (∫ ω, ∏ i, clippedInverse δ lam (noDropQuenched ℓ (x i) ω) ∂environmentLaw ν) ≤
        (∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν) ^ k + ε := by
  classical
  let B := max 1 (δ ^ (-lam))
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hlim := (noDrop_clipped_inverse_L1 ν ℓ 0 hδ hlam).const_mul (B ^ k * (k : ℝ))
  simp only [mul_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hε).exists
  refine ⟨n, fun x hx => ?_⟩
  let f : Fin k → Environment d → ℝ := fun i ω =>
    clippedInverse δ lam (noDropQuenched ℓ (x i) ω)
  let g : Fin k → Environment d → ℝ := fun i ω =>
    clippedInverse δ lam (noDropFinite ℓ (x i) n ω)
  have hf i : Measurable (f i) :=
    (clippedInverse_measurable δ lam).comp (measurable_noDropQuenched ℓ (x i))
  have hg i : Measurable (g i) :=
    (clippedInverse_measurable δ lam).comp (noDropFinite_measurable ℓ (x i) n)
  have hfb i ω : 0 ≤ f i ω ∧ f i ω ≤ B :=
    ⟨(clippedInverse_bounds lam hδ hlam _).1,
      (clippedInverse_bounds lam hδ hlam _).2.trans (le_max_right _ _)⟩
  have hgb i ω : 0 ≤ g i ω ∧ g i ω ≤ B :=
    ⟨(clippedInverse_bounds lam hδ hlam _).1,
      (clippedInverse_bounds lam hδ hlam _).2.trans (le_max_right _ _)⟩
  have hgf i ω : g i ω ≤ f i ω := clippedInverse_antitone hδ hlam
    (measure_ne_top _ _) (noDropQuenched_le_finite ℓ (x i) ω n)
  have hfi i := integrable_of_nonneg_bound (environmentLaw ν) (hf i) (hfb i)
  have hgi i := integrable_of_nonneg_bound (environmentLaw ν) (hg i) (hgb i)
  have hfpi : Integrable (fun ω => ∏ i, f i ω) (environmentLaw ν) :=
    integrable_of_nonneg_bound _ (Finset.measurable_fun_prod _ (fun i _ => hf i))
      (fun ω => by
        simpa using nonneg_prod_le_const Finset.univ (fun i => f i ω)
          (fun i _ => hfb i ω))
  have hgpi : Integrable (fun ω => ∏ i, g i ω) (environmentLaw ν) :=
    integrable_of_nonneg_bound _ (Finset.measurable_fun_prod _ (fun i _ => hg i))
      (fun ω => by
        simpa using nonneg_prod_le_const Finset.univ (fun i => g i ω)
          (fun i _ => hgb i ω))
  have hsum : Integrable (fun ω => ∑ i, (f i ω - g i ω)) (environmentLaw ν) :=
    integrable_finsetSum _ (fun i _ => (hfi i).sub (hgi i))
  have hbd := integral_mono hfpi (hgpi.add (hsum.const_mul (B ^ k)))
    (fun ω => by
      simpa using prod_difference_bound Finset.univ
        (fun i => f i ω) (fun i => g i ω) hB
        (fun i _ => ⟨(hgb i ω).1, hgf i ω, (hfb i ω).2⟩))
  simp only [Pi.add_apply] at hbd
  rw [integral_add hgpi (hsum.const_mul (B ^ k)), integral_const_mul,
    integral_finsetSum (f := fun i ω => f i ω - g i ω) _
      (fun i _ => (hfi i).sub (hgi i))] at hbd
  have hprod : (∫ ω, ∏ i, g i ω ∂environmentLaw ν) =
      (∫ ω, clippedInverse δ lam (noDropFinite ℓ 0 n ω) ∂environmentLaw ν) ^ k := by
    rw [fresh_rows_prod ν Finset.univ (fun i => LatticeBall (x i) n) g
      (fun i _ j _ hij => hx hij) (fun i _ =>
        (clippedInverse_measurable δ lam).comp (noDropFinite_measurable_ball ℓ (x i) n))]
    simp only [g, clipped_inverse_finite_integral_translation ν ℓ _ δ lam n,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hgap i : (∫ ω, f i ω - g i ω ∂environmentLaw ν) =
      ∫ ω, |clippedInverse δ lam (noDropQuenched ℓ 0 ω) -
        clippedInverse δ lam (noDropFinite ℓ 0 n ω)| ∂environmentLaw ν :=
    clipped_inverse_integral_gap ν ℓ (x i) hδ hlam n
  simp only [hprod, hgap, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hbd
  have hle : (∫ ω, clippedInverse δ lam (noDropFinite ℓ 0 n ω) ∂environmentLaw ν) ≤
      ∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν :=
    integral_mono (clipped_inverse_integrable ν (noDropFinite_measurable ℓ 0 n) hδ hlam)
      (clipped_inverse_integrable ν (measurable_noDropQuenched ℓ 0) hδ hlam)
      (fun ω => clippedInverse_antitone hδ hlam (measure_ne_top _ _)
        (noDropQuenched_le_finite ℓ 0 ω n))
  have hpow := pow_le_pow_left₀
    (integral_nonneg (fun ω => (clippedInverse_bounds lam hδ hlam _).1)) hle k
  change (∫ ω, ∏ i, f i ω ∂environmentLaw ν) ≤ _
  exact hbd.trans (add_le_add hpow (by simpa only [mul_assoc] using hn.le))

lemma latticeBall_disjoint_of_coordinate_gap {d : ℕ} (i : Fin d)
    {x y : Lattice d} {n : ℕ} (hxy : (2 * n : ℤ) < |x i - y i|) :
    Disjoint (LatticeBall x n) (LatticeBall y n) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hx := hz i
  have hy := hz' i
  have hh := abs_add_le (x i - z i) (z i - y i)
  rw [sub_add_sub_cancel] at hh
  rw [abs_sub_comm (x i) (z i)] at hh
  omega

lemma noDrop_real_inverse_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
      Integrable (fun ω => (noDropQuenched ℓ 0 ω).toReal ^ (-lam)) (environmentLaw ν) := by
  obtain ⟨p, hp, hm⟩ := noDrop_inverse_moment ν hue ℓ hℓ htrans
  let lam := min p 1
  have hlam : 0 < lam := lt_min hp zero_lt_one
  have hfin : (∫⁻ ω, noDropQuenched ℓ 0 ω ^ (-lam) ∂environmentLaw ν) < ∞ := by
    apply lt_of_le_of_lt (lintegral_mono (fun ω => ?_)) hm
    exact ENNReal.rpow_le_rpow_of_exponent_ge (prob_le_one)
      (neg_le_neg (min_le_left p 1))
  refine ⟨lam, hlam, min_le_right _ _, ?_⟩
  simpa only [ENNReal.toReal_rpow] using
    integrable_toReal_of_lintegral_ne_top
      ((measurable_noDropQuenched ℓ 0).pow_const (-lam)).aemeasurable hfin.ne

lemma prod_max_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    (∏ i ∈ s, max (f i) δ) ≤ (∏ i ∈ s, f i) + δ := by
  classical
  by_cases h : ∀ i ∈ s, δ ≤ f i
  · have heq : (∏ i ∈ s, max (f i) δ) = ∏ i ∈ s, f i :=
      Finset.prod_congr rfl (fun i hi => max_eq_left (h i hi))
    rw [heq]
    exact le_add_of_nonneg_right hδ
  · push Not at h
    obtain ⟨i, hi, hif⟩ := h
    have hp := Finset.prod_le_prod_of_subset_of_le_one
      (show {i} ⊆ s from Finset.singleton_subset_iff.mpr hi)
      (f := fun j => max (f j) δ)
      (fun j hj => (hf j hj).1.trans (le_max_left _ _))
      (fun j hj _ => max_le (hf j hj).2 hδ1)
    simp only [Finset.prod_singleton, max_eq_right hif.le] at hp
    exact hp.trans (le_add_of_nonneg_left (Finset.prod_nonneg (fun j hj => (hf j hj).1)))

lemma noDropQuenched_toReal_le_one {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) : (noDropQuenched ℓ x ω).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono (show (1 : ℝ≥0∞) ≠ ∞ by simp)
    (show noDropQuenched ℓ x ω ≤ 1 from prob_le_one)

lemma noDropProduct_bounds {d k : ℕ} (ℓ : Vector d) (x : Fin k → Lattice d)
    (ω : Environment d) : 0 ≤ noDropProduct ℓ x ω ∧ noDropProduct ℓ x ω ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg),
    Finset.prod_le_one (fun _ _ => ENNReal.toReal_nonneg)
      (fun _ _ => noDropQuenched_toReal_le_one ℓ _ ω)⟩

lemma clippedNoDropProduct_bounds {d k : ℕ} (ℓ : Vector d) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : Fin k → Lattice d) (ω : Environment d) :
    δ ^ k ≤ clippedNoDropProduct ℓ δ x ω ∧ clippedNoDropProduct ℓ δ x ω ≤ 1 := by
  constructor
  · have h := Finset.prod_le_prod (s := Finset.univ)
      (f := fun _ : Fin k => δ) (g := fun i => max (noDropQuenched ℓ (x i) ω).toReal δ)
      (fun _ _ => hδ) (fun _ _ => le_max_right _ _)
    simpa [clippedNoDropProduct] using h
  · exact Finset.prod_le_one (fun _ _ => hδ.trans (le_max_right _ _))
      (fun _ _ => max_le (noDropQuenched_toReal_le_one ℓ _ ω) hδ1)

lemma clippedNoDropProduct_error {d k : ℕ} (ℓ : Vector d) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : Fin k → Lattice d) (ω : Environment d) :
    clippedNoDropProduct ℓ δ x ω ≤ noDropProduct ℓ x ω + δ := by
  exact prod_max_bound Finset.univ (fun i => (noDropQuenched ℓ (x i) ω).toReal)
    hδ hδ1 (fun _ _ => ⟨ENNReal.toReal_nonneg,
      noDropQuenched_toReal_le_one ℓ _ ω⟩)

lemma clippedNoDropProduct_measurable {d k : ℕ} (ℓ : Vector d) (δ : ℝ) :
    Measurable (fun z : Environment d × (Fin k → Lattice d) => clippedNoDropProduct ℓ δ z.2 z.1) := by
  apply measurable_from_prod_countable_left
  intro x
  exact Finset.measurable_fun_prod _ (fun i _ =>
    (measurable_noDropQuenched ℓ (x i)).ennreal_toReal.max measurable_const)

lemma clippedNoDropProduct_inverse {d k : ℕ} (ℓ : Vector d) {δ : ℝ}
    (hδ : 0 ≤ δ) (lam : ℝ) (x : Fin k → Lattice d) (ω : Environment d) :
    clippedNoDropProduct ℓ δ x ω ^ (-lam) =
      ∏ i, clippedInverse δ lam (noDropQuenched ℓ (x i) ω) := by
  exact (Real.finsetProd_rpow Finset.univ _
    (fun _ _ => hδ.trans (le_max_right _ _)) _).symm

lemma separated_noDropProduct_inverse_bound {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) {δ lam : ℝ}
    (hδ : 0 < δ) (hlam : 0 ≤ lam)
    (hpos : ∀ᵐ ω ∂environmentLaw ν, 0 < noDropQuenched ℓ 0 ω)
    (hmom : Integrable (fun ω => (noDropQuenched ℓ 0 ω).toReal ^ (-lam)) (environmentLaw ν))
    (k : ℕ) :
    ∃ n : ℕ, ∀ x : Fin k → Lattice d,
      (Pairwise fun i j => Disjoint (LatticeBall (x i) n) (LatticeBall (x j) n)) →
      (∫ ω, clippedNoDropProduct ℓ δ x ω ^ (-lam) ∂environmentLaw ν) ≤
        2 * (max 1 (∫ ω, (noDropQuenched ℓ 0 ω).toReal ^ (-lam) ∂environmentLaw ν)) ^ k := by
  obtain ⟨n, hn⟩ := separated_clipped_inverse_product ν ℓ hδ hlam k (show (0 : ℝ) < 1 by norm_num)
  refine ⟨n, fun x hx => ?_⟩
  simp_rw [clippedNoDropProduct_inverse ℓ hδ.le]
  have hle : (∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν) ≤
      ∫ ω, (noDropQuenched ℓ 0 ω).toReal ^ (-lam) ∂environmentLaw ν := by
    apply integral_mono_ae (clipped_inverse_integrable ν (measurable_noDropQuenched ℓ 0) hδ hlam) hmom
    filter_upwards [hpos] with ω hω
    exact Real.rpow_le_rpow_of_nonpos (ENNReal.toReal_pos hω.ne' (measure_ne_top _ _))
      (le_max_left _ _) (neg_nonpos.mpr hlam)
  have hnonneg : 0 ≤ ∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν :=
    integral_nonneg (fun ω => (clippedInverse_bounds lam hδ hlam
      (noDropQuenched ℓ 0 ω)).1)
  have hp := pow_le_pow_left₀ hnonneg (hle.trans (le_max_right 1 _)) k
  have h1 := one_le_pow₀ (n := k) (le_max_left 1
    (∫ ω, (noDropQuenched ℓ 0 ω).toReal ^ (-lam) ∂environmentLaw ν))
  have h := hn x hx
  nlinarith

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightSlab
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.recordCount_zero _root_.OAI.DirectionalTransience.regenerationTimes_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma convexOn_rpow_nonpos_Ici {δ p : ℝ} (hδ : 0 < δ) (hp : p ≤ 0) :
    ConvexOn ℝ (Set.Ici δ) (fun x : ℝ => x ^ p) := by
  refine ⟨convex_Ici δ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 := hδ.trans_le hx
  have hy0 := hδ.trans_le hy
  have hz : 0 < a • x + b • y :=
    hδ.trans_le ((convex_Ici δ) hx hy ha hb hab)
  have hl := (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).2 hx0 hy0 ha hb hab
  have he := convexOn_exp.2 (Set.mem_univ (p * Real.log x))
    (Set.mem_univ (p * Real.log y)) ha hb hab
  simp only [smul_eq_mul] at hl he hz ⊢
  rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hy0]
  calc
    Real.exp (Real.log (a * x + b * y) * p) ≤
      Real.exp (a * (p * Real.log x) + b * (p * Real.log y)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonpos_right hl hp]
    _ ≤ a * Real.exp (Real.log x * p) + b * Real.exp (Real.log y * p) := by
      simpa only [mul_comm p] using he

lemma inverse_jensen_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {δ B lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam) (hb : ∀ x, δ ≤ f x ∧ f x ≤ B) :
    (∫ x, f x ∂μ) ^ (-lam) ≤ ∫ x, (f x) ^ (-lam) ∂μ := by
  have hi : Integrable f μ :=
    (MemLp.of_bound (p := 1) hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hδ.le.trans (hb x).1)] using
          (hb x).2)).integrable le_rfl
  have hj : Integrable (fun x => (f x) ^ (-lam)) μ :=
    (MemLp.of_bound (p := 1) (hf.pow_const _).aestronglyMeasurable (δ ^ (-lam))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hδ.le.trans (hb x).1) _)]
        exact Real.rpow_le_rpow_of_nonpos hδ (hb x).1 (neg_nonpos.mpr hlam))).integrable le_rfl
  exact (convexOn_rpow_nonpos_Ici hδ (neg_nonpos.mpr hlam)).map_integral_le
    (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hδ.trans_le hx))))
    isClosed_Ici (Filter.Eventually.of_forall fun x => (hb x).1) hi hj

lemma inverse_mixture_markov {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) (π : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (F : Ω → A → ℝ) (hF : Measurable (Function.uncurry F)) (Q : Ω → ℝ)
    {δ₀ δ lam s K : ℝ} (hδ₀ : 0 < δ₀) (hlam : 0 ≤ lam) (hs : 0 < s) (hδs : δ ≤ s)
    (hb : ∀ ω a, δ₀ ≤ F ω a ∧ F ω a ≤ 1)
    (hQ : ∀ ω, (∫ a, F ω a ∂π) ≤ Q ω + δ)
    (hE : (∫ ω, ∫ a, (F ω a) ^ (-lam) ∂π ∂μ) ≤ K) :
    μ {ω | Q ω < 2 * s} ≤ ENNReal.ofReal ((3 * s) ^ lam * K) := by
  have hGi : Integrable (fun z : Ω × A => F z.1 z.2 ^ (-lam)) (μ.prod π) :=
    (MemLp.of_bound (p := 1) (hF.pow_const _).aestronglyMeasurable (δ₀ ^ (-lam))
      (Filter.Eventually.of_forall fun z => by
        change ‖F z.1 z.2 ^ (-lam)‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hδ₀.le.trans (hb z.1 z.2).1) _)]
        exact Real.rpow_le_rpow_of_nonpos hδ₀ (hb z.1 z.2).1
          (neg_nonpos.mpr hlam))).integrable le_rfl
  have hJi ω : Integrable (F ω) π :=
    (MemLp.of_bound (p := 1) (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun a => by
        change ‖F ω a‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (hδ₀.le.trans (hb ω a).1)]
        exact (hb ω a).2)).integrable le_rfl
  have hJpos ω : 0 < ∫ a, F ω a ∂π := by
    have hl := integral_mono (integrable_const δ₀) (hJi ω) (fun a => (hb ω a).1)
    have hl' : δ₀ ≤ ∫ a, F ω a ∂π := by simpa using hl
    exact hδ₀.trans_le hl'
  have hp : 0 < 3 * s := mul_pos (by norm_num) hs
  have hMeas := (hGi.integral_prod_left.const_mul ((3 * s) ^ lam)).measure_le_integral
    (Filter.Eventually.of_forall fun ω => mul_nonneg (Real.rpow_nonneg hp.le _)
      (integral_nonneg (fun a => Real.rpow_nonneg (hδ₀.le.trans (hb ω a).1) _)))
    (s := {ω | Q ω < 2 * s}) (fun ω hω => by
      have hJle : (∫ a, F ω a ∂π) ≤ 3 * s := by
        change Q ω < 2 * s at hω
        linarith [hQ ω]
      have hj := inverse_jensen_bounded π
        (hF.comp (measurable_const.prodMk measurable_id)) hδ₀ hlam (hb ω)
      have hr := Real.rpow_le_rpow_of_nonpos (hJpos ω) hJle (neg_nonpos.mpr hlam)
      calc
        1 = (3 * s) ^ lam * (3 * s) ^ (-lam) := by
          rw [← Real.rpow_add hp, add_neg_cancel, Real.rpow_zero]
        _ ≤ (3 * s) ^ lam * ∫ a, F ω a ^ (-lam) ∂π :=
          mul_le_mul_of_nonneg_left (hr.trans hj) (Real.rpow_nonneg hp.le _))
  rw [integral_const_mul] at hMeas
  exact hMeas.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hp.le _)))

theorem separated_initial_inverse_moment {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d)
    (hℓ : dot ℓ ℓ = 1) (htrans : DirectionallyTransient ν ℓ) (e : Fin d) :
    ∃ lam C : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < C ∧
      ∀ Bstar : ℝ, 0 < Bstar → ∀ k : ℕ, 1 ≤ k → ∃ G : ℕ,
      ∀ (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π],
        (∀ᵐ x ∂π, Pairwise fun i j => (G : ℤ) ≤ |x i e - x j e|) →
        ∀ s : ℝ, Real.exp (-Bstar) ≤ s →
        (environmentLaw ν) {ω | (∫ x, noDropProduct ℓ x ω ∂π) < 2 * s} ≤
          ENNReal.ofReal (Real.exp (C * k) * s ^ lam) := by
  classical
  obtain ⟨lam, hlam, hlam1, hmom⟩ := noDrop_real_inverse_moment ν hue ℓ hℓ htrans
  let M := max 1 (∫ ω, (noDropQuenched ℓ 0 ω).toReal ^ (-lam) ∂environmentLaw ν)
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let C := Real.log (6 * M)
  have hC : 0 < C := Real.log_pos (by linarith)
  refine ⟨lam, C, hlam, hlam1, hC, ?_⟩
  intro Bstar hBstar k hk
  let δ := Real.exp (-Bstar)
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hBstar.le)
  have hpos : ∀ᵐ ω ∂environmentLaw ν, 0 < noDropQuenched ℓ 0 ω := by
    filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans] with ω hω
    exact hω 0
  obtain ⟨n, hn⟩ := separated_noDropProduct_inverse_bound ν ℓ hδ hlam.le hpos hmom k
  refine ⟨2 * n + 1, ?_⟩
  intro π hπ hsep s hs
  have hs0 : 0 < s := hδ.trans_le hs
  let F : Environment d → (Fin k → Lattice d) → ℝ := fun ω x => clippedNoDropProduct ℓ δ x ω
  have hF : Measurable (Function.uncurry F) := clippedNoDropProduct_measurable ℓ δ
  have hb ω x : δ ^ k ≤ F ω x ∧ F ω x ≤ 1 :=
    clippedNoDropProduct_bounds ℓ hδ.le hδ1 x ω
  have hGi : Integrable (fun z : Environment d × (Fin k → Lattice d) =>
      F z.1 z.2 ^ (-lam)) ((environmentLaw ν).prod π) := by
    apply integrable_of_nonneg_bound _ (hF.pow_const _)
    intro z
    exact ⟨Real.rpow_nonneg ((pow_pos hδ k).le.trans (hb z.1 z.2).1) _,
      Real.rpow_le_rpow_of_nonpos (pow_pos hδ k) (hb z.1 z.2).1 (neg_nonpos.mpr hlam.le)⟩
  have hE : (∫ ω, ∫ x, F ω x ^ (-lam) ∂π ∂environmentLaw ν) ≤ 2 * M ^ k := by
    rw [integral_integral_swap hGi]
    have hh := integral_mono_ae hGi.integral_prod_right (integrable_const (2 * M ^ k))
      (hsep.mono fun x hx => hn x (fun i j hij => latticeBall_disjoint_of_coordinate_gap e
        (by have h := hx hij; omega)))
    simpa using hh
  have hQ ω : (∫ x, F ω x ∂π) ≤ (∫ x, noDropProduct ℓ x ω ∂π) + δ := by
    have hI : Integrable (noDropProduct ℓ · ω) π :=
      integrable_of_nonneg_bound π (measurable_of_countable _) (fun x => noDropProduct_bounds ℓ x ω)
    have hJ : Integrable (F ω) π :=
      integrable_of_nonneg_bound π (measurable_of_countable _) (fun x =>
        ⟨(pow_pos hδ k).le.trans (hb ω x).1, (hb ω x).2⟩)
    calc
      (∫ x, F ω x ∂π) ≤ ∫ x, noDropProduct ℓ x ω + δ ∂π :=
        integral_mono hJ (hI.add (integrable_const δ)) (clippedNoDropProduct_error ℓ hδ.le hδ1 · ω)
      _ = (∫ x, noDropProduct ℓ x ω ∂π) + δ := by simp [integral_add hI (integrable_const δ)]
  have hmark := inverse_mixture_markov (environmentLaw ν) π F hF
    (fun ω => ∫ x, noDropProduct ℓ x ω ∂π) (pow_pos hδ k) hlam.le hs0 hs hb hQ hE
  apply hmark.trans (ENNReal.ofReal_le_ofReal ?_)
  have h3 : (3 : ℝ) ^ lam ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 3 by norm_num) hlam1
  have h6 : (6 : ℝ) ≤ 6 ^ k := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 6 by norm_num) hk
    simpa only [pow_one] using h
  have hexp : Real.exp (C * k) = (6 * M) ^ k := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by positivity : 0 < 6 * M)]
  rw [hexp, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hs0.le, mul_pow]
  have hsp : 0 ≤ s ^ lam := Real.rpow_nonneg hs0.le _
  calc
    3 ^ lam * s ^ lam * (2 * M ^ k) ≤ 6 * M ^ k * s ^ lam := by
      nlinarith [mul_le_mul_of_nonneg_right h3 (mul_nonneg hsp (pow_nonneg hM0 k))]
    _ ≤ 6 ^ k * M ^ k * s ^ lam := by gcongr

lemma hit_concatenation {d : ℕ} {S₁ T₁ S₂ T₂ S : Set (Lattice d)}
    (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) :
    (⋃ n, HitAt S₁ T₁ n ∩ FutureEvent (fun _ => Hit S₂ T₂) n) ⊆ Hit S T₂ := by
  rintro X hX
  obtain ⟨n, hn, hfuture⟩ := Set.mem_iUnion.mp hX
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hfuture
  apply Set.mem_iUnion.mpr
  refine ⟨n + m, hm.1, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · exact h₁ (hn.2 j hjn)
  · have hn : n ≤ j := by omega
    have hsub : j - n < m := by omega
    have := h₂ (hm.2 (j - n) hsub)
    simpa only [Nat.add_sub_of_le hn] using this

lemma hitKernel_comp_le {d : ℕ} (ω : Environment d) (x : Lattice d)
    {S₁ T₁ S₂ T₂ S : Set (Lattice d)}
    (hST₁ : Disjoint S₁ T₁) (hST₂ : Disjoint S₂ T₂) (hST : Disjoint S T₂)
    (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) (U : Set (Lattice d)) :
    (∫⁻ y, hitKernel S₂ T₂ (ω, y) U ∂hitKernel S₁ T₁ (ω, x)) ≤
      hitKernel S T₂ (ω, x) U := by
  simp_rw [hitKernel_apply_eq_hit hST₂ U]
  rw [hitKernel_future ω x hST₁ (fun _ => Hit S₂ (T₂ ∩ U))
    (fun _ => measurableSet_hit _ _), hitKernel_apply_eq_hit hST U]
  exact measure_mono (hit_concatenation h₁ h₂)

lemma mass_smul_normalizedMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] :
    μ Set.univ • normalizedMeasure μ = μ := by
  by_cases hμ : μ Set.univ = 0
  · have hzero : μ = 0 := Measure.measure_univ_eq_zero.mp hμ
    simp [hzero, normalizedMeasure]
  · rw [normalizedMeasure, smul_smul,
      ENNReal.mul_inv_cancel hμ (measure_ne_top μ Set.univ), one_smul]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordIncrement
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma signedCoordinate_step_other {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1) :
    signedCoordinate e (step f) = 0 := by
  simp [signedCoordinate,step,hef]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OrderedTimes
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma fluctuationScale_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (r : ℝ) : 0 ≤ fluctuationScale μ S r := by
  apply div_nonneg (sq_nonneg _)
  exact integral_nonneg (fun x => le_min (sq_nonneg _) (sq_nonneg _))

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SuccessfulAverage
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma quenched_noDrop_subset_cross_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x H,
      NoDrop ℓ x ≤ᵐ[quenchedKernel (ω,x)] Cross ℓ x H := by
  filter_upwards [quenched_directionallyTransient_ae ν ℓ htrans] with ω hω x H
  filter_upwards [hω x] with X hX
  exact fun hD => noDrop_subset_cross_of_tendsto ℓ x X hX hD H

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_CoordinateKernelComp
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma coordinate_raw_kernel_comp_le {d : ℕ} (e : Direction d) (k m : ℕ)
    (ω : Environment d) (x : Lattice d) (U : Set (Lattice d)) :
    (∫⁻ y, hitKernel (Strip (realPosition (step e)) y m) (Upper (realPosition (step e)) y m) (ω,y) U
      ∂hitKernel (Strip (realPosition (step e)) x k) (Upper (realPosition (step e)) x k) (ω,x)) ≤
      hitKernel (Strip (realPosition (step e)) x (k+m)) (Upper (realPosition (step e)) x (k+m)) (ω,x) U := by
  let ℓ := realPosition (step e)
  let b := dot (realPosition x) ℓ+(k:ℝ)
  let c := dot (realPosition x) ℓ+((k+m:ℕ):ℝ)
  let S₂ : Set (Lattice d) := {y | b ≤ dot (realPosition y) ℓ ∧ dot (realPosition y) ℓ < c}
  let T₂ : Set (Lattice d) := {y | c ≤ dot (realPosition y) ℓ}
  have he : (∫⁻ y, hitKernel (Strip ℓ y m) (Upper ℓ y m) (ω,y) U
      ∂hitKernel (Strip ℓ x k) (Upper ℓ x k) (ω,x)) =
      ∫⁻ y, hitKernel S₂ T₂ (ω,y) U ∂hitKernel (Strip ℓ x k) (Upper ℓ x k) (ω,x) := by
    apply lintegral_congr_ae
    filter_upwards [coordinate_hitKernel_supported e x k ω] with y hy
    have hproj : dot (realPosition y) ℓ=b := by
      dsimp [ℓ,b]
      rw [signedHeight_projection,signedHeight_projection]
      exact_mod_cast hy
    have hS : Strip ℓ y m=S₂ := by
      ext z
      simp only [Strip,Set.mem_ofPred_eq,S₂,hproj,b,c,Nat.cast_add,add_assoc]
    have hT : Upper ℓ y m=T₂ := by
      ext z
      simp only [Upper,Set.mem_ofPred_eq,T₂,hproj,b,c,Nat.cast_add,add_assoc]
    rw [hS,hT]
  rw [he]
  have hd : Disjoint S₂ T₂ := Set.disjoint_left.mpr (fun y hy hz => (not_lt_of_ge hz) hy.2)
  have hT : T₂=Upper ℓ x (k+m) := by
    simp only [T₂,Upper,c,Nat.cast_add]
  have hk : Strip ℓ x k ⊆ Strip ℓ x (k+m) := by
    intro y hy
    refine ⟨hy.1,?_⟩
    dsimp [Strip] at hy ⊢
    have := Nat.cast_nonneg (α := ℝ) m
    linarith [hy.2]
  have hm : S₂ ⊆ Strip ℓ x (k+m) := by
    intro y hy
    refine ⟨?_,by simpa only [c,Nat.cast_add] using hy.2⟩
    dsimp [S₂,b,Strip] at hy ⊢
    have := Nat.cast_nonneg (α := ℝ) k
    linarith [hy.1]
  have hh := hitKernel_comp_le ω x (disjoint_strip_upper ℓ x k) hd
    (hT ▸ disjoint_strip_upper ℓ x (k+m)) hk hm U
  simpa only [hT] using hh
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TupleEndpoint
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience
namespace TupleKernel

lemma fin_tsum_product {A : Type*} (n : ℕ) (f : Fin n → A → ℝ≥0∞) :
    (∑' x : Fin n → A, ∏ j, f j (x j)) = ∏ j, ∑' x : A, f j x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih]

lemma measure_le_of_singletons {A : Type*} [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A] (μ ν : Measure A)
    (h : ∀ x, μ {x} ≤ ν {x}) : μ ≤ ν := by
  intro s
  conv_lhs => rw [← Measure.sum_smul_dirac μ]
  conv_rhs => rw [← Measure.sum_smul_dirac ν]
  simp only [Measure.sum_apply_of_countable, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul_left (h x) _

lemma countable_pi_mono {A : Type*} [MeasurableSpace A] [Countable A]
    [MeasurableSingletonClass A] (n : ℕ) (μ ν : Fin n → Measure A)
    [∀ j, SigmaFinite (μ j)] [∀ j, SigmaFinite (ν j)]
    (h : ∀ j, μ j ≤ ν j) : Measure.pi μ ≤ Measure.pi ν := by
  apply measure_le_of_singletons
  intro x
  simp only [Measure.pi_singleton]
  exact Finset.prod_le_prod' fun j _ => h j {x j}

lemma countable_pi_bind {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (n : ℕ) (μ : Fin n → Measure A) (K : Fin n → A → Measure B)
    [∀ j, SigmaFinite (μ j)] [∀ j x, SigmaFinite (K j x)]
    [∀ j, SigmaFinite ((μ j).bind (K j))] :
    (Measure.pi μ).bind (fun x => Measure.pi (fun j => K j (x j))) =
      Measure.pi (fun j => (μ j).bind (K j)) := by
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable]
  simp_rw [Measure.pi_singleton,Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable,
    lintegral_countable',Measure.pi_singleton,← Finset.prod_mul_distrib]
  exact fin_tsum_product n (fun j a => K j a {y j} * μ j {a})

end TupleKernel

lemma rawTupleEndpointLaw_comp_le {d k : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    rawTupleMixture (realPosition (step e)) m
      (rawTupleEndpointLaw (realPosition (step e)) h ω x) ω ≤
        rawTupleEndpointLaw (realPosition (step e)) (h+m) ω x := by
  let ℓ := realPosition (step e)
  let K := fun (n : ℕ) (y : Lattice d) => variableHitKernel ℓ n (ω,y)
  have hcomp (y : Lattice d) : (K h y).bind (K m) ≤ K (h+m) y := by
    intro U
    rw [Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable]
    change (∫⁻ a, hitKernel (Strip ℓ a (m : ℝ)) (Upper ℓ a (m : ℝ)) (ω,a) U
      ∂hitKernel (Strip ℓ y (h : ℝ)) (Upper ℓ y (h : ℝ)) (ω,y)) ≤
      hitKernel (Strip ℓ y ((h+m : ℕ) : ℝ)) (Upper ℓ y ((h+m : ℕ) : ℝ)) (ω,y) U
    simpa only [ℓ, Nat.cast_add] using coordinate_raw_kernel_comp_le e h m ω y U
  let : ∀ y, IsFiniteMeasure ((K h y).bind (K m)) := fun y =>
    ⟨lt_of_le_of_lt (hcomp y Set.univ) (measure_lt_top _ _)⟩
  change (Measure.pi (fun j => K h (x j))).bind (fun y => Measure.pi (fun j => K m (y j))) ≤
    Measure.pi (fun j => K (h+m) (x j))
  rw [TupleKernel.countable_pi_bind]
  exact TupleKernel.countable_pi_mono k _ _ (fun j => hcomp (x j))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SuccessfulWords
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma rawTupleWordLaw_endpoint {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    (rawTupleWordLaw ℓ H ω x).map (fun w j => wordPath (x j) (w j) (w j).length) =
      rawTupleEndpointLaw ℓ H ω x := by
  have he := Measure.pi_map_pi (μ := fun j : Fin k => rawWordLaw ℓ H ω (x j))
    (f := fun j w => wordPath (x j) w w.length)
    (fun _ => (measurable_of_countable _).aemeasurable)
  rw [rawTupleWordLaw,he]
  simp only [rawWordLaw_endpoint,rawTupleEndpointLaw]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_FiniteWordGeometry
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma wordWeight_append {d : ℕ} (ω : Environment d) (x : Lattice d)
    (u v : List (Direction d)) :
    wordWeight ω x (u ++ v) = wordWeight ω x u * wordWeight ω (wordPath x u u.length) v := by
  induction u generalizing x with
  | nil => simp [wordWeight,wordPath]
  | cons e u ih => simp only [List.cons_append,wordWeight,List.length_cons,wordPath,ih,mul_assoc]

lemma wordFirstHitTime_zero {d : ℕ} (e : Direction d) (x : Lattice d)
    (w : List (Direction d)) : wordFirstHitTime e x 0 w = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply wordFirstHitTime_le
  simp

lemma wordFirstHitTime_eq {d : ℕ} (e : Direction d) (x : Lattice d) (s : ℕ)
    (w : List (Direction d)) (n : ℕ)
    (hn : signedHeight e x+s ≤ signedHeight e (wordPath x w n))
    (hmin : ∀ i < n, signedHeight e (wordPath x w i) < signedHeight e x+s) :
    wordFirstHitTime e x s w = n := by
  apply le_antisymm (wordFirstHitTime_le e x s w hn)
  by_contra hc
  have hi : wordFirstHitTime e x s w < n := by omega
  exact (hmin _ hi).not_ge (wordFirstHitTime_spec e x s w ⟨n,hn⟩)

lemma wordFirstHitTime_append_prefix {d : ℕ} (e : Direction d) (x : Lattice d)
    (h s : ℕ) (hs : s ≤ h)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : List (Direction d)) :
    wordFirstHitTime e x s (u.val++v) = wordFirstHitTime e x s u.val := by
  have hend : signedHeight e x+s ≤ signedHeight e (wordPath x u.val u.val.length) := by
    rw [wordPath_hit_exact e x h u]; omega
  have hn := wordFirstHitTime_le e x s u.val hend
  apply wordFirstHitTime_eq
  · rw [wordPath_append_prefix x u.val v hn]
    exact wordFirstHitTime_spec e x s u.val ⟨u.val.length,hend⟩
  · intro i hi
    rw [wordPath_append_prefix x u.val v (hi.le.trans hn)]
    exact wordFirstHitTime_min e x s u.val hi

lemma wordFirstHitPosition_append_prefix {d : ℕ} (e : Direction d) (x : Lattice d)
    (h s : ℕ) (hs : s ≤ h)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : List (Direction d)) :
    wordFirstHitPosition e x s (u.val++v) = wordFirstHitPosition e x s u.val := by
  rw [wordFirstHitPosition,wordFirstHitTime_append_prefix e x h s hs u v]
  apply wordPath_append_prefix
  apply wordFirstHitTime_le
  rw [wordPath_hit_exact e x h u]
  omega

lemma wordFirstHitTime_append_suffix {d : ℕ} (e : Direction d) (x : Lattice d)
    (h m t : ℕ) (ht : t ≤ m)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : HitWord (wordPath x u.val u.val.length)
      (Strip (realPosition (step e)) (wordPath x u.val u.val.length) m)
      (Upper (realPosition (step e)) (wordPath x u.val u.val.length) m)) :
    wordFirstHitTime e x (h+t) (u.val++v.val) =
      u.val.length+wordFirstHitTime e (wordPath x u.val u.val.length) t v.val := by
  have hy := wordPath_hit_exact e x h u
  have hend : signedHeight e (wordPath x u.val u.val.length)+t ≤
      signedHeight e (wordPath (wordPath x u.val u.val.length) v.val v.val.length) := by
    rw [wordPath_hit_exact e _ m v]; omega
  apply wordFirstHitTime_eq
  · rw [wordPath_append_suffix,Nat.cast_add,← add_assoc,← hy]
    exact wordFirstHitTime_spec e _ t v.val ⟨v.val.length,hend⟩
  · intro i hi
    by_cases hui : i < u.val.length
    · rw [wordPath_append_prefix x u.val v.val hui.le]
      have hp := ((coordinate_mem_strip_iff e x _ h).mp (u.property.2 _ hui)).2
      push_cast; omega
    · have he : i = u.val.length+(i-u.val.length) := by omega
      rw [he,wordPath_append_suffix,Nat.cast_add,← add_assoc,← hy]
      apply wordFirstHitTime_min
      omega

lemma wordFirstHitPosition_append_suffix {d : ℕ} (e : Direction d) (x : Lattice d)
    (h m t : ℕ) (ht : t ≤ m)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : HitWord (wordPath x u.val u.val.length)
      (Strip (realPosition (step e)) (wordPath x u.val u.val.length) m)
      (Upper (realPosition (step e)) (wordPath x u.val u.val.length) m)) :
    wordFirstHitPosition e x (h+t) (u.val++v.val) =
      wordFirstHitPosition e (wordPath x u.val u.val.length) t v.val := by
  rw [wordFirstHitPosition,wordFirstHitTime_append_suffix e x h m t ht u v,
    wordPath_append_suffix]
  rfl

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordConcatenation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma coordinateWordConcat_injective {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ) :
    Function.Injective (coordinateWordConcat e x h m) := by
  intro u v huv
  have he : u.val.1++u.val.2 = v.val.1++v.val.2 := Subtype.ext_iff.mp huv
  have hlen (p : CoordinateSplit e x h m) :
      wordFirstHitTime e x h (p.val.1++p.val.2) = p.val.1.length := by
    have hf := wordFirstHitTime_append_prefix e x h h le_rfl (coordinateSplitFirst e x h m p) p.val.2
    have hg := wordFirstHitTime_endpoint e x h (coordinateSplitFirst e x h m p)
    exact hf.trans hg
  have hl : u.val.1.length = v.val.1.length := by rw [← hlen u,he,hlen v]
  have hp := List.append_inj he hl
  exact Subtype.ext (Prod.ext hp.1 hp.2)

namespace TupleKernel

lemma countable_map_apply {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (f : A → B) (b : B) :
    μ.map f {b} = ∑' a, if f a = b then μ {a} else 0 := by
  rw [← Measure.sum_smul_dirac μ,Measure.map_sum (measurable_of_countable _).aemeasurable,
    Measure.sum_apply_of_countable]
  congr 1
  funext a
  rw [Measure.map_smul,
    Measure.map_dirac' (measurable_of_countable _),Measure.smul_apply]
  by_cases ha : f a = b <;> simp [ha]

lemma countable_restricted_map_le {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (ν : Measure B) (S : Set A) (f : A → B)
    (hf : Set.InjOn f S) (hzero : ∀ a ∉ S, μ {a} = 0)
    (hatom : ∀ a ∈ S, μ {a} ≤ ν {f a}) : μ.map f ≤ ν := by
  apply measure_le_of_singletons
  intro b
  rw [countable_map_apply]
  by_cases hex : ∃ a ∈ S, f a = b
  · obtain ⟨a,ha,hab⟩ := hex
    rw [tsum_eq_single a]
    · simpa [hab] using hatom a ha
    · intro c hca
      by_cases hc : c ∈ S
      · have hne : f c ≠ b := fun he => hca (hf hc ha (he.trans hab.symm))
        simp only [ite_eq_right hne]
      · simp only [hzero c hc,ite_self]
  · have hz : ∀ a, (if f a = b then μ {a} else 0) = 0 := by
      intro a
      by_cases he : f a = b
      · rw [ite_eq_left he]
        exact hzero a (fun ha => hex ⟨a,ha,he⟩)
      · exact ite_eq_right he
    simp only [hz,tsum_zero,zero_le]

end TupleKernel

lemma rawWordPairLaw_singleton {d : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Lattice d) (u v : List (Direction d)) :
    rawWordPairLaw e h m ω x {(u,v)} =
      rawWordLaw (realPosition (step e)) h ω x {u} *
      rawWordLaw (realPosition (step e)) m ω (wordPath x u u.length) {v} := by
  rw [rawWordPairLaw,Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable,
    lintegral_countable']
  have he (a : List (Direction d)) :
      ((rawWordLaw (realPosition (step e)) m ω (wordPath x a a.length)).map (fun v => (a,v))) {(u,v)} =
      if a=u then rawWordLaw (realPosition (step e)) m ω (wordPath x a a.length) {v} else 0 := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    by_cases ha : a=u
    · subst a
      rw [ite_eq_left rfl]
      congr 1
      ext b
      simp
    · rw [ite_eq_right ha]
      have hset : (fun b => (a,b)) ⁻¹' {(u,v)} = (∅ : Set (List (Direction d))) := by
        ext b
        simp [ha]
      rw [hset,measure_empty]
  simp_rw [he]
  rw [tsum_eq_single u]
  · simp [mul_comm]
  · intro a ha
    simp [ha]

lemma rawWordPairLaw_invalid {d : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Lattice d) (p : List (Direction d) × List (Direction d))
    (hp : ¬ ValidWordSplit e x h m p) : rawWordPairLaw e h m ω x {p} = 0 := by
  rw [← Prod.eta p,rawWordPairLaw_singleton]
  simp only [rawWordLaw_singleton]
  unfold ValidWordSplit at hp
  by_cases h1 : wordPath x p.1 ∈ HitAt (Strip (realPosition (step e)) x h)
    (Upper (realPosition (step e)) x h) p.1.length
  · have h2 : ¬ wordPath (wordPath x p.1 p.1.length) p.2 ∈ HitAt
      (Strip (realPosition (step e)) (wordPath x p.1 p.1.length) m)
      (Upper (realPosition (step e)) (wordPath x p.1 p.1.length) m) p.2.length := fun h2 => hp ⟨h1,h2⟩
    simp only [ite_eq_left h1,ite_eq_right h2,mul_zero]
  · simp only [ite_eq_right h1,zero_mul]

lemma rawWordPairLaw_valid {d : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Lattice d) (p : CoordinateSplit e x h m) :
    rawWordPairLaw e h m ω x {p.val} =
      rawWordLaw (realPosition (step e)) (h+m) ω x {p.val.1++p.val.2} := by
  rw [← Prod.eta p.val,rawWordPairLaw_singleton]
  simp only [rawWordLaw_singleton,ite_eq_left p.property.1,ite_eq_left p.property.2]
  have hc := (coordinateWordConcat e x h m p).property
  change wordPath x (p.val.1++p.val.2) ∈ HitAt (Strip (realPosition (step e)) x (h+m : ℕ))
    (Upper (realPosition (step e)) x (h+m : ℕ)) (p.val.1++p.val.2).length at hc
  rw [ite_eq_left hc,wordWeight_append,ENNReal.ofReal_mul (wordWeight_nonneg ω x p.val.1)]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RelativeBudget
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma relativeWordDisplacement_append_prefix {d : ℕ} (e f : Direction d) (x : Lattice d)
    (h s : ℕ) (hs : s ≤ h)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : List (Direction d)) :
    relativeWordDisplacement e f x s (u.val++v) = relativeWordDisplacement e f x s u.val := by
  unfold relativeWordDisplacement
  rw [wordFirstHitPosition_append_prefix e x h s hs u v]

lemma relativeWordDisplacement_append_suffix {d : ℕ} (e f : Direction d) (x : Lattice d)
    (h m t : ℕ) (ht : t ≤ m)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : HitWord (wordPath x u.val u.val.length)
      (Strip (realPosition (step e)) (wordPath x u.val u.val.length) m)
      (Upper (realPosition (step e)) (wordPath x u.val u.val.length) m)) :
    relativeWordDisplacement e f x (h+t) (u.val++v.val) =
      relativeWordDisplacement e f x h u.val +
        relativeWordDisplacement e f (wordPath x u.val u.val.length) t v.val := by
  rw [relativeWordDisplacement_endpoint e f x h u]
  unfold relativeWordDisplacement
  rw [wordFirstHitPosition_append_suffix e x h m t ht u v]
  simp only [signedCoordinate_sub]
  ring

lemma tupleRelativeBudget_append {d k : ℕ} (e f : Direction d) (x : Fin k → Lattice d)
    (h m : ℕ) (r q : ℝ) (hq : 0 ≤ q)
    (u : ∀ j, HitWord (x j) (Strip (realPosition (step e)) (x j) h) (Upper (realPosition (step e)) (x j) h))
    (v : ∀ j, HitWord (wordPath (x j) (u j).val (u j).val.length)
      (Strip (realPosition (step e)) (wordPath (x j) (u j).val (u j).val.length) m)
      (Upper (realPosition (step e)) (wordPath (x j) (u j).val (u j).val.length) m))
    (hu : TupleRelativeBudget e f x h r (fun j => (u j).val))
    (hv : TupleRelativeBudget e f (fun j => wordPath (x j) (u j).val (u j).val.length)
      m q (fun j => (v j).val)) :
    TupleRelativeBudget e f x (h+m) (r+q) (fun j => (u j).val++(v j).val) := by
  intro s hs i j
  by_cases hsh : s ≤ h
  · rw [relativeWordDisplacement_append_prefix e f (x i) h s hsh (u i) (v i).val,
      relativeWordDisplacement_append_prefix e f (x j) h s hsh (u j) (v j).val]
    exact (hu s hsh i j).trans (le_add_of_nonneg_right hq)
  · have he : s = h+(s-h) := by omega
    have ht : s-h ≤ m := by omega
    rw [he,relativeWordDisplacement_append_suffix e f (x i) h m (s-h) ht (u i) (v i),
      relativeWordDisplacement_append_suffix e f (x j) h m (s-h) ht (u j) (v j)]
    have h1 := hu h le_rfl i j
    have h2 := hv (s-h) ht i j
    calc
      _ = |(relativeWordDisplacement e f (x i) h (u i).val -
        relativeWordDisplacement e f (x j) h (u j).val) +
        (relativeWordDisplacement e f (wordPath (x i) (u i).val (u i).val.length) (s-h) (v i).val -
        relativeWordDisplacement e f (wordPath (x j) (u j).val (u j).val.length) (s-h) (v j).val)| := by
          congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)

lemma relativeBudgetEndpointLaw_le {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    relativeBudgetEndpointLaw e f H r ω x ≤ rawTupleEndpointLaw (realPosition (step e)) H ω x := by
  rw [← rawTupleWordLaw_endpoint (realPosition (step e)) H ω x]
  exact Measure.map_mono Measure.restrict_le_self (measurable_of_countable _)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience
namespace TupleKernel

lemma dependentPair_singleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (K : A → Measure B) (a : A) (b : B) :
    dependentPair μ K {(a,b)} = μ {a} * K a {b} := by
  rw [dependentPair,Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable,
    lintegral_countable']
  have he (c : A) : ((K c).map (fun b => (c,b))) {(a,b)} = if c=a then K c {b} else 0 := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    by_cases hc : c=a
    · subst c
      rw [ite_eq_left rfl]
      congr 1
      ext y
      simp
    · rw [ite_eq_right hc]
      have hset : (fun y => (c,y)) ⁻¹' {(a,b)} = (∅ : Set B) := by
        ext y
        simp [hc]
      rw [hset,measure_empty]
  simp_rw [he]
  rw [tsum_eq_single a]
  · simp [mul_comm]
  · intro c hc
    simp [hc]

end TupleKernel

lemma rawTupleSplitLaw_singleton {d k : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) (u v : Fin k → List (Direction d)) :
    rawTupleSplitLaw e h m ω x {(u,v)} = ∏ j, rawWordPairLaw e h m ω (x j) {(u j,v j)} := by
  rw [rawTupleSplitLaw,TupleKernel.dependentPair_singleton]
  simp only [rawTupleWordLaw_singleton,rawWordPairLaw_singleton,tupleWordEndpoint,Finset.prod_mul_distrib]

lemma tupleWordConcat_injOn {d k : ℕ} (e : Direction d) (x : Fin k → Lattice d) (h m : ℕ) :
    Set.InjOn (tupleWordConcat (d := d) (k := k)) {p | ValidTupleSplit e x h m p} := by
  intro u hu v hv he
  have hi (j) : (u.1 j,u.2 j) = (v.1 j,v.2 j) := by
    apply congrArg Subtype.val
      (coordinateWordConcat_injective e (x j) h m (a₁ := ⟨(u.1 j,u.2 j),hu j⟩)
        (a₂ := ⟨(v.1 j,v.2 j),hv j⟩) _)
    exact Subtype.ext (congrFun he j)
  exact Prod.ext (funext fun j => congrArg Prod.fst (hi j)) (funext fun j => congrArg Prod.snd (hi j))

lemma rawTupleSplitLaw_invalid {d k : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d)
    (p : (Fin k → List (Direction d)) × (Fin k → List (Direction d)))
    (hp : ¬ ValidTupleSplit e x h m p) : rawTupleSplitLaw e h m ω x {p} = 0 := by
  rw [← Prod.eta p,rawTupleSplitLaw_singleton]
  obtain ⟨j,hj⟩ := not_forall.mp hp
  exact Finset.prod_eq_zero (Finset.mem_univ j)
    (rawWordPairLaw_invalid e h m ω (x j) (p.1 j,p.2 j) hj)

lemma rawTupleSplitLaw_valid {d k : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d)
    (p : (Fin k → List (Direction d)) × (Fin k → List (Direction d)))
    (hp : ValidTupleSplit e x h m p) : rawTupleSplitLaw e h m ω x {p} =
      rawTupleWordLaw (realPosition (step e)) (h+m) ω x {tupleWordConcat p} := by
  rw [← Prod.eta p,rawTupleSplitLaw_singleton,rawTupleWordLaw_singleton]
  apply Finset.prod_congr rfl
  intro j _
  exact rawWordPairLaw_valid e h m ω (x j) ⟨(p.1 j,p.2 j),hp j⟩

lemma relativeBudgetSplitLaw_singleton {d k : ℕ} (e f : Direction d) (h m : ℕ)
    (r q : ℝ) (ω : Environment d) (x : Fin k → Lattice d)
    (p : (Fin k → List (Direction d)) × (Fin k → List (Direction d))) :
    relativeBudgetSplitLaw e f h m r q ω x {p} =
      if TupleRelativeBudget e f x h r p.1 ∧
        TupleRelativeBudget e f (tupleWordEndpoint x p.1) m q p.2
      then rawTupleSplitLaw e h m ω x {p} else 0 := by
  rw [← Prod.eta p,relativeBudgetSplitLaw,TupleKernel.dependentPair_singleton,
    rawTupleSplitLaw,TupleKernel.dependentPair_singleton]
  simp only [relativeBudgetWordLaw_singleton]
  split_ifs <;> simp_all

lemma relativeBudgetWordLaw_comp_le {d k : ℕ} (e f : Direction d) (h m : ℕ)
    (r q : ℝ) (hq : 0 ≤ q) (ω : Environment d) (x : Fin k → Lattice d) :
    (relativeBudgetSplitLaw e f h m r q ω x).map tupleWordConcat ≤
      relativeBudgetWordLaw e f (h+m) (r+q) ω x := by
  let S := {p | ValidTupleSplit e x h m p ∧ TupleRelativeBudget e f x h r p.1 ∧
    TupleRelativeBudget e f (tupleWordEndpoint x p.1) m q p.2}
  apply TupleKernel.countable_restricted_map_le _ _ S
  · intro a ha b hb he
    exact tupleWordConcat_injOn e x h m ha.1 hb.1 he
  · intro p hp
    rw [relativeBudgetSplitLaw_singleton]
    by_cases hbudget : TupleRelativeBudget e f x h r p.1 ∧
        TupleRelativeBudget e f (tupleWordEndpoint x p.1) m q p.2
    · rw [ite_eq_left hbudget]
      exact rawTupleSplitLaw_invalid e h m ω x p (fun hval => hp ⟨hval,hbudget⟩)
    · exact ite_eq_right hbudget
  · intro p hp
    rw [relativeBudgetSplitLaw_singleton,ite_eq_left hp.2,rawTupleSplitLaw_valid e h m ω x p hp.1,
      relativeBudgetWordLaw_singleton]
    have hc : TupleRelativeBudget e f x (h+m) (r+q) (tupleWordConcat p) :=
      tupleRelativeBudget_append e f x h m r q hq
        (fun j => coordinateSplitFirst e (x j) h m ⟨(p.1 j,p.2 j),hp.1 j⟩)
        (fun j => coordinateSplitSecond e (x j) h m ⟨(p.1 j,p.2 j),hp.1 j⟩) hp.2.1 hp.2.2
    rw [ite_eq_left hc]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetAdapted
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma relativeBudgetWordLaw_rows {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (x : Fin k → Lattice d) (S : Set (Lattice d))
    (hx : ∀ j, Strip (realPosition (step e)) (x j) H ⊆ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω => relativeBudgetWordLaw e f H r ω x) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply TupleKernel.measurable_countable_measure
  intro w
  simp only [relativeBudgetWordLaw,TupleKernel.restrict_singleton]
  by_cases hb : TupleRelativeBudget e f x H r w
  · simp only [hb,Set.mem_ofPred_eq,ite_eq_left,rawTupleWordLaw_singleton]
    apply Finset.measurable_prod
    intro j _
    exact (Measure.measurable_coe (measurableSet_singleton (w j))).comp
      ((measurable_rawWordLaw_rows (realPosition (step e)) H (x j)).mono
        (rowSigma_mono (hx j)) le_rfl)
  · simp only [Set.mem_ofPred_eq,hb,ite_false, if_false]
    exact measurable_const

lemma relativeBudgetMassENN_joint_rows {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (C : Set (Fin k → Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, ∀ j, Strip (realPosition (step e)) (x j) H ⊆ S) :
    @Measurable (SupportedTupleMeasures C × Environment d) ℝ≥0∞
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => relativeBudgetMassENN e f H r p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  simp only [relativeBudgetMassENN,lintegral_countable']
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ C
  · exact (((Measure.measurable_coe MeasurableSet.univ).comp
      (relativeBudgetWordLaw_rows e f H r x S (hC x hx))).comp measurable_snd).mul
      ((Measure.measurable_coe (measurableSet_singleton x)).comp
        (measurable_subtype_coe.comp measurable_fst))
  · have he : (fun p : SupportedTupleMeasures C × Environment d =>
        relativeBudgetWordLaw e f H r p.2 x Set.univ*p.1.val {x}) = fun _ => 0 := by
      funext p
      rw [supportedTupleMeasures_singleton C p.1 hx,mul_zero]
    rw [he]
    exact measurable_const

lemma relativeBudgetMassENN_toReal {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π]
    (ω : Environment d) : (relativeBudgetMassENN e f H r π ω).toReal =
      relativeBudgetMass e f H r π ω := by
  symm
  exact integral_toReal (measurable_of_countable _).aemeasurable
    (ae_of_all _ fun x => measure_lt_top (relativeBudgetWordLaw e f H r ω x) Set.univ)

lemma budgetTraversalMass_adapted {d k : ℕ} (e f : Direction d) (a r : ℝ)
    (π : Environment d → SupportedTupleMeasures (TupleAtHeight (k := k) (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    Adapted (rowHeightFiltration (realPosition (step e)) a) (budgetTraversalMass e f a r π) := by
  intro h
  by_cases hh : h=0
  · simp only [hh]
    exact measurable_const
  · have hle : rowSigma (BelowHeight (realPosition (step e)) a) ≤
        rowSigma (BelowHeight (realPosition (step e)) (a+h)) := by
      apply rowSigma_mono
      intro y hy
      dsimp [BelowHeight] at hy ⊢
      have : (0:ℝ) ≤ h := Nat.cast_nonneg h
      linarith
    have hC (x : Fin k → Lattice d) (hx : x ∈ TupleAtHeight (k := k) (realPosition (step e)) a) :
        ∀ j, Strip (realPosition (step e)) (x j) h ⊆ BelowHeight (realPosition (step e)) (a+h) := by
      intro j y hy
      change dot (realPosition y) (realPosition (step e)) < a+h
      simpa only [hx j] using hy.2
    have hp := hπ.mono hle le_rfl
    have hm := (relativeBudgetMassENN_joint_rows e f h r (TupleAtHeight (k := k) (realPosition (step e)) a)
      (BelowHeight (realPosition (step e)) (a+h)) hC).comp (hp.prodMk measurable_id)
    change @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+h))) _ _
    unfold budgetTraversalMass
    simp only [ite_eq_right hh]
    exact hm

lemma budgetFirstThreat_stopping {d k : ℕ} (e f : Direction d) (a r g : ℝ)
    (π : Environment d → SupportedTupleMeasures (TupleAtHeight (k := k) (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) (H : ℕ) :
    IsStoppingTime (rowHeightFiltration (realPosition (step e)) a)
      (fun ω => (budgetFirstThreat e f a r g π H ω : WithTop ℕ)) :=
  (budgetTraversalMass_adapted e f a r π hπ).isStoppingTime_hittingBtwn measurableSet_Iio

lemma before_budgetFirstThreat_pass {d k : ℕ} (e f : Direction d) (a r g : ℝ)
    (π : Environment d → SupportedTupleMeasures (TupleAtHeight (k := k) (realPosition (step e)) a))
    (H : ℕ) (ω : Environment d) {j : ℕ} (hj : 0 < j)
    (hjlt : j < budgetFirstThreat e f a r g π H ω) :
    ENNReal.ofReal g ≤ relativeBudgetMassENN e f j r (π ω).val ω := by
  have hn := notMem_of_lt_hittingBtwn hjlt hj
  simpa only [budgetTraversalMass,ite_eq_right (Nat.ne_of_gt hj),Set.mem_Iio,not_lt] using hn

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma relativeWordDisplacement_zero {d : ℕ} (e f : Direction d) (x : Lattice d)
    (w : List (Direction d)) : relativeWordDisplacement e f x 0 w = 0 := by
  have ht : wordFirstHitTime e x 0 w = 0 := Nat.eq_zero_of_le_zero
    (wordFirstHitTime_le e x 0 w (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  simp [relativeWordDisplacement,wordFirstHitPosition,ht,signedCoordinate]

lemma upwardWord_budget {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (x : Fin k → Lattice d) : TupleRelativeBudget e f x 1 0 (fun _ => [e]) := by
  intro s hs i j
  interval_cases s
  · simp only [relativeWordDisplacement_zero,sub_self,abs_zero,le_refl]
  · have hd (y : Lattice d) : relativeWordDisplacement e f y 1 [e] = 0 := by
      rw [show [e] = (upwardHitWord e y).val from rfl,
        relativeWordDisplacement_endpoint e f y 1 (upwardHitWord e y)]
      simp only [upwardHitWord,List.length_singleton,wordPath,add_sub_cancel_left,
        signedCoordinate_step_other f e hef.symm]
    simp only [hd,sub_self,abs_zero,le_refl]

lemma tupleAppendUpward_injective {d k : ℕ} (e : Direction d) :
    Function.Injective (tupleAppendUpward (k := k) e) := by
  intro u v h
  funext j
  exact List.append_cancel_right (congrFun h j)

lemma tupleAppendUpward_budget {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (x : Fin k → Lattice d) (H : ℕ) (r : ℝ)
    (w : ∀ j, HitWord (x j) (Strip (realPosition (step e)) (x j) H) (Upper (realPosition (step e)) (x j) H))
    (hb : TupleRelativeBudget e f x H r (fun j => (w j).val)) :
    TupleRelativeBudget e f x (H+1) r (tupleAppendUpward e (fun j => (w j).val)) := by
  change TupleRelativeBudget e f x (H+1) r (fun j => (w j).val++[e])
  simpa only [add_zero,upwardHitWord] using
    tupleRelativeBudget_append e f x H 1 r 0 le_rfl w
      (fun j => upwardHitWord e (wordPath (x j) (w j).val (w j).val.length)) hb
      (upwardWord_budget e f hef _)

lemma rawWordLaw_upward_atom {d : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d)
    (x : Lattice d)
    (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)) :
    rawWordLaw (realPosition (step e)) (H+1) ω x {w.val++[e]} =
      rawWordLaw (realPosition (step e)) H ω x {w.val} *
        ((ω (wordPath x w.val w.val.length)).1 e : ℝ≥0∞) := by
  have hc := wordPath_hit_append e x H 1 w (upwardHitWord e (wordPath x w.val w.val.length))
  change wordPath x (w.val++[e]) ∈ HitAt (Strip (realPosition (step e)) x (H+1:ℕ))
    (Upper (realPosition (step e)) x (H+1:ℕ)) (w.val++[e]).length at hc
  rw [rawWordLaw_singleton,ite_eq_left hc,rawWordLaw_singleton,ite_eq_left w.property,
    wordWeight_append,ENNReal.ofReal_mul (wordWeight_nonneg _ _ _)]
  simp only [wordWeight,mul_one,ENNReal.ofReal_coe_nnreal]

lemma relativeBudgetWordLaw_upward {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d)
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ : ℝ≥0∞)^k • (relativeBudgetWordLaw e f H r ω x).map (tupleAppendUpward e) ≤
      relativeBudgetWordLaw e f (H+1) r ω x := by
  rw [← Measure.map_smul]
  let S : Set (Fin k → List (Direction d)) := {w | TupleRelativeBudget e f x H r w ∧
    ∀ j, wordPath (x j) (w j) ∈ HitAt (Strip (realPosition (step e)) (x j) H)
      (Upper (realPosition (step e)) (x j) H) (w j).length}
  apply TupleKernel.countable_restricted_map_le _ _ S _ (tupleAppendUpward_injective e).injOn
  · intro w hw
    rw [Measure.smul_apply,smul_eq_mul,relativeBudgetWordLaw_singleton]
    by_cases hb : TupleRelativeBudget e f x H r w
    · rw [ite_eq_left hb,rawTupleWordLaw_singleton]
      have hj : ∃ j, ¬ wordPath (x j) (w j) ∈ HitAt (Strip (realPosition (step e)) (x j) H)
          (Upper (realPosition (step e)) (x j) H) (w j).length := by
        by_contra hn
        push Not at hn
        exact hw ⟨hb,hn⟩
      obtain ⟨j,hj⟩ := hj
      have hz := Finset.prod_eq_zero (f := fun j => rawWordLaw (realPosition (step e)) H ω (x j) {w j}) (Finset.mem_univ j)
        (show rawWordLaw (realPosition (step e)) H ω (x j) {w j}=0 by rw [rawWordLaw_singleton,ite_eq_right hj])
      rw [hz,mul_zero]
    · rw [ite_eq_right hb,mul_zero]
  · intro w hw
    let u j : HitWord (x j) (Strip (realPosition (step e)) (x j) H) (Upper (realPosition (step e)) (x j) H) :=
      ⟨w j,hw.2 j⟩
    have hb := tupleAppendUpward_budget e f hef x H r u hw.1
    rw [Measure.smul_apply,smul_eq_mul,relativeBudgetWordLaw_singleton,ite_eq_left hw.1,
      relativeBudgetWordLaw_singleton,ite_eq_left hb,rawTupleWordLaw_singleton,rawTupleWordLaw_singleton]
    have he (j : Fin k) : rawWordLaw (realPosition (step e)) (H+1) ω (x j) {tupleAppendUpward e w j} =
        rawWordLaw (realPosition (step e)) H ω (x j) {w j} *
          ((ω (wordPath (x j) (w j) (w j).length)).1 e : ℝ≥0∞) := rawWordLaw_upward_atom e H ω (x j) (u j)
    simp_rw [he]
    rw [Finset.prod_mul_distrib,mul_comm]
    apply mul_le_mul_right
    calc
      (κ : ℝ≥0∞)^k = ∏ _j : Fin k, (κ : ℝ≥0∞) := by simp
      _ ≤ _ := Finset.prod_le_prod' fun j _ => ENNReal.coe_le_coe.mpr (hκ _)

lemma relativeBudgetMassENN_upward {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (H : ℕ) (r : ℝ) (ω : Environment d) (π : Measure (Fin k → Lattice d))
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ : ℝ≥0∞)^k * relativeBudgetMassENN e f H r π ω ≤
      relativeBudgetMassENN e f (H+1) r π ω := by
  rw [relativeBudgetMassENN,← lintegral_const_mul _ (measurable_of_countable _)]
  apply lintegral_mono
  intro x
  have ht := relativeBudgetWordLaw_upward e f hef H r ω x κ hκ Set.univ
  simpa only [Measure.smul_apply,smul_eq_mul,Measure.map_apply (measurable_of_countable _) MeasurableSet.univ,
    Set.preimage_univ] using ht

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetEndpoint
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience
namespace TupleKernel

lemma countable_map_bind {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [Countable A] [Countable B] [Countable C]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (μ : Measure A) (K : A → Measure B) (F : B → C) :
    (μ.bind K).map F = μ.bind (fun a => (K a).map F) := by
  ext s hs
  rw [Measure.map_apply (measurable_of_countable _) hs,
    Measure.bind_apply ((measurable_of_countable F) hs) (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hs (measurable_of_countable _).aemeasurable]
  congr 1
  funext a
  exact (Measure.map_apply (measurable_of_countable _) hs).symm

lemma countable_bind_map {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [Countable A] [Countable B] [Countable C]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (μ : Measure A) (F : A → B) (K : B → Measure C) :
    (μ.map F).bind K = μ.bind (fun a => K (F a)) := by
  ext s hs
  rw [Measure.bind_apply hs (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hs (measurable_of_countable _).aemeasurable,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

lemma dependentPair_map {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [Countable A] [Countable B] [Countable C]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (μ : Measure A) (K : A → Measure B) (F : A × B → C) :
    (dependentPair μ K).map F = μ.bind (fun a => (K a).map (fun b => F (a,b))) := by
  rw [dependentPair,countable_map_bind]
  congr 1
  funext a
  exact Measure.map_map (measurable_of_countable _) (measurable_of_countable _)

lemma countable_bind_mono {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (K L : A → Measure B) (h : ∀ a, K a ≤ L a) : μ.bind K ≤ μ.bind L := by
  intro s
  rw [Measure.bind_apply (Set.to_countable s).measurableSet (measurable_of_countable _).aemeasurable,
    Measure.bind_apply (Set.to_countable s).measurableSet (measurable_of_countable _).aemeasurable]
  exact lintegral_mono fun a => h a s

end TupleKernel

lemma tupleWordEndpoint_concat {d k : ℕ} (x : Fin k → Lattice d)
    (p : (Fin k → List (Direction d)) × (Fin k → List (Direction d))) :
    tupleWordEndpoint x (tupleWordConcat p) = tupleWordEndpoint (tupleWordEndpoint x p.1) p.2 := by
  funext j
  exact (show wordPath (x j) (p.1 j++p.2 j) (p.1 j++p.2 j).length =
    wordPath (wordPath (x j) (p.1 j) (p.1 j).length) (p.2 j) (p.2 j).length by
      rw [List.length_append,wordPath_append_suffix])

lemma relativeBudgetEndpointLaw_comp_le {d k : ℕ} (e f : Direction d) (h m : ℕ)
    (r q : ℝ) (hq : 0 ≤ q) (ω : Environment d) (x : Fin k → Lattice d) :
    (relativeBudgetEndpointLaw e f h r ω x).bind (relativeBudgetEndpointLaw e f m q ω) ≤
      relativeBudgetEndpointLaw e f (h+m) (r+q) ω x := by
  have hm := Measure.map_mono (relativeBudgetWordLaw_comp_le e f h m r q hq ω x)
    (measurable_of_countable (tupleWordEndpoint x))
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hm
  have he : (tupleWordEndpoint x ∘ tupleWordConcat) = fun p => tupleWordEndpoint (tupleWordEndpoint x p.1) p.2 := by
    funext p; exact tupleWordEndpoint_concat x p
  rw [he,relativeBudgetSplitLaw,TupleKernel.dependentPair_map] at hm
  change _ ≤ (relativeBudgetWordLaw e f (h+m) (r+q) ω x).map (tupleWordEndpoint x)
  rw [relativeBudgetEndpointLaw,TupleKernel.countable_bind_map]
  exact hm

lemma budgetEndpointMixture_comp_le {d k : ℕ} (e f : Direction d) (h m : ℕ)
    (r q : ℝ) (hq : 0 ≤ q) (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    budgetEndpointMixture e f m q (budgetEndpointMixture e f h r π ω) ω ≤
      budgetEndpointMixture e f (h+m) (r+q) π ω := by
  unfold budgetEndpointMixture
  rw [Measure.bind_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  exact TupleKernel.countable_bind_mono _ _ _ fun x => relativeBudgetEndpointLaw_comp_le e f h m r q hq ω x

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetNormalize
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma normalizeOr_mass {α : Type*} [MeasurableSpace α] (μ ρ : Measure α)
    [IsFiniteMeasure μ] : μ Set.univ • normalizeOr μ ρ = μ := by
  by_cases h : μ Set.univ=0
  · rw [h,zero_smul]; exact (Measure.measure_univ_eq_zero.mp h).symm
  · rw [normalizeOr,ite_eq_right h,mass_smul_normalizedMeasure]

lemma BudgetProfile.measurable_toSupported {d k : ℕ} (e f : Direction d) (a G : ℝ) :
    Measurable (BudgetProfile.toSupported (d:=d) (k:=k) (e:=e) (f:=f) (a:=a) (G:=G)) :=
  measurable_subtype_coe.subtype_mk

lemma nextBudgetProfile_mass {d k : ℕ} (e f : Direction d) (H : ℕ) (a G r : ℝ)
    (hr : 0 ≤ r) (π : BudgetProfile (k:=k) e f a G) (ω : Environment d) :
    relativeBudgetMassENN e f H r π.val ω •
      (nextBudgetProfile e f H a G r hr π ω).val = budgetEndpointMixture e f H r π.val ω := by
  change _ • normalizeOr _ _ = _
  rw [← budgetEndpointMixture_univ]
  exact normalizeOr_mass _ _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetMeasurable
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma relativeBudgetEndpointLaw_rows {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (x : Fin k → Lattice d) (S : Set (Lattice d))
    (hx : ∀ j, Strip (realPosition (step e)) (x j) H ⊆ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω => relativeBudgetEndpointLaw e f H r ω x) := by
  exact (Measure.measurable_map _ (measurable_of_countable _)).comp
    (relativeBudgetWordLaw_rows e f H r x S hx)

lemma budgetEndpointMixture_joint_rows {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (C : Set (Fin k → Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, ∀ j, Strip (realPosition (step e)) (x j) H ⊆ S) :
    @Measurable (SupportedTupleMeasures C × Environment d) (Measure (Fin k → Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => budgetEndpointMixture e f H r p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [budgetEndpointMixture_apply,lintegral_countable']
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ C
  · exact (((Measure.measurable_coe hA).comp
      (relativeBudgetEndpointLaw_rows e f H r x S (hC x hx))).comp measurable_snd).mul
      ((Measure.measurable_coe (measurableSet_singleton x)).comp
        (measurable_subtype_coe.comp measurable_fst))
  · have he : (fun p : SupportedTupleMeasures C × Environment d =>
        relativeBudgetEndpointLaw e f H r p.2 x A*p.1.val {x}) = fun _ => 0 := by
      funext p
      rw [supportedTupleMeasures_singleton C p.1 hx,mul_zero]
    rw [he]
    exact measurable_const

lemma budgetProfileMass_joint_rows {d k : ℕ} (e f : Direction d) (a G : ℝ)
    (H : ℕ) (r : ℝ) (S : Set (Lattice d))
    (hS : ∀ x ∈ TupleAtHeight (k:=k) (realPosition (step e)) a,
      ∀ j, Strip (realPosition (step e)) (x j) H ⊆ S) :
    @Measurable (BudgetProfile (k:=k) e f a G × Environment d) ℝ
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => relativeBudgetMass e f H r p.1.val p.2) := by
  have hm := (relativeBudgetMassENN_joint_rows e f H r _ S hS).comp
    (((BudgetProfile.measurable_toSupported e f a G).comp measurable_fst).prodMk measurable_snd)
  have he : (fun p : BudgetProfile (k:=k) e f a G × Environment d =>
      relativeBudgetMass e f H r p.1.val p.2) =
      fun p => (relativeBudgetMassENN e f H r p.1.val p.2).toReal := by
    funext p; exact (relativeBudgetMassENN_toReal e f H r _ _).symm
  rw [he]
  exact hm.ennreal_toReal

lemma nextBudgetProfile_measurable_rows {d k : ℕ} (e f : Direction d) (a G r : ℝ)
    (hr : 0 ≤ r) (H : ℕ) (S : Set (Lattice d))
    (hS : ∀ x ∈ TupleAtHeight (k:=k) (realPosition (step e)) a,
      ∀ j, Strip (realPosition (step e)) (x j) H ⊆ S)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma S) _ π) :
    @Measurable _ _ (rowSigma S) _ (fun ω => nextBudgetProfile e f H a G r hr (π ω) ω) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  have hm := (budgetEndpointMixture_joint_rows e f H r _ S hS).comp
    (((BudgetProfile.measurable_toSupported e f a G).comp hπ).prodMk measurable_id)
  have hρ := (Measure.measurable_map (tupleShiftUp e H) (measurable_of_countable _)).comp
    (measurable_subtype_coe.comp hπ)
  exact (measurable_normalizeOr _ _ hm hρ).subtype_mk

lemma nextBudgetProfile_measurable_below {d k : ℕ} (e f : Direction d) (a G r : ℝ)
    (hr : 0 ≤ r) (H : ℕ)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+H))) _
      (fun ω => nextBudgetProfile e f H a G r hr (π ω) ω) := by
  apply nextBudgetProfile_measurable_rows
  · intro x hx j y hy
    change dot (realPosition y) (realPosition (step e)) < a+H
    simpa only [hx j] using hy.2
  · exact hπ.mono (rowSigma_mono (by
      intro x hx
      change dot (realPosition x) (realPosition (step e)) < a+H
      have hn : (0:ℝ) ≤ H := Nat.cast_nonneg H
      exact lt_of_lt_of_le hx (le_add_of_nonneg_right hn))) le_rfl

lemma measurableSet_profileBudgetThreat_upper {d k : ℕ} (e f : Direction d)
    (a G r s : ℝ) (H : ℕ) :
    @MeasurableSet (BudgetProfile (k:=k) e f a G × Environment d)
      (MeasurableSpace.prod inferInstance (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}))
      {p | p.2 ∈ budgetThreatEvent e f H r p.1.val s} := by
  let : MeasurableSpace (Environment d) := rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}
  change MeasurableSet {p : BudgetProfile (k:=k) e f a G × Environment d |
    ∃ h ≤ H, relativeBudgetMass e f h r p.1.val p.2 < s}
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion; intro h
  by_cases hh : h ≤ H
  · simp only [hh,true_and]
    apply measurableSet_lt _ measurable_const
    apply budgetProfileMass_joint_rows
    intro x hx j y hy
    change a ≤ dot (realPosition y) (realPosition (step e))
    simpa only [hx j] using hy.1
  · simp only [hh,false_and,Set.ofPred_false]
    exact MeasurableSet.empty

lemma fresh_random_budget_threat {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a G r s : ℝ) (H : ℕ)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A)
    (c : ℝ≥0∞)
    (hbound : ∀ η ∈ A, environmentLaw ν (budgetThreatEvent e f H r (π η).val s) ≤ c) :
    environmentLaw ν {ω | ω ∈ A ∧ ω ∈ budgetThreatEvent e f H r (π ω).val s} ≤
      c*environmentLaw ν A := by
  let S := BelowHeight (realPosition (step e)) a
  let T : Set (Lattice d) := {y | a ≤ dot (realPosition y) (realPosition (step e))}
  let B : Set (Environment d × Environment d) := {p | p.2 ∈ budgetThreatEvent e f H r (π p.1).val s}
  have hB : @MeasurableSet (Environment d × Environment d)
      (MeasurableSpace.prod (rowSigma S) (rowSigma T)) B :=
    (measurableSet_profileBudgetThreat_upper e f a G r s H).preimage
      ((hπ.comp measurable_fst).prodMk measurable_snd)
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  have hb (η : Environment d) (hη : η ∈ A) :
      (@Measure.map (Environment d) (Environment d) inferInstance (rowSigma T) id (environmentLaw ν))
        {ω | (η,ω) ∈ B} ≤ c := by
    rw [show {ω | (η,ω) ∈ B}=Prod.mk η ⁻¹' B from rfl,
      Measure.map_apply hV (hB.preimage measurable_prodMk_left)]
    exact hbound η hη
  apply @fresh_rows_random_test_bound d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
    ν _ S T _ id id measurable_id measurable_id A hA B hB c hb
  exact Set.disjoint_left.mpr fun x hx hy =>
    (not_lt.mpr (show a ≤ dot (realPosition x) (realPosition (step e)) from hy))
      (show dot (realPosition x) (realPosition (step e)) < a from hx)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma fullTupleProfile_mass {d k : ℕ} (e : Direction d) (a : ℝ) (H : ℕ)
    (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    rawTupleMixture (realPosition (step e)) H π.val ω Set.univ •
      (fullTupleProfile e a H π ω).val=rawTupleMixture (realPosition (step e)) H π.val ω :=
  normalizeOr_mass _ _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_StageSeedProfile
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedSeparatedProfile_mass {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (a G : ℝ) (H : ℕ) (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    seedSeparatedRaw e f H G π.val ω Set.univ •
      (seedSeparatedProfile e f hef a G H π ω).val=seedSeparatedRaw e f H G π.val ω :=
  normalizeOr_mass _ _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetAlgebra
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma relativeBudgetWordLaw_zero_univ {d k : ℕ} (e f : Direction d) (r : ℝ) (hr : 0 ≤ r)
    (ω : Environment d) (x : Fin k → Lattice d) :
    relativeBudgetWordLaw e f 0 r ω x Set.univ = 1 := by
  apply le_antisymm (relativeBudgetWordLaw_le_one e f 0 r ω x)
  let w : Fin k → List (Direction d) := fun _ => []
  have hb : TupleRelativeBudget e f x 0 r w := by
    intro s hs i j
    have : s=0 := by omega
    subst s
    simpa [relativeWordDisplacement,wordFirstHitPosition,wordFirstHitTime_zero,w] using hr
  have hw (j : Fin k) : wordPath (x j) (w j) ∈ HitAt
      (Strip (realPosition (step e)) (x j) (0:ℕ))
      (Upper (realPosition (step e)) (x j) (0:ℕ)) (w j).length := by
    constructor
    · simp [w,Upper,wordPath_zero]
    · intro n hn; simp [w] at hn
  have ha : relativeBudgetWordLaw e f 0 r ω x {w}=1 := by
    rw [relativeBudgetWordLaw_singleton,ite_eq_left hb,rawTupleWordLaw_singleton]
    simp only [rawWordLaw_singleton,hw,ite_eq_left,w,wordWeight,ENNReal.ofReal_one,Finset.prod_const_one]
  rw [← ha]
  exact measure_mono (Set.subset_univ _)

lemma relativeBudgetMassENN_zero {d k : ℕ} (e f : Direction d) (r : ℝ) (hr : 0 ≤ r)
    (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    relativeBudgetMassENN e f 0 r π ω=1 := by
  simp only [relativeBudgetMassENN,relativeBudgetWordLaw_zero_univ e f r hr]
  simp

lemma relativeBudgetWordLaw_mono {d k : ℕ} (e f : Direction d) (H : ℕ) {r q : ℝ} (hrq : r ≤ q)
    (ω : Environment d) (x : Fin k → Lattice d) :
    relativeBudgetWordLaw e f H r ω x ≤ relativeBudgetWordLaw e f H q ω x := by
  apply Measure.restrict_mono_set
  intro w hw s hs i j
  exact (hw s hs i j).trans hrq

lemma relativeBudgetMassENN_mono {d k : ℕ} (e f : Direction d) (H : ℕ) {r q : ℝ} (hrq : r ≤ q)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    relativeBudgetMassENN e f H r π ω ≤ relativeBudgetMassENN e f H q π ω :=
  lintegral_mono fun x => relativeBudgetWordLaw_mono e f H hrq ω x Set.univ

lemma relativeBudgetMassENN_restart_comp {d k : ℕ} (e f : Direction d) (h m : ℕ)
    (a G r q : ℝ) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (π : BudgetProfile (k:=k) e f a G) (ω : Environment d) :
    relativeBudgetMassENN e f h r π.val ω *
      relativeBudgetMassENN e f m q (nextBudgetProfile e f h a G r hr π ω).val ω ≤
        relativeBudgetMassENN e f (h+m) (r+q) π.val ω := by
  have ht := budgetEndpointMixture_comp_le e f h m r q hq π.val ω Set.univ
  rw [budgetEndpointMixture_univ,budgetEndpointMixture_univ] at ht
  rw [← nextBudgetProfile_mass e f h a G r hr π ω] at ht
  simpa only [relativeBudgetMassENN,lintegral_smul_measure,smul_eq_mul] using ht

lemma budgetFirstThreat_eq_measurable {d k : ℕ} (e f : Direction d) (a G r s : ℝ)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (H h : ℕ) : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+h))]
      {ω | budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω = h} := by
  have ht := budgetFirstThreat_stopping e f a r s _
    ((BudgetProfile.measurable_toSupported e f a G).comp hπ) H
  have he : {ω | (budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω : WithTop ℕ) = (h : WithTop ℕ)} =
      {ω | budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω = h} := by
    ext ω
    exact WithTop.coe_eq_coe
  have hm : @MeasurableSet (Environment d) (rowHeightFiltration (realPosition (step e)) a h)
      {ω | (budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω : WithTop ℕ) = (h : WithTop ℕ)} := ht.measurableSet_eq h
  rw [he] at hm
  exact hm

lemma budgetFirstThreat_lt_threat {d k : ℕ} (e f : Direction d) (a G r s : ℝ)
    (π : Environment d → BudgetProfile (k:=k) e f a G) (H : ℕ) (ω : Environment d)
    (hlt : budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω < H) :
    ω ∈ budgetThreatEvent e f H r (π ω).val s := by
  let τ := budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω
  have hH : 1 ≤ H := by omega
  have hτ : 1 ≤ τ := le_hittingBtwn hH ω
  have hhit := hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  change budgetTraversalMass e f a r (fun ω => (π ω).toSupported) τ ω < ENNReal.ofReal s at hhit
  have hm : relativeBudgetMassENN e f τ r (π ω).val ω < ENNReal.ofReal s := by
    simpa only [budgetTraversalMass,ite_eq_right (show τ≠0 by omega),Set.mem_Iio,BudgetProfile.toSupported] using hhit
  refine ⟨τ,(hittingBtwn_le ω),?_⟩
  rw [← relativeBudgetMassENN_toReal]
  exact ENNReal.toReal_lt_of_lt_ofReal hm

lemma budgetFirstThreat_mass_lower {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G r s : ℝ) (hr : 0 ≤ r) (hs : s ≤ 1)
    (π : Environment d → BudgetProfile (k:=k) e f a G) (H : ℕ) (hH : 1 ≤ H)
    (ω : Environment d) (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ:ℝ≥0∞)^k * ENNReal.ofReal s ≤ relativeBudgetMassENN e f
      (budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω) r (π ω).val ω := by
  let τ := budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω
  have ht : 1 ≤ τ := le_hittingBtwn hH ω
  have hp : ENNReal.ofReal s ≤ relativeBudgetMassENN e f (τ-1) r (π ω).val ω := by
    by_cases h0 : τ-1=0
    · rw [h0,relativeBudgetMassENN_zero e f r hr]
      exact ENNReal.ofReal_le_one.mpr hs
    · have hh : τ-1 < τ := by omega
      exact before_budgetFirstThreat_pass e f a r s (fun ω => (π ω).toSupported) H ω (j:=τ-1) (by omega) hh
  have hu := relativeBudgetMassENN_upward e f hef (τ-1) r ω (π ω).val κ hκ
  rw [Nat.sub_add_cancel ht] at hu
  exact (mul_le_mul_right hp _).trans hu

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma rowSigma_below_mono_nat {d : ℕ} (e : Direction d) (a : ℝ) (h : ℕ) :
    rowSigma (BelowHeight (realPosition (step e)) a) ≤
      rowSigma (BelowHeight (realPosition (step e)) (a+h)) :=
  rowSigma_mono fun x hx =>
    show dot (realPosition x) (realPosition (step e)) < a+h from
      lt_of_lt_of_le (show dot (realPosition x) (realPosition (step e)) < a from hx)
        (le_add_of_nonneg_right (Nat.cast_nonneg h))

lemma budgetRetryEvent_probability {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (r s g : ℝ) (hr : 0 ≤ r) (Hmax : ℕ) (c : ℝ≥0∞)
    (hb : ∀ (H : ℕ), H ≤ Hmax → ∀ (a G : ℝ), g ≤ G →
      ∀ π : BudgetProfile (k:=k) e f a G,
        environmentLaw ν (budgetThreatEvent e f H r π.val s) ≤ c)
    (n H : ℕ) (hH : H ≤ Hmax) (a G : ℝ) (hG : g+n*r ≤ G)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A) :
    environmentLaw ν (A ∩ budgetRetryEvent e f r s hr n H a G π) ≤ c^n*environmentLaw ν A := by
  induction n generalizing H a G A with
  | zero => simp [budgetRetryEvent]
  | succ n ih =>
    let τ := budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H
    let I := {h : ℕ // 0<h ∧ h<H}
    let E (h : I) : Set (Environment d) := A ∩ {ω | τ ω=h.val}
    have hE (h : I) : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+h.val))] (E h) :=
      ((rowSigma_below_mono_nat e a h.val) A hA).inter
        (budgetFirstThreat_eq_measurable e f a G r s π hπ H h.val)
    have hEm (h : I) : MeasurableSet (E h) := (rowSigma_le _) _ (hE h)
    have hEd : Pairwise (Function.onFun Disjoint E) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      rintro ω ⟨_,hi⟩ ⟨_,hj⟩
      exact hij (Subtype.ext (hi.symm.trans hj))
    have hnext (h : I) : environmentLaw ν
        (E h ∩ budgetRetryEvent e f r s hr n (H-h.val) (a+h.val) (G-r)
          (fun ω => nextBudgetProfile e f h.val a G r hr (π ω) ω)) ≤ c^n*environmentLaw ν (E h) := by
      apply ih (H-h.val) (Nat.sub_le _ _ |>.trans hH) (a+h.val) (G-r) _ _
        (nextBudgetProfile_measurable_below e f a G r hr h.val π hπ) (E h) (hE h)
      have hcast : (n+1:ℕ)=n+1 := rfl
      push_cast at hG
      nlinarith
    have hs : (⋃ h : I, E h) ⊆ {ω | ω ∈ A ∧ ω ∈ budgetThreatEvent e f H r (π ω).val s} := by
      intro ω hω
      obtain ⟨h,ha,ht⟩ := Set.mem_iUnion.mp hω
      refine ⟨ha,budgetFirstThreat_lt_threat e f a G r s π H ω ?_⟩
      change τ ω < H
      rw [ht]
      exact h.property.2
    have hGs : g ≤ G := by
      have hn : 0 ≤ (n+1:ℕ)*r := mul_nonneg (Nat.cast_nonneg _) hr
      linarith
    have hsum : (∑' h : I, environmentLaw ν (E h)) ≤ c*environmentLaw ν A := by
      rw [← measure_iUnion hEd hEm]
      exact (measure_mono hs).trans (fresh_random_budget_threat ν e f a G r s H π hπ A hA c
        (fun η _ => hb H hH a G hGs (π η)))
    have he : A ∩ budgetRetryEvent e f r s hr (n+1) H a G π =
        ⋃ h : I, E h ∩ budgetRetryEvent e f r s hr n (H-h.val) (a+h.val) (G-r)
          (fun ω => nextBudgetProfile e f h.val a G r hr (π ω) ω) := by
      simp only [budgetRetryEvent,Set.inter_iUnion,Set.inter_assoc,E,τ,I]
    rw [he]
    calc
      _ ≤ ∑' h : I, environmentLaw ν
          (E h ∩ budgetRetryEvent e f r s hr n (H-h.val) (a+h.val) (G-r)
            (fun ω => nextBudgetProfile e f h.val a G r hr (π ω) ω)) := measure_iUnion_le _
      _ ≤ ∑' h : I, c^n*environmentLaw ν (E h) := ENNReal.tsum_le_tsum hnext
      _ = c^n * ∑' h : I, environmentLaw ν (E h) := ENNReal.tsum_mul_left
      _ ≤ c^n*(c*environmentLaw ν A) := mul_le_mul_right hsum _
      _ = c^(n+1)*environmentLaw ν A := by rw [pow_succ,mul_assoc]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetLoss
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma budget_loss_requires_retries {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r s : ℝ) (hr : 0 ≤ r) (hs : s ≤ 1) (κ : ℝ≥0) (t : ℝ≥0∞)
    (ht : t ≤ 1) (hkt : t ≤ (κ:ℝ≥0∞)^k*ENNReal.ofReal s)
    (n H : ℕ) (a G : ℝ) (π : Environment d → BudgetProfile (k:=k) e f a G)
    (ω : Environment d) (hκ : ∀ y, κ ≤ (ω y).1 e)
    (hbad : relativeBudgetMassENN e f H ((n:ℝ)*r) (π ω).val ω < t^n) :
    ω ∈ budgetRetryEvent e f r s hr n H a G π := by
  induction n generalizing H a G with
  | zero => exact Set.mem_univ _
  | succ n ih =>
    have hpow : t^(n+1) ≤ 1 := pow_le_one₀ bot_le ht
    have hH : 1 ≤ H := by
      by_contra hn
      have h0 : H=0 := by omega
      rw [h0,relativeBudgetMassENN_zero e f _ (mul_nonneg (Nat.cast_nonneg _) hr)] at hbad
      exact (not_lt.mpr hpow) hbad
    let τ := budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω
    have htau : 1 ≤ τ := le_hittingBtwn hH ω
    have htaum : τ ≤ H := hittingBtwn_le ω
    have hmass : t ≤ relativeBudgetMassENN e f τ r (π ω).val ω :=
      hkt.trans (budgetFirstThreat_mass_lower e f hef a G r s hr hs π H hH ω κ hκ)
    have hbudget : r ≤ (n+1:ℕ)*r := by
      have hn : 0 ≤ (n:ℝ)*r := mul_nonneg (Nat.cast_nonneg n) hr
      push_cast <;> linarith
    have hthreat : τ < H := by
      by_contra hn
      have he : τ=H := by omega
      have hp : t^(n+1) ≤ t := by
        rw [pow_succ]
        calc
          _ ≤ 1*t := mul_le_mul_left (pow_le_one₀ bot_le ht) t
          _ = t := one_mul t
      exact (not_lt.mpr ((hp.trans (by simpa only [he] using hmass)).trans
        (relativeBudgetMassENN_mono e f H hbudget (π ω).val ω))) hbad
    let π' := fun η => nextBudgetProfile e f τ a G r hr (π η) η
    have hbad' : relativeBudgetMassENN e f (H-τ) ((n:ℝ)*r) (π' ω).val ω < t^n := by
      by_contra hn
      have hp := relativeBudgetMassENN_restart_comp e f τ (H-τ) a G r ((n:ℝ)*r) hr
        (mul_nonneg (Nat.cast_nonneg n) hr) (π ω) ω
      rw [Nat.add_sub_of_le htaum,
        show r+(n:ℝ)*r = ((n+1:ℕ):ℝ)*r by push_cast; ring] at hp
      have hb : t^(n+1) ≤ relativeBudgetMassENN e f H ((n+1:ℕ)*r) (π ω).val ω := by
        rw [pow_succ,mul_comm]
        exact (mul_le_mul hmass (le_of_not_gt hn) bot_le bot_le).trans hp
      exact (not_lt.mpr hb) hbad
    have hi := ih (H-τ) (a+τ) (G-r) π' hbad'
    apply Set.mem_iUnion.mpr
    exact ⟨⟨τ,by omega,hthreat⟩,rfl,hi⟩

theorem budget_rapid_loss_from_fresh_bound {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) (r s g : ℝ) (hr : 0 ≤ r) (hs : s ≤ 1)
    (κ : ℝ≥0) (hκ : ∀ᵐ ω ∂environmentLaw ν, ∀ y, κ ≤ (ω y).1 e)
    (t : ℝ≥0∞) (ht : t ≤ 1) (hkt : t ≤ (κ:ℝ≥0∞)^k*ENNReal.ofReal s)
    (n H : ℕ) (c : ℝ≥0∞)
    (hb : ∀ (h : ℕ), h ≤ H → ∀ (a G : ℝ), g ≤ G →
      ∀ π : BudgetProfile (k:=k) e f a G,
        environmentLaw ν (budgetThreatEvent e f h r π.val s) ≤ c)
    (a G : ℝ) (hG : g+n*r ≤ G) (π : BudgetProfile (k:=k) e f a G) :
    environmentLaw ν {ω | relativeBudgetMassENN e f H ((n:ℝ)*r) π.val ω < t^n} ≤ c^n := by
  have hsub : {ω | relativeBudgetMassENN e f H ((n:ℝ)*r) π.val ω < t^n} ≤ᵐ[environmentLaw ν]
      budgetRetryEvent e f r s hr n H a G (fun _ => π) := by
    filter_upwards [hκ] with ω hω hbad
    exact budget_loss_requires_retries e f hef r s hr hs κ t ht hkt n H a G (fun _ => π) ω hω hbad
  apply (measure_mono_ae hsub).trans
  simpa using budgetRetryEvent_probability ν e f r s g hr H c hb n H le_rfl a G hG
    (fun _ => π) measurable_const Set.univ MeasurableSet.univ

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem rapid_loss_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ (κ : ℝ≥0) (lam C : ℝ), 0 < κ ∧ (∀ᵐ p ∂ν, ∀ u, κ ≤ p.1 u) ∧
      0 < lam ∧ lam ≤ 1 ∧ 0 < C ∧
      ∀ Bstar : ℝ, 0 < Bstar → ∀ k : ℕ, 1 ≤ k → ∃ Gzero : ℕ,
      ∀ (L H : ℕ) (a G b x : ℝ), 1 ≤ L → 0 < b → b ≤ G/2 →
        (Gzero:ℝ) ≤ G-b → (k:ℝ)*L*Real.log (1/(κ:ℝ)) ≤ x → x ≤ Bstar →
        ∀ π : BudgetProfile (k:=k) e f a G,
          (environmentLaw ν).real {ω | relativeBudgetMassENN e f H b π.val ω <
            ENNReal.ofReal (Real.exp (-x))} ≤
          (Real.exp (C*k-lam*x/L) + C*k*Real.exp (x/L)*H /
            fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
              (commonIncrementProcess (realPosition (step e)) f 0) (b/(2*L)))^L := by
  obtain ⟨κ,hκ,hrows⟩ := hue
  have hue : UniformElliptic ν := ⟨κ,hκ,hrows⟩
  have hκ0 : 0 < (κ:ℝ) := hκ
  have hκ1 : (κ:ℝ) ≤ 1 := by
    obtain ⟨p,hp⟩ := hrows.exists
    exact_mod_cast (hp e).trans (row_entry_le_one p e)
  have henv : ∀ᵐ ω ∂environmentLaw ν, ∀ y, κ ≤ (ω y).1 e := by
    apply ae_all_iff.mpr
    intro y
    exact ((measurePreserving_eval_infinitePi (fun _ : Lattice d => ν) y).quasiMeasurePreserving.ae hrows).mono
      fun p hp => hp e
  obtain ⟨lam,C,D,hlam,hlam1,hC,hD,hfresh⟩ := fresh_budget_threat_bound ν hue e f htrans
  let K := Real.log (1/(κ:ℝ))
  have hK : 0 ≤ K := by
    dsimp [K]
    apply Real.log_nonneg
    exact (one_le_div hκ0).mpr hκ1
  have hlog : Real.log (κ:ℝ) = -K := by simp [K]
  let C' := max (C+lam*K) D
  have hC' : 0 < C' := hD.trans_le (le_max_right _ _)
  refine ⟨κ,lam,C',hκ,hrows,hlam,hlam1,hC',?_⟩
  intro Bstar hB k hk
  obtain ⟨Gzero,hGzero⟩ := hfresh Bstar hB k hk
  refine ⟨Gzero,?_⟩
  intro L H a G b x hL hb hhalf hG hx hxb π
  have hL0 : 0 < (L:ℝ) := by exact_mod_cast (by omega : 0<L)
  have hLn : (L:ℝ) ≠ 0 := ne_of_gt hL0
  have hk0 : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  have hx0 : 0 ≤ x := (mul_nonneg (mul_nonneg hk0 hL0.le) hK).trans hx
  have hxl : (k:ℝ)*K ≤ x/L := (le_div_iff₀ hL0).mpr (by nlinarith [hx])
  have hxlB : x/L ≤ Bstar := by
    have hL1 : 1 ≤ (L:ℝ) := by exact_mod_cast hL
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  let s := Real.exp ((k:ℝ)*K-x/L)
  have hs0 : 0 < s := Real.exp_pos _
  have hs1 : s ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsB : Real.exp (-Bstar) ≤ s := Real.exp_le_exp.mpr (by
    have : 0 ≤ (k:ℝ)*K := mul_nonneg hk0 hK
    linarith)
  let t := ENNReal.ofReal (Real.exp (-x/L))
  have ht : t ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx0) hL0.le
  have hkt : t = (κ:ℝ≥0∞)^k*ENNReal.ofReal s := by
    have he : (κ:ℝ)^k*s = Real.exp (-x/L) := by
      have hpow : (κ:ℝ)^k = Real.exp ((k:ℝ)*Real.log (κ:ℝ)) := by
        rw [Real.exp_nat_mul,Real.exp_log hκ0]
      rw [hpow,hlog,← Real.exp_add]
      congr 1
      ring
    rw [← ENNReal.ofReal_coe_nnreal,← ENNReal.ofReal_pow hκ0.le,
      ← ENNReal.ofReal_mul (pow_nonneg hκ0.le k),he]
  let N := fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) (b/(2*L))
  have hN : 0 ≤ N := fluctuationScale_nonneg _ _ _
  let c := Real.exp (C'*k-lam*x/L)+C'*k*Real.exp (x/L)*H/N
  have hc : 0 ≤ c := add_nonneg (Real.exp_pos _).le (by positivity)
  have hbound (h : ℕ) (hh : h ≤ H) (a' G' : ℝ) (hG' : (Gzero:ℝ) ≤ G')
      (π' : BudgetProfile (k:=k) e f a' G') :
      environmentLaw ν (budgetThreatEvent e f h (b/L) π'.val s) ≤ ENNReal.ofReal c := by
    have hsep : ∀ᵐ u ∂π'.val, Pairwise fun i j => (Gzero:ℤ) ≤ |u i f.1-u j f.1| := by
      filter_upwards [π'.property.2] with u hu
      apply (tupleSeparated_coordinate f Gzero u).mp
      exact tupleSeparated_mono f hG' u hu.2
    have hb0 : 0 < b/(2*L) := div_pos hb (mul_pos (by norm_num) hL0)
    have hf := hGzero π'.val hsep h (b/(2*L)) s hb0 hsB
    have hrad : 2*(b/(2*L)) = b/L := by field_simp
    rw [hrad] at hf
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc).mpr
    apply hf.trans
    apply add_le_add
    · calc
        Real.exp (C*k)*s^lam = Real.exp ((C+lam*K)*k-lam*x/L) := by
          rw [Real.rpow_def_of_pos hs0]
          dsimp only [s]
          rw [Real.log_exp,← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (C'*k-lam*x/L) := Real.exp_le_exp.mpr (by
          have : (C+lam*K)*k ≤ C'*k := mul_le_mul_of_nonneg_right (le_max_left _ _) hk0
          linarith)
    · have hinv : 1/s ≤ Real.exp (x/L) := by
        dsimp only [s]
        rw [one_div,← Real.exp_neg]
        apply Real.exp_le_exp.mpr
        have : 0 ≤ (k:ℝ)*K := mul_nonneg hk0 hK
        linarith
      have hD' : D*k*(h:ℝ)/N ≤ C'*k*(H:ℝ)/N := by
        apply div_le_div_of_nonneg_right _ hN
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hk0
        · exact_mod_cast hh
        · exact Nat.cast_nonneg h
        · exact mul_nonneg hC'.le hk0
      calc
        D*k*h/N/s = (D*k*h/N)*(1/s) := by ring
        _ ≤ (C'*k*H/N)*Real.exp (x/L) := mul_le_mul hD' hinv
          (one_div_nonneg.mpr hs0.le) (by positivity)
        _ = C'*k*Real.exp (x/L)*H/N := by ring
  have hbudget : (L:ℝ)*(b/L) = b := mul_div_cancel₀ _ hLn
  have hsep : (Gzero:ℝ)+(L:ℝ)*(b/L) ≤ G := by rw [hbudget]; linarith
  have hloss := budget_rapid_loss_from_fresh_bound ν e f hef (b/L) s Gzero
    (div_nonneg hb.le hL0.le) hs1 κ henv t ht hkt.le L H (ENNReal.ofReal c)
    hbound a G hsep π
  have htL : t^L = ENNReal.ofReal (Real.exp (-x)) := by
    dsimp only [t]
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,← Real.exp_nat_mul]
    congr 2
    field_simp
  rw [hbudget,htL,← ENNReal.ofReal_pow hc] at hloss
  exact ENNReal.toReal_le_of_le_ofReal (pow_nonneg hc L) hloss

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_LateMoment
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma relativeBudgetMass_bounds {d k : ℕ} (e f : Direction d) (H : ℕ) (b : ℝ)
    (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    0 ≤ relativeBudgetMass e f H b π ω ∧ relativeBudgetMass e f H b π ω≤1 := by
  rw [← relativeBudgetMassENN_toReal]
  exact ⟨ENNReal.toReal_nonneg,by
    have := ENNReal.toReal_mono (by norm_num : (1:ℝ≥0∞)≠∞) (relativeBudgetMassENN_le_one e f H b π ω)
    simpa using this⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProtectionLoss
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma protectionGap_eq (G : ℝ) (r : ℕ → ℝ) (n : ℕ) :
    protectionGap G r n=G-∑ i∈Finset.range n, r i := by
  induction n with
  | zero => simp [protectionGap]
  | succ n ih => simp [protectionGap,ih,Finset.sum_range_succ,sub_sub]

lemma protectionMass_bounds {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) (n : ℕ) (ω : Environment d) :
    0≤protectionMass e f base G H r hr π n ω ∧ protectionMass e f base G H r hr π n ω≤1 :=
  relativeBudgetMass_bounds e f (H n) (r n) _ ω

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RetainedComposition
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma rawTupleMixture_mono {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) {μ ν : Measure (Fin k → Lattice d)} (h : μ≤ν) :
    rawTupleMixture ℓ H μ ω ≤ rawTupleMixture ℓ H ν ω := by
  apply Measure.le_iff.mpr
  intro U hU
  rw [rawTupleMixture_apply,rawTupleMixture_apply]
  exact lintegral_mono' h le_rfl

lemma rawTupleMixture_smul {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (c : ℝ≥0∞) (μ : Measure (Fin k → Lattice d)) :
    rawTupleMixture ℓ H (c•μ) ω=c•rawTupleMixture ℓ H μ ω :=
  Measure.bind_smul c μ _

lemma rawTupleMixture_comp_le {d k : ℕ} (e : Direction d) (h m : ℕ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    rawTupleMixture (realPosition (step e)) m
      (rawTupleMixture (realPosition (step e)) h π ω) ω≤
        rawTupleMixture (realPosition (step e)) (h+m) π ω := by
  unfold rawTupleMixture
  rw [Measure.bind_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  apply Measure.le_iff.mpr
  intro U hU
  rw [Measure.bind_apply hU (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hU (measurable_of_countable _).aemeasurable]
  apply lintegral_mono
  intro x
  exact rawTupleEndpointLaw_comp_le e h m ω x U

lemma rawTupleEndpointLaw_zero {d k : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Fin k → Lattice d) : rawTupleEndpointLaw ℓ 0 ω x=Measure.dirac x := by
  apply Measure.ext_of_singleton
  intro y
  rw [rawTupleEndpointLaw_singleton]
  have hz (j : Fin k) : variableHitKernel ℓ 0 (ω,x j)=Measure.dirac (x j) := by
    simpa only [variableHitKernel, Kernel.coe_mk, Nat.cast_zero] using hitKernel_height_zero ℓ (x j) ω
  simp_rw [hz]
  by_cases h : x=y
  · subst y
    simp
  · obtain ⟨j,hj⟩ : ∃ j, x j ≠ y j := by
      by_contra! hn
      exact h (funext hn)
    simp only [Measure.dirac_apply', measurableSet_singleton, Set.indicator_apply,
      Pi.one_apply, Set.mem_singleton_iff, h, ↓reduceIte]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

lemma rawTupleMixture_zero {d k : ℕ} (ℓ : Vector d) (π : Measure (Fin k → Lattice d))
    (ω : Environment d) : rawTupleMixture ℓ 0 π ω=π := by
  unfold rawTupleMixture
  have hz : rawTupleEndpointLaw (k:=k) ℓ 0 ω=Measure.dirac := funext (rawTupleEndpointLaw_zero ℓ ω)
  rw [hz,Measure.bind_dirac]

lemma budgetEndpointMixture_le_raw {d k : ℕ} (e f : Direction d) (H : ℕ) (r : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    budgetEndpointMixture e f H r π ω ≤ rawTupleMixture (realPosition (step e)) H π ω := by
  apply Measure.le_iff.mpr
  intro U hU
  rw [budgetEndpointMixture_apply,rawTupleMixture_apply]
  exact lintegral_mono fun x => relativeBudgetEndpointLaw_le e f H r ω x U

lemma protectionMass_ennreal {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) (n : ℕ) (ω : Environment d) :
    ENNReal.ofReal (protectionMass e f base G H r hr π n ω)=
      relativeBudgetMassENN e f (H n) (r n) (protectionProfile e f base G H r hr π n ω).val ω := by
  rw [protectionMass,←relativeBudgetMassENN_toReal]
  exact ENNReal.ofReal_toReal (lt_of_le_of_lt (relativeBudgetMassENN_le_one e f _ _ _ _) ENNReal.one_lt_top).ne

lemma protection_retained_succ {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) (n : ℕ) (ω : Environment d) :
    ENNReal.ofReal (protectionMass e f base G H r hr π n ω) •
      (protectionProfile e f base G H r hr π (n+1) ω).val≤
        rawTupleMixture (realPosition (step e)) (H n)
          (protectionProfile e f base G H r hr π n ω).val ω := by
  rw [protectionMass_ennreal]
  change relativeBudgetMassENN e f (H n) (r n) _ ω •
    (nextBudgetProfile e f (H n) _ _ (r n) (hr n) _ ω).val≤_
  rw [nextBudgetProfile_mass]
  exact budgetEndpointMixture_le_raw e f _ _ _ ω

theorem protection_retained_le_raw {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) (n : ℕ) (ω : Environment d) :
    (∏ i∈Finset.range n, ENNReal.ofReal (protectionMass e f base G H r hr π i ω)) •
      (protectionProfile e f base G H r hr π n ω).val≤
        rawTupleMixture (realPosition (step e)) (∑ i∈Finset.range n, H i) (π ω).val ω := by
  induction n with
  | zero => simp [protectionProfile,rawTupleMixture_zero]
  | succ n ih =>
    rw [Finset.prod_range_succ,Finset.sum_range_succ,mul_smul]
    let c := ∏ i∈Finset.range n, ENNReal.ofReal (protectionMass e f base G H r hr π i ω)
    let p := (protectionProfile e f base G H r hr π n ω).val
    have hs : c • (ENNReal.ofReal (protectionMass e f base G H r hr π n ω) •
        (protectionProfile e f base G H r hr π (n+1) ω).val)≤
        c • rawTupleMixture (realPosition (step e)) (H n) p ω :=
      smul_le_smul_left c (protection_retained_succ e f base G H r hr π n ω)
    have hc := rawTupleMixture_smul (realPosition (step e)) (H n) ω c p
    have hm := rawTupleMixture_mono (realPosition (step e)) (H n) ω ih
    exact hs.trans ((le_of_eq hc.symm).trans
      (hm.trans (rawTupleMixture_comp_le e _ _ _ ω)))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellAttempt
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma cellEarlyProfile_retained {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G : ℝ) (hG : 0 ≤ G) (Hs He : ℕ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (ω : Environment d) :
    (cellSeedMass e f a G Hs π ω * ENNReal.ofReal (cellEarlyMass e f hef a G Hs He π ω)) •
      (cellEarlyProfile e f hef a G hG Hs He π ω).val  ≤
        rawTupleMixture (realPosition (step e)) (Hs+He) (π ω).val ω := by
  let p := seedSeparatedProfile e f hef a G Hs (π ω) ω
  have hp : cellSeedMass e f a G Hs π ω • p.val=seedSeparatedRaw e f Hs G (π ω).val ω :=
    seedSeparatedProfile_mass e f hef a G Hs (π ω) ω
  have hq : ENNReal.ofReal (cellEarlyMass e f hef a G Hs He π ω) •
      (cellEarlyProfile e f hef a G hG Hs He π ω).val =
      budgetEndpointMixture e f He (G/4) p.val ω := by
    change ENNReal.ofReal (relativeBudgetMass e f He (G/4) p.val ω) •
      (nextBudgetProfile e f He (a+Hs) G (G/4) (by positivity) p ω).val = _
    rw [←relativeBudgetMassENN_toReal, ENNReal.ofReal_toReal (lt_of_le_of_lt
      (relativeBudgetMassENN_le_one e f He (G/4) p.val ω) ENNReal.one_lt_top).ne]
    exact nextBudgetProfile_mass e f He (a+Hs) G (G/4) (by positivity) p ω
  rw [mul_smul,hq]
  calc
    _  ≤  cellSeedMass e f a G Hs π ω • rawTupleMixture (realPosition (step e)) He p.val ω := by
      exact smul_le_smul_left _ (budgetEndpointMixture_le_raw e f He (G/4) p.val ω)
    _ = rawTupleMixture (realPosition (step e)) He
        (cellSeedMass e f a G Hs π ω • p.val) ω := (rawTupleMixture_smul _ _ _ _ _).symm
    _  ≤  rawTupleMixture (realPosition (step e)) He
        (rawTupleMixture (realPosition (step e)) Hs (π ω).val ω) ω := by
      rw [hp]
      exact rawTupleMixture_mono _ _ _ Measure.restrict_le_self
    _  ≤  _ := rawTupleMixture_comp_le e Hs He (π ω).val ω

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RadixBudget
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma lateBudget_sum_le {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0≤ρ) (s n : ℕ) :
    (∑ i∈Finset.range n, lateBudget c ρ s i) ≤ c*ρ/8 := by
  have hgeom := geom_sum_mul_neg (1/2:ℝ) n
  have hnonneg : 0≤(1/2:ℝ)^n := by positivity
  have hsum : (∑ i∈Finset.range n, (1/2:ℝ)^i)≤2 := by linarith
  calc
    _ ≤ ∑ i∈Finset.range n, (c*ρ/16)*(1/2:ℝ)^i := by
      apply Finset.sum_le_sum; intro i hi
      unfold lateBudget
      have hpow : (2:ℝ)^i≤(2:ℝ)^(s+i) := pow_le_pow_right₀ (by norm_num) (Nat.le_add_left i s)
      calc
        _ ≤ (c/16)*ρ/(2:ℝ)^i := div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
        _ = _ := by rw [one_div_pow]; ring
    _ = (c*ρ/16)*(∑ i∈Finset.range n, (1/2:ℝ)^i) := by rw [Finset.mul_sum]
    _ ≤ (c*ρ/16)*2 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

lemma lateBudget_gaps {c ρ : ℝ} (hc : 0 < c) (hρ : 0<ρ) (s n : ℕ) :
    lateBudget c ρ s n≤protectionGap (3*c*ρ/4) (lateBudget c ρ s) n/2 ∧
    c*ρ/2≤protectionGap (3*c*ρ/4) (lateBudget c ρ s) n-lateBudget c ρ s n := by
  have hn := lateBudget_sum_le hc.le hρ.le s n
  have hn1 := lateBudget_sum_le hc.le hρ.le s (n+1)
  rw [Finset.sum_range_succ] at hn1
  have hb : lateBudget c ρ s n ≤ c*ρ/16 := by
    unfold lateBudget
    have ht : (1:ℝ)≤(2:ℝ)^(s+n) := one_le_pow₀ (by norm_num)
    calc
      _ ≤ (c/16)*ρ/1 := div_le_div_of_nonneg_left (by positivity) (by norm_num) ht
      _ = _ := by ring
  rw [protectionGap_eq]
  constructor <;> nlinarith [mul_pos hc hρ]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellSchedule
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators
namespace DirectionalTransience

lemma cellWidth_step (w m i : ℕ) (hi : i < m) :
    cellWidth w m i=16*cellWidth w m (i+1) := by
  have he : m-i=(m-(i+1))+1 := by omega
  unfold cellWidth
  rw [he,pow_succ]
  ring
lemma cellOpportunity_last (v w m : ℕ) : cellOpportunity v w m m=v+w := by
  simp [cellOpportunity]

lemma cell_seed_endpoint (v w m i : ℕ) (hv : 2*cellWidth w m 0 ≤ v) (hi : i < m) :
    cellOpportunity v w m i+cellWidth w m i=v-cellWidth w m i := by
  have hw := Nat.mul_le_mul_left 2 (cellWidth_antitone w m (Nat.zero_le i))
  simp only [cellOpportunity,ite_eq_left hi]
  omega

lemma cell_seed_before_next (v w m i : ℕ) (hv : 2*cellWidth w m 0 ≤ v) (hi : i < m) :
    cellOpportunity v w m i+cellWidth w m i ≤ cellOpportunity v w m (i+1) := by
  rw [cell_seed_endpoint v w m i hv hi]
  by_cases hn : i+1 < m
  · simp only [cellOpportunity,ite_eq_left hn]
    apply Nat.sub_le_sub_left
    rw [cellWidth_step w m i hi]
    omega
  · simp only [cellOpportunity,ite_eq_right hn]
    omega

lemma cellEarly_endpoint (v w m i s : ℕ) (hv : 2*cellWidth w m 0 ≤ v)
    (hi : i < m) (hs : 0 < s) :
    cellOpportunity v w m i+cellWidth w m i+cellEarlyHeight v w m i s=
      cellOpportunity v w m (i+min s (m-i)) := by
  unfold cellEarlyHeight
  have hmin : 1 ≤ min s (m-i) := by omega
  have hh := cellOpportunity_monotone v w m (show i+1 ≤ i+min s (m-i) by omega)
  have ht := cell_seed_before_next v w m i hv hi
  omega

lemma cellLate_endpoint (v w m i s n : ℕ) (_ : 2*cellWidth w m 0 ≤ v)
    (hn : i+s+n ≤ m) :
    cellOpportunity v w m (i+s)+(∑ j∈Finset.range n,cellLateHeight v w m i s j)=
      cellOpportunity v w m (i+s+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hin : i+s+n < m := by omega
    have hp := ih (by omega)
    rw [Finset.sum_range_succ,←Nat.add_assoc,hp]
    simp only [cellLateHeight,ite_eq_left hin]
    have hh := cellOpportunity_monotone v w m (show i+s+n ≤ i+s+n+1 by omega)
    have he : i+s+(n+1)=i+s+n+1 := by omega
    rw [he]
    omega

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordPrefixes
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma wordCylinder_prefix {d : ℕ} (e : Direction d) (x : Lattice d) (h : ℕ)
    (w : List (Direction d)) : wordCylinder x w ⊆ wordCylinder x (wordPrefix e x h w) := by
  intro X hX i hi
  have hlen : (wordPrefix e x h w).length≤w.length := by
    simp only [wordPrefix,List.length_take]; exact min_le_right _ _
  have hin : i≤wordFirstHitTime e x h w := by
    exact hi.trans (by simp only [wordPrefix,List.length_take]; exact min_le_left _ _)
  exact (hX i (hi.trans hlen)).trans (wordPath_take x w _ i hin).symm

lemma successfulWordLaw_prefix_le {d : ℕ} (e : Direction d) (ω : Environment d)
    (x : Lattice d) (h H : ℕ) (hh : h≤H) :
    (successfulWordLaw ω x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)).map
      (coordinateWordPrefix e x h H hh) ≤
    successfulWordLaw ω x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h) := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.map_apply (measurable_of_countable _) hE,
    successfulWordLaw_event _ _ _ _ (disjoint_strip_upper _ _ _),
    successfulWordLaw_event _ _ _ _ (disjoint_strip_upper _ _ _)]
  apply measure_mono
  intro X hX
  obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hX
  exact Set.mem_iUnion.mpr ⟨⟨coordinateWordPrefix e x h H hh w.val,w.property⟩,
    wordCylinder_prefix e x h w.val.val hw⟩

lemma rawWordLaw_prefix_le {d : ℕ} (e : Direction d) (ω : Environment d)
    (x : Lattice d) (h H : ℕ) (hh : h≤H) :
    (rawWordLaw (realPosition (step e)) H ω x).map (wordPrefix e x h)≤
    rawWordLaw (realPosition (step e)) h ω x := by
  let μ : Measure (CoordinateWord e x H) := successfulWordLaw ω x
    (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)
  let μ' : Measure (CoordinateWord e x h) := successfulWordLaw ω x
    (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h)
  have hf : (μ.map (coordinateWordPrefix e x h H hh)).map Subtype.val≤μ'.map Subtype.val :=
    Measure.map_mono (successfulWordLaw_prefix_le e ω x h H hh) measurable_subtype_coe
  rw [Measure.map_map measurable_subtype_coe (measurable_of_countable _)] at hf
  change (μ.map Subtype.val).map (wordPrefix e x h)≤μ'.map Subtype.val
  rw [Measure.map_map (measurable_of_countable _) measurable_subtype_coe]
  exact hf

lemma rawTupleWordLaw_prefix_le {d k : ℕ} (e : Direction d) (ω : Environment d)
    (x : Fin k → Lattice d) (h H : ℕ) (hh : h≤H) :
    (rawTupleWordLaw (realPosition (step e)) H ω x).map (tupleWordPrefix e x h)≤
    rawTupleWordLaw (realPosition (step e)) h ω x := by
  change (Measure.pi (fun j => rawWordLaw (realPosition (step e)) H ω (x j))).map
    (fun w j => wordPrefix e (x j) h (w j))≤_
  rw [Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable)]
  exact TupleKernel.countable_pi_mono k _ _ fun j => rawWordLaw_prefix_le e ω (x j) h H hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma relativeWordDisplacement_prefix {d : ℕ} (e f : Direction d) (x : Lattice d)
    (h H : ℕ) (hh : h≤H) (s : ℕ) (hs : s≤h) (w : CoordinateWord e x H) :
    relativeWordDisplacement e f x s (wordPrefix e x h w.val)=relativeWordDisplacement e f x s w.val := by
  have he := relativeWordDisplacement_append_prefix e f x h s hs
    (coordinateWordPrefix e x h H hh w) (w.val.drop (wordFirstHitTime e x h w.val))
  change relativeWordDisplacement e f x s (w.val.take (wordFirstHitTime e x h w.val)++
    w.val.drop (wordFirstHitTime e x h w.val))=_ at he
  rw [List.take_append_drop] at he
  exact he.symm

lemma tupleRelativeBudget_prefix {d k : ℕ} (e f : Direction d) (x : Fin k → Lattice d)
    (h H : ℕ) (hh : h≤H) (r : ℝ) (w : ∀ j, CoordinateWord e (x j) H)
    (hw : TupleRelativeBudget e f x H r (fun j => (w j).val)) :
    TupleRelativeBudget e f x h r (tupleWordPrefix e x h (fun j => (w j).val)) := by
  intro s hs i j
  change |relativeWordDisplacement e f (x i) s (wordPrefix e (x i) h (w i).val)-
    relativeWordDisplacement e f (x j) s (wordPrefix e (x j) h (w j).val)| ≤ r
  rw [relativeWordDisplacement_prefix e f (x i) h H hh s hs (w i),
    relativeWordDisplacement_prefix e f (x j) h H hh s hs (w j)]
  exact hw s (hs.trans hh) i j

lemma tupleRelativeBudget_prefix_separation {d k : ℕ} (e f : Direction d)
    (x : Fin k → Lattice d) (h H : ℕ) (hh : h≤H) (G r : ℝ)
    (w : ∀ j, CoordinateWord e (x j) H) (hG : TupleSeparated f G x)
    (hw : TupleRelativeBudget e f x H r (fun j => (w j).val)) :
    TupleSeparated f (G-r) (tupleWordEndpoint x (tupleWordPrefix e x h (fun j => (w j).val))) :=
  tupleRelativeBudget_separation e f x h G r (fun j => coordinateWordPrefix e (x j) h H hh (w j))
    hG (tupleRelativeBudget_prefix e f x h H hh r w hw)

lemma rawTupleWordLaw_valid_ae {d k : ℕ} (e : Direction d) (ω : Environment d)
    (x : Fin k → Lattice d) (H : ℕ) :
    ∀ᵐ w ∂rawTupleWordLaw (realPosition (step e)) H ω x, ∀ j,
      wordPath (x j) (w j)∈HitAt (Strip (realPosition (step e)) (x j) H)
        (Upper (realPosition (step e)) (x j) H) (w j).length := by
  apply ae_iff_of_countable.mpr
  intro w hw j
  by_contra hj
  apply hw
  rw [rawTupleWordLaw_singleton]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [rawWordLaw_singleton,ite_eq_right hj]

lemma relativeBudgetWordLaw_prefix_separation_ae {d k : ℕ} (e f : Direction d)
    (ω : Environment d) (x : Fin k → Lattice d) (h H : ℕ) (hh : h≤H) (G r : ℝ)
    (hG : TupleSeparated f G x) :
    ∀ᵐ w ∂relativeBudgetWordLaw e f H r ω x,
    TupleSeparated f (G-r) (tupleWordEndpoint x (tupleWordPrefix e x h w)) := by
  have hv := (rawTupleWordLaw_valid_ae e ω x H).filter_mono
    (ae_mono (show relativeBudgetWordLaw e f H r ω x ≤ rawTupleWordLaw (realPosition (step e)) H ω x from
      Measure.restrict_le_self))
  have hb : ∀ᵐ w ∂relativeBudgetWordLaw e f H r ω x,TupleRelativeBudget e f x H r w :=
    ae_restrict_mem (Set.to_countable _).measurableSet
  filter_upwards [hv,hb] with w hw hb
  exact tupleRelativeBudget_prefix_separation e f x h H hh G r (fun j => ⟨w j,hw j⟩) hG hb

theorem budget_prefix_certificate {d k : ℕ} (e f : Direction d) (ω : Environment d)
    (x : Fin k → Lattice d) (h H : ℕ) (hh : h≤H) (G r : ℝ)
    (hG : TupleSeparated f G x) :
    relativeBudgetWordLaw e f H r ω x Set.univ ≤
      rawTupleEndpointLaw (realPosition (step e)) h ω x {y | TupleSeparated f (G-r) y} := by
  let P := fun w : Fin k → List (Direction d) => tupleWordEndpoint x (tupleWordPrefix e x h w)
  have hle : (relativeBudgetWordLaw e f H r ω x).map P ≤ rawTupleEndpointLaw (realPosition (step e)) h ω x := by
    rw [←rawTupleWordLaw_endpoint (realPosition (step e)) h ω x]
    have hp := (Measure.map_mono (show relativeBudgetWordLaw e f H r ω x≤
      rawTupleWordLaw (realPosition (step e)) H ω x from Measure.restrict_le_self)
        (measurable_of_countable (tupleWordPrefix e x h))).trans (rawTupleWordLaw_prefix_le e ω x h H hh)
    have he := Measure.map_mono hp (measurable_of_countable (tupleWordEndpoint x))
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at he
    exact he
  have he : (relativeBudgetWordLaw e f H r ω x).map P {y | TupleSeparated f (G-r) y}=
      relativeBudgetWordLaw e f H r ω x Set.univ := by
    rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    apply measure_congr
    filter_upwards [relativeBudgetWordLaw_prefix_separation_ae e f ω x h H hh G r hG] with w hw
    apply propext
    exact iff_true_intro hw
  rw [←he]
  exact hle _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ScheduledCellSuccess
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma budget_profile_prefix_certificate {d k : ℕ} (e f : Direction d)
    (a G r : ℝ) (π : BudgetProfile (k:=k) e f a G) (ω : Environment d)
    (h H : ℕ) (hh : h≤H) :
    relativeBudgetMassENN e f H r π.val ω ≤
      rawTupleMixture (realPosition (step e)) h π.val ω {y | TupleSeparated f (G-r) y} := by
  rw [relativeBudgetMassENN,rawTupleMixture_apply]
  apply lintegral_mono_ae
  filter_upwards [π.property.2] with x hx
  exact budget_prefix_certificate e f ω x h H hh G r hx.2

theorem protection_prefix_certificate {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i,0 ≤ r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (n h : ℕ) (hh : h≤H n) (ω : Environment d) :
    (∏ i∈Finset.range (n+1),ENNReal.ofReal (protectionMass e f base G H r hr π i ω)) ≤
      rawTupleMixture (realPosition (step e)) ((∑ i∈Finset.range n,H i)+h) (π ω).val ω
        {y | TupleSeparated f (protectionGap G r n-r n) y} := by
  let c := ∏ i∈Finset.range n,ENNReal.ofReal (protectionMass e f base G H r hr π i ω)
  let p := protectionProfile e f base G H r hr π n ω
  have hi := budget_profile_prefix_certificate e f _ _ (r n) p ω h (H n) hh
  have hp := protection_retained_le_raw e f base G H r hr π n ω
  rw [Finset.prod_range_succ,protectionMass_ennreal]
  change c*relativeBudgetMassENN e f (H n) (r n) p.val ω ≤ _
  calc
    _ ≤ c*rawTupleMixture (realPosition (step e)) h p.val ω
      {y | TupleSeparated f (protectionGap G r n-r n) y} := mul_le_mul_right hi c
    _ = rawTupleMixture (realPosition (step e)) h (c•p.val) ω
      {y | TupleSeparated f (protectionGap G r n-r n) y} := by
        rw [rawTupleMixture_smul,Measure.smul_apply,smul_eq_mul]
    _ ≤ rawTupleMixture (realPosition (step e)) h
      (rawTupleMixture (realPosition (step e)) (∑ i∈Finset.range n,H i) (π ω).val ω) ω
      {y | TupleSeparated f (protectionGap G r n-r n) y} := (rawTupleMixture_mono _ _ _ hp) _
    _ ≤ _ := rawTupleMixture_comp_le e (∑ i∈Finset.range n,H i) h (π ω).val ω _

theorem protection_prefix_after_retention {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i,0 ≤ r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (n h : ℕ) (hh : h≤H n) (ω : Environment d)
    (μ : Measure (Fin k → Lattice d)) (t : ℕ) (c : ℝ≥0∞)
    (hc : c•(π ω).val ≤ rawTupleMixture (realPosition (step e)) t μ ω) :
    c*(∏ i∈Finset.range (n+1),ENNReal.ofReal (protectionMass e f base G H r hr π i ω)) ≤
      rawTupleMixture (realPosition (step e)) (t+(∑ i∈Finset.range n,H i)+h) μ ω
        {y | TupleSeparated f (protectionGap G r n-r n) y} := by
  have hp := protection_prefix_certificate e f base G H r hr π n h hh ω
  calc
    _ ≤ c*rawTupleMixture (realPosition (step e)) ((∑ i∈Finset.range n,H i)+h) (π ω).val ω
      {y | TupleSeparated f (protectionGap G r n-r n) y} := mul_le_mul_right hp c
    _ = rawTupleMixture (realPosition (step e)) ((∑ i∈Finset.range n,H i)+h) (c•(π ω).val) ω
      {y | TupleSeparated f (protectionGap G r n-r n) y} := by
        rw [rawTupleMixture_smul,Measure.smul_apply,smul_eq_mul]
    _ ≤ rawTupleMixture (realPosition (step e)) ((∑ i∈Finset.range n,H i)+h)
      (rawTupleMixture (realPosition (step e)) t μ ω) ω
      {y | TupleSeparated f (protectionGap G r n-r n) y} := (rawTupleMixture_mono _ _ _ hc) _
    _ ≤ _ := by
      simpa only [Nat.add_assoc] using rawTupleMixture_comp_le e t ((∑ i∈Finset.range n,H i)+h) μ ω
        {y | TupleSeparated f (protectionGap G r n-r n) y}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellCertificates
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma cellEarly_prefix_certificate {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G : ℝ) (Hs He h : ℕ) (hh : h ≤ He)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    cellSeedMass e f a G Hs π ω*ENNReal.ofReal (cellEarlyMass e f hef a G Hs He π ω) ≤
      rawTupleMixture (realPosition (step e)) (Hs+h) (π ω).val ω {y | TupleSeparated f (G-G/4) y} := by
  let p := seedSeparatedProfile e f hef a G Hs (π ω) ω
  have hp : cellSeedMass e f a G Hs π ω • p.val=seedSeparatedRaw e f Hs G (π ω).val ω :=
    seedSeparatedProfile_mass e f hef a G Hs (π ω) ω
  have hi := budget_profile_prefix_certificate e f (a+Hs) G (G/4) p ω h He hh
  have he : ENNReal.ofReal (cellEarlyMass e f hef a G Hs He π ω)=relativeBudgetMassENN e f He (G/4) p.val ω := by
    change ENNReal.ofReal (relativeBudgetMass e f He (G/4) p.val ω)=_
    rw [←relativeBudgetMassENN_toReal,ENNReal.ofReal_toReal]
    exact (lt_of_le_of_lt (relativeBudgetMassENN_le_one e f He (G/4) p.val ω) ENNReal.one_lt_top).ne
  rw [he]
  calc
    _ ≤ cellSeedMass e f a G Hs π ω*rawTupleMixture (realPosition (step e)) h p.val ω
        {y | TupleSeparated f (G-G/4) y} := mul_le_mul_right hi _
    _ = rawTupleMixture (realPosition (step e)) h (cellSeedMass e f a G Hs π ω • p.val) ω
        {y | TupleSeparated f (G-G/4) y} := by
          rw [rawTupleMixture_smul,Measure.smul_apply,smul_eq_mul]
    _ ≤ rawTupleMixture (realPosition (step e)) h
        (rawTupleMixture (realPosition (step e)) Hs (π ω).val ω) ω
        {y | TupleSeparated f (G-G/4) y} := by
          rw [hp]
          exact (rawTupleMixture_mono _ _ _ Measure.restrict_le_self) _
    _ ≤ _ := rawTupleMixture_comp_le e Hs h (π ω).val ω _

lemma cellLate_prefix_certificate {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (Hs He s : ℕ) (H : ℕ → ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (n h : ℕ) (hh : h ≤ H n) (ω : Environment d) :
    (cellSeedMass e f a (c*ρ) Hs π ω*ENNReal.ofReal (cellEarlyMass e f hef a (c*ρ) Hs He π ω))*
      (∏ i∈Finset.range (n+1),ENNReal.ofReal (cellLateMass e f hef a c ρ hc hρ Hs He s H π i ω)) ≤
      rawTupleMixture (realPosition (step e)) (Hs+He+(∑ i∈Finset.range n,H i)+h) (π ω).val ω
        {y | TupleSeparated f (c*ρ/2) y} := by
  have hret := cellEarlyProfile_retained e f hef a (c*ρ) (mul_nonneg hc.le hρ.le) Hs He π ω
  have hh' := protection_prefix_after_retention e f (a+Hs+He) (3*c*ρ/4) H
    (lateBudget c ρ s) (fun i => (lateBudget_pos hc hρ s i).le)
    (cellLateInitial e f hef a c ρ hc.le hρ.le Hs He π) n h hh ω (π ω).val (Hs+He)
    (cellSeedMass e f a (c*ρ) Hs π ω*ENNReal.ofReal (cellEarlyMass e f hef a (c*ρ) Hs He π ω)) hret
  apply hh'.trans
  apply measure_mono
  intro y hy i j hij
  exact (lateBudget_gaps hc hρ s n).2.trans (hy i j hij)

lemma fullStream_prefix_certificate {d k : ℕ} (e : Direction d) (a : ℝ)
    (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) (t h : ℕ)
    (E : Set (Fin k → Lattice d)) (b : ℝ≥0∞)
    (hb : b ≤ rawTupleMixture (realPosition (step e)) h (fullTupleProfile e a t π ω).val ω E) :
    rawTupleMixture (realPosition (step e)) t π.val ω Set.univ*b ≤
      rawTupleMixture (realPosition (step e)) (t+h) π.val ω E := by
  calc
    _ ≤ rawTupleMixture (realPosition (step e)) t π.val ω Set.univ*
      rawTupleMixture (realPosition (step e)) h (fullTupleProfile e a t π ω).val ω E :=
        mul_le_mul_right hb _
    _ = rawTupleMixture (realPosition (step e)) h
      (rawTupleMixture (realPosition (step e)) t π.val ω) ω E := by
        conv_rhs => rw [←fullTupleProfile_mass e a t π ω]
        rw [rawTupleMixture_smul,Measure.smul_apply,smul_eq_mul]
    _ ≤ _ := rawTupleMixture_comp_le e t h π.val ω E

end DirectionalTransience

end

section

open scoped BigOperators
namespace DirectionalTransience

lemma cell_early_covers (v w m i s : ℕ) (hv : 2*cellWidth w m 0 ≤ v)
    (hi : i < m) (hs : 0 < s) (hsmall : m-i ≤ s) :
    cellOpportunity v w m i+cellWidth w m i ≤ v ∧
      cellOpportunity v w m i+cellWidth w m i+cellEarlyHeight v w m i s=v+w := by
  constructor
  · rw [cell_seed_endpoint v w m i hv hi]; omega
  · rw [cellEarly_endpoint v w m i s hv hi hs,min_eq_right hsmall,
      Nat.add_sub_of_le hi.le,cellOpportunity_last]

lemma cell_late_covers (v w m i s : ℕ) (hv : 2*cellWidth w m 0 ≤ v)
    (hi : i < m) (hs : 0 < s) (hlarge : s < m-i) :
    let n := m-i-s-1
    (cellOpportunity v w m i+cellWidth w m i+cellEarlyHeight v w m i s+
      (∑ j∈Finset.range n,cellLateHeight v w m i s j) ≤ v) ∧
    (cellOpportunity v w m i+cellWidth w m i+cellEarlyHeight v w m i s+
      (∑ j∈Finset.range n,cellLateHeight v w m i s j)+cellLateHeight v w m i s n=v+w) := by
  dsimp only
  have hmin : min s (m-i)=s := min_eq_left hlarge.le
  have hearly := cellEarly_endpoint v w m i s hv hi hs
  rw [hmin] at hearly
  have hlast : i+s+(m-i-s-1)=m-1 := by omega
  have hlast' : i+s+(m-i-s-1+1)=m := by omega
  have hprev := cellLate_endpoint v w m i s (m-i-s-1) hv (by omega)
  rw [hlast,←hearly] at hprev
  have hfin := cellLate_endpoint v w m i s (m-i-s-1+1) hv (by omega)
  rw [hlast',←hearly,Finset.sum_range_succ,cellOpportunity_last,←Nat.add_assoc] at hfin
  refine ⟨?_,hfin⟩
  rw [hprev]
  simp only [cellOpportunity,ite_eq_left (show m-1 < m by omega)]
  omega

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

theorem successful_cell_certificate {d k : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A : ℝ) (hc : 0 < c)
    (hA : 0 ≤ A) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (v w m s i : ℕ) (hv : 2*cellWidth w m 0 ≤ v) (hs : 0 < s)
    (ω : Environment d) (hS : ω ∈ scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π v w m s i)
    (t : ℕ) (hvt : v ≤ t) (ht : t ≤ v+w) :
    rawTupleMixture (realPosition (step e)) (cellOpportunity v w m i) (π ω).val ω Set.univ*
      (ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m))) ≤
    rawTupleMixture (realPosition (step e)) t (π ω).val ω
      {y | TupleSeparated f (c*cellRadius ν e f C w m i/2) y} := by
  have hi : i < m := by
    by_contra hh
    simp only [scheduledCellSuccess,ite_eq_right hh,Set.mem_empty_iff_false] at hS
  rw [scheduledCellSuccess,ite_eq_left hi] at hS
  let t₀ := cellOpportunity v w m i
  let ρ := cellRadius ν e f C w m i
  let π₀ := cellRestart e a π v w m i
  let Hs := cellWidth w m i
  let He := cellEarlyHeight v w m i s
  let H := cellLateHeight v w m i s
  have hρ : 0 < ρ := cellRadius_pos ν e f C w m i
  have hseed := hS.1
  have hear := hS.2.1
  have hlate := hS.2.2
  have hcoef : ENNReal.ofReal g₀*ENNReal.ofReal g₁ ≤
      cellSeedMass e f (a+t₀) (c*ρ) Hs π₀ ω*ENNReal.ofReal
        (cellEarlyMass e f hef (a+t₀) (c*ρ) Hs He π₀ ω) :=
    mul_le_mul hseed (ENNReal.ofReal_le_ofReal hear) zero_le zero_le
  suffices ∃ h : ℕ, t₀+h=t ∧
      ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m)) ≤
        rawTupleMixture (realPosition (step e)) h (π₀ ω).val ω
          {y | TupleSeparated f (c*ρ/2) y} by
    obtain ⟨h,he,hc⟩ := this
    have hh := fullStream_prefix_certificate e a (π ω) ω t₀ h _ _ hc
    rw [he] at hh
    exact hh
  by_cases hsmall : m-i ≤ s
  · obtain ⟨hstart,hend⟩ := cell_early_covers v w m i s hv hi hs hsmall
    have hb : t₀+Hs ≤ t := hstart.trans hvt
    let h := t-(t₀+Hs)
    have hhe : h ≤ He := by dsimp [h,He,t₀,Hs] at *; omega
    have he : t₀+(Hs+h)=t := by dsimp [h]; omega
    have hcert := cellEarly_prefix_certificate e f hef (a+t₀) (c*ρ) Hs He h hhe π₀ ω
    refine ⟨Hs+h,he,?_⟩
    apply le_trans _ (hcert.trans ?_)
    · apply le_trans _ hcoef
      have hexp : ENNReal.ofReal (Real.exp (-A*k*m)) ≤ 1 := by
        rw [←ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_one_iff.mpr
        have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
        have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
        nlinarith only [mul_nonneg (mul_nonneg hA hk0) hm0]
      simpa only [mul_one] using mul_le_mul_right hexp (ENNReal.ofReal g₀*ENNReal.ofReal g₁)
    · apply measure_mono
      intro y hy j l hjl
      have hg : c*ρ/2 ≤ c*ρ-c*ρ/4 := by nlinarith only [mul_pos hc hρ]
      exact hg.trans (hy j l hjl)
  · have hlarge : s < m-i := by omega
    let n := m-i-s-1
    obtain ⟨hstart,hend⟩ := cell_late_covers v w m i s hv hi hs hlarge
    change t₀+Hs+He+(∑ j∈Finset.range n,H j) ≤ v at hstart
    change t₀+Hs+He+(∑ j∈Finset.range n,H j)+H n=v+w at hend
    let z := t₀+Hs+He+(∑ j∈Finset.range n,H j)
    have hz : z ≤ t := hstart.trans hvt
    let h := t-z
    have hh : h ≤ H n := by dsimp [h,z] at *; omega
    have he : t₀+(Hs+He+(∑ j∈Finset.range n,H j)+h)=t := by dsimp [h,z]; omega
    have hcert := cellLate_prefix_certificate e f hef (a+t₀) c ρ hc hρ Hs He s H π₀ n h hh ω
    have hn : n < m-i-s := by dsimp [n]; omega
    have hpass := hlate n hn
    have hqn : ∀ j, 0 ≤ cellLateMass e f hef (a+t₀) c ρ hc hρ Hs He s H π₀ j ω := by
      intro j
      exact (protectionMass_bounds e f (a+t₀+Hs+He) (3*c*ρ/4) H (lateBudget c ρ s)
        (fun u => (lateBudget_pos hc hρ s u).le)
        (cellLateInitial e f hef (a+t₀) c ρ hc.le hρ.le Hs He π₀) j ω).1
    have hprod : ENNReal.ofReal (Real.exp (-A*k*m)) ≤
        ∏ j∈Finset.range (n+1),ENNReal.ofReal (cellLateMass e f hef (a+t₀) c ρ hc hρ Hs He s H π₀ j ω) := by
      rw [←ENNReal.ofReal_prod_of_nonneg (fun j _ => hqn j)]
      apply ENNReal.ofReal_le_ofReal
      apply le_trans _ hpass
      apply Real.exp_le_exp.mpr
      have hcst : (s:ℝ)+(n:ℝ)+1 ≤ m := by
        have hsn : s+n+1 ≤ m := by dsimp [n]; omega
        exact_mod_cast hsn
      have ha : 0 ≤ A*(k:ℝ) := mul_nonneg hA (Nat.cast_nonneg _)
      nlinarith only [mul_nonneg ha (sub_nonneg.mpr hcst)]
    exact ⟨_,he,(mul_le_mul hcoef hprod zero_le zero_le).trans hcert⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellBadEvent
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma cell_bad_event_subset {d k : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A G : ℝ) (hc : 0 < c)
    (hA : 0 ≤ A) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (v w m s : ℕ) (hv : 2*cellWidth w m 0 ≤ v) (hs : 0 < s)
    (hG : ∀ i < m, G ≤ c*cellRadius ν e f C w m i/2) (q : ℝ≥0∞) :
    {ω | ∃ t : ℕ, v ≤ t ∧ t ≤ v+w ∧
      rawTupleMixture (realPosition (step e)) t (π ω).val ω {y | TupleSeparated f G y} <
        q*(ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m)))} ⊆
    {ω | ∃ h : ℕ, rawTupleMixture (realPosition (step e)) h (π ω).val ω Set.univ < q} ∪
      (⋃ i, scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π v w m s i)ᶜ := by
  intro ω hω
  by_cases hmass : ω ∈ {ω | ∃ h : ℕ, rawTupleMixture (realPosition (step e)) h (π ω).val ω Set.univ < q}
  · exact Or.inl hmass
  · refine Or.inr ?_
    intro hcert
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hcert
    have him : i < m := by
      by_contra hh
      simp only [scheduledCellSuccess,ite_eq_right hh,Set.mem_empty_iff_false] at hi
    obtain ⟨t,hvt,ht,hbad⟩ := hω
    have hq : q ≤ rawTupleMixture (realPosition (step e)) (cellOpportunity v w m i) (π ω).val ω Set.univ := by
      by_contra hh
      exact hmass ⟨_,not_le.mp hh⟩
    have hp := successful_cell_certificate ν e f hef a C c g₀ g₁ A hc hA π v w m s i hv hs ω hi t hvt ht
    have hmono : rawTupleMixture (realPosition (step e)) t (π ω).val ω
        {y | TupleSeparated f (c*cellRadius ν e f C w m i/2) y} ≤
      rawTupleMixture (realPosition (step e)) t (π ω).val ω {y | TupleSeparated f G y} := by
      apply measure_mono
      intro y hy j l hjl
      exact (hG i him).trans (hy j l hjl)
    exact (not_lt_of_ge ((mul_le_mul_left hq _).trans (hp.trans hmono))) hbad

lemma cells_bad_probability {d k n : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A : ℝ) (hc : 0 < c)
    (hA : 0 ≤ A) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (v w : Fin n → ℕ) (m s : ℕ) (hs : 0 < s) (G : Fin n → ℝ)
    (hv : ∀ j, 2*cellWidth (w j) m 0 ≤ v j)
    (hG : ∀ j i, i < m → G j ≤ c*cellRadius ν e f C (w j) m i/2)
    (q δ ε : ℝ≥0∞)
    (hmass : environmentLaw ν {ω | ∃ h : ℕ, rawTupleMixture (realPosition (step e)) h (π ω).val ω Set.univ < q} ≤ δ)
    (hcell : ∀ j, environmentLaw ν (⋃ i, scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π (v j) (w j) m s i)ᶜ ≤ ε) :
    environmentLaw ν {ω | ∃ j : Fin n, ∃ t : ℕ, v j ≤ t ∧ t ≤ v j+w j ∧
      rawTupleMixture (realPosition (step e)) t (π ω).val ω {y | TupleSeparated f (G j) y} <
        q*(ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m)))} ≤ δ+n*ε := by
  let E := {ω | ∃ h : ℕ, rawTupleMixture (realPosition (step e)) h (π ω).val ω Set.univ < q}
  let F := fun j : Fin n => (⋃ i, scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π (v j) (w j) m s i)ᶜ
  have hsub : {ω | ∃ j : Fin n, ∃ t : ℕ, v j ≤ t ∧ t ≤ v j+w j ∧
      rawTupleMixture (realPosition (step e)) t (π ω).val ω {y | TupleSeparated f (G j) y} <
        q*(ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m)))} ⊆ E ∪ ⋃ j, F j := by
    rintro ω ⟨j,hj⟩
    rcases cell_bad_event_subset ν e f hef a C c g₀ g₁ A (G j) hc hA π (v j) (w j) m s (hv j) hs (hG j) q hj with he|hf
    · exact Or.inl he
    · exact Or.inr (Set.mem_iUnion.mpr ⟨j,hf⟩)
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  apply add_le_add hmass
  apply (measure_iUnion_fintype_le _ _).trans
  calc
    ∑ j : Fin n, environmentLaw ν (F j) ≤ ∑ _j : Fin n, ε := Finset.sum_le_sum (fun j _ => hcell j)
    _ = n*ε := by simp [nsmul_eq_mul]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

theorem finite_stage_assembly {d k n : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A G Gminus Gplus r : ℝ)
    (hc : 0 < c) (hA : 0 ≤ A) (π : BudgetProfile (k:=k) e f a G)
    (He H : ℕ) (v w : Fin n → ℕ) (m s : ℕ) (hs : 0 < s) (Gs : Fin n → ℝ)
    (hv : ∀ j, 2*cellWidth (w j) m 0 ≤ v j)
    (hGs : ∀ j i, i < m → Gs j ≤ c*cellRadius ν e f C (w j) m i/2)
    (hcover : ∀ h : ℕ, He < h → h ≤ H → ∃ j, v j ≤ h ∧ h ≤ v j+w j ∧ Gminus ≤ Gs j)
    (hgrowth : ∃ j, v j ≤ H ∧ H ≤ v j+w j ∧ Gplus ≤ Gs j)
    (hshortgap : Gminus ≤ G-r) (p q δ₀ δ₁ ε : ℝ≥0∞)
    (hp : p ≤ q*(ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m))))
    (hshort : environmentLaw ν {ω | relativeBudgetMassENN e f He r π.val ω < p} ≤ δ₀)
    (hmass : environmentLaw ν {ω | ∃ h : ℕ, rawTupleMixture (realPosition (step e)) h π.val ω Set.univ < q} ≤ δ₁)
    (hcell : ∀ j, environmentLaw ν (⋃ i, scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc
      (fun _ => π.toLayerProfile) (v j) (w j) m s i)ᶜ ≤ ε) :
    environmentLaw ν (stageBadEvent e f H Gminus Gplus π.val p) ≤ δ₀+δ₁+n*ε := by
  let E := {ω | relativeBudgetMassENN e f He r π.val ω < p}
  let F := {ω | ∃ j : Fin n, ∃ t : ℕ, v j ≤ t ∧ t ≤ v j+w j ∧
      rawTupleMixture (realPosition (step e)) t π.val ω {y | TupleSeparated f (Gs j) y} <
        q*(ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m)))}
  have hF : environmentLaw ν F ≤ δ₁+n*ε :=
    cells_bad_probability ν e f hef a C c g₀ g₁ A hc hA (fun _ => π.toLayerProfile)
      v w m s hs Gs hv hGs q δ₁ ε hmass hcell
  have hsub : stageBadEvent e f H Gminus Gplus π.val p ⊆ E ∪ F := by
    intro ω hω
    rcases hω with ⟨h,hh,hH,hbad⟩|hbad
    · by_cases he : h ≤ He
      · apply Or.inl
        apply lt_of_le_of_lt _ hbad
        have hb := budget_profile_prefix_certificate e f a G r π ω h He he
        apply hb.trans
        exact measure_mono (fun y hy j l hjl => hshortgap.trans (hy j l hjl))
      · obtain ⟨j,hv,hw,hg⟩ := hcover h (not_le.mp he) hH
        refine Or.inr ⟨j,h,hv,hw,lt_of_le_of_lt ?_ (hbad.trans_le hp)⟩
        exact measure_mono (fun y hy i l hil => hg.trans (hy i l hil))
    · obtain ⟨j,hv,hw,hg⟩ := hgrowth
      refine Or.inr ⟨j,H,hv,hw,lt_of_le_of_lt ?_ (hbad.trans_le hp)⟩
      exact measure_mono (fun y hy i l hil => hg.trans (hy i l hil))
  exact (measure_mono hsub).trans ((measure_union_le E F).trans
    (by simpa only [add_assoc] using add_le_add hshort hF))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma noDropProduct_le_raw {d k : ℕ} (ℓ : Vector d) (ω : Environment d)
    (hω : ∀ x H, NoDrop ℓ x ≤ᵐ[quenchedKernel (ω,x)] Cross ℓ x H)
    (x : Fin k → Lattice d) (H : ℕ) :
    ENNReal.ofReal (noDropProduct ℓ x ω) ≤ rawTupleEndpointLaw ℓ H ω x Set.univ := by
  rw [noDropProduct,ENNReal.ofReal_prod_of_nonneg (fun j _ => ENNReal.toReal_nonneg),
    rawTupleEndpointLaw,Measure.pi_univ]
  apply Finset.prod_le_prod'
  intro j _
  rw [ENNReal.ofReal_toReal (show noDropQuenched ℓ (x j) ω ≠ ⊤ from measure_ne_top _ _)]
  have hh : noDropQuenched ℓ (x j) ω ≤ crossingQuenched ℓ (x j) H ω :=
    measure_mono_ae (hω (x j) H)
  rw [crossingQuenched_eq_hitKernel] at hh
  exact hh

lemma fullStream_noDrop_lower {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π],
      ∀ H : ℕ, ENNReal.ofReal (∫ x, noDropProduct ℓ x ω ∂π) ≤
        rawTupleMixture ℓ H π ω Set.univ := by
  filter_upwards [quenched_noDrop_subset_cross_ae ν ℓ htrans] with ω hω π hπ H
  have hI : Integrable (fun x => noDropProduct ℓ x ω) π :=
    integrable_of_nonneg_bound π (measurable_of_countable _) (fun x => noDropProduct_bounds ℓ x ω)
  rw [ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall
    (fun x => (noDropProduct_bounds ℓ x ω).1)),rawTupleMixture_apply]
  exact lintegral_mono fun x => noDropProduct_le_raw ℓ ω hω x H

theorem fullStream_small_mass_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d)
    (hℓ : dot ℓ ℓ = 1) (htrans : DirectionallyTransient ν ℓ) (e : Fin d) :
    ∃ lam C : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < C ∧
      ∀ Bstar : ℝ, 0 < Bstar → ∀ k : ℕ, 1 ≤ k → ∃ G : ℕ,
      ∀ (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π],
        (∀ᵐ x ∂π, Pairwise fun i j => (G:ℤ) ≤ |x i e-x j e|) →
        ∀ s : ℝ, Real.exp (-Bstar) ≤ s →
        environmentLaw ν {ω | ∃ H : ℕ, rawTupleMixture ℓ H π ω Set.univ < ENNReal.ofReal s} ≤
          ENNReal.ofReal (Real.exp (C*k)*s^lam) := by
  obtain ⟨lam,C,hlam,hlam1,hC,hb⟩ := separated_initial_inverse_moment ν hue ℓ hℓ htrans e
  refine ⟨lam,C,hlam,hlam1,hC,fun Bstar hB k hk => ?_⟩
  obtain ⟨G,hG⟩ := hb Bstar hB k hk
  refine ⟨G,fun π hπ hsep s hs => ?_⟩
  apply le_trans _ (hG π hsep s hs)
  apply measure_mono_ae
  filter_upwards [fullStream_noDrop_lower ν ℓ htrans] with ω hω
  rintro ⟨H,hH⟩
  have hq := (hω π H).trans_lt hH
  have hs0 : 0 < s := (Real.exp_pos _).trans_le hs
  have hqs : (∫ x, noDropProduct ℓ x ω ∂π) < s := (ENNReal.ofReal_lt_ofReal_iff hs0).mp hq
  change (∫ x, noDropProduct ℓ x ω ∂π) < 2*s
  linarith

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FiniteStage
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

theorem actual_finite_stage_estimate_oai {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ (κ : ℝ≥0) (lam Cr lamq Cq A : ℝ), 0 < κ ∧
      (∀ᵐ p ∂ν, ∀ u, κ ≤ p.1 u) ∧ 0 < lam ∧ lam ≤ 1 ∧ 0 < Cr ∧
      0 < lamq ∧ lamq ≤ 1 ∧ 0 < Cq ∧ 1 ≤ A ∧
      ∀ k : ℕ, 2 ≤ k → ∃ C c g₀ g₁ : ℝ, 0 < C ∧ ∃ _ : 0 < c,
      c ≤ 1 ∧ 0 < g₀ ∧ 0 < g₁ ∧ ∃ s : ℕ, 0 < s ∧
      ∀ Bstar : ℝ, 0 < Bstar → ∃ W N : ℕ, 0 < W ∧
      ∀ (n L He H m : ℕ) (a G B q Gminus Gplus : ℝ)
        (v w : Fin n → ℕ) (Gs : Fin n → ℝ),
        1 ≤ L → 0 < G → (N:ℝ) ≤ G → 0 < B → B/2 ≤ Bstar →
        (k:ℝ)*L*Real.log (1/(κ:ℝ)) ≤ B/2 → Real.exp (-Bstar) ≤ q →
        (2*A*k)*(m:ℝ) ≤ Bstar →
        (∀ j, W ≤ w j) → (∀ j, 2*cellWidth (w j) m 0 ≤ v j) →
        (∀ j i, i < m → Gs j ≤ c*cellRadius ν e f C (w j) m i/2) →
        (∀ h : ℕ, He < h → h ≤ H → ∃ j, v j ≤ h ∧ h ≤ v j+w j ∧ Gminus ≤ Gs j) →
        (∃ j, v j ≤ H ∧ H ≤ v j+w j ∧ Gplus ≤ Gs j) →
        Gminus ≤ G/2 →
        ENNReal.ofReal (Real.exp (-B)) ≤ ENNReal.ofReal q*
          (ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m))) →
        ∀ π : BudgetProfile (k:=k) e f a G,
        environmentLaw ν (stageBadEvent e f H Gminus Gplus π.val (ENNReal.ofReal (Real.exp (-B)))) ≤
          ENNReal.ofReal ((Real.exp (Cr*k-lam*(B/2)/L)+Cr*k*Real.exp ((B/2)/L)*He /
            fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
              (commonIncrementProcess (realPosition (step e)) f 0) (G/(4*L)))^L) +
          ENNReal.ofReal (Real.exp (Cq*k)*q^lamq) +
          (n:ℝ≥0∞)*((2:ℝ≥0∞)^(m-1)*ENNReal.ofReal (Real.exp (-2*k*m))) := by
  obtain ⟨κ,lam,Cr,hκ,hrows,hlam,hlam1,hCr,hr⟩ := rapid_loss_probability ν hue e f hef htrans
  obtain ⟨lamq,Cq,hlamq,hlamq1,hCq,hq⟩ := fullStream_small_mass_probability ν hue _ (signed_direction_unit e) htrans f.1
  obtain ⟨A,hA,hcells⟩ := actual_cell_no_success ν hue e f hef htrans
  refine ⟨κ,lam,Cr,lamq,Cq,A,hκ,hrows,hlam,hlam1,hCr,hlamq,hlamq1,hCq,hA,fun k hk => ?_⟩
  obtain ⟨C,c,g₀,g₁,hC,hc,hc1,hg₀,hg₁,s,hs,hcb⟩ := hcells k hk
  refine ⟨C,c,g₀,g₁,hC,hc,hc1,hg₀,hg₁,s,hs,fun Bstar hBstar => ?_⟩
  obtain ⟨W,hW,hWbound⟩ := hcb Bstar hBstar
  obtain ⟨Nr,hNr⟩ := hr Bstar hBstar k (by omega)
  obtain ⟨Nq,hNq⟩ := hq Bstar hBstar k (by omega)
  refine ⟨W,max Nq (2*Nr),hW,?_⟩
  intro n L He H m a G B q Gminus Gplus v w Gs hL hG0 hG hB hcap hell hqcap hmb hw hv hGs hcover hgrowth hshortgap hcoef π
  have hGNq : (Nq:ℝ) ≤ G := (show (Nq:ℝ) ≤ (max Nq (2*Nr):ℕ) by exact_mod_cast le_max_left Nq (2*Nr)).trans hG
  have hGNr : (Nr:ℝ) ≤ G-G/2 := by
    have hh : (2:ℝ)*Nr ≤ G := (show (2:ℝ)*Nr ≤ (max Nq (2*Nr):ℕ) by exact_mod_cast le_max_right Nq (2*Nr)).trans hG
    linarith
  have hmass := hNq π.val (π.property.2.mono (fun x hx =>
    (tupleSeparated_coordinate f Nq x).mp (tupleSeparated_mono f hGNq x hx.2))) q hqcap
  have hshort0 := hNr L He a G (G/2) (B/2) hL (by positivity) le_rfl hGNr hell hcap π
  have harg : (G/2)/(2*(L:ℝ))=G/(4*L) := by ring
  rw [harg] at hshort0
  have hshort : environmentLaw ν {ω | relativeBudgetMassENN e f He (G/2) π.val ω < ENNReal.ofReal (Real.exp (-B))} ≤
      ENNReal.ofReal ((Real.exp (Cr*k-lam*(B/2)/L)+Cr*k*Real.exp ((B/2)/L)*He /
        fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (G/(4*L)))^L) := by
    apply le_trans _ (ENNReal.ofReal_le_ofReal hshort0)
    rw [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]
    apply measure_mono
    intro ω hω
    exact hω.trans_le (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith)))
  apply finite_stage_assembly ν e f hef a C c g₀ g₁ A G Gminus Gplus (G/2) hc
    (zero_le_one.trans hA) π He H v w m s hs Gs hv hGs hcover hgrowth (by linarith)
    _ (ENNReal.ofReal q) _ _ _ hcoef hshort hmass
  intro j
  exact hWbound (w j) (hw j) m hmb (v j) (hv j) a (fun _ => π.toLayerProfile) measurable_const

end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.actual_finite_stage_estimate_oai := @OAI.DirectionalTransience.actual_finite_stage_estimate_oai
