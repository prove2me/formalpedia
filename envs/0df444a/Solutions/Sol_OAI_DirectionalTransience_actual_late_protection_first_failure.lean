-- Prove2me | solution 1 for OAI.DirectionalTransience.actual_late_protection_first_failure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:59.447192+00:00
-- url     : https://prove2.me/submissions/5c96a138-e608-4582-a556-b643010a1352

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal004
import Definitions.Def_OAIQ242Bal005
import Theorems.Thm_OAI_DirectionalTransience_fresh_budget_threat_bound

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentRandomTestBound
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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

lemma wordWeight_nonneg {d : ℕ} (ω : Environment d) (x : Lattice d)
    (w : List (Direction d)) : 0 ≤ wordWeight ω x w := by
  induction w generalizing x with
  | nil => simp [wordWeight]
  | cons e w ih => exact mul_nonneg (NNReal.coe_nonneg _) (ih _)

lemma annealed_wordCylinder {d : ℕ} (ν : Measure (Row d)) (w : List (Direction d)) :
    annealedLaw ν (wordCylinder 0 w) =
      ∫⁻ ω, ENNReal.ofReal (wordWeight ω 0 w) ∂environmentLaw ν := by
  rw [annealed_apply ν (measurableSet_wordCylinder 0 w)]
  congr 1
  funext ω
  exact quenched_wordCylinder ω 0 w

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_CoordinateStrip
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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

lemma wordWeight_lower {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (x : Lattice d) (w : List (Direction d)) :
    (κ : ℝ) ^ w.length ≤ wordWeight ω x w := by
  induction w generalizing x with
  | nil => simp [wordWeight]
  | cons e w ih =>
    simp only [List.length_cons, pow_succ', wordWeight]
    exact mul_le_mul (by exact_mod_cast hκ x e) (ih _)
      (pow_nonneg κ.coe_nonneg _) (NNReal.coe_nonneg _)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightSlab
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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

lemma mass_smul_normalizedMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] :
    μ Set.univ • normalizedMeasure μ = μ := by
  by_cases hμ : μ Set.univ = 0
  · have hzero : μ = 0 := Measure.measure_univ_eq_zero.mp hμ
    simp [hzero, normalizedMeasure]
  · rw [normalizedMeasure, smul_smul,
      ENNReal.mul_inv_cancel hμ (measure_ne_top μ Set.univ), one_smul]

lemma quenched_restrict_stay_congr {d : ℕ} (S : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d) :
    (quenchedKernel (ω, x)).restrict (Stay S) =
      (quenchedKernel (η, x)).restrict (Stay S) := by
  apply pathMeasure_ext
  intro f n
  rw [Measure.restrict_apply (measurableSet_pathCylinder f n),
    Measure.restrict_apply (measurableSet_pathCylinder f n)]
  by_cases hf : ∀ j ≤ n, f j ∈ S
  · have he : pathCylinder f n ∩ Stay S =
        (fun X : Path d => fun j => X (n + j)) ⁻¹' Stay S ∩ pathCylinder f n := by
      ext X
      constructor
      · rintro ⟨hX, hS⟩
        exact ⟨fun j => hS (n + j), hX⟩
      · rintro ⟨hS, hX⟩
        refine ⟨hX, fun j => ?_⟩
        by_cases hj : j ≤ n
        · simpa only [hX j hj] using hf j hj
        · have hnj : n ≤ j := by omega
          simpa only [Nat.add_sub_of_le hnj] using hS (j - n)
    rw [he]
    by_cases hfx : f 0 = x
    · rw [quenched_prefix_future ω x f hfx n (measurableSet_stay S),
        quenched_prefix_future η x f hfx n (measurableSet_stay S),
        pathCylinder_weight_locality S ω η hωη x f n (fun j hj => hf j hj.le),
        quenched_stay_congr S ω η hωη (f n)]
    · rw [measure_mono_null Set.inter_subset_right (quenched_pathCylinder_zero ω x f hfx n),
        measure_mono_null Set.inter_subset_right (quenched_pathCylinder_zero η x f hfx n)]
  · have he : pathCylinder f n ∩ Stay S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨hX, hS⟩
      exact hf fun j hj => by simpa only [← hX j hj] using hS j
    rw [he]
    simp

lemma quenched_stay_event_congr {d : ℕ} (A : Set (Path d))
    (T : Set (Lattice d)) (hA : MeasurableSet A) (hAT : A ⊆ Stay T)
    (ω η : Environment d) (hωη : Set.EqOn ω η T) (x : Lattice d) :
    quenchedKernel (ω, x) A = quenchedKernel (η, x) A := by
  have := congrArg (fun μ : Measure (Path d) => μ A)
    (quenched_restrict_stay_congr T ω η hωη x)
  simpa only [Measure.restrict_apply hA, Set.inter_eq_left.mpr hAT] using this

lemma measurable_quenched_stay_event_rows {d : ℕ} (T : Set (Lattice d))
    (x : Lattice d) (hx : x ∈ T) (A : Set (Path d))
    (hA : MeasurableSet A) (hAT : A ⊆ Stay T) :
    @Measurable _ _ (rowSigma T) _ (fun ω : Environment d => quenchedKernel (ω, x) A) := by
  apply measurable_of_row_locality _
    ((Kernel.measurable_coe _ hA).comp (measurable_id.prodMk measurable_const)) T x hx
  intro ω η h
  exact quenched_stay_event_congr A T hA hAT ω η h x

lemma annealed_event_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x : Lattice d) (A : Set (Path d)) (hA : MeasurableSet A) :
    (∫⁻ ω, quenchedKernel (ω, x) ((fun X : Path d => fun n => X n - x) ⁻¹' A)
      ∂environmentLaw ν) = annealedLaw ν A := by
  have ht : Measurable (fun X : Path d => fun n => X n - x) := by fun_prop
  have he (ω : Environment d) :
      quenchedKernel (ω, x) ((fun X : Path d => fun n => X n - x) ⁻¹' A) =
        quenchedKernel ((fun a => ω (x + a)), 0) A := by
    have := congrArg (fun μ : Measure (Path d) => μ A) (quenched_translation ω x 0)
    rw [Measure.map_apply ht hA] at this
    simpa only [add_zero] using this
  simp_rw [he]
  have hm : Measurable (fun ω : Environment d => quenchedKernel (ω, 0) A) :=
    (Kernel.measurable_coe _ hA).comp (measurable_id.prodMk measurable_const)
  rw [← lintegral_map hm (show Measurable (fun ω : Environment d => fun a => ω (x + a)) by
    fun_prop), environment_translation, ← annealed_apply ν hA]

lemma annealed_record_suffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (w : List (Direction d))
    (hrecord : ∀ y ∈ wordDepartures 0 w,
      dot (realPosition y) ℓ < dot (realPosition (wordPath 0 w w.length)) ℓ)
    (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    annealedLaw ν ((fun X : Path d => fun j => X (w.length + j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) =
      annealedLaw ν (wordCylinder 0 w) * annealedLaw ν A := by
  let y := wordPath 0 w w.length
  let S : Set (Lattice d) := ↑(wordDepartures 0 w)
  let T : Set (Lattice d) := {z | dot (realPosition y) ℓ ≤ dot (realPosition z) ℓ}
  let B : Set (Path d) := (fun X : Path d => fun j => X j - y) ⁻¹' A
  have hB : MeasurableSet B := hA.preimage (by fun_prop)
  have hBT : B ⊆ Stay T := by
    intro X hX j
    have h := hAD hX j
    change dot (realPosition y) ℓ ≤ dot (realPosition (X j)) ℓ
    change dot (realPosition 0) ℓ ≤ dot (realPosition (X j - y)) ℓ at h
    rw [dot_realPosition_sub] at h
    have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot, realPosition]
    rw [hzero] at h
    linarith
  have hST : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (not_le_of_gt (hrecord z hz)) hz'
  have hw (ω : Environment d) : quenchedKernel (ω, 0)
      ((fun X : Path d => fun j => X (w.length + j) - y) ⁻¹' A ∩ wordCylinder 0 w) =
      ENNReal.ofReal (wordWeight ω 0 w) * quenchedKernel (ω, y) B := by
    have hh := quenched_prefix_future ω 0 (wordPath 0 w) (by simp) w.length hB
    change quenchedKernel (ω, 0) (_ ∩ wordCylinder 0 w) =
      quenchedKernel (ω, 0) (wordCylinder 0 w) * quenchedKernel (ω, y) B at hh
    rwa [quenched_wordCylinder] at hh
  rw [annealed_apply ν ((hA.preimage (by fun_prop)).inter (measurableSet_wordCylinder 0 w))]
  change (∫⁻ ω, quenchedKernel (ω, 0)
    ((fun X : Path d => fun j => X (w.length + j) - y) ⁻¹' A ∩ wordCylinder 0 w)
    ∂environmentLaw ν) = _
  simp_rw [hw]
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hST)
    ((measurable_wordWeight_on 0 w (fun _ hz => hz)).ennreal_ofReal)
    (measurable_quenched_stay_event_rows T y
      (show dot (realPosition y) ℓ ≤ dot (realPosition y) ℓ from le_rfl) B hB hBT)]
  rw [← annealed_wordCylinder, annealed_event_translation ν y A hA]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StrictRecord
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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

lemma measurableSet_trueRecord {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    MeasurableSet {X : Path d | TrueRecord ℓ X n} :=
  (measurableSet_strictRecord ℓ n).inter (measurableSet_futureNoDrop ℓ n)

lemma suffix_noDrop_iff {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) :
    (fun j => X (n + j) - X n) ∈ NoDrop ℓ 0 ↔ X ∈ FutureNoDrop ℓ n := by
  change (∀ j, dot (realPosition 0) ℓ ≤ dot (realPosition (X (n + j) - X n)) ℓ) ↔ _
  simp only [dot_realPosition_sub, FutureNoDrop, Set.mem_ofPred_eq]
  have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot, realPosition]
  rw [hzero]
  exact forall_congr' fun j => sub_nonneg

lemma conditionedLaw_apply_of_subset {d : ℕ} (ν : Measure (Row d))
    (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    conditionedLaw ν ℓ A = (annealedLaw ν (NoDrop ℓ 0))⁻¹ * annealedLaw ν A := by
  rw [conditionedLaw, Measure.smul_apply, Measure.restrict_apply hA,
    Set.inter_eq_left.mpr hAD, smul_eq_mul]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FirstWordEvent
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma conditionedLaw_inter_noDrop {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    conditionedLaw ν ℓ (A ∩ NoDrop ℓ 0) = conditionedLaw ν ℓ A := by
  simp only [conditionedLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA, Measure.restrict_apply (hA.inter (measurableSet_noDrop ℓ 0)),
    Set.inter_self, Set.inter_assoc]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_Regeneration
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma annealed_wordCylinder_lower {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (κ : ℝ≥0) (hκ : ∀ᵐ ω ∂environmentLaw ν, ∀ x e, κ ≤ (ω x).1 e)
    (w : List (Direction d)) : (κ : ℝ≥0∞)^w.length ≤ annealedLaw ν (wordCylinder 0 w) := by
  rw [annealed_wordCylinder]
  have hconst : (κ : ℝ≥0∞)^w.length = ∫⁻ _ : Environment d, (κ : ℝ≥0∞)^w.length
      ∂environmentLaw ν := by simp
  rw [hconst]
  apply lintegral_mono_ae
  filter_upwards [hκ] with ω hω
  have hh := ENNReal.ofReal_le_ofReal (wordWeight_lower ω hω 0 w)
  simpa only [ENNReal.ofReal_pow κ.coe_nonneg, ENNReal.ofReal_coe_nnreal] using hh

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonTrueRecord
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma measurableSet_commonTrueRecord {d : ℕ} (ℓ : Vector d) (n m : ℕ) :
    MeasurableSet {P : Path d × Path d | CommonTrueRecord ℓ P n m} := by
  exact ((measurableSet_trueRecord ℓ n).preimage measurable_fst).inter
    (((measurableSet_trueRecord ℓ m).preimage measurable_snd).inter
      (measurableSet_eq_fun
        ((measurable_of_countable (fun z : Lattice d => dot (realPosition z) ℓ)).comp
          ((measurable_pi_apply n).comp measurable_fst))
        ((measurable_of_countable (fun z : Lattice d => dot (realPosition z) ℓ)).comp
          ((measurable_pi_apply m).comp measurable_snd))))

lemma measurableSet_firstCommonTrueRecord {d : ℕ} (ℓ : Vector d) (n m : ℕ) :
    MeasurableSet {P : Path d × Path d | FirstCommonTrueRecord ℓ P n m} := by
  simp only [FirstCommonTrueRecord, Set.ofPred_and, Set.ofPred_forall]
  refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((measurableSet_commonTrueRecord ℓ n m).inter ?_))
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
        (measurableSet_commonTrueRecord ℓ j k).compl

lemma not_trueRecord_before_true_iff {d : ℕ} (ℓ : Vector d) (X : Path d)
    {j n : ℕ} (hjn : j < n) (hj : StrictRecord ℓ X j) (hn : TrueRecord ℓ X n) :
    ¬ TrueRecord ℓ X j ↔ ∃ k, j < k ∧ k < n ∧
      dot (realPosition (X k)) ℓ < dot (realPosition (X j)) ℓ := by
  constructor
  · intro hnot
    have hD : ¬ X ∈ FutureNoDrop ℓ j := fun h => hnot ⟨hj,h⟩
    change ¬ ∀ k, dot (realPosition (X j)) ℓ ≤ dot (realPosition (X (j+k))) ℓ at hD
    push Not at hD
    obtain ⟨a,ha⟩ := hD
    have hpos : 0 < a := by
      by_contra h
      have hz : a = 0 := by omega
      simp [hz] at ha
    refine ⟨j+a, by omega, ?_, ha⟩
    by_contra hkn
    have hnj : dot (realPosition (X j)) ℓ < dot (realPosition (X n)) ℓ := hn.1 j hjn
    have hd := hn.2 (j+a-n)
    change dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n+(j+a-n)))) ℓ at hd
    rw [show n+(j+a-n) = j+a by omega] at hd
    linarith
  · rintro ⟨k,hjk,_,hdrop⟩ htrue
    have hd := htrue.2 (k-j)
    change dot (realPosition (X j)) ℓ ≤ dot (realPosition (X (j+(k-j)))) ℓ at hd
    rw [show j+(k-j) = k by omega] at hd
    exact (not_lt_of_ge hd) hdrop

lemma noDrop_iff_prefix_and_future {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (X : Path d) (n : ℕ) (hD : X ∈ FutureNoDrop ℓ n) :
    X ∈ NoDrop ℓ x ↔
      ∀ j ≤ n, dot (realPosition x) ℓ ≤ dot (realPosition (X j)) ℓ := by
  constructor
  · exact fun h j _ => h j
  · intro h j
    by_cases hj : j ≤ n
    · exact h j hj
    · have hd := hD (j-n)
      change dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n+(j-n)))) ℓ at hd
      rw [show n+(j-n) = j by omega] at hd
      exact (h n le_rfl).trans hd

lemma firstCommonWords_characterization {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (w v : List (Direction d)) (P : Path d × Path d)
    (hw : P.1 ∈ wordCylinder x w) (hv : P.2 ∈ wordCylinder y v) :
    (P.1 ∈ NoDrop ℓ x ∧ P.2 ∈ NoDrop ℓ y ∧
      FirstCommonTrueRecord ℓ P w.length v.length) ↔
    (AdmissibleCommonWords ℓ x y w v ∧
      P.1 ∈ FutureNoDrop ℓ w.length ∧ P.2 ∈ FutureNoDrop ℓ v.length) := by
  have hr1 j (hj : j ≤ w.length) : StrictRecord ℓ P.1 j ↔
      StrictRecord ℓ (wordPath x w) j := strictRecord_congr_prefix ℓ hj hw
  have hr2 k (hk : k ≤ v.length) : StrictRecord ℓ P.2 k ↔
      StrictRecord ℓ (wordPath y v) k := strictRecord_congr_prefix ℓ hk hv
  constructor
  · rintro ⟨hD1,hD2,hwpos,hvpos,⟨ht1,ht2,he⟩,hfirst⟩
    refine ⟨⟨hwpos,hvpos,?_,(hr1 _ le_rfl).mp ht1.1,(hr2 _ le_rfl).mp ht2.1,
      ?_,?_,?_⟩,ht1.2,ht2.2⟩
    · simpa only [hw _ le_rfl,hv _ le_rfl] using he
    · intro j hj
      simpa only [hw j hj] using hD1 j
    · intro k hk
      simpa only [hv k hk] using hD2 k
    · intro j k hj hjn hk hkm hrj hrk heq
      have hj' := (hr1 j hjn.le).mpr hrj
      have hk' := (hr2 k hkm.le).mpr hrk
      have he' : dot (realPosition (P.1 j)) ℓ = dot (realPosition (P.2 k)) ℓ := by
        simpa only [hw j hjn.le,hv k hkm.le] using heq
      have hnot := hfirst j k hj hjn hk hkm
      have hdis : ¬ TrueRecord ℓ P.1 j ∨ ¬ TrueRecord ℓ P.2 k := by
        by_cases h1 : TrueRecord ℓ P.1 j
        · exact Or.inr fun h2 => hnot ⟨h1,h2,he'⟩
        · exact Or.inl h1
      rcases hdis with h1 | h2
      · obtain ⟨a,hja,han,ha⟩ := (not_trueRecord_before_true_iff ℓ P.1 hjn hj' ht1).mp h1
        exact Or.inl ⟨a,hja,han,by simpa only [hw a han.le,hw j hjn.le] using ha⟩
      · obtain ⟨b,hkb,hbm,hb⟩ := (not_trueRecord_before_true_iff ℓ P.2 hkm hk' ht2).mp h2
        exact Or.inr ⟨b,hkb,hbm,by simpa only [hv b hbm.le,hv k hkm.le] using hb⟩
  · rintro ⟨⟨hwpos,hvpos,he,hrw,hrv,hD1,hD2,hfail⟩,hF1,hF2⟩
    have ht1 : TrueRecord ℓ P.1 w.length := ⟨(hr1 _ le_rfl).mpr hrw,hF1⟩
    have ht2 : TrueRecord ℓ P.2 v.length := ⟨(hr2 _ le_rfl).mpr hrv,hF2⟩
    refine ⟨(noDrop_iff_prefix_and_future ℓ x P.1 _ hF1).mpr ?_,
      (noDrop_iff_prefix_and_future ℓ y P.2 _ hF2).mpr ?_,
      hwpos,hvpos,⟨ht1,ht2,?_⟩,?_⟩
    · intro j hj
      simpa only [hw j hj] using hD1 j hj
    · intro k hk
      simpa only [hv k hk] using hD2 k hk
    · simpa only [hw _ le_rfl,hv _ le_rfl] using he
    · intro j k hj hjn hk hkm htrue
      have hdis := hfail j k hj hjn hk hkm ((hr1 _ hjn.le).mp htrue.1.1)
        ((hr2 _ hkm.le).mp htrue.2.1.1)
        (by simpa only [hw j hjn.le,hv k hkm.le] using htrue.2.2)
      rcases hdis with ⟨a,hja,han,ha⟩ | ⟨b,hkb,hbm,hb⟩
      · exact (not_trueRecord_before_true_iff ℓ P.1 hjn htrue.1.1 ht1).mpr
          ⟨a,hja,han,by simpa only [hw a han.le,hw j hjn.le] using ha⟩ htrue.1
      · exact (not_trueRecord_before_true_iff ℓ P.2 hkm htrue.2.1.1 ht2).mpr
          ⟨b,hkb,hbm,by simpa only [hv b hbm.le,hv k hkm.le] using hb⟩ htrue.2.1

lemma measurableSet_commonWordEvent {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (w v : List (Direction d)) : MeasurableSet (commonWordEvent ℓ x y w v) :=
  ((measurableSet_wordCylinder x w).prod (measurableSet_wordCylinder y v)).inter
    (measurableSet_firstCommonTrueRecord ℓ w.length v.length)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentPairLaw
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma commonTrueRecord_time_order {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    {n m j k : ℕ} (hn : CommonTrueRecord ℓ P n m) (hj : CommonTrueRecord ℓ P j k) :
    n < j ↔ m < k := by
  constructor
  · intro hnj
    have hheight := hj.1.1 n hnj
    rw [hn.2.2,hj.2.2] at hheight
    by_contra hmk
    rcases lt_or_eq_of_le (not_lt.mp hmk) with hkm | rfl
    · exact (not_lt_of_ge (hn.2.1.1 k hkm).le) hheight
    · exact (lt_irrefl _ hheight)
  · intro hmk
    have hheight := hj.2.1.1 m hmk
    rw [← hn.2.2,← hj.2.2] at hheight
    by_contra hnj
    rcases lt_or_eq_of_le (not_lt.mp hnj) with hjn | rfl
    · exact (not_lt_of_ge (hn.1.1 j hjn).le) hheight
    · exact (lt_irrefl _ hheight)

lemma firstCommonTrueRecord_unique {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    {n m j k : ℕ} (hn : FirstCommonTrueRecord ℓ P n m)
    (hj : FirstCommonTrueRecord ℓ P j k) : n = j ∧ m = k := by
  have hnj : n = j := by
    rcases lt_trichotomy n j with h | h | h
    · exact False.elim (hj.2.2.2 n m hn.1 h hn.2.1
        ((commonTrueRecord_time_order ℓ P hn.2.2.1 hj.2.2.1).mp h) hn.2.2.1)
    · exact h
    · exact False.elim (hn.2.2.2 j k hj.1 h hj.2.1
        ((commonTrueRecord_time_order ℓ P hj.2.2.1 hn.2.2.1).mp h) hj.2.2.1)
  refine ⟨hnj,?_⟩
  apply Nat.le_antisymm
  · by_contra h
    have := (commonTrueRecord_time_order ℓ P hj.2.2.1 hn.2.2.1).mpr (by omega : k < m)
    omega
  · by_contra h
    have := (commonTrueRecord_time_order ℓ P hn.2.2.1 hj.2.2.1).mpr (by omega : m < k)
    omega

lemma measurableSet_firstPairWordEvent {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d)) : MeasurableSet (FirstPairWordEvent ℓ wv) :=
  ((measurableSet_noDrop ℓ 0).prod (measurableSet_noDrop ℓ 0)).inter
    (measurableSet_commonWordEvent ℓ 0 0 wv.1 wv.2)

lemma firstPairWordEvent_nil {d : ℕ} (ℓ : Vector d) :
    FirstPairWordEvent ℓ (([] : List (Direction d)),[]) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  exact fun P hP => Nat.lt_irrefl 0 hP.2.2.1

lemma firstPairWordEvent_disjoint {d : ℕ} (ℓ : Vector d) :
    Pairwise (fun u v : List (Direction d) × List (Direction d) =>
      Disjoint (FirstPairWordEvent ℓ u) (FirstPairWordEvent ℓ v)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro P hPu hPv
  have hlen := firstCommonTrueRecord_unique ℓ P hPu.2.2 hPv.2.2
  exact huv (Prod.ext (word_eq_of_cylinders 0 u.1 v.1 P.1 hPu.2.1.1 hPv.2.1.1 hlen.1)
    (word_eq_of_cylinders 0 u.2 v.2 P.2 hPu.2.1.2 hPv.2.1.2 hlen.2))

lemma firstPairWord_eq_iff {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (wv : List (Direction d) × List (Direction d)) (hwv : wv ≠ ([],[])) :
    firstPairWord ℓ P = wv ↔ P ∈ FirstPairWordEvent ℓ wv := by
  classical
  unfold firstPairWord
  split_ifs with h
  · constructor
    · intro he
      exact he ▸ h.choose_spec
    · intro hP
      by_contra hne
      exact (Set.disjoint_left.mp (firstPairWordEvent_disjoint ℓ hne)) h.choose_spec hP
  · simp only [eq_comm (a := (([],[]) : List (Direction d) × List (Direction d))),
      hwv,false_iff]
    exact fun hP => h ⟨wv,hP⟩

lemma firstPairWord_nil_iff {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) :
    firstPairWord ℓ P = ([],[]) ↔ ¬ ∃ wv, P ∈ FirstPairWordEvent ℓ wv := by
  classical
  unfold firstPairWord
  split_ifs with h
  · simp only [h,not_true_eq_false,iff_false]
    intro he
    have := h.choose_spec
    rw [he,firstPairWordEvent_nil] at this
    exact this
  · simp [h]

lemma measurable_firstPairWord {d : ℕ} (ℓ : Vector d) : Measurable (firstPairWord ℓ) := by
  classical
  apply measurable_to_countable'
  intro wv
  by_cases h : wv = ([],[])
  · subst wv
    have he : firstPairWord ℓ ⁻¹' {([],[])} = (⋃ wv,FirstPairWordEvent ℓ wv)ᶜ := by
      ext P
      simp only [Set.mem_preimage,Set.mem_singleton_iff,firstPairWord_nil_iff,
        Set.mem_compl_iff,Set.mem_iUnion]
    rw [he]
    exact (MeasurableSet.iUnion (measurableSet_firstPairWordEvent ℓ)).compl
  · have he : firstPairWord ℓ ⁻¹' {wv} = FirstPairWordEvent ℓ wv := by
      ext P
      exact firstPairWord_eq_iff ℓ P wv h
    rw [he]
    exact measurableSet_firstPairWordEvent ℓ wv

lemma measurable_renewPairSuffix {d : ℕ} (ℓ : Vector d) : Measurable (renewPairSuffix ℓ) := by
  have hf : Measurable (fun P : Path d × Path d => (firstPairWord ℓ P).1.length) :=
    (measurable_of_countable List.length).comp (measurable_firstPairWord ℓ).fst
  have hg : Measurable (fun P : Path d × Path d => (firstPairWord ℓ P).2.length) :=
    (measurable_of_countable List.length).comp (measurable_firstPairWord ℓ).snd
  have heval : Measurable (fun p : Path d × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro j
    exact (heval.comp (measurable_fst.prodMk (hf.add_const j))).sub
      (heval.comp (measurable_fst.prodMk hf))
  · apply Measurable.of_eval
    intro j
    exact (heval.comp (measurable_snd.prodMk (hg.add_const j))).sub
      (heval.comp (measurable_snd.prodMk hg))

lemma conditioned_record_word_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (w : List (Direction d)) (hr : StrictRecord ℓ (wordPath 0 w) w.length)
    (hprefix : ∀ j ≤ w.length, dot (realPosition (0 : Lattice d)) ℓ ≤
      dot (realPosition (wordPath 0 w j)) ℓ)
    (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    conditionedLaw ν ℓ ((fun X : Path d => fun j => X (w.length+j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) =
      annealedLaw ν (wordCylinder 0 w) * conditionedLaw ν ℓ A := by
  have hE : MeasurableSet ((fun X : Path d => fun j => X (w.length+j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) :=
    (hA.preimage (by fun_prop)).inter (measurableSet_wordCylinder _ _)
  have hED : ((fun X : Path d => fun j => X (w.length+j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) ⊆ NoDrop ℓ 0 := by
    rintro X ⟨hXA,hX⟩
    have hD : X ∈ FutureNoDrop ℓ w.length := by
      apply (suffix_noDrop_iff ℓ X w.length).mp
      simpa only [hX w.length le_rfl] using hAD hXA
    apply (noDrop_iff_prefix_and_future ℓ 0 X w.length hD).mpr
    intro j hj
    rw [hX j hj]
    exact hprefix j hj
  have hdep : ∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
      dot (realPosition (wordPath 0 w w.length)) ℓ := by
    intro y hy
    obtain ⟨j,hj,rfl⟩ := (wordDepartures_mem_iff 0 y w).mp hy
    exact hr j hj
  rw [conditionedLaw_apply_of_subset ν ℓ _ hE hED,
    annealed_record_suffix ν ℓ w hdep A hA hAD,
    conditionedLaw_apply_of_subset ν ℓ A hA hAD]
  ac_rfl

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FixedPairSuffix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma firstPairWordEvent_suffix_rectangle {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d))
    (had : AdmissibleCommonWords ℓ 0 0 wv.1 wv.2) (A B : Set (Path d)) :
    FirstPairWordEvent ℓ wv ∩ fixedPairSuffix wv ⁻¹' (A ×ˢ B) =
      (((fun X : Path d => fun j => X (wv.1.length+j) - wordPath 0 wv.1 wv.1.length) ⁻¹'
          (A ∩ NoDrop ℓ 0) ∩ wordCylinder 0 wv.1) ×ˢ
       ((fun X : Path d => fun j => X (wv.2.length+j) - wordPath 0 wv.2 wv.2.length) ⁻¹'
          (B ∩ NoDrop ℓ 0) ∩ wordCylinder 0 wv.2)) := by
  ext P
  constructor
  · rintro ⟨hP,hAB⟩
    have hFs := ((firstCommonWords_characterization ℓ 0 0 wv.1 wv.2 P
      hP.2.1.1 hP.2.1.2).mp ⟨hP.1.1,hP.1.2,hP.2.2⟩).2
    refine ⟨⟨⟨hAB.1,?_⟩,hP.2.1.1⟩,⟨⟨hAB.2,?_⟩,hP.2.1.2⟩⟩
    · have := (suffix_noDrop_iff ℓ P.1 wv.1.length).mpr hFs.1
      simpa only [hP.2.1.1 wv.1.length le_rfl] using this
    · have := (suffix_noDrop_iff ℓ P.2 wv.2.length).mpr hFs.2
      simpa only [hP.2.1.2 wv.2.length le_rfl] using this
  · rintro ⟨⟨⟨hA,hD1⟩,hw⟩,⟨⟨hB,hD2⟩,hv⟩⟩
    have hF1 : P.1 ∈ FutureNoDrop ℓ wv.1.length := by
      apply (suffix_noDrop_iff ℓ P.1 wv.1.length).mp
      simpa only [hw wv.1.length le_rfl] using hD1
    have hF2 : P.2 ∈ FutureNoDrop ℓ wv.2.length := by
      apply (suffix_noDrop_iff ℓ P.2 wv.2.length).mp
      simpa only [hv wv.2.length le_rfl] using hD2
    have hc := (firstCommonWords_characterization ℓ 0 0 wv.1 wv.2 P hw hv).mpr
      ⟨had,hF1,hF2⟩
    exact ⟨⟨⟨hc.1,hc.2.1⟩,⟨hw,hv⟩,hc.2.2⟩,hA,hB⟩

lemma independent_conditioned_pair_word_rectangle {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (wv : List (Direction d) × List (Direction d))
    (had : AdmissibleCommonWords ℓ 0 0 wv.1 wv.2)
    (A B : Set (Path d)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    independentConditionedPairLaw ν ℓ
      (FirstPairWordEvent ℓ wv ∩ fixedPairSuffix wv ⁻¹' (A ×ˢ B)) =
      (annealedLaw ν (wordCylinder 0 wv.1) * annealedLaw ν (wordCylinder 0 wv.2)) *
        independentConditionedPairLaw ν ℓ (A ×ˢ B) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  rw [firstPairWordEvent_suffix_rectangle ℓ wv had A B,
    independentConditionedPairLaw,Measure.prod_prod,Measure.prod_prod,
    conditioned_record_word_factor ν ℓ wv.1 had.2.2.2.1 had.2.2.2.2.2.1 _
      (hA.inter (measurableSet_noDrop ℓ 0)) Set.inter_subset_right,
    conditioned_record_word_factor ν ℓ wv.2 had.2.2.2.2.1 had.2.2.2.2.2.2.1 _
      (hB.inter (measurableSet_noDrop ℓ 0)) Set.inter_subset_right,
    conditionedLaw_inter_noDrop ν ℓ A hA,conditionedLaw_inter_noDrop ν ℓ B hB]
  ac_rfl

lemma independent_conditioned_pair_word_mass {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (wv : List (Direction d) × List (Direction d))
    (had : AdmissibleCommonWords ℓ 0 0 wv.1 wv.2) :
    independentConditionedPairLaw ν ℓ (FirstPairWordEvent ℓ wv) =
      annealedLaw ν (wordCylinder 0 wv.1) * annealedLaw ν (wordCylinder 0 wv.2) := by
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ hp
  simpa only [Set.univ_prod_univ,Set.preimage_univ,Set.inter_univ,measure_univ,mul_one] using
    independent_conditioned_pair_word_rectangle ν ℓ hp wv had Set.univ Set.univ
      MeasurableSet.univ MeasurableSet.univ

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordIncrement
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma admissible_transverse_commonWords {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1) :
    AdmissibleCommonWords (realPosition (step e)) 0 0 [f,e] [e] := by
  have hzero : dot (realPosition (0 : Lattice d)) (realPosition (step e)) = 0 := by
    simp [dot,realPosition]
  have he := signed_direction_unit e
  have hf : dot (realPosition (step f)) (realPosition (step e)) = 0 := by
    rw [dot_signed_direction,signedCoordinate_step_other e f hef]
  have hfe : dot (realPosition (step f+step e)) (realPosition (step e)) = 1 := by
    rw [dot_realPosition_add,hf,he]; ring
  refine ⟨by simp,by simp,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_cons,List.length_nil,wordPath,zero_add] using hfe.trans he.symm
  · intro j hj
    have hj' : j = 0 ∨ j = 1 := by simp only [List.length_cons,List.length_nil] at hj; omega
    rcases hj' with rfl | rfl <;>
      simp only [List.length_cons,List.length_nil,wordPath,zero_add,hzero,hf,hfe] <;> norm_num
  · intro j hj
    have hj' : j = 0 := by simp only [List.length_cons,List.length_nil] at hj; omega
    subst j
    simp only [List.length_cons,List.length_nil,wordPath,zero_add,hzero,he]
    norm_num
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
      simp only [List.length_cons,List.length_nil] at hj; omega
    rcases hj' with rfl | rfl | rfl <;>
      simp only [wordPath,zero_add,hzero,hf,hfe] <;> norm_num
  · intro j hj
    have hj' : j = 0 ∨ j = 1 := by simp only [List.length_cons,List.length_nil] at hj; omega
    rcases hj' with rfl | rfl <;> simp only [wordPath,zero_add,hzero,he] <;> norm_num
  · intro j k _ _ hk hkl _ _ _
    simp only [List.length_cons,List.length_nil] at hkl
    omega

lemma annealed_wordCylinder_positive {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (w : List (Direction d)) :
    0 < annealedLaw ν (wordCylinder 0 w) := by
  obtain ⟨κ,hκ,hrows⟩ := environment_uniform_elliptic ν hue
  exact (ENNReal.pow_pos (by exact_mod_cast hκ : (0 : ℝ≥0∞) < κ) w.length).trans_le
    (annealed_wordCylinder_lower ν κ hrows w)

lemma independent_commonWordIncrement_nonzero {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    0 < independentConditionedPairLaw ν (realPosition (step e))
      {P | commonWordIncrement f (firstPairWord (realPosition (step e)) P) ≠ 0} := by
  let ℓ := realPosition (step e)
  have had := admissible_transverse_commonWords e f hef
  have hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0 := ne_of_gt
    (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hm : 0 < independentConditionedPairLaw ν ℓ (FirstPairWordEvent ℓ ([f,e],[e])) := by
    rw [independent_conditioned_pair_word_mass ν ℓ hp _ had]
    exact ENNReal.mul_pos (ne_of_gt (annealed_wordCylinder_positive ν hue _))
      (ne_of_gt (annealed_wordCylinder_positive ν hue _))
  apply hm.trans_le (measure_mono _)
  intro P hP
  have heq : firstPairWord ℓ P = ([f,e],[e]) :=
    (firstPairWord_eq_iff ℓ P _ (by simp)).mpr hP
  change commonWordIncrement f (firstPairWord ℓ P) ≠ 0
  rw [heq]
  simp only [commonWordIncrement,wordCoordinate,List.length_cons,List.length_nil,
    wordPath,zero_add,signedCoordinate_add,signedCoordinate_step_self,
    signedCoordinate_step_other f e (Ne.symm hef)]
  norm_num

lemma integrable_truncated_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S) (r : ℝ) :
    Integrable (fun x => min ((S x)^2) (r^2)) μ := by
  apply (integrable_const (r^2)).mono' ((hS.pow_const 2).min measurable_const).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
    exact min_le_right _ _

lemma truncatedVariance_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) {r : ℝ} (hr : 0 < r) :
    0 < truncatedVariance μ S r := by
  apply (integral_pos_iff_support_of_nonneg (fun x => le_min (sq_nonneg _) (sq_nonneg _))
    (integrable_truncated_square μ S hS r)).mpr
  apply hne.trans_le (measure_mono _)
  intro x hx
  exact ne_of_gt (lt_min (sq_pos_of_ne_zero hx) (sq_pos_of_pos hr))

lemma truncatedVariance_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : truncatedVariance μ S r ≤ truncatedVariance μ S s := by
  apply integral_mono (integrable_truncated_square μ S hS r) (integrable_truncated_square μ S hS s)
  intro x
  exact min_le_min_left _ (pow_le_pow_left₀ hr hrs 2)

lemma fluctuationScale_scaling {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) (hc1 : c ≤ 1) :
    c^2*fluctuationScale μ S r ≤ fluctuationScale μ S (c*r) := by
  have hcr := mul_pos hc hr
  have hle : c*r ≤ r := by nlinarith
  unfold fluctuationScale
  rw [← mul_div_assoc,mul_pow]
  exact div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (truncatedVariance_pos μ S hS hne hcr) (truncatedVariance_mono μ S hS hcr.le hle)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SymmetricTruncate
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma measurable_commonIncrementProcess {d : ℕ} (ℓ : Vector d) (e : Direction d) (n : ℕ) :
    Measurable (commonIncrementProcess ℓ e n) :=
  (measurable_of_countable (commonWordIncrement e)).comp
    ((measurable_firstPairWord ℓ).comp ((measurable_renewPairSuffix ℓ).iterate n))

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TupleEndpoint
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
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

lemma measure_le_of_singletons {A : Type*} [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A] (μ ν : Measure A)
    (h : ∀ x, μ {x} ≤ ν {x}) : μ ≤ ν := by
  intro s
  conv_lhs => rw [← Measure.sum_smul_dirac μ]
  conv_rhs => rw [← Measure.sum_smul_dirac ν]
  simp only [Measure.sum_apply_of_countable, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul_left (h x) _

end TupleKernel

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_FiniteWordGeometry
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_FreshBudgetEvent
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma fresh_random_budget_mass_lt {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a G r s : ℝ) (H : ℕ)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A)
    (c : ℝ≥0∞)
    (hbound : ∀ η ∈ A, environmentLaw ν {ω | relativeBudgetMass e f H r (π η).val ω < s} ≤ c) :
    environmentLaw ν (A∩{ω | relativeBudgetMass e f H r (π ω).val ω < s}) ≤ c*environmentLaw ν A := by
  let S := BelowHeight (realPosition (step e)) a
  let T : Set (Lattice d) := {y | a≤dot (realPosition y) (realPosition (step e))}
  let B : Set (Environment d×Environment d) := {p | relativeBudgetMass e f H r (π p.1).val p.2 < s}
  have hQ := budgetProfileMass_joint_rows (k:=k) e f a G H r T (fun x hx j y hy => by
    change a≤dot (realPosition y) (realPosition (step e))
    simpa only [hx j] using hy.1)
  have hB : @MeasurableSet (Environment d×Environment d) (MeasurableSpace.prod (rowSigma S) (rowSigma T)) B :=
    measurableSet_lt (hQ.comp ((hπ.comp measurable_fst).prodMk measurable_snd)) measurable_const
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  have hb (η : Environment d) (hη : η∈A) :
      (@Measure.map (Environment d) (Environment d) inferInstance (rowSigma T) id (environmentLaw ν))
        {ω | (η,ω)∈B} ≤ c := by
    rw [show {ω | (η,ω)∈B}=Prod.mk η ⁻¹' B from rfl,
      Measure.map_apply hV (hB.preimage measurable_prodMk_left)]
    exact hbound η hη
  apply @fresh_rows_random_test_bound d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
    ν _ S T _ id id measurable_id measurable_id A hA B hB c hb
  exact Set.disjoint_left.mpr fun x hx hy =>
    (not_lt.mpr (show a≤dot (realPosition x) (realPosition (step e)) from hy))
      (show dot (realPosition x) (realPosition (step e))<a from hx)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CappedLoss
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace DirectionalTransience

lemma cappedLogLoss_bounds {a q : ℝ} (ha : 0≤a) (hq : 0≤q) (hq1 : q≤1) :
    0 ≤ cappedLogLoss a q ∧ cappedLogLoss a q≤a := by
  unfold cappedLogLoss
  split
  · exact ⟨ha,le_rfl⟩
  · have hlog : Real.log q≤0 := Real.log_nonpos hq hq1
    exact ⟨le_min ha (neg_nonneg.mpr hlog),min_le_left _ _⟩

lemma lt_cappedLogLoss_iff {a q x : ℝ} (hq : 0≤q) (hx : 0≤x) :
    x < cappedLogLoss a q ↔ x<a ∧ q<Real.exp (-x) := by
  by_cases hnonpos : a ≤ 0
  · have hax : a ≤ x := hnonpos.trans hx
    unfold cappedLogLoss
    split
    · simp only [not_lt_of_ge hax, false_and]
    · simp only [lt_min_iff, not_lt_of_ge hax, false_and]
  unfold cappedLogLoss
  by_cases hq0 : q=0
  · simp [hq0,Real.exp_pos]
  · rw [ite_eq_right hq0,lt_min_iff]
    constructor
    · rintro ⟨ha,hq'⟩
      refine ⟨ha,?_⟩
      have : Real.log q < -x := by linarith
      simpa [Real.exp_log (lt_of_le_of_ne hq (Ne.symm hq0))] using Real.exp_lt_exp.mpr this
    · rintro ⟨ha,hq'⟩
      have hh := Real.log_lt_log (lt_of_le_of_ne hq (Ne.symm hq0)) hq'
      rw [Real.log_exp] at hh
      exact ⟨ha,by linarith⟩

lemma measurable_cappedLogLoss {Ω : Type*} [MeasurableSpace Ω]
    (a : ℝ) (q : Ω → ℝ) (hq : Measurable q) :
    Measurable (fun ω => cappedLogLoss a (q ω)) := by
  unfold cappedLogLoss
  exact Measurable.ite (measurableSet_eq_fun hq measurable_const)
    measurable_const (measurable_const.min hq.log.neg)

lemma integrable_exp_cappedLogLoss {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (a t : ℝ) (ha : 0≤a) (ht : 0≤t)
    (q : Ω → ℝ) (hq : Measurable q) (hq0 : ∀ ω, 0≤q ω) (hq1 : ∀ ω, q ω≤1) :
    Integrable (fun ω => Real.exp (t*cappedLogLoss a (q ω))) μ := by
  apply (integrable_const (Real.exp (t*a))).mono'
    ((measurable_cappedLogLoss a q hq).const_mul t).exp.aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (cappedLogLoss_bounds ha (hq0 ω) (hq1 ω)).2 ht)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace DirectionalTransience

lemma exp_moment_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0≤X ω) (a : ℝ) (hXa : ∀ ω, X ω≤a)
    (t D : ℝ) (ht : 0<t) (hD : 0≤D)
    (htail : ∀ x : ℝ, 0≤x → μ {ω | x<X ω} ≤ ENNReal.ofReal (D*Real.exp (-2*t*x))) :
    (∫ ω, Real.exp (t*X ω) ∂μ) ≤ 1+D := by
  have hE : Integrable (fun ω => Real.exp (t*X ω)) μ := by
    apply (integrable_const (Real.exp (t*a))).mono' (hX.const_mul t).exp.aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hXa ω) ht.le)
  have hg : Continuous (fun x : ℝ => t*Real.exp (t*x)) := by fun_prop
  have hprim (x : ℝ) : (∫ u in 0..x, t*Real.exp (t*u))=Real.exp (t*x)-1 := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => Real.exp (t*u)) (f' := fun u => t*Real.exp (t*u))
      (a := 0) (b := x) (fun u _ => by
        simpa only [id_eq,mul_one,mul_comm] using ((hasDerivAt_id u).const_mul t).exp) (hg.intervalIntegrable 0 x)
    simpa only [mul_zero, Real.exp_zero] using hh
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ hX0) hX.aemeasurable (fun x _ => hg.intervalIntegrable 0 x)
    (g := fun x => t*Real.exp (t*x)) (ae_of_all _ fun x => mul_nonneg ht.le (Real.exp_pos _).le)
  simp_rw [hprim] at hlayer
  have hi : IntegrableOn (fun x : ℝ => D*t*Real.exp (-t*x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ht) 0).const_mul (D*t)
  have hint : (∫ x in Ioi 0, D*t*Real.exp (-t*x))=D := by
    rw [integral_const_mul,integral_exp_mul_Ioi (neg_lt_zero.mpr ht)]
    simp only [mul_zero,Real.exp_zero]
    field_simp
  have hbound : (∫⁻ x in Ioi 0, μ {ω | x<X ω} * ENNReal.ofReal (t*Real.exp (t*x))) ≤ ENNReal.ofReal D := by
    calc
      _ ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal (D*t*Real.exp (-t*x)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        calc
          _ ≤ ENNReal.ofReal (D*Real.exp (-2*t*x))*ENNReal.ofReal (t*Real.exp (t*x)) :=
            by gcongr; exact htail x hx.le
          _ = ENNReal.ofReal (D*t*Real.exp (-t*x)) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg hD (Real.exp_pos _).le)]
            congr 1
            calc
              _ = D*t*(Real.exp (-2*t*x)*Real.exp (t*x)) := by ring
              _ = _ := by rw [← Real.exp_add]; congr 2; ring
      _ = ENNReal.ofReal D := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by positivity),hint]
  have hnon : ∀ ω, 0≤Real.exp (t*X ω)-1 := fun ω => sub_nonneg.mpr
    (Real.one_le_exp_iff.mpr (mul_nonneg ht.le (hX0 ω)))
  have hId := ofReal_integral_eq_lintegral_ofReal (f := fun ω => Real.exp (t*X ω)-1)
    (hE.sub (integrable_const 1)) (ae_of_all _ hnon)
  rw [← hId] at hlayer
  have hh : (∫ ω, Real.exp (t*X ω)-1 ∂μ)≤D :=
    (ENNReal.ofReal_le_ofReal_iff hD).mp (hlayer.trans_le hbound)
  rw [integral_sub hE (integrable_const 1),integral_const] at hh
  simpa using (show (∫ ω, Real.exp (t*X ω) ∂μ)≤1+D by simpa [add_comm] using (sub_le_iff_le_add.mp hh))

end DirectionalTransience

end

section

open Filter
open scoped Topology
namespace DirectionalTransience

lemma exp_le_half_exp {u v : ℝ} (h : u+Real.log 2≤v) :
    Real.exp u≤Real.exp v/2 := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ)<2)]
  calc
    Real.exp u*2 = Real.exp (u+Real.log 2) := by rw [Real.exp_add,Real.exp_log (by norm_num)]
    _ ≤ Real.exp v := Real.exp_le_exp.mpr h

lemma late_step_tail_arithmetic (lam C θ K : ℝ) (hlam : 0<lam) (hC : 0≤C)
    (hθ : 0<θ) (hK : 0≤K) :
    ∃ C₀ : ℝ, 0<C₀ ∧ ∀ (k : ℕ), 1≤k → ∀ a : ℝ, 1≤a →
      ∀ D : ℕ → ℝ, (∀ L, 0≤D L) → ∃ l₀ : ℕ,
      ∀ l≥l₀, ∀ T : ℝ → ℝ, (∀ x, T x≤1) →
        (∀ L : ℕ, 1≤L → ∀ x : ℝ, (k:ℝ)*L*K≤x → x≤a*(l+1) →
          T x≤(Real.exp (C*k-lam*x/L)+D L*Real.exp (x/L-θ*l))^L) →
        (∀ x : ℝ, 0≤x → x≤a*(l+1) → T x≤Real.exp (C₀*k-lam*x/2)) ∧
        T (a*(l+1))≤Real.exp (-lam*(a*(l+1))/2) := by
  let C₀ := C+lam*K+2
  have hC₀ : 0<C₀ := by dsimp [C₀] <;> positivity
  refine ⟨C₀,hC₀,?_⟩
  intro k hk a ha D hD
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hk0 : 0≤(k:ℝ) := Nat.cast_nonneg k
  have ha0 : 0<a := by linarith
  let c := min (1/2:ℝ) (θ/(4*(1+lam)))
  have hc : 0 < c := lt_min (by norm_num) (div_pos hθ (by positivity))
  have hc1 : c≤1/2 := min_le_left _ _
  have hcθ : (1+lam)*c≤θ/4 := by
    have hh := min_le_right (1/2:ℝ) (θ/(4*(1+lam)))
    have hh' := (le_div_iff₀ (show 0<4*(1+lam) by positivity)).mp hh
    dsimp [c]
    nlinarith only [hh']
  obtain ⟨L,hL⟩ := exists_nat_gt (max 1 (4*(1+lam)*a/θ))
  have hL1 : 1≤L := by have := (le_max_left 1 (4*(1+lam)*a/θ)).trans_lt hL; exact_mod_cast this.le
  have hL0 : 0<(L:ℝ) := by exact_mod_cast (by omega : 0<L)
  have hθL : 4*(1+lam)*a<θ*L := by
    have hh := (le_max_right 1 (4*(1+lam)*a/θ)).trans_lt hL
    exact (div_lt_iff₀ hθ).mp hh |>.trans_eq (mul_comm _ _)
  let D₁ := max (D 1) 1
  let D₂ := max (D L) 1
  have hD₁ : 0<D₁ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hD₂ : 0<D₂ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let R := max 1 (max (2*Real.log D₁/θ)
    (max (2*L*(C*k+Real.log 2)/(lam*c))
      (max ((k:ℝ)*L*K/c) (2*Real.log (2*D₂)/θ))))
  obtain ⟨l₀,hl₀⟩ := exists_nat_gt R
  refine ⟨l₀,?_⟩
  intro l hl T hT htail
  have hlR : R≤(l:ℝ) := hl₀.le.trans (by exact_mod_cast hl)
  have hl1 : (1:ℝ)≤l := (le_max_left _ _).trans hlR
  have hl0 : 0≤(l:ℝ) := Nat.cast_nonneg l
  have hR₂ : max (2*Real.log D₁/θ)
      (max (2*L*(C*k+Real.log 2)/(lam*c))
        (max ((k:ℝ)*L*K/c) (2*Real.log (2*D₂)/θ)))≤(l:ℝ) := (le_max_right _ _).trans hlR
  have hlog₁ : Real.log D₁≤θ*l/2 := by
    have hh := (div_le_iff₀ hθ).mp ((le_max_left _ _).trans hR₂)
    nlinarith only [hh]
  have hR₃ := (le_max_right _ _).trans hR₂
  have hfirst : 2*L*(C*k+Real.log 2)≤lam*c*l := by
    have hh := (div_le_iff₀ (mul_pos hlam hc)).mp ((le_max_left _ _).trans hR₃)
    nlinarith only [hh]
  have hR₄ := (le_max_right _ _).trans hR₃
  have hell : (k:ℝ)*L*K ≤ c*l := by
    have hh := (div_le_iff₀ hc).mp ((le_max_left _ _).trans hR₄)
    nlinarith only [hh]
  have hlog₂ : Real.log (2*D₂)≤θ*l/2 := by
    have hh := (div_le_iff₀ hθ).mp ((le_max_right _ _).trans hR₄)
    nlinarith only [hh]
  have hlarge (x : ℝ) (hxc : c*l≤x) (hxa : x≤a*(l+1)) :
      T x≤Real.exp (-lam*x/2) := by
    have hx0 : 0≤x := (mul_nonneg hc.le hl0).trans hxc
    have hbound := htail L hL1 x (hell.trans hxc) hxa
    have hab : Real.exp (C*k-lam*x/L)≤Real.exp (-lam*x/(2*L))/2 := by
      apply exp_le_half_exp
      have hfh : 2*L*(C*k+Real.log 2)≤lam*x := hfirst.trans
        (by nlinarith only [mul_le_mul_of_nonneg_left hxc hlam.le])
      have hf : C*k+Real.log 2≤lam*x/(2*L) :=
        (le_div_iff₀ (mul_pos (by norm_num) hL0)).mpr (by nlinarith only [hfh])
      have hid : lam*x/L=2*(lam*x/(2*L)) := by field_simp
      rw [hid]
      ring_nf at hf ⊢
      linarith only [hf]
    have hfrac : (1+lam/2)*x/L≤θ*l/2 := by
      apply (div_le_iff₀ hL0).mpr
      have hx2 : x≤2*a*l := by nlinarith only [hxa,mul_le_mul_of_nonneg_left hl1 ha0.le]
      have hml := mul_le_mul_of_nonneg_left hx2 (show 0≤1+lam/2 by positivity)
      have hθL' : 4*(1+lam/2)*a≤θ*L := by nlinarith only [hθL,mul_nonneg hlam.le ha0.le]
      have hh := mul_le_mul_of_nonneg_right hθL' hl0
      nlinarith only [hml,hh]
    have hbb : D L*Real.exp (x/L-θ*l)≤Real.exp (-lam*x/(2*L))/2 := by
      calc
        _ ≤ D₂*Real.exp (x/L-θ*l) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
        _ = Real.exp (Real.log D₂+x/L-θ*l) := by simp only [Real.exp_sub,Real.exp_add,Real.exp_log hD₂] <;> ring
        _ ≤ _ := by
          apply exp_le_half_exp
          have hh : Real.log D₂+Real.log 2≤θ*l/2 := by
            rw [← Real.log_mul (ne_of_gt hD₂) (by norm_num),mul_comm]
            exact hlog₂
          have : Real.log D₂+Real.log 2+(1+lam/2)*x/L≤θ*l := by linarith only [hh,hfrac]
          have hid : -lam*x/(2*L)= -(lam/2)*x/L := by ring
          rw [hid]
          ring_nf at this ⊢
          linarith only [this]
    calc
      T x ≤ (Real.exp (C*k-lam*x/L)+D L*Real.exp (x/L-θ*l))^L := hbound
      _ ≤ (Real.exp (-lam*x/(2*L)))^L := by
        apply pow_le_pow_left₀ (add_nonneg (Real.exp_pos _).le (mul_nonneg (hD L) (Real.exp_pos _).le))
        linarith only [hab,hbb]
      _ = Real.exp (-lam*x/2) := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  constructor
  · intro x hx0 hxa
    by_cases hxc : c*l≤x
    · exact (hlarge x hxc hxa).trans (Real.exp_le_exp.mpr (by linarith only [mul_nonneg hC₀.le hk0]))
    · by_cases hell1 : (k:ℝ)*K≤x
      · have hh := htail 1 (by omega) x (by simpa using hell1) hxa
        simp only [Nat.cast_one,div_one,pow_one] at hh
        have hb : D 1*Real.exp (x-θ*l)≤Real.exp (-lam*x) := by
          calc
            _ ≤ D₁*Real.exp (x-θ*l) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
            _ = Real.exp (Real.log D₁+x-θ*l) := by simp only [Real.exp_sub,Real.exp_add,Real.exp_log hD₁] <;> ring
            _ ≤ _ := by
              apply Real.exp_le_exp.mpr
              have hh := mul_le_mul_of_nonneg_left (not_le.mp hxc).le (show 0≤1+lam by positivity)
              have hh' := mul_le_mul_of_nonneg_right hcθ hl0
              nlinarith only [hh,hh',hlog₁,mul_nonneg hθ.le hl0]
        have hcpos : 0≤C*k := mul_nonneg hC hk0
        calc
          T x ≤ 2*Real.exp (C*k-lam*x) := by
            have he := Real.exp_le_exp.mpr (show -lam*x≤C*k-lam*x by linarith only [hcpos])
            linarith only [hh,hb,he]
          _ = Real.exp (Real.log 2+C*k-lam*x) := by simp only [Real.exp_sub,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)] <;> ring
          _ ≤ Real.exp (C₀*k-lam*x/2) := by
            apply Real.exp_le_exp.mpr
            have hlog2 : Real.log 2≤1 := by
              convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2) using 1
              all_goals try with_reducible_and_instances rfl
              norm_num
            dsimp [C₀]
            have hm := mul_nonneg (mul_nonneg hlam.le hK) hk0
            nlinarith only [hlog2,hk1,hm,mul_nonneg hlam.le hx0]
      · apply (hT x).trans
        apply Real.one_le_exp_iff.mpr
        have hxk := not_le.mp hell1
        dsimp [C₀]
        have hm₁ := mul_le_mul_of_nonneg_left hxk.le hlam.le
        have hm₂ := mul_nonneg hC hk0
        have hm₃ := mul_nonneg (mul_nonneg hlam.le hK) hk0
        nlinarith only [hm₁,hm₂,hm₃,hk1]
  · apply hlarge
    · nlinarith only [ha,hl0,mul_le_mul_of_nonneg_right ha hl0,mul_le_mul_of_nonneg_right hc1 hl0]
    · exact le_rfl

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_FreshMoment
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma independent_random_moment_bound {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → A) (V : Ω → B) (hU : Measurable U) (hV : Measurable V)
    (hind : IndepFun U V μ) (F : A × B → ℝ≥0∞) (hF : Measurable F)
    (w : A → ℝ≥0∞) (hw : Measurable w) (c : ℝ≥0∞)
    (hbound : ∀ a, (∫⁻ b, F (a,b) ∂μ.map V) ≤ c) :
    (∫⁻ ω, w (U ω)*F (U ω,V ω) ∂μ) ≤ c*(∫⁻ ω, w (U ω) ∂μ) := by
  have hG : Measurable (fun p : A×B => w p.1*F p) := (hw.comp measurable_fst).mul hF
  rw [← lintegral_map hG (hU.prodMk hV),
    hind.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable,
    lintegral_prod _ hG.aemeasurable]
  calc
    _ ≤ ∫⁻ a, w a*c ∂μ.map U := by
      apply lintegral_mono
      intro a
      change (∫⁻ b, w a*F (a,b) ∂μ.map V)≤w a*c
      have hFa : Measurable (fun b => F (a,b)) := hF.comp measurable_prodMk_left
      rw [lintegral_const_mul (w a) hFa]
      simpa only [mul_comm] using mul_le_mul_left (hbound a) (w a)
    _ = c*(∫⁻ ω, w (U ω) ∂μ) := by
      simp_rw [mul_comm (w _) c]
      rw [lintegral_const_mul c hw,lintegral_map hw hU]

lemma fresh_rows_moment_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (F : Environment d × Environment d → ℝ≥0∞)
    (hF : @Measurable _ _ (MeasurableSpace.prod (rowSigma S) (rowSigma T)) _ F)
    (w : Environment d → ℝ≥0∞) (hw : @Measurable _ _ (rowSigma S) _ w)
    (c : ℝ≥0∞) (hbound : ∀ η, (∫⁻ ω, F (η,ω) ∂environmentLaw ν) ≤ c) :
    (∫⁻ ω, w ω*F (ω,ω) ∂environmentLaw ν) ≤ c*(∫⁻ ω, w ω ∂environmentLaw ν) := by
  have hU : @Measurable (Environment d) (Environment d) inferInstance (rowSigma S) id :=
    measurable_id.mono le_rfl (rowSigma_le S)
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  have hb (η : Environment d) : (∫⁻ ω, F (η,ω) ∂
      @Measure.map (Environment d) (Environment d) inferInstance (rowSigma T) id (environmentLaw ν)) ≤ c := by
    have hm := @lintegral_map (Environment d) (Environment d) inferInstance (rowSigma T)
      (environmentLaw ν) (fun ω => F (η,ω)) id (hF.comp measurable_prodMk_left) hV
    rw [hm]
    exact hbound η
  exact @independent_random_moment_bound (Environment d) (Environment d) (Environment d)
    inferInstance (rowSigma S) (rowSigma T) (environmentLaw ν) inferInstance
    id id hU hV
    (@indepFun_of_disjoint_rows d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
      ν _ S T hST id id measurable_id measurable_id) F hF w hw c hb

lemma fresh_budget_capped_moment {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (base G : ℝ) (H : ℕ) (b a t : ℝ)
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (hstrip : ∀ x, dot (realPosition x) (realPosition (step e))=base →
      Strip (realPosition (step e)) x H ⊆ T)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (hπ : @Measurable _ _ (rowSigma S) _ π)
    (w : Environment d → ℝ≥0∞) (hw : @Measurable _ _ (rowSigma S) _ w)
    (c : ℝ≥0∞)
    (hb : ∀ p : BudgetProfile (k:=k) e f base G,
      (∫⁻ ω, ENNReal.ofReal (Real.exp (t*cappedLogLoss a
        (relativeBudgetMass e f H b p.val ω))) ∂environmentLaw ν) ≤ c) :
    (∫⁻ ω, w ω*ENNReal.ofReal (Real.exp (t*cappedLogLoss a
      (relativeBudgetMass e f H b (π ω).val ω))) ∂environmentLaw ν)≤
      c*(∫⁻ ω, w ω ∂environmentLaw ν) := by
  let F := fun p : Environment d×Environment d => ENNReal.ofReal
    (Real.exp (t*cappedLogLoss a (relativeBudgetMass e f H b (π p.1).val p.2)))
  have hQ : @Measurable _ _ (MeasurableSpace.prod (rowSigma S) (rowSigma T)) _
      (fun p : Environment d×Environment d => relativeBudgetMass e f H b (π p.1).val p.2) :=
    (budgetProfileMass_joint_rows e f base G H b T (fun x hx j => hstrip (x j) (hx j))).comp
      ((hπ.comp measurable_fst).prodMk measurable_snd)
  have hF : @Measurable _ _ (MeasurableSpace.prod (rowSigma S) (rowSigma T)) _ F :=
    (Real.measurable_exp.comp ((@measurable_cappedLogLoss (Environment d×Environment d)
      (MeasurableSpace.prod (rowSigma S) (rowSigma T)) a _ hQ).const_mul t)).ennreal_ofReal
  exact fresh_rows_moment_bound ν hST F hF w hw c (fun η => hb (π η))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetAlgebra
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurable_relativeBudgetMass_fixed {d k : ℕ} (e f : Direction d)
    (base G : ℝ) (H : ℕ) (b : ℝ) (π : BudgetProfile (k:=k) e f base G) :
    Measurable (fun ω => relativeBudgetMass e f H b π.val ω) := by
  have hm : @Measurable _ _ (rowSigma Set.univ) _
      (fun ω => relativeBudgetMass e f H b π.val ω) :=
    (budgetProfileMass_joint_rows e f base G H b Set.univ
      (fun _ _ _ => Set.subset_univ _)).comp (measurable_const.prodMk measurable_id)
  exact hm.mono (rowSigma_le _) le_rfl

lemma relativeBudgetMass_bounds {d k : ℕ} (e f : Direction d) (H : ℕ) (b : ℝ)
    (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    0 ≤ relativeBudgetMass e f H b π ω ∧ relativeBudgetMass e f H b π ω≤1 := by
  rw [← relativeBudgetMassENN_toReal]
  exact ⟨ENNReal.toReal_nonneg,by
    have := ENNReal.toReal_mono (by norm_num : (1:ℝ≥0∞)≠∞) (relativeBudgetMassENN_le_one e f H b π ω)
    simpa using this⟩

lemma relativeBudgetMass_lt_exp {d k : ℕ} (e f : Direction d) (H : ℕ) (b x : ℝ)
    (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    relativeBudgetMass e f H b π ω<Real.exp (-x) ↔
      relativeBudgetMassENN e f H b π ω<ENNReal.ofReal (Real.exp (-x)) := by
  rw [← relativeBudgetMassENN_toReal]
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos (-x)).le] using
    (ENNReal.toReal_lt_toReal (ne_top_of_le_ne_top (by norm_num)
      (relativeBudgetMassENN_le_one e f H b π ω))
      (ENNReal.ofReal_ne_top (r := Real.exp (-x))))

theorem actual_late_step_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) (θ : ℝ) (hθ : 0<θ) :
    ∃ lam Cmg : ℝ, 0<lam ∧ lam≤1 ∧ 0<Cmg ∧
      ∀ (k : ℕ), 2≤k → ∀ a : ℝ, 1≤a → ∀ D : ℕ → ℝ, (∀ L, 0≤D L) →
      ∃ l₀ : ℕ, ∀ Bstar : ℝ, 0<Bstar → ∃ Gzero : ℕ,
      ∀ l≥l₀, a*(l+1)≤Bstar → ∀ (H : ℕ) (base G b : ℝ),
        0<b → b≤G/2 → (Gzero:ℝ)≤G-b →
        (∀ L : ℕ, 1≤L → (H:ℝ)/fluctuationScale
          (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (b/(2*L)) ≤
            D L*Real.exp (-θ*l)) →
        ∀ π : BudgetProfile (k:=k) e f base G,
          (∫ ω, Real.exp ((lam/4)*cappedLogLoss (a*(l+1))
            (relativeBudgetMass e f H b π.val ω)) ∂environmentLaw ν) ≤Real.exp (Cmg*k) ∧
          (environmentLaw ν).real {ω | relativeBudgetMassENN e f H b π.val ω<
            ENNReal.ofReal (Real.exp (-(a*(l+1))))}≤Real.exp (-lam*(a*(l+1))/2) := by
  obtain ⟨κ,lam,C,hκ,hrows,hlam,hlam1,hC,hloss⟩ := rapid_loss_probability ν hue e f hef htrans
  have hκ0 : 0<(κ:ℝ) := hκ
  have hκ1 : (κ:ℝ)≤1 := by
    obtain ⟨p,hp⟩ := hrows.exists
    exact_mod_cast (hp e).trans (row_entry_le_one p e)
  let K := Real.log (1/(κ:ℝ))
  have hK : 0≤K := Real.log_nonneg ((one_le_div hκ0).mpr hκ1)
  obtain ⟨C₀,hC₀,harith⟩ := late_step_tail_arithmetic lam C θ K hlam hC.le hθ hK
  refine ⟨lam,C₀+1,hlam,hlam1,by positivity,?_⟩
  intro k hk a ha D hD
  have hk1 : 1≤k := by omega
  have hk1r : (1:ℝ)≤k := by exact_mod_cast hk1
  let D' := fun L => C*k*D L
  have hD' : ∀ L, 0≤D' L := fun L => mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg k)) (hD L)
  obtain ⟨l₀,hl₀⟩ := harith k hk1 a ha D' hD'
  refine ⟨l₀,fun Bstar hB => ?_⟩
  obtain ⟨Gzero,hGzero⟩ := hloss Bstar hB k hk1
  refine ⟨Gzero,?_⟩
  intro l hl hcap H base G b hb hhalf hG hratio π
  let T := fun x => (environmentLaw ν).real {ω | relativeBudgetMassENN e f H b π.val ω<ENNReal.ofReal (Real.exp (-x))}
  have hT : ∀ x, T x≤1 := fun x => by
    exact measureReal_le_one
  have htail (L : ℕ) (hL : 1≤L) (x : ℝ) (hx : (k:ℝ)*L*K≤x) (hxa : x≤a*(l+1)) :
      T x≤(Real.exp (C*k-lam*x/L)+D' L*Real.exp (x/L-θ*l))^L := by
    apply (hGzero L H base G b x hL hb hhalf hG hx (hxa.trans hcap) π).trans
    have hn := fluctuationScale_nonneg
      (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (b/(2*L))
    apply pow_le_pow_left₀ (by positivity)
    apply add_le_add_right
    calc
      C*k*Real.exp (x/L)*H/fluctuationScale
          (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (b/(2*L)) =
          (C*k*Real.exp (x/L))*((H:ℝ)/fluctuationScale
            (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) (b/(2*L))) := by ring
      _ ≤ (C*k*Real.exp (x/L))*(D L*Real.exp (-θ*l)) :=
        mul_le_mul_of_nonneg_left (hratio L hL) (by positivity)
      _ = D' L*Real.exp (x/L-θ*l) := by dsimp [D']; rw [sub_eq_add_neg,Real.exp_add]; ring_nf
  obtain ⟨hsmall,hlarge⟩ := hl₀ l hl T hT htail
  refine ⟨?_,hlarge⟩
  let q := fun ω => relativeBudgetMass e f H b π.val ω
  let X := fun ω => cappedLogLoss (a*(l+1)) (q ω)
  have hq : Measurable q := measurable_relativeBudgetMass_fixed e f base G H b π
  have hqa : ∀ ω, 0≤q ω ∧ q ω≤1 := relativeBudgetMass_bounds e f H b π.val
  have hcap0 : 0≤a*(l+1) := mul_nonneg (by linarith only [ha]) (by positivity)
  have hX : Measurable X := measurable_cappedLogLoss _ q hq
  have hX0 : ∀ ω, 0≤X ω := fun ω => (cappedLogLoss_bounds hcap0 (hqa ω).1 (hqa ω).2).1
  have hXa : ∀ ω, X ω≤a*(l+1) := fun ω => (cappedLogLoss_bounds hcap0 (hqa ω).1 (hqa ω).2).2
  have hbound (x : ℝ) (hx : 0≤x) : environmentLaw ν {ω | x<X ω}≤
      ENNReal.ofReal (Real.exp (C₀*k)*Real.exp (-2*(lam/4)*x)) := by
    by_cases hxc : x<a*(l+1)
    · have he : {ω | x<X ω}={ω | relativeBudgetMassENN e f H b π.val ω<ENNReal.ofReal (Real.exp (-x))} := by
        ext ω
        change x < cappedLogLoss _ (q ω) ↔ _
        rw [lt_cappedLogLoss_iff (hqa ω).1 hx,and_iff_right hxc]
        exact relativeBudgetMass_lt_exp e f H b x π.val ω
      rw [he]
      apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
      apply (hsmall x hx hxc.le).trans
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      ring_nf
      exact le_rfl
    · have he : {ω | x<X ω}=∅ := Set.eq_empty_iff_forall_notMem.mpr
        (fun ω hω => (not_lt_of_ge ((hXa ω).trans (not_lt.mp hxc))) hω)
      rw [he,measure_empty]
      exact bot_le
  have hm := exp_moment_of_tail (environmentLaw ν) X hX hX0 (a*(l+1)) hXa
    (lam/4) (Real.exp (C₀*k)) (by positivity) (Real.exp_pos _).le hbound
  apply hm.trans
  calc
    1+Real.exp (C₀*k) ≤ 2*Real.exp (C₀*k) := by
      have hh := Real.one_le_exp_iff.mpr (mul_nonneg hC₀.le (Nat.cast_nonneg k))
      linarith only [hh]
    _ ≤ Real.exp ((C₀+1)*k) := by
      have he : (2:ℝ)≤Real.exp (k:ℝ) := by
        have hh := Real.add_one_le_exp (k:ℝ)
        linarith only [hh,hk1r]
      calc
        _ ≤ Real.exp (k:ℝ)*Real.exp (C₀*k) := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProtectionLoss
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace DirectionalTransience

lemma cappedLogLoss_eq_neg_log {a q : ℝ} (ha : Real.exp (-a)≤q) :
    cappedLogLoss a q= -Real.log q := by
  have hq : 0<q := (Real.exp_pos _).trans_le ha
  have hlog := Real.log_le_log (Real.exp_pos _) ha
  rw [Real.log_exp] at hlog
  simp only [cappedLogLoss,ite_eq_right hq.ne',min_eq_right (by linarith : -Real.log q≤a)]

lemma exp_neg_cappedLogLoss {a q : ℝ} (hq : 0≤q) :
    Real.exp (-cappedLogLoss a q)=max (Real.exp (-a)) q := by
  by_cases h : Real.exp (-a)≤q
  · rw [cappedLogLoss_eq_neg_log h,neg_neg,Real.exp_log ((Real.exp_pos _).trans_le h),max_eq_right h]
  · have hlt : q<Real.exp (-a) := not_le.mp h
    have hcap : cappedLogLoss a q=a := by
      unfold cappedLogLoss
      by_cases hz : q=0
      · simp [hz]
      · rw [ite_eq_right hz,min_eq_left]
        have hlog := Real.log_le_log (lt_of_le_of_ne hq (Ne.symm hz)) hlt.le
        rw [Real.log_exp] at hlog
        linarith
    rw [hcap,max_eq_left hlt.le]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma protectionGap_eq (G : ℝ) (r : ℕ → ℝ) (n : ℕ) :
    protectionGap G r n=G-∑ i∈Finset.range n, r i := by
  induction n with
  | zero => simp [protectionGap]
  | succ n ih => simp [protectionGap,ih,Finset.sum_range_succ,sub_sub]

lemma protectionProfile_measurable {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) base)) _ π) (n : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e))
      (protectionHeight base H n))) _ (protectionProfile e f base G H r hr π n) := by
  induction n with
  | zero => exact hπ
  | succ n ih => exact nextBudgetProfile_measurable_below e f _ _ _ (hr n) (H n) _ ih

lemma protectionMass_measurable {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) base)) _ π) (n : ℕ) :
    Measurable[protectionFiltration e base H (n+1)] (protectionMass e f base G H r hr π n) := by
  have hpm := protectionProfile_measurable e f base G H r hr π hπ n
  apply (budgetProfileMass_joint_rows e f _ _ (H n) (r n)
    (BelowHeight (realPosition (step e)) (protectionHeight base H (n+1))) ?_).comp
      ((hpm.mono ((protectionFiltration e base H).mono (Nat.le_succ n)) le_rfl).prodMk measurable_id)
  intro x hx j y hy
  change dot (realPosition y) (realPosition (step e)) < protectionHeight base H n+H n
  simpa only [hx j] using hy.2

lemma protectionMass_bounds {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) (n : ℕ) (ω : Environment d) :
    0≤protectionMass e f base G H r hr π n ω ∧ protectionMass e f base G H r hr π n ω≤1 :=
  relativeBudgetMass_bounds e f (H n) (r n) _ ω

lemma protection_capped_step {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (base G : ℝ) (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) base)) _ π)
    (a t : ℝ) (c : ℝ≥0∞) (n : ℕ)
    (hb : ∀ p : BudgetProfile (k:=k) e f (protectionHeight base H n) (protectionGap G r n),
      (∫⁻ ω, ENNReal.ofReal (Real.exp (t*cappedLogLoss a
        (relativeBudgetMass e f (H n) (r n) p.val ω))) ∂environmentLaw ν) ≤ c)
    (w : Environment d → ℝ≥0∞) (hw : Measurable[protectionFiltration e base H n] w) :
    (∫⁻ ω, w ω*ENNReal.ofReal (Real.exp (t*cappedLogLoss a
      (protectionMass e f base G H r hr π n ω))) ∂environmentLaw ν) ≤ c*(∫⁻ ω, w ω ∂environmentLaw ν) := by
  apply fresh_budget_capped_moment ν e f _ _ (H n) (r n) a t
    (S:=BelowHeight (realPosition (step e)) (protectionHeight base H n))
    (T:={y | protectionHeight base H n≤dot (realPosition y) (realPosition (step e))})
    ?_ ?_ _ (protectionProfile_measurable e f base G H r hr π hπ n) w hw c hb
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt.mpr (show protectionHeight base H n≤dot (realPosition x) (realPosition (step e)) from hy))
      (show dot (realPosition x) (realPosition (step e))<protectionHeight base H n from hx)
  · intro x hx y hy
    change protectionHeight base H n≤dot (realPosition y) (realPosition (step e))
    simpa only [hx] using hy.1

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RadixBudget
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma radix16_budget_ratio {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0<μ {x | S x≠0}) {ρ c C : ℝ} (hρ : 0<ρ) (hc : 0 < c) (hc1 : c≤1)
    (hC : 0≤C) (l L H : ℕ) (hL : 1≤L)
    (hH : (H:ℝ)≤3*C*fluctuationScale μ S ρ/(16:ℝ)^l) :
    (H:ℝ)/fluctuationScale μ S (((c/16)*ρ/(2:ℝ)^l)/(2*L)) ≤
      (3*C*(32*(L:ℝ)/c)^2)*Real.exp (-(Real.log 4)*l) := by
  have hL0 : (0:ℝ)<L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hL1 : (1:ℝ)≤L := by exact_mod_cast hL
  have h2 : (0:ℝ)<(2:ℝ)^l := by positivity
  have h16 : (0:ℝ)<(16:ℝ)^l := by positivity
  let r := c/(32*(L:ℝ)*(2:ℝ)^l)
  have hr : 0 < r := by dsimp [r] <;> positivity
  have hr1 : r≤1 := by
    dsimp [r]
    apply (div_le_one (by positivity)).mpr
    have hp : (1:ℝ)≤(2:ℝ)^l := one_le_pow₀ (by norm_num)
    have hprod : 1≤(L:ℝ)*(2:ℝ)^l := one_le_mul_of_one_le_of_one_le hL1 hp
    nlinarith only [hc1,hprod]
  have hn : 0<fluctuationScale μ S ρ := by
    exact div_pos (sq_pos_of_pos hρ) (truncatedVariance_pos μ S hS hne hρ)
  have hn' : 0<fluctuationScale μ S (r*ρ) := by
    exact div_pos (sq_pos_of_pos (mul_pos hr hρ))
      (truncatedVariance_pos μ S hS hne (mul_pos hr hρ))
  have hscale := fluctuationScale_scaling μ S hS hne hρ hr hr1
  have heq : ((c/16)*ρ/(2:ℝ)^l)/(2*L)=r*ρ := by dsimp [r]; field_simp <;> ring
  rw [heq]
  calc
    (H:ℝ)/fluctuationScale μ S (r*ρ) ≤
        (3*C*fluctuationScale μ S ρ/(16:ℝ)^l)/(r^2*fluctuationScale μ S ρ) :=
      div_le_div₀ (by positivity) hH (by positivity) hscale
    _ = (3*C*(32*(L:ℝ)/c)^2) / (4:ℝ)^l := by
      have hp : ((2:ℝ)^l)^2*(4:ℝ)^l=(16:ℝ)^l := by
        rw [← pow_mul, mul_comm l 2, pow_mul, ← mul_pow]; norm_num
      dsimp [r]
      field_simp
      nlinarith only [congrArg (fun x : ℝ => C*x) hp]
    _ = _ := by
      rw [neg_mul,Real.exp_neg,mul_comm (Real.log 4) (l:ℝ),Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<4)]
      ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma adapted_weighted_product_moment {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m)
    (X : ℕ → Ω → ℝ≥0∞) (hX : ∀ n, Measurable[ℱ (n+1)] (X n))
    (W : Ω → ℝ≥0∞) (hW : Measurable[ℱ 0] W) (c : ℝ≥0∞) (N : ℕ)
    (hstep : ∀ n<N, ∀ w : Ω → ℝ≥0∞, Measurable[ℱ n] w →
      (∫⁻ ω, w ω*X n ω ∂μ) ≤ c*(∫⁻ ω, w ω ∂μ)) :
    (∫⁻ ω, W ω*∏ i∈Finset.range N, X i ω ∂μ) ≤ c^N*(∫⁻ ω, W ω ∂μ) := by
  have hm (n : ℕ) : Measurable[ℱ n] (fun ω => W ω*∏ i∈Finset.range n, X i ω) := by
    apply (hW.mono (ℱ.mono (Nat.zero_le n)) le_rfl).mul
    apply Finset.measurable_fun_prod
    intro i hi
    exact (hX i).mono (ℱ.mono (by simpa using hi)) le_rfl
  induction N with
  | zero => simp
  | succ N ih =>
    simp_rw [Finset.prod_range_succ,← mul_assoc]
    apply (hstep N (Nat.lt_succ_self N) _ (hm N)).trans
    have hh := mul_le_mul_left (ih (fun n hn => hstep n (Nat.lt_trans hn (Nat.lt_succ_self N)))) c
    simpa [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh

lemma adapted_weighted_exp_sum_tail {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m)
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable[ℱ (n+1)] (X n))
    (W : Ω → ℝ≥0∞) (hW : Measurable[ℱ 0] W)
    (t C : ℝ) (ht : 0<t) (N : ℕ)
    (hstep : ∀ n<N, ∀ w : Ω → ℝ≥0∞, Measurable[ℱ n] w →
      (∫⁻ ω, w ω*ENNReal.ofReal (Real.exp (t*X n ω)) ∂μ)≤
        ENNReal.ofReal (Real.exp C)*(∫⁻ ω, w ω ∂μ)) (v : ℝ) :
    μ.withDensity W {ω | v≤∑ i∈Finset.range N, X i ω}≤
      ENNReal.ofReal (Real.exp (C*N-t*v))*(∫⁻ ω, W ω ∂μ) := by
  let Y := fun i ω => ENNReal.ofReal (Real.exp (t*X i ω))
  have hY (i : ℕ) : Measurable[ℱ (i+1)] (Y i) := ((hX i).const_mul t).exp.ennreal_ofReal
  have hprod := adapted_weighted_product_moment μ ℱ Y hY W hW (ENNReal.ofReal (Real.exp C)) N hstep
  have hsum : Measurable (fun ω => ∑ i∈Finset.range N, X i ω) :=
    Finset.measurable_fun_sum _ (fun i _ => (hX i).mono (ℱ.le _) le_rfl)
  have hid (ω : Ω) : (∏ i∈Finset.range N, Y i ω)=
      ENNReal.ofReal (Real.exp (t*∑ i∈Finset.range N, X i ω)) := by
    simp only [Y,← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos (t*X i ω)).le),
      ← Real.exp_sum,Finset.mul_sum]
  simp_rw [hid] at hprod
  have hmeas : Measurable (fun ω => ENNReal.ofReal (Real.exp (t*∑ i∈Finset.range N, X i ω))) :=
    (hsum.const_mul t).exp.ennreal_ofReal
  have he : {ω | v≤∑ i∈Finset.range N, X i ω} =
      {ω | ENNReal.ofReal (Real.exp (t*v))≤ENNReal.ofReal (Real.exp (t*∑ i∈Finset.range N, X i ω))} := by
    ext ω
    simp only [Set.mem_ofPred_eq,ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
      Real.exp_le_exp,mul_le_mul_iff_right₀ ht]
  rw [he]
  apply (meas_ge_le_lintegral_div (μ:=μ.withDensity W) hmeas.aemeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top).trans
  rw [lintegral_withDensity_eq_lintegral_mul μ (hW.mono (ℱ.le 0) le_rfl) hmeas]
  calc
    _ ≤ (ENNReal.ofReal (Real.exp C)^N*(∫⁻ ω, W ω ∂μ))/ENNReal.ofReal (Real.exp (t*v)) :=
      ENNReal.div_le_div_right hprod _
    _ = ENNReal.ofReal (Real.exp (C*N-t*v))*(∫⁻ ω, W ω ∂μ) := by
      rw [ENNReal.mul_div_right_comm,← ENNReal.ofReal_pow (Real.exp_pos C).le,
        ← ENNReal.ofReal_div_of_pos (Real.exp_pos _),← Real.exp_nat_mul,← Real.exp_sub]
      congr 2
      ring_nf

end DirectionalTransience

end

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

lemma fixed_budget_momentENN {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (base G : ℝ) (H : ℕ) (b a t C : ℝ)
    (ha : 0≤a) (ht : 0≤t) (π : BudgetProfile (k:=k) e f base G)
    (hb : (∫ ω, Real.exp (t*cappedLogLoss a (relativeBudgetMass e f H b π.val ω))
      ∂environmentLaw ν)≤Real.exp C) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (t*cappedLogLoss a (relativeBudgetMass e f H b π.val ω)))
      ∂environmentLaw ν)≤ENNReal.ofReal (Real.exp C) := by
  have hi := integrable_exp_cappedLogLoss (environmentLaw ν) a t ha ht _
    (measurable_relativeBudgetMass_fixed e f base G H b π)
    (fun ω => (relativeBudgetMass_bounds e f H b π.val ω).1)
    (fun ω => (relativeBudgetMass_bounds e f H b π.val ω).2)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal hb

theorem scheduled_late_step_bounds {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ lam Cmg : ℝ, 0<lam ∧ lam≤1 ∧ 0<Cmg ∧
      ∀ (k : ℕ), 2≤k → ∀ a : ℝ, 1≤a → ∀ c C : ℝ, 0 < c → c≤1 → 0<C →
      ∃ l₀ : ℕ, 0<l₀ ∧ ∀ Bstar : ℝ, 0<Bstar → ∃ R : ℝ, 0<R ∧
      ∀ ρ≥R, ∀ n : ℕ, a*(l₀+n+1)≤Bstar → ∀ H : ℕ,
        (H:ℝ)≤3*C*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) ρ/(16:ℝ)^(l₀+n) →
        ∀ base : ℝ, ∀ π : BudgetProfile (k:=k) e f base
          (protectionGap (3*c*ρ/4) (lateBudget c ρ l₀) n),
          (∫⁻ ω, ENNReal.ofReal (Real.exp ((lam/4)*cappedLogLoss (a*(l₀+n+1))
            (relativeBudgetMass e f H (lateBudget c ρ l₀ n) π.val ω))) ∂environmentLaw ν)≤
              ENNReal.ofReal (Real.exp (Cmg*k)) ∧
          environmentLaw ν {ω | relativeBudgetMass e f H (lateBudget c ρ l₀ n) π.val ω<
            Real.exp (-(a*(l₀+n+1)))}≤ENNReal.ofReal (Real.exp (-lam*(a*(l₀+n+1))/2)) := by
  obtain ⟨lam,Cmg,hlam,hlam1,hCmg,hh⟩ := actual_late_step_moment ν hue e f hef htrans (Real.log 4)
    (Real.log_pos (by norm_num))
  refine ⟨lam,Cmg,hlam,hlam1,hCmg,?_⟩
  intro k hk a ha c C hc hc1 hC
  let D := fun L : ℕ => 3*C*(32*(L:ℝ)/c)^2
  obtain ⟨lmin,hl₀⟩ := hh k hk a ha D (fun L => by dsimp [D] <;> positivity)
  let l₀ := lmin+1
  refine ⟨l₀,by dsimp [l₀]; omega,fun Bstar hB => ?_⟩
  obtain ⟨Gzero,hGzero⟩ := hl₀ Bstar hB
  refine ⟨max 1 (2*Gzero/c),lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro ρ hρR n hn H hH base π
  have hρ : 0<ρ := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hρR)
  have hG : (Gzero:ℝ) ≤ c*ρ/2 := by
    have hh := (le_max_right 1 (2*Gzero/c)).trans hρR
    have hh' := (div_le_iff₀ hc).mp hh
    nlinarith only [hh']
  let μ := independentConditionedPairLaw ν (realPosition (step e))
  let S := commonIncrementProcess (realPosition (step e)) f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν _
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
  have hS : Measurable S := measurable_commonIncrementProcess _ _ _
  have hne : 0<μ {x | S x≠0} := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hgaps := lateBudget_gaps hc hρ l₀ n
  have hcap : a*((l₀+n:ℕ)+1)≤Bstar := by exact_mod_cast hn
  have hb := hGzero (l₀+n) (by dsimp [l₀]; omega) hcap H base _ _
    (lateBudget_pos hc hρ l₀ n) hgaps.1 (hG.trans hgaps.2)
    (fun L hL => radix16_budget_ratio μ S hS hne hρ hc hc1 hC.le (l₀+n) L H hL hH) π
  constructor
  · apply fixed_budget_momentENN ν e f base _ H _ _ _ _ (by positivity) (by positivity) π
    simpa only [Nat.cast_add,Nat.cast_one] using hb.1
  · have he : {ω | relativeBudgetMass e f H (lateBudget c ρ l₀ n) π.val ω<Real.exp (-(a*(l₀+n+1)))}=
        {ω | relativeBudgetMassENN e f H (lateBudget c ρ l₀ n) π.val ω<ENNReal.ofReal (Real.exp (-(a*(l₀+n+1))))} := by
      ext ω; exact relativeBudgetMass_lt_exp e f H _ _ π.val ω
    rw [he]
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr
    simpa only [Nat.cast_add,Nat.cast_one,Measure.real] using hb.2

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProtectionFirstFailure
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma first_protection_failure_split_offset (q : ℕ → ℝ) (kA : ℝ) (hkA : 0≤kA)
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ) (hq : ∀ i≤n, 0≤q i ∧ q i≤1)
    (hpass : ∀ j<n, Real.exp (-kA*(s+j+1))≤∏ i∈Finset.range (j+1), q i)
    (hfail : (∏ i∈Finset.range (n+1), q i)<Real.exp (-kA*(s+n+1))) :
    q n<Real.exp (-(2*kA*(s+n+1))) ∨
      kA*(s+n+1)<∑ i∈Finset.range (n+1), cappedLogLoss (2*kA*(s+i+1)) (q i) := by
  by_cases hnew : q n<Real.exp (-(2*kA*(s+n+1)))
  · exact Or.inl hnew
  apply Or.inr
  have hlow (i : ℕ) (hi : i≤n) : Real.exp (-(2*kA*(s+i+1)))≤q i := by
    by_cases hin : i=n
    · subst i; exact not_lt.mp hnew
    · have hit : i<n := lt_of_le_of_ne hi hin
      have hprod : (∏ j∈Finset.range (i+1), q j)≤q i := by
        have hh := Finset.prod_le_prod_of_subset_of_le_one
          (show {i}⊆Finset.range (i+1) by simp) (fun j hj => (hq j (by simp only [Finset.mem_range] at hj; omega)).1)
          (fun j hj _ => (hq j (by simp only [Finset.mem_range] at hj; omega)).2)
        simpa using hh
      apply le_trans _ ((hpass i hit).trans hprod)
      apply Real.exp_le_exp.mpr
      have hi0 : 0 ≤ s+(i:ℝ)+1 := by positivity
      nlinarith only [mul_nonneg hkA hi0]
  have hprod : (∏ i∈Finset.range (n+1), q i)=Real.exp
      (-(∑ i∈Finset.range (n+1), cappedLogLoss (2*kA*(s+i+1)) (q i))) := by
    rw [← Finset.sum_neg_distrib,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    rw [exp_neg_cappedLogLoss (hq i (by simpa using hi)).1,max_eq_right (hlow i (by simpa using hi))]
  rw [hprod,Real.exp_lt_exp] at hfail
  linarith only [hfail]

lemma firstProtectionFailure_bound {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (q : ℕ → Ω → ℝ)
    (hqm : ∀ i, Measurable[ℱ (i+1)] (q i)) (hq : ∀ i ω, 0≤q i ω ∧ q i ω≤1)
    (kA s : ℝ) (hkA : 0≤kA) (hs : 0 ≤ s) (t C : ℝ) (ht : 0<t) (n : ℕ)
    (hstep : ∀ i<n+1, ∀ w : Ω → ℝ≥0∞, Measurable[ℱ i] w →
      (∫⁻ ω, w ω*ENNReal.ofReal (Real.exp (t*cappedLogLoss (2*kA*(s+i+1)) (q i ω))) ∂μ)≤
        ENNReal.ofReal (Real.exp C)*(∫⁻ ω, w ω ∂μ))
    (cap : ℝ≥0∞) (hcap : ∀ A : Set Ω, MeasurableSet[ℱ n] A →
      μ (A∩{ω | q n ω<Real.exp (-(2*kA*(s+n+1)))}) ≤ cap*μ A)
    (A : Set Ω) (hA : MeasurableSet[ℱ 0] A) :
    μ (A∩firstProtectionFailure q kA s n)≤
      (cap+ENNReal.ofReal (Real.exp (C*(n+1)-t*(kA*(s+n+1)))))*μ A := by
  let X := fun (i : ℕ) ω => cappedLogLoss (2*kA*(s+i+1)) (q i ω)
  have hX : ∀ i, Measurable[ℱ (i+1)] (X i) := fun i =>
    @measurable_cappedLogLoss Ω (ℱ (i+1)) _ _ (hqm i)
  let E : Set Ω := {ω | kA*(s+n+1)≤∑ i∈Finset.range (n+1), X i ω}
  have hEm : MeasurableSet E := measurableSet_le measurable_const
    (Finset.measurable_fun_sum _ (fun i _ => (hX i).mono (ℱ.le _) le_rfl))
  have hAm : MeasurableSet A := ℱ.le 0 A hA
  have hW : Measurable[ℱ 0] (A.indicator (fun _ : Ω => (1:ℝ≥0∞))) := measurable_const.indicator hA
  have htail := adapted_weighted_exp_sum_tail μ ℱ X hX _ hW t C ht (n+1) hstep (kA*(s+n+1))
  have heq : μ.withDensity (A.indicator (fun _ : Ω => (1:ℝ≥0∞)))=μ.restrict A :=
    withDensity_indicator_one hAm
  rw [heq,Measure.restrict_apply hEm,lintegral_indicator hAm] at htail
  simp only [lintegral_const,one_mul,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Nat.cast_add,Nat.cast_one] at htail
  have hsub : A∩firstProtectionFailure q kA s n ⊆
      (A∩{ω | q n ω<Real.exp (-(2*kA*(s+n+1)))})∪(A∩E) := by
    rintro ω ⟨hω,hpass,hfail⟩
    rcases first_protection_failure_split_offset (fun i => q i ω) kA hkA s hs n
      (fun i _ => hq i ω) hpass hfail with h|h
    · exact Or.inl ⟨hω,h⟩
    · exact Or.inr ⟨hω,h.le⟩
  apply (measure_mono hsub).trans ((measure_union_le _ _).trans _)
  rw [add_mul]
  apply add_le_add (hcap A (ℱ.mono (Nat.zero_le n) A hA))
  simpa only [Set.inter_comm] using htail

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma protection_failure_exponents {lam Cmg A : ℝ} (hC : 0≤Cmg)
    (hA : Cmg+8≤(lam/4)*A) (k s n : ℕ) (hk : 1≤k) :
    Real.exp (-lam*((2*A*k)*((s:ℝ)+n+1))/2)+
      Real.exp ((Cmg*k)*((n:ℝ)+1)-(lam/4)*((A*k)*((s:ℝ)+n+1)))≤
        Real.exp (-5*k*((s:ℝ)+n+1)) := by
  let T : ℝ := s+n+1
  have hT : 1≤T := by dsimp [T] <;> linarith [Nat.cast_nonneg (α:=ℝ) s,Nat.cast_nonneg (α:=ℝ) n]
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hkT : 1≤(k:ℝ)*T := one_le_mul_of_one_le_of_one_le hk1 hT
  have hCpos : 0≤Cmg*k*T := by positivity
  have hah := mul_le_mul_of_nonneg_right hA (show 0≤(k:ℝ)*T by positivity)
  have hcap : -lam*((2*A*k)*T)/2≤-8*k*T := by nlinarith only [hah,hCpos,hkT]
  have hcount : Cmg*k*((n:ℝ)+1)≤Cmg*k*T := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    dsimp [T] <;> linarith [Nat.cast_nonneg (α:=ℝ) s]
  have hsum : (Cmg*k)*((n:ℝ)+1)-(lam/4)*((A*k)*T)≤-8*k*T := by
    nlinarith only [hah,hcount]
  have he : 2≤Real.exp (3*k*T) := by
    have hh := Real.add_one_le_exp (3*k*T)
    nlinarith only [hh,hkT]
  calc
    _ ≤ 2*Real.exp (-8*k*T) := by
      have h1 := Real.exp_le_exp.mpr hcap
      have h2 := Real.exp_le_exp.mpr hsum
      change Real.exp (-lam*((2*A*k)*T)/2)+Real.exp ((Cmg*k)*((n:ℝ)+1)-(lam/4)*((A*k)*T))≤_
      linarith only [h1,h2]
    _ ≤ Real.exp (3*k*T)*Real.exp (-8*k*T) := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [T] <;> ring

theorem actual_late_protection_first_failure_oai {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ lam Cmg : ℝ, 0<lam ∧ lam≤1 ∧ 0<Cmg ∧
      ∀ A : ℝ, 1≤A → Cmg+8≤(lam/4)*A → ∀ k : ℕ, 2≤k →
      ∀ (c C : ℝ) (hc : 0 < c), c≤1 → 0<C → ∃ l₀ : ℕ, 0<l₀ ∧
      ∀ Bstar : ℝ, 0<Bstar → ∃ R : ℝ, ∃ hR : 0<R,
      ∀ (ρ : ℝ) (hρR : R≤ρ), ∀ n : ℕ, (2*A*k)*(l₀+n+1)≤Bstar →
      ∀ H : ℕ → ℕ, (∀ i≤n, (H i:ℝ)≤3*C*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) ρ/(16:ℝ)^(l₀+i)) →
      ∀ base : ℝ, ∀ π : Environment d → BudgetProfile (k:=k) e f base (3*c*ρ/4),
      @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) base)) _ π →
      ∀ E : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) base)] E →
        environmentLaw ν (E∩firstProtectionFailure
          (protectionMass e f base (3*c*ρ/4) H (lateBudget c ρ l₀)
            (fun i => (lateBudget_pos hc (lt_of_lt_of_le hR hρR) l₀ i).le) π)
          (A*k) l₀ n)≤ENNReal.ofReal (Real.exp (-5*k*((l₀:ℝ)+n+1)))*environmentLaw ν E := by
  obtain ⟨lam,Cmg,hlam,hlam1,hCmg,hh⟩ := scheduled_late_step_bounds ν hue e f hef htrans
  refine ⟨lam,Cmg,hlam,hlam1,hCmg,?_⟩
  intro A hA hAchoice k hk c C hc hc1 hC
  have hk1 : 1≤k := by omega
  have hk1r : (1:ℝ)≤k := by exact_mod_cast hk1
  have hak : 1≤2*A*k := by nlinarith
  obtain ⟨l₀,hlpos,hl₀⟩ := hh k hk (2*A*k) hak c C hc hc1 hC
  refine ⟨l₀,hlpos,fun Bstar hB => ?_⟩
  obtain ⟨R,hR,hbound⟩ := hl₀ Bstar hB
  refine ⟨R,hR,?_⟩
  intro ρ hρR n hcap H hH base π hπ E hE
  have hρ := hR.trans_le hρR
  let r := lateBudget c ρ l₀
  let hr := fun i => (lateBudget_pos hc hρ l₀ i).le
  let q := protectionMass e f base (3*c*ρ/4) H r hr π
  let ℱ := protectionFiltration e base H
  have hqm : ∀ i, Measurable[ℱ (i+1)] (q i) := protectionMass_measurable e f base _ H r hr π hπ
  have hqb : ∀ i ω, 0≤q i ω ∧ q i ω≤1 := protectionMass_bounds e f base _ H r hr π
  have hiCap (i : ℕ) (hi : i≤n) : (2*A*k)*((l₀:ℝ)+i+1)≤Bstar := by
    apply le_trans _ hcap
    gcongr
  have hb (i : ℕ) (hi : i≤n) (p : BudgetProfile (k:=k) e f (protectionHeight base H i)
      (protectionGap (3*c*ρ/4) r i)) := hbound ρ hρR i (hiCap i hi) (H i) (hH i hi) _ p
  have hstep : ∀ i<n+1, ∀ w : Environment d → ℝ≥0∞, Measurable[ℱ i] w →
      (∫⁻ ω, w ω*ENNReal.ofReal (Real.exp ((lam/4)*cappedLogLoss (2*(A*k)*((l₀:ℝ)+i+1)) (q i ω))) ∂environmentLaw ν)≤
        ENNReal.ofReal (Real.exp (Cmg*k))*(∫⁻ ω, w ω ∂environmentLaw ν) := by
    intro i hi w hw
    apply protection_capped_step ν e f base _ H r hr π hπ _ (lam/4) _ i _ w hw
    intro p
    simpa only [r,mul_assoc] using (hb i (by omega) p).1
  have hcapbound : ∀ E : Set (Environment d), MeasurableSet[ℱ n] E →
      environmentLaw ν (E∩{ω | q n ω<Real.exp (-(2*(A*k)*((l₀:ℝ)+n+1)))})≤
        ENNReal.ofReal (Real.exp (-lam*((2*A*k)*((l₀:ℝ)+n+1))/2))*environmentLaw ν E := by
    intro E hE
    apply fresh_random_budget_mass_lt ν e f _ _ _ _ (H n) _
      (protectionProfile_measurable e f base _ H r hr π hπ n) E hE
    intro η hη
    simpa only [r,mul_assoc] using (hb n le_rfl (protectionProfile e f base _ H r hr π n η)).2
  have hfirst := firstProtectionFailure_bound (environmentLaw ν) ℱ q hqm hqb (A*k) l₀
    (by positivity) (Nat.cast_nonneg _) (lam/4) (Cmg*k) (by positivity) n hstep _ hcapbound E hE
  apply hfirst.trans
  apply mul_le_mul_left
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (protection_failure_exponents hCmg.le hAchoice k l₀ n hk1)

end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.actual_late_protection_first_failure_oai := @OAI.DirectionalTransience.actual_late_protection_first_failure_oai
