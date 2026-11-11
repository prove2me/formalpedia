-- Prove2me | solution 1 for OAI.DirectionalTransience.actual_expected_stages
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:55:20.685254+00:00
-- url     : https://prove2.me/submissions/7d5bbd73-c74d-4f79-b32e-5b0b964c53c0

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal006

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentRandomTestBound
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetNormalize
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma BudgetProfile.measurable_toSupported {d k : ℕ} (e f : Direction d) (a G : ℝ) :
    Measurable (BudgetProfile.toSupported (d:=d) (k:=k) (e:=e) (f:=f) (a:=a) (G:=G)) :=
  measurable_subtype_coe.subtype_mk

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_FreshBudgetEvent
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma fresh_layer_diagonal_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (a : ℝ) (A : Set (Environment d))
    (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A)
    (B : Set (Environment d×Environment d))
    (hB : @MeasurableSet (Environment d×Environment d)
      (MeasurableSpace.prod (rowSigma (BelowHeight (realPosition (step e)) a))
        (rowSigma {y | a≤dot (realPosition y) (realPosition (step e))})) B)
    (c : ℝ≥0∞) (hbound : ∀ η∈A, environmentLaw ν {ω | (η,ω)∈B} ≤ c) :
    environmentLaw ν (A∩{ω | (ω,ω)∈B}) ≤ c*environmentLaw ν A := by
  let S := BelowHeight (realPosition (step e)) a
  let T : Set (Lattice d) := {y | a≤dot (realPosition y) (realPosition (step e))}
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_FreshStages
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma stageBadEvent_joint_rows {d k : ℕ} (e f : Direction d) (a G Gminus Gplus : ℝ)
    (H : ℕ) (p : ℝ≥0∞) :
    @MeasurableSet (BudgetProfile (k:=k) e f a G × Environment d)
      (MeasurableSpace.prod inferInstance
        (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}))
      {z | z.2 ∈ stageBadEvent e f H Gminus Gplus z.1.val p} := by
  let : MeasurableSpace (Environment d) := rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}
  have hm (h : ℕ) : Measurable (fun z : BudgetProfile (k:=k) e f a G × Environment d =>
      rawTupleMixture (realPosition (step e)) h z.1.val z.2) := by
    apply (rawTupleMixture_joint_rows (realPosition (step e)) h
      (TupleAtHeight (k:=k) (realPosition (step e)) a) _ (fun x hx j y hy => ?_)).comp
      (((BudgetProfile.measurable_toSupported e f a G).comp measurable_fst).prodMk measurable_snd)
    simpa only [hx j,Set.mem_ofPred_eq] using hy.1
  have he (h : ℕ) (g : ℝ) : Measurable (fun z : BudgetProfile (k:=k) e f a G × Environment d =>
      rawTupleMixture (realPosition (step e)) h z.1.val z.2 {y | TupleSeparated f g y}) :=
    (Measure.measurable_coe (Set.to_countable _).measurableSet).comp (hm h)
  have hE : MeasurableSet {z : BudgetProfile (k:=k) e f a G × Environment d |
      ∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧ rawTupleMixture (realPosition (step e)) h z.1.val z.2 {y | TupleSeparated f Gminus y} < p} := by
    rw [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro h
    exact (MeasurableSet.const (1 ≤ h)).inter ((MeasurableSet.const (h ≤ H)).inter (measurableSet_lt (he h Gminus) measurable_const))
  have hF : MeasurableSet {z : BudgetProfile (k:=k) e f a G × Environment d |
      rawTupleMixture (realPosition (step e)) H z.1.val z.2 {y | TupleSeparated f Gplus y} < p} :=
    measurableSet_lt (he H Gplus) measurable_const
  exact hE.union hF

lemma fresh_layer_test_bound {d : ℕ} {D : Type*} [MeasurableSpace D]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (e : Direction d) (a : ℝ)
    (bad : D → Set (Environment d))
    (hbad : @MeasurableSet (D × Environment d)
      (MeasurableSpace.prod inferInstance
        (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))})) {z | z.2 ∈ bad z.1})
    (π : Environment d → D)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A)
    (δ : ℝ≥0∞) (hb : ∀ η∈A, environmentLaw ν (bad (π η)) ≤ δ) :
    environmentLaw ν (A ∩ {ω | ω ∈ bad (π ω)}) ≤ δ*environmentLaw ν A := by
  let S := rowSigma (BelowHeight (realPosition (step e)) a)
  let T := rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}
  have hp : @Measurable (Environment d×Environment d) D
      (MeasurableSpace.prod S T) _ (fun z => π z.1) := hπ.comp measurable_fst
  have hq : @Measurable (Environment d×Environment d) (Environment d)
      (MeasurableSpace.prod S T) T Prod.snd := measurable_snd
  have hpair : @Measurable (Environment d×Environment d) (D×Environment d)
      (MeasurableSpace.prod S T) (MeasurableSpace.prod inferInstance T)
      (fun z => (π z.1,z.2)) := hp.prodMk hq
  have hm : @MeasurableSet (Environment d×Environment d) (MeasurableSpace.prod S T)
      {z | z.2 ∈ bad (π z.1)} := hbad.preimage hpair
  exact fresh_layer_diagonal_bound ν e a A hA {z | z.2 ∈ bad (π z.1)} hm δ hb

lemma fresh_stage_bound {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a G Gminus Gplus : ℝ) (H : ℕ) (p δ : ℝ≥0∞)
    (π : Environment d → BudgetProfile (k:=k) e f a G)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (hbound : ∀ η, environmentLaw ν (stageBadEvent e f H Gminus Gplus (π η).val p) ≤ δ)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A) :
    environmentLaw ν (A ∩ {ω | ω ∈ stageBadEvent e f H Gminus Gplus (π ω).val p}) ≤
      δ*environmentLaw ν A :=
  fresh_layer_test_bound ν e a (fun ρ : BudgetProfile (k:=k) e f a G => stageBadEvent e f H Gminus Gplus ρ.val p)
    (stageBadEvent_joint_rows e f a G Gminus Gplus H p) π hπ A hA δ (fun η _ => hbound η)

lemma stopped_stage_failure_subset {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) (hH : 1 ≤ H) (hR : 1 ≤ R) :
    {ω | stageTestMass e f a Gminus Gplus π H (stageStop e f a Gminus Gplus B π H R ω) ω <
      ENNReal.ofReal (Real.exp (-B))} ⊆
    {ω | ω ∈ stageBadEvent e f H Gminus Gplus (π ω).val (ENNReal.ofReal (Real.exp (-B)))} := by
  intro ω hω
  have hle : stageStop e f a Gminus Gplus B π H R ω ≤ min H R := hittingBtwn_le ω
  have hpos : 1 ≤ stageStop e f a Gminus Gplus B π H R ω :=
    le_hittingBtwn (le_min hH hR) _
  change stageTestMass e f a Gminus Gplus π H (stageStop e f a Gminus Gplus B π H R ω) ω < ENNReal.ofReal (Real.exp (-B)) at hω
  simp only [stageTestMass,ite_eq_right (by omega : stageStop e f a Gminus Gplus B π H R ω ≠ 0)] at hω
  by_cases he : stageStop e f a Gminus Gplus B π H R ω=H
  · simp only [ite_eq_left he,min_lt_iff] at hω
    exact hω.elim (fun hh => Or.inl ⟨_,hpos,hle.trans (min_le_left _ _),hh⟩)
      (fun hh => Or.inr (by simpa only [he,stageEndpointMass] using hh))
  · simp only [ite_eq_right he] at hω
    exact Or.inl ⟨_,hpos,hle.trans (min_le_left _ _),hω⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StageRetention
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma stageStop_pos {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ)
    (hH : 0<H) (hR : 0<R) (ω : Environment d) :
    0 < stageStop e f a Gminus Gplus B π H R ω := by
  change 1 ≤ stageStop e f a Gminus Gplus B π H R ω
  exact le_hittingBtwn (n:=1) (le_min hH hR) ω

lemma stageStop_le {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) (ω : Environment d) :
    stageStop e f a Gminus Gplus B π H R ω  ≤  min H R := hittingBtwn_le ω

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_OperationalEpisode
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeStageNext_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hq : q.height ≤ N) :
    (episodeStageNext e f hef r fexp g χ b N q ω).height ≤ N := by
  have hs := stageStop_le e f q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) ω
  change episodeStageLength e f r fexp g χ b N q ω  ≤  _ at hs
  rw [episodeStageNext_height]
  omega

lemma episodeStageNext_gt {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hH : ∀ s, sfloor ≤ s  →  0 < episodeStageH χ b s)
    (hq : EpisodeReady e f r sfloor N q) :
    q.height<(episodeStageNext e f hef r fexp g χ b N q ω).height := by
  rw [episodeStageNext_height]
  exact Nat.lt_add_of_pos_right (stageStop_pos e f q.height _ _ _ _ _ _
    (hH q.scale hq.2) (Nat.sub_pos_of_lt hq.1) ω)

lemma episodeRun_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hq : q.height ≤ N) (n : ℕ) :
    (episodeRun e f hef r fexp g χ b sfloor N q ω n).height ≤ N := by
  induction n with
  | zero => exact hq
  | succ n ih =>
    rw [episodeRun]
    split
    · exact episodeStageNext_le e f hef r fexp g χ b N _ ω ih
    · exact ih

lemma episodeRun_progress {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hH : ∀ s, sfloor ≤ s  →  0 < episodeStageH χ b s) (n : ℕ)
    (hready : EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n)) :
    q.height+n ≤ (episodeRun e f hef r fexp g χ b sfloor N q ω n).height := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [episodeRun] at hready ⊢
    by_cases hp : EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n)
    · rw [ite_eq_left hp] at hready ⊢
      have ht := episodeStageNext_gt e f hef r fexp g χ b sfloor N _ ω hH hp
      have hi := ih hp
      omega
    · rw [ite_eq_right hp] at hready
      exact False.elim (hp hready)

theorem episodeRun_terminates {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hq : q.height ≤ N)
    (hH : ∀ s, sfloor ≤ s  →  0 < episodeStageH χ b s) :
    ¬EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω N) := by
  intro hr
  have hp := episodeRun_progress e f hef r fexp g χ b sfloor N q ω hH N hr
  have hu := episodeRun_le e f hef r fexp g χ b sfloor N q ω hq N
  have hn := hr.1
  omega

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StageClassification
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeStage_grows_iff {d k : ℕ} (e f : Direction d)
    (r : ℝ → ℝ) (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) :
    episodeStageGrows e f r fexp g χ b N q ω ↔
      episodeStageLength e f r fexp g χ b N q ω=episodeStageH χ b q.scale ∧
        ¬episodeStageFails e f r fexp g χ b N q ω := by
  simp only [episodeStageGrows,episodeStageFails,not_lt,neg_mul]

lemma episodeStage_not_fail_length {d k : ℕ} (e f : Direction d)
    (r : ℝ → ℝ) (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hf : ¬episodeStageFails e f r fexp g χ b N q ω) :
    episodeStageLength e f r fexp g χ b N q ω = min (episodeStageH χ b q.scale) (N-q.height) := by
  have hu : episodeStageLength e f r fexp g χ b N q ω ≤ min (episodeStageH χ b q.scale) (N-q.height) :=
    hittingBtwn_le ω
  apply le_antisymm hu
  by_contra hn
  have hl := lt_of_not_ge hn
  exact hf (hittingBtwn_mem_set_of_hittingBtwn_lt hl)

lemma episodeStage_incomplete_terminal {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hq : q.height ≤ N) (hf : ¬episodeStageFails e f r fexp g χ b N q ω)
    (hg : ¬episodeStageGrows e f r fexp g χ b N q ω) :
    (episodeStageNext e f hef r fexp g χ b N q ω).height=N := by
  have hl := episodeStage_not_fail_length e f r fexp g χ b N q ω hf
  have hn : episodeStageLength e f r fexp g χ b N q ω ≠ episodeStageH χ b q.scale := by
    intro he
    exact hg ((episodeStage_grows_iff e f r fexp g χ b N q ω).mpr ⟨he,hf⟩)
  rw [episodeStageNext_height]
  omega

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeAdapted
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

lemma branch_unique (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (l m : Option (ℕ×Bool))
    (hl : ω∈(c.branch hef fexp g χ b sfloor N l).event)
    (hm : ω∈(c.branch hef fexp g χ b sfloor N m).event) : l=m := by
  cases l with
  | none =>
    cases m with
    | none => rfl
    | some m => exact False.elim (hl.2 ⟨hm.2.1,hm.2.2.1⟩)
  | some l =>
    cases m with
    | none => exact False.elim (hm.2 ⟨hl.2.1,hl.2.2.1⟩)
    | some m =>
      have hj : l.1=m.1 := hl.2.2.2.1.symm.trans hm.2.2.2.1
      have hg := hl.2.2.2.2
      rw [hj] at hg
      have hb : (l.2=true) ↔ (m.2=true) := hg.symm.trans hm.2.2.2.2
      have hbool : l.2=m.2 := by
        cases h₁ : l.2 <;> cases h₂ : m.2 <;> simp_all only [Bool.false_eq_true,iff_false,
          iff_true,not_true_eq_false,iff_self]
      exact congrArg some (Prod.ext hj hbool)

end EpisodeChart

lemma episodeInitialAtlas_partition {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (sfloor : ℝ) (hR : 0 ≤ r sfloor) (t : ℕ) :
    (episodeInitialAtlas (k:=k) e f hef r sfloor hR t).IsPartition :=
  by
    intro l m _ _ _
    change Unit at l m
    exact Subsingleton.elim l m

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeLength
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
  (q : EpisodeState (k:=k) e f r) (ω : Environment d)

local notation "R" => episodeRun e f hef r fexp g χ b sfloor N q ω
local notation "A" => scale e f hef r fexp g χ b sfloor N q ω
local notation "Grow" => episodeStageGrows e f r fexp g χ b N
local notation "Fail" => episodeStageFails e f r fexp g χ b N
local notation "Ready" => EpisodeReady e f r sfloor N

lemma scale_pos (hq : 0 < q.scale) (n : ℕ) : 0 < A n := by
  induction n with
  | zero => exact hq
  | succ n ih => dsimp only [scale]; split; split; positivity; split <;> positivity; exact ih

lemma scale_agrees (n : ℕ) (hn : (R n).height < N) : A n=(R n).scale := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [episodeRun] at hn ⊢
    rw [scale]
    by_cases hr : Ready (R n)
    · simp only [ite_eq_left hr] at hn ⊢
      rw [ih hr.1]
      change (if Grow (R n) ω then (R n).scale*Real.exp (g*b) else
        if Fail (R n) ω then (R n).scale*Real.exp (-fexp*b) else (R n).scale) =
          episodeStageScale e f r fexp g χ b N (R n) ω
      unfold episodeStageScale
      by_cases hg : Grow (R n) ω
      · simp only [ite_eq_left hg]
      · rw [ite_eq_right hg,ite_eq_right hg]
        by_cases hf : Fail (R n) ω
        · rw [ite_eq_left hf]
        · have ht := episodeStage_incomplete_terminal e f hef r fexp g χ b N (R n) ω hr.1.le hf hg
          omega
    · simp only [ite_eq_right hr] at hn ⊢
      exact ih hn

lemma scale_le (hq : 0 < q.scale) (hqcap : q.scale ≤ max sfloor (N:ℝ))
    (hqN : q.height ≤ N) (hf : 0 ≤ fexp) (hb : 0 ≤ b)
    (hH : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s : ℝ)) (n : ℕ) :
    A n ≤ max sfloor (N:ℝ) := by
  induction n with
  | zero => exact hqcap
  | succ n ih =>
    rw [scale]
    by_cases hr : Ready (R n)
    · rw [ite_eq_left hr]
      by_cases hg : Grow (R n) ω
      · rw [ite_eq_left hg,scale_agrees e f hef r fexp g χ b sfloor N q ω n hr.1]
        have hl : episodeStageLength e f r fexp g χ b N (R n) ω ≤ N := by
          have hn := episodeStageNext_le e f hef r fexp g χ b N (R n) ω
            (episodeRun_le e f hef r fexp g χ b sfloor N q ω hqN n)
          rw [episodeStageNext_height] at hn
          omega
        apply (hH _ hr.2).trans
        have he := (episodeStage_grows_iff e f r fexp g χ b N (R n) ω).mp hg
        rw [←he.1]
        exact (show (episodeStageLength e f r fexp g χ b N (R n) ω : ℝ) ≤ (N:ℝ) by exact_mod_cast hl).trans
          (le_max_right _ _)
      · rw [ite_eq_right hg]
        split
        · apply le_trans _ ih
          exact mul_le_of_le_one_right (scale_pos e f hef r fexp g χ b sfloor N q ω hq n).le
            (Real.exp_le_one_iff.mpr (by nlinarith))
        · exact ih
    · rw [ite_eq_right hr]
      exact ih

lemma log_scale (hq : 0 < q.scale) (n : ℕ) :
    Real.log (A n)-Real.log q.scale =
      g*b*(episodeCount e f hef r fexp g χ b sfloor N q ω Grow n : ℝ) -
      fexp*b*(episodeCount e f hef r fexp g χ b sfloor N q ω Fail n : ℝ) := by
  induction n with
  | zero => simp only [scale,episodeCount,Nat.cast_zero,mul_zero,sub_self]
  | succ n ih =>
    rw [scale,episodeCount,episodeCount]
    by_cases hr : Ready (R n)
    · by_cases hg : Grow (R n) ω
      · have hf := ((episodeStage_grows_iff e f r fexp g χ b N (R n) ω).mp hg).2
        simp only [hr,hg,hf,and_self,and_false,ite_true, if_true,ite_false, if_false,
          Nat.cast_add,Nat.cast_one,add_zero]
        rw [Real.log_mul (ne_of_gt (scale_pos e f hef r fexp g χ b sfloor N q ω hq n)) (Real.exp_ne_zero _),Real.log_exp]
        linarith
      · by_cases hf : Fail (R n) ω
        · simp only [hr,hg,hf,and_self,and_false,ite_true, if_true,ite_false, if_false,
            Nat.cast_add,Nat.cast_one,add_zero]
          rw [Real.log_mul (ne_of_gt (scale_pos e f hef r fexp g χ b sfloor N q ω hq n)) (Real.exp_ne_zero _),Real.log_exp]
          linarith
        · simpa only [hr,hg,hf,and_false,ite_true, if_true,ite_false, if_false,add_zero] using ih
    · simpa only [hr,false_and,ite_false, if_false,add_zero] using ih

end EpisodeLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeCountLedger
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

namespace EpisodeLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
  (q : EpisodeState (k:=k) e f r) (ω : Environment d)
local notation "R" => episodeRun e f hef r fexp g χ b sfloor N q ω
local notation "Grow" => episodeStageGrows e f r fexp g χ b N
local notation "Fail" => episodeStageFails e f r fexp g χ b N
local notation "Inc" => episodeStageIncomplete e f r fexp g χ b N
local notation "Ready" => EpisodeReady e f r sfloor N
local notation "Count" => episodeCount e f hef r fexp g χ b sfloor N q ω
local notation "J" => episodeSteps e f hef r fexp g χ b sfloor N q ω

lemma counts_partition (n : ℕ) : J n=Count Grow n+Count Fail n+Count Inc n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [episodeSteps,episodeCount,episodeCount,episodeCount]
    by_cases hr : Ready (R n)
    · by_cases hg : Grow (R n) ω
      · have hf := ((episodeStage_grows_iff e f r fexp g χ b N (R n) ω).mp hg).2
        simp only [episodeStageIncomplete,hr,hg,hf,not_true_eq_false,false_and,and_self,
          true_and,ite_true, if_true,ite_false, if_false,add_zero]
        omega
      · by_cases hf : Fail (R n) ω
        · simp only [episodeStageIncomplete,hr,hg,hf,not_true_eq_false,not_false_eq_true,
            true_and,and_false,ite_true, if_true,ite_false, if_false,add_zero]
          omega
        · simp only [episodeStageIncomplete,hr,hg,hf,not_false_eq_true,true_and,
            and_true,ite_true, if_true,ite_false, if_false,add_zero]
          omega
    · simp only [hr,false_and,ite_false, if_false,add_zero]
      exact ih

lemma incomplete_count (n : ℕ) : Count Inc n ≤ 1 ∧ ((R n).height < N → Count Inc n=0) := by
  induction n with
  | zero => exact ⟨by simp only [episodeCount]; omega,fun _ => rfl⟩
  | succ n ih =>
    rw [episodeCount,episodeRun]
    by_cases hr : Ready (R n)
    · rw [ite_eq_left hr]
      by_cases hi : Inc (R n) ω
      · rw [ite_eq_left ⟨hr,hi⟩,ih.2 hr.1]
        refine ⟨by omega,?_⟩
        have ht := episodeStage_incomplete_terminal e f hef r fexp g χ b N (R n) ω hr.1.le hi.2 hi.1
        intro hn
        omega
      · rw [ite_eq_right (fun hh => hi hh.2),add_zero]
        exact ⟨ih.1,fun _ => ih.2 hr.1⟩
    · rw [ite_eq_right hr,ite_eq_right (fun hh => hr hh.1),add_zero]
      exact ih

lemma nonterminal_ledger (hq : 0 < q.scale) (hqN : q.height ≤ N)
    (hqfloor : q.scale=sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hn : (R N).height < N) :
    g*b*(Count Grow N : ℝ) ≤ fexp*b*(Count Fail N : ℝ) := by
  have ht := episodeRun_terminates e f hef r fexp g χ b sfloor N q ω hqN hH
  have hs : (R N).scale < sfloor := lt_of_not_ge (fun hh => ht ⟨hn,hh⟩)
  have ha := scale_agrees e f hef r fexp g χ b sfloor N q ω N hn
  have hl := log_scale e f hef r fexp g χ b sfloor N q ω hq N
  have hp := scale_pos e f hef r fexp g χ b sfloor N q ω hq N
  have hlog : Real.log (scale e f hef r fexp g χ b sfloor N q ω N) ≤ Real.log q.scale :=
    Real.log_le_log hp (by rw [ha,hqfloor]; exact hs.le)
  linarith only [hl,hlog]

lemma terminal_ledger (hq : 0 < q.scale) (hqfloor : q.scale=sfloor)
    (hqN : q.height ≤ N) (hN : sfloor ≤ (N:ℝ)) (hf : 0 ≤ fexp) (hb : 0 ≤ b)
    (hH : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s : ℝ)) :
    g*b*(Count Grow N : ℝ)-fexp*b*(Count Fail N : ℝ) ≤ Real.log (N:ℝ)-Real.log sfloor := by
  have ha := scale_le e f hef r fexp g χ b sfloor N q ω hq
    (by rw [hqfloor]; exact le_max_left _ _) hqN hf hb hH N
  rw [max_eq_right hN] at ha
  have hlog := Real.log_le_log (scale_pos e f hef r fexp g χ b sfloor N q ω hq N) ha
  have hl := log_scale e f hef r fexp g χ b sfloor N q ω hq N
  rw [hqfloor] at hl
  linarith only [hl,hlog]

end EpisodeLedger
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
  (ω : Environment d)

local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω
local notation "Q" => episodeInitial (k:=k) e f hef r sfloor hR
local notation "Grow" => episodeStageGrows (k:=k) e f r fexp g χ b N
local notation "Fail" => episodeStageFails (k:=k) e f r fexp g χ b N
local notation "Inc" => episodeStageIncomplete (k:=k) e f r fexp g χ b N

local notation "C" => count e f hef r fexp g χ b sfloor hR N ω
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N ω

lemma partition (i : ℕ) : J i=C Grow i+C Fail i+C Inc i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [steps,count,count,count]
    by_cases ht : T i < N
    · simp only [ite_eq_left ht]
      have hp := EpisodeLedger.counts_partition (k:=k) e f hef r fexp g χ b sfloor N (Q (T i) ω) ω N
      omega
    · simpa only [ite_eq_right ht,add_zero] using ih

lemma incomplete (i : ℕ) : C Inc i ≤ 1 ∧ (T i < N → C Inc i=0) := by
  induction i with
  | zero => exact ⟨by simp only [count]; omega,fun _ => rfl⟩
  | succ i ih =>
    rw [count,episodeBoundary]
    by_cases ht : T i < N
    · simp only [ite_eq_left ht]
      have hz := ih.2 ht
      rw [hz,zero_add]
      exact EpisodeLedger.incomplete_count e f hef r fexp g χ b sfloor N (Q (T i) ω) ω N
    · simpa only [ite_eq_right ht,add_zero] using ih

lemma counts_le (i : ℕ) : J i ≤ C Grow i+C Fail i+1 := by
  have hp := partition (k:=k) e f hef r fexp g χ b sfloor hR N ω i
  have hi := (incomplete (k:=k) e f hef r fexp g χ b sfloor hR N ω i).1
  omega

lemma balance (hs : 0 < sfloor) (hN : sfloor ≤ (N:ℝ))
    (hf : 0 ≤ fexp) (hb : 0 ≤ b)
    (hH : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s : ℝ)) (i : ℕ) :
    g*b*(C Grow i : ℝ)-fexp*b*(C Fail i : ℝ) ≤ Real.log (N:ℝ)-Real.log sfloor ∧
      (T i < N → g*b*(C Grow i : ℝ)-fexp*b*(C Fail i : ℝ) ≤ 0) := by
  have hH0 : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s := by
    intro s h
    exact_mod_cast (mul_pos (hs.trans_le h) (Real.exp_pos (g*b))).trans_le (hH s h)
  have hL : 0 ≤ Real.log (N:ℝ)-Real.log sfloor := sub_nonneg.mpr (Real.log_le_log hs hN)
  induction i with
  | zero => simpa only [count,Nat.cast_zero,mul_zero,sub_self] using ⟨hL,fun _ => le_refl 0⟩
  | succ i ih =>
    rw [count,count,episodeBoundary]
    by_cases ht : T i < N
    · simp only [ite_eq_left ht,Nat.cast_add]
      have hqN : (Q (T i) ω).height ≤ N := Nat.succ_le_of_lt ht
      have hqpos : 0 < (Q (T i) ω).scale := hs
      have hqeq : (Q (T i) ω).scale=sfloor := rfl
      have hp := ih.2 ht
      have hu := EpisodeLedger.terminal_ledger e f hef r fexp g χ b sfloor N
        (Q (T i) ω) ω hqpos hqeq hqN hN hf hb hH
      constructor
      · nlinarith only [hp,hu]
      · intro hn
        have hh := EpisodeLedger.nonterminal_ledger e f hef r fexp g χ b sfloor N
          (Q (T i) ω) ω hqpos hqN hqeq hH0 hn
        nlinarith only [hp,hh]
    · simpa only [ite_eq_right ht,add_zero] using ih

theorem stage_count_bound (hs : 1 ≤ sfloor) (hN : sfloor ≤ (N:ℝ))
    (hf : 0 ≤ fexp) (hg : 0 < g) (hb : 0 < b)
    (hH : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s : ℝ)) :
    (J N : ℝ) ≤ Real.log (N:ℝ)/(g*b)+(1+fexp/g)*(C Fail N : ℝ)+1 := by
  have hbal := (balance (k:=k) e f hef r fexp g χ b sfloor hR N ω
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hs) hN hf hb.le hH N).1
  have hlog : 0 ≤ Real.log sfloor := Real.log_nonneg hs
  have hcnt : (J N : ℝ) ≤ (C Grow N : ℝ)+(C Fail N : ℝ)+1 := by
    exact_mod_cast counts_le (k:=k) e f hef r fexp g χ b sfloor hR N ω N
  have hgb : 0 < g*b := mul_pos hg hb
  apply (mul_le_mul_iff_right₀ hgb).mp
  have he : (g*b)*(Real.log (N:ℝ)/(g*b)+(1+fexp/g)*(C Fail N : ℝ)+1) =
      Real.log (N:ℝ)+(g*b)*(C Fail N : ℝ)+(fexp*b)*(C Fail N : ℝ)+g*b := by
    field_simp
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_right hcnt hgb.le
  nlinarith only [hh,hbal,hlog]

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_LocalEpisodeLog
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

lemma countedBranch_unique (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (l m : Option (ℕ×Bool×Bool))
    (hl : ω∈(c.countedBranch hef fexp g χ b sfloor N l).event)
    (hm : ω∈(c.countedBranch hef fexp g χ b sfloor N m).event) : l=m := by
  cases l with
  | none =>
    cases m with
    | none => rfl
    | some m => exact False.elim (hl.2 ⟨hm.1.2.1,hm.1.2.2.1⟩)
  | some l =>
    cases m with
    | none => exact False.elim (hm.2 ⟨hl.1.2.1,hl.1.2.2.1⟩)
    | some m =>
      have hp := c.branch_unique hef fexp g χ b sfloor N ω (some (l.1,l.2.1)) (some (m.1,m.2.1)) hl.1 hm.1
      have hj : l.1=m.1 := congrArg (fun z : ℕ×Bool => z.1) (Option.some.inj hp)
      have hg : l.2.1=m.2.1 := congrArg (fun z : ℕ×Bool => z.2) (Option.some.inj hp)
      have hh := hl.2
      rw [hj] at hh
      have hb : (l.2.2=true) ↔ (m.2.2=true) := hh.symm.trans hm.2
      have hf : l.2.2=m.2.2 := by
        cases h₁ : l.2.2 <;> cases h₂ : m.2.2 <;> simp_all only [Bool.false_eq_true,iff_false,
          iff_true,not_true_eq_false,iff_self]
      exact congrArg some (Prod.ext hj (Prod.ext hg hf))

end EpisodeChart
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeRecordedAtlas
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

lemma advance_partition (A : EpisodeRecordedAtlas q J F) (hA : A.toEpisodeAtlas.IsPartition)
    (hef : e.1 ≠ f.1) (fexp g χ b sfloor : ℝ) (N : ℕ) :
    (A.advance hef fexp g χ b sfloor N).toEpisodeAtlas.IsPartition := by
  rintro ⟨l,j⟩ ⟨m,h⟩ ω hl hm
  have hl₀ := ((A.chart l).countedBranch_state hef fexp g χ b sfloor N ω j hl).1
  have hm₀ := ((A.chart m).countedBranch_state hef fexp g χ b sfloor N ω h hm).1
  have he := hA l m ω hl₀ hm₀
  subst m
  exact Prod.ext rfl ((A.chart l).countedBranch_unique hef fexp g χ b sfloor N ω j h hl hm)

lemma count_event (A : EpisodeRecordedAtlas q J F) (m j h : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)]
      {ω | (q ω).height=m ∧ J ω=j ∧ F ω=h} := by
  have := A.countable
  have he : {ω | (q ω).height=m ∧ J ω=j ∧ F ω=h} =
      ⋃ l : {l : A.Label // (A.chart l).height=m ∧ A.stages l=j ∧ A.failures l=h}, (A.chart l.val).event := by
    ext ω
    constructor
    · rintro ⟨hm,hj,hf⟩
      obtain ⟨l,hl⟩ := A.cover ω
      refine Set.mem_iUnion.mpr ⟨⟨l,?_,?_,?_⟩,hl⟩
      · rw [A.correct l ω hl] at hm
        exact hm
      · exact (A.stages_correct l ω hl).symm.trans hj
      · exact (A.failures_correct l ω hl).symm.trans hf
    · intro hh
      obtain ⟨l,hl⟩ := Set.mem_iUnion.mp hh
      change (q ω).height=m ∧ J ω=j ∧ F ω=h
      rw [A.correct l ω hl,A.stages_correct l ω hl,A.failures_correct l ω hl]
      exact l.property
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  have hm := (A.chart l.val).measurable_event
  rwa [l.property.1] at hm

end EpisodeRecordedAtlas
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

lemma runFrom_partition (A : EpisodeRecordedAtlas q J F) (hA : A.toEpisodeAtlas.IsPartition)
    (hef : e.1 ≠ f.1) (fexp g χ b sfloor : ℝ) (N n : ℕ) :
    (A.runFrom hef fexp g χ b sfloor N n).toEpisodeAtlas.IsPartition := by
  induction n with
  | zero => exact hA
  | succ n ih =>
    exact advance_partition _ ih hef fexp g χ b sfloor N

end EpisodeRecordedAtlas
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeCounterChain
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeCounterAtlas_partition {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N i : ℕ) :
    (episodeCounterAtlas (k:=k) e f hef r fexp g χ b sfloor hR N i).toEpisodeAtlas.IsPartition := by
  induction i with
  | zero => exact episodeInitialAtlas_partition e f hef r sfloor hR 0
  | succ i ih => exact EpisodeRecordedAtlas.runFrom_partition _ ih hef fexp g χ b sfloor N N

lemma episodeRun_stopped {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hq : N ≤ q.height) (n : ℕ) :
    episodeRun e f hef r fexp g χ b sfloor N q ω n=q ∧
    episodeSteps e f hef r fexp g χ b sfloor N q ω n=0 ∧
    episodeCount e f hef r fexp g χ b sfloor N q ω (episodeStageFails e f r fexp g χ b N) n=0 := by
  have hnr : ¬EpisodeReady e f r sfloor N q := fun h => (Nat.not_lt_of_ge hq) h.1
  induction n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    simp only [episodeRun,episodeSteps,episodeCount,ih.1,ih.2.1,ih.2.2,hnr,ite_false, if_false,false_and,add_zero,and_self]

lemma episodeCounterChain_actual {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) (i : ℕ) :
    let T := episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    let p := episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    (T<N → p.state=episodeInitial e f hef r sfloor hR T ω) ∧
    (N≤T → N≤p.state.height) ∧
    p.stages=EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i ∧
    p.failures=EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
      (episodeStageFails e f r fexp g χ b N) i := by
  dsimp only
  induction i with
  | zero => exact ⟨fun _ => rfl,fun h => h.trans (Nat.zero_le _),rfl,rfl⟩
  | succ i ih =>
    let T := episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    let p := episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    by_cases ht : T<N
    <;> dsimp only [T] at ht
    · have he := ih.1 ht
      simp only [episodeBoundary,episodeCounterChain,EpisodeChainLedger.steps,EpisodeChainLedger.count,he,ite_eq_left ht]
      refine ⟨fun _ => rfl,?_,?_,?_⟩
      · intro hh
        exact hh.trans (Nat.le_add_right _ 1)
      · rw [ih.2.2.1]
      · rw [ih.2.2.2]
    · have hp := ih.2.1 (Nat.le_of_not_lt ht)
      have hz := episodeRun_stopped e f hef r fexp g χ b sfloor N p.state ω hp N
      dsimp only [p] at hz
      simp only [episodeBoundary,episodeCounterChain,EpisodeChainLedger.steps,EpisodeChainLedger.count,ite_eq_right ht,
        hz.1,hz.2.1,hz.2.2,add_zero]
      refine ⟨fun h => False.elim (ht h),?_,ih.2.2.1,ih.2.2.2⟩
      intro _
      exact hp.trans (Nat.le_add_right _ 1)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

lemma measurable_counts (A : EpisodeRecordedAtlas q J F) : Measurable (fun ω => (J ω,F ω)) := by
  apply measurable_to_countable'
  intro z
  have he : (fun ω => (J ω,F ω)) ⁻¹' {z} =
      ⋃ m : ℕ, {ω | (q ω).height=m ∧ J ω=z.1 ∧ F ω=z.2} := by
    ext ω
    constructor
    · intro h
      have hh : J ω=z.1 ∧ F ω=z.2 := Prod.mk.inj h
      exact Set.mem_iUnion.mpr ⟨(q ω).height,rfl,hh⟩
    · intro h
      obtain ⟨m,hm,hj,hf⟩ := Set.mem_iUnion.mp h
      exact Prod.ext hj hf
  rw [he]
  exact MeasurableSet.iUnion fun m => (rowSigma_le _) _ (A.count_event m z.1 z.2)

end EpisodeRecordedAtlas

lemma episode_counts_le_loops {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r)
    (ω : Environment d) (test : EpisodeState (k:=k) e f r → Environment d → Prop) (n : ℕ) :
    episodeSteps e f hef r fexp g χ b sfloor N q ω n ≤ n ∧
    episodeCount e f hef r fexp g χ b sfloor N q ω test n ≤ n := by
  induction n with
  | zero => exact ⟨le_refl _,le_refl _⟩
  | succ n ih =>
    rw [episodeSteps,episodeCount]
    constructor <;> split <;> omega

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "Fail" => episodeStageFails (k:=k) e f r fexp g χ b N
local notation "J" => fun ω i => steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i
local notation "C" => fun ω i => count (k:=k) e f hef r fexp g χ b sfloor hR N ω Fail i

lemma measurable_counts (i : ℕ) : Measurable (fun ω => (J ω i,C ω i)) := by
  have he : (fun ω => ((episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).stages,
      (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).failures)) =
      (fun ω => (J ω i,C ω i)) := by
    funext ω
    have hh := episodeCounterChain_actual (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    exact Prod.ext hh.2.2.1 hh.2.2.2
  rw [←he]
  exact (episodeCounterAtlas (k:=k) e f hef r fexp g χ b sfloor hR N i).measurable_counts

lemma counts_bounded (ω : Environment d) (i : ℕ) : J ω i ≤ i*N ∧ C ω i ≤ i*N := by
  induction i with
  | zero => simp only [steps,count,Nat.zero_mul,le_refl,and_self]
  | succ i ih =>
    have hh := episode_counts_le_loops e f hef r fexp g χ b sfloor N
      (episodeInitial (k:=k) e f hef r sfloor hR
        (episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i) ω) ω Fail N
    dsimp only at ih ⊢
    rw [steps,count,Nat.succ_mul]
    constructor <;> split <;> omega

lemma counts_integrable (Q : Measure (Environment d)) [IsFiniteMeasure Q] (i : ℕ) :
    Integrable (fun ω => (J ω i:ℝ)) Q ∧ Integrable (fun ω => (C ω i:ℝ)) Q := by
  have hm := measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N i
  have hcast : Measurable (fun n : ℕ => (n:ℝ)) := measurable_of_countable _
  constructor
  · apply Entropy.integrable_of_bounded (hcast.comp hm.fst)
    refine ⟨(i*N:ℕ),fun ω => ?_⟩
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp only [Function.comp_def]
    exact_mod_cast (counts_bounded (k:=k) e f hef r fexp g χ b sfloor hR N ω i).1
  · apply Entropy.integrable_of_bounded (hcast.comp hm.snd)
    refine ⟨(i*N:ℕ),fun ω => ?_⟩
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp only [Function.comp_def]
    exact_mod_cast (counts_bounded (k:=k) e f hef r fexp g χ b sfloor hR N ω i).2

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeFresh
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

lemma actual_failure_bound (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (N : ℕ)
    (ht : c.height<N) (hH : 0 < episodeStageH χ b c.scale) (δ : ℝ≥0∞)
    (hbound : ∀ π : BudgetProfile (k:=k) e f c.height (r c.scale),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b c.scale)
        (r (c.scale*Real.exp (-fexp*b))) (r (c.scale*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ δ)
    (A : Set (Environment d))
    (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) c.height)] A) :
    environmentLaw ν (A ∩ {ω | episodeStageFails e f r fexp g χ b N (c.state ω) ω}) ≤
      δ*environmentLaw ν A := by
  have hb := fresh_stage_bound ν e f c.height (r c.scale)
    (r (c.scale*Real.exp (-fexp*b))) (r (c.scale*Real.exp (g*b)))
    (episodeStageH χ b c.scale) (ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))) δ
    c.profile c.measurable_profile (fun η => hbound (c.profile η)) A hA
  apply le_trans (measure_mono ?_) hb
  intro ω hω
  refine ⟨hω.1,?_⟩
  have hs := stopped_stage_failure_subset e f c.height
    (r (c.scale*Real.exp (-fexp*b))) (r (c.scale*Real.exp (g*b))) ((k:ℝ)*b)
    c.layerProfile (episodeStageH χ b c.scale) (N-c.height) hH (by omega)
  apply hs
  exact hω.2

end EpisodeChart
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeExponential
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma stagePotential_succ_le (t : ℝ) (j f : ℕ) (D : Prop) [Decidable D] :
    stagePotential t (j+1) (f+if D then 1 else 0) ≤
      stagePotential t j f * ENNReal.ofReal (Real.exp (-Real.exp (-t))) *
        (1+ENNReal.ofReal (Real.exp t)*(if D then 1 else 0)) := by
  unfold stagePotential
  have he (z : ℝ) : t*((f:ℝ)+z)-Real.exp (-t)*((j:ℝ)+1) =
      (t*(f:ℝ)-Real.exp (-t)*(j:ℝ))+(-Real.exp (-t))+t*z := by ring
  by_cases h : D
  · simp only [ite_eq_left h,Nat.cast_add,Nat.cast_one,he,Real.exp_add,mul_one]
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact le_add_left (le_refl _)
  · simp only [ite_eq_right h,add_zero,Nat.cast_add,Nat.cast_one,mul_zero,add_zero]
    have he' : t*(f:ℝ)-Real.exp (-t)*((j:ℝ)+1) =
        (t*(f:ℝ)-Real.exp (-t)*(j:ℝ))+(-Real.exp (-t)) := by ring
    rw [he',Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _),mul_one]

lemma stage_exponential_factor (t : ℝ) :
    ENNReal.ofReal (Real.exp (-Real.exp (-t))) *
      (1+ENNReal.ofReal (Real.exp t)*ENNReal.ofReal (Real.exp (-2*t))) ≤ 1 := by
  have ht : Real.exp t*Real.exp (-2*t)=Real.exp (-t) := by rw [←Real.exp_add]; congr 1; ring
  rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),ht,←ENNReal.ofReal_one,
    ←ENNReal.ofReal_add (by norm_num : (0:ℝ)≤1) (Real.exp_nonneg _),
    ←ENNReal.ofReal_mul (Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.exp (-Real.exp (-t))*Real.exp (Real.exp (-t)) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (Real.exp (-t))]) (by positivity)
    _ = 1 := by rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]

lemma stagePotential_set_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E D : Set Ω) (hE : MeasurableSet E) (t : ℝ) (j f : ℕ)
    (hD : P (E∩D) ≤ ENNReal.ofReal (Real.exp (-2*t))*P E) :
    ∫⁻ ω in E, stagePotential t (j+1) (f+if ω∈D then 1 else 0) ∂P ≤
      stagePotential t j f*P E := by
  let a := ENNReal.ofReal (Real.exp (-Real.exp (-t)))
  let c := ENNReal.ofReal (Real.exp t)
  let w := stagePotential t j f
  have hd : ∫⁻ ω in E, D.indicator (fun _ => (1:ℝ≥0∞)) ω ∂P ≤ P (E∩D) := by
    have h := lintegral_indicator_const_le (μ:=P.restrict E) D (1:ℝ≥0∞)
    simpa only [one_mul,Measure.restrict_apply' hE,Set.inter_comm] using h
  calc
    _ ≤ ∫⁻ ω in E, w*a*(1+c*D.indicator (fun _ => (1:ℝ≥0∞)) ω) ∂P := by
      apply lintegral_mono
      intro ω
      simpa only [Set.indicator_apply,Pi.one_apply] using stagePotential_succ_le t j f (ω∈D)
    _ = w*a*(P E+c*(∫⁻ ω in E, D.indicator (fun _ => (1:ℝ≥0∞)) ω ∂P)) := by
      rw [lintegral_const_mul' (w*a) _ (ENNReal.mul_ne_top (by simp [w,stagePotential]) (by simp [a])),
        lintegral_add_left measurable_const,lintegral_const_mul' c _ (by simp [c])]
      simp only [lintegral_const,Measure.restrict_apply_univ,one_mul]
    _ ≤ w*a*(P E+c*(ENNReal.ofReal (Real.exp (-2*t))*P E)) :=
      by gcongr; exact hd.trans hD
    _ = w*(a*(1+c*ENNReal.ofReal (Real.exp (-2*t))))*P E := by ring
    _ ≤ w*1*P E := by gcongr; exact stage_exponential_factor t
    _ = _ := by rw [mul_one]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

lemma integral_partition (A : EpisodeRecordedAtlas q J F) (hA : A.toEpisodeAtlas.IsPartition)
    (P : Measure (Environment d)) (W : Environment d → ℝ≥0∞) :
    ∫⁻ ω, W ω ∂P = ∑' l : A.Label, ∫⁻ ω in (A.chart l).event, W ω ∂P := by
  let := A.countable
  have hu : (⋃ l : A.Label, (A.chart l).event)=Set.univ :=
    Set.eq_univ_of_forall (fun ω => Set.mem_iUnion.mpr (A.cover ω))
  have hd : Pairwise (fun l m : A.Label => Disjoint (A.chart l).event (A.chart m).event) := by
    intro l m hne
    exact Set.disjoint_left.mpr (fun ω hl hm => hne (hA l m ω hl hm))
  simpa only [hu,Measure.restrict_univ] using
    lintegral_iUnion (μ:=P) (fun l => (rowSigma_le _) _ (A.chart l).measurable_event) hd W

lemma potential_advance (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (A : EpisodeRecordedAtlas q J F) (hA : A.toEpisodeAtlas.IsPartition)
    (fexp g χ b sfloor K : ℝ) (N : ℕ)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
        (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b)))) :
    ∫⁻ ω, stagePotential (K*b)
      (J ω+if EpisodeReady e f r sfloor N (q ω) then 1 else 0)
      (F ω+if EpisodeReady e f r sfloor N (q ω) ∧ episodeStageFails e f r fexp g χ b N (q ω) ω then 1 else 0)
      ∂environmentLaw ν ≤
    ∫⁻ ω, stagePotential (K*b) (J ω) (F ω) ∂environmentLaw ν := by
  rw [A.integral_partition hA,A.integral_partition hA]
  apply ENNReal.tsum_le_tsum
  intro l
  let c := A.chart l
  have hc : MeasurableSet c.event := (rowSigma_le _) _ c.measurable_event
  have hold : (∫⁻ ω in c.event, stagePotential (K*b) (J ω) (F ω) ∂environmentLaw ν) =
      stagePotential (K*b) (A.stages l) (A.failures l)*environmentLaw ν c.event := by
    rw [setLIntegral_congr_fun hc (fun ω hω => by rw [A.stages_correct l ω hω,A.failures_correct l ω hω])]
    simp only [lintegral_const,Measure.restrict_apply_univ]
  rw [hold]
  by_cases hr : c.height<N ∧ sfloor ≤ c.scale
  · have he := c.actual_failure_bound ν fexp g χ b N hr.1 (hH _ hr.2)
      (ENNReal.ofReal (Real.exp (-2*(K*b)))) (hbound _ hr.2 _) c.event c.measurable_event
    calc
      _ = ∫⁻ ω in c.event, stagePotential (K*b) (A.stages l+1)
          (A.failures l+if episodeStageFails e f r fexp g χ b N (c.state ω) ω then 1 else 0)
          ∂environmentLaw ν := by
        apply setLIntegral_congr_fun hc
        intro ω hω
        dsimp only
        rw [A.stages_correct l ω hω,A.failures_correct l ω hω,A.correct l ω hω]
        change stagePotential (K*b)
          (A.stages l+if EpisodeReady e f r sfloor N (c.state ω) then 1 else 0)
          (A.failures l+if EpisodeReady e f r sfloor N (c.state ω) ∧ episodeStageFails e f r fexp g χ b N (c.state ω) ω then 1 else 0) = _
        have hready : EpisodeReady e f r sfloor N (c.state ω) := hr
        simp only [hready,ite_true, if_true,true_and]
      _ ≤ _ := stagePotential_set_step _ _ _ hc _ _ _ he
  · calc
      _ = ∫⁻ ω in c.event, stagePotential (K*b) (A.stages l) (A.failures l)
          ∂environmentLaw ν := by
        apply setLIntegral_congr_fun hc
        intro ω hω
        dsimp only
        rw [A.stages_correct l ω hω,A.failures_correct l ω hω,A.correct l ω hω]
        change stagePotential (K*b)
          (A.stages l+if EpisodeReady e f r sfloor N (c.state ω) then 1 else 0)
          (A.failures l+if EpisodeReady e f r sfloor N (c.state ω) ∧ episodeStageFails e f r fexp g χ b N (c.state ω) ω then 1 else 0) = _
        have hready : ¬EpisodeReady e f r sfloor N (c.state ω) := hr
        simp only [hready,ite_false, if_false,false_and,add_zero]
      _ ≤ _ := by simp only [lintegral_const,Measure.restrict_apply_univ,le_refl]

end EpisodeRecordedAtlas
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodePotentialIteration
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

lemma potential_runFrom (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (A : EpisodeRecordedAtlas q J F) (hA : A.toEpisodeAtlas.IsPartition) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor K : ℝ) (N : ℕ)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
        (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b)))) (n : ℕ) :
    ∫⁻ ω, stagePotential (K*b)
      (J ω+episodeSteps e f hef r fexp g χ b sfloor N (q ω) ω n)
      (F ω+episodeCount e f hef r fexp g χ b sfloor N (q ω) ω
        (episodeStageFails e f r fexp g χ b N) n) ∂environmentLaw ν ≤
    ∫⁻ ω, stagePotential (K*b) (J ω) (F ω) ∂environmentLaw ν := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    have hh := (A.runFrom hef fexp g χ b sfloor N n).potential_advance ν
      (A.runFrom_partition hA hef fexp g χ b sfloor N n) fexp g χ b sfloor K N hH hbound
    apply le_trans _ ih
    simpa only [episodeSteps,episodeCount,Nat.add_assoc] using hh

end EpisodeRecordedAtlas

theorem actual_stage_exponential {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) (r : ℝ → ℝ)
    (fexp g χ b sfloor K : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
        (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b)))) (i : ℕ) :
    ∫⁻ ω, stagePotential (K*b)
      (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i)
      (EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
        (episodeStageFails e f r fexp g χ b N) i) ∂environmentLaw ν ≤ 1 := by
  have hc : ∀ i : ℕ, ∫⁻ ω, stagePotential (K*b)
      (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).stages
      (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).failures ∂environmentLaw ν ≤ 1 := by
    intro i
    induction i with
    | zero => simp only [episodeCounterChain,stagePotential,Nat.cast_zero,mul_zero,sub_self,Real.exp_zero,
        ENNReal.ofReal_one,lintegral_one,measure_univ,le_refl]
    | succ i ih =>
      apply le_trans _ ih
      exact (episodeCounterAtlas (k:=k) e f hef r fexp g χ b sfloor hR N i).potential_runFrom ν
        (episodeCounterAtlas_partition (k:=k) e f hef r fexp g χ b sfloor hR N i)
        hef fexp g χ b sfloor K N hH hbound N
  have he : (fun ω => stagePotential (K*b)
      (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).stages
      (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).failures) =
      (fun ω => stagePotential (K*b)
        (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i)
        (EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
          (episodeStageFails e f r fexp g χ b N) i)) := by
    funext ω
    have hh := episodeCounterChain_actual (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    rw [hh.2.2.1,hh.2.2.2]
  simpa only [he] using hc i

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

theorem actual_stage_entropy {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) (r : ℝ → ℝ)
    (fexp g χ b sfloor K : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
        (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b))))
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q] (C : ℝ) (hC : 0 ≤ C)
    (hkl : klDiv Q (environmentLaw ν) ≤ ENNReal.ofReal C) (i : ℕ) :
    K*b*(∫ ω, (EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
        (episodeStageFails e f r fexp g χ b N) i:ℝ) ∂Q) ≤ C+Real.exp (-(K*b))*
      (∫ ω, (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i:ℝ) ∂Q) := by
  let J := fun ω => (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i:ℝ)
  let F := fun ω => (EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
    (episodeStageFails e f r fexp g χ b N) i:ℝ)
  let Z := fun ω => K*b*F ω-Real.exp (-(K*b))*J ω
  have hm := EpisodeChainLedger.measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N i
  have hcast : Measurable (fun n : ℕ => (n:ℝ)) := measurable_of_countable _
  have hJ : Measurable J := hcast.comp hm.fst
  have hF : Measurable F := hcast.comp hm.snd
  have hZ : Measurable Z := (hF.const_mul _).sub (hJ.const_mul _)
  have hB : ∃ B : ℝ, ∀ ω, |Z ω| ≤ B := by
    refine ⟨(|K*b|+Real.exp (-(K*b)))*(i*N:ℕ),fun ω => ?_⟩
    have hh := EpisodeChainLedger.counts_bounded (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    have hj : |J ω| ≤ (i*N:ℕ) := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      dsimp only [J]
      exact_mod_cast hh.1
    have hf : |F ω| ≤ (i*N:ℕ) := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      dsimp only [F]
      exact_mod_cast hh.2
    calc
      |Z ω| ≤ |K*b*F ω|+|Real.exp (-(K*b))*J ω| := by
        simpa only [Z,sub_eq_add_neg,abs_neg] using abs_add_le (K*b*F ω) (-(Real.exp (-(K*b))*J ω))
      _ = |K*b| *|F ω|+Real.exp (-(K*b))*|J ω| := by
        simp only [abs_mul,abs_of_pos (Real.exp_pos _)]
      _ ≤ |K*b| *(i*N:ℕ)+Real.exp (-(K*b))*(i*N:ℕ) := by gcongr
      _ = _ := by ring
  have he := Entropy.exp_integrable_of_bounded (μ:=environmentLaw ν) hZ hB
  have hmgf := actual_stage_exponential ν e f hef r fexp g χ b sfloor K hR N hH hbound i
  have hint : (∫ ω, Real.exp (Z ω) ∂environmentLaw ν) ≤ 1 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ)≤1)).mp
    rw [ofReal_integral_eq_lintegral_ofReal he (ae_of_all _ fun ω => (Real.exp_pos _).le)]
    simpa only [stagePotential,Z,J,F,ENNReal.ofReal_one] using hmgf
  have hE := Entropy.expBudget_of_kl_le Q (environmentLaw ν) hC hkl Z hZ hB
  have hi := EpisodeChainLedger.counts_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q i
  have hze : (∫ ω, Z ω ∂Q) = K*b*(∫ ω, F ω ∂Q)-Real.exp (-(K*b))*(∫ ω, J ω ∂Q) := by
    rw [integral_sub (hi.2.const_mul _) (hi.1.const_mul _),integral_const_mul,integral_const_mul]
  rw [hze] at hE
  change K*b*(∫ ω, F ω ∂Q) ≤ C+Real.exp (-(K*b))*(∫ ω, J ω ∂Q)
  linarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episode_count_absorption (j z L b g f K D β : ℝ)
    (hj : 0 ≤ j) (hL : 0 ≤ L) (hb : 0 < b) (hg : 0 < g) (hf : 0 ≤ f) (hK : 0 < K)
    (hc : 1/g+(1+f/g)*D/K ≤ β/32)
    (hs : (1+f/g)*Real.exp (-(K*b))/(K*b) ≤ 1/2)
    (hlarge : 32*b ≤ β*L)
    (hcount : j ≤ L/(g*b)+(1+f/g)*z+1)
    (hent : K*b*z ≤ D*L+Real.exp (-(K*b))*j) :
    2*b*j ≤ β/4*L := by
  have hkb : 0 < K*b := mul_pos hK hb
  have hcf : 0 ≤ 1+f/g := by positivity
  have hz : z ≤ (D*L+Real.exp (-(K*b))*j)/(K*b) := (le_div_iff₀ hkb).mpr (by nlinarith only [hent])
  have he : L/(g*b)+(1+f/g)*((D*L+Real.exp (-(K*b))*j)/(K*b))+1 =
      (L/b)*(1/g+(1+f/g)*D/K)+((1+f/g)*Real.exp (-(K*b))/(K*b))*j+1 := by
    field_simp
    ring
  have hh : j ≤ L/(g*b)+(1+f/g)*((D*L+Real.exp (-(K*b))*j)/(K*b))+1 := by
    have hx := mul_le_mul_of_nonneg_left hz hcf
    linarith only [hcount,hx]
  rw [he] at hh
  have ht := mul_le_mul_of_nonneg_left hc (div_nonneg hL hb.le)
  have hu := mul_le_mul_of_nonneg_right hs hj
  have hh' : j/2 ≤ (L/b)*(β/32)+1 := by linarith
  have hv := mul_le_mul_of_nonneg_left hh' hb.le
  have hEq : b*((L/b)*(β/32)+1)=β*L/32+b := by field_simp
  rw [hEq] at hv
  nlinarith only [hv,hlarge]

theorem actual_expected_stages_oai {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) (r : ℝ → ℝ)
    (fexp g χ b sfloor K D β : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (hs : 1 ≤ sfloor) (hN : sfloor ≤ (N:ℝ))
    (hf : 0 ≤ fexp) (hg : 0 < g) (hb : 0 < b) (hK : 0 < K) (hD : 0 ≤ D)
    (hH : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s:ℝ))
    (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
        (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b))))
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hkl : klDiv Q (environmentLaw ν) ≤ ENNReal.ofReal (D*Real.log (N:ℝ)))
    (hc : 1/g+(1+fexp/g)*D/K ≤ β/32)
    (hsmall : (1+fexp/g)*Real.exp (-(K*b))/(K*b) ≤ 1/2)
    (hlarge : 32*b ≤ β*Real.log (N:ℝ)) :
    2*b*(∫ ω, (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω N:ℝ) ∂Q) ≤
      β/4*Real.log (N:ℝ) := by
  let J := fun ω => (EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω N:ℝ)
  let F := fun ω => (EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
    (episodeStageFails e f r fexp g χ b N) N:ℝ)
  have hi := EpisodeChainLedger.counts_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q N
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (hs.trans hN)
  have hH0 : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s := by
    intro s h
    have hp : 0 < s := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (hs.trans h)
    exact_mod_cast (mul_pos hp (Real.exp_pos _)).trans_le (hH s h)
  have he := actual_stage_entropy ν e f hef r fexp g χ b sfloor K hR N hH0 hbound Q
    (D*Real.log (N:ℝ)) (mul_nonneg hD hlog) hkl N
  have hcount : (∫ ω, J ω ∂Q) ≤ Real.log (N:ℝ)/(g*b)+(1+fexp/g)*(∫ ω, F ω ∂Q)+1 := by
    have hh := integral_mono hi.1
      (((integrable_const (Real.log (N:ℝ)/(g*b))).add (hi.2.const_mul (1+fexp/g))).add (integrable_const 1))
      (fun ω => EpisodeChainLedger.stage_count_bound (k:=k) e f hef r fexp g χ b sfloor hR N ω hs hN hf hg hb hH)
    change (∫ ω, J ω ∂Q) ≤ (∫ ω, Real.log (N:ℝ)/(g*b)+(1+fexp/g)*F ω+1 ∂Q) at hh
    have hfi : Integrable F Q := hi.2
    rw [integral_add (f:=fun ω => Real.log (N:ℝ)/(g*b)+(1+fexp/g)*F ω) (g:=fun _ => (1:ℝ))
      ((integrable_const _).add (hfi.const_mul _)) (integrable_const _),
      integral_add (f:=fun _ => Real.log (N:ℝ)/(g*b)) (g:=fun ω => (1+fexp/g)*F ω)
        (integrable_const _) (hfi.const_mul _),integral_const_mul] at hh
    simpa only [integral_const,probReal_univ,one_smul] using hh
  exact episode_count_absorption _ _ _ _ _ _ _ _ _
    (integral_nonneg (fun ω => Nat.cast_nonneg _)) hlog hb hg hf hK hc hsmall hlarge hcount he

end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.actual_expected_stages_oai := @OAI.DirectionalTransience.actual_expected_stages_oai
