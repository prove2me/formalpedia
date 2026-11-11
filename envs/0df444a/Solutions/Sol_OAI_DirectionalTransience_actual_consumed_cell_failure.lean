-- Prove2me | solution 1 for OAI.DirectionalTransience.actual_consumed_cell_failure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:57:30.515769+00:00
-- url     : https://prove2.me/submissions/2f1a9977-46fe-4ab7-8d49-0bd72d007b0f

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal006
import Theorems.Thm_OAI_DirectionalTransience_actual_late_protection_first_failure
import Theorems.Thm_OAI_DirectionalTransience_clipping_uniform
import Theorems.Thm_OAI_DirectionalTransience_separated_seeds

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FixedPairSuffix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma recordCount_integer_height {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ)) (X : Path d)
    (hstep : ∀ n, height (X (n+1)) ≤ height (X n)+1) (n : ℕ) :
    (∀ j ≤ n, height (X j) ≤ height (X 0) + (recordCount ℓ X n : ℤ)) ∧
    ∃ j ≤ n, height (X j) = height (X 0) + (recordCount ℓ X n : ℤ) := by
  classical
  induction n with
  | zero => simp [recordCount]
  | succ n ih =>
    have he : recordCount ℓ X (n+1) = recordCount ℓ X n +
      (if StrictRecord ℓ X (n+1) then 1 else 0) := recordCount_succ ℓ X n
    rw [he]
    by_cases hr : StrictRecord ℓ X (n+1)
    · rw [ite_eq_left hr]
      obtain ⟨j,hj,heq⟩ := ih.2
      have hlt := hr j (by omega)
      rw [hproj,hproj] at hlt
      have hlt' : height (X j) < height (X (n+1)) := by exact_mod_cast hlt
      have hb : height (X (n+1)) ≤ height (X 0)+(recordCount ℓ X n : ℤ)+1 := by
        have := hstep n; have := ih.1 n le_rfl; omega
      have hend : height (X (n+1)) = height (X 0)+(recordCount ℓ X n : ℤ)+1 := by omega
      constructor
      · intro k hk
        by_cases hk' : k ≤ n
        · have := ih.1 k hk'; push_cast; omega
        · have hk' : k = n+1 := by omega
          rw [hk',hend]; push_cast; omega
      · exact ⟨n+1,le_rfl,by rw [hend]; push_cast; omega⟩
    · rw [ite_eq_right hr,Nat.add_zero]
      have hb : height (X (n+1)) ≤ height (X 0)+(recordCount ℓ X n : ℤ) := by
        simp only [StrictRecord] at hr
        push Not at hr
        obtain ⟨j,hj,hj'⟩ := hr
        rw [hproj,hproj] at hj'
        have hle : height (X (n+1)) ≤ height (X j) := by exact_mod_cast hj'
        exact hle.trans (ih.1 j (by omega))
      refine ⟨fun k hk => ?_, ?_⟩
      · by_cases hk' : k ≤ n
        · exact ih.1 k hk'
        · have : k = n+1 := by omega
          simpa only [this,Nat.add_zero] using hb
      · obtain ⟨j,hj,he⟩ := ih.2
        exact ⟨j,by omega,he⟩

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordWidth
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma recordCount_eq_height_at_record {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ)) (X : Path d)
    (hstep : ∀ n, height (X (n+1)) ≤ height (X n)+1) {n : ℕ}
    (hn : StrictRecord ℓ X n) :
    height (X n) = height (X 0) + (recordCount ℓ X n : ℤ) := by
  obtain ⟨hb,j,hj,he⟩ := recordCount_integer_height ℓ height hproj X hstep n
  by_cases hjn : j = n
  · simpa only [hjn] using he
  · have hh := hn j (lt_of_le_of_ne hj hjn)
    rw [hproj,hproj] at hh
    have hlt : height (X j) < height (X n) := by exact_mod_cast hh
    have := hb n le_rfl
    omega

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_TubePrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
namespace DirectionalTransience

lemma measurableSet_tubePrefixAt {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (θ z : ℝ) (s n : ℕ) : MeasurableSet (TubePrefixAt ℓ f x θ z s n) := by
  apply (measurableSet_hitAt _ _ n).inter
  simp only [Set.ofPred_forall,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iInter; intro j
  apply MeasurableSet.iInter; intro _
  apply MeasurableSet.iUnion; intro a
  refine (MeasurableSet.const (a ≤ n)).inter ?_
  have hm : Measurable (fun X : Path d => fun k => X k-x) := by fun_prop
  have hc : Measurable (fun X : Path d => signedCoordinate f (X a-x)) :=
    (measurable_of_countable (signedCoordinate f)).comp
      ((measurable_pi_apply a : Measurable (fun X : Path d => X a)).sub_const x)
  exact ((measurableSet_recordOrZeroPrefix ℓ j a).preimage hm).inter
    (measurableSet_le ((hc.sub_const ((j:ℝ)*θ)).abs) measurable_const)

lemma measurableSet_tubePrefix {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (θ z : ℝ) (s : ℕ) : MeasurableSet (TubePrefix ℓ f x θ z s) :=
  MeasurableSet.iUnion (measurableSet_tubePrefixAt ℓ f x θ z s)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_MixtureSmallMassProbability
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
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
namespace DirectionalTransience

lemma mixture_small_mass_probability {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    (μ : Measure Ω) (π : Measure I) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (F : Ω → I → ℝ) (hF : Measurable (Function.uncurry F))
    (hF0 : ∀ ω x, 0 ≤ F ω x) (hF1 : ∀ ω x, F ω x ≤ 1)
    {δ α : ℝ} (hδ : 0 < δ)
    (hbad : ∀ x, μ.real {ω | F ω x < 2*δ} ≤ α) :
    μ.real {ω | (∫ x, F ω x ∂π) < δ} ≤ 2*α := by
  have hFw (ω : Ω) : Measurable (F ω) := hF.comp (measurable_const.prodMk measurable_id)
  have hFx (x : I) : Measurable (fun ω => F ω x) := hF.comp (measurable_id.prodMk measurable_const)
  have hBw (ω : Ω) : MeasurableSet {x | F ω x < 2*δ} := measurableSet_lt (hFw ω) measurable_const
  have hBx (x : I) : MeasurableSet {ω | F ω x < 2*δ} := measurableSet_lt (hFx x) measurable_const
  let B : Set (Ω × I) := {z | F z.1 z.2 < 2*δ}
  have hB : MeasurableSet B := hF measurableSet_Iio
  let G : Ω × I → ℝ := B.indicator (fun _ => 1)
  have hG : Measurable G := measurable_const.indicator hB
  have hG0 (z : Ω × I) : 0 ≤ G z := by by_cases h : z ∈ B <;> simp [G,h]
  have hG1 (z : Ω × I) : ‖G z‖ ≤ 1 := by by_cases h : z ∈ B <;> simp [G,h]
  have hGi : Integrable G (μ.prod π) :=
    (integrable_const (1:ℝ)).mono' hG.aestronglyMeasurable (ae_of_all _ hG1)
  let T : Ω → ℝ := fun ω => ∫ x, G (ω,x) ∂π
  have hT (ω : Ω) : T ω = π.real {x | F ω x < 2*δ} := by
    change (∫ x, ({x | F ω x < 2*δ}).indicator (fun _ => (1:ℝ)) x ∂π) = _
    rw [integral_indicator (hBw ω)]
    simp
  have hswap : (∫ ω, T ω ∂μ) = ∫ x, μ.real {ω | F ω x < 2*δ} ∂π := by
    rw [show (∫ ω, T ω ∂μ) = ∫ ω, ∫ x, G (ω,x) ∂π ∂μ from rfl,
      integral_integral_swap (f := fun ω x => G (ω,x)) hGi]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change (∫ ω, ({ω | F ω x < 2*δ}).indicator (fun _ => (1:ℝ)) ω ∂μ) = _
      rw [integral_indicator (hBx x)]
      simp
  have hmean : (∫ ω, T ω ∂μ) ≤ α := by
    rw [hswap]
    have hh := integral_mono_ae hGi.integral_prod_right (integrable_const α)
      (ae_of_all π fun x => by
        change (∫ ω, G (ω,x) ∂μ) ≤ α
        have he : (∫ ω, G (ω,x) ∂μ) = μ.real {ω | F ω x < 2*δ} := by
          change (∫ ω, ({ω | F ω x < 2*δ}).indicator (fun _ => (1:ℝ)) ω ∂μ) = _
          rw [integral_indicator (hBx x)]
          simp
        rw [he]; exact hbad x)
    have he (x : I) : (∫ ω, G (ω,x) ∂μ) = μ.real {ω | F ω x < 2*δ} := by
      change (∫ ω, ({ω | F ω x < 2*δ}).indicator (fun _ => (1:ℝ)) ω ∂μ) = _
      rw [integral_indicator (hBx x)]
      simp
    simpa only [he, integral_const, probReal_univ, one_smul] using hh
  have hinter (ω : Ω) : Integrable (F ω) π :=
    (integrable_const (1:ℝ)).mono' (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hF0 ω x)]; exact hF1 ω x)
  have hsub : {ω | (∫ x, F ω x ∂π) < δ} ⊆ {ω | (1:ℝ)/2 ≤ T ω} := by
    intro ω hsmall
    have hh := mul_meas_ge_le_integral_of_nonneg (ae_of_all π (hF0 ω)) (hinter ω) (2*δ)
    have he : {x | 2*δ ≤ F ω x} = {x | F ω x < 2*δ}ᶜ := by ext x; simp
    rw [he,measureReal_compl (hBw ω),
      probReal_univ,← hT ω] at hh
    change (1:ℝ)/2 ≤ T ω
    change (∫ x, F ω x ∂π) < δ at hsmall
    nlinarith
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω => integral_nonneg fun x => hG0 (ω,x)) hGi.integral_prod_left (1/2)
  have hm := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (μ := μ) hsub)
  change μ.real {ω | (∫ x, F ω x ∂π) < δ} ≤ μ.real {ω | (1:ℝ)/2 ≤ T ω} at hm
  change (1/2)*μ.real {ω | (1:ℝ)/2 ≤ T ω} ≤ ∫ ω, T ω ∂μ at hmark
  linarith

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_FiniteWordGeometry
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma wordFirstHitTime_zero {d : ℕ} (e : Direction d) (x : Lattice d)
    (w : List (Direction d)) : wordFirstHitTime e x 0 w = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply wordFirstHitTime_le
  simp

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TupleClipping
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma product_small_mass_probability {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    (μ : Measure Ω) (π : Measure I) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (k : ℕ) (F : Ω → I → Fin k → ℝ)
    (hF : ∀ j, Measurable (fun p : Ω × I => F p.1 p.2 j))
    (hF0 : ∀ ω x j, 0 ≤ F ω x j) (hF1 : ∀ ω x j, F ω x j ≤ 1)
    {c α : ℝ} (hc : 0 < c)
    (hbad : ∀ x j, μ.real {ω | F ω x j < c} ≤ α) :
    μ.real {ω | (∫ x, ∏ j, F ω x j ∂π) < c^k/2} ≤ 2*k*α := by
  have hb (x : I) : μ.real {ω | (∏ j, F ω x j) < 2*(c^k/2)} ≤ k*α := by
    have hs : {ω | (∏ j, F ω x j) < 2*(c^k/2)} ⊆ ⋃ j, {ω | F ω x j < c} := by
      intro ω hω
      change (∏ j, F ω x j) < 2*(c^k/2) at hω
      by_contra hn
      simp only [Set.mem_iUnion,Set.mem_ofPred_eq,not_exists,not_lt] at hn
      have hh := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin k => c)
        (g := fun j => F ω x j) (fun _ _ => hc.le) (fun j _ => hn j)
      simpa using (show c^k ≤ ∏ j, F ω x j by simpa using hh).not_gt (by linarith)
    have hh := (measureReal_mono (μ := μ) hs).trans (measureReal_iUnion_fintype_le _)
    have hh' := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hbad x j)
    simpa using hh.trans hh'
  have hh := mixture_small_mass_probability μ π (fun ω x => ∏ j, F ω x j)
    (Finset.measurable_prod _ fun j _ => hF j)
    (fun ω x => Finset.prod_nonneg fun j _ => hF0 ω x j)
    (fun ω x => Finset.prod_le_one (fun j _ => hF0 ω x j) (fun j _ => hF1 ω x j))
    (show 0 < c^k/2 by positivity) hb
  simpa only [mul_assoc] using hh

lemma measurable_tupleTube_integrand {d k : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z : ℝ) (H : ℕ) (j : Fin k) :
    Measurable (fun p : Environment d × (Fin k → Lattice d) =>
      (quenchedKernel (p.1,p.2 j)).real (TubePrefix ℓ f (p.2 j) θ z H)) := by
  apply Measurable.ennreal_toReal
  apply measurable_from_prod_countable_left
  intro x
  exact (Kernel.measurable_coe _ (measurableSet_tubePrefix ℓ f (x j) θ z H)).comp
    (measurable_id.prodMk measurable_const)

theorem initial_tuple_clipping {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∃ θ : ℝ,
      ∀ (H : ℕ) (π : Measure (Fin k → Lattice d)), IsProbabilityMeasure π →
      (H:ℝ) ≤ T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      (environmentLaw ν).real {ω | tupleTubeMass (realPosition (step e)) f θ (η*r) H π ω < c} < ε := by
  let α := ε/(4*((k:ℝ)+1))
  have hα : 0 < α := by dsimp [α] <;> positivity
  obtain ⟨c,hc,hc1,R,hR,hh⟩ := clipping_uniform ν hue e f hef htrans hT hη hα
  have hcfin : c ≠ ∞ := ne_top_of_le_ne_top (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hc1
  have hcr : 0 < c.toReal := ENNReal.toReal_pos (ne_of_gt hc) hcfin
  refine ⟨c.toReal^k/2,by positivity,R,hR,fun r hr => ?_⟩
  obtain ⟨θ,hθ⟩ := hh r hr
  refine ⟨θ,fun H π hπ hH => ?_⟩
  let := hπ
  have hb (x : Fin k → Lattice d) (j : Fin k) :
      (environmentLaw ν).real {ω | (quenchedKernel (ω,x j)).real
        (TubePrefix (realPosition (step e)) f (x j) θ (η*r) H) < c.toReal} ≤ α := by
    have he : {ω | (quenchedKernel (ω,x j)).real
        (TubePrefix (realPosition (step e)) f (x j) θ (η*r) H) < c.toReal} =
      {ω | quenchedKernel (ω,x j) (TubePrefix (realPosition (step e)) f (x j) θ (η*r) H) < c} := by
      ext ω
      exact ENNReal.toReal_lt_toReal (measure_ne_top _ _) hcfin
    rw [he]
    exact (hθ (x j) H hH).le
  have he := product_small_mass_probability (environmentLaw ν) π k
    (fun ω x j => (quenchedKernel (ω,x j)).real (TubePrefix (realPosition (step e)) f (x j) θ (η*r) H))
    (measurable_tupleTube_integrand _ _ _ _ _)
    (fun _ _ _ => ENNReal.toReal_nonneg) (fun _ _ _ => by exact ENNReal.toReal_mono (by simp) (show _ ≤ (1:ℝ≥0∞) from prob_le_one)) hcr hb
  change (environmentLaw ν).real {ω | tupleTubeMass _ _ θ (η*r) H π ω < c.toReal^k/2} ≤ 2*k*α at he
  apply lt_of_le_of_lt he
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  dsimp [α]
  rw [←mul_div_assoc,div_lt_iff₀ (by positivity)]
  nlinarith
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetClipping
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma signedHeight_sub' {d : ℕ} (e : Direction d) (x y : Lattice d) :
    signedHeight e (x-y) = signedHeight e x-signedHeight e y := by
  simp only [signedHeight,Pi.sub_apply]
  split <;> ring

lemma recordOrZeroPrefix_wordFirstHit {d : ℕ} (e : Direction d) (x : Lattice d)
    (X : Path d) (h0 : X 0 = x) (hnn : ∀ n, ∃ f, X (n+1)=X n+step f)
    (w : List (Direction d)) (hw : X ∈ wordCylinder x w) (s a : ℕ)
    (ha : a ≤ w.length)
    (hrec : (fun n => X n-x) ∈ RecordOrZeroPrefix (realPosition (step e)) s a) :
    wordFirstHitTime e x s w = a := by
  by_cases hs : s=0
  · subst s
    have ha0 : a=0 := by simpa [RecordOrZeroPrefix] using hrec
    rw [ha0,wordFirstHitTime_zero]
  · have hr : (fun n => X n-x) ∈ RecordIndexPrefix (realPosition (step e)) s a := by
      simpa only [RecordOrZeroPrefix,ite_eq_right hs] using hrec
    have hstep (n : ℕ) : signedHeight e (X (n+1)-x) ≤ signedHeight e (X n-x)+1 := by
      obtain ⟨g,hg⟩ := hnn n
      rw [signedHeight_sub',signedHeight_sub',hg]
      have hh := signedHeight_step_le e (X n) g
      omega
    have ht := recordCount_eq_height_at_record (realPosition (step e)) (signedHeight e)
      (signedHeight_projection e) (fun n => X n-x) hstep hr.2.1
    have hheight : signedHeight e (X a) = signedHeight e x+s := by
      rw [hr.2.2.1,h0,sub_self] at ht
      simp only [signedHeight_sub'] at ht
      have hz : signedHeight e (0 : Lattice d)=0 := by simp [signedHeight]
      rw [hz] at ht
      omega
    have hwa : signedHeight e x+s ≤ signedHeight e (wordPath x w a) := by
      rw [← hw a ha,hheight]
    apply le_antisymm (wordFirstHitTime_le e x s w hwa)
    by_contra hn
    have hn' : wordFirstHitTime e x s w < a := by omega
    have hlt := hr.2.1 _ hn'
    simp only [signedHeight_projection,signedHeight_sub'] at hlt
    have hlt' : signedHeight e (X (wordFirstHitTime e x s w)) < signedHeight e (X a) := by
      have hh : signedHeight e (X (wordFirstHitTime e x s w))-signedHeight e x <
          signedHeight e (X a)-signedHeight e x := by exact_mod_cast hlt
      omega
    rw [hw _ (hn'.le.trans ha),hheight] at hlt'
    exact hlt'.not_ge (wordFirstHitTime_spec e x s w ⟨a,hwa⟩)

lemma tubePrefix_word_budget {d : ℕ} (e f : Direction d) (x : Lattice d)
    (X : Path d) (h0 : X 0=x) (hnn : ∀ n, ∃ g, X (n+1)=X n+step g)
    (H : ℕ) (θ z : ℝ)
    (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H))
    (hw : X ∈ wordCylinder x w.val)
    (ht : X ∈ TubePrefix (realPosition (step e)) f x θ z H) :
    CentralWordBudget e f x H θ z w.val := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ht
  have hp := hitWord_prefix x _ _ w hw
  have hlen : n=w.val.length := by
    by_contra hne
    exact Set.disjoint_left.mp (hitAt_pairwise_disjoint (disjoint_strip_upper _ _ _) hne) hn.1 hp
  intro s hs
  obtain ⟨a,ha,hrec,hgood⟩ := hn.2 s hs
  rw [hlen] at ha
  have he := recordOrZeroPrefix_wordFirstHit e x X h0 hnn w.val hw s a ha hrec
  simpa only [relativeWordDisplacement,wordFirstHitPosition,he,← hw a ha] using hgood

lemma tubePrefix_le_centralWordBudget {d : ℕ} (e f : Direction d) (x : Lattice d)
    (ω : Environment d) (H : ℕ) (θ z : ℝ) :
    quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ z H) ≤
      rawWordLaw (realPosition (step e)) H ω x {w | CentralWordBudget e f x H θ z w} := by
  rw [rawWordLaw,Measure.map_apply measurable_subtype_coe (Set.to_countable _).measurableSet,
    successfulWordLaw_event ω x _ _ (disjoint_strip_upper _ _ _)]
  apply measure_mono_ae
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  intro ht
  have hh : X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) := by
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ht
    exact Set.mem_iUnion.mpr ⟨n,hn.1⟩
  obtain ⟨w,hw⟩ := (hitWord_cover x _ _ X h0 hnn).mp hh
  exact Set.mem_iUnion.mpr ⟨⟨w,tubePrefix_word_budget e f x X h0 hnn H θ z w hw ht⟩,hw⟩

lemma tupleCentral_budget {d k : ℕ} (e f : Direction d) (x : Fin k → Lattice d)
    (H : ℕ) (θ z : ℝ) (w : Fin k → List (Direction d))
    (hw : ∀ j, CentralWordBudget e f (x j) H θ z (w j)) :
    TupleRelativeBudget e f x H (2*z) w := by
  intro s hs i j
  calc
    _ = |(relativeWordDisplacement e f (x i) s (w i)-(s:ℝ)*θ)-
      (relativeWordDisplacement e f (x j) s (w j)-(s:ℝ)*θ)| := by congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (by linarith [hw i s hs,hw j s hs])

lemma tupleTubeMass_le_relativeBudget {d k : ℕ} (e f : Direction d)
    (H : ℕ) (θ z : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    (∏ j, quenchedKernel (ω,x j) (TubePrefix (realPosition (step e)) f (x j) θ z H)) ≤
      relativeBudgetWordLaw e f H (2*z) ω x Set.univ := by
  rw [relativeBudgetWordLaw,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
  calc
    _ ≤ ∏ j, rawWordLaw (realPosition (step e)) H ω (x j)
        {w | CentralWordBudget e f (x j) H θ z w} := by
      exact Finset.prod_le_prod' fun j _ => tubePrefix_le_centralWordBudget e f (x j) ω H θ z
    _ = rawTupleWordLaw (realPosition (step e)) H ω x
        {w | ∀ j, CentralWordBudget e f (x j) H θ z (w j)} := by
      symm
      simpa only [rawTupleWordLaw,Set.pi,Set.mem_univ,forall_true_left,Set.mem_ofPred_eq] using
        Measure.pi_pi (fun j => rawWordLaw (realPosition (step e)) H ω (x j))
          (fun j => {w | CentralWordBudget e f (x j) H θ z w})
    _ ≤ _ := measure_mono fun _ hw => tupleCentral_budget e f x H θ z _ hw

lemma tupleTubeMass_le_relativeBudgetMass {d k : ℕ} (e f : Direction d)
    (H : ℕ) (θ z : ℝ) (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π]
    (ω : Environment d) :
    tupleTubeMass (realPosition (step e)) f θ z H π ω ≤ relativeBudgetMass e f H (2*z) π ω := by
  apply integral_mono
  · apply (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.prod_nonneg fun _ _ => measureReal_nonneg)]
    exact Finset.prod_le_one (fun _ _ => measureReal_nonneg) (fun _ _ => measureReal_le_one)
  · apply (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top (relativeBudgetWordLaw_le_one e f H (2*z) ω x)).trans_eq ENNReal.toReal_one
  · intro x
    have hh := ENNReal.toReal_mono (measure_ne_top (relativeBudgetWordLaw e f H (2*z) ω x) _)
      (tupleTubeMass_le_relativeBudget e f H θ z ω x)
    simpa only [ENNReal.toReal_prod,Measure.real] using hh

theorem initial_relativeBudget_clipping {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r →
      ∀ (H : ℕ) (π : Measure (Fin k → Lattice d)), IsProbabilityMeasure π →
      (H:ℝ) ≤ T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      (environmentLaw ν).real {ω | relativeBudgetMass e f H (η*r) π ω < c} < ε := by
  obtain ⟨c,hc,R,hR,hh⟩ := initial_tuple_clipping ν hue e f hef htrans k hT
    (show 0<η/2 by positivity) hε
  refine ⟨c,hc,R,hR,fun r hr H π hπ hH => ?_⟩
  let := hπ
  obtain ⟨θ,hθ⟩ := hh r hr
  have he : 2*(η/2*r)=η*r := by ring
  apply lt_of_le_of_lt (measureReal_mono (μ := environmentLaw ν) ?_) (hθ H π hπ hH)
  intro ω hω
  exact (he ▸ tupleTubeMass_le_relativeBudgetMass e f H θ (η/2*r) π ω).trans_lt hω

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetAdapted
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

end DirectionalTransience

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetMeasurable
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_StageSeedProfile
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedSeparatedRaw_univ {d k : ℕ} (e f : Direction d) (H : ℕ) (G : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    seedSeparatedRaw e f H G π ω Set.univ=
      rawTupleMixture (realPosition (step e)) H π ω {y | TupleSeparated f G y} := by
  simp [seedSeparatedRaw]

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

lemma fresh_layer_profile_event_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (a : ℝ) {D : Type*} [MeasurableSpace D]
    (b : D → Environment d → ℝ≥0∞)
    (hb : @Measurable (D×Environment d) ℝ≥0∞
      (MeasurableSpace.prod inferInstance
        (rowSigma {y | a≤dot (realPosition y) (realPosition (step e))})) _
      (fun p => b p.1 p.2))
    (π : Environment d → D)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A)
    (g c : ℝ≥0∞) (hbound : ∀ η∈A, environmentLaw ν {ω | b (π η) ω<g} ≤ c) :
    environmentLaw ν (A∩{ω | b (π ω) ω<g}) ≤ c*environmentLaw ν A := by
  apply fresh_layer_diagonal_bound ν e a A hA {p | b (π p.1) p.2<g} _ c hbound
  exact measurableSet_lt (hb.comp ((hπ.comp measurable_fst).prodMk measurable_snd)) measurable_const

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma seedSeparatedMass_joint_upper {d k : ℕ} (e f : Direction d) (a G : ℝ) (H : ℕ) :
    @Measurable (LayerTupleProfile (k:=k) e a×Environment d) ℝ≥0∞
      (@Prod.instMeasurableSpace _ _ inferInstance
        (rowSigma {y | a≤dot (realPosition y) (realPosition (step e))})) _
      (fun p => seedSeparatedRaw e f H G p.1.val p.2 Set.univ) := by
  apply (Measure.measurable_coe MeasurableSet.univ).comp
  apply seedSeparatedRaw_joint_rows
  intro x hx j y hy
  change a≤dot (realPosition y) (realPosition (step e))
  simpa only [hx j] using hy.1

lemma fresh_random_seed_failure {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a G : ℝ) (H : ℕ) (g : ℝ≥0∞)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A)
    (c : ℝ≥0∞)
    (hbound : ∀ η∈A, environmentLaw ν {ω | seedSeparatedRaw e f H G (π η).val ω Set.univ<g} ≤ c) :
    environmentLaw ν (A∩{ω | seedSeparatedRaw e f H G (π ω).val ω Set.univ<g}) ≤ c*environmentLaw ν A := by
  exact fresh_layer_profile_event_bound ν e a (D:=LayerTupleProfile (k:=k) e a)
    (fun (p : LayerTupleProfile (k:=k) e a) ω => seedSeparatedRaw e f H G p.val ω Set.univ)
    (seedSeparatedMass_joint_upper (k:=k) e f a G H) π hπ A hA g c hbound

lemma seedSeparatedRaw_measurable {d k : ℕ} (e f : Direction d) (H : ℕ) (G a : ℝ)
    (π : LayerTupleProfile (k:=k) e a) : Measurable (fun ω => seedSeparatedRaw e f H G π.val ω) := by
  have hh := seedSeparatedRaw_joint_rows (k:=k) e f H G a Set.univ (fun _ _ _ => Set.subset_univ _)
  exact (hh.comp (measurable_const.prodMk measurable_id)).mono (rowSigma_le _) le_rfl

theorem adapted_separated_seeds {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) (hk : 2≤k) (p : ℝ) (hp : 0<p) :
    ∃ C c₀ g₀ : ℝ, 0<C ∧ 0 < c₀ ∧ 0<g₀ ∧ ∃ H₀ : ℕ, ∀ H≥H₀,
      ∀ (a : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a),
        @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
      ∀ A : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A →
        environmentLaw ν (A∩{ω | seedSeparatedRaw e f H
          (c₀*fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) ((H:ℝ)/C))
          (π ω).val ω Set.univ<ENNReal.ofReal g₀})≤ENNReal.ofReal p*environmentLaw ν A := by
  obtain ⟨C,c₀,g₀,hC,hc,hg,H₀,hh⟩ := separated_seeds ν hue e f hef htrans k hk p hp
  refine ⟨C,c₀,g₀,hC,hc,hg,H₀,fun H hH a π hπ A hA => ?_⟩
  apply fresh_random_seed_failure ν e f a _ H _ π hπ A hA (ENNReal.ofReal p)
  intro η _
  have hs := hh H hH ⟨(π η).val,(π η).property.1⟩
  let G := c₀*fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) ((H:ℝ)/C)
  have hm : MeasurableSet {ω | seedSeparatedRaw e f H G (π η).val ω Set.univ<ENNReal.ofReal g₀} :=
    measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp
      (seedSeparatedRaw_measurable e f H G a (π η))) measurable_const
  have he : {ω | ENNReal.ofReal g₀ ≤ rawTupleMixture (realPosition (step e)) H (π η).val ω {v | TupleSeparated f G v}} =
      {ω | seedSeparatedRaw e f H G (π η).val ω Set.univ<ENNReal.ofReal g₀}ᶜ := by
    ext ω; simp only [Set.mem_ofPred_eq,Set.mem_compl_iff,not_lt,seedSeparatedRaw_univ]
  change 1-p < (environmentLaw ν).real {ω | ENNReal.ofReal g₀ ≤ rawTupleMixture (realPosition (step e)) H (π η).val ω {v | TupleSeparated f G v}} at hs
  rw [he,measureReal_compl hm,probReal_univ] at hs
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  linarith

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_CellSeedParameters
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedSeparatedRaw_mass_antitone {d k : ℕ} (e f : Direction d) (H : ℕ)
    {G F : ℝ} (hGF : G≤F) (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    seedSeparatedRaw e f H F π ω Set.univ ≤ seedSeparatedRaw e f H G π ω Set.univ := by
  rw [seedSeparatedRaw_univ,seedSeparatedRaw_univ]
  exact measure_mono (fun x hx => tupleSeparated_mono f hGF x hx)

theorem adapted_separated_seeds_capped {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) (hk : 2≤k) (p : ℝ) (hp : 0<p) :
    ∃ C c₀ g₀ : ℝ, 0<C ∧ 0 < c₀ ∧ c₀≤1 ∧ 0<g₀ ∧ ∃ H₀ : ℕ, ∀ H≥H₀,
      ∀ (a : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a),
        @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
      ∀ A : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] A →
        environmentLaw ν (A∩{ω | seedSeparatedRaw e f H
          (c₀*fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) ((H:ℝ)/C))
          (π ω).val ω Set.univ<ENNReal.ofReal g₀})≤ENNReal.ofReal p*environmentLaw ν A := by
  obtain ⟨C,c,g,hC,hc,hg,H₀,hh⟩ := adapted_separated_seeds ν hue e f hef htrans k hk p hp
  refine ⟨C,min c 1,g,hC,lt_min hc (by norm_num),min_le_right _ _,hg,H₀,?_⟩
  intro H hH a π hπ A hA
  apply le_trans (measure_mono ?_) (hh H hH a π hπ A hA)
  rintro ω ⟨hA,hfail⟩
  refine ⟨hA,?_⟩
  change seedSeparatedRaw e f H _ (π ω).val ω Set.univ < _
  exact lt_of_le_of_lt (seedSeparatedRaw_mass_antitone e f H
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (fluctuationRadius_pos _ _ _).le) _ _) hfail

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_FreshClipping
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

theorem adapted_initial_clipping {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) {T η ε : ℝ} (hT : 0<T) (hη : 0<η) (hε : 0<ε) :
    ∃ g : ℝ, 0<g ∧ ∃ R : ℝ, 0<R ∧ ∀ ρ : ℝ, R≤ρ →
      ∀ H : ℕ, (H:ℝ)≤T*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) ρ →
      ∀ (a G : ℝ) (π : Environment d → BudgetProfile (k:=k) e f a G),
      @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
      ∀ E : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] E →
        environmentLaw ν (E∩{ω | relativeBudgetMass e f H (η*ρ) (π ω).val ω<g})≤
          ENNReal.ofReal ε*environmentLaw ν E := by
  obtain ⟨g,hg,R,hR,hh⟩ := initial_relativeBudget_clipping ν hue e f hef htrans k hT hη hε
  refine ⟨g,hg,R,hR,fun ρ hρ H hH a G π hπ E hE => ?_⟩
  apply fresh_random_budget_mass_lt ν e f a G (η*ρ) g H π hπ E hE (ENNReal.ofReal ε)
  intro θ _
  have h := hh ρ hρ H (π θ).val (π θ).property.1 hH
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h.le

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellAttempt
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

lemma cellEarlyProfile_measurable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G : ℝ) (hG : 0 ≤ G) (Hs He : ℕ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He))) _
      (cellEarlyProfile e f hef a G hG Hs He π) := by
  let : MeasurableSpace (Environment d) :=
    rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He))
  have hm := nextBudgetProfile_measurable_below e f (a+Hs) G (G/4) (by positivity) He
    (fun ω => seedSeparatedProfile e f hef a G Hs (π ω) ω)
    (seedSeparatedProfile_measurable e f hef a G Hs π hπ)
  exact (measurable_subtype_coe.comp hm).subtype_mk

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellFailure
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma cellLateInitial_measurable {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (a c ρ : ℝ) (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (Hs He : ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a)
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He))) _
      (cellLateInitial e f hef a c ρ hc hρ Hs He π) := by
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He))
  exact (measurable_subtype_coe.comp
    (cellEarlyProfile_measurable e f hef a (c*ρ) (mul_nonneg hc hρ) Hs He π hπ)).subtype_mk

lemma triple_exp_failure {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    3*Real.exp (-5*(k:ℝ)*n)  ≤  Real.exp (-2*(k:ℝ)*n) := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hkn : 1 ≤ (k:ℝ)*n := one_le_mul_of_one_le_of_one_le hk' hn'
  have hh : 3 ≤ Real.exp (3*(k:ℝ)*n) := by
    have ht := Real.add_one_le_exp (3*(k:ℝ)*n)
    nlinarith only [hkn,ht]
  calc
    _  ≤  Real.exp (3*(k:ℝ)*n)*Real.exp (-5*(k:ℝ)*n) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

lemma consumedCellFailure_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (seed : Ω → ℝ≥0∞) (early : Ω → ℝ) (q : ℕ → Ω → ℝ)
    (g₀ g₁ kA : ℝ) (s m n k : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (E : Set Ω)
    (hseed : μ (E∩{ω | seed ω < ENNReal.ofReal g₀}) ≤ ENNReal.ofReal (Real.exp (-6*(k:ℝ)))*μ E)
    (hearly : μ (E∩{ω | early ω < g₁}) ≤ ENNReal.ofReal (Real.exp (-6*(k:ℝ)*s))*μ E)
    (hlate : s  <  n → n  ≤  m → μ (E∩firstProtectionFailure q kA s (n-s-1)) ≤
      ENNReal.ofReal (Real.exp (-5*(k:ℝ)*n))*μ E) :
    μ (E∩consumedCellFailure seed early q g₀ g₁ kA s m n) ≤
      ENNReal.ofReal (Real.exp (-2*(k:ℝ)*n))*μ E := by
  let b := ENNReal.ofReal (Real.exp (-5*(k:ℝ)*n))*μ E
  have hs : μ (E∩{ω | n=1 ∧ seed ω < ENNReal.ofReal g₀}) ≤ b := by
    by_cases he : n=1
    · subst n
      calc
        _ ≤ μ (E∩{ω | seed ω < ENNReal.ofReal g₀}) :=
          measure_mono (fun ω hω => ⟨hω.1,hω.2.2⟩)
        _ ≤ ENNReal.ofReal (Real.exp (-6*(k:ℝ)))*μ E := hseed
        _ ≤ b := by
          dsimp [b]
          apply mul_le_mul_left
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          simp only [Nat.cast_one,mul_one]
          linarith [Nat.cast_nonneg (α:=ℝ) k]
    · simp [he,b]
  have he : μ (E∩{ω | n=min s m ∧ ENNReal.ofReal g₀ ≤ seed ω ∧ early ω < g₁}) ≤ b := by
    by_cases hnm : n=min s m
    · have hns : n ≤ s := hnm ▸ min_le_left _ _
      have hns' : (n:ℝ) ≤ s := by exact_mod_cast hns
      calc
        _ ≤ μ (E∩{ω | early ω < g₁}) :=
          measure_mono (fun ω hω => ⟨hω.1,hω.2.2.2⟩)
        _ ≤ ENNReal.ofReal (Real.exp (-6*(k:ℝ)*s))*μ E := hearly
        _ ≤ b := by
          dsimp [b]
          apply mul_le_mul_left
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
          nlinarith [mul_le_mul_of_nonneg_left hns' (Nat.cast_nonneg (α:=ℝ) k),
            mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) hn0]
    · simp [hnm,b]
  have hl : μ (E∩{ω | s < n ∧ n ≤ m ∧ ENNReal.ofReal g₀ ≤ seed ω ∧ g₁ ≤ early ω ∧
      ω∈firstProtectionFailure q kA s (n-s-1)}) ≤ b := by
    by_cases hs : s < n
    · by_cases hm : n ≤ m
      · calc
          _ ≤ μ (E∩firstProtectionFailure q kA s (n-s-1)) :=
            measure_mono (fun ω hω => ⟨hω.1,hω.2.2.2.2.2⟩)
          _ ≤ b := hlate hs hm
      · simp [hm,b]
    · simp [hs,b]
  have ht : μ (E∩consumedCellFailure seed early q g₀ g₁ kA s m n) ≤ b+b+b := by
    unfold consumedCellFailure
    rw [Set.inter_union_distrib_left,Set.inter_union_distrib_left]
    exact (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add hs he)) hl)
  apply ht.trans
  dsimp [b]
  rw [←add_mul,←add_mul,←ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
    ←ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  convert triple_exp_failure hk hn using 1
  all_goals try with_reducible_and_instances rfl
  ring

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_Cell
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma belowHeight_add_nat_mono {d : ℕ} (e : Direction d) (a : ℝ) (n : ℕ) :
    rowSigma (BelowHeight (realPosition (step e)) a) ≤
      rowSigma (BelowHeight (realPosition (step e)) (a+n)) := by
  apply rowSigma_mono
  intro x hx
  change dot (realPosition x) (realPosition (step e)) < a+n
  exact lt_of_lt_of_le hx (le_add_of_nonneg_right (Nat.cast_nonneg n))

theorem actual_consumed_cell_failure_oai {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ k : ℕ, 2 ≤ k →
      ∃ C c g₀ g₁ : ℝ, 0 < C ∧ ∃ hc : 0 < c, c ≤ 1 ∧ 0 < g₀ ∧ 0 < g₁ ∧
      ∃ s H₀ : ℕ, 0 < s ∧ ∀ Bstar : ℝ, 0 < Bstar → ∃ R : ℝ, 0 < R ∧
      ∀ Hs ≥ H₀, ∀ (ρ : ℝ) (hρ : 0 < ρ), R ≤ ρ →
        ρ = fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) ((Hs:ℝ)/C) →
      ∀ He : ℕ, (He:ℝ) ≤ 3*C*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) ρ →
      ∀ H : ℕ → ℕ, (∀ i, (H i:ℝ) ≤ 3*C*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) ρ/(16:ℝ)^(s+i)) →
      ∀ m : ℕ, (2*A*k)*m ≤ Bstar → ∀ n : ℕ, 1 ≤ n → n ≤ m →
      ∀ (a : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a),
        @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
      ∀ E : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] E →
        environmentLaw ν (E∩consumedCellFailure
          (cellSeedMass e f a (c*ρ) Hs π) (cellEarlyMass e f hef a (c*ρ) Hs He π)
          (cellLateMass e f hef a c ρ hc hρ Hs He s H π) g₀ g₁ (A*k) s m n) ≤
            ENNReal.ofReal (Real.exp (-2*k*n))*environmentLaw ν E := by
  obtain ⟨lam,Cmg,hlam,hlam1,hCmg,hlate⟩ :=
    actual_late_protection_first_failure ν hue e f hef htrans
  let A := max 1 (4*(Cmg+8)/lam)
  have hA : 1 ≤ A := le_max_left _ _
  have hchoice : Cmg+8 ≤ (lam/4)*A := by
    have h := le_max_right 1 (4*(Cmg+8)/lam)
    have hh := (div_le_iff₀ hlam).mp h
    dsimp [A]
    nlinarith only [hh]
  refine ⟨A,hA,fun k hk => ?_⟩
  obtain ⟨C,c,g₀,hC,hc,hc1,hg₀,H₀,hseed⟩ := adapted_separated_seeds_capped
    ν hue e f hef htrans k hk (Real.exp (-6*k)) (Real.exp_pos _)
  obtain ⟨s,hs,hsbound⟩ := hlate A hA hchoice k hk c C hc hc1 hC
  obtain ⟨g₁,hg₁,R₁,hR₁,hearly⟩ := adapted_initial_clipping ν hue e f hef htrans k
    (show 0 < 3*C by positivity) (show 0 < c/4 by positivity)
    (Real.exp_pos (-6*k*s))
  refine ⟨C,c,g₀,g₁,hC,hc,hc1,hg₀,hg₁,s,H₀,hs,fun Bstar hB => ?_⟩
  obtain ⟨R₂,hR₂,hb⟩ := hsbound Bstar hB
  refine ⟨max R₁ R₂,hR₁.trans_le (le_max_left _ _),?_⟩
  intro Hs hHs ρ hρ hρR hρeq He hHe H hH m hm n hn hnm a π hπ E hE
  have hr1 : R₁ ≤ ρ := (le_max_left _ _).trans hρR
  have hr2 : R₂ ≤ ρ := (le_max_right _ _).trans hρR
  apply consumedCellFailure_bound (environmentLaw ν) _ _ _ g₀ g₁ (A*k) s m n k (by omega) hn E
  · simpa only [cellSeedMass,hρeq] using hseed Hs hHs a π hπ E hE
  · have hEs : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+Hs))] E :=
      belowHeight_add_nat_mono e a Hs E hE
    have hh := hearly ρ hr1 He hHe (a+Hs) (c*ρ)
      (fun ω => seedSeparatedProfile e f hef a (c*ρ) Hs (π ω) ω)
      (seedSeparatedProfile_measurable e f hef a (c*ρ) Hs π hπ) E hEs
    have heq : (c/4)*ρ=(c*ρ)/4 := by ring
    simpa only [heq,cellEarlyMass] using hh
  · intro hsn hnm'
    have heq : s+(n-s-1)+1=n := by omega
    have heq' : (s:ℝ)+((n-s-1:ℕ):ℝ)+1=n := by exact_mod_cast heq
    have ht : (2*A*k)*((s:ℝ)+((n-s-1:ℕ):ℝ)+1) ≤ Bstar := by
      rw [heq']
      exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hnm') (by positivity)).trans hm
    have hEl : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+Hs+He))] E :=
      belowHeight_add_nat_mono e (a+Hs) He E (belowHeight_add_nat_mono e a Hs E hE)
    have hh := hb ρ hr2 (n-s-1) ht H (fun i _ => hH i) (a+Hs+He)
      (cellLateInitial e f hef a c ρ hc.le hρ.le Hs He π)
      (cellLateInitial_measurable e f hef a c ρ hc.le hρ.le Hs He π hπ) E hEl
    simpa only [cellLateMass,heq'] using hh

end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.actual_consumed_cell_failure_oai := @OAI.DirectionalTransience.actual_consumed_cell_failure_oai
