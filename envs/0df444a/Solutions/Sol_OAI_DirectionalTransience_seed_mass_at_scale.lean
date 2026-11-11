-- Prove2me | solution 1 for OAI.DirectionalTransience.seed_mass_at_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:56:54.402657+00:00
-- url     : https://prove2.me/submissions/2bb49cfe-f983-4342-80de-87a7488b07fb

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal007
import Theorems.Thm_OAI_DirectionalTransience_seed_block_tests

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentRandomTestBound
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightSlab
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_CoordinateKernelComp
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma measurable_rawTupleEndpointLaw {d k : ℕ} (ℓ : Vector d) (H : ℕ) :
    Measurable (fun p : Environment d × (Fin k → Lattice d) => rawTupleEndpointLaw ℓ H p.1 p.2) := by
  apply TupleKernel.measurable_countable_measure
  intro y
  simp_rw [rawTupleEndpointLaw_singleton]
  apply Finset.measurable_prod
  intro j _
  exact (Kernel.measurable_coe (variableHitKernel ℓ H) (measurableSet_singleton _)).comp
    (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetNormalize
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

lemma normalizeOr_mass {α : Type*} [MeasurableSpace α] (μ ρ : Measure α)
    [IsFiniteMeasure μ] : μ Set.univ • normalizeOr μ ρ = μ := by
  by_cases h : μ Set.univ=0
  · rw [h,zero_smul]; exact (Measure.measure_univ_eq_zero.mp h).symm
  · rw [normalizeOr,ite_eq_right h,mass_smul_normalizedMeasure]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedMedian
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma selectedIntegerMedian_spec (μ : ProbabilityMeasure ℤ) :
    IsIntegerMedian μ.toMeasure (selectedIntegerMedian μ) :=
  Nat.find_spec (exists_nat_integerMedian μ)

lemma measurable_selectedIntegerMedian : Measurable selectedIntegerMedian := by
  apply (measurable_of_countable (fun n => (Encodable.decode (α:=ℤ) n).getD 0)).comp
  apply measurable_find exists_nat_integerMedian
  intro n
  exact (measurableSet_le measurable_const
    ((Measure.measurable_coe (Set.to_countable _).measurableSet).comp measurable_subtype_coe)).inter
    (measurableSet_le measurable_const
      ((Measure.measurable_coe (Set.to_countable _).measurableSet).comp measurable_subtype_coe))

lemma measurable_orientedIntegerLaw {d : ℕ} (f : Direction d) (s : ℤ) :
    Measurable (orientedIntegerLaw f s) := by
  exact ((Measure.measurable_map _ (measurable_of_countable _)).comp measurable_subtype_coe).subtype_mk

lemma measurable_seedMedian {d : ℕ} (f : Direction d) (s : ℤ) : Measurable (seedMedian f s) :=
  measurable_selectedIntegerMedian.comp (measurable_orientedIntegerLaw f s)

lemma seedHalfRaw_mass {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) :
    (1/2:ℝ≥0∞) ≤ seedHalfRaw f s upper μ Set.univ := by
  have h := selectedIntegerMedian_spec (orientedIntegerLaw f s μ)
  change (1/2:ℝ≥0∞) ≤ μ.toMeasure.map (fun x => s*signedHeight f x)
    (Set.Iic (seedMedian f s μ)) ∧ (1/2:ℝ≥0∞) ≤ μ.toMeasure.map (fun x => s*signedHeight f x)
    (Set.Ici (seedMedian f s μ)) at h
  rw [Measure.map_apply (measurable_of_countable _) measurableSet_Iic,
    Measure.map_apply (measurable_of_countable _) measurableSet_Ici] at h
  cases upper
  · simpa [seedHalfRaw,Set.preimage,Set.Iic] using h.1
  · simpa [seedHalfRaw,Set.preimage,Set.Ici] using h.2

lemma measurable_seedHalfRaw {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool) :
    Measurable (seedHalfRaw f s upper) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  have hfun : Measurable (fun p : ProbabilityMeasure (Lattice d) × ℤ =>
      p.1.toMeasure (U ∩ {x | if upper then p.2 ≤ s*signedHeight f x else s*signedHeight f x ≤ p.2})) := by
    apply measurable_from_prod_countable_left
    intro j
    exact (Measure.measurable_coe (Set.to_countable
      (U ∩ {x : Lattice d | if upper then j ≤ s*signedHeight f x else s*signedHeight f x ≤ j})).measurableSet).comp measurable_subtype_coe
  simpa only [seedHalfRaw,Measure.restrict_apply hU,Function.comp_def,id_eq] using
    hfun.comp (measurable_id.prodMk (measurable_seedMedian f s))

lemma measurable_seedHalf {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool) :
    Measurable (seedHalf f s upper) :=
  (measurable_normalizeOr _ _ (measurable_seedHalfRaw f s upper) measurable_subtype_coe).subtype_mk

lemma seedHalf_domination {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) :
    (1/2:ℝ≥0∞) • (seedHalf f s upper μ).toMeasure ≤ μ.toMeasure := by
  have hm := normalizeOr_mass (seedHalfRaw f s upper μ) μ.toMeasure
  calc
    _ ≤ seedHalfRaw f s upper μ Set.univ • (seedHalf f s upper μ).toMeasure :=
      by
        apply Measure.le_iff.mpr
        intro U _
        simp only [Measure.smul_apply,smul_eq_mul]
        exact mul_le_mul_left (seedHalfRaw_mass f s upper μ) _
    _ = seedHalfRaw f s upper μ := hm
    _ ≤ μ.toMeasure := Measure.restrict_le_self

lemma seedHalf_ae {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) :
    ∀ᵐ x ∂(seedHalf f s upper μ).toMeasure,
      if upper then seedMedian f s μ ≤ s*signedHeight f x
      else s*signedHeight f x ≤ seedMedian f s μ := by
  have hm : seedHalfRaw f s upper μ Set.univ ≠ 0 := ne_of_gt
    ((by norm_num : (0:ℝ≥0∞)<1/2).trans_le (seedHalfRaw_mass f s upper μ))
  change ∀ᵐ x ∂normalizeOr (seedHalfRaw f s upper μ) μ.toMeasure, _
  rw [normalizeOr,ite_eq_right hm,normalizedMeasure]
  apply Measure.ae_smul_measure
  exact ae_restrict_mem (Set.to_countable _).measurableSet

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedEndpointRaw_le {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d) :
    seedEndpointRaw e H R μ ω ≤ seedEndpointRaw e H (fun _ _ => True) μ ω := by
  intro U
  simp only [seedEndpointRaw_apply,Set.ofPred_true,Set.inter_univ]
  exact lintegral_mono fun _ => measure_mono Set.inter_subset_left

lemma seedEndpointRaw_mono {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) {μ ρ : Measure (Lattice d)} (h : μ ≤ ρ) (ω : Environment d) :
    seedEndpointRaw e H R μ ω ≤ seedEndpointRaw e H R ρ ω := by
  intro U
  simp only [seedEndpointRaw_apply]
  exact lintegral_mono' h le_rfl

lemma seedEndpointRaw_smul {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d) (c : ℝ≥0∞) :
    seedEndpointRaw e H R (c • μ) ω = c • seedEndpointRaw e H R μ ω :=
  Measure.bind_smul _ _ _

lemma seedEndpointRaw_comp_le {d : ℕ} (e : Direction d) (h H : ℕ)
    (R S : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d) :
    seedEndpointRaw e H S (seedEndpointRaw e h R μ ω) ω ≤
      seedEndpointRaw e (h+H) (fun _ _ => True) μ ω := by
  apply le_trans (seedEndpointRaw_le e H S _ ω)
  apply le_trans (seedEndpointRaw_mono e H _ (seedEndpointRaw_le e h R μ ω) ω)
  intro U
  simp only [seedEndpointRaw,Set.ofPred_true,Measure.restrict_univ]
  rw [Measure.bind_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  simp_rw [Measure.bind_apply (Set.to_countable U).measurableSet (measurable_of_countable _).aemeasurable]
  apply lintegral_mono
  intro x
  change (∫⁻ y, hitKernel (Strip (realPosition (step e)) y H)
    (Upper (realPosition (step e)) y H) (ω,y) U ∂hitKernel
      (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h) (ω,x)) ≤
        hitKernel (Strip (realPosition (step e)) x (h+H:ℕ))
          (Upper (realPosition (step e)) x (h+H:ℕ)) (ω,x) U
  simpa only [Nat.cast_add] using coordinate_raw_kernel_comp_le e h H ω x U

lemma seedEndpointRaw_joint_rows {d : ℕ} (e : Direction d) {H : ℕ} (hH : 0 < H)
    (R : Lattice d → Lattice d → Prop) (C S : Set (Lattice d))
    (hS : ∀ x ∈ C, Strip (realPosition (step e)) x H ⊆ S) :
    @Measurable ({μ : Measure (Lattice d) // ∀ᵐ x ∂μ, x ∈ C} × Environment d) (Measure (Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => seedEndpointRaw e H R p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply Measure.measurable_of_measurable_coe
  intro U _
  simp only [seedEndpointRaw_apply,lintegral_countable']
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ C
  · have hm := (measurable_hitKernel_rows (Strip (realPosition (step e)) x H)
        (Upper (realPosition (step e)) x H) x
        (show x ∈ Strip (realPosition (step e)) x H from
          ⟨le_rfl,lt_add_of_pos_right _ (by exact_mod_cast hH)⟩)).mono (rowSigma_mono (hS x hx)) le_rfl
    exact (((Measure.measurable_coe (Set.to_countable _).measurableSet).comp hm).comp measurable_snd).mul
      ((Measure.measurable_coe (measurableSet_singleton x)).comp (measurable_subtype_coe.comp measurable_fst))
  · have hz (p : {μ : Measure (Lattice d) // ∀ᵐ x ∂μ, x ∈ C}) : p.val {x}=0 :=
      measure_mono_null (show {x} ⊆ Cᶜ from fun y hy => by simpa [Set.mem_singleton_iff.mp hy] using hx)
        (ae_iff.mp p.property)
    simp only [hz,mul_zero]
    exact measurable_const

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedProfile
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma SeedProfile.measurable_measure {d : ℕ} (e : Direction d) (a : ℤ) :
    Measurable (SeedProfile.measure (e:=e) (a:=a)) := measurable_subtype_coe.comp measurable_subtype_coe

lemma measurable_seedHalfProfile {d : ℕ} (e f : Direction d) (a s : ℤ) (upper : Bool) :
    Measurable (seedHalfProfile e f a s upper) :=
  ((measurable_seedHalf f s upper).comp measurable_subtype_coe).subtype_mk

lemma measurable_seedShift {d : ℕ} (e : Direction d) (H : ℕ) : Measurable (seedShift e H) :=
  ((Measure.measurable_map _ (measurable_of_countable _)).comp measurable_subtype_coe).subtype_mk

lemma seedAdvance_mass {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : SeedProfile e a) (ω : Environment d) :
    seedEndpointRaw e H R μ.measure ω Set.univ • (seedAdvance e a H R μ ω).measure =
      seedEndpointRaw e H R μ.measure ω := normalizeOr_mass _ _

lemma seedAdvance_domination {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : SeedProfile e a) (ω : Environment d)
    (c : ℝ≥0∞) (hc : c ≤ seedEndpointRaw e H R μ.measure ω Set.univ) :
    c • (seedAdvance e a H R μ ω).measure ≤ seedEndpointRaw e H R μ.measure ω := by
  rw [← seedAdvance_mass e a H R μ ω]
  intro U
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul_left hc _

lemma SeedProfile.measurable_supported {d : ℕ} (e : Direction d) (a : ℤ) :
    Measurable (fun μ : SeedProfile e a =>
      (⟨μ.measure,μ.property⟩ : {ρ : Measure (Lattice d) // ∀ᵐ x ∂ρ, signedHeight e x=a})) :=
  (SeedProfile.measurable_measure e a).subtype_mk

lemma seedAdvance_joint_rows {d : ℕ} (e : Direction d) (a : ℤ) {H : ℕ} (hH : 0 < H)
    (R : Lattice d → Lattice d → Prop) (S : Set (Lattice d))
    (hS : ∀ x, signedHeight e x=a → Strip (realPosition (step e)) x H ⊆ S) :
    @Measurable (SeedProfile e a × Environment d) (SeedProfile e (a+H))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => seedAdvance e a H R p.1 p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  have hm := (seedEndpointRaw_joint_rows e hH R {x | signedHeight e x=a} S hS).comp
    (((SeedProfile.measurable_supported e a).comp measurable_fst).prodMk measurable_snd)
  have hρ : Measurable (fun p : SeedProfile e a × Environment d => (seedShift e H p.1.val).toMeasure) :=
    measurable_subtype_coe.comp ((measurable_seedShift e H).comp (measurable_subtype_coe.comp measurable_fst))
  exact ((measurable_normalizeOr _ _ hm hρ).subtype_mk).subtype_mk

lemma seedAdvance_retained {d : ℕ} (e : Direction d) (a : ℤ) (h H : ℕ)
    (R : Lattice d → Lattice d → Prop) (π : Measure (Lattice d))
    (μ : SeedProfile e a) (ω : Environment d) (δ c : ℝ≥0∞)
    (hμ : δ • μ.measure ≤ seedEndpointRaw e h (fun _ _ => True) π ω)
    (hc : c ≤ seedEndpointRaw e H R μ.measure ω Set.univ) :
    (δ*c) • (seedAdvance e a H R μ ω).measure ≤ seedEndpointRaw e (h+H) (fun _ _ => True) π ω := by
  have hd : δ • (c • (seedAdvance e a H R μ ω).measure) ≤ δ • seedEndpointRaw e H R μ.measure ω := by
    intro U
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul_right (seedAdvance_domination e a H R μ ω c hc U) δ
  rw [smul_smul,← seedEndpointRaw_smul] at hd
  exact hd.trans ((seedEndpointRaw_mono e H R hμ ω).trans
    (seedEndpointRaw_comp_le e h H _ R π ω))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedOrder
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma ae_at_atom {A : Type*} [MeasurableSpace A] {μ : Measure A} {P : A → Prop}
    (h : ∀ᵐ x ∂μ, P x) {x : A} (hx : μ {x} ≠ 0) : P x := by
  by_contra hnot
  exact hx (measure_mono_null (by simpa only [Set.singleton_subset_iff,Set.mem_ofPred_eq] using hnot) (ae_iff.mp h))

lemma atom_of_ae_domination {A : Type*} [MeasurableSpace A] (μ ρ : Measure A)
    (c : ℝ≥0∞) (hc : c ≠ 0) (h : c • μ ≤ ρ) {x : A} (hx : μ {x} ≠ 0) : ρ {x} ≠ 0 := by
  intro hz
  have hh := h {x}
  simp only [Measure.smul_apply,smul_eq_mul,hz,nonpos_iff_eq_zero,mul_eq_zero] at hh
  exact hh.elim hc hx

lemma seedEndpointRaw_atom_origin {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d)
    (y : Lattice d) (hy : seedEndpointRaw e H R μ ω {y} ≠ 0) :
    ∃ x, μ {x} ≠ 0 ∧ R x y := by
  by_contra! hn
  apply hy
  rw [seedEndpointRaw_apply,lintegral_countable']
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  by_cases hx : μ {x}=0
  · simp [hx]
  · have hxy := hn x hx
    have he : {y} ∩ {z | R x z}=∅ := by ext z; simp only [Set.mem_inter_iff,Set.mem_singleton_iff,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]; rintro ⟨rfl,h⟩; exact hxy h
    simp [he]

lemma seedAdvance_atom_origin {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : SeedProfile e a) (ω : Environment d)
    (hm : seedEndpointRaw e H R μ.measure ω Set.univ ≠ 0)
    (y : Lattice d) (hy : (seedAdvance e a H R μ ω).measure {y} ≠ 0) :
    ∃ x, μ.measure {x} ≠ 0 ∧ R x y := by
  apply seedEndpointRaw_atom_origin e H R μ.measure ω y
  rw [←seedAdvance_mass e a H R μ ω,Measure.smul_apply,smul_eq_mul]
  exact mul_ne_zero hm hy

lemma seedHalfProfile_atom_origin {d : ℕ} (e f : Direction d) (a s : ℤ) (upper : Bool)
    (μ : SeedProfile e a) (x : Lattice d)
    (hx : (seedHalfProfile e f a s upper μ).measure {x} ≠ 0) :
    μ.measure {x} ≠ 0 ∧
      (if upper then seedMedian f s μ.val ≤ s*signedHeight f x
       else s*signedHeight f x ≤ seedMedian f s μ.val) := by
  exact ⟨atom_of_ae_domination _ _ _ (by norm_num) (seedHalf_domination f s upper μ.val) hx,
    ae_at_atom (seedHalf_ae f s upper μ.val) hx⟩

lemma seedOrdered_mono {d : ℕ} (f : Direction d) (s : ℤ) {g g' : ℝ}
    {μ ρ : Measure (Lattice d)} (h : SeedOrdered f s g μ ρ) (hg : g' ≤ g) : SeedOrdered f s g' μ ρ :=
  fun x hx y hy => hg.trans (h x hx y hy)

lemma seedOrdered_central {d : ℕ} (e f : Direction d) (a s : ℤ) (H : ℕ)
    (θ z g : ℝ) (hs : s=1 ∨ s= -1) (μ ρ : SeedProfile e a) (ω : Environment d)
    (hm : seedEndpointRaw e H (SeedCentral f H θ z) μ.measure ω Set.univ ≠ 0)
    (hr : seedEndpointRaw e H (SeedCentral f H θ z) ρ.measure ω Set.univ ≠ 0)
    (ho : SeedOrdered f s g μ.measure ρ.measure) :
    SeedOrdered f s (g-2*z) (seedAdvance e a H (SeedCentral f H θ z) μ ω).measure
      (seedAdvance e a H (SeedCentral f H θ z) ρ ω).measure := by
  intro x hx y hy
  obtain ⟨u,hu,hux⟩ := seedAdvance_atom_origin e a H _ μ ω hm x hx
  obtain ⟨v,hv,hvy⟩ := seedAdvance_atom_origin e a H _ ρ ω hr y hy
  have huv := ho u hu v hv
  simp only [SeedCentral,signedCoordinate_sub,abs_le] at hux hvy
  rcases hs with rfl | rfl <;> norm_num at huv ⊢ <;> linarith [hux.1,hux.2,hvy.1,hvy.2]

lemma signedHeight_cast_coordinate {d : ℕ} (f : Direction d) (x : Lattice d) :
    (signedHeight f x:ℝ)=signedCoordinate f x := by
  simp only [signedHeight,signedCoordinate,Int.cast_ite,Int.cast_neg]

lemma seedOrdered_split {d : ℕ} (e f : Direction d) (a s : ℤ) (H : ℕ)
    (θ z b : ℝ) (hs : s=1 ∨ s= -1) (μ : SeedProfile e a) (ω : Environment d)
    (hm : seedEndpointRaw e H (SeedCentral f H θ z) (seedHalfProfile e f a s false μ).measure ω Set.univ ≠ 0)
    (hr : seedEndpointRaw e H (SeedJump f H s θ b) (seedHalfProfile e f a s true μ).measure ω Set.univ ≠ 0) :
    SeedOrdered f s (b-z)
      (seedAdvance e a H (SeedCentral f H θ z) (seedHalfProfile e f a s false μ) ω).measure
      (seedAdvance e a H (SeedJump f H s θ b) (seedHalfProfile e f a s true μ) ω).measure := by
  intro x hx y hy
  obtain ⟨u,hu,hux⟩ := seedAdvance_atom_origin e a H _ _ ω hm x hx
  obtain ⟨v,hv,hvy⟩ := seedAdvance_atom_origin e a H _ _ ω hr y hy
  have hlu := (seedHalfProfile_atom_origin e f a s false μ u hu).2
  have hlv := (seedHalfProfile_atom_origin e f a s true μ v hv).2
  simp only [Bool.false_eq_true,↓reduceIte] at hlu
  simp only [↓reduceIte] at hlv
  have ho : (s:ℝ)*signedCoordinate f u ≤ (s:ℝ)*signedCoordinate f v := by
    simpa only [Int.cast_mul,signedHeight_cast_coordinate] using (show ((s*signedHeight f u:ℤ):ℝ) ≤ ((s*signedHeight f v:ℤ):ℝ) from by exact_mod_cast hlu.trans hlv)
  simp only [SeedCentral,signedCoordinate_sub,abs_le] at hux
  simp only [SeedJump,signedCoordinate_sub] at hvy
  rcases hs with rfl | rfl <;> norm_num at ho hvy ⊢ <;> linarith [hux.1,hux.2]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurable_seedEval {d : ℕ} (e : Direction d) (a : ℤ) :
    Measurable (fun p : (ℕ → SeedProfile e a) × ℕ => p.1 p.2) :=
  measurable_from_prod_countable_left fun n => measurable_pi_apply n

lemma measurable_seedCentralInput {d : ℕ} (e f : Direction d) (a s : ℤ) (k i : ℕ) :
    Measurable (fun q : SeedState e a => seedCentralInput e f a s k q i) := by
  unfold seedCentralInput
  exact (((measurable_seedHalfProfile e f a s false).comp ((measurable_pi_apply i).comp measurable_snd))).ite
    ((measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_eq_fun measurable_const (measurable_fst.sub_const 1)))
    ((measurable_pi_apply i).comp measurable_snd)

lemma measurable_seedJumpInput {d : ℕ} (e f : Direction d) (a s : ℤ) :
    Measurable (seedJumpInput e f a s) := by
  apply (measurable_seedHalfProfile e f a s true).comp
  exact (measurable_seedEval e a).comp (measurable_snd.prodMk (measurable_fst.sub_const 1))

lemma seedStateStep_count {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j : ℝ) (q : SeedState e a) (ω : Environment d) :
    q.1 ≤ (seedStateStep e f a s k H θ z b j q ω).1 ∧
    (seedStateStep e f a s k H θ z b j q ω).1 ≤ q.1+1 ∧
    (q.1≤k → (seedStateStep e f a s k H θ z b j q ω).1≤k) := by
  simp only [seedStateStep]
  split_ifs <;> omega

lemma seedStateStep_strict {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j : ℝ) (q : SeedState e a) (ω : Environment d) (hq : q.1<k)
    (ht : seedSplitTest e f a s H θ b j q ω) :
    q.1 < (seedStateStep e f a s k H θ z b j q ω).1 := by
  simp [seedStateStep,hq,ht]

lemma seedCentralInput_domination {d : ℕ} (e f : Direction d) (a s : ℤ) (k : ℕ)
    (q : SeedState e a) (i : ℕ) :
    (1/2:ℝ≥0∞) • (seedCentralInput e f a s k q i).measure ≤ (q.2 i).measure := by
  unfold seedCentralInput
  split_ifs
  · exact seedHalf_domination f s false (q.2 i).val
  · intro U
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_of_le_one_left bot_le (by norm_num)

lemma seedCentralInput_atom {d : ℕ} (e f : Direction d) (a s : ℤ) (k : ℕ)
    (q : SeedState e a) (i : ℕ) {x : Lattice d}
    (hx : (seedCentralInput e f a s k q i).measure {x} ≠ 0) : (q.2 i).measure {x} ≠ 0 :=
  atom_of_ae_domination _ _ _ (by norm_num) (seedCentralInput_domination e f a s k q i) hx

lemma seedStateStep_retained {d : ℕ} (e f : Direction d) (a s : ℤ) (k H h : ℕ)
    (θ z b j c : ℝ) (q : SeedState e a) (ω : Environment d) (π : Measure (Lattice d))
    (δ : ℝ≥0∞) (hq : 0 < q.1) (hj : 0 ≤ j) (hc : 0 ≤ c)
    (hr : SeedStateRetained e a h π ω δ q)
    (hp : SeedPreserved e f a s k H θ z c q ω) :
    SeedStateRetained e (a+H) (h+H) π ω (δ*(ENNReal.ofReal (min c j)/2))
      (seedStateStep e f a s k H θ z b j q ω) := by
  intro i hi
  have hcentral (i : ℕ) (hi : i<q.1) :
      (δ*(ENNReal.ofReal (min c j)/2)) •
        (seedAdvance e a H (SeedCentral f H θ z) (seedCentralInput e f a s k q i) ω).measure ≤
          seedEndpointRaw e (h+H) (fun _ _ => True) π ω := by
    have hsub : (δ/2) • (seedCentralInput e f a s k q i).measure ≤ seedEndpointRaw e h (fun _ _ => True) π ω := by
      calc
        _ = δ • ((1/2:ℝ≥0∞) • (seedCentralInput e f a s k q i).measure) := by rw [smul_smul]; congr 1; simp [div_eq_mul_inv]
        _ ≤ δ • (q.2 i).measure := by
          intro U; simpa only [Measure.smul_apply,smul_eq_mul] using mul_le_mul_right (seedCentralInput_domination e f a s k q i U) δ
        _ ≤ _ := hr i hi
    have hmass : ENNReal.ofReal (min c j) ≤ seedEndpointRaw e H (SeedCentral f H θ z) (seedCentralInput e f a s k q i).measure ω Set.univ := by
      apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
      rw [ENNReal.toReal_ofReal (le_min hc hj)]
      exact (min_le_left _ _).trans (hp i hi)
    have hh := seedAdvance_retained e a h H _ π (seedCentralInput e f a s k q i) ω (δ/2) (ENNReal.ofReal (min c j)) hsub hmass
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp [div_eq_mul_inv,mul_comm,mul_left_comm]
  by_cases ht : q.1<k ∧ seedSplitTest e f a s H θ b j q ω
  · simp only [seedStateStep,ite_eq_left ht] at hi ⊢
    by_cases he : i=q.1
    · simp only [he]
      have hsub : (δ/2) • (seedJumpInput e f a s q).measure ≤ seedEndpointRaw e h (fun _ _ => True) π ω := by
        calc
          _ = δ • ((1/2:ℝ≥0∞) • (seedJumpInput e f a s q).measure) := by rw [smul_smul]; congr 1; simp [div_eq_mul_inv]
          _ ≤ δ • (q.2 (q.1-1)).measure := by
            intro U; simpa only [Measure.smul_apply,smul_eq_mul,seedJumpInput,seedHalfProfile,SeedProfile.measure] using mul_le_mul_right (seedHalf_domination f s true (q.2 (q.1-1)).val U) δ
          _ ≤ _ := hr (q.1-1) (by omega)
      have hmass : ENNReal.ofReal (min c j) ≤ seedEndpointRaw e H (SeedJump f H s θ b) (seedJumpInput e f a s q).measure ω Set.univ := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans ht.2)
      have hh := seedAdvance_retained e a h H _ π (seedJumpInput e f a s q) ω (δ/2) (ENNReal.ofReal (min c j)) hsub hmass
      simpa [seedStateStep,ht,he,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
    · simp only [he,and_false,ite_false, if_false]
      exact hcentral i (by omega)
  · simp only [seedStateStep,ite_eq_right ht] at hi ⊢
    simpa [seedStateStep,ht] using hcentral i hi

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedStateOrder
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma exists_atom_probability {A : Type*} [MeasurableSpace A] [Countable A]
    [MeasurableSingletonClass A] (μ : Measure A) [IsProbabilityMeasure μ] : ∃ x, μ {x} ≠ 0 := by
  by_contra! hn
  have hz : μ=0 := Measure.ext_of_singleton fun x => by simp [hn x]
  have h := measure_univ (μ:=μ)
  simp only [hz,Measure.coe_zero,Pi.zero_apply] at h
  exact zero_ne_one h

lemma seedOrdered_trans {d : ℕ} (f : Direction d) (s : ℤ) (g h : ℝ)
    (μ ρ σ : Measure (Lattice d)) [IsProbabilityMeasure ρ]
    (h₁ : SeedOrdered f s g μ ρ) (h₂ : SeedOrdered f s h ρ σ) : SeedOrdered f s (g+h) μ σ := by
  obtain ⟨y,hy⟩ := exists_atom_probability ρ
  intro x hx z hz
  have hxy := h₁ x hx y hy
  have hyz := h₂ y hy z hz
  nlinarith

lemma seedStateStep_ordered {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j c g g' : ℝ) (q : SeedState e a) (ω : Environment d)
    (hs : s=1 ∨ s= -1) (hq : 0<q.1) (hj : 0<j) (hc : 0 < c)
    (hg' : 0≤g') (hgg' : g'≤g-2*z) (hbg' : g'≤b-z)
    (ho : SeedStateOrdered f s g q)
    (hp : SeedPreserved e f a s k H θ z c q ω) :
    SeedStateOrdered f s g' (seedStateStep e f a s k H θ z b j q ω) := by
  let P := fun i => seedAdvance e a H (SeedCentral f H θ z) (seedCentralInput e f a s k q i) ω
  have hm (i : ℕ) (hi : i<q.1) : seedEndpointRaw e H (SeedCentral f H θ z)
      (seedCentralInput e f a s k q i).measure ω Set.univ ≠ 0 := by
    intro hz
    have hh := hp i hi
    rw [hz,ENNReal.toReal_zero] at hh
    linarith
  have hop (i t : ℕ) (hit : i<t) (ht : t<q.1) : SeedOrdered f s g' (P i).measure (P t).measure := by
    apply seedOrdered_mono f s (g:=g-2*z) _ hgg'
    apply seedOrdered_central e f a s H θ z g hs _ _ ω (hm i (hit.trans ht)) (hm t ht)
    intro x hx y hy
    exact ho i t hit ht x (seedCentralInput_atom e f a s k q i hx) y (seedCentralInput_atom e f a s k q t hy)
  intro i t hit ht
  by_cases hsplit : q.1<k ∧ seedSplitTest e f a s H θ b j q ω
  · have htt : t<q.1+1 := by simpa [seedStateStep,hsplit] using ht
    have hi : i<q.1 := by omega
    have hqi : i≠q.1 := by omega
    by_cases hqt : t=q.1
    · let J := seedAdvance e a H (SeedJump f H s θ b) (seedJumpInput e f a s q) ω
      have hjm : seedEndpointRaw e H (SeedJump f H s θ b) (seedJumpInput e f a s q).measure ω Set.univ ≠ 0 := by
        intro hz
        have hh := hsplit.2
        change j ≤ _ at hh
        rw [hz,ENNReal.toReal_zero] at hh
        linarith
      have hlast : SeedOrdered f s g' (P (q.1-1)).measure J.measure := by
        have he : seedCentralInput e f a s k q (q.1-1)=seedHalfProfile e f a s false (q.2 (q.1-1)) := by
          simp [seedCentralInput,hsplit.1]
        have hh := seedOrdered_split e f a s H θ z b hs (q.2 (q.1-1)) ω
          (by simpa only [←he] using hm (q.1-1) (by omega)) hjm
        apply seedOrdered_mono f s _ hbg'
        simpa only [P,J,seedJumpInput,he] using hh
      have hip : SeedOrdered f s g' (P i).measure J.measure := by
        by_cases he : i=q.1-1
        · simpa only [he] using hlast
        · have hh := seedOrdered_trans f s g' g' (P i).measure (P (q.1-1)).measure J.measure
            (hop i (q.1-1) (by omega) (by omega)) hlast
          exact seedOrdered_mono f s hh (by linarith)
      simpa [seedStateStep,hsplit,hqt,hqi,P,J] using hip
    · have htt' : t<q.1 := by omega
      simpa [seedStateStep,hsplit,hqt,hqi,P] using hop i t hit htt'
  · have htt : t<q.1 := by simpa [seedStateStep,hsplit] using ht
    simpa [seedStateStep,hsplit,P] using hop i t hit htt

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedProfileRaw_joint_rows {d : ℕ} (e : Direction d) (a : ℤ) {H : ℕ} (hH : 0<H)
    (R : Lattice d → Lattice d → Prop) (S : Set (Lattice d))
    (hS : ∀ x, signedHeight e x=a → Strip (realPosition (step e)) x H ⊆ S) :
    @Measurable (SeedProfile e a × Environment d) ℝ
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => (seedEndpointRaw e H R p.1.measure p.2 Set.univ).toReal) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  exact ((Measure.measurable_coe MeasurableSet.univ).comp
    ((seedEndpointRaw_joint_rows e hH R {x | signedHeight e x=a} S hS).comp
      (((SeedProfile.measurable_supported e a).comp measurable_fst).prodMk measurable_snd))).ennreal_toReal

lemma seedSplitTest_joint_rows {d : ℕ} (e f : Direction d) (a s : ℤ) {H : ℕ} (hH : 0<H)
    (θ b j : ℝ) (S : Set (Lattice d))
    (hS : ∀ x, signedHeight e x=a → Strip (realPosition (step e)) x H ⊆ S) :
    @MeasurableSet (SeedState e a × Environment d)
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S))
      {p | seedSplitTest e f a s H θ b j p.1 p.2} := by
  let : MeasurableSpace (Environment d) := rowSigma S
  change MeasurableSet {p : SeedState e a × Environment d | j ≤
    (seedEndpointRaw e H (SeedJump f H s θ b) (seedJumpInput e f a s p.1).measure p.2 Set.univ).toReal}
  have hm := (seedProfileRaw_joint_rows e a hH (SeedJump f H s θ b) S hS).comp
    (((measurable_seedJumpInput e f a s).comp measurable_fst).prodMk measurable_snd)
  exact measurableSet_le measurable_const hm

lemma seedStateStep_joint_rows {d : ℕ} (e f : Direction d) (a s : ℤ) (k : ℕ) {H : ℕ} (hH : 0<H)
    (θ z b j : ℝ) (S : Set (Lattice d))
    (hS : ∀ x, signedHeight e x=a → Strip (realPosition (step e)) x H ⊆ S) :
    @Measurable (SeedState e a × Environment d) (SeedState e (a+H))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => seedStateStep e f a s k H θ z b j p.1 p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  have ht : MeasurableSet {p : SeedState e a × Environment d | p.1.1<k ∧ seedSplitTest e f a s H θ b j p.1 p.2} := (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_const).inter
    (seedSplitTest_joint_rows e f a s hH θ b j S hS)
  apply Measurable.prodMk
  · exact ((measurable_fst.comp measurable_fst).add_const 1).ite ht (measurable_fst.comp measurable_fst)
  · apply measurable_pi_iff.mpr
    intro i
    have hjump := (seedAdvance_joint_rows e a hH (SeedJump f H s θ b) S hS).comp
      (((measurable_seedJumpInput e f a s).comp measurable_fst).prodMk measurable_snd)
    have hcentral := (seedAdvance_joint_rows e a hH (SeedCentral f H θ z) S hS).comp
      (((measurable_seedCentralInput e f a s k i).comp measurable_fst).prodMk measurable_snd)
    exact hjump.ite (ht.inter (measurableSet_eq_fun measurable_const (measurable_fst.comp measurable_fst))) hcentral

lemma seedPreserved_joint_rows {d : ℕ} (e f : Direction d) (a s : ℤ) (k : ℕ) {H : ℕ} (hH : 0<H)
    (θ z c : ℝ) (S : Set (Lattice d))
    (hS : ∀ x, signedHeight e x=a → Strip (realPosition (step e)) x H ⊆ S) :
    @MeasurableSet (SeedState e a × Environment d)
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S))
      {p | SeedPreserved e f a s k H θ z c p.1 p.2} := by
  let : MeasurableSpace (Environment d) := rowSigma S
  simp only [SeedPreserved,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have hc := (seedProfileRaw_joint_rows e a hH (SeedCentral f H θ z) S hS).comp
      (((measurable_seedCentralInput e f a s k i).comp measurable_fst).prodMk measurable_snd)
  have hi : MeasurableSet {p : SeedState e a × Environment d | i<p.1.1} :=
    measurableSet_lt measurable_const (measurable_fst.comp measurable_fst)
  have hmass : MeasurableSet {p : SeedState e a × Environment d | c ≤
      (seedEndpointRaw e H (SeedCentral f H θ z) (seedCentralInput e f a s k p.1 i).measure p.2 Set.univ).toReal} :=
    measurableSet_le measurable_const hc
  convert hi.compl.union hmass using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_compl_iff,imp_iff_not_or]

lemma seedBelow_disjoint_above {d : ℕ} (e : Direction d) (a : ℤ) : Disjoint (seedBelow e a) (seedAbove e a) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  change signedHeight e x < a at hx
  change a ≤ signedHeight e x at hy
  omega

lemma strip_subset_seedAbove {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ)
    (x : Lattice d) (hx : signedHeight e x=a) : Strip (realPosition (step e)) x H ⊆ seedAbove e a := by
  intro y hy
  have hh := hy.1
  simp only [signedHeight_projection,hx] at hh
  exact_mod_cast hh

lemma strip_subset_seedBelow {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ)
    (x : Lattice d) (hx : signedHeight e x=a) : Strip (realPosition (step e)) x H ⊆ seedBelow e (a+H) := by
  intro y hy
  have hh := hy.2
  simp only [signedHeight_projection,hx] at hh
  change signedHeight e y<a+(H:ℤ)
  exact_mod_cast hh

lemma seed_fresh_test_bound {d : ℕ} {A : Type*} [MeasurableSpace A]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (e : Direction d) (a : ℤ)
    (U : Environment d → A) (hU : @Measurable _ _ (rowSigma (seedBelow e a)) _ U)
    (E : Set (Environment d)) (hE : MeasurableSet[rowSigma (seedBelow e a)] E)
    (G : Set (A × Environment d))
    (hG : @MeasurableSet _ (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma (seedAbove e a))) G)
    (c : ℝ≥0∞) (hb : ∀ η ∈ E, environmentLaw ν {ω | (U η,ω)∈G} ≤ c) :
    environmentLaw ν {ω | ω∈E ∧ (U ω,ω)∈G} ≤ c*environmentLaw ν E := by
  let S := seedBelow e a
  let T := seedAbove e a
  let K : Set (Environment d × Environment d) := {p | (U p.1,p.2)∈G}
  have hK : @MeasurableSet _ (MeasurableSpace.prod (rowSigma S) (rowSigma T)) K :=
    hG.preimage ((hU.comp measurable_fst).prodMk measurable_snd)
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  have hb' (η : Environment d) (hη : η∈E) :
      (@Measure.map (Environment d) (Environment d) inferInstance (rowSigma T) id (environmentLaw ν))
        {ω | (η,ω)∈K} ≤ c := by
    rw [show {ω | (η,ω)∈K}=Prod.mk η ⁻¹' K from rfl,
      Measure.map_apply hV (hK.preimage measurable_prodMk_left)]
    exact hb η hη
  exact @fresh_rows_random_test_bound d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
    ν _ S T (seedBelow_disjoint_above e a) id id measurable_id measurable_id E hE K hK c hb'

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedIteration
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedHeight_eq (a : ℤ) (H n : ℕ) : seedHeight a H n=a+(n:ℤ)*H := by
  induction n with
  | zero => simp [seedHeight]
  | succ n ih => simp only [seedHeight,ih,Nat.cast_add,Nat.cast_one] <;> ring

lemma seedHeight_mono (a : ℤ) (H : ℕ) : Monotone (seedHeight a H) := by
  intro m n hmn
  rw [seedHeight_eq,seedHeight_eq]
  have hm : (m:ℤ) ≤ n := by exact_mod_cast hmn
  exact add_le_add_right (mul_le_mul_of_nonneg_right hm (Int.natCast_nonneg H)) a

lemma seedBelow_mono {d : ℕ} (e : Direction d) {a b : ℤ} (h : a≤b) : seedBelow e a ⊆ seedBelow e b := fun _ hx => hx.trans_le h

lemma seedRun_measurable {d : ℕ} (e f : Direction d) (a s : ℤ) (k : ℕ) {H : ℕ} (hH : 0<H)
    (θ z b j : ℝ) (q : SeedState e a) (n : ℕ) :
    @Measurable _ _ (rowSigma (seedBelow e (seedHeight a H n))) _ (seedRun e f a s k H θ z b j q n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hle := rowSigma_mono (seedBelow_mono e (seedHeight_mono a H (Nat.le_succ n)))
    exact (seedStateStep_joint_rows e f (seedHeight a H n) s k hH θ z b j
      (seedBelow e (seedHeight a H n+H)) (strip_subset_seedBelow e (seedHeight a H n) H)).comp
        ((ih.mono hle le_rfl).prodMk measurable_id)

lemma seedRun_count_step {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j : ℝ) (q : SeedState e a) (n : ℕ) (ω : Environment d) :
    (seedRun e f a s k H θ z b j q n ω).1 ≤ (seedRun e f a s k H θ z b j q (n+1) ω).1 ∧
    (seedRun e f a s k H θ z b j q (n+1) ω).1 ≤ (seedRun e f a s k H θ z b j q n ω).1+1 :=
  (seedStateStep_count e f (seedHeight a H n) s k H θ z b j _ ω).imp_right And.left

lemma seedRun_count_mono {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j : ℝ) (q : SeedState e a) (ω : Environment d) :
    Monotone (fun n => (seedRun e f a s k H θ z b j q n ω).1) :=
  monotone_nat_of_le_succ fun n => (seedRun_count_step e f a s k H θ z b j q n ω).1

lemma seedRun_count_bounds {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j : ℝ) (q : SeedState e a) (hq : 0<q.1) (hqk : q.1≤k) (n : ℕ) (ω : Environment d) :
    0<(seedRun e f a s k H θ z b j q n ω).1 ∧ (seedRun e f a s k H θ z b j q n ω).1≤k := by
  induction n with
  | zero => exact ⟨hq,hqk⟩
  | succ n ih => exact ⟨ih.1.trans_le (seedRun_count_step e f a s k H θ z b j q n ω).1,
      (seedStateStep_count e f (seedHeight a H n) s k H θ z b j _ ω).2.2 ih.2⟩

lemma seedEndpointRaw_zero {d : ℕ} (e : Direction d) (μ : Measure (Lattice d)) (ω : Environment d) :
    seedEndpointRaw e 0 (fun _ _ => True) μ ω=μ := by
  simp only [seedEndpointRaw,Set.ofPred_true,Measure.restrict_univ]
  have he (x : Lattice d) : variableHitKernel (realPosition (step e)) 0 (ω,x)=Measure.dirac x :=
    by
      simpa only [variableHitKernel,Kernel.coe_mk,Nat.cast_zero] using
        hitKernel_height_zero (realPosition (step e)) x ω
  simp_rw [he]
  exact Measure.bind_dirac

lemma seedRun_retained {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j c : ℝ) (μ : SeedProfile e a) (hk : 1≤k) (hj : 0≤j) (hc : 0 ≤ c)
    (n : ℕ) (ω : Environment d)
    (hp : ∀ t<n, SeedPreserved e f (seedHeight a H t) s k H θ z c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) t ω) ω) :
    SeedStateRetained e (seedHeight a H n) (n*H) μ.measure ω
      ((ENNReal.ofReal (min c j)/2)^n) (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) := by
  induction n with
  | zero =>
    intro i hi
    simp only [seedRun,pow_zero,one_smul,Nat.zero_mul,seedEndpointRaw_zero]
    exact le_rfl
  | succ n ih =>
    have hh := seedStateStep_retained e f (seedHeight a H n) s k H (n*H) θ z b j c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) ω μ.measure
      ((ENNReal.ofReal (min c j)/2)^n)
      (seedRun_count_bounds e f a s k H θ z b j (1,fun _ => μ) (by norm_num) hk n ω).1 hj hc
      (ih (fun t ht => hp t (ht.trans (Nat.lt_succ_self n)))) (hp n (Nat.lt_succ_self n))
    simpa only [seedRun,seedHeight,Nat.add_mul,Nat.one_mul,pow_succ] using hh

lemma seedRun_ordered {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j c : ℝ) (μ : SeedProfile e a) (hk : 1≤k) (hj : 0<j) (hc : 0 < c)
    (hs : s=1 ∨ s= -1) (hz : 0≤z) (n : ℕ) (ω : Environment d)
    (hg : 0≤b+z-2*(n:ℝ)*z)
    (hp : ∀ t<n, SeedPreserved e f (seedHeight a H t) s k H θ z c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) t ω) ω) :
    SeedStateOrdered f s (b+z-2*(n:ℝ)*z) (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) := by
  induction n with
  | zero => intro i t hit ht; change t<1 at ht; omega
  | succ n ih =>
    have hn : (n:ℝ)+1=(n+1:ℕ) := by norm_num
    have hgprev : 0≤b+z-2*(n:ℝ)*z := by push_cast at hg <;> nlinarith
    apply seedStateStep_ordered e f (seedHeight a H n) s k H θ z b j c (b+z-2*(n:ℝ)*z) _ _ ω hs
      (seedRun_count_bounds e f a s k H θ z b j (1,fun _ => μ) (by norm_num) hk n ω).1 hj hc hg
    · push_cast; ring_nf; exact le_rfl
    · push_cast <;> nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    · exact ih hgprev (fun t ht => hp t (ht.trans (Nat.lt_succ_self n)))
    · exact hp n (Nat.lt_succ_self n)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedPreserved_failure_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a s : ℤ) (k H : ℕ) (θ z c : ℝ) (ε : ℝ≥0∞)
    (hc : ∀ μ : ProbabilityMeasure (Lattice d), environmentLaw ν {ω |
      (seedEndpointRaw e H (SeedCentral f H θ z) μ.toMeasure ω Set.univ).toReal < c} ≤ ε)
    (q : SeedState e a) (hq : q.1≤k) :
    environmentLaw ν {ω | ¬SeedPreserved e f a s k H θ z c q ω} ≤ k*ε := by
  have hs : {ω | ¬SeedPreserved e f a s k H θ z c q ω} ⊆ ⋃ i∈Finset.range k,
      {ω | (seedEndpointRaw e H (SeedCentral f H θ z) (seedCentralInput e f a s k q i).measure ω Set.univ).toReal < c} := by
    intro ω hω
    obtain ⟨i,hi⟩ := not_forall.mp hω
    have hi' : i<q.1 := by by_contra h; exact hi (fun h' => (h h').elim)
    have hm := not_le.mp (fun h => hi (fun _ => h))
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (hi'.trans_le hq),hm⟩⟩
  calc
    _ ≤ _ := measure_mono hs
    _ ≤ ∑ i∈Finset.range k, environmentLaw ν {ω |
      (seedEndpointRaw e H (SeedCentral f H θ z) (seedCentralInput e f a s k q i).measure ω Set.univ).toReal < c} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i∈Finset.range k, ε := Finset.sum_le_sum fun i _ => hc (seedCentralInput e f a s k q i).val
    _ = _ := by simp

lemma seedRun_preservation_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a s : ℤ) (k : ℕ) {H : ℕ} (hH : 0<H)
    (θ z b j c : ℝ) (ε : ℝ≥0∞) (μ : SeedProfile e a) (hk : 1≤k)
    (hc : ∀ μ : ProbabilityMeasure (Lattice d), environmentLaw ν {ω |
      (seedEndpointRaw e H (SeedCentral f H θ z) μ.toMeasure ω Set.univ).toReal < c} ≤ ε)
    (J : ℕ) : environmentLaw ν {ω | ∃ n<J, ¬SeedPreserved e f (seedHeight a H n) s k H θ z c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) ω} ≤ J*(k*ε) := by
  have hb (n : ℕ) : environmentLaw ν {ω | ¬SeedPreserved e f (seedHeight a H n) s k H θ z c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) ω} ≤ k*ε := by
    have hh := seed_fresh_test_bound ν e (seedHeight a H n)
      (seedRun e f a s k H θ z b j (1,fun _ => μ) n)
      (seedRun_measurable e f a s k hH θ z b j _ n) Set.univ MeasurableSet.univ
      {p | ¬SeedPreserved e f (seedHeight a H n) s k H θ z c p.1 p.2}
      (seedPreserved_joint_rows e f (seedHeight a H n) s k hH θ z c (seedAbove e (seedHeight a H n))
        (strip_subset_seedAbove e (seedHeight a H n) H)).compl (k*ε)
      (fun η _ => seedPreserved_failure_bound ν e f (seedHeight a H n) s k H θ z c ε hc _
        (seedRun_count_bounds e f a s k H θ z b j (1,fun _ => μ) (by norm_num) hk n η).2)
    simpa only [Set.mem_univ,true_and,measure_univ,mul_one,Set.mem_ofPred_eq] using hh
  have he : {ω | ∃ n<J, ¬SeedPreserved e f (seedHeight a H n) s k H θ z c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) ω} = ⋃ n∈Finset.range J,
      {ω | ¬SeedPreserved e f (seedHeight a H n) s k H θ z c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) ω} := by ext ω; simp
  rw [he]
  exact (measure_biUnion_finset_le _ _).trans ((Finset.sum_le_sum fun n _ => hb n).trans_eq (by simp))

lemma seedRun_stall_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a s : ℤ) (k : ℕ) {H : ℕ} (hH : 0<H)
    (θ z b j : ℝ) (q : SeedState e a) (ρ : ℝ≥0∞)
    (hf : ∀ (a : ℤ) (q : SeedState e a), environmentLaw ν {ω | ¬seedSplitTest e f a s H θ b j q ω}≤ρ)
    (u N : ℕ) : environmentLaw ν {ω | (seedRun e f a s k H θ z b j q u ω).1<k ∧
      (seedRun e f a s k H θ z b j q (u+N) ω).1=(seedRun e f a s k H θ z b j q u ω).1} ≤ ρ^N := by
  let run := seedRun e f a s k H θ z b j q
  let E := fun n => {ω : Environment d | (run u ω).1<k ∧ (run (u+n) ω).1=(run u ω).1}
  have hm (n : ℕ) : MeasurableSet[rowSigma (seedBelow e (seedHeight a H (u+n)))] (E n) := by
    have hn := (measurable_fst.comp (seedRun_measurable e f a s k hH θ z b j q (u+n)))
    have hu := (measurable_fst.comp (seedRun_measurable e f a s k hH θ z b j q u)).mono
      (rowSigma_mono (seedBelow_mono e (seedHeight_mono a H (Nat.le_add_right u n)))) le_rfl
    exact (measurableSet_lt hu measurable_const).inter (measurableSet_eq_fun hn hu)
  have hb (n : ℕ) : environmentLaw ν (E (n+1)) ≤ ρ*environmentLaw ν (E n) := by
    have hs : E (n+1) ⊆ {ω | ω∈E n ∧ ¬seedSplitTest e f (seedHeight a H (u+n)) s H θ b j (run (u+n) ω) ω} := by
      intro ω hω
      change (run u ω).1<k ∧ (run (u+(n+1)) ω).1=(run u ω).1 at hω
      have hmono := seedRun_count_mono e f a s k H θ z b j q ω
      have hlow := hmono (Nat.le_add_right u n)
      have hhigh := hmono (show u+n≤u+(n+1) by omega)
      change (run u ω).1 ≤ (run (u+n) ω).1 at hlow
      change (run (u+n) ω).1 ≤ (run (u+(n+1)) ω).1 at hhigh
      have he : (run (u+n) ω).1=(run u ω).1 := by omega
      refine ⟨⟨hω.1,he⟩,fun ht => ?_⟩
      have ht' := seedStateStep_strict e f (seedHeight a H (u+n)) s k H θ z b j (run (u+n) ω) ω (he.symm ▸ hω.1) ht
      change (run (u+n) ω).1<(run (u+n+1) ω).1 at ht'
      have he' : (run (u+n+1) ω).1=(run u ω).1 :=
        (congrArg (fun t => (run t ω).1) (by omega : u+n+1=u+(n+1))).trans hω.2
      omega
    apply (measure_mono hs).trans
    exact seed_fresh_test_bound ν e (seedHeight a H (u+n)) (run (u+n))
      (seedRun_measurable e f a s k hH θ z b j q (u+n)) (E n) (hm n)
      {p | ¬seedSplitTest e f (seedHeight a H (u+n)) s H θ b j p.1 p.2}
      (seedSplitTest_joint_rows e f (seedHeight a H (u+n)) s hH θ b j (seedAbove e (seedHeight a H (u+n)))
        (strip_subset_seedAbove e (seedHeight a H (u+n)) H)).compl ρ (fun η _ => hf _ _)
  change environmentLaw ν (E N)≤ρ^N
  induction N with
  | zero => simpa using (measure_mono (μ:=environmentLaw ν) (Set.subset_univ (E 0)))
  | succ n ih =>
    calc
      _ ≤ ρ*environmentLaw ν (E n) := hb n
      _ ≤ ρ*ρ^n := by gcongr
      _ = ρ^(n+1) := by rw [pow_succ,mul_comm]

lemma monotone_count_failure_stall (v : ℕ → ℕ) (hv : Monotone v) (hzero : 1≤v 0)
    (k N : ℕ) (hk : 1≤k) (hfail : v ((k-1)*N)<k) :
    ∃ l<k-1, v (l*N)<k ∧ v ((l+1)*N)=v (l*N) := by
  by_contra h
  have hstrict (l : ℕ) (hl : l<k-1) : v (l*N)<v ((l+1)*N) := by
    have he : v ((l+1)*N)≠v (l*N) := fun he => h ⟨l,hl,
      (hv (Nat.mul_le_mul_right N (by omega))).trans_lt hfail,he⟩
    exact lt_of_le_of_ne (hv (Nat.mul_le_mul_right N (Nat.le_succ l))) (Ne.symm he)
  have hcount (l : ℕ) (hl : l≤k-1) : l+1≤v (l*N) := by
    induction l with
    | zero => simpa using hzero
    | succ l ih => have hh := hstrict l (by omega); have hi := ih (by omega); omega
  have hf := hcount (k-1) le_rfl
  omega

lemma seedRun_completion_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a s : ℤ) (k : ℕ) {H : ℕ} (hH : 0<H)
    (θ z b j : ℝ) (μ : SeedProfile e a) (hk : 1≤k) (ρ : ℝ≥0∞)
    (hf : ∀ (a : ℤ) (q : SeedState e a), environmentLaw ν {ω | ¬seedSplitTest e f a s H θ b j q ω}≤ρ)
    (N : ℕ) : environmentLaw ν {ω | (seedRun e f a s k H θ z b j (1,fun _ => μ) ((k-1)*N) ω).1<k} ≤ (k-1:ℕ)*ρ^N := by
  let run := seedRun e f a s k H θ z b j (1,fun _ => μ)
  let E := fun l => {ω : Environment d | (run (l*N) ω).1<k ∧ (run (l*N+N) ω).1=(run (l*N) ω).1}
  have hs : {ω | (run ((k-1)*N) ω).1<k} ⊆ ⋃ l∈Finset.range (k-1), E l := by
    intro ω hω
    obtain ⟨l,hl,hcount,he⟩ := monotone_count_failure_stall (fun n => (run n ω).1)
      (seedRun_count_mono e f a s k H θ z b j _ ω) (by exact le_rfl) k N hk hω
    exact Set.mem_iUnion.mpr ⟨l,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hl,hcount,(congrArg (fun t => (run t ω).1) (by simp [Nat.add_mul] : l*N+N=(l+1)*N)).trans he⟩⟩
  calc
    _ ≤ _ := measure_mono hs
    _ ≤ ∑ l∈Finset.range (k-1), environmentLaw ν (E l) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _l∈Finset.range (k-1), ρ^N := Finset.sum_le_sum fun l _ => seedRun_stall_probability ν e f a s k hH θ z b j _ ρ hf (l*N) N
    _ = _ := by simp

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedOptions
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedOptions_of_run {d : ℕ} (e f : Direction d) (a s : ℤ) (k h J L : ℕ)
    (θ z b j c : ℝ) (μ : SeedProfile e a) (hk : 1≤k) (hj : 0<j) (hc : 0 < c)
    (hs : s=1 ∨ s= -1) (hz : 0≤z) (ω : Environment d)
    (hg : 0≤b+z-2*(J:ℝ)*z)
    (hcount : (seedRun e f a s k h θ z b j (1,fun _ => μ) J ω).1=k)
    (hp : ∀ t<J, SeedPreserved e f (seedHeight a h t) s k h θ z c
      (seedRun e f a s k h θ z b j (1,fun _ => μ) t ω) ω)
    (ht : ∀ i<k, c≤(seedEndpointRaw e L (SeedCentral f L θ z)
      ((seedRun e f a s k h θ z b j (1,fun _ => μ) J ω).2 i).measure ω Set.univ).toReal) :
    SeedOptions f k s (b-z-2*(J:ℝ)*z)
      (((ENNReal.ofReal (min c j)/2)^J)*ENNReal.ofReal c)
      (seedEndpointRaw e (J*h+L) (fun _ _ => True) μ.measure ω) := by
  let q := seedRun e f a s k h θ z b j (1,fun _ => μ) J ω
  refine ⟨fun i => (seedAdvance e (seedHeight a h J) L (SeedCentral f L θ z) (q.2 i) ω).val,?_,?_⟩
  · intro i
    have hr := seedRun_retained e f a s k h θ z b j c μ hk hj.le hc.le J ω hp i.val (hcount.symm ▸ i.isLt)
    have hm : ENNReal.ofReal c ≤ seedEndpointRaw e L (SeedCentral f L θ z) (q.2 i).measure ω Set.univ := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal (ht i.val i.isLt)
    exact seedAdvance_retained e (seedHeight a h J) (J*h) L (SeedCentral f L θ z) μ.measure (q.2 i) ω _ _ hr hm
  · intro i t hit
    have ho := seedRun_ordered e f a s k h θ z b j c μ hk hj hc hs hz J ω hg hp i.val t.val hit (hcount.symm ▸ t.isLt)
    have hm (i : Fin k) : seedEndpointRaw e L (SeedCentral f L θ z) (q.2 i).measure ω Set.univ≠0 := by
      intro he
      have hh := ht i.val i.isLt
      change c≤(seedEndpointRaw e L (SeedCentral f L θ z) (q.2 i).measure ω Set.univ).toReal at hh
      rw [he,ENNReal.toReal_zero] at hh
      exact (not_le_of_gt hc) hh
    have hh := seedOrdered_central e f (seedHeight a h J) s L θ z (b+z-2*(J:ℝ)*z) hs (q.2 i) (q.2 t) ω (hm i) (hm t) ho
    convert hh using 1 <;> first | rfl | ring

lemma seed_tail_failure_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a : ℤ) (k : ℕ) {L : ℕ} (hL : 0<L) (θ z c : ℝ) (ε : ℝ≥0∞)
    (μ : Environment d → ℕ → SeedProfile e a)
    (hμ : @Measurable _ _ (rowSigma (seedBelow e a)) _ μ)
    (hc : ∀ μ : ProbabilityMeasure (Lattice d), environmentLaw ν {ω |
      (seedEndpointRaw e L (SeedCentral f L θ z) μ.toMeasure ω Set.univ).toReal < c} ≤ ε) :
    environmentLaw ν {ω | ∃ i<k, (seedEndpointRaw e L (SeedCentral f L θ z) (μ ω i).measure ω Set.univ).toReal < c} ≤ k*ε := by
  have hb (i : ℕ) : environmentLaw ν {ω | (seedEndpointRaw e L (SeedCentral f L θ z) (μ ω i).measure ω Set.univ).toReal < c}≤ε := by
    have hh := seed_fresh_test_bound ν e a (fun ω => μ ω i) ((measurable_pi_apply i).comp hμ)
      Set.univ MeasurableSet.univ
      {p : SeedProfile e a × Environment d | (seedEndpointRaw e L (SeedCentral f L θ z) p.1.measure p.2 Set.univ).toReal < c}
      (measurableSet_lt (seedProfileRaw_joint_rows e a hL (SeedCentral f L θ z) (seedAbove e a)
        (strip_subset_seedAbove e a L)) measurable_const) ε (fun η _ => hc (μ η i).val)
    simpa only [Set.mem_univ,true_and,Set.mem_ofPred_eq,measure_univ,mul_one] using hh
  have he : {ω | ∃ i<k, (seedEndpointRaw e L (SeedCentral f L θ z) (μ ω i).measure ω Set.univ).toReal < c} = ⋃ i∈Finset.range k,
      {ω | (seedEndpointRaw e L (SeedCentral f L θ z) (μ ω i).measure ω Set.univ).toReal < c} := by ext ω; simp
  rw [he]
  exact (measure_biUnion_finset_le _ _).trans ((Finset.sum_le_sum fun i _ => hb i).trans_eq (by simp))

lemma seedOptions_failure_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a s : ℤ) (k N : ℕ) {h L : ℕ} (hh : 0<h) (hL : 0<L)
    (θ z b j c : ℝ) (μ : SeedProfile e a) (hk : 1≤k) (hj : 0<j) (hc : 0 < c)
    (hs : s=1 ∨ s= -1) (hz : 0≤z) (ε ρ : ℝ≥0∞)
    (hg : 0≤b+z-2*((k-1)*N:ℕ)*z)
    (hclip : ∀ t∈({h,L}:Finset ℕ), ∀ μ : ProbabilityMeasure (Lattice d), environmentLaw ν {ω |
      (seedEndpointRaw e t (SeedCentral f t θ z) μ.toMeasure ω Set.univ).toReal < c}≤ε)
    (hjump : ∀ (a : ℤ) (q : SeedState e a), environmentLaw ν {ω | ¬seedSplitTest e f a s h θ b j q ω}≤ρ) :
    environmentLaw ν {ω | ¬SeedOptions f k s (b-z-2*((k-1)*N:ℕ)*z)
      (((ENNReal.ofReal (min c j)/2)^((k-1)*N))*ENNReal.ofReal c)
      (seedEndpointRaw e (((k-1)*N)*h+L) (fun _ _ => True) μ.measure ω)} ≤
        (k-1:ℕ)*ρ^N+((k-1)*N:ℕ)*(k*ε)+k*ε := by
  let J := (k-1)*N
  let run := seedRun e f a s k h θ z b j (1,fun _ => μ)
  let A := {ω | (run J ω).1<k}
  let B := {ω | ∃ t<J, ¬SeedPreserved e f (seedHeight a h t) s k h θ z c (run t ω) ω}
  let C := {ω | ∃ i<k, (seedEndpointRaw e L (SeedCentral f L θ z) ((run J ω).2 i).measure ω Set.univ).toReal < c}
  have hA : environmentLaw ν A≤(k-1:ℕ)*ρ^N := seedRun_completion_probability ν e f a s k hh θ z b j μ hk ρ hjump N
  have hB : environmentLaw ν B≤J*(k*ε) := seedRun_preservation_failure ν e f a s k hh θ z b j c ε μ hk (hclip h (by simp)) J
  have hC : environmentLaw ν C≤k*ε := seed_tail_failure_bound ν e f (seedHeight a h J) k hL θ z c ε
    (fun ω => (run J ω).2) (measurable_snd.comp (seedRun_measurable e f a s k hh θ z b j _ J)) (hclip L (by simp))
  have he : {ω | ¬SeedOptions f k s (b-z-2*(J:ℝ)*z)
      (((ENNReal.ofReal (min c j)/2)^J)*ENNReal.ofReal c)
      (seedEndpointRaw e (J*h+L) (fun _ _ => True) μ.measure ω)} ⊆ (A∪B)∪C := by
    intro ω hω
    by_contra hn
    have ha : ω∉A := fun ha => hn (Or.inl (Or.inl ha))
    have hb : ω∉B := fun hb => hn (Or.inl (Or.inr hb))
    have hc' : ω∉C := fun hc => hn (Or.inr hc)
    apply hω
    apply seedOptions_of_run e f a s k h J L θ z b j c μ hk hj hc hs hz ω hg
    · have hcount := (seedRun_count_bounds e f a s k h θ z b j (1,fun _ => μ) (by norm_num) hk J ω).2
      exact le_antisymm hcount (Nat.le_of_not_gt ha)
    · intro t ht
      exact not_not.mp (fun hbad => hb ⟨t,ht,hbad⟩)
    · intro i hi
      exact le_of_not_gt (fun hbad => hc' ⟨i,hi,hbad⟩)
  exact (measure_mono he).trans ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add hA hB)) hC))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedOrdered_near_impossible {d : ℕ} (f : Direction d) (s : ℤ) (g r : ℝ)
    (hs : s=1 ∨ s= -1) (hg : 2*r<g) (μ ρ : Measure (Lattice d))
    (ho : SeedOrdered f s g μ ρ) (x y z : Lattice d) (hx : μ {x}≠0) (hy : ρ {y}≠0)
    (hxn : |signedCoordinate f x-signedCoordinate f z| < r)
    (hyn : |signedCoordinate f y-signedCoordinate f z| < r) : False := by
  have hh := ho x hx y hy
  rw [abs_lt] at hxn hyn
  rcases hs with rfl | rfl <;> norm_num at hh <;> linarith [hxn.1,hxn.2,hyn.1,hyn.2]

lemma seedOptions_avoid_mass {d k n : ℕ} (f : Direction d) (s : ℤ) (g r : ℝ)
    (hs : s=1 ∨ s= -1) (hg : 2*r<g) (δ : ℝ≥0∞) (ρ : Measure (Lattice d))
    (ho : SeedOptions f k s g δ ρ) (hn : n<k) (v : Fin n → Lattice d) :
    δ ≤ ρ {x | ∀ j, r≤|signedCoordinate f x-signedCoordinate f (v j)|} := by
  obtain ⟨μ,hdom,hord⟩ := ho
  have hex : ∃ i : Fin k, ∀ x, (μ i).toMeasure {x}≠0 → ∀ j : Fin n,
      r≤|signedCoordinate f x-signedCoordinate f (v j)| := by
    by_contra hnex
    have hbad (i : Fin k) : ∃ j : Fin n, ∃ x, (μ i).toMeasure {x}≠0 ∧
        |signedCoordinate f x-signedCoordinate f (v j)| < r := by
      have hi : ¬∀ x, (μ i).toMeasure {x}≠0 → ∀ j : Fin n,
          r≤|signedCoordinate f x-signedCoordinate f (v j)| := fun hi => hnex ⟨i,hi⟩
      push Not at hi
      obtain ⟨x,hx,j,hj⟩ := hi
      exact ⟨j,x,hx,hj⟩
    choose j x hx hnear using hbad
    have hj : Function.Injective j := by
      intro i t he
      by_contra hit
      rcases lt_or_gt_of_ne hit with hit | hti
      · exact seedOrdered_near_impossible f s g r hs hg _ _ (hord i t hit) (x i) (x t) (v (j i)) (hx i) (hx t)
          (hnear i) (he.symm ▸ hnear t)
      · exact seedOrdered_near_impossible f s g r hs hg _ _ (hord t i hti) (x t) (x i) (v (j i)) (hx t) (hx i)
          (he.symm ▸ hnear t) (hnear i)
    have hc := Fintype.card_le_of_injective j hj
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨i,hi⟩ := hex
  have hae : ∀ᵐ x ∂(μ i).toMeasure, ∀ j, r≤|signedCoordinate f x-signedCoordinate f (v j)| :=
    ae_iff_of_countable.mpr hi
  have hm : (μ i).toMeasure {x | ∀ j, r≤|signedCoordinate f x-signedCoordinate f (v j)|}=1 :=
    (prob_compl_eq_zero_iff (Set.to_countable _).measurableSet).mp (ae_iff.mp hae)
  have hh := hdom i {x | ∀ j, r≤|signedCoordinate f x-signedCoordinate f (v j)|}
  simpa only [Measure.smul_apply,smul_eq_mul,hm,mul_one] using hh

lemma countable_pi_cons_apply {A : Type*} [MeasurableSpace A] [Countable A]
    [MeasurableSingletonClass A] (n : ℕ) (μ : Fin (n+1) → Measure A) [∀ i, SigmaFinite (μ i)]
    (S : Set (Fin (n+1) → A)) :
    Measure.pi μ S = ∫⁻ t, μ 0 {x | Fin.cons x t∈S} ∂Measure.pi (fun j => μ j.succ) := by
  have hm := (measurePreserving_piFinSuccAbove μ 0).symm.map_eq
  rw [← hm,Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    Measure.prod_apply_symm (Set.to_countable _).measurableSet]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero,Fin.zero_succAbove]
  rfl

lemma tupleSeparated_cons {d n : ℕ} (f : Direction d) (r : ℝ) (x : Lattice d) (v : Fin n → Lattice d)
    (hv : TupleSeparated f r v) (hx : ∀ j, r≤|signedCoordinate f x-signedCoordinate f (v j)|) :
    TupleSeparated f r (Fin.cons x v) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j => simpa using hx j
  | succ i =>
    cases j using Fin.cases with
    | zero => simpa only [Fin.cons_succ,Fin.cons_zero,abs_sub_comm] using hx i
    | succ j => simpa only [Fin.cons_succ] using hv i j (fun he => hij (congrArg Fin.succ he))

lemma seedOptions_product_mass {d k n : ℕ} (f : Direction d) (s : ℤ) (g r : ℝ)
    (hs : s=1 ∨ s= -1) (hg : 2*r<g) (δ : ℝ≥0∞) (μ : Fin n → Measure (Lattice d))
    [∀ i, IsFiniteMeasure (μ i)] (hn : n≤k)
    (ho : ∀ i, SeedOptions f k s g δ (μ i)) :
    δ^n ≤ Measure.pi μ {v | TupleSeparated f r v} := by
  induction n with
  | zero =>
    have he : {v : Fin 0 → Lattice d | TupleSeparated f r v}=Set.univ := by
      ext v; simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]; intro i; exact Fin.elim0 i
    rw [he,Measure.pi_univ,pow_zero]
    simp
  | succ n ih =>
    have hi := ih (fun i => μ i.succ) (by omega) (fun i => ho i.succ)
    rw [countable_pi_cons_apply]
    have hb (v : Fin n → Lattice d) :
        {v | TupleSeparated f r v}.indicator (fun _ => δ) v ≤ μ 0 {x | TupleSeparated f r (Fin.cons x v)} := by
      by_cases hv : TupleSeparated f r v
      · simp only [Set.indicator,Set.mem_ofPred_eq,ite_eq_left hv]
        exact (seedOptions_avoid_mass f s g r hs hg δ (μ 0) (ho 0) (by omega) v).trans
          (measure_mono fun x hx => tupleSeparated_cons f r x v hv hx)
      · simp only [Set.indicator,Set.mem_ofPred_eq,ite_eq_right hv]; exact bot_le
    calc
      δ^(n+1) = δ*δ^n := by rw [pow_succ,mul_comm]
      _ ≤ δ*Measure.pi (fun i => μ i.succ) {v | TupleSeparated f r v} := by gcongr
      _ = ∫⁻ v, {v | TupleSeparated f r v}.indicator (fun _ => δ) v ∂Measure.pi (fun i => μ i.succ) := by
        rw [lintegral_indicator (Set.to_countable _).measurableSet,lintegral_const,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
      _ ≤ _ := lintegral_mono hb

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedUniform
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedOptions_mono {d : ℕ} (f : Direction d) (k : ℕ) (s : ℤ) {g g' : ℝ}
    (hg : g'≤g) (δ : ℝ≥0∞) (ρ : Measure (Lattice d)) :
    SeedOptions f k s g δ ρ → SeedOptions f k s g' δ ρ := by
  rintro ⟨μ,hd,ho⟩
  exact ⟨μ,hd,fun i j hij => seedOrdered_mono f s (ho i j hij) hg⟩

theorem seed_uniform_options {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) (hk : 1≤k) (p : ℝ) (hp : 0<p) :
    ∃ C A R : ℝ, ∃ δ : ℝ≥0∞, 0<C ∧ 0<A ∧ 0<R ∧ 0<δ ∧
    ∀ r : ℝ, R ≤ r → ∀ H : ℕ,
      (H:ℝ)=C*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      ∃ s : ℤ, (s=1 ∨ s= -1) ∧ ∀ (a : ℤ) (μ : SeedProfile e a),
        environmentLaw ν {ω | ¬SeedOptions f k s (A*r) δ
          (seedEndpointRaw e H (fun _ _ => True) μ.measure ω)} ≤ ENNReal.ofReal p := by
  obtain ⟨b,j,hb,hj,hj1,htests⟩ := seed_block_tests ν hue e f hef htrans
  have hρ : 0≤1-j := by linarith
  have hρ1 : 1-j<1 := by linarith
  have hlim : Tendsto (fun n : ℕ => ((k-1:ℕ):ℝ)*(1-j)^n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1) :
      Tendsto (fun n : ℕ => ((k-1:ℕ):ℝ)*(1-j)^n) atTop (nhds (((k-1:ℕ):ℝ)*0)))
  obtain ⟨N,hN⟩ := (hlim.eventually (gt_mem_nhds (show (0:ℝ)<p/2 by positivity))).exists
  let J := (k-1)*N
  let C : ℝ := 2*(J+1)
  let η : ℝ := b/(4*(2*J+1))
  let ε : ℝ := p/(2*((J+1)*k+1))
  have hC : 0<C := by dsimp [C] <;> positivity
  have hη : 0<η := by dsimp [η] <;> positivity
  have hε : 0<ε := by dsimp [ε] <;> positivity
  have hηeq : (2*(J:ℝ)+1)*η=b/4 := by dsimp [η]; field_simp
  have hεeq : ((J:ℝ)+1)*k*ε≤p/2 := by
    have he : (2*(((J:ℝ)+1)*k+1))*ε=p := by dsimp [ε]; field_simp
    nlinarith [hε.le]
  obtain ⟨c,R,hc,hR,hrest⟩ := htests C η ε hC hη hε
  let δ := (ENNReal.ofReal (min c j)/2)^J*ENNReal.ofReal c
  have hδ : 0<δ := ENNReal.mul_pos_iff.mpr ⟨ENNReal.pow_pos (ENNReal.div_pos
    (ne_of_gt (ENNReal.ofReal_pos.mpr (lt_min hc hj))) (by norm_num)) J, ENNReal.ofReal_pos.mpr hc⟩
  refine ⟨C,b/2,R,δ,hC,by positivity,hR,hδ,fun r hr H hH => ?_⟩
  obtain ⟨hh,θ,s,hs,hclip,hjump⟩ := hrest r hr
  let n := fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) r
  let h := ⌊n⌋₊
  have hn : 0<n := by exact (Nat.floor_pos.mp hh).trans_lt' (by norm_num)
  have hhn : (h:ℝ)≤n := Nat.floor_le hn.le
  have hJ : (J*h:ℕ)<H := by
    have hreal : ((J*h:ℕ):ℝ)<H := by
      rw [Nat.cast_mul,hH]
      change (J:ℝ)*(h:ℝ)<C*n
      have hle := mul_le_mul_of_nonneg_left hhn (show (0:ℝ)≤J by positivity)
      dsimp [C] at *
      nlinarith
    exact_mod_cast hreal
  let L := H-J*h
  have hL : 0<L := by dsimp [L]; omega
  have hsum : J*h+L=H := by dsimp [L]; omega
  have hz : 0≤η*r := mul_nonneg hη.le (hR.le.trans hr)
  have hgap : b/2*r ≤ b*r-η*r-2*(J:ℝ)*(η*r) := by
    have heq : b*r-η*r-2*(J:ℝ)*(η*r)=(b-(2*(J:ℝ)+1)*η)*r := by ring
    rw [heq,hηeq]
    nlinarith [hR.le.trans hr]
  have hg : 0≤b*r+η*r-2*(J:ℝ)*(η*r) := by
    have hpos : 0≤b/2*r := mul_nonneg (by positivity) (hR.le.trans hr)
    linarith
  refine ⟨s,hs,fun a μ => ?_⟩
  have hc' (t : ℕ) (ht : t∈({h,L}:Finset ℕ)) (μ : ProbabilityMeasure (Lattice d)) :
      environmentLaw ν {ω | (seedEndpointRaw e t (SeedCentral f t θ (η*r)) μ.toMeasure ω Set.univ).toReal < c}≤ENNReal.ofReal ε := by
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε.le).mpr
    apply hclip
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hhn.trans (by change n≤C*n; dsimp [C] <;> nlinarith)
    · have hlo : L≤H := by dsimp [L]; omega
      exact (Nat.cast_le.mpr hlo).trans_eq hH
  have hj' (a : ℤ) (q : SeedState e a) :
      environmentLaw ν {ω | ¬seedSplitTest e f a s h θ (b*r) j q ω}≤ENNReal.ofReal (1-j) := by
    have hmeas : MeasurableSet {ω | seedSplitTest e f a s h θ (b*r) j q ω} := by
      have hm := (seedSplitTest_joint_rows e f a s hh θ (b*r) j (seedAbove e a)
        (strip_subset_seedAbove e a h )).preimage (f := fun ω => (q,ω)) (measurable_const.prodMk measurable_id)
      exact (rowSigma_le _ _ hm)
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hρ).mpr
    change (environmentLaw ν).real {ω | ¬seedSplitTest e f a s h θ (b*r) j q ω}≤1-j
    rw [show {ω | ¬seedSplitTest e f a s h θ (b*r) j q ω} = {ω | seedSplitTest e f a s h θ (b*r) j q ω}ᶜ by rfl,
      measureReal_compl hmeas]
    simp only [measureReal_def,measure_univ,ENNReal.toReal_one]
    have hh := hjump (seedJumpInput e f a s q).val
    change j≤(environmentLaw ν).real {ω | seedSplitTest e f a s h θ (b*r) j q ω} at hh
    simpa only [measureReal_def] using (sub_le_sub_left hh 1)
  have hbound := seedOptions_failure_bound ν e f a s k N hh hL θ (η*r) (b*r) j c μ hk hj hc hs hz
    (ENNReal.ofReal ε) (ENNReal.ofReal (1-j)) hg hc' hj'
  have hsub : {ω | ¬SeedOptions f k s (b/2*r) δ (seedEndpointRaw e H (fun _ _ => True) μ.measure ω)} ⊆
      {ω | ¬SeedOptions f k s (b*r-η*r-2*(J:ℝ)*(η*r)) δ
        (seedEndpointRaw e (J*h+L) (fun _ _ => True) μ.measure ω)} := by
    intro ω hω ho
    rw [hsum] at ho
    exact hω (seedOptions_mono f k s hgap δ _ ho)
  apply (measure_mono hsub).trans (hbound.trans _)
  have he : (k-1:ℕ)*(ENNReal.ofReal (1-j))^N+(J:ℕ)*(k*ENNReal.ofReal ε)+k*ENNReal.ofReal ε =
      ENNReal.ofReal (((k-1:ℕ):ℝ)*(1-j)^N+((J:ℝ)+1)*k*ε) := by
    have hp₁ : 0≤((k-1:ℕ):ℝ)*(1-j)^N := by positivity
    have hp₂ : 0≤((J:ℝ)+1)*k*ε := by positivity
    rw [ENNReal.ofReal_add hp₁ hp₂, ENNReal.ofReal_mul (by positivity : (0:ℝ)≤(k-1:ℕ)),
      ENNReal.ofReal_natCast,ENNReal.ofReal_pow hρ, ENNReal.ofReal_mul (by positivity : (0:ℝ)≤((J:ℝ)+1)*k),
      ENNReal.ofReal_mul (by positivity : (0:ℝ)≤(J:ℝ)+1),
      ENNReal.ofReal_add (by positivity : (0:ℝ)≤J) (by norm_num),ENNReal.ofReal_one,
      ENNReal.ofReal_natCast,ENNReal.ofReal_natCast]
    ring
  change (k-1:ℕ)*(ENNReal.ofReal (1-j))^N+J*(k*ENNReal.ofReal ε)+k*ENNReal.ofReal ε≤ENNReal.ofReal p
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  linarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedPoint_raw {d : ℕ} (e : Direction d) (H : ℕ) (x : Lattice d) (ω : Environment d) :
    seedEndpointRaw e H (fun _ _ => True) (seedPoint e x).measure ω =
      variableHitKernel (realPosition (step e)) H (ω,x) := by
  simp only [seedEndpointRaw,seedPoint,SeedProfile.measure,ProbabilityMeasure.coe_mk,
    Set.ofPred_true,Measure.restrict_univ]
  exact Measure.dirac_bind (measurable_of_countable _) x

lemma seed_tuple_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (k H : ℕ) (s : ℤ) (hs : s=1 ∨ s= -1) (r g : ℝ) (hg : 2*r<g)
    (δ ε : ℝ≥0∞) (hoptions : ∀ x : Lattice d, environmentLaw ν {ω | ¬SeedOptions f k s g δ
      (variableHitKernel (realPosition (step e)) H (ω,x))}≤ε)
    (v : Fin k → Lattice d) :
    environmentLaw ν {ω | rawTupleEndpointLaw (realPosition (step e)) H ω v {y | TupleSeparated f r y}<δ^k}≤k*ε := by
  have hsub : {ω | rawTupleEndpointLaw (realPosition (step e)) H ω v {y | TupleSeparated f r y}<δ^k} ⊆
      ⋃ i : Fin k, {ω | ¬SeedOptions f k s g δ (variableHitKernel (realPosition (step e)) H (ω,v i))} := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,not_exists,not_not] at hn
    have hh := seedOptions_product_mass f s g r hs hg δ
      (fun i : Fin k => variableHitKernel (realPosition (step e)) H (ω,v i)) le_rfl hn
    exact (not_lt_of_ge hh) hω
  exact (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
    ((Finset.sum_le_sum fun i _ => hoptions (v i)).trans_eq (by simp)))

theorem seed_mass_at_scale_oai {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) (hk : 2≤k) (p : ℝ) (hp : 0<p) :
    ∃ C c₀ g₀ R : ℝ, 0<C ∧ 0 < c₀ ∧ 0<g₀ ∧ 0<R ∧
    ∀ r : ℝ, R ≤ r → ∀ H : ℕ,
      (H:ℝ)=C*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      ∀ π : ProbabilityMeasure (Fin k → Lattice d),
        1-p < (environmentLaw ν).real {ω | ENNReal.ofReal g₀≤
          rawTupleMixture (realPosition (step e)) H π.toMeasure ω {v | TupleSeparated f (c₀*r) v}} := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  let ε := p/(4*k)
  have hε : 0<ε := div_pos hp (by positivity)
  obtain ⟨C,A,R,δ,hC,hA,hR,hδ,hopt⟩ := seed_uniform_options ν hue e f hef htrans k (by omega) ε hε
  let D := (min δ 1)^k
  have hD : 0<D := ENNReal.pow_pos (lt_min hδ (by norm_num)) k
  have hD1 : D≤1 := by exact pow_le_one₀ (show (0:ℝ≥0∞) ≤ min δ 1 from bot_le) (min_le_right _ _)
  have hDt : D≠⊤ := ne_top_of_le_ne_top (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hD1
  have hDr : 0<D.toReal := ENNReal.toReal_pos (ne_of_gt hD) hDt
  refine ⟨C,A/4,D.toReal/2,R,hC,by positivity,by positivity,hR,fun r hr H hH π => ?_⟩
  obtain ⟨s,hs,hsall⟩ := hopt r hr H hH
  have hopt' (x : Lattice d) : environmentLaw ν {ω | ¬SeedOptions f k s (A*r) δ
      (variableHitKernel (realPosition (step e)) H (ω,x))}≤ENNReal.ofReal ε := by
    simpa only [seedPoint_raw] using hsall (signedHeight e x) (seedPoint e x)
  have hgap : 2*(A/4*r)<A*r := by nlinarith [hR.trans_le hr]
  let S := {v : Fin k → Lattice d | TupleSeparated f (A/4*r) v}
  let F : Environment d → (Fin k → Lattice d) → ℝ := fun ω v =>
    (rawTupleEndpointLaw (realPosition (step e)) H ω v S).toReal
  have hF : Measurable (Function.uncurry F) :=
    ((Measure.measurable_coe (Set.to_countable _).measurableSet).comp
      (measurable_rawTupleEndpointLaw _ _)).ennreal_toReal
  have hF0 (ω) (v) : 0≤F ω v := ENNReal.toReal_nonneg
  have hF1 (ω) (v) : F ω v≤1 := by
    apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
    simpa using (measure_mono (Set.subset_univ S) |>.trans (rawTupleEndpointLaw_le_one _ _ ω v))
  have hbad (v : Fin k → Lattice d) : (environmentLaw ν).real {ω | F ω v<2*(D.toReal/2)}≤k*ε := by
    have hsub : {ω | F ω v<2*(D.toReal/2)} ⊆
        {ω | rawTupleEndpointLaw (realPosition (step e)) H ω v S<δ^k} := by
      intro ω hω
      have hd : D≤δ^k := by dsimp [D]; gcongr; exact min_le_left _ _
      by_contra hn
      have hl : D ≤ rawTupleEndpointLaw (realPosition (step e)) H ω v S := hd.trans (not_lt.mp hn)
      have hh := ENNReal.toReal_mono (measure_ne_top _ _) hl
      change D.toReal≤F ω v at hh
      change F ω v<2*(D.toReal/2) at hω
      linarith
    have hb := seed_tuple_failure ν e f k H s hs (A/4*r) (A*r) hgap δ (ENNReal.ofReal ε) hopt' v
    have hbu : environmentLaw ν {ω | F ω v<2*(D.toReal/2)}≤ENNReal.ofReal ((k:ℝ)*ε) := by
      rw [ENNReal.ofReal_mul hk0.le,ENNReal.ofReal_natCast]
      exact (measure_mono hsub).trans hb
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbu
  have hm := mixture_small_mass_probability (environmentLaw ν) π.toMeasure F hF hF0 hF1
    (show 0<D.toReal/2 by positivity) hbad
  have hint (ω : Environment d) : (∫ v, F ω v ∂π.toMeasure) =
      (rawTupleMixture (realPosition (step e)) H π.toMeasure ω S).toReal := by
    rw [rawTupleMixture_apply]
    exact integral_toReal (measurable_of_countable _).aemeasurable (ae_of_all _ fun v => measure_lt_top _ _)
  have hmf : Measurable (fun ω => (rawTupleMixture (realPosition (step e)) H π.toMeasure ω S).toReal) := by
    have hh : Measurable (fun ω => ∫ v, F ω v ∂π.toMeasure) := hF.stronglyMeasurable.integral_prod_right.measurable
    simpa only [hint] using hh
  have hmass (ω : Environment d) : rawTupleMixture (realPosition (step e)) H π.toMeasure ω S≤1 := by
    rw [rawTupleMixture_apply]
    exact (lintegral_mono fun v => (measure_mono (Set.subset_univ S)).trans (rawTupleEndpointLaw_le_one _ _ ω v)).trans_eq (by simp)
  have he : {ω | ENNReal.ofReal (D.toReal/2) ≤ rawTupleMixture (realPosition (step e)) H π.toMeasure ω S} =
      {ω | (rawTupleMixture (realPosition (step e)) H π.toMeasure ω S).toReal<D.toReal/2}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_compl_iff,not_lt]
    exact ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (hmass ω))
  rw [he,measureReal_compl (measurableSet_lt hmf measurable_const)]
  simp only [hint] at hm
  have heps : 2*((k:ℝ)*ε)=p/2 := by dsimp [ε]; field_simp <;> ring
  rw [heps] at hm
  have hu : (environmentLaw ν).real Set.univ=1 := by simp [measureReal_def]
  rw [hu]
  linarith

end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.seed_mass_at_scale_oai := @OAI.DirectionalTransience.seed_mass_at_scale_oai
