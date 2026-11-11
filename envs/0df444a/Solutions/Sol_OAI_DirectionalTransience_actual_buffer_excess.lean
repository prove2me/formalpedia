-- Prove2me | solution 1 for OAI.DirectionalTransience.actual_buffer_excess
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:58:10.117211+00:00
-- url     : https://prove2.me/submissions/c33c22f6-cec3-4906-aeef-69649a805302

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal007
import Theorems.Thm_OAI_DirectionalTransience_clipped_pair_favorable_fraction

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_FreshWeightedTest
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
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

lemma independent_random_test_weighted_lower {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → A) (V : Ω → B) (hU : Measurable U) (hV : Measurable V)
    (hind : IndepFun U V μ) (E : Set A) (hE : MeasurableSet E)
    (G : Set (A × B)) (hG : MeasurableSet G) (w : A → ℝ≥0∞) (hw : Measurable w)
    (c : ℝ≥0∞) (hbound : ∀ a ∈ E, c ≤ (μ.map V) {b | (a,b) ∈ G}) :
    c*(∫⁻ ω in U ⁻¹' E, w (U ω) ∂μ) ≤
      ∫⁻ ω in {ω | U ω ∈ E ∧ (U ω,V ω) ∈ G}, w (U ω) ∂μ := by
  let K : Set (A × B) := (E ×ˢ Set.univ) ∩ G
  have hK : MeasurableSet K := (hE.prod MeasurableSet.univ).inter hG
  have hUV : Measurable (fun ω => (U ω,V ω)) := hU.prodMk hV
  have he : {ω | U ω ∈ E ∧ (U ω,V ω) ∈ G} = (fun ω => (U ω,V ω)) ⁻¹' K := by
    ext ω; simp [K]
  have hf : Measurable (K.indicator (fun p : A × B => w p.1)) := (hw.comp measurable_fst).indicator hK
  have hpush : (∫⁻ ω in {ω | U ω ∈ E ∧ (U ω,V ω) ∈ G}, w (U ω) ∂μ) =
      ∫⁻ p, K.indicator (fun q => w q.1) p ∂(μ.map U).prod (μ.map V) := by
    rw [he,←lintegral_indicator (hK.preimage hUV)]
    have heind : (fun ω => ((fun ω => (U ω,V ω)) ⁻¹' K).indicator (fun ω => w (U ω)) ω) =
        fun ω => K.indicator (fun p : A × B => w p.1) (U ω,V ω) := by
      funext ω
      by_cases h : (U ω,V ω) ∈ K <;> simp [h]
    rw [heind,←lintegral_map hf hUV,
      hind.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable]
  rw [hpush,lintegral_prod _ hf.aemeasurable]
  have hlow : (∫⁻ a, (E.indicator (fun _ => c*w a)) a ∂μ.map U) ≤
      ∫⁻ a, ∫⁻ b, K.indicator (fun p => w p.1) (a,b) ∂μ.map V ∂μ.map U := by
    apply lintegral_mono
    intro a
    dsimp only
    by_cases ha : a ∈ E
    · rw [Set.indicator_of_mem ha]
      have heq : (fun b => K.indicator (fun p => w p.1) (a,b)) =
          {b | (a,b) ∈ G}.indicator (fun _ => w a) := by
        funext b
        by_cases hb : (a,b) ∈ G <;> simp [K,ha,hb]
      have hslice : MeasurableSet {b | (a,b) ∈ G} := hG.preimage measurable_prodMk_left
      rw [heq,lintegral_indicator hslice,lintegral_const]
      simp only [Measure.restrict_apply_univ]
      calc
        c*w a ≤ (μ.map V) {b | (a,b) ∈ G}*w a := by gcongr; exact hbound a ha
        _ = w a*(μ.map V) {b | (a,b) ∈ G} := mul_comm _ _
    · rw [Set.indicator_of_notMem ha]
      exact zero_le
  refine LE.le.trans ?_ hlow
  rw [←lintegral_indicator (hE.preimage hU)]
  have heind2 : (fun ω => (U ⁻¹' E).indicator (fun ω => w (U ω)) ω) =
      fun ω => E.indicator w (U ω) := by
    funext ω
    by_cases h : U ω ∈ E <;> simp [h]
  rw [heind2,←lintegral_map (hw.indicator hE) hU]
  rw [←lintegral_const_mul c (hw.indicator hE)]
  apply le_of_eq
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ E <;> simp [ha]
end DirectionalTransience

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

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma firstLayerHit_record {d : ℕ} (ℓ : Vector d) (h : Lattice d → ℤ)
    (hproj : ∀ x, dot (realPosition x) ℓ = (h x : ℝ)) (H : ℤ) (n : ℕ)
    (X : Path d) (hX : X ∈ FirstLayerHit h H n) : StrictRecord ℓ X n := by
  intro j hj
  rw [hproj,hproj,hX.1]
  exact_mod_cast hX.2 j hj

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FixedPairSuffix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstHitPairGap
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
namespace DirectionalTransience

lemma recordIndexTime_zero {d : ℕ} (ℓ : Vector d) (X : Path d) : recordIndexTime ℓ 0 X = 0 := by
  classical
  have hn : ¬ ∃ n, X ∈ RecordIndexPrefix ℓ 0 n := by
    rintro ⟨n,hn,hr,hc,_⟩
    have hh := recordCount_lt_of_strictRecord ℓ X hn hr
    simp only [recordCount_zero,hc,lt_self_iff_false] at hh
  simp only [recordIndexTime,dite_eq_right hn]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AlignedRecordPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
namespace DirectionalTransience

lemma recordOrZeroPrefix_time {d : ℕ} (ℓ : Vector d) {r n : ℕ} {X : Path d}
    (hX : X ∈ RecordOrZeroPrefix ℓ r n) : recordIndexTime ℓ r X = n := by
  by_cases hr : r = 0
  · subst r
    have : n = 0 := by simpa [RecordOrZeroPrefix] using hX
    rw [this,recordIndexTime_zero]
  · exact recordIndexTime_eq ℓ r n X (by simpa [RecordOrZeroPrefix,hr] using hX)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_EndpointPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
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

lemma coordinate_hitAt_record {d : ℕ} (e : Direction d) (x : Lattice d) (X : Path d)
    (h0 : X 0=x) (hnn : ∀ n, ∃ f, X (n+1)=X n+step f) {H n : ℕ} (hH : 0 < H)
    (hX : X ∈ HitAt (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) n) :
    recordIndexPosition (realPosition (step e)) H (fun j => X j-x)=X n-x := by
  let ℓ := realPosition (step e)
  let Y : Path d := fun j => X j-x
  have hy0 : Y 0=0 := by simp [Y,h0]
  have hheight := coordinate_hitAt_exact e x X h0 hnn H n hX
  have hadd (u v : Lattice d) : signedHeight e (u-v)=signedHeight e u-signedHeight e v := by
    simp only [signedHeight,Pi.sub_apply]
    split_ifs <;> ring
  have hfirst : Y ∈ FirstLayerHit (signedHeight e) H n := by
    refine ⟨?_,?_⟩
    · simp only [Y,hadd,hheight,add_sub_cancel_left]
    · intro j hj
      have hh := (hX.2 j hj).2
      change dot (realPosition (X j)) ℓ < dot (realPosition x) ℓ+(H:ℝ) at hh
      rw [signedHeight_projection,signedHeight_projection] at hh
      change signedHeight e (X j-x) < (H:ℤ)
      rw [hadd]
      exact_mod_cast (show (signedHeight e (X j):ℝ)-(signedHeight e x:ℝ) < (H:ℝ) by linarith)
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n=0 := by omega
    have hh := hfirst.1
    rw [hn0,hy0] at hh
    simp only [signedHeight,Pi.zero_apply,ite_self,neg_zero] at hh
    omega
  have hrec := firstLayerHit_record ℓ (signedHeight e) (signedHeight_projection e) H n Y hfirst
  have hsteps (j : ℕ) : signedHeight e (Y (j+1)) ≤ signedHeight e (Y j)+1 := by
    obtain ⟨g,hg⟩ := hnn j
    have he : Y (j+1)=Y j+step g := by dsimp [Y]; rw [hg]; abel
    rw [he]
    exact signedHeight_step_le e _ g
  have hcount := recordCount_eq_height_at_record ℓ (signedHeight e) (signedHeight_projection e) Y hsteps hrec
  rw [hfirst.1,hy0,show signedHeight e (0:Lattice d)=0 by simp [signedHeight],zero_add] at hcount
  have hr : Y ∈ RecordIndexPrefix ℓ H n := by
    refine ⟨hn,hrec,by exact_mod_cast hcount.symm,?_⟩
    intro j hj
    have hh : dot (realPosition x) ℓ ≤ dot (realPosition (X j)) ℓ := by
      rcases lt_or_eq_of_le hj with hj | rfl
      · exact (hX.2 j hj).1
      · have hh := hX.1
        change dot (realPosition x) ℓ+(H:ℝ) ≤ dot (realPosition (X j)) ℓ at hh
        linarith [show (0:ℝ) ≤ H by positivity]
    change dot (realPosition (0:Lattice d)) ℓ ≤ dot (realPosition (X j-x)) ℓ
    rw [dot_realPosition_sub]
    simpa only [dot,realPosition,Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero,sub_nonneg] using hh
  change X (recordIndexTime ℓ H Y)-x=X n-x
  rw [recordIndexTime_eq ℓ H n Y hr]

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurveWordDisjoint
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma coordinate_hitAt_recordPrefix {d : ℕ} (e : Direction d) (x : Lattice d) (X : Path d)
    (h0 : X 0=x) (hnn : ∀ n, ∃ f, X (n+1)=X n+step f) {H n : ℕ} (hH : 0 < H)
    (hX : X ∈ HitAt (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) n) :
    (fun j => X j-x) ∈ RecordIndexPrefix (realPosition (step e)) H n := by
  let ℓ := realPosition (step e)
  let Y : Path d := fun j => X j-x
  have hy0 : Y 0=0 := by simp [Y,h0]
  have hheight := coordinate_hitAt_exact e x X h0 hnn H n hX
  have hadd (u v : Lattice d) : signedHeight e (u-v)=signedHeight e u-signedHeight e v := by
    simp only [signedHeight,Pi.sub_apply]
    split_ifs <;> ring
  have hfirst : Y ∈ FirstLayerHit (signedHeight e) H n := by
    refine ⟨?_,?_⟩
    · simp only [Y,hadd,hheight,add_sub_cancel_left]
    · intro j hj
      have hh := (hX.2 j hj).2
      change dot (realPosition (X j)) ℓ < dot (realPosition x) ℓ+(H:ℝ) at hh
      rw [signedHeight_projection,signedHeight_projection] at hh
      change signedHeight e (X j-x) < (H:ℤ)
      rw [hadd]
      exact_mod_cast (show (signedHeight e (X j):ℝ)-(signedHeight e x:ℝ) < (H:ℝ) by linarith)
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n=0 := by omega
    have hh := hfirst.1
    rw [hn0,hy0] at hh
    simp only [signedHeight,Pi.zero_apply,ite_self,neg_zero] at hh
    omega
  have hrec := firstLayerHit_record ℓ (signedHeight e) (signedHeight_projection e) H n Y hfirst
  have hsteps (j : ℕ) : signedHeight e (Y (j+1)) ≤ signedHeight e (Y j)+1 := by
    obtain ⟨g,hg⟩ := hnn j
    have he : Y (j+1)=Y j+step g := by dsimp [Y]; rw [hg]; abel
    rw [he]
    exact signedHeight_step_le e _ g
  have hcount := recordCount_eq_height_at_record ℓ (signedHeight e) (signedHeight_projection e) Y hsteps hrec
  rw [hfirst.1,hy0,show signedHeight e (0:Lattice d)=0 by simp [signedHeight],zero_add] at hcount
  have hr : Y ∈ RecordIndexPrefix ℓ H n := by
    refine ⟨hn,hrec,by exact_mod_cast hcount.symm,?_⟩
    intro j hj
    have hh : dot (realPosition x) ℓ ≤ dot (realPosition (X j)) ℓ := by
      rcases lt_or_eq_of_le hj with hj | rfl
      · exact (hX.2 j hj).1
      · have hh := hX.1
        change dot (realPosition x) ℓ+(H:ℝ) ≤ dot (realPosition (X j)) ℓ at hh
        linarith [show (0:ℝ) ≤ H by positivity]
    change dot (realPosition (0:Lattice d)) ℓ ≤ dot (realPosition (X j-x)) ℓ
    rw [dot_realPosition_sub]
    simpa only [dot,realPosition,Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero,sub_nonneg] using hh
  exact hr

lemma recordPrefix_lower {d : ℕ} (ℓ : Vector d) (X : Path d) {H n j : ℕ}
    (hX : X ∈ RecordIndexPrefix ℓ H n) (hj : j ≤ H) :
    ∃ a ≤ n, X ∈ RecordOrZeroPrefix ℓ j a := by
  classical
  by_cases hj0 : j = 0
  · exact ⟨0,Nat.zero_le _,by simp [RecordOrZeroPrefix,hj0]⟩
  have hex : ∃ a, j ≤ recordCount ℓ X a := ⟨n,by rw [hX.2.2.1]; exact hj⟩
  let a := Nat.find hex
  have ha : j ≤ recordCount ℓ X a := Nat.find_spec hex
  have han : a ≤ n := Nat.find_min' hex (by rw [hX.2.2.1]; exact hj)
  have ha0 : 0 < a := by
    by_contra! hn
    have he : a = 0 := Nat.eq_zero_of_le_zero hn
    simp only [he,recordCount_zero] at ha
    omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha0)
  have hklt : recordCount ℓ X k < j := Nat.lt_of_not_ge
    (Nat.find_min hex (by omega))
  have hrec : StrictRecord ℓ X a := by
    by_contra hn
    rw [hk,recordCount_succ,ite_eq_right (by simpa only [hk,Nat.succ_eq_add_one] using hn),Nat.add_zero] at ha
    omega
  have hc : recordCount ℓ X a = j := by
    rw [hk,recordCount_succ,ite_eq_left (by simpa only [hk,Nat.succ_eq_add_one] using hrec)]
    rw [hk,recordCount_succ,ite_eq_left (by simpa only [hk,Nat.succ_eq_add_one] using hrec)] at ha
    omega
  refine ⟨a,han,?_⟩
  rw [RecordOrZeroPrefix,ite_eq_right hj0]
  exact ⟨ha0,hrec,hc,fun k hk => hX.2.2.2 k (hk.trans han)⟩

lemma curvePrefix_iff {d : ℕ} (e f : Direction d) (x : Lattice d) (b : ℕ → ℝ)
    (z : ℝ) {H : ℕ} (hH : 0 < H) (X : Path d)
    (h0 : X 0 = x) (hnn : ∀ n, ∃ g, X (n+1)=X n+step g) :
    X ∈ CurvePrefix (realPosition (step e)) f x b z H ↔
      X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∧
      ∀ j ≤ H, |signedCoordinate f (recordIndexPosition (realPosition (step e)) j
        (fun k => X k-x))-b j| ≤ z := by
  constructor
  · intro hX
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    refine ⟨Set.mem_iUnion.mpr ⟨n,hn.1⟩,?_⟩
    intro j hj
    obtain ⟨a,ha,hr,hb⟩ := hn.2 j hj
    have ht := recordOrZeroPrefix_time _ hr
    simpa only [recordIndexPosition,ht] using hb
  · rintro ⟨hX,hbound⟩
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    refine Set.mem_iUnion.mpr ⟨n,hn,?_⟩
    intro j hj
    obtain ⟨a,ha,hr⟩ := recordPrefix_lower _ (fun k => X k-x)
      (coordinate_hitAt_recordPrefix e x X h0 hnn hH hn) hj
    refine ⟨a,ha,hr,?_⟩
    have ht := recordOrZeroPrefix_time _ hr
    simpa only [recordIndexPosition,ht] using hbound j hj

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_TubeHeightMono
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma tubePrefix_eq_curvePrefix {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (θ z : ℝ) (H : ℕ) :
    TubePrefix ℓ f x θ z H = CurvePrefix ℓ f x (fun j => (j:ℝ)*θ) z H := rfl

lemma tubePrefix_mono_height_ae {d : ℕ} (e f : Direction d) (x : Lattice d)
    (θ z : ℝ) {H K : ℕ} (hH : 0 < H) (hHK : H ≤ K) (ω : Environment d) :
    TubePrefix (realPosition (step e)) f x θ z K ≤ᵐ[quenchedKernel (ω,x)]
      TubePrefix (realPosition (step e)) f x θ z H := by
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  intro hX
  rw [tubePrefix_eq_curvePrefix] at hX ⊢
  have hX := (curvePrefix_iff e f x _ z (hH.trans_le hHK) X h0 hnn).mp hX
  apply (curvePrefix_iff e f x _ z hH X h0 hnn).mpr
  refine ⟨?_,fun j hj => hX.2 j (hj.trans hHK)⟩
  have hh := hX.1
  rw [←cross_eq_hit] at hh ⊢
  exact cross_antitone _ x (by exact_mod_cast hHK) hh

lemma quenchedTube_mono_height {d : ℕ} (e f : Direction d) (x : Lattice d)
    (θ z : ℝ) {H K : ℕ} (hH : 0 < H) (hHK : H ≤ K) (ω : Environment d) :
    quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ z K) ≤
      quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ z H) :=
  measure_mono_ae (tubePrefix_mono_height_ae e f x θ z hH hHK ω)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPairEndpoint
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma measurable_prefixEndpoint {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℕ) :
    Measurable (prefixEndpoint ℓ x H) := by
  exact measurable_const.add ((measurable_recordIndexPosition ℓ H).comp
    (Measurable.of_eval fun j => (measurable_of_countable (fun u : Lattice d => u-x)).comp (measurable_pi_apply j)))

lemma signedCoordinate_sub_add {d : ℕ} (f : Direction d) (x y u v : Lattice d) :
    signedCoordinate f ((y+v)-(x+u)) =
      signedCoordinate f (y-x)+signedCoordinate f v-signedCoordinate f u := by
  simp only [signedCoordinate,Pi.sub_apply,Pi.add_apply,Int.cast_sub,Int.cast_add]
  split_ifs <;> ring

lemma tubePrefix_endpoint_bound {d : ℕ} (e f : Direction d) (x : Lattice d)
    (θ z : ℝ) {H : ℕ} (hH : 0 < H) (X : Path d)
    (h0 : X 0=x) (hnn : ∀ n, ∃ g, X (n+1)=X n+step g)
    (hX : X ∈ TubePrefix (realPosition (step e)) f x θ z H) :
    X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∧
    |signedCoordinate f (recordIndexPosition (realPosition (step e)) H (fun j => X j-x))-(H:ℝ)*θ| ≤ z := by
  rw [tubePrefix_eq_curvePrefix] at hX
  have hh := (curvePrefix_iff e f x _ z hH X h0 hnn).mp hX
  exact ⟨hh.1,hh.2 H le_rfl⟩

lemma endpointPrefix_endpoint_ae {d : ℕ} (e : Direction d) (x : Lattice d)
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (A : Set (Lattice d)) :
    ∀ᵐ X ∂quenchedKernel (ω,x), X ∈ EndpointPrefix (realPosition (step e)) x H A →
      X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∧
      prefixEndpoint (realPosition (step e)) x H X ∈ A := by
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn hX
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
  have hh : X ∈ HitAt (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) n :=
    ⟨hn.1.1,hn.2⟩
  refine ⟨Set.mem_iUnion.mpr ⟨n,hh⟩,?_⟩
  dsimp [prefixEndpoint]
  rw [coordinate_hitAt_record e x X h0 hnn hH hh]
  simpa only [add_sub_cancel] using hn.1.2

lemma quenched_pair_regular {d : ℕ} (ω : Environment d) (x y : Lattice d) :
    ∀ᵐ p ∂(quenchedKernel (ω,x)).prod (quenchedKernel (ω,y)),
      (p.1 0=x ∧ ∀ n, ∃ g, p.1 (n+1)=p.1 n+step g) ∧
      (p.2 0=y ∧ ∀ n, ∃ g, p.2 (n+1)=p.2 n+step g) := by
  exact (Measure.quasiMeasurePreserving_fst.ae (quenched_initial_ae (ω,x) |>.and (quenched_nearest_neighbor (ω,x)))).and
    (Measure.quasiMeasurePreserving_snd.ae (quenched_initial_ae (ω,y) |>.and (quenched_nearest_neighbor (ω,y))))

lemma central_pair_mass_le {d : ℕ} (e f : Direction d) (x y : Lattice d)
    (θ z b : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d)
    (hgap : b+2*z ≤ signedCoordinate f (y-x)) :
    centralPrefixMass (realPosition (step e)) f θ z H ω x*
      centralPrefixMass (realPosition (step e)) f θ z H ω y ≤
    ((quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))).real
      (PairEndpointEvent (realPosition (step e)) f x y H b) := by
  have hs : (TubePrefix (realPosition (step e)) f x θ z H ×ˢ
      TubePrefix (realPosition (step e)) f y θ z H) ≤ᵐ[
      (quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))]
      PairEndpointEvent (realPosition (step e)) f x y H b := by
    filter_upwards [quenched_pair_regular ω x y] with p hp hmem
    have hx := tubePrefix_endpoint_bound e f x θ z hH p.1 hp.1.1 hp.1.2 hmem.1
    have hy := tubePrefix_endpoint_bound e f y θ z hH p.2 hp.2.1 hp.2.2 hmem.2
    refine ⟨hx.1,hy.1,?_⟩
    rw [prefixEndpoint,prefixEndpoint,signedCoordinate_sub_add]
    have hx' := (abs_le.mp hx.2).2
    have hy' := (abs_le.mp hy.2).1
    linarith
  have hh := measure_mono_ae hs
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) hh
  simpa only [Measure.prod_prod,ENNReal.toReal_mul,centralPrefixMass,Measure.real] using hr
lemma jump_central_pair_mass_le {d : ℕ} (e f : Direction d) (x y : Lattice d)
    (θ z a s b : ℝ) (hs : s=1 ∨ s= -1) {H : ℕ} (hH : 0 < H) (ω : Environment d)
    (hgap : b+z-a ≤ signedCoordinate f (y-x)) :
    jumpPrefixMass (realPosition (step e)) f ((H:ℝ)*θ) a s H ω (if s=1 then y else x)*
      centralPrefixMass (realPosition (step e)) f θ z H ω (if s=1 then x else y) ≤
    ((quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))).real
      (PairEndpointEvent (realPosition (step e)) f x y H b) := by
  let ℓ := realPosition (step e)
  let A := fun w => EndpointPrefix ℓ w H {v | a < s*(signedCoordinate f (v-w)-(H:ℝ)*θ)}
  have hx := endpointPrefix_endpoint_ae e x hH ω {v | a < s*(signedCoordinate f (v-x)-(H:ℝ)*θ)}
  have hy := endpointPrefix_endpoint_ae e y hH ω {v | a < s*(signedCoordinate f (v-y)-(H:ℝ)*θ)}
  have hAE := (Measure.quasiMeasurePreserving_fst.ae hx).and (Measure.quasiMeasurePreserving_snd.ae hy)
  rcases hs with rfl | rfl
  · have hs : (TubePrefix ℓ f x θ z H ×ˢ A y) ≤ᵐ[
        (quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))]
        PairEndpointEvent ℓ f x y H b := by
      filter_upwards [quenched_pair_regular ω x y,hAE] with p hp he hmem
      have hc := tubePrefix_endpoint_bound e f x θ z hH p.1 hp.1.1 hp.1.2 hmem.1
      have hj := he.2 hmem.2
      refine ⟨hc.1,hj.1,?_⟩
      have hb := (abs_le.mp hc.2).2
      have hj' := hj.2
      simp only [prefixEndpoint,add_sub_cancel_left,one_mul] at hj'
      rw [prefixEndpoint,prefixEndpoint,signedCoordinate_sub_add]
      linarith
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs)
    simpa only [Measure.prod_prod,ENNReal.toReal_mul,centralPrefixMass,jumpPrefixMass,A,
      Measure.real,ite_true, if_true,mul_comm] using hh
  · have hs : (A x ×ˢ TubePrefix ℓ f y θ z H) ≤ᵐ[
        (quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))]
        PairEndpointEvent ℓ f x y H b := by
      filter_upwards [quenched_pair_regular ω x y,hAE] with p hp he hmem
      have hj := he.1 hmem.1
      have hc := tubePrefix_endpoint_bound e f y θ z hH p.2 hp.2.1 hp.2.2 hmem.2
      refine ⟨hj.1,hc.1,?_⟩
      have hb := (abs_le.mp hc.2).1
      have hj' := hj.2
      simp only [prefixEndpoint,add_sub_cancel_left,neg_one_mul] at hj'
      rw [prefixEndpoint,prefixEndpoint,signedCoordinate_sub_add]
      linarith
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs)
    simpa only [Measure.prod_prod,ENNReal.toReal_mul,centralPrefixMass,jumpPrefixMass,A,
      Measure.real,show (-1:ℝ) ≠ 1 by norm_num,ite_false, if_false] using hh
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma integral_lower_from_fraction {I : Type*} [MeasurableSpace I]
    (π : Measure I) [IsProbabilityMeasure π] (A : I → Prop)
    (hA : MeasurableSet {x | A x}) (G : I → ℝ) (hG : Measurable G)
    (hG0 : ∀ x, 0 ≤ G x) (hG1 : ∀ x, G x ≤ 1)
    {c g : ℝ} (hg : 0 ≤ g) (hgood : ∀ x, A x → g ≤ G x)
    (hfrac : c ≤ ∫ x, if A x then (1:ℝ) else 0 ∂π) :
    c*g ≤ ∫ x, G x ∂π := by
  have hI : Integrable G π := (integrable_const (1:ℝ)).mono' hG.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hG0 x)]; exact hG1 x)
  have hII : Integrable (fun x => if A x then (1:ℝ) else 0) π := by
    have he : (fun x => if A x then (1:ℝ) else 0) = ({x | A x}).indicator (fun _ => (1:ℝ)) := by
      funext x; simp [Set.indicator]
    rw [he]
    exact (integrable_const _).indicator hA
  have hh := integral_mono (hII.mul_const g) hI (fun x => ?_)
  · rw [integral_mul_const] at hh
    exact (mul_le_mul_of_nonneg_right hfrac hg).trans hh
  · split_ifs with hx
    · simpa using hgood x hx
    · simpa using hG0 x

lemma centralPrefixMass_bounds {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z : ℝ) (H : ℕ) (ω : Environment d) (x : Lattice d) :
    0 ≤ centralPrefixMass ℓ f θ z H ω x ∧ centralPrefixMass ℓ f θ z H ω x ≤ 1 :=
  ⟨measureReal_nonneg,measureReal_le_one⟩
lemma jumpPrefixMass_bounds {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b a s : ℝ) (H : ℕ) (ω : Environment d) (x : Lattice d) :
    0 ≤ jumpPrefixMass ℓ f b a s H ω x ∧ jumpPrefixMass ℓ f b a s H ω x ≤ 1 :=
  ⟨measureReal_nonneg,measureReal_le_one⟩
lemma pair_retained_mass_of_favorable_fraction {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z a s : ℝ) (H : ℕ) (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (ω : Environment d) {c j d₀ : ℝ} (hj : 0 ≤ j) (hd : 0 ≤ d₀)
    (hfrac : c ≤ ∫ x,
      if j ≤ jumpPrefixMass ℓ f ((H:ℝ)*θ) a s H ω (if s=1 then x.2 else x.1) ∧
        d₀ ≤ centralPrefixMass ℓ f θ z H ω x.1 ∧
        d₀ ≤ centralPrefixMass ℓ f θ z H ω x.2
      then (1:ℝ) else 0 ∂π) :
    c*d₀^2 ≤ pairCentralRetainedMass ℓ f θ z H π ω ∧
    c*(j*d₀) ≤ pairJumpRetainedMass ℓ f θ z a s H π ω := by
  let J := jumpPrefixMass ℓ f ((H:ℝ)*θ) a s H ω
  let C := centralPrefixMass ℓ f θ z H ω
  let A := fun x : Lattice d × Lattice d => j ≤ J (if s=1 then x.2 else x.1) ∧ d₀ ≤ C x.1 ∧ d₀ ≤ C x.2
  have hf : c ≤ ∫ x, @ite ℝ (A x) (Classical.propDecidable _) 1 0 ∂π := by
    convert hfrac using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [A,J,C]
    split_ifs <;> rfl
  have hJ (x) := jumpPrefixMass_bounds ℓ f ((H:ℝ)*θ) a s H ω x
  have hC (x) := centralPrefixMass_bounds ℓ f θ z H ω x
  constructor
  · apply integral_lower_from_fraction π A (Set.to_countable _ |>.measurableSet)
      (fun x => C x.1*C x.2) (measurable_of_countable _)
      (fun x => mul_nonneg (hC x.1).1 (hC x.2).1)
      (fun x => (mul_le_of_le_one_left (hC x.2).1 (hC x.1).2).trans (hC x.2).2)
      (sq_nonneg d₀) (fun x hx => ?_) hf
    simpa only [pow_two] using mul_le_mul hx.2.1 hx.2.2 hd (hd.trans hx.2.1)
  · apply integral_lower_from_fraction π A (Set.to_countable _ |>.measurableSet)
      (fun x => J (if s=1 then x.2 else x.1)*C (if s=1 then x.1 else x.2)) (measurable_of_countable _)
      (fun x => mul_nonneg (hJ _).1 (hC _).1)
      (fun x => (mul_le_of_le_one_left (hC (if s=1 then x.1 else x.2)).1
        (hJ (if s=1 then x.2 else x.1)).2).trans (hC (if s=1 then x.1 else x.2)).2)
      (mul_nonneg hj hd) (fun x hx => ?_) hf
    apply mul_le_mul hx.1 _ hd (hj.trans hx.1)
    split_ifs
    · exact hx.2.1
    · exact hx.2.2
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferStageSuccess
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma central_retained_le_rawPair {d : ℕ} (e f : Direction d) (θ z b : ℝ)
    {h H : ℕ} (hh : 0 < h) (hhH : h ≤ H) (ω : Environment d)
    (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (hgap : ∀ᵐ x ∂π, b+2*z ≤ signedCoordinate f (x.2-x.1)) :
    pairCentralRetainedMass (realPosition (step e)) f θ z H π ω ≤
      rawPairEndpointMass (realPosition (step e)) f h b π ω := by
  have hC (x) := centralPrefixMass_bounds (realPosition (step e)) f θ z H ω x
  have hI : Integrable (fun x : Lattice d × Lattice d =>
      centralPrefixMass (realPosition (step e)) f θ z H ω x.1*
      centralPrefixMass (realPosition (step e)) f θ z H ω x.2) π :=
    (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hC _).1 (hC _).1)]
        exact (mul_le_of_le_one_left (hC _).1 (hC _).2).trans (hC _).2)
  have hJ : Integrable (fun x : Lattice d × Lattice d =>
      ((quenchedKernel (ω,x.1)).prod (quenchedKernel (ω,x.2))).real
        (PairEndpointEvent (realPosition (step e)) f x.1 x.2 h b)) π :=
    (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  apply integral_mono_ae hI hJ
  filter_upwards [hgap] with x hx
  have hm (w : Lattice d) : centralPrefixMass (realPosition (step e)) f θ z H ω w ≤
      centralPrefixMass (realPosition (step e)) f θ z h ω w :=
    ENNReal.toReal_mono (measure_ne_top _ _) (quenchedTube_mono_height e f w θ z hh hhH ω)
  exact (mul_le_mul (hm x.1) (hm x.2) (hC x.2).1
    (centralPrefixMass_bounds _ _ _ _ _ _ _).1).trans
      (central_pair_mass_le e f x.1 x.2 θ z b hh ω hx)

lemma jump_retained_le_rawPair {d : ℕ} (e f : Direction d) (θ z a s b : ℝ)
    (hs : s=1 ∨ s= -1) {H : ℕ} (hH : 0 < H) (ω : Environment d)
    (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (hgap : ∀ᵐ x ∂π, b+z-a ≤ signedCoordinate f (x.2-x.1)) :
    pairJumpRetainedMass (realPosition (step e)) f θ z a s H π ω ≤
      rawPairEndpointMass (realPosition (step e)) f H b π ω := by
  have hC (x) := centralPrefixMass_bounds (realPosition (step e)) f θ z H ω x
  have hJ (x) := jumpPrefixMass_bounds (realPosition (step e)) f ((H:ℝ)*θ) a s H ω x
  have hI : Integrable (fun x : Lattice d × Lattice d =>
      jumpPrefixMass (realPosition (step e)) f ((H:ℝ)*θ) a s H ω (if s=1 then x.2 else x.1)*
      centralPrefixMass (realPosition (step e)) f θ z H ω (if s=1 then x.1 else x.2)) π :=
    (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hJ _).1 (hC _).1)]
        exact (mul_le_of_le_one_left (hC _).1 (hJ _).2).trans (hC _).2)
  have hK : Integrable (fun x : Lattice d × Lattice d =>
      ((quenchedKernel (ω,x.1)).prod (quenchedKernel (ω,x.2))).real
        (PairEndpointEvent (realPosition (step e)) f x.1 x.2 H b)) π :=
    (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  apply integral_mono_ae hI hK
  filter_upwards [hgap] with x hx
  exact jump_central_pair_mass_le e f x.1 x.2 θ z a s b hs hH ω hx

theorem buffer_stage_success_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε →
      ∃ g R : ℝ, 0 < g ∧ 0 < R ∧ ∀ r : ℝ, R ≤ r →
        let H := ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊
        0 < H ∧ ∀ z₀ : ℝ, ∀ π : Measure (Lattice d × Lattice d), IsProbabilityMeasure π →
          (∀ᵐ x ∂π, z₀+r ≤ signedCoordinate f (x.2-x.1)) →
          c ≤ (environmentLaw ν).real {ω | BufferStageSuccess (realPosition (step e)) f H z₀ r ε a g π ω} := by
  obtain ⟨a,j,c,ha,hj,hc,hfair⟩ := clipped_pair_favorable_fraction ν hue e f hef htrans
  refine ⟨a/4,c,by positivity,hc,fun ε hε => ?_⟩
  let δ := min (ε/4) (a/4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨d₀,R,hd,hR,hr⟩ := hfair δ hδ
  refine ⟨min (c*d₀^2) (c*(j*d₀)),R,lt_min (by positivity) (by positivity),hR,fun r hrr => ?_⟩
  obtain ⟨hH,θ,s,hs,hfrac⟩ := hr r hrr
  refine ⟨hH,fun z₀ π hπ hgap => ?_⟩
  have := hπ
  have hr0 : 0 ≤ r := (hR.trans_le hrr).le
  have heps : 2*δ ≤ ε := by have := min_le_left (ε/4) (a/4); dsimp [δ] <;> linarith
  have haδ : a/4+δ ≤ a := by have := min_le_right (ε/4) (a/4); dsimp [δ] <;> linarith
  refine (hfrac π hπ).trans (measureReal_mono ?_)
  intro ω hω
  obtain ⟨hcentral,hjump⟩ := pair_retained_mass_of_favorable_fraction (realPosition (step e)) f
    θ (δ*r) (a*r) s _ π ω hj.le hd.le hω
  constructor
  · intro h hh hhH
    refine (min_le_left _ _).trans (hcentral.trans
      (central_retained_le_rawPair e f θ (δ*r) (z₀+(1-ε)*r) hh hhH ω π ?_))
    filter_upwards [hgap] with x hx
    have := mul_le_mul_of_nonneg_right heps hr0
    linarith
  · refine (min_le_right _ _).trans (hjump.trans
      (jump_retained_le_rawPair e f θ (δ*r) (a*r) s (z₀+(1+a/4)*r) hs hH ω π ?_))
    filter_upwards [hgap] with x hx
    have := mul_le_mul_of_nonneg_right haδ hr0
    linarith
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_RawPairKernel
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma hit_prefixEndpoint_iff {d : ℕ} (e : Direction d) (x : Lattice d)
    {H : ℕ} (hH : 0 < H) (A : Set (Lattice d)) (X : Path d)
    (h0 : X 0=x) (hnn : ∀ n, ∃ g, X (n+1)=X n+step g) :
    X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H ∩ A) ↔
      X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∧
      prefixEndpoint (realPosition (step e)) x H X ∈ A := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp h
    have hh : X ∈ HitAt (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) n := ⟨hn.1.1,hn.2⟩
    refine ⟨Set.mem_iUnion.mpr ⟨n,hh⟩,?_⟩
    dsimp [prefixEndpoint]
    rw [coordinate_hitAt_record e x X h0 hnn hH hh]
    simpa only [add_sub_cancel] using hn.1.2
  · rintro ⟨h,hA⟩
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp h
    dsimp [prefixEndpoint] at hA
    rw [coordinate_hitAt_record e x X h0 hnn hH hn] at hA
    exact Set.mem_iUnion.mpr ⟨n,⟨hn.1,by simpa only [add_sub_cancel] using hA⟩,hn.2⟩

lemma hitKernel_eq_map_prefixEndpoint {d : ℕ} (e : Direction d) (x : Lattice d)
    {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    hitKernel (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) (ω,x) =
      ((quenchedKernel (ω,x)).restrict (Hit (Strip (realPosition (step e)) x H)
        (Upper (realPosition (step e)) x H))).map (prefixEndpoint (realPosition (step e)) x H) := by
  apply Measure.ext
  intro A hA
  rw [hitKernel_apply_eq_hit (disjoint_strip_upper _ _ _),Measure.map_apply
    (measurable_prefixEndpoint _ _ _) hA,Measure.restrict_apply ((measurable_prefixEndpoint _ _ _) hA)]
  apply measure_congr
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  have := hit_prefixEndpoint_iff e x hH A X h0 hnn
  apply propext
  exact this.trans and_comm

lemma rawPairEndpointLaw_eq {d : ℕ} (e f : Direction d) (x : Lattice d × Lattice d)
    {H : ℕ} (hH : 0 < H) (z : ℝ) (ω : Environment d) :
    rawPairEndpointLaw (realPosition (step e)) H ω x {y | z ≤ signedCoordinate f (y.2-y.1)} =
      ((quenchedKernel (ω,x.1)).prod (quenchedKernel (ω,x.2)))
        (PairEndpointEvent (realPosition (step e)) f x.1 x.2 H z) := by
  have hgap : MeasurableSet {y : Lattice d × Lattice d | z ≤ signedCoordinate f (y.2-y.1)} := Set.to_countable _ |>.measurableSet
  have hm := (measurable_prefixEndpoint (realPosition (step e)) x.1 H).prodMap
    (measurable_prefixEndpoint (realPosition (step e)) x.2 H)
  unfold rawPairEndpointLaw
  rw [hitKernel_eq_map_prefixEndpoint e x.1 hH,hitKernel_eq_map_prefixEndpoint e x.2 hH,
    Measure.map_prod_map _ _ (measurable_prefixEndpoint _ _ _) (measurable_prefixEndpoint _ _ _),
    Measure.prod_restrict,Measure.map_apply hm hgap,
    Measure.restrict_apply (hm hgap)]
  congr 1
  ext p
  simp only [PairEndpointEvent,Set.mem_inter_iff,Set.mem_preimage,
    Set.mem_ofPred_eq,Set.mem_prod]
  tauto
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPairLocality
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma rawPairEndpointLaw_total_le_one {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) :
    rawPairEndpointLaw ℓ H ω x Set.univ ≤ 1 := by
  rw [rawPairEndpointLaw,←Set.univ_prod_univ,Measure.prod_prod]
  exact (mul_le_of_le_one_left (by positivity)
    (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _)).trans
      (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma pairKernelMass_le_one {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (ω : Environment d) : pairKernelMass ℓ f H z π ω ≤ 1 := by
  calc
    pairKernelMass ℓ f H z π ω ≤ ∫⁻ _ : Lattice d × Lattice d, (1:ℝ≥0∞) ∂π := by
      apply lintegral_mono
      intro x
      exact (measure_mono (Set.subset_univ _)).trans (rawPairEndpointLaw_total_le_one ℓ H ω x)
    _ = 1 := by simp

lemma pairKernelMass_toReal {d : ℕ} (e f : Direction d) {H : ℕ} (hH : 0 < H)
    (z : ℝ) (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    (pairKernelMass (realPosition (step e)) f H z π ω).toReal =
      rawPairEndpointMass (realPosition (step e)) f H z π ω := by
  unfold pairKernelMass
  rw [←integral_toReal (measurable_of_countable _).aemeasurable
    (ae_of_all _ fun x => lt_of_le_of_lt
      ((measure_mono (Set.subset_univ _)).trans (rawPairEndpointLaw_total_le_one _ _ _ x)) ENNReal.one_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [rawPairEndpointLaw_eq e f x hH]
  rfl

lemma pairKernelMass_lower_iff {d : ℕ} (e f : Direction d) {H : ℕ} (hH : 0 < H)
    (z : ℝ) (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (ω : Environment d) {g : ℝ} (_ : 0 ≤ g) :
    ENNReal.ofReal g ≤ pairKernelMass (realPosition (step e)) f H z π ω ↔
      g ≤ rawPairEndpointMass (realPosition (step e)) f H z π ω := by
  have hn := ne_top_of_le_ne_top ENNReal.one_ne_top (pairKernelMass_le_one (realPosition (step e)) f H z π ω)
  rw [←pairKernelMass_toReal e f hH z π ω]
  exact ENNReal.ofReal_le_iff_le_toReal hn

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPairRetention
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma rawPairMixture_le_one {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    rawPairMixture ℓ H π ω Set.univ ≤ 1 := by
  rw [rawPairMixture_apply]
  calc
    _ ≤ ∫⁻ _ : Lattice d × Lattice d, (1:ℝ≥0∞) ∂π :=
      lintegral_mono fun x => rawPairEndpointLaw_total_le_one ℓ H ω x
    _ = 1 := by simp

lemma retainedPairLaw_mass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    retainedPairLaw ℓ f H z π ω Set.univ = pairKernelMass ℓ f H z π ω := by
  rw [retainedPairLaw,Measure.restrict_apply_univ,rawPairMixture_apply]
  rfl

lemma retainedPairLaw_support {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    ∀ᵐ y ∂retainedPairLaw ℓ f H z π ω, z ≤ signedCoordinate f (y.2-y.1) :=
  ae_restrict_mem (Set.to_countable _).measurableSet

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferStageEvent_iff {d : ℕ} (e f : Direction d) {H : ℕ} (hH : 0 < H)
    (z₀ r ε a : ℝ) {g : ℝ} (hg : 0 ≤ g) (π : Measure (Lattice d × Lattice d))
    [IsProbabilityMeasure π] (ω : Environment d) :
    BufferStageEvent (realPosition (step e)) f H z₀ r ε a g π ω ↔
      BufferStageSuccess (realPosition (step e)) f H z₀ r ε a g π ω := by
  unfold BufferStageEvent BufferStageSuccess
  apply and_congr
  · apply forall_congr'
    intro h
    apply forall_congr'
    intro hh
    apply forall_congr'
    intro _
    exact pairKernelMass_lower_iff e f hh _ π ω hg
  · exact pairKernelMass_lower_iff e f hH _ π ω hg

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_FreshRowWeights
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma fresh_rows_weighted_test_lower {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (G : Set (Environment d × Environment d))
    (hG : @MeasurableSet (Environment d × Environment d)
      (MeasurableSpace.prod (rowSigma S) (rowSigma T)) G)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma S] A)
    (w : Environment d → ℝ≥0∞) (hw : @Measurable _ _ (rowSigma S) _ w)
    (c : ℝ≥0∞) (hbound : ∀ η ∈ A, c ≤ environmentLaw ν {ω | (η,ω) ∈ G}) :
    c*(∫⁻ ω in A, w ω ∂environmentLaw ν) ≤
      ∫⁻ ω in {ω | ω ∈ A ∧ (ω,ω) ∈ G}, w ω ∂environmentLaw ν := by
  have hU : @Measurable (Environment d) (Environment d) inferInstance (rowSigma S) id :=
    measurable_id.mono le_rfl (rowSigma_le S)
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  have hb (η : Environment d) (hη : η ∈ A) :
      c ≤ (@Measure.map (Environment d) (Environment d) inferInstance (rowSigma T) id (environmentLaw ν))
        {ω | (η,ω) ∈ G} := by
    have he : {ω | (η,ω) ∈ G} = Prod.mk η ⁻¹' G := rfl
    rw [he,Measure.map_apply hV (hG.preimage measurable_prodMk_left)]
    exact hbound η hη
  exact @independent_random_test_weighted_lower (Environment d) (Environment d) (Environment d)
    inferInstance (rowSigma S) (rowSigma T) (environmentLaw ν) inferInstance
    id id hU hV
    (@indepFun_of_disjoint_rows d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
      ν _ S T hST id id measurable_id measurable_id) A hA G hG w hw c hb

lemma fresh_buffer_weighted_test {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) {H : ℕ} (hH : 0 < H) (z₀ r ε a g : ℝ)
    (C : Set (Lattice d × Lattice d)) {S T : Set (Lattice d)} (hST : Disjoint S T)
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ T ∧ Strip ℓ x.2 H ⊆ T)
    (π : Environment d → SupportedPairMeasures C)
    (hπ : @Measurable _ _ (rowSigma S) _ π)
    (A : Set (Environment d)) (hA : MeasurableSet[rowSigma S] A)
    (w : Environment d → ℝ≥0∞) (hw : @Measurable _ _ (rowSigma S) _ w)
    (c : ℝ≥0∞)
    (hbound : ∀ η ∈ A, c ≤ environmentLaw ν
      {ω | BufferStageEvent ℓ f H z₀ r ε a g (π η).val ω}) :
    c*(∫⁻ ω in A, w ω ∂environmentLaw ν) ≤
      ∫⁻ ω in {ω | ω ∈ A ∧ BufferStageEvent ℓ f H z₀ r ε a g (π ω).val ω},
        w ω ∂environmentLaw ν := by
  let G : Set (Environment d × Environment d) :=
    {p | BufferStageEvent ℓ f H z₀ r ε a g (π p.1).val p.2}
  have hG : @MeasurableSet (Environment d × Environment d)
      (MeasurableSpace.prod (rowSigma S) (rowSigma T)) G :=
    (measurableSet_bufferStageEvent_rows ℓ f hH z₀ r ε a g C T hC).preimage
      ((hπ.comp measurable_fst).prodMk measurable_snd)
  exact fresh_rows_weighted_test_lower ν hST G hG A hA w hw c hbound
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_CountableFreshBuffer
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical Function
namespace DirectionalTransience

lemma weighted_countable_partition_lower {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (A B : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hB : ∀ i, MeasurableSet (B i)) (hdis : Pairwise (Disjoint on A))
    (hsub : ∀ i, B i ⊆ A i) (w : Ω → ℝ≥0∞) (c : ℝ≥0∞)
    (hbound : ∀ i, c*(∫⁻ ω in A i, w ω ∂μ) ≤ ∫⁻ ω in B i, w ω ∂μ) :
    c*(∫⁻ ω in ⋃ i, A i, w ω ∂μ) ≤ ∫⁻ ω in ⋃ i, B i, w ω ∂μ := by
  rw [lintegral_iUnion hA hdis,lintegral_iUnion hB
    (fun i j hij => (hdis hij).mono (hsub i) (hsub j)),←ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum hbound

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_FreshBufferAE
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma pairLawValidSet_iff {d : ℕ} (f : Direction d) (z : ℝ) {C : Set (Lattice d × Lattice d)}
    (π : Environment d → SupportedPairMeasures C) (ω : Environment d) :
    ω ∈ pairLawValidSet f z π ↔ IsProbabilityMeasure (π ω).val ∧
      ∀ᵐ x ∂(π ω).val, z ≤ signedCoordinate f (x.2-x.1) := by
  constructor
  · rintro ⟨hp,hg⟩
    exact ⟨⟨hp⟩,ae_iff.mpr hg⟩
  · rintro ⟨hp,hg⟩
    let := hp
    exact ⟨measure_univ,ae_iff.mp hg⟩

lemma pairLawValidSet_measurable {d : ℕ} (f : Direction d) (z : ℝ) {C : Set (Lattice d × Lattice d)}
    (π : Environment d → SupportedPairMeasures C) {m : MeasurableSpace (Environment d)} (hπ : @Measurable _ _ m _ π) :
    MeasurableSet[m] (pairLawValidSet f z π) := by
  have hm := hπ.subtype_val
  exact (measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp hm) measurable_const).inter
    (measurableSet_eq_fun ((Measure.measurable_coe (Set.to_countable _).measurableSet).comp hm) measurable_const)

lemma weighted_test_ae_valid {Ω : Type*} [mΩ : MeasurableSpace Ω] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (μ : @Measure Ω mΩ) (A V E : Set Ω) (hA : MeasurableSet[m] A)
    (hV : MeasurableSet[m] V) (w : Ω → ℝ≥0∞) (c : ℝ≥0∞)
    (hvalid : ∀ᵐ ω ∂μ, ω ∈ A → ω ∈ V)
    (hbound : ∀ A', MeasurableSet[m] A' → A' ⊆ A → A' ⊆ V →
      c*(∫⁻ ω in A', w ω ∂μ) ≤ ∫⁻ ω in A' ∩ E, w ω ∂μ) :
    c*(∫⁻ ω in A, w ω ∂μ) ≤ ∫⁻ ω in A ∩ E, w ω ∂μ := by
  have hv : (fun ω => ω ∈ A ∩ V) =ᵐ[μ] (fun ω => ω ∈ A) := hvalid.mono fun ω h => by
    simp only [Set.mem_inter_iff]
    exact propext ⟨And.left,fun hA => ⟨hA,h hA⟩⟩
  have hvE : (fun ω => ω ∈ (A ∩ V) ∩ E) =ᵐ[μ] (fun ω => ω ∈ A ∩ E) := hv.mono fun ω h => by
    change (ω ∈ A ∩ V ∧ ω ∈ E) = (ω ∈ A ∧ ω ∈ E)
    change (ω ∈ A ∩ V) = (ω ∈ A) at h
    rw [h]
  have hh := hbound (A ∩ V) (hA.inter hV) Set.inter_subset_left Set.inter_subset_right
  have hr : μ.restrict (A ∩ V)=μ.restrict A := by
    rw [Set.inter_comm, ← Measure.restrict_restrict (hm V hV)]
    exact Measure.restrict_eq_self_of_ae_mem ((ae_restrict_iff' (hm A hA)).mpr hvalid)
  have hrE : μ.restrict ((A ∩ V) ∩ E)=μ.restrict (A ∩ E) := Measure.restrict_congr_set hvE
  rwa [hr,hrE] at hh

lemma fresh_buffer_weight_ae_valid {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) {H : ℕ} (hH : 0 < H) (z₀ r ε α g c : ℝ)
    (C : Set (Lattice d × Lattice d)) (D S : Set (Lattice d))
    (hdis : Disjoint D S) (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S)
    (hchance : ∀ π : SupportedPairMeasures C, IsProbabilityMeasure π.val →
      (∀ᵐ x ∂π.val, z₀+r ≤ signedCoordinate f (x.2-x.1)) →
      ENNReal.ofReal c ≤ environmentLaw ν {ω | BufferStageEvent ℓ f H z₀ r ε α g π.val ω})
    (π : Environment d → SupportedPairMeasures C)
    (hπ : @Measurable _ _ (rowSigma D) _ π) (A : Set (Environment d))
    (hA : MeasurableSet[rowSigma D] A)
    (hvalid : ∀ᵐ ω ∂environmentLaw ν, ω ∈ A → IsProbabilityMeasure (π ω).val ∧
      ∀ᵐ x ∂(π ω).val, z₀+r ≤ signedCoordinate f (x.2-x.1))
    (w : Environment d → ℝ≥0∞) (hw : @Measurable _ _ (rowSigma D) _ w) :
    ENNReal.ofReal c*(∫⁻ ω in A, w ω ∂environmentLaw ν) ≤
      ∫⁻ ω in {ω | ω ∈ A ∧ BufferStageEvent ℓ f H z₀ r ε α g (π ω).val ω}, w ω ∂environmentLaw ν := by
  apply weighted_test_ae_valid (mΩ := (inferInstance : MeasurableSpace (Environment d))) (m := rowSigma D) (rowSigma_le D) (environmentLaw ν) A (pairLawValidSet f (z₀+r) π)
    {ω | BufferStageEvent ℓ f H z₀ r ε α g (π ω).val ω} hA
    (pairLawValidSet_measurable f (z₀+r) π hπ) w (ENNReal.ofReal c)
      (hvalid.mono fun ω h hω => (pairLawValidSet_iff f (z₀+r) π ω).mpr (h hω))
  intro A' hA' hsub hV
  apply fresh_buffer_weighted_test ν ℓ f hH z₀ r ε α g C hdis hC π hπ A' hA' w hw
  intro ω hω
  obtain ⟨hp,hgap⟩ := (pairLawValidSet_iff f (z₀+r) π ω).mp (hV hω)
  exact hchance (π ω) hp hgap
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstHitUpward
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma single_step_dirac_le_hitKernel {d : ℕ} (ω : Environment d) (x : Lattice d)
    (e : Direction d) {S T : Set (Lattice d)} (hST : Disjoint S T)
    (hx : x ∈ S) (he : x+step e ∈ T) :
    ((ω x).1 e : ℝ≥0∞) • Measure.dirac (x+step e) ≤ hitKernel S T (ω,x) := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  rw [Measure.smul_apply, smul_eq_mul]
  by_cases hu : x+step e ∈ U
  · rw [Measure.dirac_apply_of_mem hu, mul_one,hitKernel_apply_eq_hit hST]
    have hsub : wordCylinder x [e] ⊆ Hit S (T ∩ U) := by
      intro X hX
      apply Set.mem_iUnion.mpr
      refine ⟨1,?_,?_⟩
      · have h1 := hX 1 (by simp)
        simp only [wordPath] at h1
        simpa only [h1] using (show x+step e ∈ T ∩ U from ⟨he,hu⟩)
      · intro j hj
        have hj0 : j=0 := by omega
        subst j
        have h0 := hX 0 (by simp)
        simpa only [wordPath_zero] using h0 ▸ hx
    have hm := measure_mono (μ := quenchedKernel (ω,x)) hsub
    simpa only [quenched_wordCylinder,wordWeight,mul_one,ENNReal.ofReal_coe_nnreal] using hm
  · rw [Measure.dirac_apply' _ hU,Set.indicator_of_notMem hu,mul_zero]
    exact bot_le

lemma elliptic_single_step_le_hitKernel {d : ℕ} (ω : Environment d) (x : Lattice d)
    (e : Direction d) {κ : ℝ≥0} (hκ : κ ≤ (ω x).1 e)
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (hx : x ∈ S) (he : x+step e ∈ T) :
    (κ : ℝ≥0∞) • Measure.dirac (x+step e) ≤ hitKernel S T (ω,x) := by
  intro U
  exact (mul_le_mul_left (ENNReal.coe_le_coe.mpr hκ) ((Measure.dirac (x+step e)) U)).trans
    ((single_step_dirac_le_hitKernel ω x e hST hx he) U)

lemma hitKernel_direct_step_retention {d : ℕ} (ω : Environment d) (x : Lattice d)
    (e : Direction d) {κ : ℝ≥0} (hκ : ∀ y, κ ≤ (ω y).1 e)
    {S₁ T₁ S₂ T₂ S : Set (Lattice d)}
    (hST₁ : Disjoint S₁ T₁) (hST₂ : Disjoint S₂ T₂) (hST : Disjoint S T₂)
    (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S)
    (hy : ∀ᵐ y ∂hitKernel S₁ T₁ (ω,x), y ∈ S₂ ∧ y+step e ∈ T₂) :
    (κ : ℝ≥0∞) • (hitKernel S₁ T₁ (ω,x)).map (fun y => y+step e) ≤
      hitKernel S T₂ (ω,x) := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  have hm : Measurable (fun y : Lattice d => y+step e) := measurable_of_countable _
  rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply hm hU]
  have heq : (κ : ℝ≥0∞)*hitKernel S₁ T₁ (ω,x) ((fun y => y+step e) ⁻¹' U) =
      ∫⁻ y, ((κ : ℝ≥0∞) • Measure.dirac (y+step e)) U ∂hitKernel S₁ T₁ (ω,x) := by
    simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ hU]
    rw [lintegral_const_mul _ (measurable_of_countable _)]
    congr 1
    rw [← lintegral_indicator_one (hm hU)]
    apply lintegral_congr
    intro y
    by_cases hy : y+step e ∈ U <;> simp [hy]
  rw [heq]
  apply le_trans _ (hitKernel_comp_le ω x hST₁ hST₂ hST h₁ h₂ U)
  apply lintegral_mono_ae
  filter_upwards [hy] with y hy
  exact (elliptic_single_step_le_hitKernel ω y e (hκ y) hST₂ hy.1 hy.2) U

lemma coordinate_hitKernel_upward_retention {d : ℕ} (e : Direction d) (x : Lattice d)
    (H : ℕ) (ω : Environment d) {κ : ℝ≥0} (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ : ℝ≥0∞) • (hitKernel (Strip (realPosition (step e)) x H)
        (Upper (realPosition (step e)) x H) (ω,x)).map (fun y => y+step e) ≤
      hitKernel (Strip (realPosition (step e)) x (H+1))
        (Upper (realPosition (step e)) x (H+1)) (ω,x) := by
  apply hitKernel_direct_step_retention ω x e hκ (disjoint_strip_upper _ _ _)
    (disjoint_strip_upper _ _ _) (disjoint_strip_upper _ _ _) ?_ (fun _ h => h) ?_
  · intro y hy
    exact ⟨hy.1,by have := hy.2; dsimp [Strip] at * <;> linarith⟩
  · filter_upwards [coordinate_hitKernel_supported e x H ω] with y hy
    have hh : dot (realPosition y) (realPosition (step e)) =
        dot (realPosition x) (realPosition (step e))+(H:ℝ) := by
      simp only [signedHeight_projection]
      exact_mod_cast hy
    constructor
    · constructor
      · rw [hh]
        exact le_add_of_nonneg_right (Nat.cast_nonneg H)
      · rw [hh]
        linarith
    · change _ ≤ dot (realPosition (y+step e)) (realPosition (step e))
      rw [dot_realPosition_add,signed_direction_unit,hh]
      linarith
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AdaptiveFailureWeights
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
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

lemma successes_nonneg {Ω : Type*} (B : ℕ → Set Ω) (n : ℕ) (ω : Ω) : 0 ≤ successes B n ω := by
  apply Finset.sum_nonneg
  intro k hk
  split_ifs <;> norm_num
lemma successes_succ {Ω : Type*} (B : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    successes B (n+1) ω = successes B n ω+(if ω ∈ B n then 1 else 0) := by
  simp only [successes,Finset.sum_range_succ]
lemma measurable_successes {Ω : Type*} [MeasurableSpace Ω] (B : ℕ → Set Ω)
    (hB : ∀ n, MeasurableSet (B n)) (n : ℕ) : Measurable (successes B n) := by
  apply Finset.measurable_fun_sum
  intro k hk
  exact Measurable.ite (hB k) measurable_const measurable_const
lemma measurable_failureWeight {Ω : Type*} [MeasurableSpace Ω] (B : ℕ → Set Ω)
    (hB : ∀ n, MeasurableSet (B n)) (s : ℝ) (n : ℕ) : Measurable (failureWeight B s n) :=
  (measurable_const.sub (measurable_successes B hB n)).exp
lemma failureWeight_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (B : ℕ → Set Ω) (hB : ∀ n, MeasurableSet (B n)) (s : ℝ) (n : ℕ) :
    Integrable (failureWeight B s n) μ := by
  refine (integrable_const (Real.exp (s/4*n))).mono' (measurable_failureWeight B hB s n).aestronglyMeasurable ?_
  filter_upwards [] with ω
  dsimp only [failureWeight]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (successes_nonneg B n ω)

lemma failureWeight_step {Ω : Type*} (B : ℕ → Set Ω) (s : ℝ) (n : ℕ) (ω : Ω) :
    failureWeight B s (n+1) ω = Real.exp (s/4)*
      (failureWeight B s n ω-(1-Real.exp (-1))*
        (if ω ∈ B n then failureWeight B s n ω else 0)) := by
  rw [failureWeight,successes_succ,Nat.cast_add,Nat.cast_one]
  split_ifs with h
  · have he : s/4*((n:ℝ)+1)-(successes B n ω+1) = s/4+(s/4*n-successes B n ω)+(-1) := by ring
    rw [he,Real.exp_add,Real.exp_add]
    dsimp [failureWeight]
    ring
  · have he : s/4*((n:ℝ)+1)-(successes B n ω+0) = s/4+(s/4*n-successes B n ω) := by ring
    rw [he,Real.exp_add]
    simp only [mul_zero,sub_zero,failureWeight]

lemma failureWeight_contraction {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (s/4)*(1-s*(1-Real.exp (-1))) ≤ Real.exp (-s/4) := by
  have he : Real.exp (-1) ≤ 1/2 := by
    rw [Real.exp_neg]
    have h₂ : (2:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ)
      linarith
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) h₂
  have h₁ : 1-s*(1-Real.exp (-1)) ≤ 1-s/2 := by nlinarith
  have h₂ : 1-s/2 ≤ Real.exp (-s/2) := by
    have := Real.add_one_le_exp (-s/2)
    linarith
  calc
    Real.exp (s/4)*(1-s*(1-Real.exp (-1))) ≤ Real.exp (s/4)*Real.exp (-s/2) :=
      mul_le_mul_of_nonneg_left (h₁.trans h₂) (Real.exp_pos _).le
    _ = Real.exp (-s/4) := by rw [←Real.exp_add]; congr 1; ring

lemma adaptive_failureWeight_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B : ℕ → Set Ω) (hB : ∀ n, MeasurableSet (B n))
    {s : ℝ} (hs : 0 ≤ s)
    (hstep : ∀ n, s*(∫ ω, failureWeight B s n ω ∂μ) ≤
      ∫ ω in B n, failureWeight B s n ω ∂μ) (n : ℕ) :
    (∫ ω, failureWeight B s n ω ∂μ) ≤ (Real.exp (-s/4))^n := by
  induction n with
  | zero => simp [failureWeight,successes]
  | succ n ih =>
    have hi := failureWeight_integrable μ B hB s n
    have his := hi.indicator (hB n)
    have hid : (fun ω => if ω ∈ B n then failureWeight B s n ω else 0) =
        (B n).indicator (failureWeight B s n) := by rfl
    have hi' : Integrable (fun ω => if ω ∈ B n then failureWeight B s n ω else 0) μ := by
      rw [hid]
      exact his
    have hEq : (∫ ω, failureWeight B s (n+1) ω ∂μ) = Real.exp (s/4)*
        ((∫ ω, failureWeight B s n ω ∂μ)-(1-Real.exp (-1))*
          ∫ ω in B n, failureWeight B s n ω ∂μ) := by
      simp_rw [failureWeight_step]
      rw [integral_const_mul,integral_sub hi (hi'.const_mul _),integral_const_mul]
      rw [hid,integral_indicator (hB n)]
    have h0 : 0 ≤ 1-Real.exp (-1) := by
      have := Real.exp_le_one_iff.mpr (show (-1:ℝ) ≤ 0 by norm_num)
      linarith
    have hw0 : 0 ≤ ∫ ω, failureWeight B s n ω ∂μ := integral_nonneg fun _ => (Real.exp_pos _).le
    rw [hEq]
    calc
      Real.exp (s/4)*((∫ ω, failureWeight B s n ω ∂μ)-(1-Real.exp (-1))*
          ∫ ω in B n, failureWeight B s n ω ∂μ)
        ≤ Real.exp (s/4)*(1-s*(1-Real.exp (-1)))*(∫ ω, failureWeight B s n ω ∂μ) := by
          have hh := mul_le_mul_of_nonneg_left (hstep n) h0
          nlinarith [Real.exp_pos (s/4)]
      _ ≤ Real.exp (-s/4)*(∫ ω, failureWeight B s n ω ∂μ) :=
        mul_le_mul_of_nonneg_right (failureWeight_contraction hs) hw0
      _ ≤ Real.exp (-s/4)*(Real.exp (-s/4))^n := mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = (Real.exp (-s/4))^(n+1) := by rw [pow_succ]; ring
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurable_failureSeries {Ω : Type*} [MeasurableSpace Ω] (B : ℕ → Set Ω)
    (hB : ∀ n, MeasurableSet (B n)) (s : ℝ) : Measurable (failureSeries B s) :=
  Measurable.tsum fun index => (measurable_failureWeight B hB s index).ennreal_ofReal

lemma failureSeries_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B : ℕ → Set Ω) (hB : ∀ n, MeasurableSet (B n))
    {s : ℝ} (hs : 0 < s)
    (hstep : ∀ n, s*(∫ ω, failureWeight B s n ω ∂μ) ≤
      ∫ ω in B n, failureWeight B s n ω ∂μ) :
    (∫⁻ ω, failureSeries B s ω ∂μ) ≤ ENNReal.ofReal ((1-Real.exp (-s/4))⁻¹) := by
  have hexp0 := (Real.exp_pos (-s/4)).le
  have hexp1 : Real.exp (-s/4) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum := summable_geometric_of_lt_one hexp0 hexp1
  unfold failureSeries
  rw [lintegral_tsum (fun n => (measurable_failureWeight B hB s n).ennreal_ofReal.aemeasurable)]
  calc
    ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal (failureWeight B s n ω) ∂μ
      ≤ ∑' n : ℕ, ENNReal.ofReal ((Real.exp (-s/4))^n) := by
        apply ENNReal.tsum_le_tsum
        intro n
        rw [←ofReal_integral_eq_lintegral_ofReal (failureWeight_integrable μ B hB s n)
          (ae_of_all _ fun _ => (Real.exp_pos _).le)]
        exact ENNReal.ofReal_le_ofReal (adaptive_failureWeight_mean μ B hB hs.le hstep n)
    _ = ENNReal.ofReal ((1-Real.exp (-s/4))⁻¹) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hexp0 n) hsum,
        tsum_geometric_of_lt_one hexp0 hexp1]

theorem adaptive_failure_excess {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B : ℕ → Set Ω) (hB : ∀ n, MeasurableSet (B n))
    {s : ℝ} (hs : 0 < s)
    (hstep : ∀ n, s*(∫ ω, failureWeight B s n ω ∂μ) ≤
      ∫ ω in B n, failureWeight B s n ω ∂μ) :
    ∃ W : Ω → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
      Integrable (fun ω => Real.exp (W ω)) μ ∧
      (∀ᵐ ω ∂μ, ∀ n : ℕ, s/4*(n:ℝ)-successes B n ω ≤ W ω) ∧
      (∫ ω, Real.exp (W ω) ∂μ) ≤ 1+(1-Real.exp (-s/4))⁻¹ := by
  let F := failureSeries B s
  have hF : Measurable F := measurable_failureSeries B hB s
  have hmean := failureSeries_mean μ B hB hs hstep
  have hfinite : (∫⁻ ω, F ω ∂μ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmean
  have hae : ∀ᵐ ω ∂μ, F ω ≠ ⊤ := (ae_lt_top hF hfinite).mono fun _ h => h.ne
  have hi : Integrable (fun ω => (F ω).toReal) μ := (integrable_toReal_iff hF.aemeasurable hae).mpr hfinite
  let W := fun ω => Real.log (1+(F ω).toReal)
  have hpos (ω) : 0 < 1+(F ω).toReal := by positivity
  have heq : (fun ω => Real.exp (W ω)) = fun ω => 1+(F ω).toReal := by
    funext ω
    exact Real.exp_log (hpos ω)
  refine ⟨W,(measurable_const.add hF.ennreal_toReal).log,?_,?_,?_,?_⟩
  · intro ω
    exact Real.log_nonneg (by have := ENNReal.toReal_nonneg (a := F ω); linarith)
  · rw [heq]
    exact (integrable_const _).add hi
  · filter_upwards [hae] with ω hω
    intro n
    have hh : failureWeight B s n ω ≤ (F ω).toReal := by
      have := ENNReal.toReal_mono hω (ENNReal.le_tsum (f := fun k => ENNReal.ofReal (failureWeight B s k ω)) n)
      have hn : 0 ≤ failureWeight B s n ω := (Real.exp_pos _).le
      simpa only [ENNReal.toReal_ofReal hn] using this
    have hl := Real.log_le_log (Real.exp_pos (s/4*(n:ℝ)-successes B n ω))
      (hh.trans (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)))
    simpa only [Real.log_exp] using hl
  · rw [heq,integral_add (integrable_const _) hi,integral_const]
    simp only [probReal_univ,smul_eq_mul,one_mul]
    apply add_le_add le_rfl
    rw [integral_toReal hF.aemeasurable (hae.mono fun _ h => lt_top_iff_ne_top.mpr h)]
    have hp : 0 ≤ (1-Real.exp (-s/4))⁻¹ := by
      apply inv_nonneg.mpr
      have := Real.exp_le_one_iff.mpr (show -s/4 ≤ 0 by linarith)
      linarith
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmean
    simpa only [ENNReal.toReal_ofReal hp] using this
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferRestorationScript
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma pairRestore_gap {d : ℕ} (e f : Direction d) (m : ℕ) (x : Lattice d × Lattice d) :
    signedCoordinate f ((pairRestore e f m x).2-(pairRestore e f m x).1) =
      signedCoordinate f (x.2-x.1)+m := by
  simp only [pairRestore,signedCoordinate_sub,signedCoordinate_add,signedCoordinate_nsmul,
    signedCoordinate_step_self,mul_one]
  ring

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairUpwardRetention
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma rawPairEndpointLaw_upward {d : ℕ} (e : Direction d)
    (H : ℕ) (ω : Environment d) (x : Lattice d × Lattice d)
    {κ : ℝ≥0} (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ : ℝ≥0∞)^2 • (rawPairEndpointLaw (realPosition (step e)) H ω x).map (pairUp e) ≤
      rawPairEndpointLaw (realPosition (step e)) (H+1) ω x := by
  let ℓ := realPosition (step e)
  have hfinite (y : Lattice d) (h : ℕ) :
      IsFiniteMeasure (hitKernel (Strip ℓ y h) (Upper ℓ y h) (ω,y)) :=
    ⟨lt_of_le_of_lt (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _) ENNReal.one_lt_top⟩
  let := hfinite x.1 H
  let := hfinite x.2 H
  let := hfinite x.1 (H+1)
  let := hfinite x.2 (H+1)
  have hp := Measure.prod_mono (coordinate_hitKernel_upward_retention e x.1 H ω hκ)
    (coordinate_hitKernel_upward_retention e x.2 H ω hκ)
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,←pow_two,
    Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)] at hp
  unfold pairUp
  simpa only [rawPairEndpointLaw,Prod.map_def,Nat.cast_add,Nat.cast_one] using hp

lemma rawPairMixture_upward {d : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) (π : Measure (Lattice d × Lattice d))
    {κ : ℝ≥0} (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ : ℝ≥0∞)^2 • (rawPairMixture (realPosition (step e)) H π ω).map (pairUp e) ≤
      rawPairMixture (realPosition (step e)) (H+1) π ω := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  have hm : Measurable (pairUp e) := measurable_of_countable _
  rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply hm hU,rawPairMixture_apply,
    ←lintegral_const_mul _ (measurable_of_countable _),rawPairMixture_apply]
  apply lintegral_mono
  intro x
  have hh := rawPairEndpointLaw_upward e H ω x hκ U
  rwa [Measure.smul_apply,smul_eq_mul,Measure.map_apply hm hU] at hh

lemma pairUp_preserves_gap {d : ℕ} (e f : Direction d) (x : Lattice d × Lattice d) :
    signedCoordinate f ((pairUp e x).2-(pairUp e x).1) = signedCoordinate f (x.2-x.1) := by
  dsimp [pairUp]
  congr 1
  abel

lemma upwardRetainedLaw_le {d : ℕ} (e f : Direction d) (H : ℕ) (z : ℝ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) :
    upwardRetainedLaw e f H z π ω κ ≤ rawPairMixture (realPosition (step e)) (H+1) π ω := by
  apply le_trans _ (rawPairMixture_upward e H ω π hκ)
  intro U
  have hU := (Set.to_countable U).measurableSet
  simp only [upwardRetainedLaw,Measure.smul_apply,smul_eq_mul,
    Measure.map_apply (measurable_of_countable _) hU]
  exact mul_le_mul_right (retainedPairLaw_le _ _ _ _ _ _ _) _

lemma upwardRetainedLaw_mass {d : ℕ} (e f : Direction d) (H : ℕ) (z : ℝ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) (κ : ℝ≥0) :
    upwardRetainedLaw e f H z π ω κ Set.univ =
      (κ : ℝ≥0∞)^2 * pairKernelMass (realPosition (step e)) f H z π ω := by
  simp only [upwardRetainedLaw,Measure.smul_apply,smul_eq_mul,
    Measure.map_apply (measurable_of_countable _) MeasurableSet.univ,
    Set.preimage_univ,retainedPairLaw_mass]

lemma upwardRetainedLaw_support {d : ℕ} (e f : Direction d) (H : ℕ) (z : ℝ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) (κ : ℝ≥0) :
    ∀ᵐ y ∂upwardRetainedLaw e f H z π ω κ, z ≤ signedCoordinate f (y.2-y.1) := by
  unfold upwardRetainedLaw
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (measurableSet_le measurable_const (measurable_of_countable _))]
  simpa only [pairUp_preserves_gap] using retainedPairLaw_support (realPosition (step e)) f H z π ω
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPair
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma pairKernelMass_zero_of_supported {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (ω : Environment d) (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (z : ℝ) (hπ : ∀ᵐ x ∂π, z ≤ signedCoordinate f (x.2-x.1)) :
    pairKernelMass ℓ f 0 z π ω = 1 := by
  unfold pairKernelMass
  rw [←rawPairMixture_apply,rawPairMixture_zero]
  exact (mem_ae_iff_prob_eq_one (Set.to_countable _ |>.measurableSet)).mp hπ
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferStageRetainedLaw_le {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) :
    bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ ≤
      rawPairMixture (realPosition (step e))
        (bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω) (π ω).val ω := by
  let ℓ := realPosition (step e)
  let z := z₀+(1-ε)*r
  let j := bufferFirstFailure ℓ f a z g π H ω
  have hj : 1 ≤ j := (bufferFirstFailure_bounds ℓ f a z g π hH ω).1
  unfold bufferStageRetainedLaw
  dsimp only
  split
  · have hn : j-1+1=j := by omega
    simpa only [hn] using upwardRetainedLaw_le e f (j-1) z (π ω).val ω hκ
  · rename_i hp
    have hjH : j=H := bufferFirstFailure_eq_top_of_pass ℓ f a z g π hH ω (le_of_not_gt hp)
    change _ ≤ rawPairMixture ℓ j (π ω).val ω
    rw [hjH]
    split <;> exact retainedPairLaw_le _ _ _ _ _ _

lemma bufferStageRetainedLaw_mass_lower {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (κ : ℝ≥0)
    (hκ1 : κ ≤ 1) (hg1 : g ≤ 1) (hr : 0 ≤ r) (hε : 0 ≤ ε)
    [IsProbabilityMeasure (π ω).val]
    (hgap : ∀ᵐ x ∂(π ω).val, z₀+r ≤ signedCoordinate f (x.2-x.1)) :
    (κ : ℝ≥0∞)^2 * ENNReal.ofReal g ≤ bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ Set.univ := by
  let ℓ := realPosition (step e)
  let z := z₀+(1-ε)*r
  let j := bufferFirstFailure ℓ f a z g π H ω
  have hj : 1 ≤ j := (bufferFirstFailure_bounds ℓ f a z g π hH ω).1
  have hκ2 : (κ : ℝ≥0∞)^2 ≤ 1 := by
    have hc : (κ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hκ1
    simpa only [one_pow] using pow_le_pow_left' hc 2
  have hsmall : (κ : ℝ≥0∞)^2 * ENNReal.ofReal g ≤ ENNReal.ofReal g := by
    calc
      _ ≤ 1*ENNReal.ofReal g := mul_le_mul_left hκ2 _
      _ = _ := one_mul _
  unfold bufferStageRetainedLaw
  dsimp only
  split
  · rw [upwardRetainedLaw_mass]
    apply mul_le_mul_right
    by_cases hz : j-1=0
    · change ENNReal.ofReal g ≤ pairKernelMass ℓ f (j-1) z (π ω).val ω
      rw [hz,pairKernelMass_zero_of_supported ℓ f ω (π ω).val z]
      · exact ENNReal.ofReal_le_one.mpr hg1
      · filter_upwards [hgap] with x hx
        dsimp [z]
        nlinarith
    · apply before_bufferFirstFailure_pass ℓ f a z g π H ω (Nat.pos_of_ne_zero hz)
      change j-1<j
      omega
  · rename_i hp
    have hjH : j=H := bufferFirstFailure_eq_top_of_pass ℓ f a z g π hH ω (le_of_not_gt hp)
    split
    · rename_i hg
      rw [retainedPairLaw_mass]
      exact hsmall.trans hg
    · rw [retainedPairLaw_mass]
      apply hsmall.trans
      have hh : ENNReal.ofReal g ≤ pairKernelMass ℓ f j z (π ω).val ω := le_of_not_gt hp
      change ENNReal.ofReal g ≤ pairKernelMass ℓ f H z (π ω).val ω
      simpa only [hjH] using hh
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferStagePacket
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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
lemma bufferStageRetainedLaw_success {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (κ : ℝ≥0)
    (hE : BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω) :
    bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ =
      retainedPairLaw (realPosition (step e)) f H (z₀+(1+α)*r) (π ω).val ω := by
  have ht := (bufferStageEvent_iff_last_tests (realPosition (step e)) f a z₀ r ε α g π hH ω).mp hE
  simp only [bufferStageRetainedLaw,ite_eq_right (not_lt_of_ge ht.1),ite_eq_left ht.2]

lemma bufferStageRetainedLaw_failure_support {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (κ : ℝ≥0)
    (hE : ¬ BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω) :
    ∀ᵐ y ∂bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ,
      z₀+(1-ε)*r ≤ signedCoordinate f (y.2-y.1) := by
  unfold bufferStageRetainedLaw
  dsimp only
  split
  · exact upwardRetainedLaw_support _ _ _ _ _ _ _
  · rename_i hp
    have hn : ¬ ENNReal.ofReal g ≤ pairKernelMass (realPosition (step e)) f H
        (z₀+(1+α)*r) (π ω).val ω := by
      intro hh
      apply hE
      exact (bufferStageEvent_iff_last_tests (realPosition (step e)) f a z₀ r ε α g π hH ω).mpr
        ⟨le_of_not_gt hp,hh⟩
    simp only [ite_eq_right hn]
    exact retainedPairLaw_support _ _ _ _ _ _

lemma bufferStageRetainedLaw_probability {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) (hκpos : 0 < κ)
    (hκ1 : κ ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1) (hr : 0 ≤ r) (hε : 0 ≤ ε)
    [IsProbabilityMeasure (π ω).val]
    (hgap : ∀ᵐ x ∂(π ω).val, z₀+r ≤ signedCoordinate f (x.2-x.1)) :
    IsProbabilityMeasure (normalizedMeasure (bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ)) := by
  have hle := bufferStageRetainedLaw_le e f a z₀ r ε α g π hH ω hκ
  have hl := bufferStageRetainedLaw_mass_lower e f a z₀ r ε α g π hH ω κ hκ1 hg1 hr hε hgap
  have hm : bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ Set.univ ≤ 1 :=
    (hle _).trans (rawPairMixture_le_one _ _ _ _)
  let : IsFiniteMeasure (bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ) :=
    ⟨lt_of_le_of_lt hm ENNReal.one_lt_top⟩
  apply normalizedMeasure_probability
  apply ne_of_gt (lt_of_lt_of_le _ hl)
  have hκ0 : (κ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκpos.ne'
  exact ENNReal.mul_pos (pow_ne_zero 2 hκ0) (ENNReal.ofReal_pos.mpr hg).ne'
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_BufferStructuralHeight
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma bufferStageStoppedProbability_gap {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (H : ℕ) (hH : 0 < H) (κ : ℝ≥0) (k : ℕ) (ω : Environment d) :
    ∀ᵐ y ∂(bufferStageStoppedProbability e f a z₀ r ε α g π H hH κ k ω).val,
      z₀+(if BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω
        then (1+α)*r else (1-ε)*r) ≤ signedCoordinate f (y.2-y.1) := by
  by_cases hk : bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k
  · simp only [bufferStageStoppedProbability,ite_eq_left hk]
    apply Measure.ae_smul_measure
    by_cases hE : BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω
    · rw [ite_eq_left hE,bufferStageRetainedLaw_success e f a z₀ r ε α g π hH ω κ hE]
      exact retainedPairLaw_support _ _ _ _ _ _
    · rw [ite_eq_right hE]
      exact bufferStageRetainedLaw_failure_support e f a z₀ r ε α g π hH ω κ hE
  · simp [bufferStageStoppedProbability,ite_eq_right hk]
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferChildNode
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma bufferRestoreLength_enough (R₀ r ε α : ℝ) (b : Bool) :
    bufferNextRadius R₀ r ε α b ≤
      (if b then 1+α else 1-ε)*r + bufferRestoreLength R₀ r ε α b := by
  have h := Nat.le_ceil (max 0 (R₀-((if b then 1+α else 1-ε)*r)))
  unfold bufferNextRadius bufferRestoreLength
  apply max_le
  · have := le_max_right 0 (R₀-((if b then 1+α else 1-ε)*r))
    linarith
  · exact le_add_of_nonneg_right (Nat.cast_nonneg _)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferChildNode_valid {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) {κ : ℝ≥0} (hκpos : 0 < κ) (hκ1 : κ ≤ 1)
    (hg : 0 < g) (hg1 : g ≤ 1) (hε : 0 ≤ ε) (N : AdaptedBufferNode e)
    (hr : 0 ≤ N.radius) (hN : BufferNodeValid e f z₀ κ N)
    (H : ℕ) (hH : 0 < H) (k : ℕ) (b : Bool) :
    BufferNodeValid e f z₀ κ (bufferChildNode e f hef R₀ z₀ ε α g κ N H hH k b) := by
  intro ω hκ hω
  have hparent : ω ∈ N.active := hω.1
  have hk : bufferFirstFailure (realPosition (step e)) f N.level (z₀+(1-ε)*N.radius) g N.law H ω = k := hω.2.1
  have hb : BufferStageEvent (realPosition (step e)) f H z₀ N.radius ε α g (N.law ω).val ω ↔ b=true := hω.2.2
  obtain ⟨hp,hgap⟩ := hN ω hκ hparent
  let := hp
  have hp' : IsProbabilityMeasure (bufferStageStoppedProbability e f N.level z₀ N.radius ε α g N.law H hH κ k ω).val := by
    simp only [bufferStageStoppedProbability,ite_eq_left hk]
    exact bufferStageRetainedLaw_probability e f N.level z₀ N.radius ε α g N.law hH ω
      (fun y => hκ y e) hκpos hκ1 hg hg1 hr hε hgap
  let := hp'
  have hmap : IsProbabilityMeasure ((bufferStageStoppedProbability e f N.level z₀ N.radius ε α g N.law H hH κ k ω).val.map
      (pairRestore e f (bufferRestoreLength R₀ N.radius ε α b))) := by
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hgapmap : ∀ᵐ x ∂(bufferStageStoppedProbability e f N.level z₀ N.radius ε α g N.law H hH κ k ω).val.map
      (pairRestore e f (bufferRestoreLength R₀ N.radius ε α b)),
      z₀+bufferNextRadius R₀ N.radius ε α b ≤ signedCoordinate f (x.2-x.1) := by
    rw [ae_map_iff (measurable_of_countable _).aemeasurable (measurableSet_le measurable_const (measurable_of_countable _))]
    filter_upwards [bufferStageStoppedProbability_gap e f N.level z₀ N.radius ε α g N.law H hH κ k ω] with x hx
    rw [pairRestore_gap]
    have hR := bufferRestoreLength_enough R₀ N.radius ε α b
    cases b
    · have hn : ¬ BufferStageEvent (realPosition (step e)) f H z₀ N.radius ε α g (N.law ω).val ω := by simpa using hb
      simp only [ite_eq_right hn] at hx
      simp only [Bool.false_eq_true,↓reduceIte] at hR
      linarith
    · have hy : BufferStageEvent (realPosition (step e)) f H z₀ N.radius ε α g (N.law ω).val ω := hb.mpr rfl
      simp only [ite_eq_left hy] at hx
      simp only [↓reduceIte] at hR
      linarith
  exact ⟨hmap,hgapmap⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_Buffer
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma bufferRootNode_valid {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a)
    (κ : ℝ≥0) :
    BufferNodeValid e f (signedCoordinate f (x.2-x.1)) κ (bufferRootNode e f hef R₀ a x hx) := by
  intro ω _ _
  have hp : IsProbabilityMeasure (Measure.dirac (pairRestore e f ⌈R₀⌉₊ x)) := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hg : ∀ᵐ y ∂Measure.dirac (pairRestore e f ⌈R₀⌉₊ x),
      signedCoordinate f (x.2-x.1)+R₀ ≤ signedCoordinate f (y.2-y.1) := by
    rw [ae_dirac_iff (Set.to_countable _).measurableSet,pairRestore_gap]
    linarith [Nat.le_ceil R₀]
  exact ⟨hp,hg⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferTree
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma bufferNodeAt_radius {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (hr : R₀ ≤ root.radius) (l : List (ℕ × Bool)) :
    R₀ ≤ (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l).radius := by
  cases l with
  | nil => exact hr
  | cons p l => exact le_max_left _ _

lemma bufferNodeAt_valid {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (z₀ ε α g : ℝ) {κ : ℝ≥0}
    (hκpos : 0 < κ) (hκ1 : κ ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1) (hε : 0 ≤ ε)
    (H : ℝ → ℕ) (hH : ∀ r, 0 < H r) (root : AdaptedBufferNode e)
    (hr : R₀ ≤ root.radius) (hroot : BufferNodeValid e f z₀ κ root) (l : List (ℕ × Bool)) :
    BufferNodeValid e f z₀ κ (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l) := by
  induction l with
  | nil => exact hroot
  | cons p l ih =>
    exact bufferChildNode_valid e f hef R₀ z₀ ε α g hκpos hκ1 hg hg1 hε _
      (hR₀.trans (bufferNodeAt_radius e f hef R₀ z₀ ε α g κ H hH root hr l)) ih _ (hH _) p.1 p.2

lemma mem_bufferChildNode_iff {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (N : AdaptedBufferNode e) (p : ℕ × Bool) (ω : Environment d) :
    ω ∈ (bufferChildNode e f hef R₀ z₀ ε α g κ N (H N.radius) (hH N.radius) p.1 p.2).active ↔
      ω ∈ N.active ∧ bufferNodeDecision e f z₀ ε α g H N ω=p := by
  change (_ ∧ _ ∧ (_ ↔ p.2=true)) ↔ (_ ∧ (_,decide _)=p)
  rw [Prod.ext_iff]
  suffices (BufferStageEvent (realPosition (step e)) f (H N.radius) z₀ N.radius ε α g (N.law ω).val ω ↔ p.2=true) ↔
      decide (BufferStageEvent (realPosition (step e)) f (H N.radius) z₀ N.radius ε α g (N.law ω).val ω)=p.2 by tauto
  cases p.2 <;> simp

lemma bufferHistory_length {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (n : ℕ) :
    (bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bufferHistory,List.length_cons,ih]

lemma bufferNodeAt_active_iff_history {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (l : List (ℕ × Bool)) :
    ω ∈ (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l).active ↔
      ω ∈ root.active ∧ bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω l.length=l := by
  induction l with
  | nil => simp only [bufferNodeAt,bufferHistory,List.length_nil,and_true]
  | cons p l ih =>
    rw [bufferNodeAt,mem_bufferChildNode_iff e f hef R₀ z₀ ε α g κ H hH
      (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l) p ω,ih]
    simp only [List.length_cons,bufferHistory,List.cons.injEq]
    constructor
    · rintro ⟨⟨hr,hl⟩,hp⟩
      exact ⟨hr,by simpa only [hl] using hp,hl⟩
    · rintro ⟨hr,hp,hl⟩
      exact ⟨⟨hr,hl⟩,by simpa only [hl] using hp⟩
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferTreeSuccess_measurable {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (n : ℕ) :
    MeasurableSet (bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root n) := by
  apply MeasurableSet.iUnion
  intro l
  let N := bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val
  have ha : MeasurableSet N.active := rowSigma_le _ _ N.active_rows
  have hp : Measurable N.law := N.law_rows.mono (rowSigma_le _) le_rfl
  have he := (measurableSet_bufferStageEvent_rows (realPosition (step e)) f (hH N.radius)
    z₀ N.radius ε α g (PairAtHeight (realPosition (step e)) N.level) Set.univ
    (fun x hx => ⟨Set.subset_univ _,Set.subset_univ _⟩)).preimage
      (hp.prodMk (measurable_id.mono le_rfl (rowSigma_le Set.univ)))
  convert ha.inter he using 1
  all_goals try with_reducible_and_instances rfl
  ext ω
  simp only [bufferNodeDecision,decide_eq_true_eq,Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,id_eq]
  rfl

lemma bufferWords_partition {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (n : ℕ) :
    (⋃ l : BufferWords n, (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val).active) = root.active ∧
    Pairwise (Disjoint on fun l : BufferWords n =>
      (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val).active) := by
  constructor
  · ext ω
    constructor
    · intro h
      obtain ⟨l,hl⟩ := Set.mem_iUnion.mp h
      exact (bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω l.val).mp hl |>.1
    · intro hr
      let l : BufferWords n := ⟨bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n,
        bufferHistory_length e f hef R₀ z₀ ε α g κ H hH root ω n⟩
      apply Set.mem_iUnion.mpr
      refine ⟨l,(bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω l.val).mpr ?_⟩
      exact ⟨hr,by rw [l.property]⟩
  · intro l m hlm
    apply Set.disjoint_left.mpr
    intro ω hl hm
    apply hlm
    apply Subtype.ext
    have hl' := (bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω l.val).mp hl |>.2
    have hm' := (bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω m.val).mp hm |>.2
    rw [l.property] at hl'
    rw [m.property] at hm'
    exact hl'.symm.trans hm'

lemma bufferTreeSuccess_iff_decision {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (hr : ω ∈ root.active) (n : ℕ) :
    ω ∈ bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root n ↔
      (bufferNodeDecision e f z₀ ε α g H (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root
        (bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n)) ω).2=true := by
  constructor
  · intro h
    obtain ⟨l,hl,hb⟩ := Set.mem_iUnion.mp h
    have hh := (bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω l.val).mp hl |>.2
    rw [l.property] at hh
    simpa only [hh] using hb
  · intro hb
    let l : BufferWords n := ⟨bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n,
      bufferHistory_length e f hef R₀ z₀ ε α g κ H hH root ω n⟩
    apply Set.mem_iUnion.mpr
    refine ⟨l,?_,hb⟩
    apply (bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω l.val).mpr
    exact ⟨hr,by rw [l.property]⟩

lemma bufferWordSuccesses_history {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (hr : ω ∈ root.active) (n : ℕ) :
    bufferWordSuccesses (bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n) =
      successes (bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root) n ω := by
  induction n with
  | zero => simp [bufferHistory,bufferWordSuccesses,successes]
  | succ n ih =>
    rw [bufferHistory,bufferWordSuccesses,ih,successes_succ]
    have hb := bufferTreeSuccess_iff_decision e f hef R₀ z₀ ε α g κ H hH root ω hr n
    simp only [←hb]
    ring

lemma buffer_failureWeight_on_branch {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (s : ℝ) (n : ℕ) (l : BufferWords n) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e))
      (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val).level)) _
      ((bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val).active.indicator
        (fun ω => ENNReal.ofReal (failureWeight (bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root) s n ω))) := by
  let N := bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val
  have he : N.active.indicator (fun ω => ENNReal.ofReal (failureWeight
      (bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root) s n ω)) =
      N.active.indicator (fun _ => ENNReal.ofReal (Real.exp (s/4*(n:ℝ)-bufferWordSuccesses l.val))) := by
    apply Set.indicator_congr
    intro ω hω
    have hh := (bufferNodeAt_active_iff_history e f hef R₀ z₀ ε α g κ H hH root ω l.val).mp hω
    have hc := bufferWordSuccesses_history e f hef R₀ z₀ ε α g κ H hH root ω hh.1 n
    rw [l.property] at hh
    rw [hh.2] at hc
    simp only [failureWeight,←hc]
  change @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) N.level)) _ _
  rw [he]
  exact measurable_const.indicator N.active_rows
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferChanceData
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma bufferStageEvent_threshold_mono {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z₀ r ε α : ℝ) {g g' : ℝ} (hgg : g' ≤ g)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    BufferStageEvent ℓ f H z₀ r ε α g π ω → BufferStageEvent ℓ f H z₀ r ε α g' π ω := by
  rintro ⟨ht,hf⟩
  exact ⟨fun j hj hjH => (ENNReal.ofReal_le_ofReal hgg).trans (ht j hj hjH),
    (ENNReal.ofReal_le_ofReal hgg).trans hf⟩

theorem actual_buffer_chance_data {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ α c : ℝ, 0 < α ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε →
      ∃ g R : ℝ, 0 < g ∧ g ≤ 1 ∧ 0 < R ∧ BufferChanceData ν e f α c ε g R := by
  obtain ⟨α,c,hα,hc,hchance⟩ := buffer_stage_success_probability ν hue e f hef htrans
  refine ⟨α,c,hα,hc,fun ε hε => ?_⟩
  obtain ⟨g,R,hg,hR,hgood⟩ := hchance ε hε
  refine ⟨min g 1,R,lt_min hg zero_lt_one,min_le_right _ _,hR,?_⟩
  intro r hr
  obtain ⟨hH,hπ⟩ := hgood r hr
  have hplan : positiveBufferPlan ν e f r = ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊ := max_eq_right hH
  refine ⟨hplan,fun z₀ π hp hgap => ?_⟩
  have hh := hπ z₀ π hp hgap
  have hb : ENNReal.ofReal c ≤ environmentLaw ν {ω | BufferStageEvent (realPosition (step e)) f
      (positiveBufferPlan ν e f r) z₀ r ε α g π ω} := by
    rw [hplan]
    have he : {ω | BufferStageEvent (realPosition (step e)) f
        ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊ z₀ r ε α g π ω} =
        {ω | BufferStageSuccess (realPosition (step e)) f
        ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊ z₀ r ε α g π ω} := by
      ext ω
      exact bufferStageEvent_iff e f hH z₀ r ε α hg.le π ω
    rw [he]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr hh
  exact hb.trans (measure_mono fun ω hω => bufferStageEvent_threshold_mono _ _ _ _ _ _ _
    (min_le_left g 1) π ω hω)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferTree_weighted_success {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (z₀ ε α g c : ℝ) {κ : ℝ≥0} (hκpos : 0 < κ) (hκ1 : κ ≤ 1)
    (hκae : ∀ᵐ ω ∂environmentLaw ν, ∀ y u, κ ≤ (ω y).1 u)
    (hg : 0 < g) (hg1 : g ≤ 1) (hε : 0 ≤ ε)
    (hdata : BufferChanceData ν e f α c ε g R₀) (root : AdaptedBufferNode e)
    (hr : R₀ ≤ root.radius) (hroot : BufferNodeValid e f z₀ κ root)
    (hactive : root.active=Set.univ) (s : ℝ) (n : ℕ) :
    let B := bufferTreeSuccess e f hef R₀ z₀ ε α g κ (positiveBufferPlan ν e f)
      (positiveBufferPlan_pos ν e f) root
    ENNReal.ofReal c*(∫⁻ ω, ENNReal.ofReal (failureWeight B s n ω) ∂environmentLaw ν) ≤
      ∫⁻ ω in B n, ENNReal.ofReal (failureWeight B s n ω) ∂environmentLaw ν := by
  let H := positiveBufferPlan ν e f
  let hH := positiveBufferPlan_pos ν e f
  let nodes := fun l : BufferWords n => bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val
  let A := fun l : BufferWords n => (nodes l).active
  let E := fun l : BufferWords n => {ω | BufferStageEvent (realPosition (step e)) f (H (nodes l).radius)
    z₀ (nodes l).radius ε α g ((nodes l).law ω).val ω}
  let B := bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root
  let w := fun ω => ENNReal.ofReal (failureWeight B s n ω)
  have hAm (l) : MeasurableSet (A l) := rowSigma_le _ _ (nodes l).active_rows
  have hEm (l) : MeasurableSet (E l) := by
    have hp := (nodes l).law_rows.mono (rowSigma_le _) le_rfl
    exact (measurableSet_bufferStageEvent_rows (realPosition (step e)) f (hH _) z₀ (nodes l).radius ε α g
      (PairAtHeight (realPosition (step e)) (nodes l).level) Set.univ
      (fun x hx => ⟨Set.subset_univ _,Set.subset_univ _⟩)).preimage
        (hp.prodMk (measurable_id.mono le_rfl (rowSigma_le Set.univ)))
  have hpart := bufferWords_partition e f hef R₀ z₀ ε α g κ H hH root n
  have hbound (l : BufferWords n) : ENNReal.ofReal c*(∫⁻ ω in A l, w ω ∂environmentLaw ν) ≤
      ∫⁻ ω in A l ∩ E l, w ω ∂environmentLaw ν := by
    let N := nodes l
    let D := BelowHeight (realPosition (step e)) N.level
    have hC (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) N.level) :
        Strip (realPosition (step e)) x.1 (H N.radius) ⊆ Dᶜ ∧
        Strip (realPosition (step e)) x.2 (H N.radius) ⊆ Dᶜ := by
      constructor
      · intro y hy
        change ¬ dot (realPosition y) (realPosition (step e)) < N.level
        have hh := hy.1
        rw [hx.1] at hh
        exact not_lt_of_ge hh
      · intro y hy
        change ¬ dot (realPosition y) (realPosition (step e)) < N.level
        have hh := hy.1
        rw [hx.2] at hh
        exact not_lt_of_ge hh
    have hNr : R₀ ≤ N.radius := bufferNodeAt_radius e f hef R₀ z₀ ε α g κ H hH root hr l.val
    have hNv := bufferNodeAt_valid e f hef hR₀.le z₀ ε α g hκpos hκ1 hg hg1 hε H hH root hr hroot l.val
    have hvalid : ∀ᵐ ω ∂environmentLaw ν, ω ∈ N.active → IsProbabilityMeasure (N.law ω).val ∧
        ∀ᵐ x ∂(N.law ω).val, z₀+N.radius ≤ signedCoordinate f (x.2-x.1) :=
      hκae.mono fun ω hω hA => hNv ω hω hA
    have hw := buffer_failureWeight_on_branch e f hef R₀ z₀ ε α g κ H hH root s n l
    have hh := fresh_buffer_weight_ae_valid ν (realPosition (step e)) f (hH N.radius)
      z₀ N.radius ε α g c (PairAtHeight (realPosition (step e)) N.level) D Dᶜ
      disjoint_compl_right hC (fun π hp hgap => (hdata N.radius hNr).2 z₀ π.val hp hgap)
      N.law N.law_rows N.active N.active_rows hvalid (N.active.indicator w) hw
    have hleft : (∫⁻ ω in N.active, N.active.indicator w ω ∂environmentLaw ν) =
        ∫⁻ ω in N.active, w ω ∂environmentLaw ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hAm l)] with ω hω
      exact Set.indicator_of_mem hω _
    have hright : (∫⁻ ω in N.active ∩ E l, N.active.indicator w ω ∂environmentLaw ν) =
        ∫⁻ ω in N.active ∩ E l, w ω ∂environmentLaw ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem ((hAm l).inter (hEm l))] with ω hω
      exact Set.indicator_of_mem hω.1 _
    change ENNReal.ofReal c*(∫⁻ ω in N.active, N.active.indicator w ω ∂environmentLaw ν) ≤
      ∫⁻ ω in N.active ∩ E l, N.active.indicator w ω ∂environmentLaw ν at hh
    rw [hleft,hright] at hh
    exact hh
  have hh := weighted_countable_partition_lower (environmentLaw ν) A (fun l => A l ∩ E l) hAm
    (fun l => (hAm l).inter (hEm l)) hpart.2 (fun _ => Set.inter_subset_left) w (ENNReal.ofReal c) hbound
  have ha : (⋃ l, A l)=Set.univ := hpart.1.trans hactive
  have hb : (⋃ l, A l ∩ E l)=B n := by
    unfold B bufferTreeSuccess
    congr 1
    funext l
    ext ω
    simp only [A,E,nodes,bufferNodeDecision,Set.mem_inter_iff,Set.mem_ofPred,decide_eq_true_eq]
  rw [ha,Measure.restrict_univ,hb] at hh
  exact hh

lemma bufferTree_real_success {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hef : e.1 ≠ f.1) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (z₀ ε α g c : ℝ) (hc : 0 ≤ c) {κ : ℝ≥0} (hκpos : 0 < κ) (hκ1 : κ ≤ 1)
    (hκae : ∀ᵐ ω ∂environmentLaw ν, ∀ y u, κ ≤ (ω y).1 u)
    (hg : 0 < g) (hg1 : g ≤ 1) (hε : 0 ≤ ε)
    (hdata : BufferChanceData ν e f α c ε g R₀) (root : AdaptedBufferNode e)
    (hr : R₀ ≤ root.radius) (hroot : BufferNodeValid e f z₀ κ root)
    (hactive : root.active=Set.univ) (n : ℕ) :
    let B := bufferTreeSuccess e f hef R₀ z₀ ε α g κ (positiveBufferPlan ν e f)
      (positiveBufferPlan_pos ν e f) root
    c*(∫ ω, failureWeight B c n ω ∂environmentLaw ν) ≤
      ∫ ω in B n, failureWeight B c n ω ∂environmentLaw ν := by
  let B := bufferTreeSuccess e f hef R₀ z₀ ε α g κ (positiveBufferPlan ν e f)
      (positiveBufferPlan_pos ν e f) root
  have hBm := bufferTreeSuccess_measurable e f hef R₀ z₀ ε α g κ
    (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root
  have hi := failureWeight_integrable (environmentLaw ν) B hBm c n
  have hp (ω) : 0 ≤ failureWeight B c n ω := (Real.exp_pos _).le
  have hh := bufferTree_weighted_success ν e f hef hR₀ z₀ ε α g c hκpos hκ1 hκae hg hg1 hε hdata root hr hroot hactive c n
  change ENNReal.ofReal c*(∫⁻ ω, ENNReal.ofReal (failureWeight B c n ω) ∂environmentLaw ν) ≤
      ∫⁻ ω in B n, ENNReal.ofReal (failureWeight B c n ω) ∂environmentLaw ν at hh
  rw [←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hp),
    ←ofReal_integral_eq_lintegral_ofReal hi.restrict (ae_of_all _ hp),←ENNReal.ofReal_mul hc] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hp)).mp hh
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_BufferGrowthArithmetic
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma buffer_log_recurrence {Ω : Type*} (B : ℕ → Set Ω) (ω : Ω)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (A D : ℝ)
    (hstep : ∀ n, R n * Real.exp (if ω ∈ B n then A else -D) ≤ R (n+1)) (n : ℕ) :
    Real.log (R n)+(if ω ∈ B n then A else -D) ≤ Real.log (R (n+1)) := by
  have hp : 0 < R n * Real.exp (if ω ∈ B n then A else -D) := mul_pos (hR n) (Real.exp_pos _)
  have hh := Real.log_le_log hp (hstep n)
  rwa [Real.log_mul (hR n).ne' (Real.exp_pos _).ne',Real.log_exp] at hh

lemma buffer_log_sum {Ω : Type*} (B : ℕ → Set Ω) (ω : Ω)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (A D : ℝ)
    (hstep : ∀ n, R n * Real.exp (if ω ∈ B n then A else -D) ≤ R (n+1)) (n : ℕ) :
    Real.log (R 0) + successes B n ω*(A+D) - (n:ℝ)*D ≤ Real.log (R n) := by
  induction n with
  | zero => simp [successes]
  | succ n ih =>
    have hh := buffer_log_recurrence B ω R hR A D hstep n
    rw [successes_succ,Nat.cast_add,Nat.cast_one]
    by_cases hb : ω ∈ B n
    · simp only [ite_eq_left hb] at hh ⊢
      nlinarith
    · simp only [ite_eq_right hb] at hh ⊢
      nlinarith

lemma buffer_log_growth {Ω : Type*} (B : ℕ → Set Ω) (ω : Ω)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) {A s W : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s)
    (hstep : ∀ n, R n * Real.exp (if ω ∈ B n then A else -(s*A/8)) ≤ R (n+1))
    (hexcess : ∀ n : ℕ, s/4*(n:ℝ)-successes B n ω ≤ W) (n : ℕ) :
    Real.log (R 0) + (s*A/8)*(n:ℝ) - W*(A+s*A/8) ≤ Real.log (R n) := by
  have hh := buffer_log_sum B ω R hR A (s*A/8) hstep n
  have hAD : 0 ≤ A+s*A/8 := by positivity
  have hc := mul_le_mul_of_nonneg_right (hexcess n) hAD
  have hn : 0 ≤ s*s*A*(n:ℝ) := by positivity
  nlinarith

lemma buffer_contraction_choice {α s : ℝ} (hα : 0 < α) (hs : 0 < s) :
    let ε := 1-Real.exp (-(s*Real.log (1+α)/8))
    0 < ε ∧ ε < 1 ∧ Real.exp (Real.log (1+α))=1+α ∧
      Real.exp (-(s*Real.log (1+α)/8))=1-ε := by
  have hA : 0 < Real.log (1+α) := Real.log_pos (by linarith)
  have hd : 0 < s*Real.log (1+α)/8 := by positivity
  have he := Real.exp_lt_one_iff.mpr (show -(s*Real.log (1+α)/8)<0 by linarith)
  have hep := Real.exp_pos (-(s*Real.log (1+α)/8))
  dsimp only
  refine ⟨by linarith,by linarith,Real.exp_log (by linarith),by ring⟩
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferCurrentNode_succ {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (n : ℕ) :
    let N := bufferCurrentNode e f hef R₀ z₀ ε α g κ H hH root ω n
    let p := bufferNodeDecision e f z₀ ε α g H N ω
    bufferCurrentNode e f hef R₀ z₀ ε α g κ H hH root ω (n+1) =
      bufferChildNode e f hef R₀ z₀ ε α g κ N (H N.radius) (hH N.radius) p.1 p.2 := rfl

lemma bufferNextRadius_exponential_step (R₀ r ε α A D : ℝ)
    (hα : Real.exp A=1+α) (hε : Real.exp (-D)=1-ε) (b : Bool) :
    r*Real.exp (if b then A else -D) ≤ bufferNextRadius R₀ r ε α b := by
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte,bufferNextRadius,hα,hε]
  · simpa only [mul_comm] using (le_max_right R₀ ((1-ε)*r))
  · simpa only [mul_comm] using (le_max_right R₀ ((1+α)*r))

lemma bufferCurrentNode_exponential_step {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g A D : ℝ) (hα : Real.exp A=1+α) (hε : Real.exp (-D)=1-ε)
    (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (hr : ω ∈ root.active) (n : ℕ) :
    (bufferCurrentNode e f hef R₀ z₀ ε α g κ H hH root ω n).radius *
      Real.exp (if ω ∈ bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root n then A else -D) ≤
      (bufferCurrentNode e f hef R₀ z₀ ε α g κ H hH root ω (n+1)).radius := by
  rw [bufferCurrentNode_succ]
  have hb := bufferTreeSuccess_iff_decision e f hef R₀ z₀ ε α g κ H hH root ω hr n
  rw [hb]
  let N := bufferCurrentNode e f hef R₀ z₀ ε α g κ H hH root ω n
  have he := bufferNextRadius_exponential_step R₀ N.radius ε α A D hα hε
    (bufferNodeDecision e f z₀ ε α g H N ω).2
  convert he using 1
  · congr 2
    exact congrArg (fun h : Decidable ((bufferNodeDecision e f z₀ ε α g H N ω).2=true) =>
      @ite ℝ _ h A (-D)) (Subsingleton.elim _ _)
  · rfl

lemma bufferCurrentNode_log_growth {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    {R₀ α s : ℝ} (hR₀ : 0 < R₀) (hα : 0 < α) (hs : 0 < s)
    (z₀ g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (hroot : root.radius=R₀) (ω : Environment d) (hr : ω ∈ root.active)
    (W : ℝ)
    (hexcess : ∀ n : ℕ, s/4*(n:ℝ)-successes
      (bufferTreeSuccess e f hef R₀ z₀ (1-Real.exp (-(s*Real.log (1+α)/8))) α g κ H hH root) n ω ≤ W)
    (n : ℕ) :
    Real.log R₀+(s*Real.log (1+α)/8)*(n:ℝ)-W*(Real.log (1+α)+s*Real.log (1+α)/8) ≤
      Real.log (bufferCurrentNode e f hef R₀ z₀ (1-Real.exp (-(s*Real.log (1+α)/8))) α g κ H hH root ω n).radius := by
  let ε := 1-Real.exp (-(s*Real.log (1+α)/8))
  let R := fun n => (bufferCurrentNode e f hef R₀ z₀ ε α g κ H hH root ω n).radius
  have hp (n : ℕ) : 0 < R n := hR₀.trans_le
    (bufferNodeAt_radius e f hef R₀ z₀ ε α g κ H hH root hroot.ge _)
  have hc := buffer_contraction_choice hα hs
  have he := bufferCurrentNode_exponential_step e f hef R₀ z₀ ε α g
    (Real.log (1+α)) (s*Real.log (1+α)/8) hc.2.2.1 hc.2.2.2 κ H hH root ω hr
  have hA : 0 ≤ Real.log (1+α) := (Real.log_pos (by linarith)).le
  have hh := buffer_log_growth
    (bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root) ω R hp hA hs.le he hexcess n
  have hr0 : R 0=R₀ := hroot
  rw [hr0] at hh
  exact hh
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferExcess
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

theorem actual_buffer_excess_oai {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ (κ : ℝ≥0) (α s g R : ℝ), 0 < κ ∧ κ ≤ 1 ∧ (∀ᵐ ω ∂environmentLaw ν, ∀ y u, κ ≤ (ω y).1 u) ∧ 0 < α ∧ 0 < s ∧
      0 < g ∧ g ≤ 1 ∧ 1 ≤ R ∧
      ∀ (a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a),
      let ε := 1-Real.exp (-(s*Real.log (1+α)/8))
      let root := bufferRootNode e f hef R a x hx
      let B := bufferTreeSuccess e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
        (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root
      ∃ W : Environment d → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
        Integrable (fun ω => Real.exp (W ω)) (environmentLaw ν) ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ, s/4*(n:ℝ)-successes B n ω ≤ W ω) ∧
        (∫ ω, Real.exp (W ω) ∂environmentLaw ν) ≤ 1+(1-Real.exp (-s/4))⁻¹ ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ,
          Real.log R+(s*Real.log (1+α)/8)*(n:ℝ)-W ω*(Real.log (1+α)+s*Real.log (1+α)/8) ≤
          Real.log (bufferCurrentNode e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
            (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root ω n).radius) := by
  obtain ⟨κ,hκ,hκae⟩ := environment_uniform_elliptic ν hue
  have hκ1 : κ ≤ 1 := by
    obtain ⟨ω,hω⟩ := hκae.exists
    exact (hω 0 e).trans (row_entry_le_one (ω 0) e)
  obtain ⟨α,s,hα,hs,hdata⟩ := actual_buffer_chance_data ν hue e f hef htrans
  let ε := 1-Real.exp (-(s*Real.log (1+α)/8))
  have hε := buffer_contraction_choice hα hs
  obtain ⟨g,R₀,hg,hg1,hR₀,hgood⟩ := hdata ε hε.1
  let R := max R₀ 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have hgood' : BufferChanceData ν e f α s ε g R := fun r hr => hgood r ((le_max_left _ _).trans hr)
  refine ⟨κ,α,s,g,R,hκ,hκ1,hκae,hα,hs,hg,hg1,le_max_right _ _,?_⟩
  intro a x hx
  let root := bufferRootNode e f hef R a x hx
  let B := bufferTreeSuccess e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
    (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root
  have hb := bufferTreeSuccess_measurable e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
    (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root
  have hstep := bufferTree_real_success ν e f hef hR (signedCoordinate f (x.2-x.1)) ε α g s hs.le
    hκ hκ1 hκae hg hg1 hε.1.le hgood' root le_rfl (bufferRootNode_valid e f hef R a x hx κ) rfl
  obtain ⟨W,hW,hW0,hWi,hWe,hWb⟩ := adaptive_failure_excess (environmentLaw ν) B hb hs hstep
  refine ⟨W,hW,hW0,hWi,hWe,hWb,?_⟩
  filter_upwards [hWe] with ω hω
  intro n
  exact bufferCurrentNode_log_growth e f hef hR hα hs (signedCoordinate f (x.2-x.1)) g κ
    (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root rfl ω (Set.mem_univ _) (W ω) hω n
end DirectionalTransience

end

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.actual_buffer_excess_oai := @OAI.DirectionalTransience.actual_buffer_excess_oai
