-- Prove2me | solution 1 for OAI.DirectionalTransience.OperationalConstants.bad_stationary_array_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:00:11.853199+00:00
-- url     : https://prove2.me/submissions/85635d45-c60e-446b-a3b1-36a71a99a359

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Definitions.Def_OAIQ242Bal006
import Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_bad_array_finite_marks
import Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_bad_limit_averaged_survival
import Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_stationary_window_entropy

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightSlab
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_BadCrossingLaw
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma badCrossingEvent_pos {d : ℕ} (e : Direction d) (N : ℕ) (β D : ℝ)
    (P : Measure (Environment d)) (hN : 0<N)
    (hmass : (N:ℝ)^(-D) ≤ P.real (badCrossingEvent e N β)) :
    P (badCrossingEvent e N β) ≠ 0 := by
  have hr : 0<P.real (badCrossingEvent e N β) :=
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _).trans_le hmass
  exact ENNReal.toReal_pos_iff.mp hr |>.1.ne'

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayTopology
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

variable {H R : Type*}
  [TopologicalSpace H] [DiscreteTopology H] [Countable H]
  [TopologicalSpace R] [CompactSpace R] [T2Space R] [SecondCountableTopology R]

omit [DiscreteTopology H] [Countable H] [CompactSpace R] [T2Space R]
  [SecondCountableTopology R] in
lemma shift_continuous : Continuous (shift : EpisodeArray H R → EpisodeArray H R) := by
  unfold shift
  fun_prop

end DirectionalTransience.StationaryCompact

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AllIndexMarks
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.annealedLaw_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.environmentLaw_probability _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.initialLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.quenchedKernel_markov _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.stateTrajectory_markov _root_.OAI.DirectionalTransience.state_measurableEq _root_.OAI.DirectionalTransience.state_measurableSingleton _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

local instance instBorelSpaceENat_solutions : BorelSpace ℕ∞ := ⟨borel_eq_top_of_countable.symm⟩

attribute [local instance] OAI.DirectionalTransience.instMeasurableSpaceOnePointSubtypeLatticeMemAddSubgroupHorizontalSpace
lemma stationary_mark_identDistrib {d : ℕ} (e : Direction d)
    (μ : Measure (ActualEpisodeArray e))
    (hstat : MeasurePreserving StationaryCompact.shift μ μ) (i : ℤ) :
    IdentDistrib (fun Y : ActualEpisodeArray e => Y.1 i) (fun Y => Y.1 0) μ μ := by
  have hm (i : ℤ) : Measurable (fun Y : ActualEpisodeArray e => Y.1 i) := by fun_prop
  have hs (i : ℤ) : IdentDistrib (fun Y : ActualEpisodeArray e => Y.1 (i+1))
      (fun Y => Y.1 i) μ μ := by
    refine ⟨(hm (i+1)).aemeasurable,(hm i).aemeasurable,?_⟩
    change Measure.map ((fun Y : ActualEpisodeArray e => Y.1 i) ∘ StationaryCompact.shift) μ = _
    rw [←Measure.map_map (hm i) hstat.measurable,hstat.map_eq]
  induction i using Int.induction_on with
  | zero => exact IdentDistrib.refl (hm 0).aemeasurable
  | succ n ih => exact (hs n).trans ih
  | pred n ih =>
    have ht := (hs (-(n:ℤ)-1)).symm
    have hi : -(n:ℤ)-1+1=-(n:ℤ) := by omega
    rw [hi] at ht
    exact ht.trans ih

lemma stationary_marks_ae_all {d : ℕ} (e : Direction d)
    (μ : Measure (ActualEpisodeArray e))
    (hstat : MeasurePreserving StationaryCompact.shift μ μ)
    (p : StationaryCompact.MarkSpace → Prop) (hp : MeasurableSet {m | p m})
    (h0 : ∀ᵐ Y ∂μ, p (Y.1 0)) : ∀ᵐ Y ∂μ, ∀ i, p (Y.1 i) := by
  apply ae_all_iff.mpr
  intro i
  exact (stationary_mark_identDistrib e μ hstat i).symm.ae_snd hp h0

lemma stationary_finite_marks_all {d : ℕ} (e : Direction d)
    (μ : Measure (ActualEpisodeArray e))
    (hstat : MeasurePreserving StationaryCompact.shift μ μ)
    (h0 : ∀ᵐ Y ∂μ, 0<(Y.1 0).1 ∧ (Y.1 0).1<⊤ ∧ (Y.1 0).2.1<⊤ ∧ (Y.1 0).2.2<∞) :
    ∀ᵐ Y ∂μ, ∀ i, 0<(Y.1 i).1 ∧ (Y.1 i).1<⊤ ∧ (Y.1 i).2.1<⊤ ∧ (Y.1 i).2.2<∞ := by
  apply stationary_marks_ae_all e μ hstat
    (fun m : StationaryCompact.MarkSpace => 0 < m.1 ∧ m.1 < ⊤ ∧ m.2.1 < ⊤ ∧ m.2.2 < ∞) _ h0
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
        (measurableSet_lt (measurable_snd.comp measurable_snd) measurable_const)))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_CoordinateKernelComp
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GlobalProfile
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma globalEndpointProfile_mass {d : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d) :
    crossingQuenched (realPosition (step e)) 0 H ω • globalEndpointProfile e H ω=
      variableHitKernel (realPosition (step e)) H (ω,0) := by
  have he : crossingQuenched (realPosition (step e)) 0 H ω=
      variableHitKernel (realPosition (step e)) H (ω,0) Set.univ := by
    simpa only [variableHitKernel,Kernel.coe_mk] using crossingQuenched_eq_hitKernel (realPosition (step e)) 0 H ω
  rw [he]
  exact normalizeOr_mass _ _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMap
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma globalHorizontalCoordinate_joint_measurable {d : ℕ} (e : Direction d) :
    Measurable (fun p : (Environment d×ℕ)×HorizontalSpace e =>
      globalHorizontalCoordinate e p.1.2 p.1.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro z
  apply Measurable.subtype_mk
  exact (((Measure.measurable_coe (measurableSet_singleton z)).comp
    (globalHorizontalProfile_joint_measurable e)).ennreal_toReal)

lemma episodeCost_measurable {d : ℕ} (e : Direction d) (t : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (i : ℤ) : Measurable (fun ω => episodeCost e t ω i) := by
  have hm : Measurable (fun p : Environment d×ℕ => crossingQuenched (realPosition (step e)) 0 p.2 p.1) := by
    apply measurable_from_prod_countable_left
    intro n
    change Measurable (crossingQuenched (realPosition (step e)) 0 (n : ℝ))
    exact measurable_crossingQuenched _ _ _
  exact (((hm.comp (measurable_id.prodMk (ht i))).ennreal_toReal.log).sub
    ((hm.comp (measurable_id.prodMk (ht (i+1)))).ennreal_toReal.log)).ennreal_ofReal

lemma episodeSplicedRow_measurable {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (i : ℤ) (m a l : ℕ) (z : HorizontalSpace e) :
    Measurable (fun X : EpisodeInput e => episodeSplicedRow e t X i m a l z) := by
  have hw : Measurable (fun X : EpisodeInput e => X.1.1) := measurable_fst.comp measurable_fst
  have hU : Measurable (fun X : EpisodeInput e => X.1.2 (i,a)) :=
    (measurable_pi_apply (i,a)).comp (measurable_snd.comp measurable_fst)
  have hx : Measurable (fun X : EpisodeInput e => horizontalLift e (t X.1.1 i+l) (X.1.2 (i,a)+z)) :=
    (measurable_of_countable (fun p : ℕ×HorizontalSpace e => horizontalLift e (p.1+l) (p.2+z))).comp
      (((ht i).comp hw).prodMk hU)
  unfold episodeSplicedRow
  apply Measurable.ite (measurableSet_lt measurable_const (((ht (i+m)).comp hw).sub ((ht i).comp hw)))
  · exact measurable_current_row.comp (hw.prodMk hx)
  · have hev : Measurable (fun p : (((ℕ×HorizontalSpace e) → Row d)×(ℕ×HorizontalSpace e)) => p.1 p.2) :=
      measurable_from_prod_countable_left (fun q => measurable_pi_apply q)
    exact hev.comp ((((measurable_pi_apply (i,m)).comp measurable_snd).prodMk
      (measurable_const.prodMk (hU.add_const z))))

lemma actualArrayCoordinate_measurable {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (j : ℤ) (p : ℤ×ℕ) (z : HorizontalSpace e) :
    Measurable (fun X : EpisodeInput e => globalHorizontalCoordinate e (t X.1.1 j) X.1.1 (X.1.2 p+z)) := by
  have hw : Measurable (fun X : EpisodeInput e => X.1.1) := measurable_fst.comp measurable_fst
  have hU : Measurable (fun X : EpisodeInput e => X.1.2 p) :=
    (measurable_pi_apply p).comp (measurable_snd.comp measurable_fst)
  have ha : Measurable (fun X : EpisodeInput e => ((X.1.1,t X.1.1 j),X.1.2 p+z)) :=
    (hw.prodMk ((ht j).comp hw)).prodMk (hU.add_const z)
  have hm := (globalHorizontalCoordinate_joint_measurable e).comp ha
  simpa only [Function.comp_def] using hm

lemma actualArrayMap_measurable {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) : Measurable (actualArrayMap e t J) := by
  have hw : Measurable (fun X : EpisodeInput e => X.1.1) := measurable_fst.comp measurable_fst
  have hU (p : ℤ×ℕ) : Measurable (fun X : EpisodeInput e => X.1.2 p) :=
    (measurable_pi_apply p).comp (measurable_snd.comp measurable_fst)
  refine Measurable.prodMk (Measurable.of_eval fun i => ?_)
    (Measurable.prodMk (Measurable.of_eval fun p => ?_)
      (Measurable.prodMk (Measurable.of_eval fun p => ?_) (Measurable.of_eval fun p => ?_)))
  · have hc : Measurable (fun n : ℕ => (n : ℕ∞)) := measurable_of_countable _
    exact (hc.comp (((ht (i+1)).comp hw).sub ((ht i).comp hw))).prodMk
      ((hc.comp ((hJ i).comp hw)).prodMk ((episodeCost_measurable e t ht i).comp hw))
  · exact OnePoint.continuous_coe.measurable.comp ((hU p.2).sub (hU p.1))
  · exact actualArrayCoordinate_measurable e t ht _ _ _
  · exact episodeSplicedRow_measurable e t ht _ _ _ _ _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SamplingLaw
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma restrict_compProd_fst {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (Q : Measure Ω) [SFinite Q] (K : Kernel Ω A) [IsSFiniteKernel K]
    (s : Set Ω) (hs : MeasurableSet s) :
    (Q.compProd K).restrict (Prod.fst ⁻¹' s)=(Q.restrict s).compProd K := by
  ext B hB
  rw [Measure.restrict_apply hB,Measure.compProd_apply (hB.inter (hs.preimage measurable_fst)),
    Measure.compProd_apply hB,←lintegral_indicator hs]
  apply lintegral_congr
  intro ω
  by_cases hω : ω∈s
  · have he : Prod.mk ω ⁻¹' Prod.fst ⁻¹' s = (Set.univ : Set A) := by
      ext a
      simp [hω]
    simp [Set.indicator_of_mem hω,he]
  · have he : Prod.mk ω ⁻¹' Prod.fst ⁻¹' s = (∅ : Set A) := by
      ext a
      simp [hω]
    simp [Set.indicator_of_notMem hω,he]

lemma episodeInputLaw_restrict {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (s : Set (Environment d)) (hs : MeasurableSet s) :
    (episodeInputLaw e ν Q t ht).restrict {X | X.1.1∈s}=
      episodeInputLaw e ν (Q.restrict s) t ht := by
  unfold episodeInputLaw
  rw [←restrict_compProd_fst Q (globalEpisodeAnchors e t ht) s hs,
    Measure.restrict_prod_eq_prod_univ]
  congr 1
  ext X
  simp

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryCompact
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace BoundedContinuousFunction
open scoped Topology
namespace DirectionalTransience.StationaryCompact

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [MetrizableSpace Ω] [SecondCountableTopology Ω]

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω] in
theorem invariant_of_weak_limit (T : Ω → Ω) (hT : Continuous T)
    (μs : ℕ → ProbabilityMeasure Ω) (μ : ProbabilityMeasure Ω)
    (hlim : Tendsto μs atTop (𝓝 μ))
    (hdefect : ∀ F : Ω →ᵇ ℝ,
      Tendsto (fun n => (∫ x, F (T x) ∂(μs n : Measure Ω)) -
        ∫ x, F x ∂(μs n : Measure Ω)) atTop (𝓝 0)) :
    MeasurePreserving T (μ : Measure Ω) (μ : Measure Ω) := by
  refine ⟨hT.measurable, ?_⟩
  let ν := μ.map (f := T) (by first | exact hT.measurable.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have heq : ν.toFiniteMeasure = μ.toFiniteMeasure := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro F
    have h₁ := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hlim hT)) F
    have h₂ := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) F
    have h₃ : Tendsto (fun n =>
        (∫ x, F (T x) ∂(μs n : Measure Ω)) - ∫ x, F x ∂(μs n : Measure Ω))
        atTop (𝓝 ((∫ x, F x ∂(ν : Measure Ω)) - ∫ x, F x ∂(μ : Measure Ω))) := by
      convert h₁.sub h₂ using 1
      all_goals try with_reducible_and_instances rfl
      ext n
      rw [ProbabilityMeasure.toMeasure_map,
        integral_map hT.measurable.aemeasurable F.continuous.aestronglyMeasurable]
    have hz := tendsto_nhds_unique h₃ (hdefect F)
    exact sub_eq_zero.mp hz
  exact congrArg FiniteMeasure.toMeasure heq

end DirectionalTransience.StationaryCompact

end

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace BoundedContinuousFunction
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

variable {X Y : Type*} [MeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

lemma sum_indicator_range (N M : ℕ) (hM : M ≤ N) (G : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, (if i < M then G i else 0)) = ∑ i ∈ Finset.range M, G i := by
  have he : (Finset.range N).filter (fun i => i < M) = Finset.range M := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [←Finset.sum_filter, he]

lemma episodeOccupationRaw_integral (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (hA : Measurable A) (M : X → ℕ) (hM : Measurable M)
    (hMN : ∀ x, M x ≤ N) (T : Y → Y) (hT : Measurable T)
    (F : Y →ᵇ ℝ) :
    (∫ y, F y ∂episodeOccupationRaw N μ A M T) =
      ∫ x, ∑ i ∈ Finset.range (M x), F (T^[i] (A x)) ∂μ := by
  have hi (i : ℕ) : Integrable (fun x => F (T^[i] (A x))) μ := by
    apply (integrable_const ‖F‖).mono' ((F.continuous.measurable.comp
      ((hT.iterate i).comp hA)).aestronglyMeasurable)
    exact Eventually.of_forall fun x => F.norm_coe_le_norm _
  have hm (i : ℕ) : MeasurableSet {x | i < M x} := measurableSet_lt measurable_const hM
  rw [episodeOccupationRaw]
  rw [integral_finsetSum_measure (fun i _ =>
    BoundedContinuousFunction.integrable ((μ.restrict {x | i < M x}).map
      (fun x => T^[i] (A x))) F)]
  calc (∑ i ∈ Finset.range N, ∫ y, F y ∂(μ.restrict {x | i < M x}).map
        (fun x => T^[i] (A x)))
      = ∑ i ∈ Finset.range N, ∫ x,
          Set.indicator {x | i < M x} (fun x => F (T^[i] (A x))) x ∂μ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_indicator (hm i)]
          exact integral_map ((hT.iterate i).comp hA).aemeasurable
            F.continuous.aestronglyMeasurable
    _ = ∫ x, ∑ i ∈ Finset.range N,
          Set.indicator {x | i < M x} (fun x => F (T^[i] (A x))) x ∂μ :=
          (integral_finsetSum _ (fun i _ => (hi i).indicator (hm i))).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [Set.indicator_apply,Set.mem_ofPred_eq]
        exact sum_indicator_range N (M x) (hMN x) _

lemma episodeOccupationRaw_mass (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (hA : Measurable A) (M : X → ℕ) (hM : Measurable M)
    (hMN : ∀ x, M x ≤ N) (T : Y → Y) (hT : Measurable T) :
    (episodeOccupationRaw N μ A M T).real Set.univ = ∫ x, (M x : ℝ) ∂μ := by
  simpa using episodeOccupationRaw_integral N μ A hA M hM hMN T hT
    (BoundedContinuousFunction.const Y (1:ℝ))

end DirectionalTransience.StationaryCompact

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OccupationSampling
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma actualOccupationRaw_integral {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M) (F : C(ActualEpisodeArray e,ℝ)) :
    (∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M)=
      ∑ i∈Finset.range N, ∫ X, F (StationaryCompact.shift^[i] (actualArrayMap e t J X))
        ∂episodeInputLaw e ν (Q.restrict {ω | i<M ω}) t ht := by
  unfold actualOccupationRaw StationaryCompact.episodeOccupationRaw
  rw [integral_finsetSum_measure (fun i _ =>
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply Finset.sum_congr rfl
  intro i _
  have hm : Measurable (fun X : EpisodeInput e => StationaryCompact.shift^[i] (actualArrayMap e t J X)) :=
    (StationaryCompact.shift_continuous.measurable.iterate i).comp (actualArrayMap_measurable e t J ht hJ)
  rw [integral_map hm.aemeasurable F.continuous.aestronglyMeasurable]
  have hr : (episodeInputLaw e ν Q t ht).restrict {X | i<M X.1.1}=
      episodeInputLaw e ν (Q.restrict {ω | i<M ω}) t ht :=
    episodeInputLaw_restrict e ν Q t ht {ω | i<M ω} (measurableSet_lt measurable_const hM)
  change (∫ X, F (StationaryCompact.shift^[i] (actualArrayMap e t J X))
    ∂(episodeInputLaw e ν Q t ht).restrict {X | i<M X.1.1})=_
  rw [hr]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical Topology
namespace DirectionalTransience

lemma actualOccupation_integral {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (F : ActualEpisodeArray e → ℝ) :
    (∫ Y, F Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)))=
      ((actualOccupationRaw e ν Q t J ht N M).real Set.univ)⁻¹ *
        ∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let ρ : FiniteMeasure (ActualEpisodeArray e) := ⟨actualOccupationRaw e ν Q t J ht N M,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hn : ρ≠0 := by
    intro hz
    have hh : (actualOccupationRaw e ν Q t J ht N M).real Set.univ=0 := by
      change (ρ : Measure (ActualEpisodeArray e)).real Set.univ=0
      rw [hz]
      simp
    linarith
  change (∫ Y, F Y ∂(ρ.normalize : Measure (ActualEpisodeArray e)))=_
  rw [←ρ.average_eq_integral_normalize hn,average,integral_smul_measure]
  simp only [ENNReal.toReal_inv,smul_eq_mul]
  rfl

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayClosed
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma closed_support_weak_limit {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [HasOuterApproxClosed X]
    (μ : ℕ → ProbabilityMeasure X) (ρ : ProbabilityMeasure X)
    (hlim : Tendsto μ atTop (𝓝 ρ)) (s : Set X) (hs : IsClosed s)
    (hμ : ∀ n, ∀ᵐ x ∂(μ n : Measure X), x∈s) :
    ∀ᵐ x ∂(ρ : Measure X), x∈s := by
  have he (n : ℕ) : (μ n : Measure X) s=1 :=
    (mem_ae_iff_prob_eq_one hs.measurableSet).mp (hμ n)
  have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hs
  simp only [he,limsup_const] at hle
  exact (mem_ae_iff_prob_eq_one hs.measurableSet).mpr
    (le_antisymm prob_le_one hle)

lemma actualOccupation_ae_of_invariant {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (s : Set (ActualEpisodeArray e)) (hs : MeasurableSet s)
    (ha : ∀ X, actualArrayMap e t J X∈s)
    (hshift : ∀ Y∈s, StationaryCompact.shift Y∈s) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)), Y∈s := by
  have hiter (i : ℕ) (X : EpisodeInput e) :
      StationaryCompact.shift^[i] (actualArrayMap e t J X)∈s := by
    induction i with
    | zero => exact ha X
    | succ i hi =>
      rw [Function.iterate_succ_apply']
      exact hshift _ hi
  have hraw : ∀ᵐ Y ∂actualOccupationRaw e ν Q t J ht N M, Y∈s := by
    unfold actualOccupationRaw StationaryCompact.episodeOccupationRaw
    rw [ae_finsetSum_measure_iff]
    intro i _
    apply (ae_map_iff ((StationaryCompact.shift_continuous.measurable.iterate i).comp
      (actualArrayMap_measurable e t J ht hJ)).aemeasurable hs).mpr
    exact Filter.Eventually.of_forall (hiter i)
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let ρ : FiniteMeasure (ActualEpisodeArray e) := ⟨actualOccupationRaw e ν Q t J ht N M,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hn : ρ≠0 := by
    intro hz
    have hh : (actualOccupationRaw e ν Q t J ht N M).real Set.univ=0 := by
      change (ρ : Measure (ActualEpisodeArray e)).real Set.univ=0
      rw [hz]
      simp
    linarith
  change ∀ᵐ Y ∂(ρ.normalize : Measure (ActualEpisodeArray e)), Y∈s
  rw [ρ.toMeasure_normalize_eq_of_nonzero hn]
  exact Measure.ae_smul_measure hraw _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AllOffsetConsistency
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma arrayOffsetsConsistent_closed {d : ℕ} (e : Direction d) :
    IsClosed {Y : ActualEpisodeArray e | ArrayOffsetsConsistent e Y} := by
  unfold ArrayOffsetsConsistent
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun u => ReferenceClasses.consistent_closed.preimage
    (by unfold selectedOffsets; fun_prop)

lemma actual_arrayOffsetsConsistent {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) :
    ArrayOffsetsConsistent e (actualArrayMap e t J X) := by
  intro u
  constructor
  · intro a
    simp [selectedOffsets,actualArrayMap]
  · intro a b z h
    have he : X.1.2 (u b)-X.1.2 (u a)=z := OnePoint.coe_injective h
    change ((X.1.2 (u a)-X.1.2 (u b) : HorizontalSpace e):OnePoint (HorizontalSpace e))=
      ((-z : HorizontalSpace e):OnePoint (HorizontalSpace e))
    rw [←he,neg_sub]
  · intro a b c z w h₁ h₂
    have h₁ : X.1.2 (u b)-X.1.2 (u a)=z := OnePoint.coe_injective h₁
    have h₂ : X.1.2 (u c)-X.1.2 (u b)=w := OnePoint.coe_injective h₂
    change ((X.1.2 (u c)-X.1.2 (u a) : HorizontalSpace e):OnePoint (HorizontalSpace e))=
      ((z+w : HorizontalSpace e):OnePoint (HorizontalSpace e))
    rw [←h₁,←h₂]
    congr 1
    abel

lemma arrayOffsetsConsistent_shift {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) : ArrayOffsetsConsistent e (StationaryCompact.shift Y) := by
  intro u
  exact h (fun n => ((u n).1+1,(u n).2))

lemma actualOccupation_offsetsConsistent {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)),
      ArrayOffsetsConsistent e Y :=
  actualOccupation_ae_of_invariant e ν Q t J ht hJ N M hpos _
    (arrayOffsetsConsistent_closed e).measurableSet (actual_arrayOffsetsConsistent e t J)
    (arrayOffsetsConsistent_shift e)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeInjection
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma episodeBoundary_progress {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) (i : ℕ) :
    min i N ≤ episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    rw [episodeBoundary]
    split
    · have hh := episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N
        (episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i) ω
      omega
    · omega

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeGlobalRetention
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma coordinate_survival_lower {d : ℕ} (e : Direction d) (ω : Environment d)
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).1 e) (H : ℕ) :
    (κ : ℝ≥0∞)^H ≤ crossingQuenched (realPosition (step e)) 0 H ω := by
  induction H with
  | zero => simp [crossingQuenched_zero]
  | succ H ih =>
    have hh := crossingQuenched_lower_step (realPosition (step e)) ω 0 e hκ (H:=H) (by positivity)
    rw [signed_direction_unit] at hh
    simpa only [Nat.cast_add,Nat.cast_one,pow_succ',Nat.succ_eq_add_one] using
      (mul_le_mul_right ih (κ : ℝ≥0∞)).trans hh

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeRecordedAtlas
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
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

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeCounterChain
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

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

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeNumber
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeBoundary_mono {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ) (ω : Environment d) :
    Monotone (episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [episodeBoundary]
  split
  · exact (episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N _ ω).le
  · exact le_refl _

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N

lemma number_le (ω : Environment d) (n : ℕ) : M ω n ≤ n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => rw [number]; split <;> omega

lemma number_measurable (n : ℕ) : Measurable (fun ω => M ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ih.add (Measurable.ite (measurableSet_lt
      (episodeBoundary_measurable (k:=k) e f hef r fexp g χ b sfloor hR N n) measurable_const)
      measurable_const measurable_const)

lemma number_integrable (Q : Measure (Environment d)) [IsFiniteMeasure Q] (n : ℕ) :
    Integrable (fun ω => (M ω n:ℝ)) Q := by
  apply Entropy.integrable_of_bounded ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
    (number_measurable (k:=k) e f hef r fexp g χ b sfloor hR N n))
  refine ⟨n,fun ω => ?_⟩
  dsimp only [Function.comp_def]
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast number_le (k:=k) e f hef r fexp g χ b sfloor hR N ω n

end EpisodeChainLedger
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N

lemma number_mono (ω : Environment d) : Monotone (M ω) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [number]
  exact Nat.le_add_right _ _

lemma number_active (ω : Environment d) (i : ℕ) (ha : T ω i<N) : M ω i=i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hprev : T ω i<N := lt_of_le_of_lt
      (episodeBoundary_mono (k:=k) e f hef r fexp g χ b sfloor hR N ω (Nat.le_succ i)) ha
    rw [number,ite_eq_left hprev,ih hprev]

lemma number_stopped (ω : Environment d) (i : ℕ) (hi : N ≤ T ω i) (j : ℕ) : M ω (i+j)=M ω i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hn : ¬T ω (i+j)<N := not_lt.mpr (hi.trans
      (episodeBoundary_mono (k:=k) e f hef r fexp g χ b sfloor hR N ω (Nat.le_add_right _ _)))
    rw [Nat.add_succ,number,ite_eq_right hn,add_zero,ih]

lemma active_iff_lt_number (ω : Environment d) (i : ℕ) : T ω i<N ↔ i<M ω N := by
  constructor
  · intro ha
    have hi := episodeBoundary_progress (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    have hin : i<N := by omega
    have hm : M ω (i+1)=i+1 := by rw [number,ite_eq_left ha,number_active (k:=k) e f hef r fexp g χ b sfloor hR N ω i ha]
    have hh := number_mono (k:=k) e f hef r fexp g χ b sfloor hR N ω (Nat.succ_le_of_lt hin)
    change M ω (i+1) ≤ M ω N at hh
    rw [hm] at hh
    exact Nat.lt_of_succ_le hh
  · intro hm
    by_contra ha
    have hi : i<N := lt_of_lt_of_le hm (number_le (k:=k) e f hef r fexp g χ b sfloor hR N ω N)
    have hh := number_stopped (k:=k) e f hef r fexp g χ b sfloor hR N ω i (Nat.le_of_not_lt ha) (N-i)
    rw [Nat.add_sub_of_le hi.le] at hh
    have hu := number_le (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    omega

lemma number_positive (ω : Environment d) (hN : 0<N) : 0<M ω N :=
  (active_iff_lt_number (k:=k) e f hef r fexp g χ b sfloor hR N ω 0).mp hN

end DirectionalTransience.EpisodeChainLedger

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeDropLedger
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N

lemma stepMark_sub (ω : Environment d) (i : ℕ) : j ω i=J ω (i+1)-J ω i := by
  rw [steps,Nat.add_sub_cancel_left]
  rfl

lemma stepMark_measurable (i : ℕ) : Measurable (fun ω => j ω i) := by
  have hi := (measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N i).fst
  have hj := (measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N (i+1)).fst
  have h : Measurable (fun ω => J ω (i+1)-J ω i) := hj.sub hi
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  exact funext (fun ω => stepMark_sub (k:=k) e f hef r fexp g χ b sfloor hR N ω i)

end DirectionalTransience.EpisodeChainLedger

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_BadCrossingEpisodes
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma episodeInputLaw_environment {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    (episodeInputLaw e ν Q t ht).map (fun X => X.1.1)=Q := by
  change Measure.map (Prod.fst ∘ Prod.fst) _=Q
  rw [←Measure.map_map measurable_fst measurable_fst]
  unfold episodeInputLaw
  rw [Measure.map_fst_prod,measure_univ,one_smul]
  exact Measure.fst_compProd Q (globalEpisodeAnchors e t ht)

lemma episodeInputLaw_env_integral {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (F : Environment d → ℝ) (hF : Measurable F) :
    (∫ X, F X.1.1 ∂episodeInputLaw e ν Q t ht)=(∫ ω, F ω ∂Q) := by
  have hh := integral_map ((measurable_fst.comp measurable_fst).aemeasurable)
    hF.aestronglyMeasurable (μ:=episodeInputLaw e ν Q t ht)
  change (∫ y, F y ∂Measure.map (fun X => X.1.1) (episodeInputLaw e ν Q t ht)) = _ at hh
  rw [episodeInputLaw_environment] at hh
  exact hh.symm

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "t" => arrayTime (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "s" => arrayStages (k:=k) e f hef r fexp g χ b sfloor hR N

lemma arrayStages_measurable (i : ℤ) : Measurable (fun ω => s ω i) := by
  unfold arrayStages
  split
  · exact measurable_const
  · exact stepMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i.toNat

lemma operational_raw_mass (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q] :
    (actualOccupationRaw e ν Q t s (arrayTime_measurable (k:=k) e f hef r fexp g χ b sfloor hR N) N (fun ω => M ω N)).real Set.univ=
      ∫ ω, (M ω N:ℝ) ∂Q := by
  unfold actualOccupationRaw
  have hM : Measurable (fun X : EpisodeInput e => M X.1.1 N) :=
    (number_measurable (k:=k) e f hef r fexp g χ b sfloor hR N N).comp (measurable_fst.comp measurable_fst)
  rw [StationaryCompact.episodeOccupationRaw_mass N _ _
    (actualArrayMap_measurable e t s (arrayTime_measurable (k:=k) e f hef r fexp g χ b sfloor hR N)
      (arrayStages_measurable (k:=k) e f hef r fexp g χ b sfloor hR N)) _
    hM
    (fun X => number_le (k:=k) e f hef r fexp g χ b sfloor hR N X.1.1 N) _ StationaryCompact.shift_continuous.measurable]
  exact episodeInputLaw_env_integral e ν Q t _ _
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (number_measurable (k:=k) e f hef r fexp g χ b sfloor hR N N))

lemma operational_mass_positive (Q : Measure (Environment d)) [IsProbabilityMeasure Q] (hN : 0<N) :
    0<∫ ω, (M ω N:ℝ) ∂Q := by
  have hh := integral_mono (integrable_const (1:ℝ))
    (number_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q N) (fun ω => by
      change (1:ℝ) ≤ (M ω N:ℝ)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (number_positive (k:=k) e f hef r fexp g χ b sfloor hR N ω hN)))
  simp only [integral_const,probReal_univ,one_smul] at hh
  exact lt_of_lt_of_le zero_lt_one hh

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BadOccupationLimit
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

omit [IsProbabilityMeasure ν] in
lemma paddedStages_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (i : ℤ) : Measurable (fun ω => C.paddedStages hef N ω i) :=
  EpisodeChainLedger.arrayStages_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i

omit [IsProbabilityMeasure ν] in
lemma activeCount_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) : Measurable (C.activeCount hef N) :=
  EpisodeChainLedger.number_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N N

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GlobalContinuation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma globalEndpointProfile_supported {d : ℕ} (e : Direction d) (k : ℕ) (ω : Environment d) :
    ∀ᵐ x ∂globalEndpointProfile e k ω, signedHeight e x=k := by
  apply normalizeOr_ae
  · simpa [variableHitKernel,signedHeight] using
      coordinate_hitKernel_supported e (0:Lattice d) k ω
  · apply (ae_dirac_iff (Set.to_countable _).measurableSet).mpr
    have hh := signedHeight_zsmul_step e (k:ℤ)
    simpa only [natCast_zsmul] using hh

lemma globalHorizontalProfile_lift {d : ℕ} (e : Direction d) (k : ℕ) (ω : Environment d) :
    (globalHorizontalProfile e k ω).map (horizontalLift e k)=globalEndpointProfile e k ω := by
  rw [globalHorizontalProfile,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  calc
    _ = (globalEndpointProfile e k ω).map id := by
      apply Measure.map_congr
      filter_upwards [globalEndpointProfile_supported e k ω] with x hx
      dsimp only [Function.comp_def,id_eq]
      rw [←hx,horizontalLift_projection]
    _ = _ := Measure.map_id

lemma globalEndpointProfile_continuation {d : ℕ} (e : Direction d) (k m : ℕ) (ω : Environment d)
    (hk : crossingQuenched (realPosition (step e)) 0 k ω≠0) (U : Set (Lattice d)) :
    (∫⁻ x, variableHitKernel (realPosition (step e)) m (ω,x) U ∂globalEndpointProfile e k ω) ≤
      (crossingQuenched (realPosition (step e)) 0 (k+m) ω /
        crossingQuenched (realPosition (step e)) 0 k ω)*globalEndpointProfile e (k+m) ω U := by
  have ha : crossingQuenched (realPosition (step e)) 0 k ω≠⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  apply (ENNReal.mul_le_mul_iff_right hk ha).mp
  rw [←mul_assoc,ENNReal.mul_div_cancel hk ha]
  have hh := coordinate_raw_kernel_comp_le e k m ω 0 U
  simp only [←Nat.cast_add] at hh ⊢
  change (∫⁻ x, variableHitKernel (realPosition (step e)) m (ω,x) U
    ∂variableHitKernel (realPosition (step e)) k (ω,0)) ≤
      variableHitKernel (realPosition (step e)) (k+m) (ω,0) U at hh
  rw [←globalEndpointProfile_mass e k ω,lintegral_smul_measure,
    ←globalEndpointProfile_mass e (k+m) ω,Measure.smul_apply,smul_eq_mul] at hh
  exact hh

lemma globalHorizontalProfile_continuation {d : ℕ} (e : Direction d) (k m : ℕ) (ω : Environment d)
    (hk : crossingQuenched (realPosition (step e)) 0 k ω≠0) (U : Set (HorizontalSpace e)) :
    (∫⁻ z, variableHitKernel (realPosition (step e)) m (ω,horizontalLift e k z)
      (horizontalProjection e ⁻¹' U) ∂globalHorizontalProfile e k ω) ≤
      (crossingQuenched (realPosition (step e)) 0 (k+m) ω /
        crossingQuenched (realPosition (step e)) 0 k ω)*globalHorizontalProfile e (k+m) ω U := by
  have hh := globalEndpointProfile_continuation e k m ω hk (horizontalProjection e ⁻¹' U)
  rw [←globalHorizontalProfile_lift e k ω,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)] at hh
  simpa only [globalHorizontalProfile,Measure.map_apply (measurable_of_countable _) (Set.to_countable U).measurableSet] using hh

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_KernelTranslation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma hitKernel_translation {d : ℕ} (ω : Environment d) (z x : Lattice d)
    (S T U : Set (Lattice d)) :
    hitKernel ((fun y => z+y) ⁻¹' S) ((fun y => z+y) ⁻¹' T) ((fun y => ω (z+y)),x) U =
      hitKernel S T (ω,z+x) ((fun y => y-z) ⁻¹' U) := by
  simp only [hitKernel_apply]
  apply tsum_congr
  intro n
  rw [←quenched_translation ω z x,
    Measure.map_apply (by fun_prop) (measurableSet_hitAt _ _ _)]
  congr 1
  ext X
  simp only [Set.mem_preimage,HitAt,Set.mem_ofPred_eq,Set.mem_inter_iff]
  simp only [add_sub_cancel]

lemma strip_translation {d : ℕ} (ℓ : Vector d) (z x : Lattice d) (H : ℝ) :
    (fun y => z+y) ⁻¹' Strip ℓ (z+x) H=Strip ℓ x H := by
  ext y
  simp only [Set.mem_preimage,Strip,Set.mem_ofPred_eq,dot_realPosition_add]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

lemma upper_translation {d : ℕ} (ℓ : Vector d) (z x : Lattice d) (H : ℝ) :
    (fun y => z+y) ⁻¹' Upper ℓ (z+x) H=Upper ℓ x H := by
  ext y
  simp only [Set.mem_preimage,Upper,Set.mem_ofPred_eq,dot_realPosition_add]
  constructor <;> intro h <;> linarith

lemma variableHitKernel_translation {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (z x : Lattice d) (U : Set (Lattice d)) :
    variableHitKernel ℓ H ((fun y => ω (z+y)),x) U =
      variableHitKernel ℓ H (ω,z+x) ((fun y => y-z) ⁻¹' U) := by
  simpa only [variableHitKernel,Kernel.coe_mk,strip_translation,upper_translation] using
    hitKernel_translation ω z x (Strip ℓ (z+x) H) (Upper ℓ (z+x) H) U

lemma horizontalProjection_sub {d : ℕ} (e : Direction d) (x y : Lattice d) :
    horizontalProjection e (x-y)=horizontalProjection e x-horizontalProjection e y := by
  apply Subtype.ext
  funext j
  by_cases hj : j=e.1
  · subst j
    simp [horizontalProjection]
  · simp [horizontalProjection,Function.update_of_ne hj]

lemma horizontalLift_add {d : ℕ} (e : Direction d) (a b : ℤ) (x y : HorizontalSpace e) :
    horizontalLift e a x+horizontalLift e b y=horizontalLift e (a+b) (x+y) := by
  simp only [horizontalLift,AddSubgroup.coe_add,add_zsmul]
  abel

lemma episodeSpliced_kernel {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (X : EpisodeInput e) (i : ℤ) (m a : ℕ)
    (z : HorizontalSpace e) (A : Set (HorizontalSpace e)) :
    upperHorizontalKernel e (t X.1.1 (i+m)-t X.1.1 i)
      (fun p => episodeSplicedRow e t X i m a p.1 p.2) z A =
    variableHitKernel (realPosition (step e)) (t X.1.1 (i+m)-t X.1.1 i)
      (X.1.1,horizontalLift e (t X.1.1 i) (X.1.2 (i,a)+z))
      {y | horizontalProjection e y-X.1.2 (i,a)∈A} := by
  let b := horizontalLift e (t X.1.1 i) (X.1.2 (i,a))
  let H := t X.1.1 (i+m)-t X.1.1 i
  have he : hitKernel (Strip (realPosition (step e)) (horizontalLift e 0 z) H)
      (Upper (realPosition (step e)) (horizontalLift e 0 z) H)
      (upperEnvironment e (fun p => episodeSplicedRow e t X i m a p.1 p.2),horizontalLift e 0 z)=
    hitKernel (Strip (realPosition (step e)) (horizontalLift e 0 z) H)
      (Upper (realPosition (step e)) (horizontalLift e 0 z) H)
      ((fun y => X.1.1 (b+y)),horizontalLift e 0 z) := by
    apply hitKernel_congr
    intro y hy
    have hy0 : 0 ≤ signedHeight e y := by
      have := hy.1
      simp only [signedHeight_projection,signedHeight_horizontalLift,Int.cast_zero] at this
      exact_mod_cast this
    have hyH : (signedHeight e y).toNat<H := by
      have := hy.2
      simp only [signedHeight_projection,signedHeight_horizontalLift,Int.cast_zero,zero_add] at this
      have hylt : signedHeight e y<(H:ℤ) := by exact_mod_cast this
      omega
    change episodeSplicedRow e t X i m a (signedHeight e y).toNat (horizontalProjection e y)=_
    rw [episodeSplicedRow,ite_eq_left hyH]
    simp only [Int.toNat_of_nonneg hy0]
    apply congrArg X.1.1
    calc
      _ = horizontalLift e (t X.1.1 i) (X.1.2 (i,a))+
          horizontalLift e (signedHeight e y) (horizontalProjection e y) :=
        (horizontalLift_add e _ _ _ _).symm
      _ = b+y := by rw [horizontalLift_projection]
  rw [upperHorizontalKernel_apply,he]
  change variableHitKernel (realPosition (step e)) H ((fun y => X.1.1 (b+y)),horizontalLift e 0 z)
    (horizontalProjection e ⁻¹' A)=_
  rw [variableHitKernel_translation]
  dsimp only [b]
  rw [horizontalLift_add,add_zero]
  congr 1
  ext y
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,horizontalProjection_sub,horizontalProjection_lift]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayWindowMarks
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

lemma arrayWindowHeight_continuous {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) :
    Continuous (arrayWindowHeight e i m) := by unfold arrayWindowHeight; fun_prop
lemma arrayWindowCost_continuous {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) :
    Continuous (arrayWindowCost e i m) := by unfold arrayWindowCost; fun_prop

lemma expNeg_continuous : Continuous expNeg :=
  ENNReal.continuous_exp.comp (continuous_coe_ennreal_ereal.neg)
lemma expNeg_toReal_continuous : Continuous (fun C => (expNeg C).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro C
  exact (ENNReal.continuousAt_toReal (expNeg_ne_top C)).comp expNeg_continuous.continuousAt

lemma arrayWindowHeight_actual {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (hmono : Monotone (t X.1.1)) (i : ℤ) (m : ℕ) :
    arrayWindowHeight e i m (actualArrayMap e t J X)=(t X.1.1 (i+m)-t X.1.1 i:ℕ) := by
  have hs : (∑ r∈Finset.range m, (t X.1.1 (i+r+1)-t X.1.1 (i+r)))=
      t X.1.1 (i+m)-t X.1.1 i := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ,ih]
      have h₁ := hmono (show i ≤ i+(m:ℤ) by omega)
      have h₂ := hmono (show i+(m:ℤ) ≤ i+m+1 by omega)
      have hx : i+(m+1:ℕ)=i+(m:ℤ)+1 := by omega
      rw [hx]
      omega
  simpa only [arrayWindowHeight,actualArrayMap,Nat.cast_sum] using congrArg (fun n : ℕ => (n:ℕ∞)) hs

lemma episodeCost_nonneg_real {d : ℕ} (e : Direction d) (t : Environment d → ℤ → ℕ)
    (ω : Environment d) (hmono : Monotone (t ω))
    (hpos : ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k ω≠0) (i : ℤ) :
    0≤Real.log (crossingQuenched (realPosition (step e)) 0 (t ω i) ω).toReal-
      Real.log (crossingQuenched (realPosition (step e)) 0 (t ω (i+1)) ω).toReal := by
  apply sub_nonneg.mpr
  apply Real.log_le_log (ENNReal.toReal_pos (hpos _) (crossingQuenched_ne_top _ _ _ _))
  apply ENNReal.toReal_mono (crossingQuenched_ne_top _ _ _ _)
  exact crossingQuenched_antitone _ _ _ (by exact_mod_cast hmono (show i ≤ i+1 by omega))

lemma arrayWindowCost_actual {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (hmono : Monotone (t X.1.1))
    (hpos : ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k X.1.1≠0) (i : ℤ) (m : ℕ) :
    arrayWindowCost e i m (actualArrayMap e t J X)=ENNReal.ofReal
      (Real.log (crossingQuenched (realPosition (step e)) 0 (t X.1.1 i) X.1.1).toReal-
      Real.log (crossingQuenched (realPosition (step e)) 0 (t X.1.1 (i+m)) X.1.1).toReal) := by
  unfold arrayWindowCost
  simp only [actualArrayMap,episodeCost]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun (r : ℕ) _ => episodeCost_nonneg_real e t X.1.1 hmono hpos (i+(r:ℤ)))]
  congr 1
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,ih]
    have hx : i+(m+1:ℕ)=i+(m:ℤ)+1 := by omega
    rw [hx]
    ring

lemma expNeg_log_ratio (a b : ℝ≥0∞) (ha : a≠0) (hat : a≠⊤)
    (hb : b≠0) (hbt : b≠⊤) (hba : b≤a) :
    expNeg (ENNReal.ofReal (Real.log a.toReal-Real.log b.toReal))=b/a := by
  have hnonneg : 0≤Real.log a.toReal-Real.log b.toReal := sub_nonneg.mpr
    (Real.log_le_log (ENNReal.toReal_pos hb hbt) (ENNReal.toReal_mono hat hba))
  unfold expNeg
  rw [EReal.coe_ennreal_ofReal, max_eq_left hnonneg]
  simp only [←EReal.coe_neg,EReal.exp_coe]
  rw [neg_sub,Real.exp_sub,Real.exp_log (ENNReal.toReal_pos hb hbt),Real.exp_log (ENNReal.toReal_pos ha hat)]
  rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos ha hat),ENNReal.ofReal_toReal hbt,ENNReal.ofReal_toReal hat]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arrayKernelImage_lowerSemicontinuous {d : ℕ} (e : Direction d) (i : ℤ) (m a H : ℕ)
    (A : Set (HorizontalSpace e)) : LowerSemicontinuous (arrayKernelImage e i m a H A) := by
  unfold arrayKernelImage
  apply lowerSemicontinuous_tsum
  intro z
  simp_rw [upperHorizontalKernel_apply, hitKernel_eq_tsum_words _ _ _ _ (disjoint_strip_upper _ _ _) _,
    ←ENNReal.tsum_mul_left]
  apply lowerSemicontinuous_tsum
  intro w
  have hp : Continuous (fun Y : ActualEpisodeArray e => (Y.2.2.1 (i,(i,a),z):ℝ)) := by fun_prop
  have hw : Continuous (fun Y : ActualEpisodeArray e =>
      wordWeight (upperEnvironment e (arrayUpperRows e i m a Y)) (horizontalLift e 0 z) w.val.val) :=
    (continuous_wordWeight _ _).comp ((upperEnvironment_continuous e).comp (arrayUpperRows_continuous e i m a))
  have he : (fun Y : ActualEpisodeArray e => arrayProfileMass e i (i,a) z Y *
      ENNReal.ofReal (wordWeight (upperEnvironment e (arrayUpperRows e i m a Y))
        (horizontalLift e 0 z) w.val.val)) =
      (fun Y => ENNReal.ofReal ((Y.2.2.1 (i,(i,a),z):ℝ)*
        wordWeight (upperEnvironment e (arrayUpperRows e i m a Y)) (horizontalLift e 0 z) w.val.val)) := by
    funext Y
    exact (ENNReal.ofReal_mul (Y.2.2.1 (i,(i,a),z)).property.1).symm
  rw [he]
  exact (ENNReal.continuous_ofReal.comp (hp.mul hw)).lowerSemicontinuous

lemma arrayDiscountedProfile_continuous {d : ℕ} (e : Direction d) (i : ℤ) (m a : ℕ)
    (z : HorizontalSpace e) : Continuous (arrayDiscountedProfile e i m a z) := by
  have he : arrayDiscountedProfile e i m a z = fun Y => ENNReal.ofReal
      ((expNeg (arrayWindowCost e i m Y)).toReal*(Y.2.2.1 (i+m,(i,a),z):ℝ)) := by
    funext Y
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (expNeg_ne_top _)]
    rfl
  rw [he]
  exact ENNReal.continuous_ofReal.comp ((expNeg_toReal_continuous.comp
    (arrayWindowCost_continuous e i m)).mul (by fun_prop))

lemma arrayContinuation_closed {d : ℕ} (e : Direction d) :
    IsClosed {Y : ActualEpisodeArray e | ArrayContinuation e Y} := by
  simp only [ArrayContinuation,Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun m => isClosed_iInter fun a =>
    isClosed_iInter fun H => isClosed_iInter fun z => ?_
  have hg : IsClosed {Y : ActualEpisodeArray e | arrayKernelImage e i m a H {z} Y ≤
      arrayDiscountedProfile e i m a z Y} :=
    (arrayKernelImage_lowerSemicontinuous e i m a H {z}).isClosed_epigraph.preimage
      (continuous_id.prodMk (arrayDiscountedProfile_continuous e i m a z))
  have ho : IsOpen {Y : ActualEpisodeArray e | arrayWindowHeight e i m Y=(H:ℕ∞)} :=
    (ENat.isOpen_singleton (by simp)).preimage (arrayWindowHeight_continuous e i m)
  convert ho.isClosed_compl.union hg using 1
  all_goals try with_reducible_and_instances rfl
  ext Y
  simp [imp_iff_not_or]

lemma actual_arrayProfileMass {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (j : ℤ) (p : StationaryCompact.Label) (z : HorizontalSpace e) :
    arrayProfileMass e j p z (actualArrayMap e t J X)=
      globalHorizontalProfile e (t X.1.1 j) X.1.1 {X.1.2 p+z} := by
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

lemma actual_arrayKernelImage {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (i : ℤ) (m a : ℕ) (A : Set (HorizontalSpace e)) :
    arrayKernelImage e i m a (t X.1.1 (i+m)-t X.1.1 i) A (actualArrayMap e t J X)=
      ∫⁻ z, variableHitKernel (realPosition (step e)) (t X.1.1 (i+m)-t X.1.1 i)
        (X.1.1,horizontalLift e (t X.1.1 i) z)
        {y | horizontalProjection e y-X.1.2 (i,a)∈A}
        ∂globalHorizontalProfile e (t X.1.1 i) X.1.1 := by
  unfold arrayKernelImage
  simp_rw [actual_arrayProfileMass]
  have he : arrayUpperRows e i m a (actualArrayMap e t J X)=
      fun p => episodeSplicedRow e t X i m a p.1 p.2 := rfl
  simp_rw [he,episodeSpliced_kernel]
  rw [lintegral_countable']
  simp_rw [mul_comm]
  exact (Equiv.addLeft (X.1.2 (i,a))).tsum_eq (fun z : HorizontalSpace e =>
    globalHorizontalProfile e (t X.1.1 i) X.1.1 {z} *
    variableHitKernel (realPosition (step e)) (t X.1.1 (i+m)-t X.1.1 i)
      (X.1.1,horizontalLift e (t X.1.1 i) z)
      {y | horizontalProjection e y-X.1.2 (i,a)∈A})

lemma actual_arrayContinuation {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (hmono : Monotone (t X.1.1))
    (hpos : ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k X.1.1≠0) :
    ArrayContinuation e (actualArrayMap e t J X) := by
  intro i m a H z hH
  rw [arrayWindowHeight_actual e t J X hmono] at hH
  have hH' : t X.1.1 (i+m)-t X.1.1 i=H := by exact_mod_cast hH
  subst H
  rw [actual_arrayKernelImage]
  have hik : t X.1.1 i ≤ t X.1.1 (i+m) := hmono (by omega)
  have hadd : t X.1.1 i+(t X.1.1 (i+m)-t X.1.1 i)=t X.1.1 (i+m) := Nat.add_sub_of_le hik
  have hh := globalHorizontalProfile_continuation e (t X.1.1 i)
    (t X.1.1 (i+m)-t X.1.1 i) X.1.1 (hpos _) {w | w-X.1.2 (i,a)∈({z}:Set (HorizontalSpace e))}
  simp only [←Nat.cast_add,hadd] at hh
  have hs : {w : HorizontalSpace e | w-X.1.2 (i,a)∈({z}:Set (HorizontalSpace e))}={X.1.2 (i,a)+z} := by
    ext w
    simp only [Set.mem_ofPred,Set.mem_singleton_iff]
    rw [sub_eq_iff_eq_add,add_comm z]
  convert hh using 1
  · rfl
  · unfold arrayDiscountedProfile
    rw [arrayWindowCost_actual e t J X hmono hpos,expNeg_log_ratio _ _ (hpos _)
    (crossingQuenched_ne_top _ _ _ _) (hpos _) (crossingQuenched_ne_top _ _ _ _)
    (crossingQuenched_antitone _ _ _ (by exact_mod_cast hik)),actual_arrayProfileMass,hs]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_BadArraySampling
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_raw_mass_pos (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (hN : C.sfloor ≤ (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2))) :
    0<(actualOccupationRaw e ν ((environmentLaw ν)[|badCrossingEvent e N (1/2)])
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
      N (C.activeCount hef N)).real Set.univ := by
  have hN0 : 0<N := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans hN)
  have : IsProbabilityMeasure ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) :=
    cond_isProbabilityMeasure (badCrossingEvent_pos e N (1/2) D (environmentLaw ν) hN0 hmass)
  have hpos := EpisodeChainLedger.operational_mass_positive (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N
    ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) hN0
  have he := EpisodeChainLedger.operational_raw_mass (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ν
    ((environmentLaw ν)[|badCrossingEvent e N (1/2)])
  exact hpos.trans_eq he.symm

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryWindowEntropy
attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma actualOccupation_ae_of_ae_invariant {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (s : Set (ActualEpisodeArray e)) (hs : MeasurableSet s)
    (ha : ∀ᵐ X ∂episodeInputLaw e ν Q t ht, actualArrayMap e t J X∈s)
    (hshift : ∀ Y∈s, StationaryCompact.shift Y∈s) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)), Y∈s := by
  have hiter (i : ℕ) : ∀ᵐ X ∂episodeInputLaw e ν Q t ht,
      StationaryCompact.shift^[i] (actualArrayMap e t J X)∈s := by
    filter_upwards [ha] with X hX
    induction i with
    | zero => exact hX
    | succ i hi =>
      rw [Function.iterate_succ_apply']
      exact hshift _ hi
  have hraw : ∀ᵐ Y ∂actualOccupationRaw e ν Q t J ht N M, Y∈s := by
    unfold actualOccupationRaw StationaryCompact.episodeOccupationRaw
    rw [ae_finsetSum_measure_iff]
    intro i _
    apply (ae_map_iff ((StationaryCompact.shift_continuous.measurable.iterate i).comp
      (actualArrayMap_measurable e t J ht hJ)).aemeasurable hs).mpr
    exact ae_restrict_of_ae (hiter i)
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let ρ : FiniteMeasure (ActualEpisodeArray e) := ⟨actualOccupationRaw e ν Q t J ht N M,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hn : ρ≠0 := by
    intro hz
    have hh : (actualOccupationRaw e ν Q t J ht N M).real Set.univ=0 := by
      change (ρ : Measure (ActualEpisodeArray e)).real Set.univ=0
      rw [hz]
      simp
    linarith
  change ∀ᵐ Y ∂(ρ.normalize : Measure (ActualEpisodeArray e)), Y∈s
  rw [ρ.toMeasure_normalize_eq_of_nonzero hn]
  exact Measure.ae_smul_measure hraw _

lemma arrayElliptic_closed {d : ℕ} (e : Direction d) (κ : ℝ≥0) :
    IsClosed {Y : ActualEpisodeArray e | ArrayElliptic e κ Y} := by
  unfold ArrayElliptic
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun m => isClosed_iInter fun a =>
    isClosed_iInter fun l => isClosed_iInter fun z => isClosed_iInter fun u => ?_
  exact isClosed_le continuous_const ((continuous_apply u).comp
    (continuous_subtype_val.comp (by fun_prop)))

lemma arrayElliptic_shift {d : ℕ} (e : Direction d) (κ : ℝ≥0)
    (Y : ActualEpisodeArray e) (h : ArrayElliptic e κ Y) :
    ArrayElliptic e κ (StationaryCompact.shift Y) := by
  intro i m a l z u
  exact h (i+1) m a l z u

lemma auxiliary_rows {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (κ : ℝ≥0) (hν : ∀ᵐ r ∂ν, ∀ u, κ ≤ r.1 u) :
    ∀ᵐ A ∂episodeAuxiliaryLaw e ν, ∀ p q u, κ ≤ (A p q).1 u := by
  have hinner : ∀ᵐ A ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν),
      ∀ q u, κ ≤ (A q).1 u := by
    apply ae_all_iff.mpr
    intro q
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ×HorizontalSpace e => ν) q).quasiMeasurePreserving.ae hν
  apply ae_all_iff.mpr
  intro p
  exact (measurePreserving_eval_infinitePi
    (fun _ : ℤ×ℕ => Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)) p).quasiMeasurePreserving.ae hinner

lemma actualArrayMap_elliptic_ae {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (κ : ℝ≥0) (hν : ∀ᵐ r ∂ν, ∀ u, κ ≤ r.1 u)
    (hQ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u) :
    ∀ᵐ X ∂episodeInputLaw e ν Q t ht, ArrayElliptic e κ (actualArrayMap e t J X) := by
  have hm : MeasurableSet {ω : Environment d | ∀ y u, κ ≤ (ω y).1 u} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro y
    apply MeasurableSet.iInter
    intro u
    exact measurableSet_le measurable_const ((measurable_pi_apply u).comp
      (measurable_subtype_coe.comp (measurable_pi_apply y)))
  have hbase := Measure.ae_compProd_of_ae_fst (globalEpisodeAnchors e t ht) hm hQ
  have hfirst := (Measure.quasiMeasurePreserving_fst
    (μ:=Q.compProd (globalEpisodeAnchors e t ht)) (ν:=episodeAuxiliaryLaw e ν)).ae hbase
  have hsecond := (Measure.quasiMeasurePreserving_snd
    (μ:=Q.compProd (globalEpisodeAnchors e t ht)) (ν:=episodeAuxiliaryLaw e ν)).ae
    (auxiliary_rows e ν κ hν)
  filter_upwards [hfirst,hsecond] with X hX hA
  intro i m a l z u
  change κ ≤ (episodeSplicedRow e t X i m a l z).1 u
  unfold episodeSplicedRow
  split
  · exact hX _ u
  · exact hA _ _ u

lemma actualOccupation_elliptic {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (κ : ℝ≥0) (hν : ∀ᵐ r ∂ν, ∀ u, κ ≤ r.1 u)
    (hQ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)), ArrayElliptic e κ Y :=
  actualOccupation_ae_of_ae_invariant e ν Q t J ht hJ N M hpos _
    (arrayElliptic_closed e κ).measurableSet (actualArrayMap_elliptic_ae e ν Q t J ht κ hν hQ)
    (arrayElliptic_shift e κ)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SurvivalConditional
attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma arrayContinuation_shift {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayContinuation e Y) : ArrayContinuation e (StationaryCompact.shift Y) := by
  intro i m a H z hH
  have he : arrayWindowHeight e i m (StationaryCompact.shift Y)=arrayWindowHeight e (i+1) m Y := by
    simp only [arrayWindowHeight,StationaryCompact.shift,add_right_comm i _ 1]
  rw [he] at hH
  have hh := h (i+1) m a H z hH
  convert hh using 1
  · rfl
  · simp only [arrayDiscountedProfile,arrayWindowCost,arrayProfileMass,StationaryCompact.shift,
      add_right_comm i _ 1]

lemma actualArrayMap_continuation_ae {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hmono : ∀ ω, Monotone (t ω)) (κ : ℝ≥0) (hκ : 0<κ)
    (hQ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u) :
    ∀ᵐ X ∂episodeInputLaw e ν Q t ht, ArrayContinuation e (actualArrayMap e t J X) := by
  have hm : MeasurableSet {ω : Environment d | ∀ y u, κ ≤ (ω y).1 u} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun y => MeasurableSet.iInter fun u =>
      measurableSet_le measurable_const ((measurable_pi_apply u).comp
        (measurable_subtype_coe.comp (measurable_pi_apply y)))
  have hb := Measure.ae_compProd_of_ae_fst (globalEpisodeAnchors e t ht) hm hQ
  have ha := (Measure.quasiMeasurePreserving_fst
    (μ:=Q.compProd (globalEpisodeAnchors e t ht)) (ν:=episodeAuxiliaryLaw e ν)).ae hb
  filter_upwards [ha] with X hX
  apply actual_arrayContinuation e t J X (hmono _)
  intro k
  exact ne_of_gt ((pos_iff_ne_zero.mpr (pow_ne_zero k (show (κ:ℝ≥0∞)≠0 by exact_mod_cast hκ.ne'))).trans_le
    (coordinate_survival_lower e X.1.1 κ (fun y => hX y e) k))

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

lemma paddedTimes_int_mono [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (ω : Environment d) : Monotone (C.paddedTimes hef N ω) := by
  intro i j hij
  exact episodeBoundary_mono (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω (Int.toNat_le_toNat hij)

variable [IsProbabilityMeasure ν]

lemma bad_limit_continuation (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (Ns : ℕ → ℕ) (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ArrayContinuation e Y := by
  apply closed_support_weak_limit _ ρ hlim _ (arrayContinuation_closed e)
  intro n
  apply actualOccupation_ae_of_ae_invariant e ν _
    (C.paddedTimes hef (Ns n)) (C.paddedStages hef (Ns n))
    (C.paddedTimes_measurable hef (Ns n)) (C.paddedStages_measurable hef (Ns n)) (Ns n)
    (C.activeCount hef (Ns n)) (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n)) _
    (arrayContinuation_closed e).measurableSet
  · exact actualArrayMap_continuation_ae e ν _ _ _ (C.paddedTimes_measurable hef (Ns n))
      (C.paddedTimes_int_mono hef (Ns n)) C.κ C.hκ0
      ((cond_absolutelyContinuous (μ:=environmentLaw ν)
        (s:=badCrossingEvent e (Ns n) (1/2))).ae_le C.rows)
  · exact arrayContinuation_shift e

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayPermutation
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arrayPerm_continuous {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ) :
    Continuous (arrayPerm e σ) := by unfold arrayPerm; fun_prop

lemma arrayPerm_shift {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (Y : ActualEpisodeArray e) :
    arrayPerm e σ (StationaryCompact.shift Y) = StationaryCompact.shift (arrayPerm e σ Y) := rfl

lemma arrayPerm_iterate {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (j : ℕ) (Y : ActualEpisodeArray e) :
    arrayPerm e σ (StationaryCompact.shift^[j] Y) = StationaryCompact.shift^[j] (arrayPerm e σ Y) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',arrayPerm_shift,ih,Function.iterate_succ_apply']

lemma anchorsPerm_measurable {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ) :
    Measurable (anchorsPerm e σ) := by unfold anchorsPerm; fun_prop

lemma inputPerm_measurable {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ) :
    Measurable (inputPerm e σ) :=
  ((measurable_fst.comp measurable_fst).prodMk
    ((anchorsPerm_measurable e σ).comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd

lemma arrayPerm_actual {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) :
    arrayPerm e σ (actualArrayMap e t J X) = actualArrayMap e t J (inputPerm e σ X) := rfl

lemma anchorLaw_perm {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) (ω : Environment d) :
    (globalEpisodeAnchors e t ht ω).map (anchorsPerm e σ) = globalEpisodeAnchors e t ht ω := by
  have hh := Measure.infinitePi_map_piCongrLeft
    (fun p : StationaryCompact.Label => episodeProfile e t ω p.1) (labelPerm σ).symm
  convert hh using 1
  · congr 1
    funext E p
    simp [anchorsPerm,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,labelPerm]
  · rfl

lemma inputLaw_perm {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [SFinite Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    (episodeInputLaw e ν Q t ht).map (inputPerm e σ) = episodeInputLaw e ν Q t ht := by
  have hk : (globalEpisodeAnchors e t ht).map (anchorsPerm e σ)=globalEpisodeAnchors e t ht := by
    ext ω
    rw [Kernel.map_apply _ (anchorsPerm_measurable e σ),anchorLaw_perm]
  have hmap : (Q.compProd (globalEpisodeAnchors e t ht)).map (Prod.map id (anchorsPerm e σ)) =
      Q.compProd (globalEpisodeAnchors e t ht) := by
    rw [←Measure.compProd_map (anchorsPerm_measurable e σ),hk]
  unfold episodeInputLaw
  change ((Q.compProd (globalEpisodeAnchors e t ht)).prod (episodeAuxiliaryLaw e ν)).map
    (Prod.map (Prod.map id (anchorsPerm e σ)) id)=_
  rw [←Measure.map_prod_map _ _ (measurable_id.prodMap (anchorsPerm_measurable e σ)) measurable_id,
    hmap,Measure.map_id]

lemma occupation_perm_integral {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (F : ActualEpisodeArray e →ᵇ ℝ) :
    (∫ Y, F (arrayPerm e σ Y) ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)))=
      ∫ Y, F Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)) := by
  rw [actualOccupation_integral e ν Q t J ht N M hpos,
    actualOccupation_integral e ν Q t J ht N M hpos]
  congr 1
  have h₁ := actualOccupationRaw_integral e ν Q t J ht hJ N M hM
    (F.toContinuousMap.comp ⟨arrayPerm e σ,arrayPerm_continuous e σ⟩)
  have h₂ := actualOccupationRaw_integral e ν Q t J ht hJ N M hM F.toContinuousMap
  simp only [ContinuousMap.comp_apply,BoundedContinuousFunction.coe_toContinuousMap,
    ContinuousMap.coe_mk] at h₁ h₂
  rw [h₁,h₂]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [arrayPerm_iterate,arrayPerm_actual]
  have hf : Measurable (fun X : EpisodeInput e => F (StationaryCompact.shift^[j] (actualArrayMap e t J X))) :=
    F.continuous.measurable.comp ((StationaryCompact.shift_continuous.measurable.iterate j).comp
      (actualArrayMap_measurable e t J ht hJ))
  rw [←integral_map (inputPerm_measurable e σ).aemeasurable hf.aestronglyMeasurable,
    inputLaw_perm]

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_limit_perm (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (Ns : ℕ → ℕ) (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) (σ : Equiv.Perm ℕ) :
    MeasurePreserving (arrayPerm e σ) (ρ : Measure (ActualEpisodeArray e)) (ρ : Measure (ActualEpisodeArray e)) := by
  apply StationaryCompact.invariant_of_weak_limit (arrayPerm e σ) (arrayPerm_continuous e σ) _ ρ hlim
  intro F
  have hz (n : ℕ) : (∫ Y, F (arrayPerm e σ Y) ∂(C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)]) : Measure (ActualEpisodeArray e)))=
      ∫ Y, F Y ∂(C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)]) : Measure (ActualEpisodeArray e)) :=
    occupation_perm_integral e σ ν _ _ _ (C.paddedTimes_measurable hef (Ns n))
      (C.paddedStages_measurable hef (Ns n)) (Ns n) _ (C.activeCount_measurable hef (Ns n))
      (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n)) F
  simpa only [hz,sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayProfileConsistency
attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma finite_translated_atoms_le_one {H : Type*} [AddCommGroup H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure H) [IsProbabilityMeasure μ] (v : H) (s : Finset H) :
    ∑ z∈s, (μ {v+z}).toReal ≤ 1 := by
  rw [←ENNReal.toReal_sum (fun z _ => measure_ne_top μ _)]
  have he : ∑ z∈s, μ {v+z}=μ (↑(s.image (fun z => v+z)):Set H) := by
    rw [←sum_measure_singleton]
    have hi : ∀ a∈s, ∀ b∈s, v+a=v+b → a=b := fun a _ b _ h => add_left_cancel h
    exact (Finset.sum_image (f := fun z => μ {z}) hi).symm
  rw [he]
  exact measureReal_le_one

lemma arrayProfilesConsistent_closed {d : ℕ} (e : Direction d) :
    IsClosed {Y : ActualEpisodeArray e | ArrayProfilesConsistent e Y} := by
  have ht : IsClosed {Y : ActualEpisodeArray e |
      ∀ (j : ℤ) (p q : StationaryCompact.Label) (z w : HorizontalSpace e),
      Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e)) →
        Y.2.2.1 (j,p,z+w)=Y.2.2.1 (j,q,w)} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun j => isClosed_iInter fun p => isClosed_iInter fun q =>
      isClosed_iInter fun z => isClosed_iInter fun w => ?_
    have heq : {Y : ActualEpisodeArray e | Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e)) →
        Y.2.2.1 (j,p,z+w)=Y.2.2.1 (j,q,w)} =
      {Y | Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e))}ᶜ ∪
      {Y | Y.2.2.1 (j,p,z+w)=Y.2.2.1 (j,q,w)} := by
      ext; simp [imp_iff_not_or]
    rw [heq]
    exact ((ReferenceClasses.finite_value_clopen z).preimage (by fun_prop)).2.isClosed_compl.union
      (isClosed_eq (by fun_prop) (by fun_prop))
  have hm : IsClosed {Y : ActualEpisodeArray e |
      ∀ (j : ℤ) (p : StationaryCompact.Label) (s : Finset (HorizontalSpace e)),
      ∑ z∈s, (Y.2.2.1 (j,p,z):ℝ) ≤ 1} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun j => isClosed_iInter fun p => isClosed_iInter fun s => ?_
    exact isClosed_le (by fun_prop) continuous_const
  exact ht.inter hm

lemma actual_arrayProfilesConsistent {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) :
    ArrayProfilesConsistent e (actualArrayMap e t J X) := by
  constructor
  · intro j p q z w h
    have he : X.1.2 q-X.1.2 p=z := OnePoint.coe_injective h
    change globalHorizontalCoordinate e (t X.1.1 j) X.1.1 (X.1.2 p+(z+w)) =
      globalHorizontalCoordinate e (t X.1.1 j) X.1.1 (X.1.2 q+w)
    congr 1
    rw [←he]
    abel
  · intro j p s
    exact finite_translated_atoms_le_one (globalHorizontalProfile e (t X.1.1 j) X.1.1) (X.1.2 p) s

lemma arrayProfilesConsistent_shift {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayProfilesConsistent e Y) : ArrayProfilesConsistent e (StationaryCompact.shift Y) := by
  constructor
  · intro j p q z w ho
    exact h.1 (j+1) (p.1+1,p.2) (q.1+1,q.2) z w ho
  · intro j p s
    exact h.2 (j+1) (p.1+1,p.2) s

lemma actualOccupation_profilesConsistent {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)),
      ArrayProfilesConsistent e Y :=
  actualOccupation_ae_of_invariant e ν Q t J ht hJ N M hpos _
    (arrayProfilesConsistent_closed e).measurableSet (actual_arrayProfilesConsistent e t J)
    (arrayProfilesConsistent_shift e)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_limit_consistent (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (Ns : ℕ → ℕ) (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)),
      ArrayOffsetsConsistent e Y ∧ ArrayProfilesConsistent e Y := by
  have ho := closed_support_weak_limit _ ρ hlim _ (arrayOffsetsConsistent_closed e) (fun n =>
    actualOccupation_offsetsConsistent e ν _ (C.paddedTimes hef (Ns n)) (C.paddedStages hef (Ns n))
      (C.paddedTimes_measurable hef (Ns n)) (C.paddedStages_measurable hef (Ns n)) (Ns n)
      (C.activeCount hef (Ns n)) (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n)))
  have hp := closed_support_weak_limit _ ρ hlim _ (arrayProfilesConsistent_closed e) (fun n =>
    actualOccupation_profilesConsistent e ν _ (C.paddedTimes hef (Ns n)) (C.paddedStages hef (Ns n))
      (C.paddedTimes_measurable hef (Ns n)) (C.paddedStages_measurable hef (Ns n)) (Ns n)
      (C.activeCount hef (Ns n)) (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n)))
  filter_upwards [ho,hp] with Y hO hP
  exact ⟨hO,hP⟩

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_BadArrayElliptic
attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma row_law_lower_bound (C : OperationalConstants ν e f D) :
    ∀ᵐ r ∂ν, ∀ u, C.κ ≤ r.1 u := by
  have hp : ∀ᵐ ω ∂environmentLaw ν, ∀ u, C.κ ≤ (ω 0).1 u :=
    C.rows.mono fun ω hω => hω 0
  have hm : MeasurableSet {r : Row d | ∀ u, C.κ ≤ r.1 u} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun u => measurableSet_le measurable_const
      ((measurable_pi_apply u).comp measurable_subtype_coe)
  have hmp := measurePreserving_eval_infinitePi (fun _ : Lattice d => ν) 0
  have hh := (ae_map_iff hmp.measurable.aemeasurable hm).mpr hp
  simpa only [environmentLaw,hmp.map_eq] using hh

lemma bad_limit_elliptic (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (Ns : ℕ → ℕ) (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ArrayElliptic e C.κ Y := by
  apply closed_support_weak_limit _ ρ hlim _ (arrayElliptic_closed e C.κ)
  intro n
  exact actualOccupation_elliptic e ν _
    (C.paddedTimes hef (Ns n)) (C.paddedStages hef (Ns n))
    (C.paddedTimes_measurable hef (Ns n)) (C.paddedStages_measurable hef (Ns n)) (Ns n)
    (C.activeCount hef (Ns n)) (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n))
    C.κ C.row_law_lower_bound
    ((cond_absolutelyContinuous (μ:=environmentLaw ν)
      (s:=badCrossingEvent e (Ns n) (1/2))).ae_le C.rows)

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryArrayLaw
attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e f : Direction d} {D : ℝ}

theorem bad_stationary_array_law_oai (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hN : ∀ n, C.sfloor≤(Ns n:ℝ)) (hlarge : ∀ n, 32*C.b≤(1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D)≤(environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2))) :
    Nonempty (StationaryArrayLaw ν e) := by
  obtain ⟨ρ,φ,hφ,hlim,hstat,hsample,hzero,hmarks,hJ,hh,hc,hcp⟩ := C.bad_array_finite_marks hef hD Ns hNs hN hlarge hmass
  let Ns' := fun n => Ns (φ n)
  have hN' := fun n => hN (φ n)
  have hlarge' := fun n => hlarge (φ n)
  have hmass' := fun n => hmass (φ n)
  exact ⟨{
    law := ρ
    preserving := hstat
    symmetric := C.bad_limit_perm hef Ns' hN' hmass' ρ hlim
    consistent := C.bad_limit_consistent hef Ns' hN' hmass' ρ hlim
    sampling := hsample
    zero_sampling := hzero
    finite_marks := stationary_finite_marks_all e _ hstat hmarks
    integrable_cost := hc
    positive_cost := C.hb.trans_le hcp
    integrable_logheight := hh
    continuation := C.bad_limit_continuation hef Ns' hN' hmass' ρ hlim
    survival := C.bad_limit_averaged_survival hef Ns' hN' hmass' ρ hlim
    κ := C.κ
    κ_pos := C.hκ0
    elliptic := C.bad_limit_elliptic hef Ns' hN' hmass' ρ hlim
    entropyConstant := C.windowEntropyConstant
    entropy := C.stationary_window_entropy hef hD Ns' hN' hlarge' hmass' ρ hlim hstat
  }⟩

end OperationalConstants
end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.OperationalConstants.bad_stationary_array_law_oai := @OAI.DirectionalTransience.OperationalConstants.bad_stationary_array_law_oai
