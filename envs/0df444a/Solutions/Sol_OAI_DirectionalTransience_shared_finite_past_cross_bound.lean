-- Prove2me | solution 1 for OAI.DirectionalTransience.shared_finite_past_cross_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:00:51.892199+00:00
-- url     : https://prove2.me/submissions/935e5066-9b00-43c3-b47c-99378d80df97

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal007
import Theorems.Thm_OAI_DirectionalTransience_shared_centered_cross_uniform_bound

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordDepartures
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClippedInverse
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
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

lemma integrable_of_nonneg_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ a, 0 ≤ f a ∧ f a ≤ B) : Integrable f μ := by
  exact (MemLp.of_bound (p := 1) hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hb a).1] using (hb a).2)).integrable le_rfl

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightSlab
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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

lemma measurableSet_firstTrueRecord {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    MeasurableSet {X : Path d | FirstTrueRecord ℓ X n} := by
  simp only [FirstTrueRecord, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.const _).inter ((measurableSet_trueRecord ℓ n).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => (measurableSet_trueRecord ℓ j).compl))

lemma admissibleTrueWord_record {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (hw : AdmissibleTrueWord ℓ w) :
    ∀ y ∈ wordDepartures 0 w,
      dot (realPosition y) ℓ < dot (realPosition (wordPath 0 w w.length)) ℓ := by
  intro y hy
  obtain ⟨j, hj, rfl⟩ := (wordDepartures_mem_iff 0 y w).mp hy
  exact (hw.2.1 j hj).2

lemma suffix_noDrop_iff {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) :
    (fun j => X (n + j) - X n) ∈ NoDrop ℓ 0 ↔ X ∈ FutureNoDrop ℓ n := by
  change (∀ j, dot (realPosition 0) ℓ ≤ dot (realPosition (X (n + j) - X n)) ℓ) ↔ _
  simp only [dot_realPosition_sub, FutureNoDrop, Set.mem_ofPred_eq]
  have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot, realPosition]
  rw [hzero]
  exact forall_congr' fun j => sub_nonneg

lemma firstTrueWord_characterization {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (X : Path d) (hX : X ∈ wordCylinder 0 w) :
    (X ∈ NoDrop ℓ 0 ∧ FirstTrueRecord ℓ X w.length) ↔
      AdmissibleTrueWord ℓ w ∧
        (fun j => X (w.length + j) - wordPath 0 w w.length) ∈ NoDrop ℓ 0 := by
  have hx0 : X 0 = 0 := by simpa only [wordPath_zero] using hX 0 (Nat.zero_le _)
  have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot, realPosition]
  have hrec (j : ℕ) (hj : j ≤ w.length) :
      StrictRecord ℓ X j ↔ StrictRecord ℓ (wordPath 0 w) j :=
    strictRecord_congr_prefix ℓ hj hX
  have hsuf : (fun j => X (w.length + j) - wordPath 0 w w.length) ∈ NoDrop ℓ 0 ↔
      X ∈ FutureNoDrop ℓ w.length := by
    rw [← hX w.length le_rfl]
    exact suffix_noDrop_iff ℓ X w.length
  rw [hsuf]
  constructor
  · rintro ⟨hD, hn, ⟨hr, hs⟩, hfirst⟩
    refine ⟨⟨hn, ?_, ?_⟩, hs⟩
    · intro j hj
      constructor
      · simpa only [← hX j hj.le, hzero] using hD j
      · simpa only [← hX j hj.le, ← hX w.length le_rfl] using hr j hj
    · intro j hj hjn hrj
      have hnot := hfirst j hj hjn
      have hnotD : X ∉ FutureNoDrop ℓ j := fun h => hnot ⟨(hrec j hjn.le).mpr hrj, h⟩
      change ¬ ∀ k, dot (realPosition (X j)) ℓ ≤ dot (realPosition (X (j + k))) ℓ at hnotD
      push Not at hnotD
      obtain ⟨k, hk⟩ := hnotD
      have hjk : j < j + k := by
        by_contra hh
        have he : j + k = j := by omega
        rw [he] at hk
        exact (lt_irrefl _) hk
      have hklen : j + k < w.length := by
        by_contra hh
        have hle : w.length ≤ j + k := by omega
        have hs' := hs (j + k - w.length)
        change dot (realPosition (X w.length)) ℓ ≤
          dot (realPosition (X (w.length + (j + k - w.length)))) ℓ at hs'
        rw [Nat.add_sub_of_le hle] at hs'
        exact (not_lt_of_ge ((hr j hjn).le.trans hs')) hk
      exact ⟨j + k, hjk, hklen, by
        simpa only [← hX (j + k) hklen.le, ← hX j hjn.le] using hk⟩
  · rintro ⟨⟨hn, hpre, hbad⟩, hs⟩
    have hr : StrictRecord ℓ X w.length := (hrec _ le_rfl).mpr fun j hj => (hpre j hj).2
    refine ⟨?_, hn, ⟨hr, hs⟩, ?_⟩
    · intro j
      by_cases hj : j < w.length
      · simpa only [hX j hj.le, hzero] using (hpre j hj).1
      · have hle : w.length ≤ j := by omega
        have ht := hs (j - w.length)
        change dot (realPosition (X w.length)) ℓ ≤
          dot (realPosition (X (w.length + (j - w.length)))) ℓ at ht
        rw [Nat.add_sub_of_le hle] at ht
        exact (le_of_eq (congrArg (fun x : Lattice d => dot (realPosition x) ℓ) hx0.symm)).trans
          ((hr 0 hn).le.trans ht)
    · intro j hj hjn ⟨hrj, hsj⟩
      obtain ⟨k, hjk, hk, hdrop⟩ := hbad j hj hjn ((hrec j hjn.le).mp hrj)
      have ht := hsj (k - j)
      change dot (realPosition (X j)) ℓ ≤ dot (realPosition (X (j + (k - j)))) ℓ at ht
      rw [Nat.add_sub_of_le hjk.le, hX j hjn.le, hX k hk.le] at ht
      exact (not_lt_of_ge ht) hdrop

lemma firstTrueRecord_unique {d : ℕ} (ℓ : Vector d) (X : Path d) {m n : ℕ}
    (hm : FirstTrueRecord ℓ X m) (hn : FirstTrueRecord ℓ X n) : m = n := by
  rcases lt_trichotomy m n with h | h | h
  · exact False.elim (hn.2.2 m hm.1 h hm.2.1)
  · exact h
  · exact False.elim (hm.2.2 n hn.1 h hn.2.1)

lemma conditionedLaw_apply_of_subset {d : ℕ} (ν : Measure (Row d))
    (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    conditionedLaw ν ℓ A = (annealedLaw ν (NoDrop ℓ 0))⁻¹ * annealedLaw ν A := by
  rw [conditionedLaw, Measure.smul_apply, Measure.restrict_apply hA,
    Set.inter_eq_left.mpr hAD, smul_eq_mul]

lemma conditioned_true_word_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (w : List (Direction d)) (hw : AdmissibleTrueWord ℓ w)
    (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    conditionedLaw ν ℓ ((fun X : Path d => fun j => X (w.length + j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) =
      annealedLaw ν (wordCylinder 0 w) * conditionedLaw ν ℓ A := by
  have hE : MeasurableSet ((fun X : Path d => fun j => X (w.length + j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) :=
    (hA.preimage (by fun_prop)).inter (measurableSet_wordCylinder _ _)
  have hED : ((fun X : Path d => fun j => X (w.length + j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) ⊆ NoDrop ℓ 0 := by
    rintro X ⟨hXA, hX⟩
    exact ((firstTrueWord_characterization ℓ w X hX).mpr ⟨hw, hAD hXA⟩).1
  rw [conditionedLaw_apply_of_subset ν ℓ _ hE hED,
    annealed_record_suffix ν ℓ w (admissibleTrueWord_record ℓ w hw) A hA hAD,
    conditionedLaw_apply_of_subset ν ℓ A hA hAD]
  ac_rfl

lemma piLE_iSup_eq {d : ℕ} :
    (⨆ n : ℕ, Filtration.piLE (X := fun _ : ℕ => Lattice d) n) =
      (inferInstance : MeasurableSpace (Path d)) := by
  apply le_antisymm (iSup_le fun n => Filtration.piLE.le n)
  change (⨆ n : ℕ, MeasurableSpace.comap (fun X : Path d => X n) inferInstance) ≤ _
  apply iSup_le
  intro n
  apply le_trans _ (le_iSup _ n)
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hm : @Measurable (Path d) (Lattice d)
      (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance) _
        (fun X => X n) := by
    have hc : Measurable (fun f : (i : Finset.Iic n) → Lattice d =>
        f ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
    exact hc.comp (Measurable.of_comap_le le_rfl)
  exact hm.comap_le

lemma prefix_probability_lower {d : ℕ} (μ : Measure (Path d))
    (E : Set (Path d)) (p : ℝ≥0∞) (n : ℕ)
    (h : ∀ f : Path d, p * μ (pathCylinder f n) ≤ μ (E ∩ pathCylinder f n))
    (S : Set (Path d)) (hS : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => Lattice d) n] S) :
    p * μ S ≤ μ (E ∩ S) := by
  classical
  rw [Filtration.piLE_eq_comap_frestrictLe] at hS
  obtain ⟨B, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hS
  rw [measure_partition_prefix μ _ n, measure_partition_prefix μ (E ∩ _) n,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro f
  have hc : Preorder.frestrictLe n ⁻¹' B ∩ pathCylinder (extendPrefix n f) n =
      if f ∈ B then pathCylinder (extendPrefix n f) n else ∅ := by
    split_ifs with hf
    · apply Set.inter_eq_right.mpr
      intro X hX
      change Preorder.frestrictLe n X ∈ B
      have he : Preorder.frestrictLe n X = f := by
        funext j
        change X j = f j
        simpa only [extendPrefix_apply n f j (Finset.mem_Iic.mp j.2)]
          using hX j (Finset.mem_Iic.mp j.2)
      rwa [he]
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨hB, hX⟩
      have he : Preorder.frestrictLe n X = f := by
        funext j
        change X j = f j
        simpa only [extendPrefix_apply n f j (Finset.mem_Iic.mp j.2)]
          using hX j (Finset.mem_Iic.mp j.2)
      exact hf (by simpa only [Set.mem_preimage, he] using hB)
  rw [Set.inter_assoc, hc]
  split_ifs
  · exact h _
  · simp

lemma ae_of_prefix_probability_lower {d : ℕ} (μ : Measure (Path d)) [IsFiniteMeasure μ]
    (E : Set (Path d)) (hE : MeasurableSet E) (p : ℝ≥0∞) (hp : 0 < p) (hpt : p ≠ ∞)
    (h : ∀ (n : ℕ) (f : Path d),
      p * μ (pathCylinder f n) ≤ μ (E ∩ pathCylinder f n)) : ∀ᵐ X ∂μ, X ∈ E := by
  let g : Path d → ℝ := E.indicator (fun _ => 1)
  have hg : Integrable g μ := (integrable_const (1 : ℝ)).indicator hE
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace (Path d)) := Filtration.piLE
  have hlo (n : ℕ) : ∀ᵐ X ∂μ, p.toReal ≤ μ[g | ℱ n] X := by
    apply ae_of_ae_trim (ℱ.le n)
    apply ae_le_of_forall_setIntegral_le (integrable_const p.toReal)
      (integrable_condExp.trim (ℱ.le n) stronglyMeasurable_condExp)
    intro S hS _
    rw [← setIntegral_trim (ℱ.le n) stronglyMeasurable_const hS,
      ← setIntegral_trim (ℱ.le n) stronglyMeasurable_condExp hS,
      setIntegral_condExp (ℱ.le n) hg hS]
    have hh := prefix_probability_lower μ E p n (h n) S hS
    have hreal := ENNReal.toReal_mono (measure_ne_top μ _) hh
    rw [ENNReal.toReal_mul] at hreal
    simpa only [g, setIntegral_indicator hE, setIntegral_const, smul_eq_mul,
      mul_one, one_mul, Measure.real, Set.inter_comm E S, mul_comm] using hreal
  have hgmeas : StronglyMeasurable[⨆ n, ℱ n] g := by
    change StronglyMeasurable[⨆ n, Filtration.piLE (X := fun _ : ℕ => Lattice d) n] g
    rw [piLE_iSup_eq]
    exact stronglyMeasurable_const.indicator hE
  have hlim := hg.tendsto_ae_condExp (ℱ := ℱ) hgmeas
  filter_upwards [ae_all_iff.mpr hlo, hlim] with X hX hlimX
  have hge : p.toReal ≤ g X := ge_of_tendsto hlimX (Eventually.of_forall hX)
  by_contra hnot
  have hzero : g X = 0 := Set.indicator_of_notMem hnot _
  rw [hzero] at hge
  exact (not_le_of_gt (ENNReal.toReal_pos hp.ne' hpt)) hge

lemma annealed_record_cylinder_noDrop {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Path d) (n : ℕ) (hn : 0 < n) (hr : StrictRecord ℓ f n) :
    annealedLaw ν ((fun X : Path d => fun j => X (n + j)) ⁻¹' NoDrop ℓ (f n) ∩
      pathCylinder f n) =
      annealedLaw ν (pathCylinder f n) * annealedLaw ν (NoDrop ℓ 0) := by
  by_cases hf : f 0 = 0
  · let S : Set (Lattice d) := {y | ∃ j < n, y = f j}
    let T : Set (Lattice d) := {y | dot (realPosition (f n)) ℓ ≤ dot (realPosition y) ℓ}
    have hST : Disjoint S T := by
      apply Set.disjoint_left.mpr
      rintro y ⟨j, hj, rfl⟩ hy
      exact (not_le_of_gt (hr j hj)) hy
    have hS0 : (0 : Lattice d) ∈ S := ⟨0, hn, hf.symm⟩
    have hm : @Measurable _ _ (rowSigma S) _
        (fun ω : Environment d => quenchedKernel (ω, 0) (pathCylinder f n)) := by
      apply measurable_of_row_locality _
        ((Kernel.measurable_coe _ (measurableSet_pathCylinder f n)).comp
          (measurable_id.prodMk measurable_const)) S 0 hS0
      intro ω η hωη
      exact pathCylinder_weight_locality S ω η hωη 0 f n (fun j hj => ⟨j, hj, rfl⟩)
    rw [annealed_apply ν ((measurableSet_noDrop ℓ (f n)).preimage
      (by fun_prop) |>.inter (measurableSet_pathCylinder f n))]
    simp_rw [quenched_prefix_future _ _ _ hf n (measurableSet_noDrop ℓ (f n))]
    change (∫⁻ ω, quenchedKernel (ω, 0) (pathCylinder f n) * noDropQuenched ℓ (f n) ω
      ∂environmentLaw ν) = _
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hST) hm
      (measurable_noDropQuenched_rows ℓ (f n)),
      annealed_noDrop_translation, ← annealed_apply ν (measurableSet_pathCylinder f n)]
  · have hzero : annealedLaw ν (pathCylinder f n) = 0 := by
      rw [annealed_apply ν (measurableSet_pathCylinder f n)]
      simp_rw [quenched_pathCylinder_zero _ _ _ hf n]
      simp
    rw [measure_mono_null Set.inter_subset_right hzero, hzero, zero_mul]

lemma prefixDetermined_mono {d : ℕ} {n m : ℕ} (hm : n ≤ m)
    {A : Set (Path d)} (hA : PrefixDetermined n A) : PrefixDetermined m A :=
  fun X Y hXY => hA X Y (fun j hj => hXY j (hj.trans hm))

lemma prefixDetermined_inter {d : ℕ} {n : ℕ} {A B : Set (Path d)}
    (hA : PrefixDetermined n A) (hB : PrefixDetermined n B) : PrefixDetermined n (A ∩ B) :=
  fun X Y hXY => and_congr (hA X Y hXY) (hB X Y hXY)

lemma prefixDetermined_cylinder {d : ℕ} (f : Path d) (n : ℕ) :
    PrefixDetermined n (pathCylinder f n) := by
  intro X Y hXY
  exact forall_congr' fun j => forall_congr' fun hj => by rw [hXY j hj]

open scoped Classical in
lemma prefixDetermined_inter_cylinder {d : ℕ} (A : Set (Path d)) (n : ℕ)
    (hA : PrefixDetermined n A) (f : Path d) :
    A ∩ pathCylinder f n = if f ∈ A then pathCylinder f n else ∅ := by
  classical
  split_ifs with hf
  · exact Set.inter_eq_right.mpr fun X hX => (hA X f hX).mpr hf
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro X ⟨hXA, hX⟩
    exact hf ((hA X f hX).mp hXA)

lemma annealed_record_event_noDrop {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (n : ℕ) (hn : 0 < n) (A : Set (Path d)) (hA : PrefixDetermined n A)
    (hr : ∀ X ∈ A, StrictRecord ℓ X n) :
    annealedLaw ν (A ∩ FutureNoDrop ℓ n) =
      annealedLaw ν A * annealedLaw ν (NoDrop ℓ 0) := by
  classical
  rw [measure_partition_prefix (annealedLaw ν) (A ∩ _) n,
    measure_partition_prefix (annealedLaw ν) A n, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro f
  let g := extendPrefix n f
  by_cases hg : g ∈ A
  · have he : (A ∩ FutureNoDrop ℓ n) ∩ pathCylinder g n =
        (fun X : Path d => fun j => X (n + j)) ⁻¹' NoDrop ℓ (g n) ∩ pathCylinder g n := by
      ext X
      constructor
      · rintro ⟨⟨_, hD⟩, hX⟩
        refine ⟨?_, hX⟩
        change ∀ j, dot (realPosition (g n)) ℓ ≤ dot (realPosition (X (n + j))) ℓ
        change ∀ j, dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n + j))) ℓ at hD
        simpa only [← hX n le_rfl] using hD
      · rintro ⟨hD, hX⟩
        refine ⟨⟨(hA X g hX).mpr hg, ?_⟩, hX⟩
        change ∀ j, dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n + j))) ℓ
        change ∀ j, dot (realPosition (g n)) ℓ ≤ dot (realPosition (X (n + j))) ℓ at hD
        simpa only [hX n le_rfl] using hD
    have hAc : A ∩ pathCylinder g n = pathCylinder g n := by
      rw [prefixDetermined_inter_cylinder A n hA g, ite_eq_left hg]
    rw [he, hAc]
    exact annealed_record_cylinder_noDrop ν ℓ g n hn (hr g hg)
  · have hzero : A ∩ pathCylinder g n = ∅ := by
      rw [prefixDetermined_inter_cylinder A n hA g, ite_eq_right hg]
    have he : (A ∩ FutureNoDrop ℓ n) ∩ pathCylinder g n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨⟨hXA, _⟩, hX⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hzero) X ⟨hXA, hX⟩
    rw [he, hzero, measure_empty, zero_mul]

lemma nextRecordAfter_prefix {d : ℕ} (ℓ : Vector d) (N n : ℕ) :
    PrefixDetermined n (NextRecordAfter ℓ N n) := by
  intro X Y hXY
  simp only [NextRecordAfter, Set.mem_ofPred_eq]
  apply and_congr Iff.rfl
  apply and_congr (strictRecord_congr_prefix ℓ le_rfl hXY)
  exact forall_congr' fun j => forall_congr' fun _ => forall_congr' fun hj =>
    not_congr (strictRecord_congr_prefix ℓ hj.le hXY)

lemma measurableSet_nextRecordAfter {d : ℕ} (ℓ : Vector d) (N n : ℕ) :
    MeasurableSet (NextRecordAfter ℓ N n) := by
  simp only [NextRecordAfter, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.const _).inter ((measurableSet_strictRecord ℓ n).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => (measurableSet_strictRecord ℓ j).compl))

lemma nextRecordAfter_disjoint {d : ℕ} (ℓ : Vector d) (N : ℕ) :
    Pairwise (fun m n => Disjoint (NextRecordAfter ℓ N m) (NextRecordAfter ℓ N n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro X hXm hXn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hXn.2.2 m hXm.1 h hXm.2.1
  · exact hXm.2.2 n hXn.1 h hXn.2.1

lemma exists_strictRecord_gt {d : ℕ} (ℓ : Vector d) (X : Path d)
    (ht : Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop) (N : ℕ) :
    ∃ n, N < n ∧ StrictRecord ℓ X n := by
  classical
  let b := ∑ j ∈ Finset.range (N + 1), |dot (realPosition (X j)) ℓ|
  have hb (j : ℕ) (hj : j ≤ N) : dot (realPosition (X j)) ℓ ≤ b := by
    apply (le_abs_self _).trans
    exact Finset.single_le_sum (f := fun j => |dot (realPosition (X j)) ℓ|)
      (fun k _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have he : ∃ n, b < dot (realPosition (X n)) ℓ :=
    Filter.Eventually.exists (show ∀ᶠ n : ℕ in atTop, b < dot (realPosition (X n)) ℓ from
      ht (eventually_gt_atTop b))
  refine ⟨Nat.find he, ?_, ?_⟩
  · by_contra hh
    exact (not_lt_of_ge (hb (Nat.find he) (by omega))) (Nat.find_spec he)
  · intro j hj
    exact (le_of_not_gt (Nat.find_min he hj)).trans_lt (Nat.find_spec he)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FirstWordEvent
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma exists_nextRecordAfter {d : ℕ} (ℓ : Vector d) (X : Path d)
    (ht : Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop) (N : ℕ) :
    ∃ n, X ∈ NextRecordAfter ℓ N n := by
  classical
  have he := exists_strictRecord_gt ℓ X ht N
  refine ⟨Nat.find he, (Nat.find_spec he).1, (Nat.find_spec he).2, ?_⟩
  intro j hj hjn hr
  exact Nat.find_min he hjn ⟨hj, hr⟩

lemma annealed_trueRecords_unbounded {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂annealedLaw ν, ∀ N, ∃ m, N < m ∧ TrueRecord ℓ X m := by
  classical
  let μ := annealedLaw ν
  let p := μ (NoDrop ℓ 0)
  have hp : 0 < p := noDrop_positive_of_directionallyTransient ν ℓ htrans
  apply ae_all_iff.mpr
  intro N
  let E : Set (Path d) := {X | ∃ m, N < m ∧ TrueRecord ℓ X m}
  have hE : MeasurableSet E := by
    simp only [E, Set.ofPred_exists, Set.ofPred_and]
    exact MeasurableSet.iUnion fun m =>
      (MeasurableSet.const _).inter (measurableSet_trueRecord ℓ m)
  apply ae_of_prefix_probability_lower μ E hE p hp (measure_ne_top _ _)
  intro n f
  let C := pathCylinder f n
  let A : ℕ → Set (Path d) := fun m => C ∩ NextRecordAfter ℓ (max N n) m
  have hA (m : ℕ) : MeasurableSet (A m) :=
    (measurableSet_pathCylinder f n).inter (measurableSet_nextRecordAfter ℓ _ m)
  have hdis : Pairwise (fun m k => Disjoint (A m) (A k)) := by
    intro m k hmk
    exact (nextRecordAfter_disjoint ℓ (max N n) hmk).mono
      Set.inter_subset_right Set.inter_subset_right
  have hcov : μ (⋃ m, A m) = μ C := by
    apply measure_congr
    filter_upwards [htrans] with X ht
    apply propext
    constructor
    · intro hX
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hX
      exact hm.1
    · intro hX
      obtain ⟨m, hm⟩ := exists_nextRecordAfter ℓ X ht (max N n)
      exact Set.mem_iUnion.mpr ⟨m, hX, hm⟩
  have hfac (m : ℕ) : μ (A m ∩ FutureNoDrop ℓ m) = μ (A m) * p := by
    by_cases hm : max N n < m
    · apply annealed_record_event_noDrop ν ℓ m (by omega) (A m)
      · exact prefixDetermined_inter
          (prefixDetermined_mono (by omega) (prefixDetermined_cylinder f n))
          (nextRecordAfter_prefix ℓ _ m)
      · exact fun X hX => hX.2.2.1
    · have he : A m = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        exact fun X hX => hm hX.2.1
      simp [he]
  have hdisD : Pairwise (fun m k =>
      Disjoint (A m ∩ FutureNoDrop ℓ m) (A k ∩ FutureNoDrop ℓ k)) := by
    intro m k hmk
    exact (hdis hmk).mono Set.inter_subset_left Set.inter_subset_left
  calc
    p * μ (pathCylinder f n) = (∑' m, μ (A m)) * p := by
      rw [← measure_iUnion hdis hA, hcov, mul_comm]
    _ = ∑' m, μ (A m ∩ FutureNoDrop ℓ m) := by simp_rw [hfac]; rw [ENNReal.tsum_mul_right]
    _ = μ (⋃ m, A m ∩ FutureNoDrop ℓ m) :=
      (measure_iUnion hdisD (fun m => (hA m).inter (measurableSet_futureNoDrop ℓ m))).symm
    _ ≤ μ (E ∩ pathCylinder f n) := by
      apply measure_mono
      intro X hX
      obtain ⟨m, ⟨hC, hR⟩, hD⟩ := Set.mem_iUnion.mp hX
      exact ⟨⟨m, lt_of_le_of_lt (le_max_left N n) hR.1, hR.2.1, hD⟩, hC⟩

lemma annealed_firstTrueRecord_exists {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂annealedLaw ν, ∃ n, FirstTrueRecord ℓ X n := by
  classical
  filter_upwards [annealed_trueRecords_unbounded ν ℓ htrans] with X hX
  have he := hX 0
  exact ⟨Nat.find he, (Nat.find_spec he).1, (Nat.find_spec he).2,
    fun j hj hjn hr => Nat.find_min he hjn ⟨hj, hr⟩⟩

lemma annealed_ae_of_quenched {d : ℕ} (ν : Measure (Row d))
    (P : Path d → Prop) (hP : MeasurableSet {X | P X})
    (h : ∀ ω : Environment d, ∀ᵐ X ∂quenchedKernel (ω, 0), P X) :
    ∀ᵐ X ∂annealedLaw ν, P X := by
  rw [ae_iff]
  change annealedLaw ν ({X | P X}ᶜ) = 0
  rw [annealed_apply ν hP.compl]
  simp only [show ∀ ω : Environment d, quenchedKernel (ω, 0) {X | P X}ᶜ = 0 from
    fun ω => ae_iff.mp (h ω), lintegral_zero]

lemma annealed_initial {d : ℕ} (ν : Measure (Row d)) :
    ∀ᵐ X ∂annealedLaw ν, X 0 = 0 := by
  exact annealed_ae_of_quenched ν _ (measurableSet_eq_fun (measurable_pi_apply 0)
    measurable_const) (fun ω => quenched_initial_ae (ω, 0))

lemma annealed_nearest_neighbor {d : ℕ} (ν : Measure (Row d)) :
    ∀ᵐ X ∂annealedLaw ν, ∀ n, ∃ e : Direction d, X (n + 1) = X n + step e := by
  apply annealed_ae_of_quenched ν
  · simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun e =>
      measurableSet_eq_fun (measurable_pi_apply (n + 1))
        ((measurable_pi_apply n : Measurable (fun X : Path d => X n)).add_const (step e))
  · exact fun ω => quenched_nearest_neighbor (ω, 0)

lemma measurableSet_firstWordEvent {d : ℕ} (ℓ : Vector d) (w : List (Direction d)) :
    MeasurableSet (FirstWordEvent ℓ w) :=
  (measurableSet_noDrop ℓ 0).inter ((measurableSet_wordCylinder 0 w).inter
    (measurableSet_firstTrueRecord ℓ w.length))

lemma firstWordEvent_nil {d : ℕ} (ℓ : Vector d) : FirstWordEvent ℓ [] = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  exact fun X hX => Nat.lt_irrefl 0 hX.2.2.1

lemma firstWordEvent_disjoint {d : ℕ} (ℓ : Vector d) :
    Pairwise (fun u v => Disjoint (FirstWordEvent ℓ u) (FirstWordEvent ℓ v)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro X hXu hXv
  exact huv (word_eq_of_cylinders 0 u v X hXu.2.1 hXv.2.1
    (firstTrueRecord_unique ℓ X hXu.2.2 hXv.2.2))

lemma firstWordEvent_eq {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (hw : AdmissibleTrueWord ℓ w) :
    FirstWordEvent ℓ w = (fun X : Path d => fun j => X (w.length + j) -
      wordPath 0 w w.length) ⁻¹' NoDrop ℓ 0 ∩ wordCylinder 0 w := by
  ext X
  constructor
  · rintro ⟨hD, hcy, hT⟩
    exact ⟨((firstTrueWord_characterization ℓ w X hcy).mp ⟨hD, hT⟩).2, hcy⟩
  · rintro ⟨hD, hcy⟩
    have hh := (firstTrueWord_characterization ℓ w X hcy).mpr ⟨hw, hD⟩
    exact ⟨hh.1, hcy, hh.2⟩

lemma conditionedLaw_absolutelyContinuous {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) :
    conditionedLaw ν ℓ ≪ annealedLaw ν :=
  (Measure.AbsolutelyContinuous.smul_left (Measure.absolutelyContinuous_restrict) _)

lemma conditionedLaw_noDrop {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ NoDrop ℓ 0 := by
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_noDrop ℓ 0)) _

lemma conditioned_firstWord_exists {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, ∃ w, X ∈ FirstWordEvent ℓ w := by
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  filter_upwards [conditionedLaw_noDrop ν ℓ, hac.ae_le (annealed_initial ν),
    hac.ae_le (annealed_nearest_neighbor ν), hac.ae_le (annealed_firstTrueRecord_exists ν ℓ htrans)]
    with X hD h0 hNN hT
  obtain ⟨n, hn⟩ := hT
  obtain ⟨w, hw, hcy⟩ := exists_word_prefix X hNN n
  exact ⟨w, hD, by simpa only [h0] using hcy, hw.symm ▸ hn⟩

lemma firstWord_eq_iff {d : ℕ} (ℓ : Vector d) (X : Path d) (w : List (Direction d))
    (hw : w ≠ []) : firstWord ℓ X = w ↔ X ∈ FirstWordEvent ℓ w := by
  classical
  unfold firstWord
  split_ifs with h
  · constructor
    · intro he
      exact he ▸ h.choose_spec
    · intro hX
      by_contra hne
      exact (Set.disjoint_left.mp (firstWordEvent_disjoint ℓ hne)) h.choose_spec hX
  · simp only [eq_comm (a := ([] : List (Direction d))), hw, false_iff]
    exact fun hX => h ⟨w, hX⟩

lemma firstWord_nil_iff {d : ℕ} (ℓ : Vector d) (X : Path d) :
    firstWord ℓ X = [] ↔ ¬ ∃ w, X ∈ FirstWordEvent ℓ w := by
  classical
  unfold firstWord
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    intro he
    have := h.choose_spec
    rw [he, firstWordEvent_nil] at this
    exact this
  · simp [h]

lemma measurable_firstWord {d : ℕ} (ℓ : Vector d) : Measurable (firstWord ℓ) := by
  classical
  apply measurable_to_countable'
  intro w
  by_cases hw : w = []
  · subst w
    have he : firstWord ℓ ⁻¹' {[]} = (⋃ w, FirstWordEvent ℓ w)ᶜ := by
      ext X
      simp only [Set.mem_preimage, Set.mem_singleton_iff, firstWord_nil_iff,
        Set.mem_compl_iff, Set.mem_iUnion]
    rw [he]
    exact (MeasurableSet.iUnion (measurableSet_firstWordEvent ℓ)).compl
  · have he : firstWord ℓ ⁻¹' {w} = FirstWordEvent ℓ w := by
      ext X
      exact firstWord_eq_iff ℓ X w hw
    rw [he]
    exact measurableSet_firstWordEvent ℓ w

lemma conditionedLaw_inter_noDrop {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    conditionedLaw ν ℓ (A ∩ NoDrop ℓ 0) = conditionedLaw ν ℓ A := by
  simp only [conditionedLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA, Measure.restrict_apply (hA.inter (measurableSet_noDrop ℓ 0)),
    Set.inter_self, Set.inter_assoc]

lemma conditionedLaw_noDrop_mass {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    conditionedLaw ν ℓ (NoDrop ℓ 0) = 1 := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  simpa only [Set.univ_inter, measure_univ] using
    conditionedLaw_inter_noDrop ν ℓ Set.univ MeasurableSet.univ

lemma conditioned_firstWordEvent_mass {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (w : List (Direction d)) (hw : AdmissibleTrueWord ℓ w) :
    conditionedLaw ν ℓ (FirstWordEvent ℓ w) = annealedLaw ν (wordCylinder 0 w) := by
  rw [firstWordEvent_eq ℓ w hw, conditioned_true_word_factor ν ℓ w hw _
    (measurableSet_noDrop ℓ 0) (Set.Subset.refl _), conditionedLaw_noDrop_mass ν ℓ hp, mul_one]

lemma firstWordEvent_empty_of_not_admissible {d : ℕ} (ℓ : Vector d)
    (w : List (Direction d)) (hw : ¬ AdmissibleTrueWord ℓ w) : FirstWordEvent ℓ w = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  exact fun X hX => hw (((firstTrueWord_characterization ℓ w X hX.2.1).mp ⟨hX.1, hX.2.2⟩).1)

lemma conditioned_firstWordEvent_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (w : List (Direction d)) (A : Set (Path d)) (hA : MeasurableSet A) :
    conditionedLaw ν ℓ (FirstWordEvent ℓ w ∩ (fun X : Path d => fun j =>
      X (w.length + j) - wordPath 0 w w.length) ⁻¹' A) =
      conditionedLaw ν ℓ (FirstWordEvent ℓ w) * conditionedLaw ν ℓ A := by
  classical
  by_cases hw : AdmissibleTrueWord ℓ w
  · have he : FirstWordEvent ℓ w ∩ (fun X : Path d => fun j =>
        X (w.length + j) - wordPath 0 w w.length) ⁻¹' A =
        (fun X : Path d => fun j => X (w.length + j) - wordPath 0 w w.length) ⁻¹'
          (A ∩ NoDrop ℓ 0) ∩ wordCylinder 0 w := by
      rw [firstWordEvent_eq ℓ w hw]
      ext X
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [he, conditioned_true_word_factor ν ℓ w hw _
      (hA.inter (measurableSet_noDrop ℓ 0)) Set.inter_subset_right,
      conditionedLaw_inter_noDrop ν ℓ A hA, conditioned_firstWordEvent_mass ν ℓ hp w hw]
  · simp only [firstWordEvent_empty_of_not_admissible ℓ w hw, Set.empty_inter,
      measure_empty, zero_mul]

lemma measurable_renewSuffix {d : ℕ} (ℓ : Vector d) : Measurable (renewSuffix ℓ) := by
  apply Measurable.of_eval
  intro j
  have hf : Measurable (fun X : Path d => (firstWord ℓ X).length) :=
    (measurable_of_countable List.length).comp (measurable_firstWord ℓ)
  have heval : Measurable (fun p : Path d × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  exact (heval.comp (measurable_id.prodMk (hf.add_const j))).sub
    (heval.comp (measurable_id.prodMk hf))

lemma renewSuffix_on_firstWordEvent {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (X : Path d) (hX : X ∈ FirstWordEvent ℓ w) :
    renewSuffix ℓ X = fun j => X (w.length + j) - wordPath 0 w w.length := by
  have hw : w ≠ [] := by
    intro he
    rw [he, firstWordEvent_nil] at hX
    exact hX
  unfold renewSuffix
  rw [(firstWord_eq_iff ℓ X w hw).mpr hX, hX.2.1 w.length le_rfl]

lemma conditioned_firstWord_fiber_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (w : List (Direction d)) :
    firstWord ℓ ⁻¹' {w} =ᵐ[conditionedLaw ν ℓ] FirstWordEvent ℓ w := by
  classical
  by_cases hw : w = []
  · subst w
    filter_upwards [conditioned_firstWord_exists ν ℓ htrans] with X hX
    apply propext
    change firstWord ℓ X = [] ↔ X ∈ FirstWordEvent ℓ []
    rw [firstWord_nil_iff, firstWordEvent_nil]
    simp only [hX, not_true_eq_false, Set.mem_empty_iff_false]
  · exact Filter.Eventually.of_forall fun X => propext (firstWord_eq_iff ℓ X w hw)

lemma conditioned_firstWord_fiber_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (w : List (Direction d)) (A : Set (Path d)) (hA : MeasurableSet A) :
    conditionedLaw ν ℓ (firstWord ℓ ⁻¹' {w} ∩ renewSuffix ℓ ⁻¹' A) =
      conditionedLaw ν ℓ (firstWord ℓ ⁻¹' {w}) * conditionedLaw ν ℓ A := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hcy := conditioned_firstWord_fiber_ae ν ℓ htrans w
  have hE : (firstWord ℓ ⁻¹' {w} ∩ renewSuffix ℓ ⁻¹' A : Set (Path d)) =ᵐ[conditionedLaw ν ℓ]
      (FirstWordEvent ℓ w ∩ renewSuffix ℓ ⁻¹' A : Set (Path d)) :=
    hcy.inter (Filter.Eventually.of_forall fun _ => rfl)
  rw [measure_congr hE, measure_congr hcy]
  have he : FirstWordEvent ℓ w ∩ renewSuffix ℓ ⁻¹' A =
      FirstWordEvent ℓ w ∩ (fun X : Path d => fun j => X (w.length + j) -
        wordPath 0 w w.length) ⁻¹' A := by
    ext X
    by_cases hX : X ∈ FirstWordEvent ℓ w
    · simp only [Set.mem_inter_iff, Set.mem_preimage, hX, true_and,
        renewSuffix_on_firstWordEvent ℓ w X hX]
    · simp only [Set.mem_inter_iff, hX, false_and]
  rw [he]
  exact conditioned_firstWordEvent_factor ν ℓ hp w A hA

lemma renewSuffix_preserves_conditioned {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    MeasurePreserving (renewSuffix ℓ) (conditionedLaw ν ℓ) (conditionedLaw ν ℓ) := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  refine ⟨measurable_renewSuffix ℓ, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_renewSuffix ℓ) hA]
  have hpart : ∀ B : Set (Path d), MeasurableSet B → conditionedLaw ν ℓ B =
      ∑' w : List (Direction d), conditionedLaw ν ℓ (firstWord ℓ ⁻¹' {w} ∩ B) := by
    intro B hB
    have he : (⋃ w : List (Direction d), firstWord ℓ ⁻¹' {w} ∩ B) = B := by
      ext X
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun ⟨w, _, hX⟩ => hX, fun hX => ⟨firstWord ℓ X, rfl, hX⟩⟩
    rw [← he]
    conv_rhs => arg 1; ext w; rw [he]
    exact measure_iUnion (fun u v huv => ((Set.disjoint_singleton.mpr huv).preimage
      (firstWord ℓ)).mono Set.inter_subset_left Set.inter_subset_left)
      (fun w => ((measurable_firstWord ℓ) (measurableSet_singleton w)).inter hB)
  have hsum : (∑' w : List (Direction d), conditionedLaw ν ℓ (firstWord ℓ ⁻¹' {w})) = 1 := by
    simpa only [Set.inter_univ, measure_univ] using (hpart Set.univ MeasurableSet.univ).symm
  rw [hpart (renewSuffix ℓ ⁻¹' A) (hA.preimage (measurable_renewSuffix ℓ))]
  simp_rw [conditioned_firstWord_fiber_factor ν ℓ htrans _ A hA]
  rw [ENNReal.tsum_mul_right, hsum, one_mul]

lemma measure_preimage_partition {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] (μ : Measure α) (f : α → β)
    (hf : Measurable f) (B : Set β) (hB : MeasurableSet B) (C : Set α) :
    μ (f ⁻¹' B ∩ C) = ∑' b : B, μ (f ⁻¹' {b.1} ∩ C) := by
  have h := tsum_measure_preimage_singleton (μ := μ.restrict C) (s := B)
    (Set.to_countable B) (f := f) (fun b _ => hf (measurableSet_singleton b))
  simpa only [Measure.restrict_apply (hf hB),
    Measure.restrict_apply (hf (measurableSet_singleton _))] using h.symm

lemma firstWord_indep_renewSuffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    IndepFun (firstWord ℓ) (renewSuffix ℓ) (conditionedLaw ν ℓ) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro B A hB hA
  have hT := renewSuffix_preserves_conditioned ν ℓ htrans
  rw [hT.measure_preimage hA.nullMeasurableSet,
    measure_preimage_partition _ _ (measurable_firstWord ℓ) B hB]
  simp_rw [conditioned_firstWord_fiber_factor ν ℓ htrans _ A hA]
  rw [ENNReal.tsum_mul_right]
  have hsum := measure_preimage_partition (conditionedLaw ν ℓ) (firstWord ℓ)
    (measurable_firstWord ℓ) B hB Set.univ
  simpa only [Set.inter_univ] using congrArg (fun x => x * conditionedLaw ν ℓ A) hsum.symm

lemma independent_iterated_symbols {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (F : α → β) (T : α → α)
    (hF : Measurable F) (hT : MeasurePreserving T μ μ) (hFT : IndepFun F T μ) :
    iIndepFun (fun n : ℕ => fun x => F (T^[n] x)) μ := by
  classical
  have hprefix : ∀ n : ℕ, ∀ (B : ℕ → Set β), (∀ i, MeasurableSet (B i)) →
      μ {x | ∀ i < n, F (T^[i] x) ∈ B i} = ∏ i ∈ Finset.range n, μ (F ⁻¹' B i) := by
    intro n
    induction n with
    | zero => intro B hB; simp
    | succ n ih =>
      intro B hB
      let E : Set α := {x | ∀ i < n, F (T^[i] x) ∈ B (i + 1)}
      have hE : MeasurableSet E := by
        simp only [E, Set.ofPred_forall]
        exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
          (hB (i + 1)).preimage (hF.comp (hT.iterate i).measurable)
      have he : {x | ∀ i < n + 1, F (T^[i] x) ∈ B i} = F ⁻¹' B 0 ∩ T ⁻¹' E := by
        ext x
        constructor
        · intro hx
          refine ⟨by simpa using hx 0 (by omega), ?_⟩
          intro i hi
          simpa only [Function.iterate_succ_apply] using hx (i + 1) (by omega)
        · rintro ⟨h0, hs⟩ i hi
          cases i with
          | zero => simpa using h0
          | succ i =>
            simpa only [Function.iterate_succ_apply] using hs i (by omega)
      rw [he, hFT.measure_inter_preimage_eq_mul _ _ (hB 0) hE,
        hT.measure_preimage hE.nullMeasurableSet]
      change μ (F ⁻¹' B 0) * μ {x | ∀ i < n, F (T^[i] x) ∈ B (i + 1)} = _
      rw [ih (fun i => B (i + 1)) (fun i => hB (i + 1)),
        Finset.prod_range_succ', mul_comm]
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S B hB
  let N := S.sup id + 1
  have hS : S ⊆ Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  let C : ℕ → Set β := fun i => if i ∈ S then B i else Set.univ
  have hC : ∀ i, MeasurableSet (C i) := by
    intro i
    by_cases hi : i ∈ S
    · simpa only [C, ite_eq_left hi] using hB i hi
    · simp only [C, ite_eq_right hi]; exact MeasurableSet.univ
  have he : (⋂ i ∈ S, (fun x => F (T^[i] x)) ⁻¹' B i) =
      {x | ∀ i < N, F (T^[i] x) ∈ C i} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · intro hx i _
      by_cases hi : i ∈ S
      · simpa only [C, ite_eq_left hi] using hx i hi
      · simp only [C, ite_eq_right hi, Set.mem_univ]
    · intro hx i hi
      simpa only [C, ite_eq_left hi] using hx i (Finset.mem_range.mp (hS hi))
  rw [he, hprefix N C hC]
  calc
    (∏ i ∈ Finset.range N, μ (F ⁻¹' C i)) = ∏ i ∈ S, μ (F ⁻¹' C i) := by
      symm
      apply Finset.prod_subset hS
      intro i _ hi
      simp only [C, ite_eq_right hi, Set.preimage_univ, measure_univ]
    _ = ∏ i ∈ S, μ ((fun x => F (T^[i] x)) ⁻¹' B i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [C, ite_eq_left hi]
      exact ((hT.iterate i).measure_preimage ((hB i hi).preimage hF).nullMeasurableSet).symm

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_RegenerationWords
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma identDistrib_iterated_symbol {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (F : α → β) (T : α → α)
    (hF : Measurable F) (hT : MeasurePreserving T μ μ) (n : ℕ) :
    IdentDistrib (fun x => F (T^[n] x)) F μ μ := by
  refine ⟨(hF.comp (hT.iterate n).measurable).aemeasurable, hF.aemeasurable, ?_⟩
  change μ.map (F ∘ T^[n]) = μ.map F
  rw [← Measure.map_map hF (hT.iterate n).measurable, (hT.iterate n).map_eq]

lemma measurable_regenerationWord {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    Measurable (fun X : Path d => regenerationWords ℓ X n) :=
  (measurable_firstWord ℓ).comp ((measurable_renewSuffix ℓ).iterate n)

lemma regenerationWords_independent {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    iIndepFun (fun n X => regenerationWords ℓ X n) (conditionedLaw ν ℓ) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  exact independent_iterated_symbols _ _ _ (measurable_firstWord ℓ)
    (renewSuffix_preserves_conditioned ν ℓ htrans) (firstWord_indep_renewSuffix ν ℓ htrans)

lemma regenerationWords_identDistrib {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (n : ℕ) :
    IdentDistrib (fun X => regenerationWords ℓ X n) (firstWord ℓ)
      (conditionedLaw ν ℓ) (conditionedLaw ν ℓ) :=
  identDistrib_iterated_symbol _ _ _ (measurable_firstWord ℓ)
    (renewSuffix_preserves_conditioned ν ℓ htrans) n

lemma firstWordEvent_self {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hX : ∃ w, X ∈ FirstWordEvent ℓ w) : X ∈ FirstWordEvent ℓ (firstWord ℓ X) := by
  classical
  simpa only [firstWord, dite_eq_left hX] using hX.choose_spec

lemma regenerationTimes_succ {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) :
    regenerationTimes ℓ X (n + 1) = regenerationTimes ℓ X n +
      (regenerationWords ℓ X n).length := by simp [regenerationTimes, Finset.sum_range_succ]

lemma iterate_renewSuffix_eq {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0) (n j : ℕ) :
    ((renewSuffix ℓ)^[n] X) j = X (regenerationTimes ℓ X n + j) -
      X (regenerationTimes ℓ X n) := by
  induction n generalizing j with
  | zero => simp [h0]
  | succ n ih =>
    rw [Function.iterate_succ_apply', renewSuffix, ih, ih, regenerationTimes_succ]
    change X (regenerationTimes ℓ X n + ((regenerationWords ℓ X n).length + j)) -
      X (regenerationTimes ℓ X n) - (X (regenerationTimes ℓ X n +
      (regenerationWords ℓ X n).length) - X (regenerationTimes ℓ X n)) = _
    rw [Nat.add_assoc]
    abel

lemma strictRecord_suffix_iff {d : ℕ} (ℓ : Vector d) (X : Path d) {n j : ℕ}
    (hn : StrictRecord ℓ X n) (hj : 0 < j) :
    StrictRecord ℓ (fun k => X (n + k) - X n) j ↔ StrictRecord ℓ X (n + j) := by
  simp only [StrictRecord, dot_realPosition_sub, sub_lt_sub_iff_right]
  constructor
  · intro h k hk
    by_cases hkn : k < n
    · exact (hn k hkn).trans (by simpa using h 0 hj)
    · have hle : n ≤ k := by omega
      simpa only [Nat.add_sub_of_le hle] using h (k - n) (by omega)
  · intro h k hk
    exact h (n + k) (by omega)

lemma trueRecord_suffix_iff {d : ℕ} (ℓ : Vector d) (X : Path d) {n j : ℕ}
    (hn : StrictRecord ℓ X n) (hj : 0 < j) :
    TrueRecord ℓ (fun k => X (n + k) - X n) j ↔ TrueRecord ℓ X (n + j) := by
  simp only [TrueRecord, strictRecord_suffix_iff ℓ X hn hj, FutureNoDrop,
    Set.mem_ofPred_eq, dot_realPosition_sub, sub_le_sub_iff_right, Nat.add_assoc]

lemma conditioned_all_firstWords {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ n, ((renewSuffix ℓ)^[n] X) ∈
      FirstWordEvent ℓ (regenerationWords ℓ X n) := by
  apply ae_all_iff.mpr
  intro n
  have h := ((renewSuffix_preserves_conditioned ν ℓ htrans).iterate n).quasiMeasurePreserving.ae
    (conditioned_firstWord_exists ν ℓ htrans)
  filter_upwards [h] with X hX
  exact firstWordEvent_self ℓ _ hX

lemma regenerationTimes_strictMono {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n)) :
    StrictMono (regenerationTimes ℓ X) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [regenerationTimes_succ]
  exact Nat.lt_add_of_pos_right (hX n).2.2.1

lemma regenerationTimes_true {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n)) :
    ∀ n, TrueRecord ℓ X (regenerationTimes ℓ X n) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun j hj => by simp at hj, ?_⟩
    have hD := (hX 0).1
    change X ∈ NoDrop ℓ 0 at hD
    change ∀ j, dot (realPosition (X 0)) ℓ ≤ dot (realPosition (X (0 + j))) ℓ
    simpa only [Nat.zero_add, h0, NoDrop, Set.mem_ofPred_eq] using hD
  | succ n ih =>
    have ht := (hX n).2.2.2.1
    have hj := (hX n).2.2.1
    rw [show (renewSuffix ℓ)^[n] X = _ from funext (iterate_renewSuffix_eq ℓ X h0 n)] at ht
    rw [regenerationTimes_succ]
    exact (trueRecord_suffix_iff ℓ X ih.1 hj).mp ht

lemma regenerationTimes_no_true_between {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (n j : ℕ) (hj : regenerationTimes ℓ X n < j) (hj' : j < regenerationTimes ℓ X (n+1)) :
    ¬ TrueRecord ℓ X j := by
  intro ht
  have hn := regenerationTimes_true ℓ X h0 hX n
  have hs := (trueRecord_suffix_iff ℓ X hn.1 (show 0 < j - regenerationTimes ℓ X n by omega)).mpr
    (show TrueRecord ℓ X (regenerationTimes ℓ X n + (j - regenerationTimes ℓ X n)) by
      simpa only [Nat.add_sub_of_le hj.le] using ht)
  have he : (fun k => X (regenerationTimes ℓ X n + k) - X (regenerationTimes ℓ X n)) =
      (renewSuffix ℓ)^[n] X := funext fun k => (iterate_renewSuffix_eq ℓ X h0 n k).symm
  rw [he] at hs
  exact (hX n).2.2.2.2 _ (by omega)
    (by rw [regenerationTimes_succ] at hj'; omega) hs

lemma recordCount_add {d : ℕ} (ℓ : Vector d) (X : Path d) {n : ℕ}
    (hn : StrictRecord ℓ X n) (m : ℕ) :
    recordCount ℓ X (n + m) = recordCount ℓ X n +
      recordCount ℓ (fun j => X (n + j) - X n) m := by
  classical
  rw [recordCount, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.add_assoc, strictRecord_suffix_iff ℓ X hn (Nat.succ_pos j)]

lemma recordCount_regenerationTimes {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n)) (n : ℕ) :
    recordCount ℓ X (regenerationTimes ℓ X n) =
      ∑ j ∈ Finset.range n, wordRecordCount ℓ (regenerationWords ℓ X j) := by
  induction n with
  | zero => simp [recordCount]
  | succ n ih =>
    rw [regenerationTimes_succ, recordCount_add ℓ X
      (regenerationTimes_true ℓ X h0 hX n).1, ih, Finset.sum_range_succ]
    congr 1
    have he := recordCount_congr_prefix ℓ (hX n).2.1
    rw [show (renewSuffix ℓ)^[n] X = _ from funext (iterate_renewSuffix_eq ℓ X h0 n)] at he
    exact he

lemma wordRecordCount_positive {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (hw : AdmissibleTrueWord ℓ w) : 0 < wordRecordCount ℓ w := by
  classical
  have hn := hw.1
  have hr : StrictRecord ℓ (wordPath 0 w) w.length := fun j hj => (hw.2.1 j hj).2
  have he : w.length - 1 + 1 = w.length := by omega
  have hterm : (if StrictRecord ℓ (wordPath 0 w) (w.length - 1 + 1) then 1 else 0 : ℕ) = 1 := by
    rw [he, ite_eq_left hr]
  have hle := Finset.single_le_sum (f := fun j =>
    (if StrictRecord ℓ (wordPath 0 w) (j+1) then 1 else 0 : ℕ))
    (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr (show w.length - 1 < w.length by omega))
  rw [hterm] at hle
  exact hle

lemma recordCount_unbounded {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hX : Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop) :
    ∀ r, ∃ n, r ≤ recordCount ℓ X n := by
  intro r
  induction r with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ r ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hnm, hm⟩ := exists_strictRecord_gt ℓ X hX n
    exact ⟨m, Nat.succ_le_of_lt (hn.trans_lt (recordCount_lt_of_strictRecord ℓ X hnm hm))⟩

lemma exists_record_at_index {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hX : Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop) {r : ℕ} (hr : 0 < r) :
    ∃ n, 0 < n ∧ StrictRecord ℓ X n ∧ recordCount ℓ X n = r := by
  classical
  let n := Nat.find (recordCount_unbounded ℓ X hX r)
  have hn : r ≤ recordCount ℓ X n := Nat.find_spec (recordCount_unbounded ℓ X hX r)
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    simp only [he, recordCount_zero] at hn
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn0)
  have hklt : recordCount ℓ X k < r := Nat.lt_of_not_ge
    (Nat.find_min (recordCount_unbounded ℓ X hX r) (by omega))
  have hrec : StrictRecord ℓ X n := by
    by_contra hrec
    rw [hk, recordCount_succ, ite_eq_right (by simpa only [hk, Nat.succ_eq_add_one] using hrec), Nat.add_zero] at hn
    omega
  refine ⟨n, hn0, hrec, ?_⟩
  rw [hk, recordCount_succ, ite_eq_left (by simpa only [hk, Nat.succ_eq_add_one] using hrec)]
  rw [hk, recordCount_succ, ite_eq_left (by simpa only [hk, Nat.succ_eq_add_one] using hrec)] at hn
  omega

lemma recordIndexPrefix_noDrop {d : ℕ} (ℓ : Vector d) (r n : ℕ) :
    RecordIndexPrefix ℓ r n ∩ FutureNoDrop ℓ n ⊆ NoDrop ℓ 0 := by
  intro X ⟨hX, hD⟩ j
  by_cases hj : j ≤ n
  · exact hX.2.2.2 j hj
  · have hnj : n ≤ j := by omega
    have h := hD (j - n)
    change dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n + (j-n)))) ℓ at h
    rw [Nat.add_sub_of_le hnj] at h
    exact (hX.2.2.2 n le_rfl).trans h

lemma conditioned_recordIndexPrefix_true {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (r n : ℕ) :
    conditionedLaw ν ℓ (RecordIndexPrefix ℓ r n ∩ FutureNoDrop ℓ n) =
      annealedLaw ν (RecordIndexPrefix ℓ r n) := by
  by_cases hn : 0 < n
  · rw [conditionedLaw, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply ((measurableSet_recordIndexPrefix ℓ r n).inter
        (measurableSet_futureNoDrop ℓ n)),
      Set.inter_eq_left.mpr (recordIndexPrefix_noDrop ℓ r n),
      annealed_record_event_noDrop ν ℓ n hn _ (recordIndexPrefix_prefix ℓ r n)
        (fun X hX => hX.2.1), mul_comm _ (annealedLaw ν _ * _),
      mul_assoc, ENNReal.mul_inv_cancel hp (measure_ne_top _ _), mul_one]
  · have he : RecordIndexPrefix ℓ r n = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun X hX => hn hX.1)
    simp only [he, Set.empty_inter, measure_empty]

lemma conditioned_true_at_index_lower {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) {r : ℕ} (hr : 0 < r) :
    annealedLaw ν (NoDrop ℓ 0) ≤ conditionedLaw ν ℓ
      {X | ∃ n, 0 < n ∧ TrueRecord ℓ X n ∧ recordCount ℓ X n = r} := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hsub : NoDrop ℓ 0 ≤ᵐ[annealedLaw ν] ⋃ n, RecordIndexPrefix ℓ r n := by
    filter_upwards [htrans] with X hX hD
    obtain ⟨n, hn, hrec, hcount⟩ := exists_record_at_index ℓ X hX hr
    exact Set.mem_iUnion.mpr ⟨n, hn, hrec, hcount, fun j _ => hD j⟩
  calc
    annealedLaw ν (NoDrop ℓ 0) ≤ annealedLaw ν (⋃ n, RecordIndexPrefix ℓ r n) := measure_mono_ae hsub
    _ = ∑' n, annealedLaw ν (RecordIndexPrefix ℓ r n) :=
      measure_iUnion (recordIndexPrefix_disjoint ℓ r) (measurableSet_recordIndexPrefix ℓ r)
    _ = ∑' n, conditionedLaw ν ℓ (RecordIndexPrefix ℓ r n ∩ FutureNoDrop ℓ n) := by
      simp_rw [conditioned_recordIndexPrefix_true ν ℓ hp]
    _ = conditionedLaw ν ℓ (⋃ n, RecordIndexPrefix ℓ r n ∩ FutureNoDrop ℓ n) := by
      symm
      exact measure_iUnion (fun m n hmn => (recordIndexPrefix_disjoint ℓ r hmn).mono
        Set.inter_subset_left Set.inter_subset_left) (fun n =>
        (measurableSet_recordIndexPrefix ℓ r n).inter (measurableSet_futureNoDrop ℓ n))
    _ ≤ _ := measure_mono (by
      rintro X ⟨s, ⟨n, rfl⟩, hX, hD⟩
      exact ⟨n, hX.1, ⟨hX.2.1, hD⟩, hX.2.2.1⟩)

lemma renewal_truncated_sum_le (s : ℕ → ℕ) (H K n : ℕ) :
    (∑ i ∈ Finset.range n, if (∑ j ∈ Finset.range i, s j) ≤ H then min (s i) K else 0) ≤ H + K := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hn : (∑ j ∈ Finset.range n, s j) ≤ H
    · rw [ite_eq_left hn]
      apply (Nat.add_le_add ?_ (min_le_right _ _)).trans (Nat.add_le_add_right hn K)
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact min_le_left _ _
      · exact Nat.zero_le _
    · simpa only [ite_eq_right hn, Nat.add_zero] using ih

lemma renewal_wald_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (S : ℕ → α → ℕ) (hS : ∀ i, Measurable (S i)) (hind : iIndepFun S μ)
    (hident : ∀ i, IdentDistrib (S i) (S 0) μ μ) (H K : ℕ) :
    (∑ i ∈ Finset.range (H+1), μ.real {x | (∑ j ∈ Finset.range i, S j x) ≤ H}) *
      (∫ x, ((min (S 0 x) K : ℕ) : ℝ) ∂μ) ≤ (H : ℝ) + K := by
  classical
  let F : ℕ → α → ℝ := fun i x => if (∑ j ∈ Finset.range i, S j x) ≤ H then
    ((min (S i x) K : ℕ) : ℝ) else 0
  have hFmeas (i : ℕ) : Measurable (F i) :=
    Measurable.ite (measurableSet_le (Finset.measurable_fun_sum _ (fun j _ => hS j)) measurable_const)
      ((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp ((hS i).min measurable_const)) measurable_const
  have hFint (i : ℕ) : Integrable (F i) μ :=
    integrable_of_nonneg_bound μ (hFmeas i) (B := K) fun x => by
      dsimp [F]
      split_ifs
      · exact ⟨Nat.cast_nonneg _, by exact_mod_cast min_le_right (S i x) K⟩
      · exact ⟨le_rfl, Nat.cast_nonneg _⟩
  have hbound : (∫ x, ∑ i ∈ Finset.range (H+1), F i x ∂μ) ≤ (H : ℝ) + K := by
    calc
      _ ≤ ∫ _ : α, (H : ℝ) + K ∂μ := integral_mono
        (integrable_finsetSum _ (fun i _ => hFint i)) (integrable_const _) fun x => by
          have hh := renewal_truncated_sum_le (fun i => S i x) H K (H+1)
          have he : (∑ i ∈ Finset.range (H+1), F i x) =
              ((∑ i ∈ Finset.range (H+1), if (∑ j ∈ Finset.range i, S j x) ≤ H
                then min (S i x) K else 0 : ℕ) : ℝ) := by
            simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, F, Nat.cast_min]
          rw [he]
          simpa only [Nat.cast_add] using (Nat.cast_le (α := ℝ)).mpr hh
      _ = _ := by simp
  have hfactor (i : ℕ) : (∫ x, F i x ∂μ) =
      μ.real {x | (∑ j ∈ Finset.range i, S j x) ≤ H} *
        ∫ x, ((min (S 0 x) K : ℕ) : ℝ) ∂μ := by
    let A : ℕ → ℝ := fun t => if t ≤ H then 1 else 0
    let B : ℕ → ℝ := fun t => ((min t K : ℕ) : ℝ)
    have hsummeas : Measurable (fun x => ∑ j ∈ Finset.range i, S j x) :=
      Finset.measurable_fun_sum _ (fun j _ => hS j)
    have hi := (hind.indepFun_finsetSum_of_notMem hS (Finset.notMem_range_self (n := i))).comp
      (measurable_of_countable A) (measurable_of_countable B)
    have hi' : IndepFun (fun x => A (∑ j ∈ Finset.range i, S j x)) (fun x => B (S i x)) μ := by
      have heq : (∑ j ∈ Finset.range i, S j) = (fun x => ∑ j ∈ Finset.range i, S j x) := by
        funext x
        simp only [Finset.sum_apply]
      rw [heq] at hi
      exact hi
    have he : F i = fun x => A (∑ j ∈ Finset.range i, S j x) * B (S i x) := by
      funext x
      simp only [F, A, B]
      split_ifs <;> simp
    rw [he, hi'.integral_fun_mul_eq_mul_integral
      ((measurable_of_countable A).comp hsummeas).aestronglyMeasurable
      ((measurable_of_countable B).comp (hS i)).aestronglyMeasurable]
    have hA : (fun x => A (∑ j ∈ Finset.range i, S j x)) =
        {x | (∑ j ∈ Finset.range i, S j x) ≤ H}.indicator (fun _ => (1 : ℝ)) := by
      funext x
      simp only [A, Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hA, integral_indicator_const (1 : ℝ) (measurableSet_le hsummeas measurable_const)]
    simp only [smul_eq_mul, mul_one]
    exact congrArg (fun y => μ.real {x | (∑ j ∈ Finset.range i, S j x) ≤ H} * y)
      ((hident i).comp (measurable_of_countable B)).integral_eq
  rw [integral_finsetSum _ (fun i _ => hFint i)] at hbound
  simp_rw [hfactor] at hbound
  simpa only [Finset.sum_mul] using hbound

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_WordHeightGain
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma renewal_occupation_lower {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (T : ℕ → α → ℕ) (hT : ∀ i, Measurable (T i))
    (hbig : ∀ᵐ x ∂μ, ∀ i, i ≤ T i x) {p : ℝ}
    (hlow : ∀ r, 0 < r → p ≤ μ.real {x | ∃ i, T i x = r}) (H : ℕ) :
    (H : ℝ) * p ≤ ∑ i ∈ Finset.range (H+1), μ.real {x | T i x ≤ H} := by
  classical
  have hlow' (r : ℕ) (hr : r ∈ Finset.Icc 1 H) :
      p ≤ ∑ i ∈ Finset.range (H+1), μ.real {x | T i x = r} := by
    have hsub : {x | ∃ i, T i x = r} ≤ᵐ[μ]
        ⋃ i ∈ Finset.range (H+1), {x | T i x = r} := by
      filter_upwards [hbig] with x hx hi
      obtain ⟨i, hi⟩ := hi
      refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr ?_, hi⟩⟩
      have hh := hx i
      have hrH := (Finset.mem_Icc.mp hr).2
      omega
    exact (hlow r (by have := (Finset.mem_Icc.mp hr).1; omega)).trans
      ((ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans
        (measureReal_biUnion_finset_le _ _))
  calc
    (H : ℝ) * p = ∑ r ∈ Finset.Icc 1 H, p := by simp
    _ ≤ ∑ r ∈ Finset.Icc 1 H, ∑ i ∈ Finset.range (H+1), μ.real {x | T i x = r} :=
      Finset.sum_le_sum hlow'
    _ = ∑ i ∈ Finset.range (H+1), ∑ r ∈ Finset.Icc 1 H, μ.real {x | T i x = r} :=
      Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have he := sum_measureReal_preimage_singleton (μ := μ) (Finset.Icc 1 H)
        (fun r _ => (hT i) (measurableSet_singleton r))
      change (∑ r ∈ Finset.Icc 1 H, μ.real (T i ⁻¹' {r})) ≤ _
      rw [he]
      exact measureReal_mono (fun x hx => show T i x ≤ H from (Finset.mem_Icc.mp hx).2)

lemma nat_integrable_of_truncated_mean_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : α → ℕ) (hS : Measurable S) {B : ℝ}
    (hB : ∀ K : ℕ, (∫ x, ((min (S x) K : ℕ) : ℝ) ∂μ) ≤ B) :
    Integrable (fun x => (S x : ℝ)) μ ∧ (∫ x, (S x : ℝ) ∂μ) ≤ B := by
  have hKint (K : ℕ) : Integrable (fun x => ((min (S x) K : ℕ) : ℝ)) μ :=
    integrable_of_nonneg_bound μ ((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp (hS.min measurable_const)) (B := K)
      fun x => ⟨Nat.cast_nonneg _, by exact_mod_cast min_le_right (S x) K⟩
  have hB0 : 0 ≤ B := by simpa only [Nat.min_zero, Nat.cast_zero, integral_zero] using hB 0
  have hbound : (∫⁻ x, (S x : ℝ≥0∞) ∂μ) ≤ ENNReal.ofReal B := by
    have he (x : α) : (S x : ℝ≥0∞) = ⨆ K : ℕ, ((min (S x) K : ℕ) : ℝ≥0∞) := by
      apply le_antisymm
      · exact le_iSup_of_le (S x) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      · exact iSup_le fun K => by exact_mod_cast min_le_left (S x) K
    simp_rw [he]
    rw [lintegral_iSup (f := fun K x => ((min (S x) K : ℕ) : ℝ≥0∞)) (fun K => (measurable_of_countable (f := fun n : ℕ =>
      ((min n K : ℕ) : ℝ≥0∞))).comp hS) (fun i j hij x => by
        dsimp only
        exact_mod_cast min_le_min_left (S x) hij)]
    apply iSup_le
    intro K
    have hh := ofReal_integral_eq_lintegral_ofReal (hKint K)
      (Filter.Eventually.of_forall fun x => Nat.cast_nonneg (min (S x) K))
    simp only [ENNReal.ofReal_natCast] at hh
    rw [← hh]
    exact ENNReal.ofReal_le_ofReal (hB K)
  have hint : Integrable (fun x => (S x : ℝ)) μ := by
    refine ⟨((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp hS).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Nat.cast_nonneg (S x))]
    simp only [ENNReal.ofReal_natCast]
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => Nat.cast_nonneg (S x))
  simp only [ENNReal.ofReal_natCast] at he
  rw [← he] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hB0).mp hbound

lemma renewal_mean_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (S : ℕ → α → ℕ) (hS : ∀ i, Measurable (S i)) (hind : iIndepFun S μ)
    (hident : ∀ i, IdentDistrib (S i) (S 0) μ μ)
    (hpos : ∀ᵐ x ∂μ, ∀ i, 0 < S i x) {p : ℝ} (hp : 0 < p)
    (hlow : ∀ r, 0 < r → p ≤ μ.real {x | ∃ i, (∑ j ∈ Finset.range i, S j x) = r}) :
    Integrable (fun x => (S 0 x : ℝ)) μ ∧ (∫ x, (S 0 x : ℝ) ∂μ) ≤ 1 / p := by
  apply nat_integrable_of_truncated_mean_bound μ (S 0) (hS 0)
  intro K
  let E := ∫ x, ((min (S 0 x) K : ℕ) : ℝ) ∂μ
  have hE : 0 ≤ E := integral_nonneg fun x => Nat.cast_nonneg _
  have hbig : ∀ᵐ x ∂μ, ∀ i, i ≤ ∑ j ∈ Finset.range i, S j x := by
    filter_upwards [hpos] with x hx i
    calc
      i = ∑ _j ∈ Finset.range i, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => hx j
  have hbound (H : ℕ) : (H : ℝ) * p * E ≤ (H : ℝ) + K :=
    (mul_le_mul_of_nonneg_right (renewal_occupation_lower μ _
      (fun i => Finset.measurable_fun_sum _ (fun j _ => hS j)) hbig hlow H) hE).trans
      (renewal_wald_bound μ S hS hind hident H K)
  have hpE : p * E ≤ 1 := by
    by_contra h
    have hpos' : 0 < p * E - 1 := by linarith
    obtain ⟨H, hH⟩ := exists_nat_gt ((K : ℝ) / (p * E - 1))
    have hH' := (div_lt_iff₀ hpos').mp hH
    have hh := hbound H
    nlinarith
  exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hpE)

lemma trueRecord_eq_regenerationTime {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    {j : ℕ} (hj : TrueRecord ℓ X j) : ∃ n, regenerationTimes ℓ X n = j := by
  have hmono := regenerationTimes_strictMono ℓ X hX
  have hbig (n : ℕ) : n ≤ regenerationTimes ℓ X n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hmono (Nat.lt_succ_self n)))
  have hex : ∃ n, j < regenerationTimes ℓ X n := ⟨j+1, (Nat.lt_succ_self j).trans_le (hbig _)⟩
  let n := Nat.find hex
  have hn : j < regenerationTimes ℓ X n := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    simp only [he, regenerationTimes_zero, not_lt_zero] at hn
  have hn' : n - 1 + 1 = n := by omega
  have hbefore : regenerationTimes ℓ X (n-1) ≤ j :=
    le_of_not_gt (Nat.find_min hex (show n-1 < Nat.find hex by change n-1 < n; omega))
  by_cases he : regenerationTimes ℓ X (n-1) = j
  · exact ⟨n-1, he⟩
  · exact False.elim (regenerationTimes_no_true_between ℓ X h0 hX (n-1) j
      (lt_of_le_of_ne hbefore he) (by simpa only [hn'] using hn) hj)

lemma conditioned_wordRecordCount_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    Integrable (fun X => (wordRecordCount ℓ (firstWord ℓ X) : ℝ)) (conditionedLaw ν ℓ) ∧
      (∫ X, (wordRecordCount ℓ (firstWord ℓ X) : ℝ) ∂conditionedLaw ν ℓ) ≤
        1 / (annealedLaw ν).real (NoDrop ℓ 0) := by
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ (ne_of_gt hp)
  let S : ℕ → Path d → ℕ := fun n X => wordRecordCount ℓ (regenerationWords ℓ X n)
  have hS (n : ℕ) : Measurable (S n) :=
    (measurable_of_countable (wordRecordCount ℓ)).comp (measurable_regenerationWord ℓ n)
  have hind : iIndepFun S (conditionedLaw ν ℓ) :=
    (regenerationWords_independent ν ℓ htrans).comp (fun _ => wordRecordCount ℓ)
      (fun _ => measurable_of_countable _)
  have hident (n : ℕ) : IdentDistrib (S n) (S 0) (conditionedLaw ν ℓ) (conditionedLaw ν ℓ) :=
    (regenerationWords_identDistrib ν ℓ htrans n).comp (measurable_of_countable (wordRecordCount ℓ))
  have hall := conditioned_all_firstWords ν ℓ htrans
  have hpos : ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ n, 0 < S n X := by
    filter_upwards [hall] with X hX n
    exact wordRecordCount_positive ℓ _
      (((firstTrueWord_characterization ℓ _ _ (hX n).2.1).mp ⟨(hX n).1, (hX n).2.2⟩).1)
  have hp' : 0 < (annealedLaw ν).real (NoDrop ℓ 0) :=
    ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _)
  have hlow (r : ℕ) (hr : 0 < r) : (annealedLaw ν).real (NoDrop ℓ 0) ≤
      (conditionedLaw ν ℓ).real {X | ∃ n, (∑ j ∈ Finset.range n, S j X) = r} := by
    apply (ENNReal.toReal_mono (measure_ne_top _ _) (conditioned_true_at_index_lower ν ℓ htrans hr)).trans
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hall, (conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν)]
      with X hX h0 hR
    obtain ⟨j, _, hj, hcount⟩ := hR
    obtain ⟨n, hn⟩ := trueRecord_eq_regenerationTime ℓ X h0 hX hj
    exact ⟨n, (recordCount_regenerationTimes ℓ X h0 hX n).symm.trans (hn ▸ hcount)⟩
  exact renewal_mean_bound (conditionedLaw ν ℓ) S hS hind hident hpos hp' hlow

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_LatticeVector
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma wordRadius_bound {d : ℕ} (w : List (Direction d)) {j : ℕ} (hj : j ≤ w.length) :
    ‖latticeVector (wordPath 0 w j)‖ ≤ wordRadius w := by
  classical
  exact Finset.le_sup' (fun j => ‖latticeVector (wordPath 0 w j)‖)
    (Finset.mem_range.mpr (by omega))

lemma wordRadius_nonneg {d : ℕ} (w : List (Direction d)) : 0 ≤ wordRadius w := by
  have hh := wordRadius_bound w (j := 0) (by omega)
  simpa only [wordPath_zero, latticeVector_zero, norm_zero] using hh

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordTemplate
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
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

lemma independent_past_current {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (W : ℕ → Ω → β) (hW : ∀ i, Measurable (W i))
    (hInd : iIndepFun W μ) (i : ℕ) :
    IndepFun (fun x => fun j : Fin i => W j x) (W i) μ := by
  have hd : Disjoint (Finset.range i) {i} := by simp
  have hh := hInd.indepFun_finset (Finset.range i) {i} hd hW
  have hc := hh.comp
    (show Measurable (fun f : (j : ↑(Finset.range i)) → β =>
      fun j : Fin i => f ⟨j, Finset.mem_range.mpr j.2⟩) by fun_prop)
    (show Measurable (fun f : (j : ↑({i} : Finset ℕ)) → β =>
      f ⟨i, Finset.mem_singleton.mpr rfl⟩) by fun_prop)
  exact hc

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SignedCoordinate
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma signedCoordinate_abs_le_norm {d : ℕ} (e : Direction d) (x : Lattice d) :
    |signedCoordinate e x| ≤ ‖latticeVector x‖ := by
  have hh := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (latticeVector x) e.1
  simpa only [signedCoordinate, apply_ite abs, abs_neg, ite_self, Real.norm_eq_abs,
    latticeVector, realPosition] using hh

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_FixedQuenchedKernel
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma annealedFrom_apply {d : ℕ} (ν : Measure (Row d)) (x : Lattice d)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    annealedFrom ν x A = ∫⁻ ω, quenchedKernel (ω,x) A ∂environmentLaw ν := by
  rw [annealedFrom, Measure.bind_apply hA (Kernel.aemeasurable _)]
  rfl

lemma sharedConditionedPairLaw_fst_le {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (A : Set (Path d)) (hA : MeasurableSet A)
    (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    sharedConditionedPairLaw ν ℓ x y (Prod.fst ⁻¹' A) ≤
      (sharedNoDropMass ν ℓ x y)⁻¹ * annealedLaw ν (NoDrop ℓ 0) *
        conditionedFrom ν ℓ x A := by
  rw [sharedConditionedPairLaw, Measure.smul_apply,
    Measure.restrict_apply (hA.preimage measurable_fst)]
  have he : Prod.fst ⁻¹' A ∩ (NoDrop ℓ x ×ˢ NoDrop ℓ y) =
      (A ∩ NoDrop ℓ x) ×ˢ NoDrop ℓ y := by
    ext z
    exact and_assoc.symm
  rw [he, sharedPairLaw_rectangle ν x y _ _ (hA.inter (measurableSet_noDrop ℓ x))
    (measurableSet_noDrop ℓ y)]
  simp only [smul_eq_mul, conditionedFrom, Measure.smul_apply,
    Measure.restrict_apply hA]
  rw [← mul_assoc, mul_assoc _ (annealedLaw ν (NoDrop ℓ 0)),
    ENNReal.mul_inv_cancel hp (measure_ne_top _ _), mul_one]
  apply mul_le_mul_right
  rw [annealedFrom_apply ν x _ (hA.inter (measurableSet_noDrop ℓ x))]
  exact lintegral_mono fun ω => mul_le_of_le_one_right' prob_le_one

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonTrueRecord
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

lemma measurableSet_commonTrueRecord {d : ℕ} (ℓ : Vector d) (n m : ℕ) :
    MeasurableSet {P : Path d × Path d | CommonTrueRecord ℓ P n m} := by
  exact ((measurableSet_trueRecord ℓ n).preimage measurable_fst).inter
    (((measurableSet_trueRecord ℓ m).preimage measurable_snd).inter
      (measurableSet_eq_fun
        ((measurable_of_countable (fun z : Lattice d => dot (realPosition z) ℓ)).comp
          ((measurable_pi_apply n).comp measurable_fst))
        ((measurable_of_countable (fun z : Lattice d => dot (realPosition z) ℓ)).comp
          ((measurable_pi_apply m).comp measurable_snd))))

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

lemma measurable_commonPairSuffix {d : ℕ} (n m : ℕ) :
    Measurable (commonPairSuffix (d := d) n m) := by
  unfold commonPairSuffix
  fun_prop

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma shared_pair_record_cylinder_noDrop {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hrf : StrictRecord ℓ f n) (hrg : StrictRecord ℓ g m)
    (he : dot (realPosition (f n)) ℓ = dot (realPosition (g m)) ℓ) :
    sharedPairLaw ν x y
      (((fun X : Path d => fun j => X (n+j)) ⁻¹' NoDrop ℓ (f n) ∩ pathCylinder f n) ×ˢ
       ((fun X : Path d => fun j => X (m+j)) ⁻¹' NoDrop ℓ (g m) ∩ pathCylinder g m)) =
      sharedPairLaw ν x y (pathCylinder f n ×ˢ pathCylinder g m) *
        sharedNoDropMass ν ℓ (f n) (g m) := by
  have hAf := ((measurableSet_noDrop ℓ (f n)).preimage
    (show Measurable (fun X : Path d => fun j => X (n+j)) by fun_prop)).inter
    (measurableSet_pathCylinder f n)
  have hAg := ((measurableSet_noDrop ℓ (g m)).preimage
    (show Measurable (fun X : Path d => fun j => X (m+j)) by fun_prop)).inter
    (measurableSet_pathCylinder g m)
  rw [sharedPairLaw_rectangle ν x y _ _ hAf hAg,
    sharedPairLaw_rectangle ν x y _ _ (measurableSet_pathCylinder f n)
      (measurableSet_pathCylinder g m)]
  by_cases hf : f 0 = x
  · by_cases hg : g 0 = y
    · let S : Set (Lattice d) := {z | (∃ j < n, z = f j) ∨ (∃ j < m, z = g j)}
      let T := {z : Lattice d | dot (realPosition (f n)) ℓ ≤ dot (realPosition z) ℓ}
      have hdis : Disjoint S T := by
        apply Set.disjoint_left.mpr
        rintro z (⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩) hz
        · exact (not_le_of_gt (hrf j hj)) hz
        · have hlt := hrg j hj
          rw [← he] at hlt
          exact (not_le_of_gt hlt) hz
      have hfm : @Measurable _ _ (rowSigma S) _
          (fun ω : Environment d => quenchedKernel (ω,x) (pathCylinder f n)) := by
        apply measurable_of_row_locality _
          ((Kernel.measurable_coe _ (measurableSet_pathCylinder f n)).comp
            (measurable_id.prodMk measurable_const)) S x (Or.inl ⟨0,hn,hf.symm⟩)
        intro ω η hωη
        exact pathCylinder_weight_locality S ω η hωη x f n (fun j hj => Or.inl ⟨j,hj,rfl⟩)
      have hgm : @Measurable _ _ (rowSigma S) _
          (fun ω : Environment d => quenchedKernel (ω,y) (pathCylinder g m)) := by
        apply measurable_of_row_locality _
          ((Kernel.measurable_coe _ (measurableSet_pathCylinder g m)).comp
            (measurable_id.prodMk measurable_const)) S y (Or.inr ⟨0,hm,hg.symm⟩)
        intro ω η hωη
        exact pathCylinder_weight_locality S ω η hωη y g m (fun j hj => Or.inr ⟨j,hj,rfl⟩)
      have hnfm : @Measurable _ _ (rowSigma T) _ (noDropQuenched ℓ (f n)) :=
        measurable_noDropQuenched_rows ℓ (f n)
      have hngm : @Measurable _ _ (rowSigma T) _ (noDropQuenched ℓ (g m)) := by
        change @Measurable _ _ (rowSigma {z | dot (realPosition (f n)) ℓ ≤ dot (realPosition z) ℓ}) _ _
        rw [he]
        exact measurable_noDropQuenched_rows ℓ (g m)
      simp_rw [quenched_prefix_future _ _ _ hf n (measurableSet_noDrop ℓ (f n)),
        quenched_prefix_future _ _ _ hg m (measurableSet_noDrop ℓ (g m)), mul_mul_mul_comm]
      have hind := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
        (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hdis)
        (hfm.mul hgm) (hnfm.mul hngm)
      simp only [Pi.mul_apply] at hind
      exact hind
    · have hz ω : quenchedKernel (ω,y)
          ((fun X : Path d => fun j => X (m+j)) ⁻¹' NoDrop ℓ (g m) ∩ pathCylinder g m) = 0 :=
        measure_mono_null Set.inter_subset_right (quenched_pathCylinder_zero ω y g hg m)
      simp only [hz, quenched_pathCylinder_zero _ _ _ hg m, mul_zero, lintegral_zero, zero_mul]
  · have hz ω : quenchedKernel (ω,x)
        ((fun X : Path d => fun j => X (n+j)) ⁻¹' NoDrop ℓ (f n) ∩ pathCylinder f n) = 0 :=
      measure_mono_null Set.inter_subset_right (quenched_pathCylinder_zero ω x f hf n)
    simp only [hz, quenched_pathCylinder_zero _ _ _ hf n, zero_mul, lintegral_zero]

lemma measurable_pairPrefix {d : ℕ} (n m : ℕ) : Measurable (pairPrefix (d := d) n m) :=
  ((Preorder.measurable_frestrictLe n).comp measurable_fst).prodMk
    ((Preorder.measurable_frestrictLe m).comp measurable_snd)

lemma pairPrefix_fiber {d : ℕ} (n m : ℕ)
    (F : ((i : Finset.Iic n) → Lattice d) × ((i : Finset.Iic m) → Lattice d)) :
    pairPrefix n m ⁻¹' {F} =
      pathCylinder (extendPrefix n F.1) n ×ˢ pathCylinder (extendPrefix m F.2) m := by
  rw [← restrict_prefix_fiber, ← restrict_prefix_fiber]
  ext P
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_prod,pairPrefix,Prod.ext_iff]

lemma measure_partition_pairprefix {d : ℕ} (μ : Measure (Path d × Path d))
    (A : Set (Path d × Path d)) (n m : ℕ) :
    μ A = ∑' F : (((i : Finset.Iic n) → Lattice d) × ((i : Finset.Iic m) → Lattice d)),
      μ (A ∩ (pathCylinder (extendPrefix n F.1) n ×ˢ pathCylinder (extendPrefix m F.2) m)) := by
  have h := tsum_measure_preimage_singleton (μ := μ.restrict A)
    (s := Set.univ) (Set.to_countable _) (f := pairPrefix (d := d) n m)
    (fun F _ => (measurable_pairPrefix n m) (measurableSet_singleton F))
  simp only [Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h
  rw [tsum_subtype Set.univ (fun F => (μ.restrict A) (pairPrefix n m ⁻¹' {F})),
    Set.indicator_univ] at h
  rw [← h]
  apply tsum_congr
  intro F
  rw [Measure.restrict_apply ((measurable_pairPrefix n m) (measurableSet_singleton F)),
    pairPrefix_fiber, Set.inter_comm]

lemma shared_pair_record_event_noDrop_lower {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x y : Lattice d)
    (c : ℝ≥0∞) (hc : ∀ u v, c ≤ sharedNoDropMass ν ℓ u v)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (A : Set (Path d × Path d))
    (hA : PairPrefixDetermined n m A)
    (hr : ∀ P ∈ A, StrictRecord ℓ P.1 n ∧ StrictRecord ℓ P.2 m ∧
      dot (realPosition (P.1 n)) ℓ = dot (realPosition (P.2 m)) ℓ) :
    c * sharedPairLaw ν x y A ≤
      sharedPairLaw ν x y (A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m)) := by
  classical
  rw [measure_partition_pairprefix (sharedPairLaw ν x y) A n m,
    measure_partition_pairprefix (sharedPairLaw ν x y) (A ∩ _) n m,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro F
  let P : Path d × Path d := (extendPrefix n F.1,extendPrefix m F.2)
  let C := pathCylinder P.1 n ×ˢ pathCylinder P.2 m
  by_cases hP : P ∈ A
  · have hAc : A ∩ C = C := Set.inter_eq_right.mpr fun Q hQ => (hA Q P hQ.1 hQ.2).mpr hP
    have he : (A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m)) ∩ C =
        (((fun X : Path d => fun j => X (n+j)) ⁻¹' NoDrop ℓ (P.1 n) ∩ pathCylinder P.1 n) ×ˢ
         ((fun X : Path d => fun j => X (m+j)) ⁻¹' NoDrop ℓ (P.2 m) ∩ pathCylinder P.2 m)) := by
      ext Q
      constructor
      · rintro ⟨⟨_,h1,h2⟩,hc1,hc2⟩
        refine ⟨⟨?_,hc1⟩,⟨?_,hc2⟩⟩
        · intro j; rw [← hc1 n le_rfl]; exact h1 j
        · intro j; rw [← hc2 m le_rfl]; exact h2 j
      · rintro ⟨⟨h1,hc1⟩,⟨h2,hc2⟩⟩
        refine ⟨⟨(hA Q P hc1 hc2).mpr hP,?_,?_⟩,hc1,hc2⟩
        · intro j; rw [hc1 n le_rfl]; exact h1 j
        · intro j; rw [hc2 m le_rfl]; exact h2 j
    change c * sharedPairLaw ν x y (A ∩ C) ≤ sharedPairLaw ν x y ((A ∩ _) ∩ C)
    rw [hAc,he,shared_pair_record_cylinder_noDrop ν ℓ x y P.1 P.2 n m hn hm
      (hr P hP).1 (hr P hP).2.1 (hr P hP).2.2]
    simpa only [mul_comm] using mul_le_mul_right (hc (P.1 n) (P.2 m)) (sharedPairLaw ν x y C)
  · have hAc : A ∩ C = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro Q ⟨hQ,hqc1,hqc2⟩
      exact hP ((hA Q P hqc1 hqc2).mp hQ)
    change c * sharedPairLaw ν x y (A ∩ C) ≤ _
    rw [hAc,measure_empty,mul_zero]
    exact zero_le

lemma annealedFrom_ae_of_quenched {d : ℕ} (ν : Measure (Row d)) (x : Lattice d)
    (A : Set (Path d)) (hA : MeasurableSet A)
    (h : ∀ᵐ ω ∂environmentLaw ν, ∀ᵐ X ∂quenchedKernel (ω,x), X ∈ A) :
    ∀ᵐ X ∂annealedFrom ν x, X ∈ A := by
  rw [ae_iff]
  change annealedFrom ν x Aᶜ = 0
  rw [annealedFrom_apply ν x Aᶜ hA.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [h] with ω hω
  exact ae_iff.mp hω

lemma sharedPairLaw_fst {d : ℕ} (ν : Measure (Row d)) (x y : Lattice d) :
    (sharedPairLaw ν x y).map Prod.fst = annealedFrom ν x := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_fst hA]
  have he : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set (Path d)) := by ext P; simp
  rw [he,sharedPairLaw_rectangle ν x y A Set.univ hA MeasurableSet.univ,
    annealedFrom_apply ν x A hA]
  simp only [measure_univ,mul_one]

lemma sharedPairLaw_snd {d : ℕ} (ν : Measure (Row d)) (x y : Lattice d) :
    (sharedPairLaw ν x y).map Prod.snd = annealedFrom ν y := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_snd hA]
  have he : Prod.snd ⁻¹' A = (Set.univ : Set (Path d)) ×ˢ A := by ext P; simp
  rw [he,sharedPairLaw_rectangle ν x y Set.univ A MeasurableSet.univ hA,
    annealedFrom_apply ν y A hA]
  simp only [measure_univ,one_mul]

lemma shared_pair_ae {d : ℕ} (ν : Measure (Row d)) (x y : Lattice d)
    (A B : Set (Path d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (ha : ∀ᵐ X ∂annealedFrom ν x, X ∈ A) (hb : ∀ᵐ Y ∂annealedFrom ν y, Y ∈ B) :
    ∀ᵐ P ∂sharedPairLaw ν x y, P.1 ∈ A ∧ P.2 ∈ B := by
  rw [← sharedPairLaw_fst ν x y] at ha
  rw [← sharedPairLaw_snd ν x y] at hb
  exact ((ae_map_iff measurable_fst.aemeasurable hA).mp ha).and
    ((ae_map_iff measurable_snd.aemeasurable hB).mp hb)

lemma measurableSet_firstLayerHit {d : ℕ} (h : Lattice d → ℤ) (H : ℤ) (n : ℕ) :
    MeasurableSet (FirstLayerHit h H n) := by
  simp only [FirstLayerHit,Set.ofPred_and,Set.ofPred_forall]
  exact (measurableSet_eq_fun ((measurable_of_countable h).comp (measurable_pi_apply n))
    measurable_const).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_lt ((measurable_of_countable h).comp (measurable_pi_apply j)) measurable_const)

lemma firstLayerHit_prefix {d : ℕ} (h : Lattice d → ℤ) (H : ℤ) (n : ℕ) :
    PrefixDetermined n (FirstLayerHit h H n) := by
  intro X Y hXY
  simp only [FirstLayerHit,Set.mem_ofPred_eq,hXY n le_rfl]
  apply and_congr Iff.rfl
  exact forall_congr' fun j => forall_congr' fun hj => by rw [hXY j hj.le]

lemma firstLayerHit_disjoint {d : ℕ} (h : Lattice d → ℤ) (H : ℤ) :
    Pairwise (fun n m => Disjoint (FirstLayerHit h H n) (FirstLayerHit h H m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro X hn hm
  rcases lt_or_gt_of_ne hnm with hnlt | hmlt
  · have hi := hm.2 n hnlt
    rw [hn.1] at hi
    exact (lt_irrefl _) hi
  · have hi := hn.2 m hmlt
    rw [hm.1] at hi
    exact (lt_irrefl _) hi

lemma firstLayerHit_record {d : ℕ} (ℓ : Vector d) (h : Lattice d → ℤ)
    (hproj : ∀ x, dot (realPosition x) ℓ = (h x : ℝ)) (H : ℤ) (n : ℕ)
    (X : Path d) (hX : X ∈ FirstLayerHit h H n) : StrictRecord ℓ X n := by
  intro j hj
  rw [hproj,hproj,hX.1]
  exact_mod_cast hX.2 j hj

lemma firstLayerHit_exists {d : ℕ} (h : Lattice d → ℤ)
    (hstep : ∀ x e, h (x+step e) ≤ h x+1) (X : Path d)
    (hnn : ∀ n, ∃ e, X (n+1) = X n+step e)
    (ht : Tendsto (fun n => (h (X n) : ℝ)) atTop atTop)
    (H : ℤ) (h0 : h (X 0) < H) : ∃ n, X ∈ FirstLayerHit h H n := by
  classical
  have hge : ∀ᶠ n : ℕ in atTop, (H : ℝ) ≤ (h (X n) : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨k,hk⟩ := hge.exists
  have he : ∃ n, H ≤ h (X n) := ⟨k, by exact_mod_cast hk⟩
  let n := Nat.find he
  have hn : H ≤ h (X n) := Nat.find_spec he
  have hb : ∀ j < n, h (X j) < H := fun j hj => lt_of_not_ge (Nat.find_min he hj)
  have hn0 : 0 < n := by
    by_contra hh
    have hz : n = 0 := by omega
    rw [hz] at hn
    omega
  obtain ⟨e,he⟩ := hnn (n-1)
  have hprev := hb (n-1) (by omega)
  have hinc := hstep (X (n-1)) e
  rw [← he,show n-1+1 = n by omega] at hinc
  exact ⟨n,by omega,hb⟩

lemma shared_pair_layer_hits {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (x y : Lattice d) (H : ℤ) (hx : height x < H) (hy : height y < H) :
    ∀ᵐ P ∂sharedPairLaw ν x y,
      (∃ n, P.1 ∈ FirstLayerHit height H n) ∧ (∃ m, P.2 ∈ FirstLayerHit height H m) := by
  let A := {X : Path d | ∃ n, X ∈ FirstLayerHit height H n}
  have hA : MeasurableSet A := by
    simp only [A,Set.ofPred_exists]
    exact MeasurableSet.iUnion (measurableSet_firstLayerHit height H)
  apply shared_pair_ae ν x y A A hA hA
  all_goals
    apply annealedFrom_ae_of_quenched ν _ A hA
    filter_upwards [quenched_directionallyTransient_ae ν ℓ htrans] with ω hω
  · filter_upwards [hω x,quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X ht h0 hnn
    exact firstLayerHit_exists height hstep X hnn (by simpa only [TransientPaths,Set.mem_ofPred_eq,hproj] using ht)
      H (by simpa only [h0] using hx)
  · filter_upwards [hω y,quenched_initial_ae (ω,y),quenched_nearest_neighbor (ω,y)] with Y ht h0 hnn
    exact firstLayerHit_exists height hstep Y hnn (by simpa only [TransientPaths,Set.mem_ofPred_eq,hproj] using ht)
      H (by simpa only [h0] using hy)

lemma firstLayerHit_pair_disjoint {d : ℕ} (height : Lattice d → ℤ) (H : ℤ) :
    Pairwise (fun q r : ℕ × ℕ => Disjoint
      (FirstLayerHit height H q.1 ×ˢ FirstLayerHit height H q.2)
      (FirstLayerHit height H r.1 ×ˢ FirstLayerHit height H r.2)) := by
  intro q r hqr
  apply Set.disjoint_left.mpr
  rintro P ⟨h1,h2⟩ ⟨h3,h4⟩
  by_cases hq : q.1 = r.1
  · have hq2 : q.2 ≠ r.2 := fun hq2 => hqr (Prod.ext hq hq2)
    exact Set.disjoint_left.mp (firstLayerHit_disjoint height H hq2) h2 h4
  · exact Set.disjoint_left.mp (firstLayerHit_disjoint height H hq) h1 h3

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentPairLaw
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RecordIndexTime
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma conditioned_recordIndexPrefix_exists {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) {r : ℕ} (hr : 0 < r) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, ∃ n, X ∈ RecordIndexPrefix ℓ r n := by
  filter_upwards [conditionedLaw_noDrop ν ℓ,
    (conditionedLaw_absolutelyContinuous ν ℓ).ae_le htrans] with X hD ht
  obtain ⟨n,hn,hrec,hcount⟩ := exists_record_at_index ℓ X ht hr
  exact ⟨n,hn,hrec,hcount,fun j _ => hD j⟩

lemma conditioned_recordIndexTime_spec {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) {r : ℕ} (hr : 0 < r) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r X) := by
  filter_upwards [conditioned_recordIndexPrefix_exists ν ℓ htrans hr] with X hX
  obtain ⟨n,hn⟩ := hX
  rwa [recordIndexTime_eq ℓ r n X hn]

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

lemma renewalSum_zero (L : ℕ → ℕ) : renewalSum L 0 = 0 := by simp [renewalSum]
lemma renewalSum_succ (L : ℕ → ℕ) (n : ℕ) : renewalSum L (n+1) = renewalSum L n+L n := by
  simp [renewalSum,Finset.sum_range_succ]
lemma renewalSum_ge (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) (n : ℕ) : n ≤ renewalSum L n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => rw [renewalSum_succ]; have := hL n; omega
lemma renewalSum_strictMono (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) : StrictMono (renewalSum L) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [renewalSum_succ]
  exact Nat.lt_add_of_pos_right (hL n)

lemma renewalCount_le (L : ℕ → ℕ) (h : ℕ) : renewalCount L h ≤ h := Nat.findGreatest_le _
lemma renewalCount_lower (L : ℕ → ℕ) (h : ℕ) : renewalSum L (renewalCount L h) ≤ h := by
  classical
  exact Nat.findGreatest_spec (P := fun k => renewalSum L k ≤ h) (Nat.zero_le h)
    (by rw [renewalSum_zero]; exact Nat.zero_le _)
lemma renewalCount_upper (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) (h : ℕ) :
    h < renewalSum L (renewalCount L h+1) := by
  classical
  by_cases hk : renewalCount L h+1 ≤ h
  · exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest
      (P := fun k => renewalSum L k ≤ h) (Nat.lt_succ_self _) hk)
  · exact (Nat.lt_of_not_ge hk).trans_le (renewalSum_ge L hL _)
lemma renewalCount_zero (L : ℕ → ℕ) : renewalCount L 0 = 0 := by simp [renewalCount]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_RenewalCountBounds
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
namespace DirectionalTransience

lemma renewalCount_eq_of_bounds (L : ℕ → ℕ) (hL : ∀ k, 0 < L k)
    {h k : ℕ} (hl : renewalSum L k ≤ h) (hu : h < renewalSum L (k+1)) :
    renewalCount L h = k := by
  have hm := renewalSum_strictMono L hL
  have hl' := renewalCount_lower L h
  have hu' := renewalCount_upper L hL h
  apply le_antisymm
  · by_contra! hh
    have := hm.monotone (show k+1 ≤ renewalCount L h by omega)
    omega
  · by_contra! hh
    have := hm.monotone (show renewalCount L h+1 ≤ k by omega)
    omega

lemma renewalCount_at_sum (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) (k : ℕ) :
    renewalCount L (renewalSum L k) = k :=
  renewalCount_eq_of_bounds L hL le_rfl ((renewalSum_strictMono L hL) (Nat.lt_succ_self k))

lemma measurable_renewalSum {Ω : Type*} [MeasurableSpace Ω]
    (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k)) (n : ℕ) :
    Measurable (fun ω => renewalSum (fun k => L k ω) n) :=
  Finset.measurable_fun_sum _ (fun k _ => hL k)

lemma integral_nat_event_indicator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Set Ω) [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
    (∫ ω, if ω ∈ A then (1:ℝ) else 0 ∂μ) = μ.real A := by
  simpa only [Set.indicator_apply,smul_eq_mul,mul_one] using integral_indicator_const (1:ℝ) hA

lemma renewal_occupation_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ → Ω → ℕ)
    (hL : ∀ k, Measurable (L k)) (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω) (s H : ℕ) :
    (∑ k ∈ Finset.range H, μ.real {ω | renewalSum (fun j => L j ω) k = s}) ≤ 1 := by
  classical
  let A := fun k => {ω | renewalSum (fun j => L j ω) k = s}
  have hA (k : ℕ) : MeasurableSet (A k) :=
    measurableSet_eq_fun (measurable_renewalSum L hL k) measurable_const
  have hi (k : ℕ) : Integrable (fun ω => if ω ∈ A k then (1:ℝ) else 0) μ :=
    by
      apply ((integrable_const (μ := μ) (1:ℝ)).indicator (hA k)).congr
      filter_upwards [] with ω
      simp only [Set.indicator_apply]
  have he : (∑ k ∈ Finset.range H, μ.real (A k)) =
      ∫ ω, ∑ k ∈ Finset.range H, if ω ∈ A k then (1:ℝ) else 0 ∂μ := by
    rw [integral_finsetSum _ (fun k _ => hi k)]
    exact Finset.sum_congr rfl (fun k _ => (integral_nat_event_indicator μ (A k) (hA k)).symm)
  rw [he]
  calc
    _ ≤ ∫ _ : Ω, (1:ℝ) ∂μ := by
      apply integral_mono_ae (integrable_finsetSum _ (fun k _ => hi k)) (integrable_const _)
      filter_upwards [hpos] with ω hω
      calc
        _ ≤ ∑ k ∈ Finset.range H, if k = renewalCount (fun j => L j ω) s then (1:ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro k _
          by_cases hk : ω ∈ A k
          · have he := renewalCount_at_sum (fun j => L j ω) hω k
            change renewalSum (fun j => L j ω) k = s at hk
            rw [hk] at he
            simp [show ω ∈ A k from hk,he]
          · simp only [ite_eq_right hk]
            split_ifs <;> norm_num
        _ ≤ 1 := by simp only [Finset.sum_ite_eq']; split_ifs <;> norm_num
    _ = 1 := by simp

lemma renewal_selected_event_bound {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ℕ → Ω → α)
    (hW : ∀ k, Measurable (W k)) (hind : iIndepFun W μ)
    (hident : ∀ k, IdentDistrib (W k) (W 0) μ μ)
    (L : α → ℕ) (hL : Measurable L) (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L (W k ω))
    (hI : Integrable (fun ω => (L (W 0 ω) : ℝ)) μ)
    (A : Set α) (hA : MeasurableSet A) (h : ℕ) :
    μ.real {ω | W (renewalCount (fun j => L (W j ω)) h) ω ∈ A} ≤
      ∫ ω, if W 0 ω ∈ A then (L (W 0 ω) : ℝ) else 0 ∂μ := by
  classical
  let S := fun k ω => renewalSum (fun j => L (W j ω)) k
  let B := fun s => {a | a ∈ A ∧ h-s < L a}
  let E := fun k s => {ω | S k ω = s ∧ W k ω ∈ B s}
  have hB (s : ℕ) : MeasurableSet (B s) := hA.inter (measurableSet_lt measurable_const hL)
  have hSm (k : ℕ) : Measurable (S k) := measurable_renewalSum _ (fun j => hL.comp (hW j)) k
  have hE (k s : ℕ) : MeasurableSet (E k s) :=
    (measurableSet_eq_fun (hSm k) measurable_const).inter ((hW k) (hB s))
  have hsub : {ω | W (renewalCount (fun j => L (W j ω)) h) ω ∈ A} ≤ᵐ[μ]
      ⋃ k ∈ Finset.range (h+1), ⋃ s ∈ Finset.range (h+1), E k s := by
    filter_upwards [hpos] with ω hω ha
    let k := renewalCount (fun j => L (W j ω)) h
    have hk := renewalCount_le (fun j => L (W j ω)) h
    have hs := renewalCount_lower (fun j => L (W j ω)) h
    have hs' := renewalCount_upper (fun j => L (W j ω)) hω h
    rw [renewalSum_succ] at hs'
    refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),
      Set.mem_iUnion.mpr ⟨S k ω,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by dsimp [S,k]; omega),
        rfl,ha,?_⟩⟩⟩⟩
    dsimp [S,k]
    omega
  have hfactor (k s : ℕ) : μ.real (E k s) =
      μ.real {ω | S k ω = s} * μ.real (W 0 ⁻¹' B s) := by
    let F := fun w : Fin k → α => ∑ j : Fin k, L (w j)
    have hF : Measurable F := Finset.measurable_fun_sum _ (fun j _ => hL.comp (measurable_pi_apply j))
    have hind' := (independent_past_current μ W hW hind k).comp hF measurable_id
    have he : (fun ω => F (fun j : Fin k => W j ω)) = S k := by
      funext ω
      dsimp [F,S,renewalSum]
      exact Fin.sum_univ_eq_sum_range (fun j => L (W j ω)) k
    change IndepFun (fun ω => F (fun j : Fin k => W j ω)) (W k) μ at hind'
    rw [he] at hind'
    have hh := hind'.measure_inter_preimage_eq_mul {s} (B s) (measurableSet_singleton s) (hB s)
    have hid := (hident k).measure_mem_eq (hB s)
    change μ (E k s) = μ {ω | S k ω = s} * μ (W k ⁻¹' B s) at hh
    rw [hid] at hh
    exact congrArg ENNReal.toReal hh |>.trans ENNReal.toReal_mul
  calc
    _ ≤ μ.real (⋃ k ∈ Finset.range (h+1), ⋃ s ∈ Finset.range (h+1), E k s) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ ∑ k ∈ Finset.range (h+1), ∑ s ∈ Finset.range (h+1), μ.real (E k s) := by
      exact (measureReal_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum (fun k _ => measureReal_biUnion_finset_le _ _))
    _ = ∑ s ∈ Finset.range (h+1),
        (∑ k ∈ Finset.range (h+1), μ.real {ω | S k ω = s}) * μ.real (W 0 ⁻¹' B s) := by
      simp_rw [hfactor]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ s ∈ Finset.range (h+1), μ.real (W 0 ⁻¹' B s) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_of_le_one_left measureReal_nonneg
        (renewal_occupation_upper μ _ (fun k => hL.comp (hW k)) hpos s (h+1))
    _ = ∑ s ∈ Finset.range (h+1), μ.real {ω | W 0 ω ∈ A ∧ s < L (W 0 ω)} := by
      simpa only [Nat.add_sub_cancel,B,Set.preimage_ofPred_eq] using
        Finset.sum_range_reflect (fun s => μ.real {ω | W 0 ω ∈ A ∧ s < L (W 0 ω)}) (h+1)
    _ ≤ _ := by
      let C := fun s => {ω | W 0 ω ∈ A ∧ s < L (W 0 ω)}
      have hC (s : ℕ) : MeasurableSet (C s) := ((hW 0) hA).inter
        (measurableSet_lt measurable_const (hL.comp (hW 0)))
      have hCi (s : ℕ) : Integrable (fun ω => if ω ∈ C s then (1:ℝ) else 0) μ :=
        by
          apply ((integrable_const (μ := μ) (1:ℝ)).indicator (hC s)).congr
          filter_upwards [] with ω
          simp only [Set.indicator_apply]
      calc
        _ = ∫ ω, ∑ s ∈ Finset.range (h+1), if ω ∈ C s then (1:ℝ) else 0 ∂μ := by
          rw [integral_finsetSum _ (fun s _ => hCi s)]
          exact Finset.sum_congr rfl (fun s _ => (integral_nat_event_indicator μ (C s) (hC s)).symm)
        _ ≤ _ := by
          apply integral_mono (integrable_finsetSum _ (fun s _ => hCi s)) (by
            apply (hI.indicator ((hW 0) hA)).congr
            filter_upwards [] with ω
            simp only [Set.indicator_apply,Set.mem_preimage])
          intro ω
          by_cases hω : W 0 ω ∈ A
          · simp only [C,Set.mem_ofPred_eq,hω,true_and,ite_eq_left]
            calc
              _ ≤ ∑ s ∈ Finset.range (L (W 0 ω)), (1:ℝ) := by
                rw [← Finset.sum_filter]
                exact Finset.sum_le_sum_of_subset_of_nonneg
                  (fun s hs => Finset.mem_range.mpr (Finset.mem_filter.mp hs).2)
                  (fun _ _ _ => zero_le_one)
              _ = _ := by simp
          · simp [C,hω]

lemma width_mark_tail_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (L : Ω → ℕ) (hL : Measurable L)
    (hI : Integrable (fun ω => (L ω : ℝ)) μ) (R : Ω → ℝ) (hR : Measurable R)
    (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) :
    Tendsto (fun i => ∫ ω, if b i ≤ |R ω| then (L ω : ℝ) else 0 ∂μ) atTop (𝓝 0) := by
  have hm (i : ℕ) : Measurable (fun ω => if b i ≤ |R ω| then (L ω : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const hR.abs)
      ((measurable_of_countable (fun j : ℕ => (j:ℝ))).comp hL) measurable_const
  have ht := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun i ω => if b i ≤ |R ω| then (L ω : ℝ) else 0) (f := fun _ => (0:ℝ))
    (fun ω => (L ω : ℝ)) (fun i => (hm i).aestronglyMeasurable) hI
    (fun i => Eventually.of_forall fun ω => by
      split_ifs <;> simp [Nat.cast_nonneg])
    (Eventually.of_forall fun ω => by
      apply tendsto_const_nhds.congr'
      filter_upwards [hb.eventually (eventually_gt_atTop |R ω|)] with i hi
      simp only [ite_eq_right (not_le_of_gt hi)])
  simpa only [integral_zero] using ht

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstHitPairGap
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
namespace DirectionalTransience

lemma recordIndexTime_zero {d : ℕ} (ℓ : Vector d) (X : Path d) : recordIndexTime ℓ 0 X = 0 := by
  classical
  have hn : ¬ ∃ n, X ∈ RecordIndexPrefix ℓ 0 n := by
    rintro ⟨n,hn,hr,hc,_⟩
    have hh := recordCount_lt_of_strictRecord ℓ X hn hr
    simp only [recordCount_zero,hc,lt_self_iff_false] at hh
  simp only [recordIndexTime,dite_eq_right hn]

lemma recordTime_between {d : ℕ} (ℓ : Vector d) (X : Path d) {h j k n : ℕ}
    (hj : StrictRecord ℓ X j) (hn : X ∈ RecordIndexPrefix ℓ h n)
    (hl : recordCount ℓ X j ≤ h) (hu : h < recordCount ℓ X k) : j ≤ n ∧ n < k := by
  constructor
  · by_contra! hh
    have := recordCount_lt_of_strictRecord ℓ X hh hj
    rw [hn.2.2.1] at this
    omega
  · by_contra! hh
    have := recordCount_mono ℓ X hh
    rw [hn.2.2.1] at this
    omega

lemma coordinate_prefix_bound {d : ℕ} (e : Direction d) (X : Path d)
    (w : List (Direction d)) {j n : ℕ}
    (hw : ∀ k ≤ w.length, X (j+k)-X j = wordPath 0 w k)
    (hl : j ≤ n) (hu : n ≤ j+w.length) :
    |signedCoordinate e (X n)-signedCoordinate e (X j)| ≤ wordRadius w := by
  rw [← signedCoordinate_sub]
  have hk : n-j ≤ w.length := by omega
  have he := hw (n-j) hk
  rw [Nat.add_sub_of_le hl] at he
  rw [he]
  exact (signedCoordinate_abs_le_norm e _).trans (wordRadius_bound w hk)

lemma measurable_firstHitPairGap {d : ℕ} (ℓ : Vector d) (e : Direction d) (h : ℕ) :
    Measurable (firstHitPairGap ℓ e h) :=
  ((measurable_of_countable (signedCoordinate e)).comp
    ((measurable_recordIndexPosition ℓ h).comp measurable_fst)).sub
    ((measurable_of_countable (signedCoordinate e)).comp
    ((measurable_recordIndexPosition ℓ h).comp measurable_snd))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_HighRecordCount
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
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
namespace DirectionalTransience

lemma recordIndexPosition_suffix {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hD : X ∈ NoDrop ℓ 0) (ht : X ∈ TransientPaths ℓ) {n : ℕ} (hn : 0 < n)
    (htrue : TrueRecord ℓ X n) (j : ℕ) :
    recordIndexPosition ℓ (j+recordCount ℓ X n) X =
      recordIndexPosition ℓ j (fun k => X (n+k)-X n)+X n := by
  let Z : Path d := fun k => X (n+k)-X n
  have hpre : X ∈ RecordIndexPrefix ℓ (recordCount ℓ X n) n :=
    ⟨hn,htrue.1,rfl,fun k _ => hD k⟩
  have hzD : Z ∈ NoDrop ℓ 0 := (suffix_noDrop_iff ℓ X n).mpr htrue.2
  have hzt : Z ∈ TransientPaths ℓ := by
    change (fun k => X (n+k)) ∈ (fun Y : Path d => fun k => Y k-X n) ⁻¹' TransientPaths ℓ
    rw [transientPaths_translation]
    change Tendsto (fun k => dot (realPosition (X (n+k))) ℓ) atTop atTop
    have hh := (tendsto_add_atTop_iff_nat n).mpr ht
    simpa only [Nat.add_comm] using hh
  by_cases hj : j = 0
  · subst j
    rw [zero_add,recordIndexPosition,recordIndexTime_eq ℓ _ n X hpre,
      recordIndexPosition,recordIndexTime_zero]
    simp
  · obtain ⟨m,hm,hrec,hcount⟩ := exists_record_at_index ℓ Z hzt (Nat.pos_of_ne_zero hj)
    have hR : Z ∈ RecordIndexPrefix ℓ j m := ⟨hm,hrec,hcount,fun k _ => hzD k⟩
    have ha : X ∈ RecordIndexPrefix ℓ (j+recordCount ℓ X n) (n+m) := by
      refine ⟨by omega,(strictRecord_suffix_iff ℓ X htrue.1 hm).mp hrec,?_,fun k _ => hD k⟩
      rw [recordCount_add ℓ X htrue.1,hcount,Nat.add_comm]
    rw [recordIndexPosition,recordIndexTime_eq ℓ _ (n+m) X ha,
      recordIndexPosition,recordIndexTime_eq ℓ j m Z hR]
    exact (sub_add_cancel _ _).symm

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SharedConditionedPairLawFst
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
namespace DirectionalTransience

lemma sharedPairLaw_swap {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x y : Lattice d) : (sharedPairLaw ν x y).map Prod.swap = sharedPairLaw ν y x := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply measurable_swap (hA.prod hB)]
  have he : Prod.swap ⁻¹' (A ×ˢ B) = B ×ˢ A := by ext Z; exact and_comm
  rw [he,sharedPairLaw_rectangle ν x y B A hB hA,sharedPairLaw_rectangle ν y x A B hA hB]
  apply lintegral_congr
  intro ω
  exact mul_comm _ _

lemma sharedNoDropMass_swap {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x y : Lattice d) : sharedNoDropMass ν ℓ x y = sharedNoDropMass ν ℓ y x := by
  unfold sharedNoDropMass
  apply lintegral_congr
  intro ω
  exact mul_comm _ _

lemma sharedConditionedPairLaw_swap {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) :
    (sharedConditionedPairLaw ν ℓ x y).map Prod.swap = sharedConditionedPairLaw ν ℓ y x := by
  have he : Prod.swap ⁻¹' (NoDrop ℓ y ×ˢ NoDrop ℓ x) = NoDrop ℓ x ×ˢ NoDrop ℓ y := by
    ext Z; exact and_comm
  rw [sharedConditionedPairLaw,Measure.map_smul,← he,← Measure.restrict_map measurable_swap
    ((measurableSet_noDrop ℓ y).prod (measurableSet_noDrop ℓ x)),sharedPairLaw_swap,
    sharedNoDropMass_swap]
  rfl

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SignedHeightSub
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
namespace DirectionalTransience

lemma signedHeight_sub {d : ℕ} (e : Direction d) (x y : Lattice d) :
    signedHeight e (x-y) = signedHeight e x-signedHeight e y := by
  simp only [signedHeight,Pi.sub_apply]
  split <;> omega

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SingleCoverWord
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
namespace DirectionalTransience

lemma single_width_positive {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n)) (n : ℕ) :
    0 < wordRecordCount ℓ (regenerationWords ℓ X n) :=
  wordRecordCount_positive ℓ _
    (((firstTrueWord_characterization ℓ _ _ (hX n).2.1).mp ⟨(hX n).1,(hX n).2.2⟩).1)

theorem single_cover_event_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (A : Set (List (Direction d))) (hA : MeasurableSet A) (h : ℕ) :
    (conditionedLaw ν ℓ).real {X | singleCoverWord ℓ h X ∈ A} ≤
      ∫ X, if firstWord ℓ X ∈ A then (wordRecordCount ℓ (firstWord ℓ X) : ℝ) else 0
        ∂conditionedLaw ν ℓ := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  apply renewal_selected_event_bound _ (fun j X => regenerationWords ℓ X j)
    (measurable_regenerationWord ℓ) (regenerationWords_independent ν ℓ htrans)
    (regenerationWords_identDistrib ν ℓ htrans) (wordRecordCount ℓ) (measurable_of_countable _) _
    (conditioned_wordRecordCount_integrable ν ℓ htrans).1 A hA h
  filter_upwards [conditioned_all_firstWords ν ℓ htrans] with X hX n
  exact single_width_positive ℓ X hX n

lemma single_cover_tail_small {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (R : List (Direction d) → ℝ) (h : ℕ → ℕ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    Tendsto (fun i => (conditionedLaw ν ℓ).real {X | r i ≤ |R (singleCoverWord ℓ (h i) X)|})
      atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun i =>
    single_cover_event_bound ν ℓ htrans {w | r i ≤ |R w|} (Set.to_countable _).measurableSet (h i))
  exact width_mark_tail_tendsto _ _
    ((measurable_of_countable (wordRecordCount ℓ)).comp (measurable_firstWord ℓ))
    (conditioned_wordRecordCount_integrable ν ℓ htrans).1 _
    ((measurable_of_countable R).comp (measurable_firstWord ℓ)) r hr

lemma late_failure_cover_width {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (height : Lattice d → ℤ) (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ n, height (X (n+1)) ≤ height (X n)+1)
    (h B c b : ℕ) (hc : X ∈ FirstLayerHit height (h+B) c) (hcb : c ≤ b)
    (hb : height (X b) < h) :
    B < wordRecordCount ℓ (singleCoverWord ℓ h X) := by
  let k := renewalCount (fun j => wordRecordCount ℓ (regenerationWords ℓ X j)) h
  let t := regenerationTimes ℓ X (k+1)
  have ht := regenerationTimes_true ℓ X h0 hX (k+1)
  have hzero : height (X 0) = 0 := by
    have hh := hproj 0
    simp only [realPosition,dot,Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero] at hh
    rw [h0]
    exact_mod_cast hh.symm
  have he : height (X t) = (renewalSum (fun j => wordRecordCount ℓ (regenerationWords ℓ X j)) (k+1) : ℤ) := by
    rw [recordCount_eq_height_at_record ℓ height hproj X hstep ht.1,hzero,zero_add,
      recordCount_regenerationTimes ℓ X h0 hX]
    rfl
  have hl := renewalCount_lower (fun j => wordRecordCount ℓ (regenerationWords ℓ X j)) h
  have hu := renewalCount_upper (fun j => wordRecordCount ℓ (regenerationWords ℓ X j))
    (single_width_positive ℓ X hX) h
  change renewalSum _ k ≤ h at hl
  change h < renewalSum _ (k+1) at hu
  by_contra! hn
  change wordRecordCount ℓ (regenerationWords ℓ X k) ≤ B at hn
  have htH : height (X t) ≤ (h+B : ℕ) := by
    rw [he,renewalSum_succ]
    exact_mod_cast (Nat.add_le_add hl hn)
  have htc : t ≤ c := by
    by_contra! hh
    have hs := ht.1 c hh
    rw [hproj,hproj,hc.1] at hs
    exact (not_lt_of_ge (by exact_mod_cast htH)) hs
  have hh := ht.2 (b-t)
  rw [Nat.add_sub_of_le (htc.trans hcb),hproj,hproj] at hh
  have hh' : height (X t) ≤ height (X b) := by exact_mod_cast hh
  rw [he] at hh'
  have hu' : (h : ℤ) < (renewalSum (fun j => wordRecordCount ℓ (regenerationWords ℓ X j)) (k+1) : ℤ) := by
    exact_mod_cast hu
  omega

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma conditionedFrom_recenter {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) (A : Set (Path d)) (hA : MeasurableSet A) :
    conditionedFrom ν ℓ x ((fun X : Path d => fun n => X n-x) ⁻¹' A) = conditionedLaw ν ℓ A := by
  have hm : Measurable (fun X : Path d => fun n => X n-x) := by fun_prop
  rw [conditionedFrom,Measure.smul_apply,Measure.restrict_apply (hA.preimage hm),conditionedLaw,
    Measure.smul_apply,Measure.restrict_apply hA]
  congr 1
  have he : NoDrop ℓ x = (fun X : Path d => fun n => X n-x) ⁻¹' NoDrop ℓ 0 := by
    rw [noDrop_translation,add_zero]
  rw [he,← Set.preimage_inter,annealedFrom_apply ν x _ ((hA.inter (measurableSet_noDrop ℓ 0)).preimage hm),
    annealed_event_translation ν x _ (hA.inter (measurableSet_noDrop ℓ 0))]

lemma shared_recenter_marginal_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d)
    (c : ℝ) (hc : 0 < c) (hlo : ENNReal.ofReal c ≤ sharedNoDropMass ν ℓ x y)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    (sharedConditionedPairLaw ν ℓ x y).real {P | (fun n => P.1 n-x) ∈ A} ≤
      c⁻¹ * (conditionedLaw ν ℓ).real A := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hm : Measurable (fun X : Path d => fun n => X n-x) := by fun_prop
  have hh := sharedConditionedPairLaw_fst_le ν ℓ x y _ (hA.preimage hm) hp
  rw [conditionedFrom_recenter ν ℓ x A hA] at hh
  have hq : sharedNoDropMass ν ℓ x y ≠ 0 := ne_of_gt ((ENNReal.ofReal_pos.mpr hc).trans_le hlo)
  have hfin : (sharedNoDropMass ν ℓ x y)⁻¹ * annealedLaw ν (NoDrop ℓ 0) * conditionedLaw ν ℓ A ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hq) (measure_ne_top _ _))
      (by let _ := conditionedLaw_probability ν ℓ hp; exact measure_ne_top _ _)
  have hh' := ENNReal.toReal_mono hfin hh
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_inv] at hh'
  apply hh'.trans
  apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
  calc
    _ ≤ (sharedNoDropMass ν ℓ x y).toReal⁻¹ :=
      mul_le_of_le_one_right (inv_nonneg.mpr ENNReal.toReal_nonneg) (by exact measureReal_le_one)
    _ ≤ c⁻¹ := by
      apply inv_anti₀ hc
      have h := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (sharedNoDropMass_le_one ν ℓ x y)) hlo
      rwa [ENNReal.toReal_ofReal hc.le] at h

lemma shared_recenter_marginal_bound_snd {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d)
    (c : ℝ) (hc : 0 < c) (hlo : ENNReal.ofReal c ≤ sharedNoDropMass ν ℓ x y)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    (sharedConditionedPairLaw ν ℓ x y).real {P | (fun n => P.2 n-y) ∈ A} ≤
      c⁻¹ * (conditionedLaw ν ℓ).real A := by
  have hh := shared_recenter_marginal_bound ν ℓ htrans y x c hc
    (by rwa [sharedNoDropMass_swap]) A hA
  rw [← sharedConditionedPairLaw_swap ν ℓ x y,measureReal_def,Measure.map_apply measurable_swap
    (show MeasurableSet {P : Path d × Path d | (fun n => P.1 n-y) ∈ A} from hA.preimage (by fun_prop))] at hh
  exact hh

lemma height_sub {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ)) (x y : Lattice d) :
    height (x-y) = height x-height y := by
  have hh := dot_realPosition_sub x y ℓ
  rw [hproj,hproj,hproj] at hh
  exact_mod_cast hh

lemma measurableSet_lateFailure {d : ℕ} (height : Lattice d → ℤ) (h B : ℤ) :
    MeasurableSet (LateFailure height h B) := by
  simp only [LateFailure,Set.ofPred_exists,Set.ofPred_and]
  exact MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun b =>
    (measurableSet_firstLayerHit height (h+B) c).inter
      ((MeasurableSet.const (c ≤ b)).inter (measurableSet_lt
        ((measurable_of_countable height).comp (measurable_pi_apply b)) measurable_const))

lemma lateFailure_recenter {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (x : Lattice d) (h B : ℤ) (X : Path d) :
    X ∈ LateFailure height (height x+h) B ↔
      (fun n => X n-x) ∈ LateFailure height h B := by
  simp only [LateFailure,FirstLayerHit,Set.mem_ofPred_eq,height_sub ℓ height hproj]
  apply exists_congr
  intro c
  apply exists_congr
  intro b
  constructor <;> rintro ⟨⟨he,hlt⟩,hcb,hb⟩
  · exact ⟨⟨by omega,fun j hj => by have := hlt j hj; omega⟩,hcb,by omega⟩
  · exact ⟨⟨by omega,fun j hj => by have := hlt j hj; omega⟩,hcb,by omega⟩

lemma conditioned_late_failure_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1) (h B : ℕ) :
    (conditionedLaw ν ℓ).real (LateFailure height h B) ≤
      ∫ X, if B < wordRecordCount ℓ (firstWord ℓ X) then
        (wordRecordCount ℓ (firstWord ℓ X) : ℝ) else 0 ∂conditionedLaw ν ℓ := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hbnd := single_cover_event_bound ν ℓ htrans {w | B < wordRecordCount ℓ w}
    (Set.to_countable _).measurableSet h
  simp only [Set.mem_ofPred_eq] at hbnd
  refine le_trans (b := (conditionedLaw ν ℓ).real {X | B < wordRecordCount ℓ (singleCoverWord ℓ h X)}) ?_ ?_
  swap
  · convert hbnd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    apply integral_congr_ae
    filter_upwards [] with X
    congr 1
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  filter_upwards [conditioned_all_firstWords ν ℓ htrans,hac.ae_le (annealed_initial ν),
    hac.ae_le (annealed_nearest_neighbor ν)] with X hX h0 hnn hlate
  obtain ⟨c,b,hc,hcb,hb⟩ := hlate
  exact late_failure_cover_width ℓ X h0 hX height hproj (fun n => by
    obtain ⟨u,hu⟩ := hnn n; rw [hu]; exact hstep _ _) h B c b (by simpa only [Nat.cast_add] using hc) hcb hb

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SingleAdjacentRadiusBound
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
namespace DirectionalTransience

lemma single_adjacent_radius_bound {d : ℕ} (ℓ : Vector d) (e : Direction d) (X : Path d)
    (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (hs : ∀ h, 0 < h → X ∈ RecordIndexPrefix ℓ h (recordIndexTime ℓ h X)) (h : ℕ) :
    |signedCoordinate e (recordIndexPosition ℓ (h+1) X)-signedCoordinate e (recordIndexPosition ℓ h X)| ≤
      2*wordRadius (singleCoverWord ℓ h X) := by
  let k := renewalCount (fun j => wordRecordCount ℓ (regenerationWords ℓ X j)) h
  let j := regenerationTimes ℓ X k
  let t := regenerationTimes ℓ X (k+1)
  have ht := regenerationTimes_true ℓ X h0 hX
  have hl := renewalCount_lower (fun j => wordRecordCount ℓ (regenerationWords ℓ X j)) h
  have hu := renewalCount_upper (fun j => wordRecordCount ℓ (regenerationWords ℓ X j))
    (single_width_positive ℓ X hX) h
  have hc (n : ℕ) : recordCount ℓ X (regenerationTimes ℓ X n) =
      renewalSum (fun j => wordRecordCount ℓ (regenerationWords ℓ X j)) n :=
    recordCount_regenerationTimes ℓ X h0 hX n
  have hlow : recordCount ℓ X j ≤ h := by rw [hc]; exact hl
  have hupp : h < recordCount ℓ X t := by rw [hc]; exact hu
  have hbound0 : j ≤ recordIndexTime ℓ h X ∧ recordIndexTime ℓ h X ≤ t := by
    by_cases hh : h = 0
    · subst h
      simp only [k,renewalCount_zero,j,regenerationTimes_zero,recordIndexTime_zero,Nat.le_refl,Nat.zero_le,and_self]
    · exact (recordTime_between ℓ X (ht k).1 (hs h (Nat.pos_of_ne_zero hh)) hlow hupp).imp_right le_of_lt
  have hbound1 : j ≤ recordIndexTime ℓ (h+1) X ∧ recordIndexTime ℓ (h+1) X ≤ t := by
    have hn := hs (h+1) (Nat.succ_pos h)
    constructor
    · by_contra! hh
      have hlt := recordCount_lt_of_strictRecord ℓ X hh (ht k).1
      rw [hn.2.2.1] at hlt
      omega
    · by_contra! hh
      have hlt := recordCount_lt_of_strictRecord ℓ X hh hn.2.1
      rw [hn.2.2.1] at hlt
      omega
  have hw : ∀ a ≤ (regenerationWords ℓ X k).length, X (j+a)-X j = wordPath 0 (regenerationWords ℓ X k) a := by
    intro a ha
    rw [← iterate_renewSuffix_eq ℓ X h0 k a]
    exact (hX k).2.1 a ha
  have ht' : t = j+(regenerationWords ℓ X k).length := regenerationTimes_succ ℓ X k
  have h1 := coordinate_prefix_bound e X (regenerationWords ℓ X k) hw hbound0.1 (ht' ▸ hbound0.2)
  have h2 := coordinate_prefix_bound e X (regenerationWords ℓ X k) hw hbound1.1 (ht' ▸ hbound1.2)
  change |_ - _| ≤ 2*wordRadius (regenerationWords ℓ X k)
  calc
    _ = |(signedCoordinate e (X (recordIndexTime ℓ (h+1) X))-signedCoordinate e (X j))-
      (signedCoordinate e (X (recordIndexTime ℓ h X))-signedCoordinate e (X j))| := by
        dsimp only [recordIndexPosition]; congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (by linarith)

lemma conditioned_adjacent_radius_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ h : ℕ,
      |signedCoordinate e (recordIndexPosition ℓ (h+1) X)-signedCoordinate e (recordIndexPosition ℓ h X)| ≤
        2*wordRadius (singleCoverWord ℓ h X) := by
  have hs : ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ h, 0 < h → X ∈ RecordIndexPrefix ℓ h (recordIndexTime ℓ h X) := by
    apply ae_all_iff.mpr
    intro h
    by_cases hh : 0 < h
    · exact (conditioned_recordIndexTime_spec ν ℓ htrans hh).mono (fun _ hX _ => hX)
    · exact Eventually.of_forall fun _ hh' => (hh hh').elim
  filter_upwards [conditioned_all_firstWords ν ℓ htrans,
    (conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν),hs] with X hX h0 hs h
  exact single_adjacent_radius_bound ℓ e X h0 hX hs h

theorem conditioned_adjacent_increment_small {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (h : ℕ → ℕ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    Tendsto (fun i => (conditionedLaw ν ℓ).real {X |
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (h i+1) X)-
        signedCoordinate e (recordIndexPosition ℓ (h i) X)|}) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun i =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_))
    (single_cover_tail_small ν ℓ htrans wordRadius h (fun i => r i/2) (hr.atTop_div_const (by norm_num)))
  filter_upwards [conditioned_adjacent_radius_bound ν ℓ e htrans] with X hX hi
  change r i ≤ |signedCoordinate e (recordIndexPosition ℓ (h i+1) X)-
    signedCoordinate e (recordIndexPosition ℓ (h i) X)| at hi
  change r i / 2 ≤ |wordRadius (singleCoverWord ℓ (h i) X)|
  rw [abs_of_nonneg (wordRadius_nonneg _)]
  exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by linarith [hX (h i)])

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FiniteHitOscillation
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
namespace DirectionalTransience

lemma large_finite_difference_step (f : ℕ → ℝ) (h R j : ℕ) (hj : j ≤ R)
    {r : ℝ} (hr : 0 < r) (hf : r ≤ |f (h+j)-f h|) :
    ∃ k < R, r/(R+1) ≤ |f (h+k+1)-f (h+k)| := by
  by_contra! hn
  have ha : 0 < r/((R:ℝ)+1) := div_pos hr (by positivity)
  have hs : ∀ k ≤ R, |f (h+k)-f h| ≤ (k:ℝ)*(r/(R+1)) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hi := ih (by omega)
      have hh := (hn k (by omega)).le
      have he : f (h+(k+1))-f h = (f (h+k+1)-f (h+k))+(f (h+k)-f h) := by
        simp only [Nat.add_assoc]
        ring
      rw [he]
      have ht := abs_add_le (f (h+k+1)-f (h+k)) (f (h+k)-f h)
      push_cast
      nlinarith
  have hj' : (j:ℝ) < (R:ℝ)+1 := by exact_mod_cast Nat.lt_succ_of_le hj
  have ht : (j:ℝ)*(r/(R+1)) < r := by
    have hh := mul_lt_mul_of_pos_right hj' ha
    have he : ((R:ℝ)+1)*(r/(R+1)) = r := by field_simp
    rwa [he] at hh
  exact (not_lt_of_ge (hf.trans (hs j hj))) ht

lemma measurableSet_finiteHitOscillation {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (h R : ℕ) (r : ℝ) : MeasurableSet (FiniteHitOscillation ℓ e h R r) := by
  simp only [FiniteHitOscillation,Set.ofPred_exists,Set.ofPred_and]
  exact MeasurableSet.iUnion fun j => (MeasurableSet.const (j ≤ R)).inter
    (measurableSet_le measurable_const (((measurable_of_countable (signedCoordinate e)).comp
      (measurable_recordIndexPosition ℓ (h+j))).sub ((measurable_of_countable (signedCoordinate e)).comp
      (measurable_recordIndexPosition ℓ h))).abs)

theorem conditioned_finite_increment_small {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (R : ℕ) (h : ℕ → ℕ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    Tendsto (fun i => (conditionedLaw ν ℓ).real (FiniteHitOscillation ℓ e (h i) R (r i)))
      atTop (𝓝 0) := by
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let A := fun i k => {X : Path d | r i/(R+1) ≤
    |signedCoordinate e (recordIndexPosition ℓ (h i+k+1) X)-
      signedCoordinate e (recordIndexPosition ℓ (h i+k) X)|}
  have hlim (k : ℕ) : Tendsto (fun i => μ.real (A i k)) atTop (𝓝 0) :=
    conditioned_adjacent_increment_small ν ℓ e htrans (fun i => h i+k)
      (fun i => r i/(R+1)) (hr.atTop_div_const (by positivity))
  have hsum := tendsto_finsetSum (Finset.range R) (fun k _ => hlim k)
  simp only [Finset.sum_const_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hsum
  filter_upwards [hr.eventually_gt_atTop 0] with i hi
  have hsub : FiniteHitOscillation ℓ e (h i) R (r i) ⊆ ⋃ k ∈ Finset.range R, A i k := by
    rintro X ⟨j,hj,hX⟩
    obtain ⟨k,hk,hh⟩ := large_finite_difference_step
      (fun n => signedCoordinate e (recordIndexPosition ℓ n X)) (h i) R j hj hi hX
    exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hk,hh⟩⟩
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans
    (measureReal_biUnion_finset_le _ _)

theorem shared_finite_increment_small {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (e : Direction d) (htrans : DirectionallyTransient ν ℓ) (R : ℕ)
    (x y : ℕ → Lattice d) (h : ℕ → ℕ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    Tendsto (fun i => (sharedConditionedPairLaw ν ℓ (x i) (y i)).real
      {P | (fun n => P.1 n-x i) ∈ FiniteHitOscillation ℓ e (h i) R (r i) ∨
        (fun n => P.2 n-y i) ∈ FiniteHitOscillation ℓ e (h i) R (r i)}) atTop (𝓝 0) := by
  obtain ⟨c₀,hc₀,htruth₀⟩ := sharedNoDropMass_uniform_positive ν hue ℓ hℓ htrans
  have hcfin : c₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ((htruth₀ 0 0).trans (sharedNoDropMass_le_one ν ℓ 0 0))
  let c := c₀.toReal
  have hc : 0 < c := ENNReal.toReal_pos hc₀.ne' hcfin
  have htruth (u v : Lattice d) : ENNReal.ofReal c ≤ sharedNoDropMass ν ℓ u v := by
    dsimp [c]; rw [ENNReal.ofReal_toReal hcfin]; exact htruth₀ u v
  have hlim := (conditioned_finite_increment_small ν ℓ e htrans R h r hr).const_mul (2*c⁻¹)
  simp only [mul_zero] at hlim
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hlim
  intro i
  have h1 := shared_recenter_marginal_bound ν ℓ htrans (x i) (y i) c hc (htruth _ _)
    _ (measurableSet_finiteHitOscillation ℓ e (h i) R (r i))
  have h2 := shared_recenter_marginal_bound_snd ν ℓ htrans (x i) (y i) c hc (htruth _ _)
    _ (measurableSet_finiteHitOscillation ℓ e (h i) R (r i))
  have hq := ne_of_gt ((ENNReal.ofReal_pos.mpr hc).trans_le (htruth (x i) (y i)))
  let : IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (x i) (y i)) :=
    sharedConditionedPairLaw_probability ν ℓ (x i) (y i) hq
  have hh := add_le_add h1 h2
  have hu := measureReal_union_le (μ := sharedConditionedPairLaw ν ℓ (x i) (y i))
    {P | (fun n => P.1 n-x i) ∈ FiniteHitOscillation ℓ e (h i) R (r i)}
    {P | (fun n => P.2 n-y i) ∈ FiniteHitOscillation ℓ e (h i) R (r i)}
  exact hu.trans (hh.trans_eq (by ring))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstLayerHitRecordIndexTime
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
namespace DirectionalTransience

lemma noDrop_firstLayerHit_exists {d : ℕ} (e : Direction d) (X : Path d)
    (h0 : X 0 = 0) (hnn : ∀ n, ∃ f, X (n+1) = X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e))) {k : ℕ} (hk : 0 < k) :
    ∃ n, X ∈ FirstLayerHit (signedHeight e) k n := by
  apply firstLayerHit_exists (signedHeight e) (signedHeight_step_le e) X hnn
  · simpa only [TransientPaths,Set.mem_ofPred_eq,signedHeight_projection] using ht
  · rw [h0]
    simp only [signedHeight,Pi.zero_apply,ite_self,neg_zero]
    exact_mod_cast hk

lemma sharedConditionedPairLaw_absolutelyContinuous {d : ℕ} (ν : Measure (Row d))
    (ℓ : Vector d) (x y : Lattice d) :
    sharedConditionedPairLaw ν ℓ x y ≪ sharedPairLaw ν x y :=
  (Measure.smul_absolutelyContinuous).trans Measure.absolutelyContinuous_restrict

lemma sharedConditionedPairLaw_noDrop {d : ℕ} (ν : Measure (Row d))
    (ℓ : Vector d) (x y : Lattice d) :
    ∀ᵐ Z ∂sharedConditionedPairLaw ν ℓ x y, Z.1 ∈ NoDrop ℓ x ∧ Z.2 ∈ NoDrop ℓ y := by
  change ∀ᵐ Z ∂((sharedNoDropMass ν ℓ x y)⁻¹ •
    (sharedPairLaw ν x y).restrict (NoDrop ℓ x ×ˢ NoDrop ℓ y)), _
  apply Measure.smul_absolutelyContinuous.ae_le
  exact ae_restrict_mem ((measurableSet_noDrop ℓ x).prod (measurableSet_noDrop ℓ y))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_RegularPath
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
namespace DirectionalTransience

lemma measurableSet_regularPath {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    MeasurableSet (RegularPath ℓ x) := by
  apply (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
  apply MeasurableSet.inter _ (measurableSet_transientPaths ℓ)
  change MeasurableSet {X : Path d | ∀ n, ∃ f, X (n+1) = X n+step f}
  simp only [Set.ofPred_forall,Set.ofPred_exists]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun f =>
    measurableSet_eq_fun (by fun_prop : Measurable (fun X : Path d => X (n+1)))
      (by fun_prop : Measurable (fun X : Path d => X n+step f))

lemma annealedFrom_regularPath {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (x : Lattice d) :
    ∀ᵐ X ∂annealedFrom ν x, X ∈ RegularPath ℓ x := by
  apply annealedFrom_ae_of_quenched ν x _ (measurableSet_regularPath ℓ x)
  filter_upwards [quenched_directionallyTransient_ae ν ℓ htrans] with ω hω
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x),hω x] with X h0 hnn ht
  exact ⟨h0,hnn,ht⟩

lemma sharedConditioned_regularPath {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d) :
    ∀ᵐ Z ∂sharedConditionedPairLaw ν ℓ x y,
      (Z.1 ∈ RegularPath ℓ x ∧ Z.1 ∈ NoDrop ℓ x) ∧
      (Z.2 ∈ RegularPath ℓ y ∧ Z.2 ∈ NoDrop ℓ y) := by
  have hh := shared_pair_ae ν x y _ _ (measurableSet_regularPath ℓ x) (measurableSet_regularPath ℓ y)
    (annealedFrom_regularPath ν ℓ htrans x) (annealedFrom_regularPath ν ℓ htrans y)
  filter_upwards [(sharedConditionedPairLaw_absolutelyContinuous ν ℓ x y).ae_le hh,
    sharedConditionedPairLaw_noDrop ν ℓ x y] with Z hZ hD
  exact ⟨⟨hZ.1,hD.1⟩,hZ.2,hD.2⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_VisibleFailure
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
namespace DirectionalTransience

lemma measurableSet_visibleFailure {d : ℕ} (height : Lattice d → ℤ) (h B : ℤ) :
    MeasurableSet (VisibleFailure height h B) := by
  simp only [VisibleFailure,Set.ofPred_exists,Set.ofPred_and]
  refine MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun c => ?_
  exact (measurableSet_firstLayerHit height h a).inter
    ((measurableSet_firstLayerHit height (h+B) c).inter
    ((MeasurableSet.const (a ≤ b)).inter ((MeasurableSet.const (b < c)).inter
      (measurableSet_lt ((measurable_of_countable height).comp (measurable_pi_apply b)) measurable_const))))

lemma visibleFailure_prefix {d : ℕ} (height : Lattice d → ℤ) (h B H : ℤ)
    (hH : h+B ≤ H) (n : ℕ) (X Y : Path d)
    (hx : X ∈ FirstLayerHit height H n) (hy : Y ∈ FirstLayerHit height H n)
    (hxy : ∀ j ≤ n, X j = Y j) :
    X ∈ VisibleFailure height h B ↔ Y ∈ VisibleFailure height h B := by
  have aux (X Y : Path d) (hx : X ∈ FirstLayerHit height H n)
      (hxy : ∀ j ≤ n, X j = Y j) (hX : X ∈ VisibleFailure height h B) :
      Y ∈ VisibleFailure height h B := by
    obtain ⟨a,b,c,ha,hc,hab,hbc,hb⟩ := hX
    have hcn : c ≤ n := by
      by_contra hn
      have hh := hc.2 n (by omega)
      rw [hx.1] at hh
      omega
    have han : a ≤ n := by omega
    refine ⟨a,b,c,(firstLayerHit_prefix height h a X Y (fun j hj => hxy j (hj.trans han))).mp ha,
      (firstLayerHit_prefix height (h+B) c X Y (fun j hj => hxy j (hj.trans hcn))).mp hc,hab,hbc,?_⟩
    simpa only [← hxy b (by omega)] using hb
  exact ⟨aux X Y hx hxy,aux Y X hy (fun j hj => (hxy j hj).symm)⟩

lemma future_truth_not_visible {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ)) (h B : ℤ)
    (n : ℕ) (X : Path d) (hx : X ∈ FirstLayerHit height h n)
    (ht : X ∈ FutureNoDrop ℓ n) : X ∉ VisibleFailure height h B := by
  rintro ⟨a,b,c,ha,_,hab,_,hb⟩
  have he : a = n := by
    by_contra he
    exact Set.disjoint_left.mp (firstLayerHit_disjoint height h he) ha hx
  subst a
  have hh := ht (b-n)
  rw [Nat.add_sub_of_le hab,hproj,hproj,hx.1] at hh
  exact (not_le_of_gt hb) (by exact_mod_cast hh)

lemma measurableSet_visibleHistory {d : ℕ} (height : Lattice d → ℤ) (H B : ℤ) (m : ℕ) :
    MeasurableSet (VisibleHistory height H B m) := by
  simp only [VisibleHistory,Set.ofPred_forall,Set.ofPred_or]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    ((measurableSet_visibleFailure height (H+j*B) B).preimage measurable_fst).union
      ((measurableSet_visibleFailure height (H+j*B) B).preimage measurable_snd)

lemma visibleHistory_at_height_prefix {d : ℕ} (height : Lattice d → ℤ) (H B : ℤ)
    (hB : 0 ≤ B) (m : ℕ) (q : ℕ × ℕ) :
    PairPrefixDetermined q.1 q.2 (VisibleHistory height H B m ∩
      (FirstLayerHit height (H+m*B) q.1 ×ˢ FirstLayerHit height (H+m*B) q.2)) := by
  intro P Q h1 h2
  have he1 := firstLayerHit_prefix height (H+m*B) q.1 P.1 Q.1 h1
  have he2 := firstLayerHit_prefix height (H+m*B) q.2 P.2 Q.2 h2
  constructor
  · rintro ⟨hP,hP1,hP2⟩
    refine ⟨?_,he1.mp hP1,he2.mp hP2⟩
    intro j hj
    have hle : H+(j:ℤ)*B+B ≤ H+(m:ℤ)*B := by
      have hcast : (j:ℤ)+1 ≤ m := by exact_mod_cast hj
      nlinarith
    exact ((visibleFailure_prefix height (H+j*B) B (H+m*B) hle q.1 P.1 Q.1 hP1 (he1.mp hP1) h1).or
      (visibleFailure_prefix height (H+j*B) B (H+m*B) hle q.2 P.2 Q.2 hP2 (he2.mp hP2) h2)).mp (hP j hj)
  · rintro ⟨hQ,hQ1,hQ2⟩
    refine ⟨?_,he1.mpr hQ1,he2.mpr hQ2⟩
    intro j hj
    have hle : H+(j:ℤ)*B+B ≤ H+(m:ℤ)*B := by
      have hcast : (j:ℤ)+1 ≤ m := by exact_mod_cast hj
      nlinarith
    exact ((visibleFailure_prefix height (H+j*B) B (H+m*B) hle q.1 P.1 Q.1 (he1.mpr hQ1) hQ1 h1).or
      (visibleFailure_prefix height (H+j*B) B (H+m*B) hle q.2 P.2 Q.2 (he2.mpr hQ2) hQ2 h2)).mpr (hQ j hj)

theorem shared_visible_history_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1)
    (x y : Lattice d) (H B : ℤ) (hx : height x < H) (hy : height y < H) (hB : 0 ≤ B)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (htruth : ∀ u v, ENNReal.ofReal c ≤ sharedNoDropMass ν ℓ u v) (m : ℕ) :
    (sharedPairLaw ν x y).real (VisibleHistory height H B m) ≤ (1-c)^m := by
  let μ := sharedPairLaw ν x y
  have hrec (k : ℕ) : μ.real (VisibleHistory height H B (k+1)) ≤
      (1-c) * μ.real (VisibleHistory height H B k) := by
    let T := H+(k:ℤ)*B
    let A := fun q : ℕ × ℕ => VisibleHistory height H B k ∩
      (FirstLayerHit height T q.1 ×ˢ FirstLayerHit height T q.2)
    let F := fun q : ℕ × ℕ => A q ∩ (FutureNoDrop ℓ q.1 ×ˢ FutureNoDrop ℓ q.2)
    have hAm q : MeasurableSet (A q) := (measurableSet_visibleHistory height H B k).inter
      ((measurableSet_firstLayerHit height T q.1).prod (measurableSet_firstLayerHit height T q.2))
    have hFm q : MeasurableSet (F q) := (hAm q).inter
      ((measurableSet_futureNoDrop ℓ q.1).prod (measurableSet_futureNoDrop ℓ q.2))
    have hdisA : Pairwise (fun q r => Disjoint (A q) (A r)) := fun _ _ h =>
      (firstLayerHit_pair_disjoint height T h).mono Set.inter_subset_right Set.inter_subset_right
    have hdisF : Pairwise (fun q r => Disjoint (F q) (F r)) := fun _ _ h =>
      (hdisA h).mono Set.inter_subset_left Set.inter_subset_left
    have hxT : height x < T := by dsimp [T] <;> nlinarith [Int.natCast_nonneg k]
    have hyT : height y < T := by dsimp [T] <;> nlinarith [Int.natCast_nonneg k]
    have hcover : μ (⋃ q, A q) = μ (VisibleHistory height H B k) := by
      apply measure_congr
      filter_upwards [shared_pair_layer_hits ν ℓ htrans height hproj hstep x y T hxT hyT] with P hP
      apply propext
      constructor
      · intro hh
        obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hh
        exact hq.1
      · intro hh
        obtain ⟨n,hn⟩ := hP.1
        obtain ⟨l,hl⟩ := hP.2
        exact Set.mem_iUnion.mpr ⟨(n,l),hh,hn,hl⟩
    have hlow : ENNReal.ofReal c * μ (VisibleHistory height H B k) ≤ μ (⋃ q, F q) := by
      rw [← hcover,measure_iUnion hdisA hAm,measure_iUnion hdisF hFm,← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro q
      by_cases hq : 0 < q.1 ∧ 0 < q.2
      · apply shared_pair_record_event_noDrop_lower ν ℓ x y (ENNReal.ofReal c) htruth _ _ hq.1 hq.2
          (A q) (visibleHistory_at_height_prefix height H B hB k q)
        intro P hP
        exact ⟨firstLayerHit_record ℓ height hproj T _ _ hP.2.1,
          firstLayerHit_record ℓ height hproj T _ _ hP.2.2,
          by rw [hproj,hproj,hP.2.1.1,hP.2.2.1]⟩
      · have hz : μ (A q) = 0 := by
          apply measure_eq_zero_iff_ae_notMem.mpr
          filter_upwards [shared_pair_ae ν x y (RegularPath ℓ x) (RegularPath ℓ y)
            (measurableSet_regularPath ℓ x) (measurableSet_regularPath ℓ y)
            (annealedFrom_regularPath ν ℓ htrans x) (annealedFrom_regularPath ν ℓ htrans y)] with P hP hh
          have h1 := hh.2.1.1
          have h2 := hh.2.2.1
          have hn : q.1 = 0 ∨ q.2 = 0 := by omega
          rcases hn with hn | hn
          · rw [hn,hP.1.1] at h1; omega
          · rw [hn,hP.2.1] at h2; omega
        rw [hz,mul_zero]; exact zero_le
    have hdis : Disjoint (VisibleHistory height H B (k+1)) (⋃ q, F q) := by
      apply Set.disjoint_left.mpr
      intro P hp hf
      obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hf
      rcases hp k (by omega) with hh | hh
      · exact future_truth_not_visible ℓ height hproj T B q.1 P.1 hq.1.2.1 hq.2.1 hh
      · exact future_truth_not_visible ℓ height hproj T B q.2 P.2 hq.1.2.2 hq.2.2 hh
    have hsub : VisibleHistory height H B (k+1) ∪ (⋃ q, F q) ⊆ VisibleHistory height H B k := by
      intro P hp
      rcases hp with hp | hp
      · intro j hj; exact hp j (by omega)
      · obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hp; exact hq.1.1
    have hsum : μ (VisibleHistory height H B (k+1)) + ENNReal.ofReal c * μ (VisibleHistory height H B k) ≤
        μ (VisibleHistory height H B k) := by
      calc
        _ ≤ μ (VisibleHistory height H B (k+1)) + μ (⋃ q, F q) := by gcongr
        _ = μ (VisibleHistory height H B (k+1) ∪ (⋃ q, F q)) :=
          (measure_union hdis (MeasurableSet.iUnion hFm)).symm
        _ ≤ _ := measure_mono hsub
    have hr := ENNReal.toReal_mono (measure_ne_top _ _) hsum
    rw [ENNReal.toReal_add (measure_ne_top _ _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
      ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] at hr
    change μ.real (VisibleHistory height H B (k+1)) + c * μ.real (VisibleHistory height H B k) ≤ μ.real (VisibleHistory height H B k) at hr
    linarith
  induction m with
  | zero => simp [VisibleHistory,Measure.real]
  | succ m ih =>
    calc
      _ ≤ (1-c) * μ.real (VisibleHistory height H B m) := hrec m
      _ ≤ (1-c) * (1-c)^m := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1-c)^(m+1) := by ring

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonLayer
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
namespace DirectionalTransience

lemma failure_visible_or_late {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (H B : ℤ) (X : Path d) (a c : ℕ) (ha : X ∈ FirstLayerHit height H a)
    (hc : X ∈ FirstLayerHit height (H+B) c) (hfalse : X ∉ FutureNoDrop ℓ a) :
    X ∈ VisibleFailure height H B ∨ X ∈ LateFailure height H B := by
  change ¬ ∀ n, dot (realPosition (X a)) ℓ ≤ dot (realPosition (X (a+n))) ℓ at hfalse
  obtain ⟨n,hn⟩ := not_forall.mp hfalse
  have hn' : height (X (a+n)) < H := by
    rw [hproj,hproj,ha.1] at hn
    exact_mod_cast (lt_of_not_ge hn)
  by_cases hab : a+n < c
  · exact Or.inl ⟨a,a+n,c,ha,hc,Nat.le_add_right _ _,hab,hn'⟩
  · exact Or.inr ⟨c,a+n,hc,by omega,hn'⟩

lemma commonLayer_failure_cover {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (H B : ℤ) (P : Path d × Path d)
    (h1 : ∃ a, P.1 ∈ FirstLayerHit height H a) (h2 : ∃ a, P.2 ∈ FirstLayerHit height H a)
    (hc1 : ∃ a, P.1 ∈ FirstLayerHit height (H+B) a) (hc2 : ∃ a, P.2 ∈ FirstLayerHit height (H+B) a)
    (hfail : P ∉ CommonLayer ℓ height H) :
    (P.1 ∈ VisibleFailure height H B ∨ P.2 ∈ VisibleFailure height H B) ∨
      (P.1 ∈ LateFailure height H B ∨ P.2 ∈ LateFailure height H B) := by
  obtain ⟨a,ha⟩ := h1
  obtain ⟨b,hb⟩ := h2
  obtain ⟨c,hc⟩ := hc1
  obtain ⟨d,hd⟩ := hc2
  by_cases hta : P.1 ∈ FutureNoDrop ℓ a
  · have htb : P.2 ∉ FutureNoDrop ℓ b := fun hh => hfail ⟨a,b,ha,hb,hta,hh⟩
    rcases failure_visible_or_late ℓ height hproj H B P.2 b d hb hd htb with hv | hl
    · exact Or.inl (Or.inr hv)
    · exact Or.inr (Or.inr hl)
  · rcases failure_visible_or_late ℓ height hproj H B P.1 a c ha hc hta with hv | hl
    · exact Or.inl (Or.inl hv)
    · exact Or.inr (Or.inl hl)

lemma shared_conditioned_raw_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (c : ℝ) (hc : 0 < c)
    (hlo : ENNReal.ofReal c ≤ sharedNoDropMass ν ℓ x y)
    (A : Set (Path d × Path d)) (hA : MeasurableSet A) :
    (sharedConditionedPairLaw ν ℓ x y).real A ≤ c⁻¹ * (sharedPairLaw ν x y).real A := by
  have hq : sharedNoDropMass ν ℓ x y ≠ 0 := ne_of_gt ((ENNReal.ofReal_pos.mpr hc).trans_le hlo)
  rw [measureReal_def,sharedConditionedPairLaw,Measure.smul_apply,Measure.restrict_apply hA,
    smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv]
  apply mul_le_mul _ (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_left))
    ENNReal.toReal_nonneg (inv_nonneg.mpr hc.le)
  have hqfin := ne_top_of_le_ne_top ENNReal.one_ne_top (sharedNoDropMass_le_one ν ℓ x y)
  apply inv_anti₀ hc
  have hh := ENNReal.toReal_mono hqfin hlo
  rwa [ENNReal.toReal_ofReal hc.le] at hh

lemma singleWidthTail_tendsto {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    Tendsto (singleWidthTail ν ℓ) atTop (𝓝 0) := by
  have hm := (measurable_of_countable (wordRecordCount ℓ)).comp (measurable_firstWord ℓ)
  have hh := width_mark_tail_tendsto (conditionedLaw ν ℓ)
    (fun X => wordRecordCount ℓ (firstWord ℓ X)) hm (conditioned_wordRecordCount_integrable ν ℓ htrans).1
    (fun X => (wordRecordCount ℓ (firstWord ℓ X) : ℝ)) (by fun_prop)
    (fun B => (B:ℝ)+1) (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext B
  apply integral_congr_ae
  filter_upwards [] with X
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have he : B < wordRecordCount ℓ (firstWord ℓ X) ↔
      (B:ℝ)+1 ≤ (wordRecordCount ℓ (firstWord ℓ X) : ℝ) := by
    rw [← Nat.cast_one,← Nat.cast_add,Nat.cast_le]; omega
  simp only [he]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem shared_no_common_grid_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1)
    (x y : Lattice d) (hxy : height x = height y)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (htruth : ∀ u v, ENNReal.ofReal c ≤ sharedNoDropMass ν ℓ u v)
    (H B m : ℕ) (hH : 0 < H) :
    (sharedConditionedPairLaw ν ℓ x y).real
      (NoCommonGrid ℓ height (height x+H) B m) ≤
      c⁻¹*(1-c)^m + (m:ℝ)*(2*c⁻¹*singleWidthTail ν ℓ B) := by
  let μ := sharedConditionedPairLaw ν ℓ x y
  have hq := ne_of_gt ((ENNReal.ofReal_pos.mpr hc).trans_le (htruth x y))
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ x y hq
  let T := fun j : ℕ => height x+(H:ℤ)+(j:ℤ)*B
  let A := NoCommonGrid ℓ height (height x+H) B m
  let V := VisibleHistory height (height x+H) B m
  let L₁ := fun j => {P : Path d × Path d | P.1 ∈ LateFailure height (T j) B}
  let L₂ := fun j => {P : Path d × Path d | P.2 ∈ LateFailure height (T j) B}
  have hhits : ∀ᵐ P ∂μ, ∀ j : ℕ,
      (∃ a, P.1 ∈ FirstLayerHit height (T j) a) ∧ (∃ b, P.2 ∈ FirstLayerHit height (T j) b) := by
    apply (sharedConditionedPairLaw_absolutelyContinuous ν ℓ x y).ae_le
    apply ae_all_iff.mpr
    intro j
    apply shared_pair_layer_hits ν ℓ htrans height hproj hstep x y (T j)
    · dsimp [T]
      have hH' : (0:ℤ) < H := by exact_mod_cast hH
      have hjB : (0:ℤ) ≤ (j:ℤ)*B := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      omega
    · dsimp [T]
      rw [← hxy]
      have hH' : (0:ℤ) < H := by exact_mod_cast hH
      have hjB : (0:ℤ) ≤ (j:ℤ)*B := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      omega
  have hsub : (A : Set (Path d × Path d)) ≤ᵐ[μ] (V ∪ (⋃ j ∈ Finset.range m, L₁ j ∪ L₂ j) : Set (Path d × Path d)) := by
    filter_upwards [hhits] with P hP hA
    by_cases hv : P ∈ V
    · exact Or.inl hv
    · have hn : ∃ j < m, ¬ (P.1 ∈ VisibleFailure height (T j) B ∨ P.2 ∈ VisibleFailure height (T j) B) := by
        simpa only [V,VisibleHistory,Set.mem_ofPred_eq,not_forall,exists_prop,T] using hv
      obtain ⟨j,hjm,hj⟩ := hn
      have hj' : T (j+1) = T j+B := by dsimp [T] <;> ring
      have hh := commonLayer_failure_cover ℓ height hproj (T j) B P
        (hP j).1 (hP j).2 (by rw [← hj']; exact (hP (j+1)).1)
        (by rw [← hj']; exact (hP (j+1)).2) (hA j hjm)
      exact Or.inr (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hjm,hh.resolve_left hj⟩⟩)
  have hlate (j : ℕ) : μ.real (L₁ j) + μ.real (L₂ j) ≤ 2*c⁻¹*singleWidthTail ν ℓ B := by
    let C := LateFailure height (H+j*B) B
    have hC : MeasurableSet C := measurableSet_lateFailure height _ _
    have he1 : L₁ j = {P : Path d × Path d | (fun n => P.1 n-x) ∈ C} := by
      ext P
      change P.1 ∈ LateFailure height (T j) B ↔ _
      rw [show T j = height x+(H+j*B:ℕ) by dsimp [T]; ring]
      exact lateFailure_recenter ℓ height hproj x (H+j*B) B P.1
    have he2 : L₂ j = {P : Path d × Path d | (fun n => P.2 n-y) ∈ C} := by
      ext P
      change P.2 ∈ LateFailure height (T j) B ↔ _
      rw [show T j = height y+(H+j*B:ℕ) by dsimp [T]; rw [hxy]; ring]
      exact lateFailure_recenter ℓ height hproj y (H+j*B) B P.2
    have hb := conditioned_late_failure_bound ν ℓ htrans height hproj hstep (H+j*B) B
    have h1 := (shared_recenter_marginal_bound ν ℓ htrans x y c hc (htruth x y) C hC).trans
      (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le))
    have h2 := (shared_recenter_marginal_bound_snd ν ℓ htrans x y c hc (htruth x y) C hC).trans
      (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le))
    rw [he1,he2]
    dsimp only [μ]
    change _ ≤ 2*c⁻¹*singleWidthTail ν ℓ B
    change _ ≤ c⁻¹*singleWidthTail ν ℓ B at h1 h2
    linarith
  have hV : μ.real V ≤ c⁻¹*(1-c)^m := by
    apply (shared_conditioned_raw_bound ν ℓ x y c hc (htruth x y) V
      (measurableSet_visibleHistory height _ _ _)).trans
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
    apply shared_visible_history_bound ν ℓ htrans height hproj hstep x y (height x+H) B
      (by exact lt_add_of_pos_right _ (by exact_mod_cast hH))
      (by rw [← hxy]; exact lt_add_of_pos_right _ (by exact_mod_cast hH))
      (by exact_mod_cast Nat.zero_le B) c hc.le hc1 htruth m
  calc
    μ.real A ≤ μ.real (V ∪ (⋃ j ∈ Finset.range m, L₁ j ∪ L₂ j)) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ μ.real V + μ.real (⋃ j ∈ Finset.range m, L₁ j ∪ L₂ j) := measureReal_union_le _ _
    _ ≤ c⁻¹*(1-c)^m + ∑ j ∈ Finset.range m, (μ.real (L₁ j) + μ.real (L₂ j)) :=
      add_le_add hV ((measureReal_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum (fun j _ => measureReal_union_le _ _)))
    _ ≤ c⁻¹*(1-c)^m + ∑ _j ∈ Finset.range m, 2*c⁻¹*singleWidthTail ν ℓ B :=
      add_le_add_right (Finset.sum_le_sum (fun j _ => hlate j)) _
    _ = _ := by simp

theorem shared_common_overshoot_tight {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, ∀ x y : Lattice d, height x = height y → ∀ H : ℕ,
      (sharedConditionedPairLaw ν ℓ x y).real
        (NoCommonInterval ℓ height (height x+H) R) < ε := by
  obtain ⟨c₀,hc₀,htruth₀⟩ := sharedNoDropMass_uniform_positive ν hue ℓ hℓ htrans
  have hc₀1 : c₀ ≤ 1 := (htruth₀ 0 0).trans (sharedNoDropMass_le_one ν ℓ 0 0)
  have hc₀fin : c₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc₀1
  let c := c₀.toReal
  have hc : 0 < c := ENNReal.toReal_pos hc₀.ne' hc₀fin
  have hc1 : c ≤ 1 := by simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hc₀1
  have htruth (u v : Lattice d) : ENNReal.ofReal c ≤ sharedNoDropMass ν ℓ u v := by
    dsimp [c]; rw [ENNReal.ofReal_toReal hc₀fin]; exact htruth₀ u v
  have hgeo := (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hc1)
    (show 1-c < 1 by linarith)).const_mul c⁻¹
  simp only [mul_zero] at hgeo
  obtain ⟨m,hm⟩ := (hgeo.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity))).exists
  have htail := (singleWidthTail_tendsto ν ℓ htrans).const_mul ((m:ℝ)*(2*c⁻¹))
  simp only [mul_zero] at htail
  obtain ⟨B,hB⟩ := (htail.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity))).exists
  refine ⟨1+m*B,fun x y hxy H => ?_⟩
  have hq := ne_of_gt ((ENNReal.ofReal_pos.mpr hc).trans_le (htruth x y))
  let : IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ x y) := sharedConditionedPairLaw_probability ν ℓ x y hq
  have hsub : NoCommonInterval ℓ height (height x+H) (1+m*B) ⊆
      NoCommonGrid ℓ height (height x+(H+1:ℕ)) B m := by
    intro P hP j hj
    apply hP (height x+(H+1:ℕ)+(j:ℤ)*B)
    · have hb : (0:ℤ) ≤ (j:ℤ)*B := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      push_cast; omega
    · have hb : (j:ℤ)*B ≤ (m:ℤ)*B := mul_le_mul_of_nonneg_right (by exact_mod_cast hj.le) (Int.natCast_nonneg _)
      push_cast; omega
  have hbnd := (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans
    (shared_no_common_grid_bound ν ℓ htrans height hproj hstep x y hxy c hc hc1 htruth (H+1) B m (by omega))
  apply hbnd.trans_lt
  have hb : (m:ℝ)*(2*c⁻¹*singleWidthTail ν ℓ B) < ε/2 := by simpa only [mul_assoc] using hB
  linarith

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonOffset
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
namespace DirectionalTransience

lemma sharedNoDropMass_positive {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d) :
    0 < sharedNoDropMass ν ℓ x y := by
  obtain ⟨c,hc,hh⟩ := sharedNoDropMass_uniform_positive ν hue ℓ hℓ htrans
  exact hc.trans_le (hh x y)

lemma commonOffset_spec {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (H : ℤ) (P : Path d × Path d) (hex : ∃ k : ℕ, P ∈ CommonLayer ℓ height (H+k)) :
    P ∈ CommonLayer ℓ height (H+commonOffset ℓ height H P) :=
  (Nat.find_spec (commonOffset_exists ℓ height H P)).resolve_right (not_not.mpr hex)

lemma commonOffset_min {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (H : ℤ) (P : Path d × Path d) (n : ℕ) (hn : P ∈ CommonLayer ℓ height (H+n)) :
    commonOffset ℓ height H P ≤ n := Nat.find_min' _ (Or.inl hn)

lemma commonOffset_gt_subset {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (H : ℤ) (R : ℕ) : {P | R < commonOffset ℓ height H P} ⊆ NoCommonInterval ℓ height H R := by
  intro P hP q hq hR hC
  change R < commonOffset ℓ height H P at hP
  have hn : 0 ≤ q-H := sub_nonneg.mpr hq
  have he : H+(q-H).toNat = q := by rw [Int.toNat_of_nonneg hn]; omega
  have hh := commonOffset_min ℓ height H P (q-H).toNat (by rwa [he])
  have hle : (q-H).toNat ≤ R := by omega
  omega

lemma shared_common_boundary_exists {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1)
    (x y : Lattice d) (hxy : height x = height y) (H : ℕ) :
    ∀ᵐ P ∂sharedConditionedPairLaw ν ℓ x y, ∃ k : ℕ, P ∈ CommonLayer ℓ height (height x+H+k) := by
  have hq := ne_of_gt (sharedNoDropMass_positive ν hue ℓ hℓ htrans x y)
  let μ := sharedConditionedPairLaw ν ℓ x y
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ x y hq
  rw [ae_iff]
  rw [← measureReal_eq_zero_iff]
  apply le_antisymm _ measureReal_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R,hR⟩ := shared_common_overshoot_tight ν hue ℓ hℓ htrans height hproj hstep hε
  have hsub : {P : Path d × Path d | ¬ ∃ k : ℕ, P ∈ CommonLayer ℓ height (height x+H+k)} ⊆
      NoCommonInterval ℓ height (height x+H) R := by
    intro P hP q hq' _ hC
    have hn : 0 ≤ q-(height x+H) := sub_nonneg.mpr hq'
    apply hP
    refine ⟨(q-(height x+H)).toNat,?_⟩
    have he : height x+(H:ℤ)+(q-(height x+H)).toNat = q := by
      rw [Int.toNat_of_nonneg hn]
      omega
    rw [he]
    exact hC
  have hh := (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans_lt (hR x y hxy H)
  convert hh.le using 1 <;> first | rfl | exact zero_add _

theorem shared_common_displacement_small {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z f, height (z+step f) ≤ height z+1)
    (x y : ℕ → Lattice d) (hxy : ∀ i, height (x i) = height (y i))
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    Tendsto (fun i => (sharedConditionedPairLaw ν ℓ (x i) (y i)).real {P |
      let k := commonOffset ℓ height (height (x i)+H i) P
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (H i+k) (fun n => P.1 n-x i))-
        signedCoordinate e (recordIndexPosition ℓ (H i) (fun n => P.1 n-x i))| ∨
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (H i+k) (fun n => P.2 n-y i))-
        signedCoordinate e (recordIndexPosition ℓ (H i) (fun n => P.2 n-y i))|}) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨R,hR⟩ := shared_common_overshoot_tight ν hue ℓ hℓ htrans height hproj hstep
    (show 0 < ε/2 by positivity)
  have hfin := shared_finite_increment_small ν hue ℓ hℓ e htrans R x y H r hr
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hfin.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity)))
  refine ⟨N,fun i hi => ?_⟩
  let μ := sharedConditionedPairLaw ν ℓ (x i) (y i)
  have hq := ne_of_gt (sharedNoDropMass_positive ν hue ℓ hℓ htrans (x i) (y i))
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ (x i) (y i) hq
  let A := {P : Path d × Path d |
      let k := commonOffset ℓ height (height (x i)+H i) P
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (H i+k) (fun n => P.1 n-x i))-
        signedCoordinate e (recordIndexPosition ℓ (H i) (fun n => P.1 n-x i))| ∨
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (H i+k) (fun n => P.2 n-y i))-
        signedCoordinate e (recordIndexPosition ℓ (H i) (fun n => P.2 n-y i))|}
  let B := NoCommonInterval ℓ height (height (x i)+H i) R
  let C := {P : Path d × Path d | (fun n => P.1 n-x i) ∈ FiniteHitOscillation ℓ e (H i) R (r i) ∨
    (fun n => P.2 n-y i) ∈ FiniteHitOscillation ℓ e (H i) R (r i)}
  have hsub : A ⊆ B ∪ C := by
    intro P hP
    by_cases hk : R < commonOffset ℓ height (height (x i)+H i) P
    · exact Or.inl (commonOffset_gt_subset ℓ height _ R hk)
    · apply Or.inr
      rcases hP with hP | hP
      · exact Or.inl ⟨_,by omega,hP⟩
      · exact Or.inr ⟨_,by omega,hP⟩
  have hh := (ENNReal.toReal_mono (measure_ne_top μ (B ∪ C)) (measure_mono (μ := μ) hsub)).trans (measureReal_union_le B C)
  change μ.real A ≤ μ.real B + μ.real C at hh
  have hb : μ.real B < ε/2 := hR (x i) (y i) (hxy i) (H i)
  have hc : μ.real C < ε/2 := hN i hi
  change dist (μ.real A) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  linarith

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_GaussianBadCutoff
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
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
namespace DirectionalTransience

lemma measurable_physicalFirstHitGap {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x y : Lattice d) (H : ℕ) : Measurable (physicalFirstHitGap ℓ f x y H) := by
  exact measurable_const.add ((measurable_firstHitPairGap ℓ f H).comp (by fun_prop))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstLayerHitRecordPrefix
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
namespace DirectionalTransience

lemma firstLayerHit_recordPrefix {d : ℕ} (e : Direction d) (X : Path d)
    (h0 : X 0 = 0) (hD : X ∈ NoDrop (realPosition (step e)) 0)
    (hnn : ∀ n, ∃ f, X (n+1) = X n+step f) {k n : ℕ} (hk : 0 < k)
    (hX : X ∈ FirstLayerHit (signedHeight e) k n) :
    X ∈ RecordIndexPrefix (realPosition (step e)) k n := by
  let ℓ := realPosition (step e)
  have hs (j : ℕ) : signedHeight e (X (j+1)) ≤ signedHeight e (X j)+1 := by
    obtain ⟨f,hf⟩ := hnn j
    rw [hf]
    exact signedHeight_step_le e _ f
  have hr := firstLayerHit_record ℓ (signedHeight e) (signedHeight_projection e) k n X hX
  have hc := recordCount_eq_height_at_record ℓ (signedHeight e) (signedHeight_projection e) X hs hr
  have hz : signedHeight e (0 : Lattice d) = 0 := by simp [signedHeight]
  have hn : 0 < n := by
    by_contra hh
    have he : n = 0 := by omega
    have hh := hX.1
    rw [he,h0,hz] at hh
    omega
  refine ⟨hn,hr,?_,fun j _ => hD j⟩
  rw [hX.1,h0,hz,zero_add] at hc
  exact_mod_cast hc.symm

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IidListProcess
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma symmetricClip_apply (w : ℝ≥0) (z : ℝ) : symmetricClip w z = max (-(w:ℝ)) (min (w:ℝ) z) := rfl

lemma symmetricClip_bound (w : ℝ≥0) (z : ℝ) : |symmetricClip w z| ≤ w := by
  rw [symmetricClip_apply,abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith [w.coe_nonneg]) (min_le_left _ _)⟩

lemma symmetricClip_uniformContinuous (w : ℝ≥0) : UniformContinuous (symmetricClip w) := by
  have h : LipschitzWith 1 (fun z : ℝ => max (-(w:ℝ)) (min (w:ℝ) z)) := by
    convert (LipschitzWith.const (-(w:ℝ))).max ((LipschitzWith.const (w:ℝ)).min LipschitzWith.id) using 1
    · norm_num
    · rfl
  exact h.uniformContinuous

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RecordPairFuture
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
open MeasureTheory ProbabilityTheory Filter
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

lemma shared_pair_record_cylinder_rectangle {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hrf : StrictRecord ℓ f n) (hrg : StrictRecord ℓ g m)
    (he : dot (realPosition (f n)) ℓ = dot (realPosition (g m)) ℓ)
    (A B : Set (Path d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAD : A ⊆ NoDrop ℓ (f n)) (hBD : B ⊆ NoDrop ℓ (g m)) :
    sharedPairLaw ν x y
      (((fun X : Path d => fun j => X (n+j)) ⁻¹' A ∩ pathCylinder f n) ×ˢ
       ((fun X : Path d => fun j => X (m+j)) ⁻¹' B ∩ pathCylinder g m)) =
      sharedPairLaw ν x y (pathCylinder f n ×ˢ pathCylinder g m) *
        sharedPairLaw ν (f n) (g m) (A ×ˢ B) := by
  have hAf := (hA.preimage
    (show Measurable (fun X : Path d => fun j => X (n+j)) by fun_prop)).inter
    (measurableSet_pathCylinder f n)
  have hAg := (hB.preimage
    (show Measurable (fun X : Path d => fun j => X (m+j)) by fun_prop)).inter
    (measurableSet_pathCylinder g m)
  rw [sharedPairLaw_rectangle ν x y _ _ hAf hAg,
    sharedPairLaw_rectangle ν x y _ _ (measurableSet_pathCylinder f n)
      (measurableSet_pathCylinder g m),sharedPairLaw_rectangle ν (f n) (g m) A B hA hB]
  by_cases hf : f 0 = x
  · by_cases hg : g 0 = y
    · let S : Set (Lattice d) := {z | (∃ j < n, z = f j) ∨ (∃ j < m, z = g j)}
      let T := {z : Lattice d | dot (realPosition (f n)) ℓ ≤ dot (realPosition z) ℓ}
      have hdis : Disjoint S T := by
        apply Set.disjoint_left.mpr
        rintro z (⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩) hz
        · exact (not_le_of_gt (hrf j hj)) hz
        · have hlt := hrg j hj
          rw [← he] at hlt
          exact (not_le_of_gt hlt) hz
      have hfm : @Measurable _ _ (rowSigma S) _
          (fun ω : Environment d => quenchedKernel (ω,x) (pathCylinder f n)) := by
        apply measurable_of_row_locality _
          ((Kernel.measurable_coe _ (measurableSet_pathCylinder f n)).comp
            (measurable_id.prodMk measurable_const)) S x (Or.inl ⟨0,hn,hf.symm⟩)
        intro ω η hωη
        exact pathCylinder_weight_locality S ω η hωη x f n (fun j hj => Or.inl ⟨j,hj,rfl⟩)
      have hgm : @Measurable _ _ (rowSigma S) _
          (fun ω : Environment d => quenchedKernel (ω,y) (pathCylinder g m)) := by
        apply measurable_of_row_locality _
          ((Kernel.measurable_coe _ (measurableSet_pathCylinder g m)).comp
            (measurable_id.prodMk measurable_const)) S y (Or.inr ⟨0,hm,hg.symm⟩)
        intro ω η hωη
        exact pathCylinder_weight_locality S ω η hωη y g m (fun j hj => Or.inr ⟨j,hj,rfl⟩)
      have hnfm : @Measurable _ _ (rowSigma T) _ (fun ω : Environment d => quenchedKernel (ω,f n) A) :=
        measurable_quenched_stay_event_rows T (f n) (by
          change dot (realPosition (f n)) ℓ ≤ dot (realPosition (f n)) ℓ
          exact le_rfl) A hA hAD
      have hngm : @Measurable _ _ (rowSigma T) _ (fun ω : Environment d => quenchedKernel (ω,g m) B) := by
        apply measurable_quenched_stay_event_rows T (g m) (le_of_eq he) B hB
        intro X hX j
        change dot (realPosition (f n)) ℓ ≤ dot (realPosition (X j)) ℓ
        rw [he]
        exact hBD hX j
      simp_rw [quenched_prefix_future _ _ _ hf n hA,
        quenched_prefix_future _ _ _ hg m hB, mul_mul_mul_comm]
      have hind := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
        (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hdis)
        (hfm.mul hgm) (hnfm.mul hngm)
      simp only [Pi.mul_apply] at hind
      exact hind
    · have hz ω : quenchedKernel (ω,y)
          ((fun X : Path d => fun j => X (m+j)) ⁻¹' B ∩ pathCylinder g m) = 0 :=
        measure_mono_null Set.inter_subset_right (quenched_pathCylinder_zero ω y g hg m)
      simp only [hz, quenched_pathCylinder_zero _ _ _ hg m, mul_zero, lintegral_zero, zero_mul]
  · have hz ω : quenchedKernel (ω,x)
        ((fun X : Path d => fun j => X (n+j)) ⁻¹' A ∩ pathCylinder f n) = 0 :=
      measure_mono_null Set.inter_subset_right (quenched_pathCylinder_zero ω x f hf n)
    simp only [hz, quenched_pathCylinder_zero _ _ _ hf n, zero_mul, lintegral_zero]

lemma shared_pair_record_cylinder_future {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hrf : StrictRecord ℓ f n) (hrg : StrictRecord ℓ g m)
    (he : dot (realPosition (f n)) ℓ = dot (realPosition (g m)) ℓ)
    (E : Set (Path d × Path d)) (hE : MeasurableSet E)
    (hED : E ⊆ NoDrop ℓ (f n) ×ˢ NoDrop ℓ (g m)) :
    sharedPairLaw ν x y ((commonPairSuffix n m ⁻¹' E) ∩
      (pathCylinder f n ×ˢ pathCylinder g m)) =
      sharedPairLaw ν x y (pathCylinder f n ×ˢ pathCylinder g m)*
        sharedPairLaw ν (f n) (g m) E := by
  let C := pathCylinder f n ×ˢ pathCylinder g m
  let D := NoDrop ℓ (f n) ×ˢ NoDrop ℓ (g m)
  let M := ((sharedPairLaw ν x y).restrict C).map (commonPairSuffix n m)
  have hD : MeasurableSet D := (measurableSet_noDrop ℓ (f n)).prod (measurableSet_noDrop ℓ (g m))
  have hmeasure : M.restrict D = sharedPairLaw ν x y C • (sharedPairLaw ν (f n) (g m)).restrict D := by
    apply Measure.ext_prod
    intro A B hA hB
    rw [Measure.restrict_apply (hA.prod hB),Measure.smul_apply,Measure.restrict_apply (hA.prod hB)]
    have hab : (A ×ˢ B) ∩ D = (A ∩ NoDrop ℓ (f n)) ×ˢ (B ∩ NoDrop ℓ (g m)) := by
      ext P; simp only [D,Set.mem_inter_iff,Set.mem_prod]; tauto
    rw [hab]
    change (((sharedPairLaw ν x y).restrict C).map (commonPairSuffix n m)) _ = _
    rw [Measure.map_apply (measurable_commonPairSuffix n m)
      ((hA.inter (measurableSet_noDrop ℓ (f n))).prod (hB.inter (measurableSet_noDrop ℓ (g m)))),
      Measure.restrict_apply (by exact ((hA.inter (measurableSet_noDrop ℓ (f n))).prod
        (hB.inter (measurableSet_noDrop ℓ (g m)))).preimage (measurable_commonPairSuffix n m))]
    have hset : commonPairSuffix n m ⁻¹' ((A ∩ NoDrop ℓ (f n)) ×ˢ (B ∩ NoDrop ℓ (g m))) ∩ C =
        (((fun X : Path d => fun j => X (n+j)) ⁻¹' (A ∩ NoDrop ℓ (f n)) ∩ pathCylinder f n) ×ˢ
         ((fun X : Path d => fun j => X (m+j)) ⁻¹' (B ∩ NoDrop ℓ (g m)) ∩ pathCylinder g m)) := by
      ext P
      simp only [commonPairSuffix,C,Set.mem_preimage,Set.mem_inter_iff,Set.mem_prod]
      tauto
    rw [hset]
    exact shared_pair_record_cylinder_rectangle ν ℓ x y f g n m hn hm hrf hrg he _ _
      (hA.inter (measurableSet_noDrop ℓ (f n))) (hB.inter (measurableSet_noDrop ℓ (g m)))
      Set.inter_subset_right Set.inter_subset_right
  have hh := congrArg (fun μ : Measure (Path d × Path d) => μ E) hmeasure
  rw [Measure.restrict_apply hE,Measure.smul_apply,Measure.restrict_apply hE,
    Set.inter_eq_left.mpr hED] at hh
  change (((sharedPairLaw ν x y).restrict C).map (commonPairSuffix n m)) E = _ at hh
  rw [Measure.map_apply (measurable_commonPairSuffix n m) hE,
    Measure.restrict_apply (hE.preimage (measurable_commonPairSuffix n m))] at hh
  exact hh

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonBoundaryRestart
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

lemma measurableSet_truePairCylinder {d : ℕ} (ℓ : Vector d) (f g : Path d) (n m : ℕ) :
    MeasurableSet (truePairCylinder ℓ f g n m) :=
  ((measurableSet_pathCylinder f n).prod (measurableSet_pathCylinder g m)).inter
    ((measurableSet_futureNoDrop ℓ n).prod (measurableSet_futureNoDrop ℓ m))

lemma truePairCylinder_future {d : ℕ} (ℓ : Vector d) (f g : Path d) (n m : ℕ)
    (B : Set (Path d × Path d)) :
    commonPairSuffix n m ⁻¹' B ∩ truePairCylinder ℓ f g n m =
      commonPairSuffix n m ⁻¹' (B ∩ (NoDrop ℓ (f n) ×ˢ NoDrop ℓ (g m))) ∩
        (pathCylinder f n ×ˢ pathCylinder g m) := by
  ext P
  constructor
  · rintro ⟨hB,⟨hf,hg⟩,hD1,hD2⟩
    refine ⟨⟨hB,?_,?_⟩,hf,hg⟩
    · intro j
      change dot (realPosition (f n)) ℓ ≤ dot (realPosition (P.1 (n+j))) ℓ
      rw [← hf n le_rfl]
      exact hD1 j
    · intro j
      change dot (realPosition (g m)) ℓ ≤ dot (realPosition (P.2 (m+j))) ℓ
      rw [← hg m le_rfl]
      exact hD2 j
  · rintro ⟨⟨hB,hD1,hD2⟩,hf,hg⟩
    refine ⟨hB,⟨hf,hg⟩,?_,?_⟩
    · intro j
      rw [hf n le_rfl]
      exact hD1 j
    · intro j
      rw [hg m le_rfl]
      exact hD2 j

lemma truePairCylinder_noDrop {d : ℕ} (ℓ : Vector d) (f g : Path d) (n m : ℕ)
    (x y : Lattice d)
    (hf : ∀ j ≤ n, dot (realPosition x) ℓ ≤ dot (realPosition (f j)) ℓ)
    (hg : ∀ j ≤ m, dot (realPosition y) ℓ ≤ dot (realPosition (g j)) ℓ) :
    truePairCylinder ℓ f g n m ⊆ NoDrop ℓ x ×ˢ NoDrop ℓ y := by
  rintro P ⟨⟨hP,hQ⟩,hD,hE⟩
  constructor
  · apply (noDrop_iff_prefix_and_future ℓ x P.1 n hD).mpr
    intro j hj
    rw [hP j hj]
    exact hf j hj
  · apply (noDrop_iff_prefix_and_future ℓ y P.2 m hE).mpr
    intro j hj
    rw [hQ j hj]
    exact hg j hj

lemma shared_truePairCylinder_map {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (f g : Path d) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hrf : StrictRecord ℓ f n) (hrg : StrictRecord ℓ g m)
    (he : dot (realPosition (f n)) ℓ = dot (realPosition (g m)) ℓ)
    (hf : ∀ j ≤ n, dot (realPosition x) ℓ ≤ dot (realPosition (f j)) ℓ)
    (hg : ∀ j ≤ m, dot (realPosition y) ℓ ≤ dot (realPosition (g j)) ℓ)
    (hp : sharedNoDropMass ν ℓ (f n) (g m) ≠ 0) :
    ((sharedConditionedPairLaw ν ℓ x y).restrict (truePairCylinder ℓ f g n m)).map
      (commonPairSuffix n m) =
        sharedConditionedPairLaw ν ℓ x y (truePairCylinder ℓ f g n m) •
          sharedConditionedPairLaw ν ℓ (f n) (g m) := by
  let C := truePairCylinder ℓ f g n m
  let D := NoDrop ℓ (f n) ×ˢ NoDrop ℓ (g m)
  let a := (sharedNoDropMass ν ℓ x y)⁻¹ *
    sharedPairLaw ν x y (pathCylinder f n ×ˢ pathCylinder g m)
  have hC : MeasurableSet C := measurableSet_truePairCylinder ℓ f g n m
  have hCD : C ⊆ NoDrop ℓ x ×ˢ NoDrop ℓ y := truePairCylinder_noDrop ℓ f g n m x y hf hg
  have hD : MeasurableSet D := (measurableSet_noDrop ℓ (f n)).prod (measurableSet_noDrop ℓ (g m))
  have hfactor (B : Set (Path d × Path d)) (hB : MeasurableSet B) :
      sharedConditionedPairLaw ν ℓ x y (commonPairSuffix n m ⁻¹' B ∩ C) =
        a * sharedPairLaw ν (f n) (g m) (B ∩ D) := by
    rw [sharedConditionedPairLaw,Measure.smul_apply,
      Measure.restrict_apply ((hB.preimage (measurable_commonPairSuffix n m)).inter hC),
      Set.inter_eq_left.mpr (Set.Subset.trans Set.inter_subset_right hCD),
      truePairCylinder_future,
      shared_pair_record_cylinder_future ν ℓ x y f g n m hn hm hrf hrg he _
        (hB.inter hD) Set.inter_subset_right]
    simp only [smul_eq_mul,a,mul_assoc]
  have hmass : sharedConditionedPairLaw ν ℓ x y C = a * sharedNoDropMass ν ℓ (f n) (g m) := by
    simpa only [Set.preimage_univ,Set.univ_inter,sharedNoDropMass_eq,D] using
      hfactor Set.univ MeasurableSet.univ
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_commonPairSuffix n m) hB,
    Measure.restrict_apply (hB.preimage (measurable_commonPairSuffix n m)),hfactor B hB,
    Measure.smul_apply,hmass,sharedConditionedPairLaw,Measure.smul_apply,Measure.restrict_apply hB]
  have hfin : sharedNoDropMass ν ℓ (f n) (g m) ≠ ∞ :=
    ne_of_lt ((sharedNoDropMass_le_one ν ℓ (f n) (g m)).trans_lt (by simp))
  simp only [smul_eq_mul,mul_assoc]
  rw [← mul_assoc (sharedNoDropMass ν ℓ (f n) (g m)),ENNReal.mul_inv_cancel hp hfin,one_mul]

lemma boundaryPrefix_characterization {d : ℕ} (ℓ : Vector d) (H : ℝ)
    (x y : Lattice d) (f g : Path d) (n m : ℕ) (P : Path d × Path d)
    (hf : P.1 ∈ pathCylinder f n) (hg : P.2 ∈ pathCylinder g m) :
    (P.1 ∈ NoDrop ℓ x ∧ P.2 ∈ NoDrop ℓ y ∧ BoundaryAt ℓ H P n m) ↔
      (AdmissibleBoundaryPrefix ℓ H x y f g n m ∧
        P.1 ∈ FutureNoDrop ℓ n ∧ P.2 ∈ FutureNoDrop ℓ m) := by
  have hr1 j (hj : j ≤ n) : StrictRecord ℓ P.1 j ↔ StrictRecord ℓ f j :=
    strictRecord_congr_prefix ℓ hj hf
  have hr2 k (hk : k ≤ m) : StrictRecord ℓ P.2 k ↔ StrictRecord ℓ g k :=
    strictRecord_congr_prefix ℓ hk hg
  constructor
  · rintro ⟨hD1,hD2,hn,hm,⟨ht1,ht2,he⟩,hH,hfirst⟩
    refine ⟨⟨hn,hm,?_,(hr1 _ le_rfl).mp ht1.1,(hr2 _ le_rfl).mp ht2.1,
      ?_,?_,?_,?_⟩,ht1.2,ht2.2⟩
    · simpa only [hf _ le_rfl,hg _ le_rfl] using he
    · intro j hj
      simpa only [hf j hj] using hD1 j
    · intro k hk
      simpa only [hg k hk] using hD2 k
    · simpa only [hf _ le_rfl] using hH
    · intro j k hj hjn hk hkm hjH hrj hrk heq
      have hj' := (hr1 j hjn.le).mpr hrj
      have hk' := (hr2 k hkm.le).mpr hrk
      have he' : dot (realPosition (P.1 j)) ℓ = dot (realPosition (P.2 k)) ℓ := by
        simpa only [hf j hjn.le,hg k hkm.le] using heq
      have hnot := hfirst j k hj hjn hk hkm (by simpa only [hf j hjn.le] using hjH)
      have hdis : ¬ TrueRecord ℓ P.1 j ∨ ¬ TrueRecord ℓ P.2 k := by
        by_cases h1 : TrueRecord ℓ P.1 j
        · exact Or.inr fun h2 => hnot ⟨h1,h2,he'⟩
        · exact Or.inl h1
      rcases hdis with h1 | h2
      · obtain ⟨a,hja,han,ha⟩ := (not_trueRecord_before_true_iff ℓ P.1 hjn hj' ht1).mp h1
        exact Or.inl ⟨a,hja,han,by simpa only [hf a han.le,hf j hjn.le] using ha⟩
      · obtain ⟨b,hkb,hbm,hb⟩ := (not_trueRecord_before_true_iff ℓ P.2 hkm hk' ht2).mp h2
        exact Or.inr ⟨b,hkb,hbm,by simpa only [hg b hbm.le,hg k hkm.le] using hb⟩
  · rintro ⟨⟨hn,hm,he,hrf,hrg,hD1,hD2,hH,hfail⟩,hF1,hF2⟩
    have ht1 : TrueRecord ℓ P.1 n := ⟨(hr1 _ le_rfl).mpr hrf,hF1⟩
    have ht2 : TrueRecord ℓ P.2 m := ⟨(hr2 _ le_rfl).mpr hrg,hF2⟩
    refine ⟨(noDrop_iff_prefix_and_future ℓ x P.1 _ hF1).mpr ?_,
      (noDrop_iff_prefix_and_future ℓ y P.2 _ hF2).mpr ?_,
      hn,hm,⟨ht1,ht2,?_⟩,?_,?_⟩
    · intro j hj
      simpa only [hf j hj] using hD1 j hj
    · intro k hk
      simpa only [hg k hk] using hD2 k hk
    · simpa only [hf _ le_rfl,hg _ le_rfl] using he
    · simpa only [hf _ le_rfl] using hH
    · intro j k hj hjn hk hkm hjH htrue
      have hdis := hfail j k hj hjn hk hkm (by simpa only [hf j hjn.le] using hjH)
        ((hr1 _ hjn.le).mp htrue.1.1) ((hr2 _ hkm.le).mp htrue.2.1.1)
        (by simpa only [hf j hjn.le,hg k hkm.le] using htrue.2.2)
      rcases hdis with ⟨a,hja,han,ha⟩ | ⟨b,hkb,hbm,hb⟩
      · exact (not_trueRecord_before_true_iff ℓ P.1 hjn htrue.1.1 ht1).mpr
          ⟨a,hja,han,by simpa only [hf a han.le,hf j hjn.le] using ha⟩ htrue.1
      · exact (not_trueRecord_before_true_iff ℓ P.2 hkm htrue.2.1.1 ht2).mpr
          ⟨b,hkb,hbm,by simpa only [hg b hbm.le,hg k hkm.le] using hb⟩ htrue.2.1

lemma boundaryAt_unique {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d)
    {n m j k : ℕ} (hn : BoundaryAt ℓ H P n m) (hj : BoundaryAt ℓ H P j k) :
    n = j ∧ m = k := by
  have hnj : n = j := by
    rcases lt_trichotomy n j with h | h | h
    · exact False.elim (hj.2.2.2.2 n m hn.1 h hn.2.1
        ((commonTrueRecord_time_order ℓ P hn.2.2.1 hj.2.2.1).mp h) hn.2.2.2.1 hn.2.2.1)
    · exact h
    · exact False.elim (hn.2.2.2.2 j k hj.1 h hj.2.1
        ((commonTrueRecord_time_order ℓ P hj.2.2.1 hn.2.2.1).mp h) hj.2.2.2.1 hj.2.2.1)
  refine ⟨hnj,?_⟩
  apply Nat.le_antisymm
  · by_contra h
    have := (commonTrueRecord_time_order ℓ P hj.2.2.1 hn.2.2.1).mpr (by omega : k < m)
    omega
  · by_contra h
    have := (commonTrueRecord_time_order ℓ P hn.2.2.1 hj.2.2.1).mpr (by omega : m < k)
    omega

lemma boundaryAt_exists {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d)
    (h : ∃ n m, 0 < n ∧ 0 < m ∧ CommonTrueRecord ℓ P n m ∧
      H ≤ dot (realPosition (P.1 n)) ℓ) : ∃ n m, BoundaryAt ℓ H P n m := by
  obtain ⟨m,hn,hm,hr,hH⟩ := Nat.find_spec h
  exact ⟨Nat.find h,m,hn,hm,hr,hH,fun j k hj hjn hk _ hjH hc =>
    Nat.find_min h hjn ⟨k,hj,hk,hc,hjH⟩⟩

lemma measurableSet_boundaryAt {d : ℕ} (ℓ : Vector d) (H : ℝ) (n m : ℕ) :
    MeasurableSet {P : Path d × Path d | BoundaryAt ℓ H P n m} := by
  have hheight (j : ℕ) : MeasurableSet {P : Path d × Path d |
      H ≤ dot (realPosition (P.1 j)) ℓ} :=
    measurableSet_le measurable_const ((measurable_of_countable
      (fun z : Lattice d => dot (realPosition z) ℓ)).comp
      ((measurable_pi_apply j).comp measurable_fst))
  simp only [BoundaryAt,Set.ofPred_and,Set.ofPred_forall]
  refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((measurableSet_commonTrueRecord ℓ n m).inter ((hheight n).inter ?_)))
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
  convert (hheight j).compl.union (measurableSet_commonTrueRecord ℓ j k).compl using 1
  all_goals try with_reducible_and_instances rfl
  ext P
  simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_ofPred_eq,imp_iff_not_or]

lemma measurable_boundaryCode {d : ℕ} (ℓ : Vector d) (H : ℝ) :
    Measurable (boundaryCode ℓ H) := by
  apply measurable_find
  intro a
  apply (measurableSet_boundaryAt ℓ H _ _).union
  change MeasurableSet ({P : Path d × Path d | ∃ n m, BoundaryAt ℓ H P n m}ᶜ)
  simp only [Set.ofPred_exists]
  exact (MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
    measurableSet_boundaryAt ℓ H n m).compl

lemma measurable_boundaryTimes {d : ℕ} (ℓ : Vector d) (H : ℝ) :
    Measurable (boundaryTimes ℓ H) := (measurable_of_countable _).comp (measurable_boundaryCode ℓ H)

lemma boundaryTimes_spec {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d)
    (h : ∃ n m, BoundaryAt ℓ H P n m) :
    BoundaryAt ℓ H P (boundaryTimes ℓ H P).1 (boundaryTimes ℓ H P).2 :=
  (Nat.find_spec (boundaryCode_exists ℓ H P)).resolve_right (not_not.mpr h)

lemma boundaryTimes_eq {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d)
    {n m : ℕ} (h : BoundaryAt ℓ H P n m) : boundaryTimes ℓ H P = (n,m) := by
  exact Prod.ext (boundaryAt_unique ℓ H P (boundaryTimes_spec ℓ H P ⟨n,m,h⟩) h).1
    (boundaryAt_unique ℓ H P (boundaryTimes_spec ℓ H P ⟨n,m,h⟩) h).2

lemma boundaryAtom_eq {d : ℕ} (ℓ : Vector d) (H : ℝ) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : boundaryAtom ℓ H x y f g n m =
      if AdmissibleBoundaryPrefix ℓ H x y f g n m then truePairCylinder ℓ f g n m else ∅ := by
  by_cases ha : AdmissibleBoundaryPrefix ℓ H x y f g n m
  · rw [ite_eq_left ha]
    ext P
    constructor
    · rintro ⟨⟨hf,hg⟩,⟨hD,hE⟩,hB⟩
      have := (boundaryPrefix_characterization ℓ H x y f g n m P hf hg).mp ⟨hD,hE,hB⟩
      exact ⟨⟨hf,hg⟩,this.2⟩
    · rintro ⟨⟨hf,hg⟩,hD,hE⟩
      have := (boundaryPrefix_characterization ℓ H x y f g n m P hf hg).mpr ⟨ha,hD,hE⟩
      exact ⟨⟨hf,hg⟩,⟨this.1,this.2.1⟩,this.2.2⟩
  · rw [ite_eq_right ha]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro P ⟨⟨hf,hg⟩,⟨hD,hE⟩,hB⟩
    exact ha ((boundaryPrefix_characterization ℓ H x y f g n m P hf hg).mp ⟨hD,hE,hB⟩).1

lemma shared_boundaryAtom_map {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (H : ℝ) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) :
    ((sharedConditionedPairLaw ν ℓ x y).restrict (boundaryAtom ℓ H x y f g n m)).map
      (commonPairSuffix n m) =
        sharedConditionedPairLaw ν ℓ x y (boundaryAtom ℓ H x y f g n m) •
          sharedConditionedPairLaw ν ℓ (f n) (g m) := by
  rw [boundaryAtom_eq]
  split_ifs with ha
  · exact shared_truePairCylinder_map ν ℓ x y f g n m ha.1 ha.2.1
      ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.1 ha.2.2.2.2.2.1 ha.2.2.2.2.2.2.1
      (ne_of_gt (sharedNoDropMass_positive ν hue ℓ hℓ htrans _ _))
  · simp

lemma boundary_exists_of_commonLayer {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ)) (x y : Lattice d)
    (hxy : height x = height y) (H : ℕ) (hH : 0 < H) (P : Path d × Path d)
    (hx : P.1 0 = x) (hy : P.2 0 = y)
    (hex : ∃ k : ℕ, P ∈ CommonLayer ℓ height (height x+H+k)) :
    ∃ n m, BoundaryAt ℓ ((height x+H : ℤ) : ℝ) P n m := by
  obtain ⟨k,n,m,hn,hm,hD,hE⟩ := hex
  apply boundaryAt_exists
  have hnpos : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    have hi := hn.1
    rw [he,hx] at hi
    omega
  have hmpos : 0 < m := by
    by_contra h
    have he : m = 0 := by omega
    have hi := hm.1
    rw [he,hy,← hxy] at hi
    omega
  refine ⟨n,m,hnpos,hmpos,⟨⟨firstLayerHit_record ℓ height hproj _ n P.1 hn,hD⟩,
    ⟨firstLayerHit_record ℓ height hproj _ m P.2 hm,hE⟩,?_⟩,?_⟩
  · rw [hproj,hproj,hn.1,hm.1]
  · rw [hproj,hn.1]
    exact_mod_cast (show height x+(H:ℤ) ≤ height x+H+k by omega)

lemma shared_boundaryTimes_spec {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1)
    (x y : Lattice d) (hxy : height x = height y) (H : ℕ) (hH : 0 < H) :
    ∀ᵐ P ∂sharedConditionedPairLaw ν ℓ x y,
      BoundaryAt ℓ ((height x+H : ℤ) : ℝ) P
        (boundaryTimes ℓ ((height x+H : ℤ) : ℝ) P).1
        (boundaryTimes ℓ ((height x+H : ℤ) : ℝ) P).2 := by
  filter_upwards [sharedConditioned_regularPath ν ℓ htrans x y,
    shared_common_boundary_exists ν hue ℓ hℓ htrans height hproj hstep x y hxy H] with P hP hC
  exact boundaryTimes_spec ℓ _ P
    (boundary_exists_of_commonLayer ℓ height hproj x y hxy H hH P hP.1.1.1 hP.2.1.1 hC)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_JointPastRestart
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

lemma boundaryData_fiber {d : ℕ} (ℓ : Vector d) (H : ℝ) (F : BoundaryData d) :
    boundaryData ℓ H ⁻¹' {F} =
      (boundaryTimes ℓ H ⁻¹' {F.1}) ∩ (pairPrefix F.1.1 F.1.2 ⁻¹' {F.2}) := by
  ext P
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_inter_iff]
  constructor
  · intro he
    have ht : boundaryTimes ℓ H P = F.1 := congrArg Sigma.fst he
    refine ⟨ht,?_⟩
    cases F with
    | mk q f =>
      dsimp only at ht ⊢
      unfold boundaryData at he
      cases ht
      exact Sigma.mk.inj_iff.mp he |>.2 |> eq_of_heq
  · rintro ⟨ht,hf⟩
    cases F with
    | mk q f =>
      dsimp only at ht hf ⊢
      unfold boundaryData
      cases ht
      exact congrArg (Sigma.mk _) hf

lemma measurable_boundaryData {d : ℕ} (ℓ : Vector d) (H : ℝ) :
    Measurable (boundaryData ℓ H) := by
  apply measurable_to_countable'
  intro F
  rw [boundaryData_fiber]
  exact ((measurable_boundaryTimes ℓ H) (measurableSet_singleton _)).inter
    ((measurable_pairPrefix _ _) (measurableSet_singleton _))

lemma measurable_boundarySuffix {d : ℕ} (ℓ : Vector d) (H : ℝ) :
    Measurable (boundarySuffix ℓ H) := by
  have hm : Measurable (fun Z : (Path d × Path d) × (ℕ × ℕ) =>
      commonPairSuffix Z.2.1 Z.2.2 Z.1) :=
    measurable_from_prod_countable_left fun q => measurable_commonPairSuffix q.1 q.2
  exact hm.comp (measurable_id.prodMk (measurable_boundaryTimes ℓ H))

lemma boundaryData_times {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d)
    (F : BoundaryData d) (hF : boundaryData ℓ H P = F) :
    boundaryTimes ℓ H P = F.1 := congrArg Sigma.fst hF

lemma boundaryAtom_fiber_ae {d : ℕ} (μ : Measure (Path d × Path d))
    (ℓ : Vector d) (H : ℝ) (x y : Lattice d)
    (hD : ∀ᵐ P ∂μ, P.1 ∈ NoDrop ℓ x ∧ P.2 ∈ NoDrop ℓ y)
    (hS : ∀ᵐ P ∂μ, BoundaryAt ℓ H P (boundaryTimes ℓ H P).1 (boundaryTimes ℓ H P).2)
    (F : BoundaryData d) :
    (boundaryData ℓ H ⁻¹' {F}) =ᵐ[μ]
      boundaryAtom ℓ H x y (extendPrefix F.1.1 F.2.1) (extendPrefix F.1.2 F.2.2) F.1.1 F.1.2 := by
  filter_upwards [hD,hS] with P hDP hSP
  rw [boundaryData_fiber,pairPrefix_fiber]
  apply propext
  change (boundaryTimes ℓ H P = F.1 ∧ _) ↔ _
  constructor
  · rintro ⟨ht,hpre⟩
    refine ⟨hpre,hDP,?_⟩
    change BoundaryAt ℓ H P F.1.1 F.1.2
    simpa only [ht] using hSP
  · rintro ⟨hpre,hno,hB⟩
    exact ⟨boundaryTimes_eq ℓ H P hB,hpre⟩

lemma shared_boundaryData_map {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1)
    (x y : Lattice d) (hxy : height x = height y) (H : ℕ) (hH : 0 < H)
    (F : BoundaryData d) :
    ((sharedConditionedPairLaw ν ℓ x y).restrict
       (boundaryData ℓ ((height x+H : ℤ) : ℝ) ⁻¹' {F})).map
       (boundarySuffix ℓ ((height x+H : ℤ) : ℝ)) =
      sharedConditionedPairLaw ν ℓ x y
        (boundaryData ℓ ((height x+H : ℤ) : ℝ) ⁻¹' {F}) •
      sharedConditionedPairLaw ν ℓ
        (extendPrefix F.1.1 F.2.1 F.1.1) (extendPrefix F.1.2 F.2.2 F.1.2) := by
  let μ := sharedConditionedPairLaw ν ℓ x y
  let h : ℝ := ((height x+H : ℤ) : ℝ)
  have hae := boundaryAtom_fiber_ae μ ℓ h x y (sharedConditionedPairLaw_noDrop ν ℓ x y)
    (shared_boundaryTimes_spec ν hue ℓ hℓ htrans height hproj hstep x y hxy H hH) F
  have hmap : (μ.restrict (boundaryData ℓ h ⁻¹' {F})).map (boundarySuffix ℓ h) =
      (μ.restrict (boundaryData ℓ h ⁻¹' {F})).map (commonPairSuffix F.1.1 F.1.2) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem ((measurable_boundaryData ℓ h) (measurableSet_singleton F))] with P hP
    have ht := boundaryData_times ℓ h P F hP
    simp only [boundarySuffix,ht]
  change (μ.restrict (boundaryData ℓ h ⁻¹' {F})).map _ = _
  rw [hmap,Measure.restrict_congr_set hae,measure_congr hae]
  exact shared_boundaryAtom_map ν hue ℓ hℓ htrans h x y _ _ _ _

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RealJointPastRestart
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma integral_partition_countable {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] (μ : Measure Ω) (D : Ω → I) (hD : Measurable D)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    (∫ a, f a ∂μ) = ∑' i, ∫ a in D ⁻¹' {i}, f a ∂μ := by
  have hu : (⋃ i, D ⁻¹' {i}) = Set.univ := by ext a; simp
  have hd : Pairwise (fun i j : I => Disjoint (D ⁻¹' {i}) (D ⁻¹' {j})) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro a hi hj
    exact hij (hi.symm.trans hj)
  have hh := integral_iUnion (μ := μ) (fun i => hD (measurableSet_singleton i)) hd
    (show IntegrableOn f (⋃ i, D ⁻¹' {i}) μ by simpa only [hu,IntegrableOn,Measure.restrict_univ] using hf)
  simpa only [hu,Measure.restrict_univ] using hh

lemma integral_countable_restart {Ω I S : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [MeasurableSpace S] [Countable I] [MeasurableSingletonClass I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (D : Ω → I) (Y : Ω → S) (κ : I → Measure S)
    [∀ i, IsProbabilityMeasure (κ i)]
    (hD : Measurable D) (hY : Measurable Y)
    (hrestart : ∀ i, (μ.restrict (D ⁻¹' {i})).map Y = μ (D ⁻¹' {i}) • κ i)
    (g : I → S → ℝ) (hg : ∀ i, Measurable (g i))
    (C : ℝ) (hC : ∀ i z, ‖g i z‖ ≤ C) :
    (∫ a, g (D a) (Y a) ∂μ) = ∫ a, (∫ z, g (D a) z ∂κ (D a)) ∂μ := by
  have hgm : Measurable (fun p : S × I => g p.2 p.1) :=
    measurable_from_prod_countable_left hg
  have hm : Measurable (fun a => g (D a) (Y a)) := hgm.comp (hY.prodMk hD)
  have hmb : ∀ i, ‖∫ z, g i z ∂κ i‖ ≤ C := fun i => by
    simpa using norm_integral_le_of_norm_le_const (μ := κ i) (Filter.Eventually.of_forall (hC i))
  have hri : Integrable (fun a => ∫ z, g (D a) z ∂κ (D a)) μ :=
    Integrable.of_bound ((measurable_of_countable (fun i => ∫ z, g i z ∂κ i)).comp hD).aestronglyMeasurable
      C (Filter.Eventually.of_forall fun a => hmb (D a))
  rw [integral_partition_countable μ D hD _ (Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun a => hC (D a) (Y a))),integral_partition_countable μ D hD _ hri]
  apply tsum_congr
  intro i
  have ha : ∀ᵐ a ∂μ.restrict (D ⁻¹' {i}), D a = i :=
    ae_restrict_mem (hD (measurableSet_singleton i))
  calc
    (∫ a in D ⁻¹' {i}, g (D a) (Y a) ∂μ) = ∫ a in D ⁻¹' {i}, g i (Y a) ∂μ :=
      integral_congr_ae (ha.mono fun a ha => by dsimp only; rw [ha])
    _ = ∫ z, g i z ∂(μ.restrict (D ⁻¹' {i})).map Y := by
      rw [integral_map hY.aemeasurable (hg i).aestronglyMeasurable]
    _ = (μ (D ⁻¹' {i})).toReal * ∫ z, g i z ∂κ i := by
      rw [hrestart i,integral_smul_measure,smul_eq_mul]
    _ = ∫ a in D ⁻¹' {i}, (∫ z, g i z ∂κ i) ∂μ := by
      rw [integral_const,Measure.real,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,smul_eq_mul]
    _ = ∫ a in D ⁻¹' {i}, (∫ z, g (D a) z ∂κ (D a)) ∂μ :=
      integral_congr_ae (ha.mono fun a ha => by dsimp only; rw [ha])

lemma boundaryTerminal_data {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) :
    boundaryTerminal (boundaryData ℓ H P) =
      (P.1 (boundaryTimes ℓ H P).1,P.2 (boundaryTimes ℓ H P).2) := by
  simp [boundaryTerminal,boundaryData,pairPrefix,extendPrefix]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BoundaryDecorrelation
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
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

lemma measurable_pairSide {α : Type*} [MeasurableSpace α] (b : Bool) :
    Measurable (pairSide (α := α) b) := by
  cases b <;> exact (by first | exact measurable_fst | exact measurable_snd)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SharedEndpointTests
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma measurable_centeredFirstHit {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (k : ℕ) (x : Lattice d) : Measurable (centeredFirstHit ℓ f θ r k x) := by
  apply Measurable.div_const
  apply Measurable.sub_const
  exact ((measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ k)).comp (by fun_prop)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_OffDiagonalCenteredCross
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma abs_le_abs_sub_add (a b : ℝ) : |a| ≤ |a-b|+|b| := by
  calc
    |a| = |a-b+b| := by congr 1; ring
    _ ≤ |a-b|+|b| := abs_add_le _ _

lemma measurable_centeredClipCross {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (H : ℕ) (w : ℝ≥0) (x y : Lattice d) :
    Measurable (centeredClipCross ℓ f θ r H w x y) := by
  exact (((symmetricClip w).continuous.measurable.comp (measurable_centeredFirstHit _ _ _ _ _ _)).comp measurable_fst).mul
    (((symmetricClip w).continuous.measurable.comp (measurable_centeredFirstHit _ _ _ _ _ _)).comp measurable_snd)

lemma centeredClipCross_bound {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (H : ℕ) (w : ℝ≥0) (x y : Lattice d) (P : Path d × Path d) :
    ‖centeredClipCross ℓ f θ r H w x y P‖ ≤ (w:ℝ)^2 := by
  rw [Real.norm_eq_abs,centeredClipCross,abs_mul,pow_two]
  exact mul_le_mul (symmetricClip_bound _ _) (symmetricClip_bound _ _) (abs_nonneg _) w.coe_nonneg

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RestartSupportedBound
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
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

lemma countable_restart_supported_bound {Ω I S : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [MeasurableSpace S] [Countable I] [MeasurableSingletonClass I]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → I) (Y : Ω → S) (κ : I → Measure S) [∀ j, IsProbabilityMeasure (κ j)]
    (hD : Measurable D) (hY : Measurable Y)
    (hrestart : ∀ j, (μ.restrict (D ⁻¹' {j})).map Y = μ (D ⁻¹' {j}) • κ j)
    (V : I → Prop) (hV : ∀ᵐ a ∂μ, V (D a))
    (f : I → ℝ) (g : I → S → ℝ) (hg : ∀ j, Measurable (g j))
    (C M B : ℝ) (hC : 0≤C) (hB : 0≤B)
    (hf : ∀ j, ‖f j‖≤C) (hM : ∀ j z, ‖g j z‖≤M)
    (hbound : ∀ j, V j → f j ≠ 0 → |∫ z, g j z ∂κ j|≤B) :
    |∫ a, f (D a)*g (D a) (Y a) ∂μ|≤C*B := by
  rw [integral_countable_restart μ D Y κ hD hY hrestart
    (fun j z => f j*g j z) (fun j => (hg j).const_mul _) (C*M)
    (fun j z => by rw [norm_mul]; exact mul_le_mul (hf j) (hM j z) (norm_nonneg _) hC)]
  simp only [integral_const_mul]
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun a => f (D a)*(∫ z, g (D a) z ∂κ (D a))) (C := C*B)
    (hV.mono fun a ha => by
      rw [norm_mul]
      by_cases hz : f (D a)=0
      · simp only [hz,norm_zero,zero_mul]; exact mul_nonneg hC hB
      · rw [Real.norm_eq_abs]
        exact mul_le_mul (hf _) (hbound _ ha hz) (abs_nonneg _) hC)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using h

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_BoundaryCrossBound
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma shared_boundary_cross_bound {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i)=signedHeight e (y i))
    (H : ℕ → ℕ) (hH : ∀ i, 0<H i) (F : ℕ → BoundaryData d → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀ i j, ‖F i j‖≤C)
    (g : ℝ →ᵇ ℝ) (hg : ∀ z, |g z|≤1) {a t : ℝ} (ha : 0<a) (ht : 0<t)
    (hgzero : ∀ z, |z|≤a → g z=0) (w : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    let Y := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    ∀ᶠ i in atTop, |∫ P, F i (D i P)*
      g (signedCoordinate f ((boundaryTerminal (D i P)).1-(boundaryTerminal (D i P)).2)/r i)*
      centeredClipCross ℓ f (θ i) (r i) ⌊t*n i⌋₊ w
        (boundaryTerminal (D i P)).1 (boundaryTerminal (D i P)).2 (Y i P)
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)| ≤
      C*(16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t))+ε) := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let Y := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let κ := fun z : BoundaryData d => sharedConditionedPairLaw ν ℓ (boundaryTerminal z).1 (boundaryTerminal z).2
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  let : ∀ j, IsProbabilityMeasure (κ j) := fun j => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  have hu := shared_centered_cross_uniform_bound ν hue e f hef htrans r hrpos hr ha ht w hε
  filter_upwards [hu] with i hi
  apply countable_restart_supported_bound (μ i) (D i) (Y i) κ (measurable_boundaryData _ _)
    (measurable_boundarySuffix _ _)
    (shared_boundaryData_map ν hue ℓ (signed_direction_unit e) htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) (x i) (y i) (hxy i) (H i) (hH i))
    (fun z => signedHeight e (boundaryTerminal z).1=signedHeight e (boundaryTerminal z).2) ?_
    (fun j => F i j*g (signedCoordinate f ((boundaryTerminal j).1-(boundaryTerminal j).2)/r i))
    (fun j => centeredClipCross ℓ f _ (r i) _ w (boundaryTerminal j).1 (boundaryTerminal j).2)
    (fun j => measurable_centeredClipCross _ _ _ _ _ _ _ _) C ((w:ℝ)^2) _ hC (by positivity) ?_
    (fun j P => centeredClipCross_bound _ _ _ _ _ _ _ _ _) ?_
  · filter_upwards [shared_boundaryTimes_spec ν hue ℓ (signed_direction_unit e) htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) (x i) (y i) (hxy i) (H i) (hH i)] with P hP
    simp only [D,boundaryTerminal_data]
    have he := hP.2.2.1.2.2
    rw [signedHeight_projection e,signedHeight_projection e] at he
    exact_mod_cast he
  · intro j
    rw [norm_mul,Real.norm_eq_abs (g _)]
    exact (mul_le_mul (hF i j) (hg _) (abs_nonneg _) hC).trans_eq (mul_one C)
  · intro j hj hnon
    apply hi _ _ hj
    have hgn : g (signedCoordinate f ((boundaryTerminal j).1-(boundaryTerminal j).2)/r i) ≠ 0 := by
      intro hz
      exact hnon (by rw [hz,mul_zero])
    have hsep : a≤|signedCoordinate f ((boundaryTerminal j).1-(boundaryTerminal j).2)/r i| := by
      exact le_of_lt (lt_of_not_ge fun h => hgn (hgzero _ h))
    rw [abs_div,abs_of_pos (hrpos i)] at hsep
    have hh := (le_div_iff₀ (hrpos i)).mp hsep
    simpa only [signedCoordinate_sub,abs_sub_comm] using hh

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_BoundaryFirstHits
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma trueRecord_firstLayerHit {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ)) (X : Path d) (n : ℕ)
    (hn : TrueRecord ℓ X n) : X ∈ FirstLayerHit height (height (X n)) n := by
  refine ⟨rfl,?_⟩
  intro j hj
  have := hn.1 j hj
  rw [hproj,hproj] at this
  exact_mod_cast this

lemma firstCommonLayer_boundaryAt {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ)) (H : ℤ)
    (P : Path d × Path d) (hx : height (P.1 0) < H) (hy : height (P.2 0) < H)
    (n m : ℕ)
    (hn : P.1 ∈ FirstLayerHit height (H+commonOffset ℓ height H P) n)
    (hm : P.2 ∈ FirstLayerHit height (H+commonOffset ℓ height H P) m)
    (hD : P.1 ∈ FutureNoDrop ℓ n) (hE : P.2 ∈ FutureNoDrop ℓ m) :
    BoundaryAt ℓ (H : ℝ) P n m := by
  have hnpos : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    have hh := hn.1
    rw [he] at hh
    omega
  have hmpos : 0 < m := by
    by_contra h
    have he : m = 0 := by omega
    have hh := hm.1
    rw [he] at hh
    omega
  refine ⟨hnpos,hmpos,⟨⟨firstLayerHit_record ℓ height hproj _ n P.1 hn,hD⟩,
    ⟨firstLayerHit_record ℓ height hproj _ m P.2 hm,hE⟩,?_⟩,?_,?_⟩
  · rw [hproj,hproj,hn.1,hm.1]
  · rw [hproj,hn.1]
    exact_mod_cast (show H ≤ H+(commonOffset ℓ height H P : ℤ) by omega)
  · intro j k hj hjn hk hkm hjH hc
    have heq : height (P.1 j) = height (P.2 k) := by
      have he := hc.2.2
      rw [hproj,hproj] at he
      exact_mod_cast he
    have hHj : H ≤ height (P.1 j) := by
      rw [hproj] at hjH
      exact_mod_cast hjH
    have hcn : P ∈ CommonLayer ℓ height (H+(height (P.1 j)-H).toNat) := by
      have he : H+((height (P.1 j)-H).toNat : ℤ) = height (P.1 j) := by omega
      rw [he]
      exact ⟨j,k,trueRecord_firstLayerHit ℓ height hproj _ _ hc.1,
        by rw [heq]; exact trueRecord_firstLayerHit ℓ height hproj _ _ hc.2.1,
        hc.1.2,hc.2.1.2⟩
    have hmin := commonOffset_min ℓ height H P (height (P.1 j)-H).toNat hcn
    have hlt := hn.2 j hjn
    omega

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_BoundaryPathCoordinates
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

lemma recordIndexPosition_prefix_coord {d : ℕ} (e : Direction d) (X Y : Path d)
    (h0 : X 0 = 0) (hD : X ∈ NoDrop (realPosition (step e)) 0)
    (hnn : ∀ n, ∃ f, X (n+1) = X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e))) (n k : ℕ)
    (hk : (k : ℤ) ≤ signedHeight e (X n)) (hXY : ∀ j ≤ n, X j = Y j) :
    recordIndexPosition (realPosition (step e)) k X =
      recordIndexPosition (realPosition (step e)) k Y := by
  by_cases hz : k = 0
  · subst k
    simp only [recordIndexPosition,recordIndexTime_zero]
    exact hXY 0 (Nat.zero_le n)
  obtain ⟨m,hm⟩ := noDrop_firstLayerHit_exists e X h0 hnn ht (Nat.pos_of_ne_zero hz)
  have hmn : m ≤ n := by
    by_contra hh
    have hc := hm.2 n (by omega)
    omega
  have hr := firstLayerHit_recordPrefix e X h0 hD hnn (Nat.pos_of_ne_zero hz) hm
  have hr' := (recordIndexPrefix_prefix (realPosition (step e)) k m X Y
    (fun j hj => hXY j (hj.trans hmn))).mp hr
  simp only [recordIndexPosition,recordIndexTime_eq _ _ _ _ hr,recordIndexTime_eq _ _ _ _ hr']
  exact hXY m hmn

lemma regularPath_recenter {d : ℕ} (ℓ : Vector d) (x : Lattice d) (X : Path d)
    (hX : X ∈ RegularPath ℓ x) : (fun j => X j-x) ∈ RegularPath ℓ 0 := by
  refine ⟨by simp only [hX.1,sub_self],?_,?_⟩
  · intro n
    obtain ⟨f,hf⟩ := hX.2.1 n
    exact ⟨f,by dsimp only; rw [hf]; abel⟩
  · change X ∈ (fun Z : Path d => fun j => Z j-x) ⁻¹' TransientPaths ℓ
    rw [transientPaths_translation]
    exact hX.2.2

lemma noDrop_recenter {d : ℕ} (ℓ : Vector d) (x : Lattice d) (X : Path d)
    (hX : X ∈ NoDrop ℓ x) : (fun j => X j-x) ∈ NoDrop ℓ 0 := by
  change X ∈ (fun Z : Path d => fun j => Z j-x) ⁻¹' NoDrop ℓ 0
  rw [noDrop_translation]
  simpa only [add_zero] using hX

lemma trueRecord_recenter {d : ℕ} (ℓ : Vector d) (x : Lattice d) (X : Path d)
    (n : ℕ) (hn : TrueRecord ℓ X n) : TrueRecord ℓ (fun j => X j-x) n := by
  constructor
  · intro j hj
    dsimp only
    simp only [dot_realPosition_sub]
    exact sub_lt_sub_right (hn.1 j hj) _
  · intro j
    dsimp only
    simp only [dot_realPosition_sub]
    exact sub_le_sub_right (hn.2 j) _

lemma translated_recordIndexPosition_suffix {d : ℕ} (e : Direction d)
    (x : Lattice d) (X : Path d)
    (hX : X ∈ RegularPath (realPosition (step e)) x)
    (hD : X ∈ NoDrop (realPosition (step e)) x)
    (n H : ℕ) (hn : 0 < n) (htrue : TrueRecord (realPosition (step e)) X n)
    (hH : signedHeight e (X n) = signedHeight e x+H) (j : ℕ) :
    recordIndexPosition (realPosition (step e)) (j+H) (fun k => X k-x) =
      recordIndexPosition (realPosition (step e)) j (fun k => X (n+k)-X n)+(X n-x) := by
  let ℓ := realPosition (step e)
  let Z : Path d := fun k => X k-x
  have hZ : Z ∈ RegularPath ℓ 0 := regularPath_recenter ℓ x X hX
  have hZD := noDrop_recenter ℓ x X hD
  have hZT := trueRecord_recenter ℓ x X n htrue
  have hs (k : ℕ) : signedHeight e (Z (k+1)) ≤ signedHeight e (Z k)+1 := by
    obtain ⟨f,hf⟩ := hZ.2.1 k
    rw [hf]
    exact signedHeight_step_le e _ f
  have hc := recordCount_eq_height_at_record ℓ (signedHeight e) (signedHeight_projection e) Z hs hZT.1
  have hc' : recordCount ℓ Z n = H := by
    have h0 : signedHeight e (Z 0) = 0 := by rw [hZ.1]; simp [signedHeight]
    have hh : signedHeight e (Z n) = H := by dsimp [Z]; rw [signedHeight_sub,hH]; omega
    rw [h0,hh,zero_add] at hc
    exact_mod_cast hc.symm
  have hh := recordIndexPosition_suffix ℓ Z hZD hZ.2.2 hn hZT j
  rw [hc'] at hh
  convert hh using 2
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext k
  dsimp [Z]
  abel

lemma boundaryData_firstHit_prefix {d : ℕ} (e : Direction d) (x y : Lattice d)
    (hxy : signedHeight e x = signedHeight e y) (H : ℕ) (P : Path d × Path d)
    (hX : P.1 ∈ RegularPath (realPosition (step e)) x)
    (hY : P.2 ∈ RegularPath (realPosition (step e)) y)
    (hD : P.1 ∈ NoDrop (realPosition (step e)) x)
    (hE : P.2 ∈ NoDrop (realPosition (step e)) y)
    (hb : BoundaryAt (realPosition (step e)) ((signedHeight e x+H : ℤ) : ℝ) P
      (boundaryTimes (realPosition (step e)) ((signedHeight e x+H : ℤ) : ℝ) P).1
      (boundaryTimes (realPosition (step e)) ((signedHeight e x+H : ℤ) : ℝ) P).2)
    (j : ℕ) (hj : j ≤ H) :
    let F := boundaryData (realPosition (step e)) ((signedHeight e x+H : ℤ) : ℝ) P
    recordIndexPosition (realPosition (step e)) j (fun k => P.1 k-x) =
      recordIndexPosition (realPosition (step e)) j (fun k => extendPrefix F.1.1 F.2.1 k-x) ∧
    recordIndexPosition (realPosition (step e)) j (fun k => P.2 k-y) =
      recordIndexPosition (realPosition (step e)) j (fun k => extendPrefix F.1.2 F.2.2 k-y) := by
  dsimp only
  let ℓ := realPosition (step e)
  let L := ((signedHeight e x+H : ℤ) : ℝ)
  let q := boundaryTimes ℓ L P
  have hh : signedHeight e x+H ≤ signedHeight e (P.1 q.1) := by
    have hh := hb.2.2.2.1
    rw [signedHeight_projection e] at hh
    exact_mod_cast hh
  have he : signedHeight e (P.1 q.1) = signedHeight e (P.2 q.2) := by
    have he := hb.2.2.1.2.2
    rw [signedHeight_projection e,signedHeight_projection e] at he
    exact_mod_cast he
  have hxr := regularPath_recenter ℓ x P.1 hX
  have hyr := regularPath_recenter ℓ y P.2 hY
  constructor
  · apply recordIndexPosition_prefix_coord e _ _ hxr.1 (noDrop_recenter ℓ x P.1 hD)
      hxr.2.1 hxr.2.2 q.1 j
    · simp only [signedHeight_sub]
      omega
    · intro k hk
      change k ≤ (boundaryTimes (realPosition (step e)) ((signedHeight e x+H : ℤ) : ℝ) P).1 at hk
      change P.1 k-x = extendPrefix q.1 (Preorder.frestrictLe q.1 P.1) k-x
      rw [extendPrefix_apply _ _ _ hk]
      rfl
  · apply recordIndexPosition_prefix_coord e _ _ hyr.1 (noDrop_recenter ℓ y P.2 hE)
      hyr.2.1 hyr.2.2 q.2 j
    · simp only [signedHeight_sub]
      omega
    · intro k hk
      change k ≤ (boundaryTimes (realPosition (step e)) ((signedHeight e x+H : ℤ) : ℝ) P).2 at hk
      change P.2 k-y = extendPrefix q.2 (Preorder.frestrictLe q.2 P.2) k-y
      rw [extendPrefix_apply _ _ _ hk]
      rfl

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BoundarySuffixIdentity
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

lemma boundaryTimes_height_identity {d : ℕ} (e : Direction d)
    (x y : Lattice d) (hxy : signedHeight e x = signedHeight e y)
    (H : ℕ) (hH : 0 < H) (P : Path d × Path d)
    (hx : P.1 ∈ RegularPath (realPosition (step e)) x)
    (hy : P.2 ∈ RegularPath (realPosition (step e)) y)
    (hc : ∃ k : ℕ, P ∈ CommonLayer (realPosition (step e)) (signedHeight e) (signedHeight e x+H+k)) :
    let ℓ := realPosition (step e)
    let J := H+commonOffset ℓ (signedHeight e) (signedHeight e x+H) P
    let nm := boundaryTimes ℓ ((signedHeight e x+H : ℤ) : ℝ) P
    signedHeight e (P.1 nm.1) = signedHeight e x+J ∧
      signedHeight e (P.2 nm.2) = signedHeight e y+J := by
  dsimp only
  let ℓ := realPosition (step e)
  obtain ⟨n,m,hn,hm,hD,hE⟩ := commonOffset_spec ℓ (signedHeight e) (signedHeight e x+H) P hc
  have hb := firstCommonLayer_boundaryAt ℓ (signedHeight e) (signedHeight_projection e)
    (signedHeight e x+H) P (by rw [hx.1]; omega) (by rw [hy.1,← hxy]; omega)
    n m hn hm hD hE
  rw [boundaryTimes_eq ℓ _ P hb]
  constructor
  · simpa only [Nat.cast_add,add_assoc] using hn.1
  · simpa only [← hxy,Nat.cast_add,add_assoc] using hm.1

lemma boundarySuffix_record_identity {d : ℕ} (e : Direction d)
    (x y : Lattice d) (hxy : signedHeight e x = signedHeight e y)
    (H : ℕ) (hH : 0 < H) (P : Path d × Path d)
    (hx : P.1 ∈ RegularPath (realPosition (step e)) x)
    (hy : P.2 ∈ RegularPath (realPosition (step e)) y)
    (hD : P.1 ∈ NoDrop (realPosition (step e)) x)
    (hE : P.2 ∈ NoDrop (realPosition (step e)) y)
    (hc : ∃ k : ℕ, P ∈ CommonLayer (realPosition (step e)) (signedHeight e) (signedHeight e x+H+k))
    (j : ℕ) :
    let ℓ := realPosition (step e)
    let L := ((signedHeight e x+H : ℤ) : ℝ)
    let S := boundarySuffix ℓ L P
    let z := boundaryTerminal (boundaryData ℓ L P)
    let J := H+commonOffset ℓ (signedHeight e) (signedHeight e x+H) P
    recordIndexPosition ℓ (j+J) (fun k => P.1 k-x) =
      recordIndexPosition ℓ j (fun k => S.1 k-z.1)+(z.1-x) ∧
    recordIndexPosition ℓ (j+J) (fun k => P.2 k-y) =
      recordIndexPosition ℓ j (fun k => S.2 k-z.2)+(z.2-y) := by
  dsimp only
  let ℓ := realPosition (step e)
  let L := ((signedHeight e x+H : ℤ) : ℝ)
  let nm := boundaryTimes ℓ L P
  have hb : BoundaryAt ℓ L P nm.1 nm.2 := by
    obtain ⟨n,m,hn,hm,hDn,hEm⟩ := commonOffset_spec ℓ (signedHeight e) (signedHeight e x+H) P hc
    apply boundaryTimes_spec
    exact ⟨n,m,firstCommonLayer_boundaryAt ℓ (signedHeight e) (signedHeight_projection e)
      (signedHeight e x+H) P (by rw [hx.1]; omega) (by rw [hy.1,← hxy]; omega)
      n m hn hm hDn hEm⟩
  obtain ⟨hn,hm⟩ := boundaryTimes_height_identity e x y hxy H hH P hx hy hc
  constructor
  · simpa only [boundarySuffix,boundaryTerminal_data,commonPairSuffix] using
      translated_recordIndexPosition_suffix e x P.1 hx hD nm.1 _ hb.1 hb.2.2.1.1 hn j
  · simpa only [boundarySuffix,boundaryTerminal_data,commonPairSuffix] using
      translated_recordIndexPosition_suffix e y P.2 hy hE nm.2 _ hb.2.1 hb.2.2.1.2.1 hm j

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

theorem shared_common_shift_at_any_height_small {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z f, height (z+step f) ≤ height z+1)
    (x y : ℕ → Lattice d) (hxy : ∀ i, height (x i) = height (y i))
    (H J : ℕ → ℕ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    Tendsto (fun i => (sharedConditionedPairLaw ν ℓ (x i) (y i)).real {P |
      let k := commonOffset ℓ height (height (x i)+H i) P
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (J i+k) (fun n => P.1 n-x i))-
        signedCoordinate e (recordIndexPosition ℓ (J i) (fun n => P.1 n-x i))| ∨
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (J i+k) (fun n => P.2 n-y i))-
        signedCoordinate e (recordIndexPosition ℓ (J i) (fun n => P.2 n-y i))|}) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨R,hR⟩ := shared_common_overshoot_tight ν hue ℓ hℓ htrans height hproj hstep
    (show 0 < ε/2 by positivity)
  have hfin := shared_finite_increment_small ν hue ℓ hℓ e htrans R x y J r hr
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hfin.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity)))
  refine ⟨N,fun i hi => ?_⟩
  let μ := sharedConditionedPairLaw ν ℓ (x i) (y i)
  have hq := ne_of_gt (sharedNoDropMass_positive ν hue ℓ hℓ htrans (x i) (y i))
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ (x i) (y i) hq
  let A := {P : Path d × Path d |
      let k := commonOffset ℓ height (height (x i)+H i) P
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (J i+k) (fun n => P.1 n-x i))-
        signedCoordinate e (recordIndexPosition ℓ (J i) (fun n => P.1 n-x i))| ∨
      r i ≤ |signedCoordinate e (recordIndexPosition ℓ (J i+k) (fun n => P.2 n-y i))-
        signedCoordinate e (recordIndexPosition ℓ (J i) (fun n => P.2 n-y i))|}
  let B := NoCommonInterval ℓ height (height (x i)+H i) R
  let C := {P : Path d × Path d | (fun n => P.1 n-x i) ∈ FiniteHitOscillation ℓ e (J i) R (r i) ∨
    (fun n => P.2 n-y i) ∈ FiniteHitOscillation ℓ e (J i) R (r i)}
  have hsub : A ⊆ B ∪ C := by
    intro P hP
    by_cases hk : R < commonOffset ℓ height (height (x i)+H i) P
    · exact Or.inl (commonOffset_gt_subset ℓ height _ R hk)
    · apply Or.inr
      rcases hP with hP | hP
      · exact Or.inl ⟨_,by omega,hP⟩
      · exact Or.inr ⟨_,by omega,hP⟩
  have hh := (ENNReal.toReal_mono (measure_ne_top μ (B ∪ C)) (measure_mono (μ := μ) hsub)).trans (measureReal_union_le B C)
  change μ.real A ≤ μ.real B + μ.real C at hh
  have hb : μ.real B < ε/2 := hR (x i) (y i) (hxy i) (H i)
  have hc : μ.real C < ε/2 := hN i hi
  change dist (μ.real A) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  linarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma recordIndexPosition_at_zero {d : ℕ} (ℓ : Vector d) (X : Path d) :
    recordIndexPosition ℓ 0 X = X 0 := by simp [recordIndexPosition,recordIndexTime_zero]

lemma measurable_centeredHitIncrement {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (H k : ℕ) (x : Lattice d) : Measurable (centeredHitIncrement ℓ f θ r H k x) := by
  apply Measurable.div_const
  apply Measurable.sub_const
  apply Measurable.sub
  · exact ((measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ _)).comp (by fun_prop)
  · exact ((measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ _)).comp (by fun_prop)

lemma boundary_centered_increment_identity {d : ℕ} (e f : Direction d)
    (x y : Lattice d) (hxy : signedHeight e x = signedHeight e y)
    (H : ℕ) (hH : 0 < H) (P : Path d × Path d)
    (hx : P.1 ∈ RegularPath (realPosition (step e)) x)
    (hy : P.2 ∈ RegularPath (realPosition (step e)) y)
    (hD : P.1 ∈ NoDrop (realPosition (step e)) x)
    (hE : P.2 ∈ NoDrop (realPosition (step e)) y)
    (hc : ∃ k : ℕ, P ∈ CommonLayer (realPosition (step e)) (signedHeight e) (signedHeight e x+H+k))
    (k : ℕ) (θ r : ℝ) (b : Bool) :
    let ℓ := realPosition (step e)
    let L := ((signedHeight e x+H : ℤ) : ℝ)
    let K := commonOffset ℓ (signedHeight e) (signedHeight e x+H) P
    centeredFirstHit ℓ f θ r k (pairSide b (boundaryTerminal (boundaryData ℓ L P)))
      (pairSide b (boundarySuffix ℓ L P)) =
    centeredHitIncrement ℓ f θ r (H+K) k (pairSide b (x,y)) (pairSide b P) := by
  dsimp only
  have h0 := boundarySuffix_record_identity e x y hxy H hH P hx hy hD hE hc 0
  have hk := boundarySuffix_record_identity e x y hxy H hH P hx hy hD hE hc k
  dsimp only at h0 hk
  simp only [zero_add,recordIndexPosition_at_zero,boundarySuffix,commonPairSuffix,
    Nat.add_zero,boundaryTerminal_data,sub_self,zero_add] at h0
  cases b
  · simp only [pairSide,Bool.false_eq_true,ite_false, if_false,centeredFirstHit,centeredHitIncrement]
    rw [show H+commonOffset (realPosition (step e)) (signedHeight e) (signedHeight e x+H) P+k =
      k+(H+commonOffset (realPosition (step e)) (signedHeight e) (signedHeight e x+H) P) by omega]
    rw [hk.1,h0.1]
    simp only [signedCoordinate_add,signedCoordinate_sub,boundaryTerminal_data]
    ring
  · simp only [pairSide,ite_true, if_true,centeredFirstHit,centeredHitIncrement]
    rw [show H+commonOffset (realPosition (step e)) (signedHeight e) (signedHeight e x+H) P+k =
      k+(H+commonOffset (realPosition (step e)) (signedHeight e) (signedHeight e x+H) P) by omega]
    rw [hk.2,h0.2]
    simp only [signedCoordinate_add,signedCoordinate_sub,boundaryTerminal_data]
    ring

theorem shared_boundary_increment_replacement {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i))
    (H k : ℕ → ℕ) (hH : ∀ i, 0 < H i) (θ r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (b : Bool) (ε : ℝ) (hε : 0 < ε) :
    let ℓ := realPosition (step e)
    let L := fun i => ((signedHeight e (x i)+H i : ℤ) : ℝ)
    Tendsto (fun i => (sharedConditionedPairLaw ν ℓ (x i) (y i)).real {P |
      ε ≤ |centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (pairSide b (x i,y i)) (pairSide b P)-
        centeredFirstHit ℓ f (θ i) (r i) (k i)
          (pairSide b (boundaryTerminal (boundaryData ℓ (L i) P)))
          (pairSide b (boundarySuffix ℓ (L i) P))|}) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  let U := fun (i j : ℕ) (P : Path d × Path d) => signedCoordinate f (recordIndexPosition ℓ j
    (fun n => pairSide b P n-pairSide b (x i,y i)))
  let K := fun (i : ℕ) (P : Path d × Path d) => commonOffset ℓ (signedHeight e) (signedHeight e (x i)+H i) P
  let A := fun (J : ℕ → ℕ) i => {P : Path d × Path d | (ε/2)*r i ≤ |U i (J i+K i P) P-U i (J i) P|}
  have hA (J : ℕ → ℕ) : Tendsto (fun i => (μ i).real (A J i)) atTop (𝓝 0) := by
    have hh := shared_common_shift_at_any_height_small ν hue ℓ (signed_direction_unit e) f htrans
      (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) x y hxy H J
      (fun i => (ε/2)*r i) (hr.const_mul_atTop (by positivity))
    apply squeeze_zero (fun _ => measureReal_nonneg) _ hh
    intro i
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro P hP
    cases b
    · exact Or.inl hP
    · exact Or.inr hP
  have hsum := (hA H).add (hA (fun i => H i+k i))
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hsum
  filter_upwards [hr.eventually (eventually_gt_atTop (0:ℝ))] with i hri
  apply le_trans _ (measureReal_union_le (A H i) (A (fun j => H j+k j) i))
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [sharedConditioned_regularPath ν ℓ htrans (x i) (y i),
    shared_common_boundary_exists ν hue ℓ (signed_direction_unit e) htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) (x i) (y i) (hxy i) (H i)] with P hP hc
  intro hh
  have he := boundary_centered_increment_identity e f (x i) (y i) (hxy i) (H i) (hH i) P
    hP.1.1 hP.2.1 hP.1.2 hP.2.2 hc (k i) (θ i) (r i) b
  dsimp only at he
  change ε ≤ |_ - _| at hh
  rw [he] at hh
  change P ∈ A H i ∪ A (fun j => H j+k j) i
  by_contra hnot
  simp only [Set.mem_union,not_or, A,Set.mem_ofPred_eq,not_le] at hnot
  have hdiff : |(U i (H i+k i) P-U i (H i) P-(k i:ℝ)*θ i)/r i-
      (U i (H i+K i P+k i) P-U i (H i+K i P) P-(k i:ℝ)*θ i)/r i| < ε := by
    have huv : |(U i (H i+k i) P-U i (H i) P-(k i:ℝ)*θ i)-
        (U i (H i+K i P+k i) P-U i (H i+K i P) P-(k i:ℝ)*θ i)| ≤
        |U i (H i+k i+K i P) P-U i (H i+k i) P|+|U i (H i+K i P) P-U i (H i) P| := by
      rw [show H i+K i P+k i = H i+k i+K i P by omega]
      calc
        _ = |-(U i (H i+k i+K i P) P-U i (H i+k i) P)+
            (U i (H i+K i P) P-U i (H i) P)| := by congr 1; ring
        _ ≤ |-(U i (H i+k i+K i P) P-U i (H i+k i) P)|+
            |U i (H i+K i P) P-U i (H i) P| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    rw [← sub_div,abs_div,abs_of_pos hri,div_lt_iff₀ hri]
    linarith [hnot.1,hnot.2]
  exact not_lt_of_ge hh hdiff

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WeightedTestPerturbation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma weighted_test_perturbation {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X Y : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (F : ℕ → Ω → ℝ) (hF : ∀ i, Measurable (F i)) (C : ℝ) (hC : 0 ≤ C)
    (hFb : ∀ i ω, ‖F i ω‖ ≤ C)
    (f : ℝ →ᵇ ℝ) (hf : UniformContinuous f)
    (hclose : ∀ ε : ℝ, 0 < ε → Tendsto (fun i => (μ i).real {ω | ε ≤ |X i ω-Y i ω|}) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ ω, F i ω*(f (X i ω)-f (Y i ω)) ∂μ i) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let a := η/(2*(C+1))
  have ha : 0 < a := by dsimp [a] <;> positivity
  obtain ⟨δ,hδ,hδf⟩ := Metric.uniformContinuous_iff.mp hf a ha
  have hh : Tendsto (fun i => C*(2*‖f‖)*(μ i).real {ω | δ ≤ |X i ω-Y i ω|}) atTop (𝓝 0) := by
    simpa using (hclose δ hδ).const_mul (C*(2*‖f‖))
  filter_upwards [hh.eventually_lt_const (show (0:ℝ)<η/2 by positivity)] with i hi
  let A := {ω | δ ≤ |X i ω-Y i ω|}
  have hA : MeasurableSet A := measurableSet_le measurable_const ((hX i).sub (hY i)).abs
  have hg : Integrable (fun ω => C*a+A.indicator (fun _ => C*(2*‖f‖)) ω) (μ i) :=
    (integrable_const _).add ((integrable_const _).indicator hA)
  have hbound : ∀ᵐ ω ∂μ i, ‖F i ω*(f (X i ω)-f (Y i ω))‖ ≤
      C*a+A.indicator (fun _ => C*(2*‖f‖)) ω := by
    exact Eventually.of_forall fun ω => by
      rw [norm_mul]
      by_cases h : ω ∈ A
      · rw [Set.indicator_of_mem h]
        have hb := (norm_sub_le (f (X i ω)) (f (Y i ω))).trans
          (add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _))
        have hb' := mul_le_mul (hFb i ω) hb (norm_nonneg _) hC
        nlinarith
      · rw [Set.indicator_of_notMem h,add_zero]
        have hdist : dist (X i ω) (Y i ω) < δ := by
          simpa only [A,Set.mem_ofPred_eq,not_le,Real.dist_eq] using h
        have hb : ‖f (X i ω)-f (Y i ω)‖ ≤ a := by
          simpa only [Real.norm_eq_abs,Real.dist_eq] using (hδf hdist).le
        exact mul_le_mul (hFb i ω) hb (norm_nonneg _) hC
  have hIntegrable := hg.mono' ((hF i).mul ((f.continuous.measurable.comp (hX i)).sub
    (f.continuous.measurable.comp (hY i)))).aestronglyMeasurable hbound
  have hnorm := (norm_integral_le_integral_norm
    (fun sample => F i sample*(f (X i sample)-f (Y i sample)))).trans
    (integral_mono_ae hIntegrable.norm hg hbound)
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hA),
    integral_const,integral_indicator_const _ hA] at hnorm
  simp only [probReal_univ,smul_eq_mul,one_mul] at hnorm
  rw [Real.dist_eq,sub_zero]
  have hac : C*a < η/2 := by
    dsimp [a]
    have hden : 0 < 2*(C+1) := by positivity
    rw [← mul_div_assoc,div_lt_iff₀ hden]
    nlinarith
  change C*(2*‖f‖)*(μ i).real A < η/2 at hi
  rw [Real.norm_eq_abs] at hnorm
  nlinarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma measurable_boundary_terminal_side {d : ℕ} (ℓ : Vector d) (L : ℝ) (b : Bool) :
    Measurable (fun P : Path d × Path d => pairSide b (boundaryTerminal (boundaryData ℓ L P))) :=
  (measurable_of_countable (fun z : BoundaryData d => pairSide b (boundaryTerminal z))).comp
    (measurable_boundaryData ℓ L)

lemma measurable_boundary_centeredFirstHit {d : ℕ} (ℓ : Vector d)
    (f : Direction d) (θ r : ℝ) (k : ℕ) (L : ℝ) (b : Bool) :
    Measurable (fun P : Path d × Path d => centeredFirstHit ℓ f θ r k
      (pairSide b (boundaryTerminal (boundaryData ℓ L P)))
      (pairSide b (boundarySuffix ℓ L P))) := by
  apply Measurable.div_const
  apply Measurable.sub_const
  apply (measurable_of_countable (signedCoordinate f)).comp
  apply (measurable_recordIndexPosition ℓ k).comp
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply j).comp ((measurable_pairSide b).comp
    (measurable_boundarySuffix ℓ L))).sub (measurable_boundary_terminal_side ℓ L b)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BoundaryGapReplacement
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma boundary_gap_identity {d : ℕ} (e f : Direction d)
    (x y : Lattice d) (hxy : signedHeight e x=signedHeight e y)
    (H : ℕ) (hH : 0<H) (P : Path d × Path d)
    (hx : P.1 ∈ RegularPath (realPosition (step e)) x)
    (hy : P.2 ∈ RegularPath (realPosition (step e)) y)
    (hD : P.1 ∈ NoDrop (realPosition (step e)) x)
    (hE : P.2 ∈ NoDrop (realPosition (step e)) y)
    (hc : ∃ k : ℕ, P ∈ CommonLayer (realPosition (step e)) (signedHeight e) (signedHeight e x+H+k)) :
    let ℓ := realPosition (step e)
    let z := boundaryTerminal (boundaryData ℓ ((signedHeight e x+H : ℤ) : ℝ) P)
    signedCoordinate f (z.1-z.2)=physicalFirstHitGap ℓ f x y
      (H+commonOffset ℓ (signedHeight e) (signedHeight e x+H) P) P := by
  dsimp only
  have h0 := boundarySuffix_record_identity e x y hxy H hH P hx hy hD hE hc 0
  dsimp only at h0
  simp only [zero_add,recordIndexPosition_at_zero,boundarySuffix,commonPairSuffix,
    Nat.add_zero,boundaryTerminal_data,sub_self] at h0
  simp only [physicalFirstHitGap,firstHitPairGap,h0.1,h0.2,signedCoordinate_sub,boundaryTerminal_data]
  ring

lemma shared_boundary_gap_replacement {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i)=signedHeight e (y i))
    (H : ℕ → ℕ) (hH : ∀ i, 0<H i) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (ε : ℝ) (hε : 0<ε) :
    let ℓ := realPosition (step e)
    let z := fun i P => boundaryTerminal (boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ) P)
    Tendsto (fun i => (sharedConditionedPairLaw ν ℓ (x i) (y i)).real {P |
      ε≤|signedCoordinate f ((z i P).1-(z i P).2)/r i-
        physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i|}) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let z := fun i P => boundaryTerminal (boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ) P)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  have hsmall := shared_common_displacement_small ν hue ℓ (signed_direction_unit e) f htrans
    (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)
    x y hxy H (fun i => (ε/2)*r i) (hr.const_mul_atTop (by positivity : 0<ε/2))
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hsmall
  filter_upwards [hr.eventually_gt_atTop 0] with i hri
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [sharedConditioned_regularPath ν ℓ htrans (x i) (y i),
    shared_common_boundary_exists ν hue ℓ (signed_direction_unit e) htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) (x i) (y i) (hxy i) (H i)] with P hP hc
  intro hh
  have he := boundary_gap_identity e f (x i) (y i) (hxy i) (H i) (hH i) P
    hP.1.1 hP.2.1 hP.1.2 hP.2.2 hc
  dsimp only at he
  change ε≤|_ - _| at hh
  rw [he] at hh
  by_contra hn
  change ¬(_ ∨ _) at hn
  simp only [not_or,not_le] at hn
  have hp : ε*r i ≤ |physicalFirstHitGap ℓ f (x i) (y i)
      (H i+commonOffset ℓ (signedHeight e) (signedHeight e (x i)+H i) P) P-
      physicalFirstHitGap ℓ f (x i) (y i) (H i) P| := by
    rw [← sub_div,abs_div,abs_of_pos hri] at hh
    exact (le_div_iff₀ hri).mp hh
  dsimp [physicalFirstHitGap,firstHitPairGap] at hp
  have hab := abs_sub
    (signedCoordinate f (recordIndexPosition ℓ (H i+commonOffset ℓ (signedHeight e) (signedHeight e (x i)+H i) P) (fun n => P.1 n-x i))-
      signedCoordinate f (recordIndexPosition ℓ (H i) (fun n => P.1 n-x i)))
    (signedCoordinate f (recordIndexPosition ℓ (H i+commonOffset ℓ (signedHeight e) (signedHeight e (x i)+H i) P) (fun n => P.2 n-y i))-
      signedCoordinate f (recordIndexPosition ℓ (H i) (fun n => P.2 n-y i)))
  have heq : ∀ a b c d z : ℝ, z+(a-b)-(z+(c-d))=(a-c)-(b-d) := by intros; ring
  rw [heq] at hp
  linarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma weighted_product_test_perturbation {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X₁ Y₁ X₂ Y₂ : ℕ → Ω → ℝ)
    (hX₁ : ∀ i, Measurable (X₁ i)) (hY₁ : ∀ i, Measurable (Y₁ i))
    (hX₂ : ∀ i, Measurable (X₂ i)) (hY₂ : ∀ i, Measurable (Y₂ i))
    (F : ℕ → Ω → ℝ) (hF : ∀ i, Measurable (F i)) (C : ℝ) (hC : 0≤C)
    (hFb : ∀ i ω, ‖F i ω‖≤C) (f g : ℝ →ᵇ ℝ) (hf : UniformContinuous f) (hg : UniformContinuous g)
    (hc₁ : ∀ ε : ℝ, 0<ε → Tendsto (fun i => (μ i).real {ω | ε≤|X₁ i ω-Y₁ i ω|}) atTop (𝓝 0))
    (hc₂ : ∀ ε : ℝ, 0<ε → Tendsto (fun i => (μ i).real {ω | ε≤|X₂ i ω-Y₂ i ω|}) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ ω, F i ω*(f (X₁ i ω)*g (X₂ i ω)-f (Y₁ i ω)*g (Y₂ i ω)) ∂μ i)
      atTop (𝓝 0) := by
  have h1 := weighted_test_perturbation μ X₁ Y₁ hX₁ hY₁ (fun i ω => F i ω*g (X₂ i ω))
    (fun i => (hF i).mul (g.continuous.measurable.comp (hX₂ i))) (C*‖g‖) (by positivity)
    (fun i ω => by rw [norm_mul]; exact mul_le_mul (hFb i ω) (g.norm_coe_le_norm _) (norm_nonneg _) hC) f hf hc₁
  have h2 := weighted_test_perturbation μ X₂ Y₂ hX₂ hY₂ (fun i ω => F i ω*f (Y₁ i ω))
    (fun i => (hF i).mul (f.continuous.measurable.comp (hY₁ i))) (C*‖f‖) (by positivity)
    (fun i ω => by rw [norm_mul]; exact mul_le_mul (hFb i ω) (f.norm_coe_le_norm _) (norm_nonneg _) hC) g hg hc₂
  have hi (i : ℕ) (A B : Ω → ℝ) (hA : Measurable A) (hB : Measurable B)
      (α β : ℝ) (hbA : ∀ ω, ‖A ω‖≤α) (hbB : ∀ ω, ‖B ω‖≤β) (hα : 0≤α) :
      Integrable (fun ω => A ω*B ω) (μ i) :=
    Integrable.of_bound (hA.mul hB).aestronglyMeasurable (α*β) (ae_of_all _ fun ω => by
      rw [norm_mul]; exact mul_le_mul (hbA ω) (hbB ω) (norm_nonneg _) hα)
  have hs := h1.add h2
  simp only [add_zero] at hs
  apply hs.congr
  intro i
  rw [← integral_add]
  · congr 1
    funext ω
    ring
  · apply hi i _ _ ((hF i).mul (g.continuous.measurable.comp (hX₂ i)))
      ((f.continuous.measurable.comp (hX₁ i)).sub (f.continuous.measurable.comp (hY₁ i)))
      (C*‖g‖) (2*‖f‖)
    · intro ω
      change ‖F i ω * _‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (hFb i ω) (g.norm_coe_le_norm _) (norm_nonneg _) hC
    · intro ω
      change ‖f (X₁ i ω) - f (Y₁ i ω)‖ ≤ _
      exact (norm_sub_le _ _).trans (by linarith [f.norm_coe_le_norm (X₁ i ω),f.norm_coe_le_norm (Y₁ i ω)])
    · positivity
  · apply hi i _ _ ((hF i).mul (f.continuous.measurable.comp (hY₁ i)))
      ((g.continuous.measurable.comp (hX₂ i)).sub (g.continuous.measurable.comp (hY₂ i)))
      (C*‖f‖) (2*‖g‖)
    · intro ω
      change ‖F i ω * _‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul (hFb i ω) (f.norm_coe_le_norm _) (norm_nonneg _) hC
    · intro ω
      change ‖g (X₂ i ω) - g (Y₂ i ω)‖ ≤ _
      exact (norm_sub_le _ _).trans (by linarith [g.norm_coe_le_norm (X₂ i ω),g.norm_coe_le_norm (Y₂ i ω)])
    · positivity

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TripleTestPerturbation
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma weighted_three_test_perturbation {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X Y : Fin 3 → ℕ → Ω → ℝ)
    (hX : ∀ j i, Measurable (X j i)) (hY : ∀ j i, Measurable (Y j i))
    (F : ℕ → Ω → ℝ) (hF : ∀ i, Measurable (F i)) (C : ℝ) (hC : 0≤C)
    (hFb : ∀ i ω, ‖F i ω‖≤C) (f : Fin 3 → ℝ →ᵇ ℝ) (hf : ∀ j, UniformContinuous (f j))
    (hc : ∀ j ε, 0<ε → Tendsto (fun i => (μ i).real {ω | ε≤|X j i ω-Y j i ω|}) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ ω, F i ω*(f 0 (X 0 i ω)*f 1 (X 1 i ω)*f 2 (X 2 i ω)-
      f 0 (Y 0 i ω)*f 1 (Y 1 i ω)*f 2 (Y 2 i ω)) ∂μ i) atTop (𝓝 0) := by
  have h1 := weighted_product_test_perturbation μ (X 0) (Y 0) (X 1) (Y 1)
    (hX 0) (hY 0) (hX 1) (hY 1) (fun i ω => F i ω*f 2 (X 2 i ω))
    (fun i => (hF i).mul ((f 2).continuous.measurable.comp (hX 2 i)))
    (C*‖f 2‖) (by positivity) (fun i ω => by
      rw [norm_mul]
      exact mul_le_mul (hFb i ω) ((f 2).norm_coe_le_norm _) (norm_nonneg _) hC)
    (f 0) (f 1) (hf 0) (hf 1) (hc 0) (hc 1)
  have h2 := weighted_test_perturbation μ (X 2) (Y 2) (hX 2) (hY 2)
    (fun i ω => F i ω*(f 0 (Y 0 i ω)*f 1 (Y 1 i ω)))
    (fun i => (hF i).mul (((f 0).continuous.measurable.comp (hY 0 i)).mul
      ((f 1).continuous.measurable.comp (hY 1 i))))
    (C*(‖f 0‖*‖f 1‖)) (by positivity) (fun i ω => by
      simp only [norm_mul]
      exact mul_le_mul (hFb i ω) (mul_le_mul ((f 0).norm_coe_le_norm _)
        ((f 1).norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)) (by positivity) hC)
    (f 2) (hf 2) (hc 2)
  have hA (i) : Integrable (fun ω => F i ω*f 2 (X 2 i ω)*
      (f 0 (X 0 i ω)*f 1 (X 1 i ω)-f 0 (Y 0 i ω)*f 1 (Y 1 i ω))) (μ i) := by
    apply Integrable.of_bound (((hF i).mul ((f 2).continuous.measurable.comp (hX 2 i))).mul
      ((((f 0).continuous.measurable.comp (hX 0 i)).mul ((f 1).continuous.measurable.comp (hX 1 i))).sub
      (((f 0).continuous.measurable.comp (hY 0 i)).mul ((f 1).continuous.measurable.comp (hY 1 i))))).aestronglyMeasurable
      ((C*‖f 2‖)*(2*(‖f 0‖*‖f 1‖)))
    apply ae_of_all
    intro ω
    change ‖F i ω*f 2 (X 2 i ω)*(f 0 (X 0 i ω)*f 1 (X 1 i ω)-f 0 (Y 0 i ω)*f 1 (Y 1 i ω))‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
    · rw [norm_mul]; exact mul_le_mul (hFb i ω) ((f 2).norm_coe_le_norm _) (norm_nonneg _) hC
    · apply (norm_sub_le _ _).trans
      simp only [norm_mul]
      have hb (Z : Fin 3 → ℕ → Ω → ℝ) := mul_le_mul ((f 0).norm_coe_le_norm (Z 0 i ω))
        ((f 1).norm_coe_le_norm (Z 1 i ω)) (norm_nonneg _) (norm_nonneg _)
      linarith [hb X,hb Y]
  have hB (i) : Integrable (fun ω => F i ω*(f 0 (Y 0 i ω)*f 1 (Y 1 i ω))*
      (f 2 (X 2 i ω)-f 2 (Y 2 i ω))) (μ i) := by
    apply Integrable.of_bound (((hF i).mul (((f 0).continuous.measurable.comp (hY 0 i)).mul
      ((f 1).continuous.measurable.comp (hY 1 i)))).mul
      (((f 2).continuous.measurable.comp (hX 2 i)).sub ((f 2).continuous.measurable.comp (hY 2 i)))).aestronglyMeasurable
      ((C*(‖f 0‖*‖f 1‖))*(2*‖f 2‖))
    apply ae_of_all
    intro ω
    change ‖F i ω*(f 0 (Y 0 i ω)*f 1 (Y 1 i ω))*(f 2 (X 2 i ω)-f 2 (Y 2 i ω))‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
    · simp only [norm_mul]
      exact mul_le_mul (hFb i ω) (mul_le_mul ((f 0).norm_coe_le_norm _)
        ((f 1).norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)) (by positivity) hC
    · exact (norm_sub_le _ _).trans (by
        linarith [(f 2).norm_coe_le_norm (X 2 i ω), (f 2).norm_coe_le_norm (Y 2 i ω)])
  have hs := h1.add h2
  simp only [add_zero] at hs
  apply hs.congr
  intro i
  rw [← integral_add (hA i) (hB i)]
  congr 1
  funext ω
  ring

end DirectionalTransience

end

section

open MeasureTheory Filter
namespace DirectionalTransience

lemma integrable_bounded_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G)
    (C D : ℝ) (hC : 0≤C) (hFb : ∀ ω, ‖F ω‖≤C) (hGb : ∀ ω, ‖G ω‖≤D) :
    Integrable (fun ω => F ω*G ω) μ :=
  Integrable.of_bound (hF.mul hG).aestronglyMeasurable (C*D) (ae_of_all _ fun ω => by
    rw [norm_mul]; exact mul_le_mul (hFb ω) (hGb ω) (norm_nonneg _) hC)

lemma integral_weighted_sub_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G K : Ω → ℝ) (hF : Measurable F) (hG : Measurable G) (hK : Measurable K)
    (C D : ℝ) (hC : 0≤C) (hFb : ∀ ω, ‖F ω‖≤C) (hGb : ∀ ω, ‖G ω‖≤D) (hKb : ∀ ω, ‖K ω‖≤D) :
    (∫ ω, F ω*(G ω-K ω) ∂μ) = (∫ ω, F ω*G ω ∂μ)-(∫ ω, F ω*K ω ∂μ) := by
  simp_rw [mul_sub]
  exact integral_sub (integrable_bounded_mul μ F G hF hG C D hC hFb hGb)
    (integrable_bounded_mul μ F K hF hK C D hC hFb hKb)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_DeterministicCrossBound
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma shared_boundary_cross_replacement {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i)=signedHeight e (y i))
    (H k : ℕ → ℕ) (hH : ∀ i, 0<H i) (θ r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (F : ℕ → BoundaryData d → ℝ) (C : ℝ) (hC : 0≤C) (hF : ∀ i j, ‖F i j‖≤C)
    (g : ℝ →ᵇ ℝ) (hg : UniformContinuous g) (w : ℝ≥0) :
    let ℓ := realPosition (step e)
    let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    let S := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    Tendsto (fun i => ∫ P, F i (D i P)*(
      g (physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i)*
      (symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (x i) P.1)*
      symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (y i) P.2))-
      g (signedCoordinate f ((boundaryTerminal (D i P)).1-(boundaryTerminal (D i P)).2)/r i)*
      centeredClipCross ℓ f (θ i) (r i) (k i) w
        (boundaryTerminal (D i P)).1 (boundaryTerminal (D i P)).2 (S i P))
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let S := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  let X : Fin 3 → ℕ → (Path d × Path d) → ℝ := ![
    (fun i P => centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (x i) P.1),
    (fun i P => centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (y i) P.2),
    (fun i P => physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i)]
  let Y : Fin 3 → ℕ → (Path d × Path d) → ℝ := ![
    (fun i P => centeredFirstHit ℓ f (θ i) (r i) (k i) (boundaryTerminal (D i P)).1 (S i P).1),
    (fun i P => centeredFirstHit ℓ f (θ i) (r i) (k i) (boundaryTerminal (D i P)).2 (S i P).2),
    (fun i P => signedCoordinate f ((boundaryTerminal (D i P)).1-(boundaryTerminal (D i P)).2)/r i)]
  have hX (j i) : Measurable (X j i) := by
    fin_cases j
    · exact (measurable_centeredHitIncrement _ _ _ _ _ _ _).comp measurable_fst
    · exact (measurable_centeredHitIncrement _ _ _ _ _ _ _).comp measurable_snd
    · exact (measurable_physicalFirstHitGap _ _ _ _ _).div_const _
  have hY (j i) : Measurable (Y j i) := by
    fin_cases j
    · exact measurable_boundary_centeredFirstHit _ _ _ _ _ _ false
    · exact measurable_boundary_centeredFirstHit _ _ _ _ _ _ true
    · exact ((measurable_of_countable (fun z : BoundaryData d => signedCoordinate f
        ((boundaryTerminal z).1-(boundaryTerminal z).2))).comp (measurable_boundaryData _ _)).div_const _
  have hc (j) (ε : ℝ) (hε : 0<ε) : Tendsto (fun i => (μ i).real
      {P | ε≤|X j i P-Y j i P|}) atTop (𝓝 0) := by
    fin_cases j
    · exact shared_boundary_increment_replacement ν hue e f htrans x y hxy H k hH θ r hr false ε hε
    · exact shared_boundary_increment_replacement ν hue e f htrans x y hxy H k hH θ r hr true ε hε
    · change Tendsto (fun i => (μ i).real {P | ε≤|physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i-
        signedCoordinate f ((boundaryTerminal (D i P)).1-(boundaryTerminal (D i P)).2)/r i|}) atTop (𝓝 0)
      simpa only [abs_sub_comm] using shared_boundary_gap_replacement ν hue e f htrans x y hxy H hH r hr ε hε
  have hh := weighted_three_test_perturbation μ X Y hX hY (fun i P => F i (D i P))
    (fun i => (measurable_of_countable (F i)).comp (measurable_boundaryData _ _)) C hC
    (fun i P => hF i (D i P)) ![symmetricClip w,symmetricClip w,g]
    (by intro j; fin_cases j; exact symmetricClip_uniformContinuous w; exact symmetricClip_uniformContinuous w; exact hg) hc
  apply hh.congr
  intro i
  congr 1
  funext P
  change F i (D i P)*(
    symmetricClip w (X 0 i P)*symmetricClip w (X 1 i P)*g (X 2 i P)-
    symmetricClip w (Y 0 i P)*symmetricClip w (Y 1 i P)*g (Y 2 i P)) =
    F i (D i P)*(g (X 2 i P)*(symmetricClip w (X 0 i P)*symmetricClip w (X 1 i P))-
    g (Y 2 i P)*(symmetricClip w (Y 0 i P)*symmetricClip w (Y 1 i P)))
  ring

lemma shared_deterministic_cross_bound {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i)=signedHeight e (y i))
    (H : ℕ → ℕ) (hH : ∀ i, 0<H i) (F : ℕ → BoundaryData d → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀ i j, ‖F i j‖≤C)
    (g : ℝ →ᵇ ℝ) (hg : UniformContinuous g) (hgb : ∀ z, |g z|≤1)
    {a t : ℝ} (ha : 0<a) (ht : 0<t) (hgzero : ∀ z, |z|≤a → g z=0)
    (w : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    ∀ᶠ i in atTop, |∫ P, F i (D i P)*
      (g (physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i)*
      (symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) ⌊t*n i⌋₊ (x i) P.1)*
      symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) ⌊t*n i⌋₊ (y i) P.2)))
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)| ≤
      C*(16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t)))+ε := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  let k := fun i => ⌊t*n i⌋₊
  let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let S := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let A := fun i P => g (physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i)*
    (symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (x i) P.1)*
    symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i) (y i) P.2))
  let B := fun i P => g (signedCoordinate f ((boundaryTerminal (D i P)).1-(boundaryTerminal (D i P)).2)/r i)*
    centeredClipCross ℓ f (θ i) (r i) (k i) w (boundaryTerminal (D i P)).1 (boundaryTerminal (D i P)).2 (S i P)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  have hA (i) : Measurable (A i) := (g.continuous.measurable.comp ((measurable_physicalFirstHitGap _ _ _ _ _).div_const _)).mul
    (((symmetricClip w).continuous.measurable.comp ((measurable_centeredHitIncrement _ _ _ _ _ _ _).comp measurable_fst)).mul
    ((symmetricClip w).continuous.measurable.comp ((measurable_centeredHitIncrement _ _ _ _ _ _ _).comp measurable_snd)))
  have hB (i) : Measurable (B i) := (g.continuous.measurable.comp
    (((measurable_of_countable (fun z : BoundaryData d => signedCoordinate f ((boundaryTerminal z).1-(boundaryTerminal z).2))).comp
      (measurable_boundaryData _ _)).div_const _)).mul
    (((symmetricClip w).continuous.measurable.comp (measurable_boundary_centeredFirstHit _ _ _ _ _ _ false)).mul
    ((symmetricClip w).continuous.measurable.comp (measurable_boundary_centeredFirstHit _ _ _ _ _ _ true)))
  have hA_b (i P) : ‖A i P‖≤(w:ℝ)^2 := by
    dsimp only [A]
    simp only [Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ 1*((w:ℝ)*(w:ℝ)) := mul_le_mul (hgb _) (mul_le_mul (symmetricClip_bound _ _)
        (symmetricClip_bound _ _) (abs_nonneg _) w.coe_nonneg) (by positivity) (by norm_num)
      _ = _ := by ring
  have hB_b (i P) : ‖B i P‖≤(w:ℝ)^2 := by
    dsimp only [B]
    rw [norm_mul,Real.norm_eq_abs (g _)]
    exact (mul_le_mul (hgb _) (centeredClipCross_bound _ _ _ _ _ _ _ _ _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hd := shared_boundary_cross_replacement ν hue e f htrans x y hxy H k hH θ r hr.1 F C hC hF g hg w
  have hd' : Tendsto (fun i => (∫ P, F i (D i P)*A i P ∂μ i)-
      (∫ P, F i (D i P)*B i P ∂μ i)) atTop (𝓝 0) := by
    apply hd.congr
    intro i
    exact integral_weighted_sub_bounded (μ i) _ _ _ ((measurable_of_countable (F i)).comp
      (measurable_boundaryData _ _)) (hA i) (hB i) C ((w:ℝ)^2) hC (fun P => hF i (D i P)) (hA_b i) (hB_b i)
  have he : 0<ε/(2*(C+1)) := by positivity
  have hb := shared_boundary_cross_bound ν hue e f hef htrans r hrpos hr x y hxy H hH F C hC hF
    g hgb ha ht hgzero w he
  filter_upwards [hb,(Metric.tendsto_nhds.mp hd') (ε/2) (by positivity)] with i hi hj
  simp only [Real.dist_eq,sub_zero] at hj
  have hab := abs_le_abs_sub_add (∫ P, F i (D i P)*A i P ∂μ i) (∫ P, F i (D i P)*B i P ∂μ i)
  have hh : C*(ε/(2*(C+1))) ≤ ε/2 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  change |∫ P, F i (D i P)*A i P ∂μ i| ≤ _
  simp_rw [mul_assoc] at hi
  change |∫ P, F i (D i P)*B i P ∂μ i| ≤ _ at hi
  nlinarith

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_FinitePastCoordinates
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

lemma shared_centeredPastCoordinates_boundary {d q : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : Lattice d) (hxy : signedHeight e x = signedHeight e y)
    (H : ℕ) (hH : 0 < H) (j : Fin q → ℕ) (hj : ∀ a, j a ≤ H) (θ r : ℝ) :
    let ℓ := realPosition (step e)
    ∀ᵐ P ∂sharedConditionedPairLaw ν ℓ x y,
      centeredPastCoordinates ℓ f θ r j x y P =
      centeredPastCoordinates ℓ f θ r j x y
        (boundaryPrefixPair (boundaryData ℓ ((signedHeight e x+H : ℤ) : ℝ) P)) := by
  dsimp only
  let ℓ := realPosition (step e)
  filter_upwards [sharedConditioned_regularPath ν ℓ htrans x y,
    shared_boundaryTimes_spec ν hue ℓ (signed_direction_unit e) htrans
      (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) x y hxy H hH]
    with P hP hb
  funext a
  obtain ⟨h1,h2⟩ := boundaryData_firstHit_prefix e x y hxy H P
    hP.1.1 hP.2.1 hP.1.2 hP.2.2 hb (j a) (hj a)
  simp only [centeredPastCoordinates,centeredFirstHit,boundaryPrefixPair]
  rw [h1,h2]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FinitePastCrossBound
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma shared_finite_past_cross_bound_oai {d q : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i)=signedHeight e (y i))
    (H : ℕ → ℕ) (hH : ∀ i, 0<H i) (j : ℕ → Fin q → ℕ) (hj : ∀ i z, j i z≤H i)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ)
    (g : ℝ →ᵇ ℝ) (hg : UniformContinuous g) (hgb : ∀ z, |g z|≤1)
    {a t : ℝ} (ha : 0<a) (ht : 0<t) (hgzero : ∀ z, |z|≤a → g z=0)
    (w : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    ∀ᶠ i in atTop, |∫ P, F (centeredPastCoordinates ℓ f (θ i) (r i) (j i) (x i) (y i) P)*
      (g (physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i)*
      (symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) ⌊t*n i⌋₊ (x i) P.1)*
      symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) ⌊t*n i⌋₊ (y i) P.2)))
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)| ≤
      ‖F‖*(16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t)))+ε := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  let F' := fun i D => F (centeredPastCoordinates ℓ f (θ i) (r i) (j i) (x i) (y i) (boundaryPrefixPair D))
  have hh := shared_deterministic_cross_bound ν hue e f hef htrans r hrpos hr x y hxy H hH F'
    ‖F‖ (norm_nonneg _) (fun i D => F.norm_coe_le_norm _) g hg hgb ha ht hgzero w hε
  filter_upwards [hh] with i hi
  convert hi using 2
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [shared_centeredPastCoordinates_boundary ν hue e f htrans (x i) (y i) (hxy i)
    (H i) (hH i) (j i) (hj i) (θ i) (r i)] with P hP
  dsimp only [F']
  rw [hP]

end DirectionalTransience

end

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.shared_finite_past_cross_bound_oai := @OAI.DirectionalTransience.shared_finite_past_cross_bound_oai
