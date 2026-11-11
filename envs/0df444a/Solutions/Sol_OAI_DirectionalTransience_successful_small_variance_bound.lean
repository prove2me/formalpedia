-- Prove2me | solution 1 for OAI.DirectionalTransience.successful_small_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:03:30.997001+00:00
-- url     : https://prove2.me/submissions/b4fd26c5-2fce-4a17-bf0a-f7c1db511d53

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Definitions.Def_OAIQ242Bal006
import Theorems.Thm_OAI_DirectionalTransience_successfulMedian_scaled_tail_comparison

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordDepartures
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FirstWordEvent
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma conditionedLaw_absolutelyContinuous {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) :
    conditionedLaw ν ℓ ≪ annealedLaw ν :=
  (Measure.AbsolutelyContinuous.smul_left (Measure.absolutelyContinuous_restrict) _)

lemma conditionedLaw_noDrop {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ NoDrop ℓ 0 := by
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_noDrop ℓ 0)) _

lemma conditionedLaw_inter_noDrop {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    conditionedLaw ν ℓ (A ∩ NoDrop ℓ 0) = conditionedLaw ν ℓ A := by
  simp only [conditionedLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA, Measure.restrict_apply (hA.inter (measurableSet_noDrop ℓ 0)),
    Set.inter_self, Set.inter_assoc]

lemma measure_preimage_partition {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] (μ : Measure α) (f : α → β)
    (hf : Measurable f) (B : Set β) (hB : MeasurableSet B) (C : Set α) :
    μ (f ⁻¹' B ∩ C) = ∑' b : B, μ (f ⁻¹' {b.1} ∩ C) := by
  have h := tsum_measure_preimage_singleton (μ := μ.restrict C) (s := B)
    (Set.to_countable B) (f := f) (fun b _ => hf (measurableSet_singleton b))
  simpa only [Measure.restrict_apply (hf hB),
    Measure.restrict_apply (hf (measurableSet_singleton _))] using h.symm

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

lemma identDistrib_iterated_symbol {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (F : α → β) (T : α → α)
    (hF : Measurable F) (hT : MeasurePreserving T μ μ) (n : ℕ) :
    IdentDistrib (fun x => F (T^[n] x)) F μ μ := by
  refine ⟨(hF.comp (hT.iterate n).measurable).aemeasurable, hF.aemeasurable, ?_⟩
  change μ.map (F ∘ T^[n]) = μ.map F
  rw [← Measure.map_map hF (hT.iterate n).measurable, (hT.iterate n).map_eq]

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_Regeneration
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma ae_of_frestrict_probability_lower {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α]
    (μ : Measure (ℕ → α)) [IsFiniteMeasure μ] (E : Set (ℕ → α))
    (hE : MeasurableSet E) (p : ℝ≥0∞) (hp : 0 < p) (hpt : p ≠ ∞)
    (h : ∀ (n : ℕ) (f : (i : Finset.Iic n) → α),
      p * μ (Preorder.frestrictLe n ⁻¹' {f}) ≤
        μ (E ∩ (Preorder.frestrictLe n ⁻¹' {f}))) : ∀ᵐ X ∂μ, X ∈ E := by
  classical
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → α)) := Filtration.piLE
  have hsup : (⨆ n, ℱ n) = (inferInstance : MeasurableSpace (ℕ → α)) := by
    apply le_antisymm (iSup_le ℱ.le)
    change (⨆ n : ℕ, MeasurableSpace.comap (fun X : ℕ → α => X n) inferInstance) ≤ _
    apply iSup_le
    intro n
    apply le_trans _ (le_iSup _ n)
    change MeasurableSpace.comap (fun X : ℕ → α => X n) inferInstance ≤ Filtration.piLE n
    rw [Filtration.piLE_eq_comap_frestrictLe]
    have hm : @Measurable (ℕ → α) α
        (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance) _ (fun X => X n) :=
      (show Measurable (fun f : (i : Finset.Iic n) → α => f ⟨n, Finset.mem_Iic.mpr le_rfl⟩) from
        measurable_pi_apply _).comp (Measurable.of_comap_le le_rfl)
    exact hm.comap_le
  have hlow (n : ℕ) (S : Set (ℕ → α)) (hS : MeasurableSet[ℱ n] S) :
      p * μ S ≤ μ (E ∩ S) := by
    change MeasurableSet[Filtration.piLE n] S at hS
    rw [Filtration.piLE_eq_comap_frestrictLe] at hS
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hS
    have hsum (A : Set (ℕ → α)) :
        (μ.restrict A) (Preorder.frestrictLe n ⁻¹' B) =
          ∑' f : B, (μ.restrict A) (Preorder.frestrictLe n ⁻¹' {f.1}) :=
      (tsum_measure_preimage_singleton (μ := μ.restrict A) B.to_countable
        (fun f _ => (Preorder.measurable_frestrictLe n) (measurableSet_singleton f))).symm
    have hpre : MeasurableSet (Preorder.frestrictLe n ⁻¹' B) :=
      (Preorder.measurable_frestrictLe (X := fun _ : ℕ => α) n) hB
    have hp0 := hsum Set.univ
    simp only [Measure.restrict_univ] at hp0
    rw [hp0, ← ENNReal.tsum_mul_left]
    have hpE := hsum E
    rw [Measure.restrict_apply hpre, Set.inter_comm] at hpE
    rw [hpE]
    apply ENNReal.tsum_le_tsum
    intro f
    rw [Measure.restrict_apply ((Preorder.measurable_frestrictLe n)
      (measurableSet_singleton f.1)), Set.inter_comm]
    exact h n f.1
  let g : (ℕ → α) → ℝ := E.indicator (fun _ => 1)
  have hg : Integrable g μ := (integrable_const (1 : ℝ)).indicator hE
  have hlo (n : ℕ) : ∀ᵐ X ∂μ, p.toReal ≤ μ[g | ℱ n] X := by
    apply ae_of_ae_trim (ℱ.le n)
    apply ae_le_of_forall_setIntegral_le (integrable_const p.toReal)
      (integrable_condExp.trim (ℱ.le n) stronglyMeasurable_condExp)
    intro S hS _
    rw [← setIntegral_trim (ℱ.le n) stronglyMeasurable_const hS,
      ← setIntegral_trim (ℱ.le n) stronglyMeasurable_condExp hS,
      setIntegral_condExp (ℱ.le n) hg hS]
    have hreal := ENNReal.toReal_mono (measure_ne_top μ _) (hlow n S hS)
    rw [ENNReal.toReal_mul] at hreal
    simpa only [g, setIntegral_indicator hE, setIntegral_const, smul_eq_mul,
      mul_one, one_mul, Measure.real, Set.inter_comm E S, mul_comm] using hreal
  have hgmeas : StronglyMeasurable[⨆ n, ℱ n] g := by
    rw [hsup]
    exact stronglyMeasurable_const.indicator hE
  have hlim := hg.tendsto_ae_condExp (ℱ := ℱ) hgmeas
  filter_upwards [ae_all_iff.mpr hlo, hlim] with X hX hlimX
  have hge : p.toReal ≤ g X := ge_of_tendsto hlimX (Eventually.of_forall hX)
  by_contra hnot
  rw [show g X = 0 from Set.indicator_of_notMem hnot _] at hge
  exact (not_le_of_gt (ENNReal.toReal_pos hp.ne' hpt)) hge

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma ae_of_pair_prefix_probability_lower {d : ℕ} (μ : Measure (Path d × Path d))
    [IsFiniteMeasure μ] (E : Set (Path d × Path d)) (hE : MeasurableSet E)
    (p : ℝ≥0∞) (hp : 0 < p) (hpt : p ≠ ∞)
    (h : ∀ (n : ℕ) (f g : Path d),
      p * μ (pathCylinder f n ×ˢ pathCylinder g n) ≤
        μ (E ∩ (pathCylinder f n ×ˢ pathCylinder g n))) : ∀ᵐ P ∂μ, P ∈ E := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Lattice d) (Lattice d) ℕ
  let η := μ.map e.symm
  have he : MeasurableSet (e ⁻¹' E) := hE.preimage e.measurable
  have hh := ae_of_frestrict_probability_lower η (e ⁻¹' E) he p hp hpt
  have hf (n : ℕ) (F : (i : Finset.Iic n) → (Lattice d × Lattice d)) :
      e.symm ⁻¹' (Preorder.frestrictLe n ⁻¹' {F}) =
        pathCylinder (extendPrefix n (fun j => (F j).1)) n ×ˢ
        pathCylinder (extendPrefix n (fun j => (F j).2)) n := by
    ext P
    change (Preorder.frestrictLe n (e.symm P) = F) ↔ _
    constructor
    · intro hF
      constructor <;> intro j hj
      · have hv := congrArg (fun G => (G ⟨j, Finset.mem_Iic.mpr hj⟩).1) hF
        simpa [e, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
          Preorder.frestrictLe, extendPrefix_apply n _ j hj] using hv
      · have hv := congrArg (fun G => (G ⟨j, Finset.mem_Iic.mpr hj⟩).2) hF
        simpa [e, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
          Preorder.frestrictLe, extendPrefix_apply n _ j hj] using hv
    · rintro ⟨h1,h2⟩
      funext j
      apply Prod.ext
      · simpa [e, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
          Preorder.frestrictLe, extendPrefix_apply _ _ _ (Finset.mem_Iic.mp j.2)] using h1 j (Finset.mem_Iic.mp j.2)
      · simpa [e, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
          Preorder.frestrictLe, extendPrefix_apply _ _ _ (Finset.mem_Iic.mp j.2)] using h2 j (Finset.mem_Iic.mp j.2)
  have hη : ∀ᵐ Z ∂η, Z ∈ e ⁻¹' E := hh (fun n F => by
    rw [Measure.map_apply e.symm.measurable ((Preorder.measurable_frestrictLe n)
        (measurableSet_singleton F)),
      Measure.map_apply e.symm.measurable (he.inter ((Preorder.measurable_frestrictLe n)
        (measurableSet_singleton F))), Set.preimage_inter, hf]
    simpa only [Set.preimage_preimage, e.apply_symm_apply, Set.preimage_id'] using h n
      (extendPrefix n (fun j => (F j).1)) (extendPrefix n (fun j => (F j).2)))
  change ∀ᵐ Z ∂μ.map e.symm, Z ∈ e ⁻¹' E at hη
  have hμ := (ae_map_iff e.symm.measurable.aemeasurable he).mp hη
  simpa only [Set.mem_preimage, e.apply_symm_apply] using hμ

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

lemma firstLayerHit_after_prefix {d : ℕ} (h : Lattice d → ℤ) (H : ℤ)
    (X : Path d) (N : ℕ) (hp : ∀ j ≤ N, h (X j) < H)
    {n : ℕ} (hn : X ∈ FirstLayerHit h H n) : N < n := by
  by_contra hh
  have hl := hp n (by omega)
  rw [hn.1] at hl
  exact (lt_irrefl _) hl

lemma measurableSet_commonTrueAbove {d : ℕ} (ℓ : Vector d) (K : ℤ) :
    MeasurableSet (CommonTrueAbove ℓ K) := by
  simp only [CommonTrueAbove,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro m
  exact (measurableSet_lt measurable_const ((measurable_of_countable (fun z : Lattice d => dot (realPosition z) ℓ)).comp
    ((measurable_pi_apply n).comp measurable_fst))).inter
      (measurableSet_commonTrueRecord ℓ n m)

lemma finite_pair_prefix_height_bound {d : ℕ} (height : Lattice d → ℤ)
    (f g : Path d) (N : ℕ) (K : ℤ) (x y : Lattice d) :
    ∃ H : ℤ, K < H ∧ height x < H ∧ height y < H ∧
      ∀ j ≤ N, height (f j) < H ∧ height (g j) < H := by
  induction N with
  | zero =>
    let H := max K (max (height x) (max (height y) (max (height (f 0)) (height (g 0)))))+1
    refine ⟨H,?_,?_,?_,?_⟩
    · dsimp [H]; omega
    · dsimp [H]; omega
    · dsimp [H]; omega
    · intro j hj
      have : j = 0 := by omega
      subst j
      dsimp [H]; omega
  | succ N ih =>
    obtain ⟨B,hK,hx,hy,hB⟩ := ih
    let H := max B (max (height (f (N+1))) (height (g (N+1))))+1
    have hBH : B < H := by dsimp [H]; omega
    refine ⟨H,hK.trans hBH,hx.trans hBH,hy.trans hBH,?_⟩
    intro j hj
    by_cases hjN : j ≤ N
    · exact ⟨(hB j hjN).1.trans hBH,(hB j hjN).2.trans hBH⟩
    · have : j = N+1 := by omega
      subst j
      dsimp [H]; omega

lemma pairPrefixDetermined_inter {d : ℕ} {n m : ℕ} {A B : Set (Path d × Path d)}
    (hA : PairPrefixDetermined n m A) (hB : PairPrefixDetermined n m B) :
    PairPrefixDetermined n m (A ∩ B) := by
  intro P Q hf hg
  exact and_congr (hA P Q hf hg) (hB P Q hf hg)

lemma pairPrefixDetermined_product {d : ℕ} {n m : ℕ} {A B : Set (Path d)}
    (hA : PrefixDetermined n A) (hB : PrefixDetermined m B) :
    PairPrefixDetermined n m (A ×ˢ B) := by
  intro P Q hf hg
  exact and_congr (hA P.1 Q.1 hf) (hB P.2 Q.2 hg)

lemma prefixDetermined_cylinder_of_le {d : ℕ} (f : Path d) {N n : ℕ} (hN : N ≤ n) :
    PrefixDetermined n (pathCylinder f N) := by
  intro X Y hXY
  constructor
  · intro hX j hj
    exact (hXY j (hj.trans hN)).symm.trans (hX j hj)
  · intro hY j hj
    exact (hXY j (hj.trans hN)).trans (hY j hj)

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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma pair_record_event_noDrop_lower {d : ℕ} (μ : Measure (Path d × Path d))
    (ℓ : Vector d) (c : ℝ≥0∞)
    (hfresh : ∀ (f g : Path d) (n m : ℕ), 0 < n → 0 < m →
      StrictRecord ℓ f n → StrictRecord ℓ g m →
      dot (realPosition (f n)) ℓ = dot (realPosition (g m)) ℓ →
      c * μ (pathCylinder f n ×ˢ pathCylinder g m) ≤ μ
        (((fun X : Path d => fun j => X (n+j)) ⁻¹' NoDrop ℓ (f n) ∩ pathCylinder f n) ×ˢ
         ((fun X : Path d => fun j => X (m+j)) ⁻¹' NoDrop ℓ (g m) ∩ pathCylinder g m)))
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (A : Set (Path d × Path d))
    (hA : PairPrefixDetermined n m A)
    (hr : ∀ P ∈ A, StrictRecord ℓ P.1 n ∧ StrictRecord ℓ P.2 m ∧
      dot (realPosition (P.1 n)) ℓ = dot (realPosition (P.2 m)) ℓ) :
    c * μ A ≤
      μ (A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m)) := by
  classical
  rw [measure_partition_pairprefix (μ) A n m,
    measure_partition_pairprefix (μ) (A ∩ _) n m,
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
    change c * μ (A ∩ C) ≤ μ ((A ∩ _) ∩ C)
    rw [hAc,he]
    exact hfresh P.1 P.2 n m hn hm (hr P hP).1 (hr P hP).2.1 (hr P hP).2.2
  · have hAc : A ∩ C = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro Q ⟨hQ,hqc1,hqc2⟩
      exact hP ((hA Q P hqc1 hqc2).mp hQ)
    change c * μ (A ∩ C) ≤ _
    rw [hAc,measure_empty,mul_zero]
    exact zero_le

lemma pair_common_true_after_prefix {d : ℕ} (μ : Measure (Path d × Path d))
    (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ)) (x y : Lattice d)
    (hhits : ∀ H : ℤ, height x < H → height y < H → ∀ᵐ P ∂μ,
      (∃ n, P.1 ∈ FirstLayerHit height H n) ∧ (∃ m, P.2 ∈ FirstLayerHit height H m))
    (c : ℝ≥0∞)
    (hfresh : ∀ (n m : ℕ), 0 < n → 0 < m → ∀ (A : Set (Path d × Path d)),
      PairPrefixDetermined n m A →
      (∀ P ∈ A, StrictRecord ℓ P.1 n ∧ StrictRecord ℓ P.2 m ∧
        dot (realPosition (P.1 n)) ℓ = dot (realPosition (P.2 m)) ℓ) →
      c * μ A ≤ μ (A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m)))
    (K : ℤ) (N : ℕ) (f g : Path d) :
    c * μ (pathCylinder f N ×ˢ pathCylinder g N) ≤
      μ (CommonTrueAbove ℓ K ∩ (pathCylinder f N ×ˢ pathCylinder g N)) := by
  classical
  let C := pathCylinder f N ×ˢ pathCylinder g N
  obtain ⟨H,hKH,hx,hy,hH⟩ := finite_pair_prefix_height_bound height f g N K x y
  let A (q : ℕ × ℕ) := C ∩ (FirstLayerHit height H q.1 ×ˢ FirstLayerHit height H q.2)
  let B (q : ℕ × ℕ) := A q ∩ (FutureNoDrop ℓ q.1 ×ˢ FutureNoDrop ℓ q.2)
  have hdisA : Pairwise (fun q r => Disjoint (A q) (A r)) := fun q r hqr =>
    (firstLayerHit_pair_disjoint height H hqr).mono Set.inter_subset_right Set.inter_subset_right
  have hdisB : Pairwise (fun q r => Disjoint (B q) (B r)) := fun q r hqr =>
    (hdisA hqr).mono Set.inter_subset_left Set.inter_subset_left
  have hmA (q : ℕ × ℕ) : MeasurableSet (A q) :=
    ((measurableSet_pathCylinder f N).prod (measurableSet_pathCylinder g N)).inter
      ((measurableSet_firstLayerHit height H q.1).prod (measurableSet_firstLayerHit height H q.2))
  have hmB (q : ℕ × ℕ) : MeasurableSet (B q) := (hmA q).inter
    ((measurableSet_futureNoDrop ℓ q.1).prod (measurableSet_futureNoDrop ℓ q.2))
  have hcover : μ C = ∑' q, μ (A q) := by
    rw [← measure_iUnion hdisA hmA]
    apply measure_congr
    filter_upwards [hhits H hx hy] with P hP
    apply propext
    change P ∈ C ↔ P ∈ ⋃ q, A q
    simp only [Set.mem_iUnion]
    constructor
    · intro hC
      obtain ⟨n,hn⟩ := hP.1
      obtain ⟨m,hm⟩ := hP.2
      exact ⟨(n,m),hC,hn,hm⟩
    · rintro ⟨q,hq⟩
      exact hq.1
  have hindices (q : ℕ × ℕ) (P : Path d × Path d) (hP : P ∈ A q) :
      N < q.1 ∧ N < q.2 := by
    constructor
    · apply firstLayerHit_after_prefix height H P.1 N _ hP.2.1
      intro j hj
      rw [hP.1.1 j hj]
      exact (hH j hj).1
    · apply firstLayerHit_after_prefix height H P.2 N _ hP.2.2
      intro j hj
      rw [hP.1.2 j hj]
      exact (hH j hj).2
  have hlower (q : ℕ × ℕ) : c * μ (A q) ≤ μ (B q) := by
    by_cases hne : (A q).Nonempty
    · obtain ⟨P,hP⟩ := hne
      have hi := hindices q P hP
      apply hfresh q.1 q.2
        (lt_of_le_of_lt (Nat.zero_le _) hi.1) (lt_of_le_of_lt (Nat.zero_le _) hi.2)
      · exact pairPrefixDetermined_inter
          (pairPrefixDetermined_product (prefixDetermined_cylinder_of_le f hi.1.le)
            (prefixDetermined_cylinder_of_le g hi.2.le))
          (pairPrefixDetermined_product (firstLayerHit_prefix height H q.1) (firstLayerHit_prefix height H q.2))
      · intro Q hQ
        refine ⟨firstLayerHit_record ℓ height hproj H q.1 Q.1 hQ.2.1,
          firstLayerHit_record ℓ height hproj H q.2 Q.2 hQ.2.2,?_⟩
        rw [hproj,hproj,hQ.2.1.1,hQ.2.2.1]
    · have hz : A q = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [hz,measure_empty,mul_zero]
      exact zero_le
  have hsub : (⋃ q, B q) ⊆ CommonTrueAbove ℓ K ∩ C := by
    intro P hP
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hP
    refine ⟨⟨q.1,q.2,?_,?_⟩,hq.1.1⟩
    · rw [hproj,hq.1.2.1.1]
      exact_mod_cast hKH
    · refine ⟨?_,?_,?_⟩
      · exact ⟨firstLayerHit_record ℓ height hproj H q.1 P.1 hq.1.2.1,hq.2.1⟩
      · exact ⟨firstLayerHit_record ℓ height hproj H q.2 P.2 hq.1.2.2,hq.2.2⟩
      · rw [hproj,hproj,hq.1.2.1.1,hq.1.2.2.1]
  calc
    c * μ C = ∑' q, c * μ (A q) := by rw [hcover,ENNReal.tsum_mul_left]
    _ ≤ ∑' q, μ (B q) := ENNReal.tsum_le_tsum hlower
    _ = μ (⋃ q, B q) := (measure_iUnion hdisB hmB).symm
    _ ≤ μ (CommonTrueAbove ℓ K ∩ C) := measure_mono hsub

lemma independent_pair_record_cylinder_noDrop {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (f g : Path d) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hrf : StrictRecord ℓ f n) (hrg : StrictRecord ℓ g m) :
    independentPairLaw ν
      (((fun X : Path d => fun j => X (n+j)) ⁻¹' NoDrop ℓ (f n) ∩ pathCylinder f n) ×ˢ
       ((fun X : Path d => fun j => X (m+j)) ⁻¹' NoDrop ℓ (g m) ∩ pathCylinder g m)) =
      (annealedLaw ν (NoDrop ℓ 0))^2 *
        independentPairLaw ν (pathCylinder f n ×ˢ pathCylinder g m) := by
  rw [independentPairLaw,Measure.prod_prod,Measure.prod_prod,
    annealed_record_cylinder_noDrop ν ℓ f n hn hrf,
    annealed_record_cylinder_noDrop ν ℓ g m hm hrg,pow_two]
  ac_rfl

lemma independent_pair_layer_hits {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (H : ℤ) (hH : height 0 < H) :
    ∀ᵐ P ∂independentPairLaw ν,
      (∃ n, P.1 ∈ FirstLayerHit height H n) ∧ (∃ m, P.2 ∈ FirstLayerHit height H m) := by
  have ha : ∀ᵐ X ∂annealedLaw ν, ∃ n, X ∈ FirstLayerHit height H n := by
    filter_upwards [htrans,annealed_initial ν,annealed_nearest_neighbor ν] with X ht h0 hn
    apply firstLayerHit_exists height hstep X hn
    · simpa only [hproj] using ht
    · simpa only [h0] using hH
  exact (Measure.quasiMeasurePreserving_fst.ae ha).and
    (Measure.quasiMeasurePreserving_snd.ae ha)

lemma independent_pair_common_true_unbounded {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentPairLaw ν, ∀ K : ℤ, P ∈ CommonTrueAbove ℓ K := by
  rw [ae_all_iff]
  intro K
  let p := annealedLaw ν (NoDrop ℓ 0)
  have hp : 0 < p := noDrop_positive_of_directionallyTransient ν ℓ htrans
  have hpt : p^2 ≠ ∞ := ENNReal.pow_ne_top (measure_ne_top _ _)
  apply ae_of_pair_prefix_probability_lower _ _ (measurableSet_commonTrueAbove ℓ K)
    (p^2) (ENNReal.pow_pos hp _) hpt
  apply pair_common_true_after_prefix (independentPairLaw ν) ℓ height hproj 0 0
    (fun H hx _ => independent_pair_layer_hits ν ℓ htrans height hproj hstep H hx) (p^2)
  intro n m hn hm A hA hr
  apply pair_record_event_noDrop_lower (independentPairLaw ν) ℓ (p^2) _ n m hn hm A hA hr
  intro f g n m hn hm hrf hrg _
  exact le_of_eq (independent_pair_record_cylinder_noDrop ν ℓ f g n m hn hm hrf hrg).symm

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

lemma firstCommonTrueRecord_exists {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h : ∃ n m, 0 < n ∧ 0 < m ∧ CommonTrueRecord ℓ P n m) :
    ∃ n m, FirstCommonTrueRecord ℓ P n m := by
  classical
  obtain ⟨m,hn,hm,hr⟩ := Nat.find_spec h
  exact ⟨Nat.find h,m,hn,hm,hr,fun j k hj hjn hk _ hc =>
    Nat.find_min h hjn ⟨k,hj,hk,hc⟩⟩

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

lemma firstPairWordEvent_admissible {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d)) (P : Path d × Path d)
    (hP : P ∈ FirstPairWordEvent ℓ wv) : AdmissibleCommonWords ℓ 0 0 wv.1 wv.2 :=
  ((firstCommonWords_characterization ℓ 0 0 wv.1 wv.2 P hP.2.1.1 hP.2.1.2).mp
    ⟨hP.1.1,hP.1.2,hP.2.2⟩).1

lemma independent_conditioned_firstPairWord_exists {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∃ wv, P ∈ FirstPairWordEvent ℓ wv := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  have hac : independentConditionedPairLaw ν ℓ ≪ independentPairLaw ν :=
    (conditionedLaw_absolutelyContinuous ν ℓ).prod (conditionedLaw_absolutelyContinuous ν ℓ)
  have hD := (Measure.quasiMeasurePreserving_fst.ae (conditionedLaw_noDrop ν ℓ)).and
    (Measure.quasiMeasurePreserving_snd.ae (conditionedLaw_noDrop ν ℓ))
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (annealed_initial ν)).and
    (Measure.quasiMeasurePreserving_snd.ae (annealed_initial ν))
  have hNN := (Measure.quasiMeasurePreserving_fst.ae (annealed_nearest_neighbor ν)).and
    (Measure.quasiMeasurePreserving_snd.ae (annealed_nearest_neighbor ν))
  filter_upwards [hac.ae_le (independent_pair_common_true_unbounded ν ℓ htrans height hproj hstep),
    hD,hac.ae_le h0,hac.ae_le hNN] with P hcommon hD h0 hNN
  obtain ⟨n,m,hh,hr⟩ := hcommon (height 0)
  have hn : 0 < n := by
    by_contra hn
    have hz : n = 0 := by omega
    rw [hz,h0.1,hproj] at hh
    exact (lt_irrefl _ hh)
  have hm : 0 < m := by
    by_contra hm
    have hz : m = 0 := by omega
    rw [hr.2.2,hz,h0.2,hproj] at hh
    exact (lt_irrefl _ hh)
  obtain ⟨j,k,hfirst⟩ := firstCommonTrueRecord_exists ℓ P ⟨n,m,hn,hm,hr⟩
  obtain ⟨w,hw,hcw⟩ := exists_word_prefix P.1 hNN.1 j
  obtain ⟨v,hv,hcv⟩ := exists_word_prefix P.2 hNN.2 k
  refine ⟨(w,v),hD,⟨?_,?_⟩,?_⟩
  · simpa only [h0.1] using hcw
  · simpa only [h0.2] using hcv
  · change FirstCommonTrueRecord ℓ P w.length v.length
    simpa only [hw,hv] using hfirst

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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma measurable_fixedPairSuffix {d : ℕ} (wv : List (Direction d) × List (Direction d)) :
    Measurable (fixedPairSuffix wv) := by unfold fixedPairSuffix; fun_prop

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

lemma independent_conditioned_pair_word_factor {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (wv : List (Direction d) × List (Direction d))
    (A : Set (Path d × Path d)) (hA : MeasurableSet A) :
    independentConditionedPairLaw ν ℓ (FirstPairWordEvent ℓ wv ∩ fixedPairSuffix wv ⁻¹' A) =
      independentConditionedPairLaw ν ℓ (FirstPairWordEvent ℓ wv) *
        independentConditionedPairLaw ν ℓ A := by
  classical
  let μ := independentConditionedPairLaw ν ℓ
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ hp
  by_cases had : AdmissibleCommonWords ℓ 0 0 wv.1 wv.2
  · have he : (μ.restrict (FirstPairWordEvent ℓ wv)).map (fixedPairSuffix wv) =
        μ (FirstPairWordEvent ℓ wv) • μ := by
      apply Measure.ext_prod
      intro B C hB hC
      rw [Measure.map_apply (measurable_fixedPairSuffix wv) (hB.prod hC),
        Measure.restrict_apply ((hB.prod hC).preimage (measurable_fixedPairSuffix wv)),
        Set.inter_comm,Measure.smul_apply,smul_eq_mul]
      exact (independent_conditioned_pair_word_rectangle ν ℓ hp wv had B C hB hC).trans
        (by rw [independent_conditioned_pair_word_mass ν ℓ hp wv had])
    have h := congrArg (fun ρ : Measure (Path d × Path d) => ρ A) he
    rw [Measure.map_apply (measurable_fixedPairSuffix wv) hA,
      Measure.restrict_apply (hA.preimage (measurable_fixedPairSuffix wv)),
      Set.inter_comm,Measure.smul_apply,smul_eq_mul] at h
    exact h
  · have he : FirstPairWordEvent ℓ wv = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      exact fun P hP => had (firstPairWordEvent_admissible ℓ wv P hP)
    simp only [he,Set.empty_inter,measure_empty,zero_mul]

lemma renewPairSuffix_on_firstPairWordEvent {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d)) (P : Path d × Path d)
    (hP : P ∈ FirstPairWordEvent ℓ wv) : renewPairSuffix ℓ P = fixedPairSuffix wv P := by
  have hwv : wv ≠ ([],[]) := by
    intro he
    rw [he,firstPairWordEvent_nil] at hP
    exact hP
  unfold renewPairSuffix fixedPairSuffix
  rw [(firstPairWord_eq_iff ℓ P wv hwv).mpr hP,
    hP.2.1.1 wv.1.length le_rfl,hP.2.1.2 wv.2.length le_rfl]

lemma independent_conditioned_firstPairWord_fiber_ae {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (wv : List (Direction d) × List (Direction d)) :
    firstPairWord ℓ ⁻¹' {wv} =ᵐ[independentConditionedPairLaw ν ℓ] FirstPairWordEvent ℓ wv := by
  classical
  by_cases hwv : wv = ([],[])
  · subst wv
    filter_upwards [independent_conditioned_firstPairWord_exists ν ℓ htrans height hproj hstep]
      with P hP
    apply propext
    change firstPairWord ℓ P = ([],[]) ↔ P ∈ FirstPairWordEvent ℓ ([],[])
    rw [firstPairWord_nil_iff,firstPairWordEvent_nil]
    simp only [hP,not_true_eq_false,Set.mem_empty_iff_false]
  · exact Filter.Eventually.of_forall fun P => propext (firstPairWord_eq_iff ℓ P wv hwv)

lemma independent_conditioned_firstPairWord_fiber_factor {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (wv : List (Direction d) × List (Direction d))
    (A : Set (Path d × Path d)) (hA : MeasurableSet A) :
    independentConditionedPairLaw ν ℓ (firstPairWord ℓ ⁻¹' {wv} ∩ renewPairSuffix ℓ ⁻¹' A) =
      independentConditionedPairLaw ν ℓ (firstPairWord ℓ ⁻¹' {wv}) *
        independentConditionedPairLaw ν ℓ A := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hcy := independent_conditioned_firstPairWord_fiber_ae ν ℓ htrans height hproj hstep wv
  have hE : (firstPairWord ℓ ⁻¹' {wv} ∩ renewPairSuffix ℓ ⁻¹' A : Set (Path d × Path d))
      =ᵐ[independentConditionedPairLaw ν ℓ]
        (FirstPairWordEvent ℓ wv ∩ renewPairSuffix ℓ ⁻¹' A : Set (Path d × Path d)) :=
    hcy.inter (Filter.Eventually.of_forall fun _ => rfl)
  rw [measure_congr hE,measure_congr hcy]
  have he : FirstPairWordEvent ℓ wv ∩ renewPairSuffix ℓ ⁻¹' A =
      FirstPairWordEvent ℓ wv ∩ fixedPairSuffix wv ⁻¹' A := by
    ext P
    by_cases hP : P ∈ FirstPairWordEvent ℓ wv
    · simp only [Set.mem_inter_iff,Set.mem_preimage,hP,true_and,
        renewPairSuffix_on_firstPairWordEvent ℓ wv P hP]
    · simp only [Set.mem_inter_iff,hP,false_and]
  rw [he]
  exact independent_conditioned_pair_word_factor ν ℓ hp wv A hA

lemma measurePreserving_of_countable_fiber_factor {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ] (F : α → β) (T : α → α)
    (hF : Measurable F) (hT : Measurable T)
    (hfac : ∀ b A, MeasurableSet A → μ (F ⁻¹' {b} ∩ T ⁻¹' A) = μ (F ⁻¹' {b}) * μ A) :
    MeasurePreserving T μ μ := by
  refine ⟨hT,?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hT hA]
  have hpart : ∀ B : Set α, MeasurableSet B → μ B = ∑' b : β, μ (F ⁻¹' {b} ∩ B) := by
    intro B hB
    have he : (⋃ b : β,F ⁻¹' {b} ∩ B) = B := by
      ext x
      simp only [Set.mem_iUnion,Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff]
      exact ⟨fun ⟨_,_,hx⟩ => hx,fun hx => ⟨F x,rfl,hx⟩⟩
    rw [← he]
    conv_rhs => arg 1; ext b; rw [he]
    exact measure_iUnion (fun u v huv => ((Set.disjoint_singleton.mpr huv).preimage F).mono
      Set.inter_subset_left Set.inter_subset_left)
      (fun b => (hF (measurableSet_singleton b)).inter hB)
  have hsum : (∑' b : β,μ (F ⁻¹' {b})) = 1 := by
    simpa only [Set.inter_univ,measure_univ] using (hpart Set.univ MeasurableSet.univ).symm
  rw [hpart (T ⁻¹' A) (hA.preimage hT)]
  simp_rw [hfac _ A hA]
  rw [ENNReal.tsum_mul_right,hsum,one_mul]

lemma indepFun_of_countable_fiber_factor {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ] (F : α → β) (T : α → α)
    (hF : Measurable F) (hT : Measurable T)
    (hfac : ∀ b A, MeasurableSet A → μ (F ⁻¹' {b} ∩ T ⁻¹' A) = μ (F ⁻¹' {b}) * μ A) :
    IndepFun F T μ := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro B A hB hA
  have hm := measurePreserving_of_countable_fiber_factor μ F T hF hT hfac
  rw [hm.measure_preimage hA.nullMeasurableSet,measure_preimage_partition μ F hF B hB]
  simp_rw [hfac _ A hA]
  rw [ENNReal.tsum_mul_right]
  have hsum := measure_preimage_partition μ F hF B hB Set.univ
  simpa only [Set.inter_univ] using congrArg (fun x => x * μ A) hsum.symm

lemma renewPairSuffix_preserves_independent_conditioned {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    MeasurePreserving (renewPairSuffix ℓ)
      (independentConditionedPairLaw ν ℓ) (independentConditionedPairLaw ν ℓ) := by
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  exact measurePreserving_of_countable_fiber_factor _ _ _
    (measurable_firstPairWord ℓ) (measurable_renewPairSuffix ℓ)
    (independent_conditioned_firstPairWord_fiber_factor ν ℓ htrans height hproj hstep)

lemma firstPairWord_indep_renewPairSuffix {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    IndepFun (firstPairWord ℓ) (renewPairSuffix ℓ) (independentConditionedPairLaw ν ℓ) := by
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  exact indepFun_of_countable_fiber_factor _ _ _
    (measurable_firstPairWord ℓ) (measurable_renewPairSuffix ℓ)
    (independent_conditioned_firstPairWord_fiber_factor ν ℓ htrans height hproj hstep)

lemma common_words_independent {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    iIndepFun (fun n : ℕ => fun P => firstPairWord ℓ ((renewPairSuffix ℓ)^[n] P))
      (independentConditionedPairLaw ν ℓ) := by
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  exact independent_iterated_symbols _ _ _ (measurable_firstPairWord ℓ)
    (renewPairSuffix_preserves_independent_conditioned ν ℓ htrans height hproj hstep)
    (firstPairWord_indep_renewPairSuffix ν ℓ htrans height hproj hstep)

lemma common_words_identDistrib {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (n : ℕ) :
    IdentDistrib (fun P => firstPairWord ℓ ((renewPairSuffix ℓ)^[n] P)) (firstPairWord ℓ)
      (independentConditionedPairLaw ν ℓ) (independentConditionedPairLaw ν ℓ) := by
  exact identDistrib_iterated_symbol _ _ _ (measurable_firstPairWord ℓ)
    (renewPairSuffix_preserves_independent_conditioned ν ℓ htrans height hproj hstep) n

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordIncrement
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma commonTrueRecord_swap {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) (n m : ℕ) :
    CommonTrueRecord ℓ P n m ↔ CommonTrueRecord ℓ P.swap m n := by
  constructor <;> rintro ⟨h1,h2,he⟩ <;> exact ⟨h2,h1,he.symm⟩

lemma firstCommonTrueRecord_swap {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) (n m : ℕ) :
    FirstCommonTrueRecord ℓ P n m ↔ FirstCommonTrueRecord ℓ P.swap m n := by
  constructor
  · rintro ⟨hn,hm,hc,hmin⟩
    refine ⟨hm,hn,(commonTrueRecord_swap ℓ P n m).mp hc,?_⟩
    intro j k hj hjm hk hkn hc'
    exact hmin k j hk hkn hj hjm ((commonTrueRecord_swap ℓ P k j).mpr hc')
  · rintro ⟨hm,hn,hc,hmin⟩
    refine ⟨hn,hm,(commonTrueRecord_swap ℓ P n m).mpr hc,?_⟩
    intro j k hj hjn hk hkm hc'
    exact hmin k j hk hkm hj hjn ((commonTrueRecord_swap ℓ P j k).mp hc')

lemma firstPairWordEvent_swap {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (wv : List (Direction d) × List (Direction d)) :
    P ∈ FirstPairWordEvent ℓ wv ↔ P.swap ∈ FirstPairWordEvent ℓ wv.swap := by
  constructor
  · rintro ⟨⟨hD1,hD2⟩,⟨hw,hv⟩,hc⟩
    exact ⟨⟨hD2,hD1⟩,⟨hv,hw⟩,(firstCommonTrueRecord_swap ℓ P _ _).mp hc⟩
  · rintro ⟨⟨hD2,hD1⟩,⟨hv,hw⟩,hc⟩
    exact ⟨⟨hD1,hD2⟩,⟨hw,hv⟩,(firstCommonTrueRecord_swap ℓ P _ _).mpr hc⟩

lemma firstPairWord_swap {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) :
    firstPairWord ℓ P.swap = (firstPairWord ℓ P).swap := by
  classical
  by_cases h : ∃ wv, P ∈ FirstPairWordEvent ℓ wv
  · have hP : P ∈ FirstPairWordEvent ℓ (firstPairWord ℓ P) := by
      simpa only [firstPairWord,dite_eq_left h] using h.choose_spec
    have hw : (firstPairWord ℓ P).swap ≠ ([],[]) := by
      intro he
      have hlen := congrArg (fun p : List (Direction d) × List (Direction d) => p.2.length) he
      exact Nat.ne_of_gt hP.2.2.1 hlen
    exact (firstPairWord_eq_iff ℓ P.swap _ hw).mpr ((firstPairWordEvent_swap ℓ P _).mp hP)
  · have h' : ¬ ∃ wv, P.swap ∈ FirstPairWordEvent ℓ wv := by
      rintro ⟨wv,hwv⟩
      exact h ⟨wv.swap,(firstPairWordEvent_swap ℓ P _).mpr hwv⟩
    rw [show firstPairWord ℓ P.swap = ([],[]) by simp only [firstPairWord,dite_eq_right h'],
      show firstPairWord ℓ P = ([],[]) by simp only [firstPairWord,dite_eq_right h]]
    rfl

lemma independent_commonWordIncrement_symmetric {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (e : Direction d) :
    IdentDistrib (fun P => commonWordIncrement e (firstPairWord ℓ P))
      (fun P => -commonWordIncrement e (firstPairWord ℓ P))
      (independentConditionedPairLaw ν ℓ) (independentConditionedPairLaw ν ℓ) := by
  have hm : Measurable (fun P => commonWordIncrement e (firstPairWord ℓ P)) :=
    (measurable_of_countable (commonWordIncrement e)).comp (measurable_firstPairWord ℓ)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hp : MeasurePreserving Prod.swap (independentConditionedPairLaw ν ℓ)
      (independentConditionedPairLaw ν ℓ) := Measure.measurePreserving_swap
  have hi : IdentDistrib (fun P => commonWordIncrement e (firstPairWord ℓ P.swap))
      (fun P => commonWordIncrement e (firstPairWord ℓ P))
      (independentConditionedPairLaw ν ℓ) (independentConditionedPairLaw ν ℓ) := by
    refine ⟨(hm.comp measurable_swap).aemeasurable,hm.aemeasurable,?_⟩
    rw [show (fun P => commonWordIncrement e (firstPairWord ℓ P.swap)) =
      (fun P => commonWordIncrement e (firstPairWord ℓ P)) ∘ Prod.swap from rfl,
      ← Measure.map_map hm measurable_swap,hp.map_eq]
  convert hi.symm using 1
  all_goals try with_reducible_and_instances rfl
  ext P
  simp only [firstPairWord_swap,commonWordIncrement,Prod.fst_swap,Prod.snd_swap,neg_sub]

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

lemma truncatedVariance_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (r : ℝ) : 0 ≤ truncatedVariance μ S r :=
  integral_nonneg fun _ => le_min (sq_nonneg _) (sq_nonneg _)

lemma truncatedVariance_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) {r : ℝ} (hr : 0 < r) :
    0 < truncatedVariance μ S r := by
  apply (integral_pos_iff_support_of_nonneg (fun x => le_min (sq_nonneg _) (sq_nonneg _))
    (integrable_truncated_square μ S hS r)).mpr
  apply hne.trans_le (measure_mono _)
  intro x hx
  exact ne_of_gt (lt_min (sq_pos_of_ne_zero hx) (sq_pos_of_pos hr))

lemma realPartialSum_succ (X : ℕ → ℝ) (n : ℕ) :
    realPartialSum X (n+1) = realPartialSum X n+X n := by simp [realPartialSum,Finset.sum_range_succ]

lemma partialSumMax_nonneg (X : ℕ → ℝ) (n : ℕ) : 0 ≤ partialSumMax X n := by
  induction n with
  | zero => rfl
  | succ n _ => exact (abs_nonneg _).trans (le_max_right _ _)

lemma abs_partialSum_le_max (X : ℕ → ℝ) (n : ℕ) : |realPartialSum X n| ≤ partialSumMax X n := by
  cases n with
  | zero => simp [realPartialSum,partialSumMax]
  | succ n => exact le_max_right _ _

lemma partialSumMax_bound (X : ℕ → ℝ) {z : ℝ} (hz : 0 ≤ z) (hX : ∀ k, |X k| ≤ z) (n : ℕ) :
    partialSumMax X n ≤ n*z := by
  induction n with
  | zero => simp [partialSumMax]
  | succ n ih =>
    apply max_le
    · simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using ih.trans (le_add_of_nonneg_right hz)
    · rw [realPartialSum_succ]
      calc
        |realPartialSum X n+X n| ≤ |realPartialSum X n|+|X n| := abs_add_le _ _
        _ ≤ n*z+z := add_le_add ((abs_partialSum_le_max X n).trans ih) (hX n)
        _ = (n+1:ℕ)*z := by push_cast <;> ring

lemma abs_absSlope (t : ℝ) : |absSlope t| = 1 := by
  unfold absSlope
  split <;> simp

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SymmetricTruncate
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma abs_supporting (t x : ℝ) : absSlope t*x ≤ |t+x|-|t| := by
  by_cases ht : 0 ≤ t
  · rw [absSlope,ite_eq_left ht,one_mul,abs_of_nonneg ht]
    linarith [le_abs_self (t+x)]
  · rw [absSlope,ite_eq_right ht,neg_one_mul,abs_of_neg (lt_of_not_ge ht)]
    linarith [neg_le_abs (t+x)]

lemma max_square_increment {m a : ℝ} : (max m |a|)^2-m^2 ≤ 2*|a| * (max m |a|-m) := by
  by_cases h : |a| ≤ m
  · rw [max_eq_left h]; ring_nf; rfl
  · rw [max_eq_right (le_of_not_ge h)]
    nlinarith [sq_nonneg (|a|-m)]

lemma partialSumMax_pathwise (X : ℕ → ℝ) (n : ℕ) :
    (partialSumMax X n)^2 ≤ 2*partialSumMax X n*|realPartialSum X n|-
      2*∑ k ∈ Finset.range n, partialSumMax X k*absSlope (realPartialSum X k)*X k := by
  induction n with
  | zero => simp [partialSumMax]
  | succ n ih =>
    have hincr := max_square_increment (m := partialSumMax X n) (a := realPartialSum X (n+1))
    have hs := mul_le_mul_of_nonneg_left (abs_supporting (realPartialSum X n) (X n))
      (partialSumMax_nonneg X n)
    rw [← realPartialSum_succ] at hs
    rw [Finset.sum_range_succ]
    change (max (partialSumMax X n) |realPartialSum X (n+1)|)^2 ≤ _
    change _ ≤ 2*max (partialSumMax X n) |realPartialSum X (n+1)| * |realPartialSum X (n+1)|-_
    nlinarith

lemma partialSumMax_square_pathwise (X : ℕ → ℝ) (n : ℕ) :
    (partialSumMax X n)^2 ≤ 4*(realPartialSum X n)^2-
      4*∑ k ∈ Finset.range n, partialSumMax X k*absSlope (realPartialSum X k)*X k := by
  have h := partialSumMax_pathwise X n
  nlinarith [sq_nonneg (partialSumMax X n-2*|realPartialSum X n|),sq_abs (realPartialSum X n)]

lemma measurable_realPartialSum {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (n : ℕ) : Measurable (fun ω => realPartialSum (fun k => X k ω) n) := by
  unfold realPartialSum
  fun_prop

lemma measurable_partialSumMax {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (n : ℕ) : Measurable (fun ω => partialSumMax (fun k => X k ω) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (measurable_realPartialSum X hX (n+1)).abs

lemma measurable_absSlope : Measurable absSlope :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

lemma integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable (Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using hC ω)

lemma realPartialSum_congr {X Y : ℕ → ℝ} (n : ℕ) (hXY : ∀ k < n, X k = Y k) :
    realPartialSum X n = realPartialSum Y n := by
  exact Finset.sum_congr rfl fun k hk => hXY k (Finset.mem_range.mp hk)

lemma partialSumMax_congr {X Y : ℕ → ℝ} (n : ℕ) (hXY : ∀ k < n, X k = Y k) :
    partialSumMax X n = partialSumMax Y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [partialSumMax,partialSumMax,ih (fun k hk => hXY k (hk.trans (Nat.lt_succ_self _))),
      realPartialSum_congr (n+1) hXY]

lemma independent_max_transform {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ) (n : ℕ) :
    IndepFun (fun ω => partialSumMax (fun k => X k ω) n*absSlope (realPartialSum (fun k => X k ω) n))
      (X n) μ := by
  let Y (v : Fin n → ℝ) (k : ℕ) := if h : k < n then v ⟨k,h⟩ else 0
  have hY : ∀ k, Measurable (fun v => Y v k) := by
    intro k
    by_cases h : k < n <;> simp only [Y,h,↓reduceDIte] <;> fun_prop
  have hm : Measurable (fun v => partialSumMax (Y v) n*absSlope (realPartialSum (Y v) n)) :=
    (measurable_partialSumMax (fun k v => Y v k) hY n).mul
      (measurable_absSlope.comp (measurable_realPartialSum (fun k v => Y v k) hY n))
  have hh := (independent_past_current μ X hX hind n).comp hm measurable_id
  convert hh using 1
  · funext ω
    have heq : ∀ k < n, X k ω = Y (fun j : Fin n => X j ω) k := fun k hk => by simp [Y,hk]
    rw [partialSumMax_congr n heq,realPartialSum_congr n heq]
    rfl
  · rfl

lemma integrable_partialSumMax_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    Integrable (fun ω => (partialSumMax (fun k => X k ω) n)^2) μ := by
  apply integrable_of_abs_bound μ _ ((measurable_partialSumMax X hX n).pow_const 2) ((n*z)^2)
  intro ω
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (partialSumMax_nonneg _ _) (partialSumMax_bound _ hz (fun k => hbound k ω) n) 2

lemma integrable_realPartialSum_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    Integrable (fun ω => (realPartialSum (fun k => X k ω) n)^2) μ := by
  apply (integrable_partialSumMax_square μ X hX hz hbound n).mono'
    ((measurable_realPartialSum X hX n).pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have := abs_partialSum_le_max (fun k => X k ω) n
    rw [← sq_abs (realPartialSum (fun k => X k ω) n)]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2

lemma integral_partialSumMax_square_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => X k ω) n)^2 ∂μ) ≤
      4*∫ ω, (realPartialSum (fun k => X k ω) n)^2 ∂μ := by
  let C (k : ℕ) (ω : Ω) := partialSumMax (fun j => X j ω) k*absSlope (realPartialSum (fun j => X j ω) k)
  have hC (k : ℕ) : Measurable (C k) := (measurable_partialSumMax X hX k).mul
    (measurable_absSlope.comp (measurable_realPartialSum X hX k))
  have hCI (k : ℕ) : Integrable (fun ω => C k ω*X k ω) μ := by
    apply integrable_of_abs_bound μ _ ((hC k).mul (hX k)) (k*z*z)
    intro ω
    dsimp [C]
    rw [abs_mul,abs_mul,abs_absSlope,mul_one,abs_of_nonneg (partialSumMax_nonneg _ _)]
    exact mul_le_mul (partialSumMax_bound _ hz (fun j => hbound j ω) k) (hbound k ω)
      (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hz)
  have hzero (k : ℕ) : ∫ ω, C k ω*X k ω ∂μ = 0 := by
    rw [(independent_max_transform μ X hX hind k).integral_fun_mul_eq_mul_integral
      (hC k).aestronglyMeasurable (hX k).aestronglyMeasurable,hmean,mul_zero]
  have hm := integral_mono (integrable_partialSumMax_square μ X hX hz hbound n)
    (((integrable_realPartialSum_square μ X hX hz hbound n).const_mul 4).sub
      ((integrable_finsetSum (Finset.range n) (fun k _ => hCI k)).const_mul 4))
    (fun ω => partialSumMax_square_pathwise (fun k => X k ω) n)
  simp only [Pi.sub_apply] at hm
  rw [integral_sub ((integrable_realPartialSum_square μ X hX hz hbound n).const_mul 4)
    ((integrable_finsetSum (Finset.range n) (fun k _ => hCI k)).const_mul 4),
    integral_const_mul,integral_const_mul,integral_finsetSum _ (fun k _ => hCI k)] at hm
  simpa only [hzero,Finset.sum_const_zero,mul_zero,sub_zero] using hm

lemma integral_partialSum_square_eq_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (realPartialSum (fun k => X k ω) n)^2 ∂μ) =
      ∑ k ∈ Finset.range n, ∫ ω, (X k ω)^2 ∂μ := by
  have hLp (k : ℕ) : MemLp (X k) 2 μ := MemLp.of_bound (hX k).aestronglyMeasurable z
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound k ω)
  have hI (k : ℕ) : Integrable (X k) μ := (hLp k).integrable (by norm_num)
  have hsum : ∫ ω, realPartialSum (fun k => X k ω) n ∂μ = 0 := by
    rw [show (fun ω => realPartialSum (fun k => X k ω) n) =
      (fun ω => ∑ k ∈ Finset.range n, X k ω) from rfl,
      integral_finsetSum _ (fun k _ => hI k)]
    simp only [hmean,Finset.sum_const_zero]
  have hv := IndepFun.variance_sum (s := Finset.range n) (fun k _ => hLp k)
    (fun i _ j _ hij => hind.indepFun hij)
  have heq : (∑ k ∈ Finset.range n, X k) = (fun ω => realPartialSum (fun k => X k ω) n) := by
    ext ω
    simp only [realPartialSum,Finset.sum_apply]
  rw [heq,variance_eq_integral (measurable_realPartialSum X hX n).aemeasurable,hsum] at hv
  simpa only [variance_eq_integral (hX _).aemeasurable,hmean,sub_zero] using hv

lemma integral_partialSumMax_square_le_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => X k ω) n)^2 ∂μ) ≤
      4*∑ k ∈ Finset.range n, ∫ ω, (X k ω)^2 ∂μ := by
  rw [← integral_partialSum_square_eq_sum μ X hX hind hmean hbound n]
  exact integral_partialSumMax_square_le μ X hX hind hmean hz hbound n

lemma measurable_symmetricTruncate (z : ℝ) : Measurable (symmetricTruncate z) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_id measurable_const

lemma measurable_truncatedTailCost (z : ℝ) : Measurable (truncatedTailCost z) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_abs) measurable_const measurable_const

lemma symmetricTruncate_bound {z : ℝ} (hz : 0 ≤ z) (x : ℝ) : |symmetricTruncate z x| ≤ z := by
  unfold symmetricTruncate
  split_ifs with h
  · exact h
  · simpa using hz

lemma symmetricTruncate_neg (z x : ℝ) : symmetricTruncate z (-x) = -symmetricTruncate z x := by
  simp only [symmetricTruncate,abs_neg]
  split_ifs <;> simp

lemma symmetricTruncate_sq_le (z x : ℝ) : (symmetricTruncate z x)^2 ≤ min (x^2) (z^2) := by
  unfold symmetricTruncate
  split_ifs with h
  · exact le_min le_rfl (by nlinarith [abs_nonneg x,sq_abs x])
  · simpa only [zero_pow (by norm_num : 2 ≠ 0)] using le_min (sq_nonneg x) (sq_nonneg z)

lemma truncatedTailCost_nonneg (z x : ℝ) : 0 ≤ truncatedTailCost z x := by
  unfold truncatedTailCost
  split_ifs <;> positivity

lemma truncatedTailCost_le {z : ℝ} (hz : 0 ≤ z) (x : ℝ) :
    truncatedTailCost z x ≤ min (x^2) (z^2) := by
  unfold truncatedTailCost
  split_ifs with h
  · exact le_min (by nlinarith [sq_abs x]) le_rfl
  · exact le_min (sq_nonneg x) (sq_nonneg z)

lemma integral_symmetricTruncate_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (z : ℝ)
    (hsym : IdentDistrib S (fun ω => -S ω) μ μ) :
    (∫ ω, symmetricTruncate z (S ω) ∂μ) = 0 := by
  have he := (hsym.comp (measurable_symmetricTruncate z)).integral_eq
  simp only [Function.comp_apply,symmetricTruncate_neg,integral_neg] at he
  linarith

lemma capped_partialSumMax_le_truncated (X : ℕ → ℝ) (n : ℕ) (z : ℝ) :
    min ((partialSumMax X n)^2) (z^2) ≤
      (partialSumMax (fun k => symmetricTruncate z (X k)) n)^2 +
        ∑ k ∈ Finset.range n, truncatedTailCost z (X k) := by
  classical
  by_cases h : ∀ k < n, |X k| ≤ z
  · have he : partialSumMax X n = partialSumMax (fun k => symmetricTruncate z (X k)) n := by
      apply partialSumMax_congr
      intro k hk
      simp only [symmetricTruncate,ite_eq_left (h k hk)]
    rw [he]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right
      (Finset.sum_nonneg fun k _ => truncatedTailCost_nonneg z (X k)))
  · push Not at h
    obtain ⟨k,hkn,hk⟩ := h
    have hs := Finset.single_le_sum (f := fun k => truncatedTailCost z (X k))
      (fun j _ => truncatedTailCost_nonneg z (X j)) (Finset.mem_range.mpr hkn)
    rw [truncatedTailCost,ite_eq_left hk] at hs
    exact (min_le_right _ _).trans (hs.trans (le_add_of_nonneg_left (sq_nonneg _)))

lemma integral_partialSumMax_capped_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    (∫ ω, min ((partialSumMax (fun k => X k ω) n)^2) (z^2) ∂μ) ≤
      5*(n : ℝ)*truncatedVariance μ (X 0) z := by
  let Y (k : ℕ) (ω : Ω) := symmetricTruncate z (X k ω)
  have hY (k : ℕ) : Measurable (Y k) := (measurable_symmetricTruncate z).comp (hX k)
  have hYb (k : ℕ) (ω : Ω) : |Y k ω| ≤ z := symmetricTruncate_bound hz _
  have hYi : iIndepFun Y μ := hind.comp (fun _ => symmetricTruncate z) (fun _ => measurable_symmetricTruncate z)
  have hYm (k : ℕ) : (∫ ω, Y k ω ∂μ) = 0 := by
    rw [show (∫ ω, Y k ω ∂μ) = ∫ ω, Y 0 ω ∂μ from
      ((hident k).comp (measurable_symmetricTruncate z)).integral_eq]
    exact integral_symmetricTruncate_zero μ (X 0) z hsym
  have htI (k : ℕ) : Integrable (fun ω => truncatedTailCost z (X k ω)) μ := by
    apply (integrable_truncated_square μ (X k) (hX k) z).mono'
      (((measurable_truncatedTailCost z).comp (hX k)).aestronglyMeasurable)
    exact Eventually.of_forall fun ω => by
      simp only [Function.comp_apply]
      rw [Real.norm_of_nonneg (truncatedTailCost_nonneg _ _)]
      exact truncatedTailCost_le hz _
  have hsqI (k : ℕ) : Integrable (fun ω => (Y k ω)^2) μ := by
    apply (integrable_truncated_square μ (X k) (hX k) z).mono'
      ((hY k).pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact symmetricTruncate_sq_le _ _
  have heq (k : ℕ) : truncatedVariance μ (X k) z = truncatedVariance μ (X 0) z :=
    ((hident k).comp ((measurable_id.pow_const 2).min measurable_const)).integral_eq
  have hsq (k : ℕ) : (∫ ω, (Y k ω)^2 ∂μ) ≤ truncatedVariance μ (X 0) z := by
    rw [← heq k]
    exact integral_mono (hsqI k) (integrable_truncated_square μ (X k) (hX k) z)
      (fun ω => symmetricTruncate_sq_le _ _)
  have ht (k : ℕ) : (∫ ω, truncatedTailCost z (X k ω) ∂μ) ≤ truncatedVariance μ (X 0) z := by
    rw [← heq k]
    exact integral_mono (htI k) (integrable_truncated_square μ (X k) (hX k) z)
      (fun ω => truncatedTailCost_le hz _)
  have hm := integral_mono (integrable_truncated_square μ _ (measurable_partialSumMax X hX n) z)
    ((integrable_partialSumMax_square μ Y hY hz hYb n).add
      (integrable_finsetSum (Finset.range n) (fun k _ => htI k)))
    (fun ω => capped_partialSumMax_le_truncated (fun k => X k ω) n z)
  simp only [Pi.add_apply] at hm
  rw [integral_add (integrable_partialSumMax_square μ Y hY hz hYb n)
    (integrable_finsetSum (Finset.range n) (fun k _ => htI k)),
    integral_finsetSum _ (fun k _ => htI k)] at hm
  have hmax := integral_partialSumMax_square_le_sum μ Y hY hYi hYm hz hYb n
  have hsum1 := Finset.sum_le_sum (s := Finset.range n) (fun k _ => hsq k)
  have hsum2 := Finset.sum_le_sum (s := Finset.range n) (fun k _ => ht k)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum1 hsum2
  linarith

lemma measurable_commonIncrementProcess {d : ℕ} (ℓ : Vector d) (e : Direction d) (n : ℕ) :
    Measurable (commonIncrementProcess ℓ e n) :=
  (measurable_of_countable (commonWordIncrement e)).comp
    ((measurable_firstPairWord ℓ).comp ((measurable_renewPairSuffix ℓ).iterate n))

lemma commonIncrements_independent {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d) :
    iIndepFun (commonIncrementProcess ℓ e) (independentConditionedPairLaw ν ℓ) :=
  (common_words_independent ν ℓ htrans height hproj hstep).comp
    (fun _ => commonWordIncrement e) (fun _ => measurable_of_countable _)

lemma commonIncrements_identDistrib {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d) (n : ℕ) :
    IdentDistrib (commonIncrementProcess ℓ e n) (commonIncrementProcess ℓ e 0)
      (independentConditionedPairLaw ν ℓ) (independentConditionedPairLaw ν ℓ) :=
  (common_words_identDistrib ν ℓ htrans height hproj hstep n).comp (measurable_of_countable _)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SuccessfulAverage
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma successfulAverage_apply {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) (H : ℝ)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    successfulAverage ν ℓ H A = ∫⁻ ω, (crossingQuenched ℓ 0 H ω)⁻¹ *
      quenchedKernel (ω,0) (A ∩ Cross ℓ 0 H) ∂environmentLaw ν := by
  rw [successfulAverage,Measure.restrict_apply hA,
    weightedAnnealed_apply ν (fun ω => (crossingQuenched ℓ 0 H ω)⁻¹)
      (show Measurable (fun ω => (crossingQuenched ℓ 0 H ω)⁻¹) from (measurable_crossingQuenched ℓ 0 H).inv) _
      (hA.inter (measurableSet_cross ℓ 0 H))]

lemma successfulAverage_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (H : ℝ) :
    IsProbabilityMeasure (successfulAverage ν ℓ H) := by
  constructor
  rw [successfulAverage_apply ν ℓ H Set.univ MeasurableSet.univ]
  have he : (fun ω => (crossingQuenched ℓ 0 H ω)⁻¹ *
      quenchedKernel (ω,0) (Set.univ ∩ Cross ℓ 0 H)) =ᵐ[environmentLaw ν] fun _ => 1 := by
    filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans,
      quenched_noDrop_subset_cross_ae ν ℓ htrans] with ω hp hsub
    have ha : crossingQuenched ℓ 0 H ω ≠ 0 := ne_of_gt
      ((hp 0).trans_le (measure_mono_ae (hsub 0 H)))
    simp only [Set.univ_inter]
    exact ENNReal.inv_mul_cancel ha (measure_ne_top _ _)
  rw [lintegral_congr_ae he]
  simp

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FavorablePairFraction
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma integral_le_of_tail_domination {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (f : α → ℝ) (g : β → ℝ)
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[ν] g) {C : ℝ} (hC : 0 ≤ C)
    (ht : ∀ t > 0, μ {x | t < f x} ≤ ENNReal.ofReal C * ν {y | t < g y}) :
    (∫ x, f x ∂μ) ≤ C * ∫ y, g y ∂ν := by
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (integral_nonneg_of_ae hg0))).mp
  rw [ENNReal.ofReal_mul hC,ofReal_integral_eq_lintegral_ofReal hf hf0,
    ofReal_integral_eq_lintegral_ofReal hg hg0,
    lintegral_eq_lintegral_meas_lt μ hf0 hf.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν hg0 hg.aemeasurable,
    ← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
  exact setLIntegral_mono' measurableSet_Ioi (fun t ht' => ht t ht')

lemma capExcessTest_nonneg (a D : ℝ) (x : unitInterval) : 0 ≤ capExcessTest a D x :=
  le_max_right _ _

lemma capExcessTest_tail {a D t : ℝ} (hD : 0 < D) (ht : 0 < t)
    (_ : 0 ≤ a) (hsmall : Real.sqrt (t+a^2) < 1) :
    {x : unitInterval | t < capExcessTest a D x} =
      {x : unitInterval | Real.sqrt (t+a^2)/D < (x:ℝ)} := by
  ext x
  have hsq : 0 ≤ t+a^2 := by positivity
  have hm : 0 ≤ min (D*(x:ℝ)) 1 := le_min (mul_nonneg hD.le x.2.1) zero_le_one
  have hroot := Real.sq_sqrt hsq
  have hrt := Real.sqrt_nonneg (t+a^2)
  change t < max ((min (D*(x:ℝ)) 1)^2-a^2) 0 ↔ _
  rw [lt_max_iff]
  simp only [not_lt.mpr ht.le,or_false]
  change t < min (D*(x:ℝ)) 1 ^ 2 - a ^ 2 ↔ Real.sqrt (t+a^2)/D < (x:ℝ)
  rw [div_lt_iff₀ hD]
  constructor
  · intro h
    have hh : Real.sqrt (t+a^2) < min (D*(x:ℝ)) 1 := by nlinarith
    exact (hh.trans_le (min_le_left _ _)).trans_eq (mul_comm _ _)
  · intro h
    have hh : Real.sqrt (t+a^2) < min (D*(x:ℝ)) 1 := lt_min (by nlinarith) hsmall
    nlinarith

lemma capExcessTest_tail_empty {a D t : ℝ} (hD : 0 ≤ D) (ht : 0 < t)
    (hlarge : 1 ≤ Real.sqrt (t+a^2)) :
    {x : unitInterval | t < capExcessTest a D x} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hm0 : 0 ≤ min (D*(x:ℝ)) 1 := le_min (mul_nonneg hD x.2.1) zero_le_one
  have hm1 := min_le_right (D*(x:ℝ)) 1
  have hsq := Real.sq_sqrt (show 0 ≤ t+a^2 by positivity)
  change t < max ((min (D*(x:ℝ)) 1)^2-a^2) 0 at hx
  rcases lt_max_iff.mp hx with hx | hx <;> nlinarith

lemma capExcess_integral_comparison (μ ν : ProbabilityMeasure unitInterval)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (htail : ∀ u > 0, (μ : Measure unitInterval) {x | u < (x:ℝ)} ≤
      ENNReal.ofReal C * (ν : Measure unitInterval) {y | u/D < (y:ℝ)})
    (a : ℝ) (ha : 0 ≤ a) :
    (∫ x, capExcessTest a 1 x ∂(μ : Measure unitInterval)) ≤
      C * ∫ y, capExcessTest a D y ∂(ν : Measure unitInterval) := by
  apply integral_le_of_tail_domination _ _ _ _
    ((capExcessTest a 1).continuous.integrable_of_hasCompactSupport (by exact HasCompactSupport.of_compactSpace _))
    ((capExcessTest a D).continuous.integrable_of_hasCompactSupport (by exact HasCompactSupport.of_compactSpace _))
    (ae_of_all _ (capExcessTest_nonneg a 1)) (ae_of_all _ (capExcessTest_nonneg a D)) hC
  intro t ht
  by_cases hh : Real.sqrt (t+a^2) < 1
  · rw [capExcessTest_tail (by norm_num : (0:ℝ)<1) ht ha hh,
      capExcessTest_tail hD ht ha hh,div_one]
    exact htail _ (Real.sqrt_pos.mpr (by positivity))
  · rw [capExcessTest_tail_empty (by norm_num : (0:ℝ)≤1) ht (le_of_not_gt hh)]
    simp

lemma capped_tail_le_excess (x : unitInterval) {A : ℝ} (hA : 0 < A) (_ : A ≤ 1) :
    (if A < (x:ℝ) then (x:ℝ)^2 else 0) ≤ 2 * capExcessTest (A/2) 1 x := by
  have hx0 := x.2.1
  have hx1 := x.2.2
  change _ ≤ 2 * max ((min (1*(x:ℝ)) 1)^2-(A/2)^2) 0
  rw [one_mul,min_eq_left hx1]
  split_ifs with h
  · have hm := le_max_left ((x:ℝ)^2-(A/2)^2) 0
    nlinarith
  · positivity

lemma capExcess_le_scaled_tail (y : unitInterval) {a D : ℝ} (ha : 0 ≤ a) (hD : 0 < D) :
    capExcessTest a D y ≤ D^2 * (if a/D < (y:ℝ) then (y:ℝ)^2 else 0) := by
  have hy0 := y.2.1
  have hm0 : 0 ≤ min (D*(y:ℝ)) 1 := le_min (mul_nonneg hD.le hy0) zero_le_one
  have hmy := min_le_left (D*(y:ℝ)) 1
  change max ((min (D*(y:ℝ)) 1)^2-a^2) 0 ≤ _
  split_ifs with h
  · apply max_le <;> nlinarith [sq_nonneg a]
  · have hh : D*(y:ℝ) ≤ a := by
      have hh := (le_div_iff₀ hD).mp (le_of_not_gt h)
      nlinarith
    apply max_le <;> nlinarith [sq_nonneg a]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WeakTailTransfer
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma weak_probability_open_le_limsup {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs atTop (𝓝 μ)) (G : Set X) (hG : IsOpen G) :
    (μ : Measure X).real G ≤ limsup (fun n => (μs n : Measure X).real G) atTop := by
  have hh := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hG
  have he : liminf (fun n => (μs n : Measure X).real G) atTop =
      (liminf (fun n => (μs n : Measure X) G) atTop).toReal :=
    ENNReal.liminf_toReal_eq (by norm_num : (1:ℝ≥0∞) ≠ ∞)
      (Eventually.of_forall fun n => (prob_le_one : (μs n : Measure X) G ≤ 1))
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => (μs n : Measure X).real G) :=
    isBoundedUnder_of ⟨1,fun n => measureReal_le_one⟩
  have hc : IsBoundedUnder (· ≥ ·) atTop (fun n => (μs n : Measure X).real G) :=
    isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
  have hfin : (liminf (fun n => (μs n : Measure X) G) atTop) ≠ ∞ := by
    apply ne_top_of_le_ne_top (by norm_num : (1:ℝ≥0∞)≠∞)
    exact (liminf_le_limsup).trans (limsup_le_of_le (h := Eventually.of_forall fun n => (prob_le_one : (μs n : Measure X) G ≤ 1)))
  have hi : (μ : Measure X).real G ≤ liminf (fun n => (μs n : Measure X).real G) atTop := by
    rw [he]
    exact ENNReal.toReal_mono hfin hh
  exact hi.trans (liminf_le_limsup hb hc)

lemma weak_probability_limsup_closed_le {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs atTop (𝓝 μ)) (G : Set X) (hG : IsClosed G) :
    limsup (fun n => (μs n : Measure X).real G) atTop ≤ (μ : Measure X).real G := by
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hG
  change limsup (fun n => ((μs n : Measure X) G).toReal) atTop ≤ _
  rw [ENNReal.limsup_toReal_eq (f := atTop) (by norm_num : (1:ℝ≥0∞)≠∞)
    (Eventually.of_forall fun n => (prob_le_one : (μs n : Measure X) G ≤ 1))]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hh

lemma weak_tail_comparison
    (μs νs : ℕ → ProbabilityMeasure unitInterval) (μ ν : ProbabilityMeasure unitInterval)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (ht : ∀ u > 0, u < 1 →
      limsup (fun n => (μs n : Measure unitInterval).real {x | u < (x:ℝ)}) atTop ≤
      C * limsup (fun n => (νs n : Measure unitInterval).real {y | u/D < (y:ℝ)}) atTop) :
    ∀ u > 0, (μ : Measure unitInterval) {x | u < (x:ℝ)} ≤
      ENNReal.ofReal C * (ν : Measure unitInterval) {y | u/(2*D) < (y:ℝ)} := by
  intro u hu
  by_cases hu1 : u < 1
  · have hop : IsOpen {x : unitInterval | u < (x:ℝ)} := isOpen_lt continuous_const continuous_subtype_val
    have hcl : IsClosed {x : unitInterval | u/D ≤ (x:ℝ)} := isClosed_le continuous_const continuous_subtype_val
    have hsub : ∀ n, (νs n : Measure unitInterval).real {y | u/D < (y:ℝ)} ≤
        (νs n : Measure unitInterval).real {y | u/D ≤ (y:ℝ)} :=
      fun n => measureReal_mono (by intro y hy; exact (show u/D < (y:ℝ) from hy).le) (measure_ne_top _ _)
    have hs := limsup_le_limsup (Eventually.of_forall hsub)
      (isBoundedUnder_of (r := (· ≥ ·)) ⟨0,fun n => measureReal_nonneg⟩).isCoboundedUnder_le
      (show IsBoundedUnder (· ≤ ·) atTop (fun n => (νs n : Measure unitInterval).real {y | u/D ≤ (y:ℝ)}) from
        isBoundedUnder_of ⟨1,fun n => measureReal_le_one⟩)
    have hre : (μ : Measure unitInterval).real {x | u < (x:ℝ)} ≤
        C * (ν : Measure unitInterval).real {y | u/(2*D) < (y:ℝ)} := by
      refine (weak_probability_open_le_limsup μs μ hμ _ hop).trans ((ht u hu hu1).trans ?_)
      apply mul_le_mul_of_nonneg_left _ hC
      refine hs.trans ((weak_probability_limsup_closed_le νs ν hν _ hcl).trans ?_)
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro y hy
      have hh : u/(2*D) < u/D := by
        apply (div_lt_div_iff₀ (by positivity) hD).mpr
        nlinarith
      exact hh.trans_le hy
    have hh := ENNReal.ofReal_le_ofReal hre
    simpa only [ENNReal.ofReal_mul hC,ofReal_measureReal (measure_ne_top _ _)] using hh
  · have he : {x : unitInterval | u < (x:ℝ)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt.mpr (x.2.2.trans (le_of_not_gt hu1))) hx
    rw [he,measure_empty]
    exact bot_le

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_CompactCapTransfer
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.array_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma capExcessTest_le_one (a : ℝ) {D : ℝ} (hD : 0 ≤ D) (x : unitInterval) :
    capExcessTest a D x ≤ 1 := by
  have hh0 : 0 ≤ min (D*(x:ℝ)) 1 := le_min (mul_nonneg hD x.2.1) zero_le_one
  have hh1 := min_le_right (D*(x:ℝ)) 1
  change max ((min (D*(x:ℝ)) 1)^2-a^2) 0 ≤ 1
  apply max_le <;> nlinarith [sq_nonneg a]

lemma capExcess_integrable (a D : ℝ) (μ : ProbabilityMeasure unitInterval) :
    Integrable (capExcessTest a D) (μ : Measure unitInterval) :=
  (capExcessTest a D).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma capExcess_integral_bounds (a : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (μ : ProbabilityMeasure unitInterval) :
    0 ≤ (∫ x, capExcessTest a D x ∂(μ : Measure unitInterval)) ∧
    (∫ x, capExcessTest a D x ∂(μ : Measure unitInterval)) ≤ 1 := by
  constructor
  · exact integral_nonneg (capExcessTest_nonneg _ _)
  · calc
      _ ≤ ∫ x : unitInterval, (1:ℝ) ∂(μ : Measure unitInterval) :=
        integral_mono (capExcess_integrable _ _ _) (integrable_const _)
          (capExcessTest_le_one a hD)
      _ = 1 := by simp

lemma compact_capped_moment_transfer
    (μs νs : ℕ → ProbabilityMeasure unitInterval)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (ht : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∀ u > 0, u < 1 →
      limsup (fun n => (μs (ns n) : Measure unitInterval).real {x | u < (x:ℝ)}) atTop ≤
      C * limsup (fun n => (νs (ns n) : Measure unitInterval).real {y | u/D < (y:ℝ)}) atTop)
    (a : ℝ) (ha : 0 ≤ a) :
    limsup (fun n => ∫ x, capExcessTest a 1 x ∂(μs n : Measure unitInterval)) atTop ≤
      C * limsup (fun n => ∫ y, capExcessTest a (2*D) y ∂(νs n : Measure unitInterval)) atTop := by
  let F : ℕ → ℝ := fun n => ∫ x, capExcessTest a 1 x ∂(μs n : Measure unitInterval)
  let G : ℕ → ℝ := fun n => ∫ y, capExcessTest a (2*D) y ∂(νs n : Measure unitInterval)
  have hF0 (n) : 0 ≤ F n := (capExcess_integral_bounds a (by norm_num) _).1
  have hF1 (n) : F n ≤ 1 := (capExcess_integral_bounds a (by norm_num) _).2
  have hG0 (n) : 0 ≤ G n := (capExcess_integral_bounds a (by positivity) _).1
  have hG1 (n) : G n ≤ 1 := (capExcess_integral_bounds a (by positivity) _).2
  have hFb : IsBoundedUnder (· ≤ ·) atTop F := isBoundedUnder_of ⟨1,hF1⟩
  have hFc : IsCoboundedUnder (· ≤ ·) atTop F := isCoboundedUnder_le_of_le atTop hF0
  have hGb : IsBoundedUnder (· ≤ ·) atTop G := isBoundedUnder_of ⟨1,hG1⟩
  apply (limsup_le_iff hFc hFb).mpr
  intro b hb
  by_contra hbad
  have hfreq : ∃ᶠ n in atTop, b ≤ F n := by simpa only [not_eventually,not_lt] using hbad
  obtain ⟨ns,hns,hnsb⟩ := exists_seq_forall_of_frequently hfreq
  obtain ⟨p,hp,ks,hks,hpk⟩ := isCompact_univ.tendsto_subseq
    (x := fun n => (μs (ns n),νs (ns n))) (fun _ => Set.mem_univ _)
  have hμ : Tendsto (fun n => μs (ns (ks n))) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hpk
  have hν : Tendsto (fun n => νs (ns (ks n))) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hpk
  have htail := weak_tail_comparison _ _ _ _ hμ hν hC hD
    (ht (ns ∘ ks) (hns.comp hks.tendsto_atTop))
  have hcomp := capExcess_integral_comparison p.1 p.2 hC (by positivity : 0 < 2*D) htail a ha
  have hlimF : Tendsto (F ∘ (ns ∘ ks)) atTop
      (𝓝 (∫ x, capExcessTest a 1 x ∂(p.1 : Measure unitInterval))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ)
      (BoundedContinuousFunction.mkOfCompact (capExcessTest a 1))
  have hlimG : Tendsto (G ∘ (ns ∘ ks)) atTop
      (𝓝 (∫ y, capExcessTest a (2*D) y ∂(p.2 : Measure unitInterval))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν)
      (BoundedContinuousFunction.mkOfCompact (capExcessTest a (2*D)))
  have hhF := ge_of_tendsto hlimF (Eventually.of_forall fun n => hnsb (ks n))
  have hhG : (∫ y, capExcessTest a (2*D) y ∂(p.2 : Measure unitInterval)) ≤ limsup G atTop := by
    rw [← hlimG.limsup_eq]
    exact (hns.comp hks.tendsto_atTop).limsup_comp_le_limsup
      (isCoboundedUnder_le_of_le atTop (fun n => hG0 (ns (ks n)))) hGb
  exact (not_le_of_gt hb) (hhF.trans (hcomp.trans (mul_le_mul_of_nonneg_left hhG hC)))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CappedMomentTransfer
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma limsup_le_mul_of_bounded_nonneg (F G : ℕ → ℝ) {C B : ℝ}
    (hC : 0 ≤ C) (hF : ∀ n, 0 ≤ F n) (hG : ∀ n, 0 ≤ G n)
    (hG1 : ∀ n, G n ≤ B) (hFG : ∀ n, F n ≤ C*G n) :
    limsup F atTop ≤ C*limsup G atTop := by
  have hGb : IsBoundedUnder (· ≤ ·) atTop G := isBoundedUnder_of ⟨B,hG1⟩
  have hCb : IsBoundedUnder (· ≤ ·) atTop (fun n => C*G n) :=
    isBoundedUnder_of ⟨C*B,fun n => mul_le_mul_of_nonneg_left (hG1 n) hC⟩
  have hh := limsup_le_limsup (Eventually.of_forall hFG)
    (isCoboundedUnder_le_of_le atTop hF) hCb
  have hm := limsup_mul_le (u := fun _ : ℕ => C) (v := G)
    (Eventually.of_forall fun _ => hC).frequently
    (isBoundedUnder_of ⟨C,fun _ => le_rfl⟩)
    (Eventually.of_forall hG) hGb
  simp only [limsup_const] at hm
  exact hh.trans hm

lemma unitTailSquare_bounds (a : ℝ) (x : unitInterval) :
    0 ≤ unitTailSquare a x ∧ unitTailSquare a x ≤ 1 := by
  have hx0 := x.2.1
  have hx1 := x.2.2
  unfold unitTailSquare
  split_ifs <;> constructor <;> nlinarith

lemma unitTailSquare_measurable (a : ℝ) : Measurable (unitTailSquare a) := by
  exact Measurable.ite (measurableSet_lt measurable_const measurable_subtype_coe)
    (measurable_subtype_coe.pow_const 2) measurable_const

lemma unitTailSquare_integrable (a : ℝ) (μ : ProbabilityMeasure unitInterval) :
    Integrable (unitTailSquare a) (μ : Measure unitInterval) := by
  apply (integrable_const (1:ℝ)).mono' (unitTailSquare_measurable a).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_of_nonneg (unitTailSquare_bounds a x).1]
    exact (unitTailSquare_bounds a x).2)

lemma unitTailSquare_integral_bounds (a : ℝ) (μ : ProbabilityMeasure unitInterval) :
    0 ≤ (∫ x, unitTailSquare a x ∂(μ : Measure unitInterval)) ∧
    (∫ x, unitTailSquare a x ∂(μ : Measure unitInterval)) ≤ 1 := by
  constructor
  · exact integral_nonneg fun x => (unitTailSquare_bounds a x).1
  · calc
      _ ≤ ∫ x : unitInterval, (1:ℝ) ∂(μ : Measure unitInterval) :=
        integral_mono (unitTailSquare_integrable a μ) (integrable_const _)
          (fun x => (unitTailSquare_bounds a x).2)
      _ = 1 := by simp

lemma compact_tail_square_moment_transfer
    (μs νs : ℕ → ProbabilityMeasure unitInterval)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (ht : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∀ u > 0, u < 1 →
      limsup (fun n => (μs (ns n) : Measure unitInterval).real {x | u < (x:ℝ)}) atTop ≤
      C * limsup (fun n => (νs (ns n) : Measure unitInterval).real {y | u/D < (y:ℝ)}) atTop)
    {A : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) :
    limsup (fun n => ∫ x, unitTailSquare A x ∂(μs n : Measure unitInterval)) atTop ≤
      (8*C*D^2) * limsup (fun n => ∫ y, unitTailSquare (A/(4*D)) y ∂(νs n : Measure unitInterval)) atTop := by
  have h1 := limsup_le_mul_of_bounded_nonneg
    (fun n => ∫ x, unitTailSquare A x ∂(μs n : Measure unitInterval))
    (fun n => ∫ x, capExcessTest (A/2) 1 x ∂(μs n : Measure unitInterval))
    (C := 2) (B := 1) (by norm_num)
    (fun n => (unitTailSquare_integral_bounds A (μs n)).1)
    (fun n => (capExcess_integral_bounds (A/2) zero_le_one (μs n)).1)
    (fun n => (capExcess_integral_bounds (A/2) zero_le_one (μs n)).2) (by
      intro n
      rw [← integral_const_mul]
      exact integral_mono (unitTailSquare_integrable A _) ((capExcess_integrable _ _ _).const_mul _)
        (fun x => capped_tail_le_excess x hA hA1))
  have h2 := compact_capped_moment_transfer μs νs hC hD ht (A/2) (by positivity)
  have h3 := limsup_le_mul_of_bounded_nonneg
    (fun n => ∫ y, capExcessTest (A/2) (2*D) y ∂(νs n : Measure unitInterval))
    (fun n => ∫ y, unitTailSquare (A/(4*D)) y ∂(νs n : Measure unitInterval))
    (C := (2*D)^2) (B := 1) (sq_nonneg _)
    (fun n => (capExcess_integral_bounds (A/2) (by positivity) (νs n)).1)
    (fun n => (unitTailSquare_integral_bounds _ (νs n)).1)
    (fun n => (unitTailSquare_integral_bounds _ (νs n)).2) (by
      intro n
      rw [← integral_const_mul]
      apply integral_mono (capExcess_integrable _ _ _) ((unitTailSquare_integrable _ _).const_mul _)
      intro y
      have he : A/2/(2*D) = A/(4*D) := by ring
      simpa only [he,unitTailSquare] using capExcess_le_scaled_tail y (by positivity : 0 ≤ A/2) (by positivity : 0 < 2*D))
  calc
    _ ≤ 2*(C*(((2*D)^2)*limsup (fun n => ∫ y, unitTailSquare (A/(4*D)) y ∂(νs n : Measure unitInterval)) atTop)) :=
      h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hC)) (by norm_num))
    _ = _ := by ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma medianDeviation_nonneg {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) (X : Path d) : 0 ≤ medianDeviation ℓ f b H X := by
  cases H with
  | zero => exact abs_nonneg _
  | succ H => exact (abs_nonneg _).trans (le_max_right _ _)

lemma measurable_medianDeviation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) : Measurable (medianDeviation ℓ f b H) := by
  induction H with
  | zero => exact (((measurable_of_countable (signedCoordinate f)).comp
      (measurable_recordIndexPosition ℓ 0)).sub_const (b 0)).abs
  | succ H ih => exact ih.max ((((measurable_of_countable (signedCoordinate f)).comp
      (measurable_recordIndexPosition ℓ (H+1))).sub_const (b (H+1))).abs)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyAverageMoment
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience
lemma limsup_nonneg_const_mul (F : ℕ → ℝ) {C B : ℝ} (hC : 0 ≤ C)
    (hF : ∀ n, 0 ≤ F n) (hB : ∀ n, F n ≤ B) :
    limsup (fun n => C*F n) atTop = C*limsup F atTop := by
  have hb : IsBoundedUnder (· ≤ ·) atTop F := isBoundedUnder_of ⟨B,hB⟩
  have hc : IsBoundedUnder (· ≤ ·) atTop (fun _ : ℕ => C) := isBoundedUnder_of ⟨C,fun _ => le_rfl⟩
  have h1 := le_limsup_mul (u := F) (v := fun _ : ℕ => C)
    (Eventually.of_forall hF).frequently hb (Eventually.of_forall (fun _ => hC)) hc
  have h2 := limsup_mul_le (u := F) (v := fun _ : ℕ => C)
    (Eventually.of_forall hF).frequently hb (Eventually.of_forall (fun _ => hC)) hc
  change limsup F atTop * liminf (fun _ : ℕ => C) atTop ≤ limsup (fun n => F n*C) atTop at h1
  change limsup (fun n => F n*C) atTop ≤ limsup F atTop * limsup (fun _ : ℕ => C) atTop at h2
  simp only [liminf_const,limsup_const,mul_comm] at h1 h2
  exact le_antisymm h2 h1
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_MomentRescaling
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma min_rescale {L : ℝ} (hL : 0 < L) (x : ℝ) : min x L = L*min (x/L) 1 := by
  rw [← div_self (ne_of_gt hL),min_div_div_right hL.le]
  field_simp

lemma cappedMoment_scale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) {L : ℝ} (hL : 0 < L) :
    cappedMoment μ X L = L^2*cappedMoment μ (fun x => X x/L) 1 := by
  unfold cappedMoment
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [min_rescale hL]
  ring

lemma cappedTailMoment_scale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (A : ℝ) {L : ℝ} (hL : 0 < L) :
    cappedTailMoment μ X A L = L^2*cappedTailMoment μ (fun x => X x/L) (A/L) 1 := by
  unfold cappedTailMoment
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [div_lt_div_iff_of_pos_right hL]
  split_ifs
  · rw [min_rescale hL]; ring
  · ring

lemma cappedMoment_unit_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ x, 0 ≤ X x) :
    0 ≤ cappedMoment μ X 1 ∧ cappedMoment μ X 1 ≤ 1 := by
  have hb (x) : 0 ≤ (min (X x) 1)^2 ∧ (min (X x) 1)^2 ≤ 1 := by
    have h0 := le_min (hX0 x) zero_le_one
    have h1 := min_le_right (X x) 1
    constructor <;> nlinarith
  have hi : Integrable (fun x => (min (X x) 1)^2) μ :=
    (integrable_const (1:ℝ)).mono' ((hX.min measurable_const).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb x).1] using (hb x).2))
  constructor
  · exact integral_nonneg (fun x => (hb x).1)
  · calc
      _ ≤ ∫ x, (1:ℝ) ∂μ := integral_mono hi (integrable_const _) (fun x => (hb x).2)
      _ = 1 := by simp

lemma cappedTailMoment_unit_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (hX0 : ∀ x, 0 ≤ X x) (A : ℝ) :
    0 ≤ cappedTailMoment μ X A 1 ∧ cappedTailMoment μ X A 1 ≤ 1 := by
  let f := fun x => if A < X x then (min (X x) 1)^2 else 0
  have hb (x) : 0 ≤ f x ∧ f x ≤ 1 := by
    have h0 := le_min (hX0 x) zero_le_one
    have h1 := min_le_right (X x) 1
    dsimp [f]
    split_ifs <;> constructor <;> nlinarith
  have hm : Measurable f := Measurable.ite (measurableSet_lt measurable_const hX)
    ((hX.min measurable_const).pow_const 2) measurable_const
  have hi : Integrable f μ := (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb x).1] using (hb x).2))
  constructor
  · exact integral_nonneg (fun x => (hb x).1)
  · calc
      _ ≤ ∫ x, (1:ℝ) ∂μ := integral_mono hi (integrable_const _) (fun x => (hb x).2)
      _ = 1 := by simp

lemma limsup_cappedMoment_scale {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hX0 : ∀ n x, 0 ≤ X n x) {L : ℝ} (hL : 0 < L) :
    limsup (fun n => cappedMoment (μ n) (X n) L) atTop =
    L^2*limsup (fun n => cappedMoment (μ n) (fun x => X n x/L) 1) atTop := by
  simp only [cappedMoment_scale _ _ hL]
  apply limsup_nonneg_const_mul _ (sq_nonneg L)
    (fun n => (cappedMoment_unit_bounds (μ n) _ ((hX n).div_const L) (fun x => div_nonneg (hX0 n x) hL.le)).1)
    (fun n => (cappedMoment_unit_bounds (μ n) _ ((hX n).div_const L) (fun x => div_nonneg (hX0 n x) hL.le)).2)

lemma limsup_cappedTailMoment_scale {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hX0 : ∀ n x, 0 ≤ X n x) (A : ℝ) {L : ℝ} (hL : 0 < L) :
    limsup (fun n => cappedTailMoment (μ n) (X n) A L) atTop =
    L^2*limsup (fun n => cappedTailMoment (μ n) (fun x => X n x/L) (A/L) 1) atTop := by
  simp only [cappedTailMoment_scale _ _ _ hL]
  apply limsup_nonneg_const_mul _ (sq_nonneg L)
    (fun n => (cappedTailMoment_unit_bounds (μ n) _ ((hX n).div_const L) (fun x => div_nonneg (hX0 n x) hL.le) _).1)
    (fun n => (cappedTailMoment_unit_bounds (μ n) _ ((hX n).div_const L) (fun x => div_nonneg (hX0 n x) hL.le) _).2)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SuccessfulScaledTail
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma unitCap_tail {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (x : ℝ) :
    u < (unitCap x : ℝ) ↔ u < x := by
  change u < min (max x 0) 1 ↔ _
  rw [lt_min_iff,lt_max_iff]
  simp only [not_lt.mpr hu.le,or_false,hu1,and_true]

lemma unitCap_coe_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (unitCap x : ℝ) = min x 1 := by simp [unitCap,max_eq_left hx]

lemma unitCapLaw_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (unitCapLaw μ X hX : Measure unitInterval).real {x | u < (x:ℝ)} = μ.real {x | u < X x} := by
  change (μ.map (unitCap ∘ X)).real _ = _
  unfold Measure.real
  rw [Measure.map_apply (continuous_unitCap.measurable.comp hX)
    (measurableSet_lt measurable_const measurable_subtype_coe)]
  have he : (unitCap ∘ X) ⁻¹' {x | u < (x:ℝ)} = {x | u < X x} := by
    ext x
    exact unitCap_tail hu hu1 (X x)
  rw [he]

lemma unitCapLaw_integral_tail_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ x, 0 ≤ X x) {A : ℝ} (hA : 0 < A) (hA1 : A < 1) :
    (∫ x, unitTailSquare A x ∂(unitCapLaw μ X hX : Measure unitInterval)) =
      ∫ x, (if A < X x then (min (X x) 1)^2 else 0) ∂μ := by
  rw [show (unitCapLaw μ X hX : Measure unitInterval) = μ.map (unitCap ∘ X) from rfl,
    integral_map (continuous_unitCap.measurable.comp hX).aemeasurable
      (unitTailSquare_measurable A).aestronglyMeasurable]
  congr 1
  funext x
  simp only [Function.comp_apply,unitTailSquare]
  simp only [unitCap_tail hA hA1]
  rw [unitCap_coe_of_nonneg (hX0 x)]

lemma raw_capped_tail_moment_transfer {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : ℕ → Measure Ω) (ν : ℕ → Measure Ξ)
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (X : ℕ → Ω → ℝ) (Y : ℕ → Ξ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hX0 : ∀ n x, 0 ≤ X n x) (hY0 : ∀ n y, 0 ≤ Y n y)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (ht : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∀ u > 0,
      limsup (fun n => (μ (ns n)).real {x | u < X (ns n) x}) atTop ≤
      C * limsup (fun n => (ν (ns n)).real {y | u/D < Y (ns n) y}) atTop)
    {A : ℝ} (hA : 0 < A) (hA1 : A < 1) :
    limsup (fun n => ∫ x, (if A < X n x then (min (X n x) 1)^2 else 0) ∂μ n) atTop ≤
      (8*C*D^2) * limsup (fun n => ∫ y, (if A/(4*D) < Y n y then (min (Y n y) 1)^2 else 0) ∂ν n) atTop := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  let μs := fun n => unitCapLaw (μ n) (X n) (hX n)
  let νs := fun n => unitCapLaw (ν n) (Y n) (hY n)
  have hh := compact_tail_square_moment_transfer μs νs hC hD0 (by
    intro ns hns u hu hu1
    have hh := ht ns hns u hu
    have hud : u/D < 1 := (div_lt_one hD0).mpr (hu1.trans_le hD)
    simpa only [μs,νs,unitCapLaw_tail _ _ _ hu hu1,
      unitCapLaw_tail _ _ _ (div_pos hu hD0) hud] using hh) hA hA1.le
  have had0 : 0 < A/(4*D) := by positivity
  have had1 : A/(4*D) < 1 := (div_lt_one (by positivity)).mpr (by nlinarith)
  simpa only [μs,νs,unitCapLaw_integral_tail_square _ _ _ (hX0 _) hA hA1,
    unitCapLaw_integral_tail_square _ _ _ (hY0 _) had0 had1] using hh

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FullCapTransfer
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma capExcess_zero_one (x : unitInterval) : capExcessTest 0 1 x = (x:ℝ)^2 := by
  simp [capExcessTest,min_eq_left x.2.2,max_eq_left (sq_nonneg (x:ℝ))]

lemma capExcess_zero_le_scaled (x : unitInterval) {D : ℝ} (hD : 0 ≤ D) :
    capExcessTest 0 D x ≤ D^2*(x:ℝ)^2 := by
  have hx := x.2.1
  have h0 : 0 ≤ min (D*(x:ℝ)) 1 := le_min (mul_nonneg hD hx) zero_le_one
  change max ((min (D*(x:ℝ)) 1)^2-0^2) 0 ≤ _
  simp only [zero_pow (by norm_num : 2 ≠ 0),sub_zero,max_eq_left (sq_nonneg _)]
  nlinarith [min_le_left (D*(x:ℝ)) 1]

lemma unitCapLaw_integral_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ x, 0 ≤ X x) :
    (∫ x : unitInterval, (x:ℝ)^2 ∂(unitCapLaw μ X hX : Measure unitInterval)) =
    ∫ x, (min (X x) 1)^2 ∂μ := by
  have hc : Continuous (fun x : unitInterval => (x:ℝ)^2) := continuous_subtype_val.pow 2
  rw [show (unitCapLaw μ X hX : Measure unitInterval) = μ.map (unitCap ∘ X) from rfl,
    integral_map (continuous_unitCap.measurable.comp hX).aemeasurable hc.aestronglyMeasurable]
  congr 1
  funext x
  simp only [Function.comp_apply,unitCap_coe_of_nonneg (hX0 x)]

lemma raw_capped_moment_transfer {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : ℕ → Measure Ω) (ν : ℕ → Measure Ξ)
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (X : ℕ → Ω → ℝ) (Y : ℕ → Ξ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hX0 : ∀ n x, 0 ≤ X n x) (hY0 : ∀ n y, 0 ≤ Y n y)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (ht : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∀ u > 0,
      limsup (fun n => (μ (ns n)).real {x | u < X (ns n) x}) atTop ≤
      C * limsup (fun n => (ν (ns n)).real {y | u/D < Y (ns n) y}) atTop) :
    limsup (fun n => ∫ x, (min (X n x) 1)^2 ∂μ n) atTop ≤
      (4*C*D^2) * limsup (fun n => ∫ y, (min (Y n y) 1)^2 ∂ν n) atTop := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  let μs := fun n => unitCapLaw (μ n) (X n) (hX n)
  let νs := fun n => unitCapLaw (ν n) (Y n) (hY n)
  have hh := compact_capped_moment_transfer μs νs hC hD0 (by
    intro ns hns u hu hu1
    have hh := ht ns hns u hu
    have hud : u/D < 1 := (div_lt_one hD0).mpr (hu1.trans_le hD)
    simpa only [μs,νs,unitCapLaw_tail _ _ _ hu hu1,
      unitCapLaw_tail _ _ _ (div_pos hu hD0) hud] using hh) 0 le_rfl
  have hsqint (p : ProbabilityMeasure unitInterval) : Integrable (fun x : unitInterval => (x:ℝ)^2) (p : Measure unitInterval) :=
    (continuous_subtype_val.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs (p : ProbabilityMeasure unitInterval) : (∫ x : unitInterval, (x:ℝ)^2 ∂(p : Measure unitInterval)) ≤ 1 := by
    calc
      _ ≤ ∫ x : unitInterval, (1:ℝ) ∂(p : Measure unitInterval) := integral_mono (hsqint p) (integrable_const _) (fun x => by
        have h0 := x.2.1; have h1 := x.2.2; nlinarith)
      _ = 1 := by simp
  have hk := limsup_le_mul_of_bounded_nonneg
    (fun n => ∫ x, capExcessTest 0 (2*D) x ∂(νs n : Measure unitInterval))
    (fun n => ∫ x : unitInterval, (x:ℝ)^2 ∂(νs n : Measure unitInterval))
    (sq_nonneg _) (fun n => integral_nonneg (capExcessTest_nonneg _ _))
    (fun n => integral_nonneg (fun _ => sq_nonneg _)) (fun n => hs (νs n)) (by
      intro n
      rw [← integral_const_mul]
      exact integral_mono (capExcess_integrable _ _ _) ((hsqint _).const_mul _) (fun x => capExcess_zero_le_scaled x (by positivity)))
  have hm := hh.trans (mul_le_mul_of_nonneg_left hk hC)
  simp only [capExcess_zero_one] at hm
  simp only [μs,νs,unitCapLaw_integral_square _ _ _ (hX0 _),unitCapLaw_integral_square _ _ _ (hY0 _)] at hm
  nlinarith only [hm]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma successfulMedian_unit_moment_transfer {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (z : ℕ → ℝ) (hz0 : ∀ n, 0 < z n) (hz : Tendsto z atTop atTop) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    let X := fun n X => medianDeviation ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) (H n) X / z n
    let Y := fun n P => partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n
    (limsup (fun n => ∫ x, (min (X n x) 1)^2 ∂successfulAverage ν ℓ (H n)) atTop ≤
      (8000/p^2) * limsup (fun n => ∫ y, (min (Y n y) 1)^2 ∂independentConditionedPairLaw ν ℓ) atTop) ∧
    (∀ A, 0 < A → A < 1 →
      limsup (fun n => ∫ x, (if A < X n x then (min (X n x) 1)^2 else 0) ∂successfulAverage ν ℓ (H n)) atTop ≤
      (16000/p^2) * limsup (fun n => ∫ y, (if A/40 < Y n y then (min (Y n y) 1)^2 else 0) ∂independentConditionedPairLaw ν ℓ) atTop) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  let b : ℕ → ℝ := fun j => (recordMedian ν ℓ hp f j:ℝ)
  let X := fun n X => medianDeviation ℓ f b (H n) X / z n
  let Y := fun n P => partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n
  let μ := fun n => successfulAverage ν ℓ (H n)
  let υ := fun _ : ℕ => independentConditionedPairLaw ν ℓ
  have hμ : ∀ n, IsProbabilityMeasure (μ n) := fun n => successfulAverage_probability ν hue ℓ (signed_direction_unit e) htrans (H n)
  have hυ : ∀ n, IsProbabilityMeasure (υ n) := fun _ => independentConditionedPairLaw_probability ν ℓ hp
  have hp0 : 0 < p := ENNReal.toReal_pos hp (measure_ne_top _ _)
  have hmX (n) : Measurable (X n) := (measurable_medianDeviation ℓ f b (H n)).div_const _
  have hmY (n) : Measurable (Y n) :=
    (measurable_partialSumMax (commonIncrementProcess ℓ f) (measurable_commonIncrementProcess ℓ f) (H n)).div_const _
  have hX0 (n) (x) : 0 ≤ X n x := div_nonneg (medianDeviation_nonneg _ _ _ _ _) (hz0 n).le
  have hY0 (n) (y) : 0 ≤ Y n y := div_nonneg (partialSumMax_nonneg _ _) (hz0 n).le
  have ht : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∀ u > 0,
      limsup (fun n => (μ (ns n)).real {x | u < X (ns n) x}) atTop ≤
      (20/p^2) * limsup (fun n => (υ (ns n)).real {y | u/10 < Y (ns n) y}) atTop := by
    intro ns hns u hu
    exact successfulMedian_scaled_tail_comparison ν hue e f htrans (H ∘ ns) (hH.comp hns)
      (z ∘ ns) (fun n => hz0 (ns n)) (hz.comp hns) hu
  constructor
  · have hh := @raw_capped_moment_transfer _ _ _ _ μ υ hμ hυ X Y hmX hmY hX0 hY0 (20/p^2) 10 (by positivity) (by norm_num) ht
    change limsup (fun n => ∫ x, (min (X n x) 1)^2 ∂μ n) atTop ≤
      (8000/p^2) * limsup (fun n => ∫ y, (min (Y n y) 1)^2 ∂υ n) atTop
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro A hA hA1
    have hh := @raw_capped_tail_moment_transfer _ _ _ _ μ υ hμ hυ X Y hmX hmY hX0 hY0 (20/p^2) 10 (by positivity) (by norm_num) ht A hA hA1
    change limsup (fun n => ∫ x, (if A < X n x then (min (X n x) 1)^2 else 0) ∂μ n) atTop ≤
      (16000/p^2) * limsup (fun n => ∫ y, (if A/40 < Y n y then (min (Y n y) 1)^2 else 0) ∂υ n) atTop
    norm_num only at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma successfulMedian_moment_transfer {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (z : ℕ → ℝ) (hz0 : ∀ n, 0 < z n) (hz : Tendsto z atTop atTop)
    {A L : ℝ} (hA : 0 < A) (hAL : A < L) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    let X := fun n X => medianDeviation ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) (H n) X / z n
    let Y := fun n P => partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n
    (limsup (fun n => cappedMoment (successfulAverage ν ℓ (H n)) (X n) L) atTop ≤
      (8000/p^2) * limsup (fun n => cappedMoment (independentConditionedPairLaw ν ℓ) (Y n) L) atTop) ∧
    (limsup (fun n => cappedTailMoment (successfulAverage ν ℓ (H n)) (X n) A L) atTop ≤
      (16000/p^2) * limsup (fun n => cappedTailMoment (independentConditionedPairLaw ν ℓ) (Y n) (A/40) L) atTop) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  let b : ℕ → ℝ := fun j => (recordMedian ν ℓ hp f j:ℝ)
  let X := fun n X => medianDeviation ℓ f b (H n) X / z n
  let Y := fun n P => partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n
  let μ := fun n => successfulAverage ν ℓ (H n)
  let υ := fun _ : ℕ => independentConditionedPairLaw ν ℓ
  have hμ : ∀ n, IsProbabilityMeasure (μ n) := fun n => successfulAverage_probability ν hue ℓ (signed_direction_unit e) htrans (H n)
  have hυ : ∀ n, IsProbabilityMeasure (υ n) := fun _ => independentConditionedPairLaw_probability ν ℓ hp
  have hmX (n) : Measurable (X n) := (measurable_medianDeviation ℓ f b (H n)).div_const _
  have hmY (n) : Measurable (Y n) :=
    (measurable_partialSumMax (commonIncrementProcess ℓ f) (measurable_commonIncrementProcess ℓ f) (H n)).div_const _
  have hX0 (n) (x) : 0 ≤ X n x := div_nonneg (medianDeviation_nonneg _ _ _ _ _) (hz0 n).le
  have hY0 (n) (y) : 0 ≤ Y n y := div_nonneg (partialSumMax_nonneg _ _) (hz0 n).le
  have hL : 0 < L := hA.trans hAL
  have hh := successfulMedian_unit_moment_transfer ν hue e f htrans H hH
    (fun n => L*z n) (fun n => mul_pos hL (hz0 n)) (hz.const_mul_atTop hL)
  have h1 : limsup (fun n => cappedMoment (μ n) (fun x => X n x/L) 1) atTop ≤
      (8000/p^2)*limsup (fun n => cappedMoment (υ n) (fun y => Y n y/L) 1) atTop := by
    simpa only [cappedMoment,X,Y,b,μ,υ,div_div,mul_comm] using hh.1
  have h2 : limsup (fun n => cappedTailMoment (μ n) (fun x => X n x/L) (A/L) 1) atTop ≤
      (16000/p^2)*limsup (fun n => cappedTailMoment (υ n) (fun y => Y n y/L) ((A/40)/L) 1) atTop := by
    have haL : 0 < A/L := div_pos hA hL
    have haL1 : A/L < 1 := (div_lt_one hL).mpr hAL
    simpa only [cappedTailMoment,X,Y,b,μ,υ,div_div,mul_comm] using hh.2 (A/L) haL haL1
  change (limsup (fun n => cappedMoment (μ n) (X n) L) atTop ≤
      (8000/p^2) * limsup (fun n => cappedMoment (υ n) (Y n) L) atTop) ∧
    (limsup (fun n => cappedTailMoment (μ n) (X n) A L) atTop ≤
      (16000/p^2) * limsup (fun n => cappedTailMoment (υ n) (Y n) (A/40) L) atTop)
  constructor
  · rw [@limsup_cappedMoment_scale _ _ μ hμ X hmX hX0 L hL,
      @limsup_cappedMoment_scale _ _ υ hυ Y hmY hY0 L hL]
    calc
      _ ≤ L^2*((8000/p^2)*_) := mul_le_mul_of_nonneg_left h1 (sq_nonneg L)
      _ = _ := by ring
  · rw [@limsup_cappedTailMoment_scale _ _ μ hμ X hmX hX0 A L hL,
      @limsup_cappedTailMoment_scale _ _ υ hυ Y hmY hY0 (A/40) L hL]
    calc
      _ ≤ L^2*((16000/p^2)*_) := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
      _ = _ := by ring

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ScaledMaxMoment
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma sq_min_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (min a b)^2 = min (a^2) (b^2) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h,min_eq_left (pow_le_pow_left₀ ha h 2)]
  · rw [min_eq_right h,min_eq_right (pow_le_pow_left₀ hb h 2)]

lemma cappedMoment_scaled_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : ∀ x, 0 ≤ X x)
    {r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b) :
    cappedMoment μ (fun x => X x/r) b = truncatedVariance μ X (b*r)/r^2 := by
  unfold cappedMoment truncatedVariance
  rw [← integral_div]
  congr 1
  funext x
  nth_rw 1 [show b = (b*r)/r from (mul_div_cancel_right₀ b (ne_of_gt hr)).symm]
  rw [min_div_div_right hr.le,div_pow,sq_min_nonneg (hX x) (mul_nonneg hb hr.le)]

lemma iid_scaled_max_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b) (n : ℕ) :
    cappedMoment μ (fun ω => partialSumMax (fun k => X k ω) n/r) b ≤
      5*(n:ℝ)*truncatedVariance μ (X 0) (b*r)/r^2 := by
  rw [cappedMoment_scaled_eq μ _ (fun ω => partialSumMax_nonneg _ _) hr hb]
  exact div_le_div_of_nonneg_right
    (integral_partialSumMax_capped_le μ X hX hind hident hsym (mul_nonneg hb hr.le) n) (sq_nonneg r)

lemma scaled_max_moment_ratio_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hne : 0 < μ {ω | X 0 ω ≠ 0})
    {r b t : ℝ} (hr : 0 < r) (hb : 0 ≤ b) (n : ℕ)
    (hn : (n:ℝ) ≤ t*fluctuationScale μ (X 0) r) :
    cappedMoment μ (fun ω => partialSumMax (fun k => X k ω) n/r) b ≤
      5*t*(truncatedVariance μ (X 0) (b*r)/truncatedVariance μ (X 0) r) := by
  have hm : 0 < truncatedVariance μ (X 0) r := truncatedVariance_pos μ (X 0) (hX 0) hne hr
  have hm0 := truncatedVariance_nonneg μ (X 0) (b*r)
  have hmul : (n:ℝ)*truncatedVariance μ (X 0) r ≤ t*r^2 := by
    rw [fluctuationScale,← mul_div_assoc] at hn
    exact (le_div_iff₀ hm).mp hn
  apply (iid_scaled_max_moment_le μ X hX hind hident hsym hr hb n).trans
  rw [div_le_iff₀ (sq_pos_of_pos hr)]
  have heq : (5*t*(truncatedVariance μ (X 0) (b*r)/truncatedVariance μ (X 0) r))*r^2 =
      (5*truncatedVariance μ (X 0) (b*r))*(t*r^2)/truncatedVariance μ (X 0) r := by ring
  rw [heq,le_div_iff₀ hm]
  nlinarith [mul_le_mul_of_nonneg_left hmul (mul_nonneg (by norm_num : (0:ℝ) ≤ 5) hm0)]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma successful_small_variance_bound_oai {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrinf : Tendsto r atTop atTop)
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) {b t F : ℝ} (hb : 0 < b)
    (hHt : ∀ᶠ n in atTop, (H n:ℝ) ≤ t*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r n))
    (hF : Tendsto (fun n => truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (b*r n) /
      truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r n)) atTop (𝓝 F)) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    limsup (fun n => cappedMoment (successfulAverage ν ℓ (H n))
      (fun X => medianDeviation ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) (H n) X/r n) b) atTop ≤
      (40000/p^2)*t*F := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  let μ := independentConditionedPairLaw ν ℓ
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ hp
  let X := commonIncrementProcess ℓ f
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hM := successfulMedian_moment_transfer ν hue e f htrans H hH r hr hrinf
    (A := b/2) (L := b) (by positivity) (by linarith)
  have hlim : Tendsto (fun n => 5*t*(truncatedVariance μ (X 0) (b*r n)/truncatedVariance μ (X 0) (r n)))
      atTop (𝓝 (5*t*F)) := tendsto_const_nhds.mul hF
  have hbound : limsup (fun n => cappedMoment μ (fun P => partialSumMax (fun k => X k P) (H n)/r n) b) atTop ≤ 5*t*F := by
    rw [← hlim.limsup_eq]
    have hev : ∀ᶠ n in atTop, cappedMoment μ (fun P => partialSumMax (fun k => X k P) (H n)/r n) b ≤
        5*t*(truncatedVariance μ (X 0) (b*r n)/truncatedVariance μ (X 0) (r n)) := by
      filter_upwards [hHt] with n hn
      exact scaled_max_moment_ratio_bound μ X (measurable_commonIncrementProcess ℓ f)
        (commonIncrements_independent ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
        (commonIncrements_identDistrib ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
        (independent_commonWordIncrement_symmetric ν ℓ htrans f) hne (hr n) hb.le (H n) hn
    have h0 : ∀ n, (0:ℝ) ≤ cappedMoment μ (fun P => partialSumMax (fun k => X k P) (H n)/r n) b :=
      fun n => integral_nonneg fun P => sq_nonneg _
    exact limsup_le_limsup hev (isCoboundedUnder_le_of_le atTop h0) hlim.isBoundedUnder_le
  have hC : 0 ≤ 8000/p^2 := by positivity
  calc
    _ ≤ (8000/p^2)*limsup (fun n => cappedMoment μ (fun P => partialSumMax (fun k => X k P) (H n)/r n) b) atTop := hM.1
    _ ≤ (8000/p^2)*(5*t*F) := mul_le_mul_of_nonneg_left hbound hC
    _ = _ := by ring

end DirectionalTransience

end

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.successful_small_variance_bound_oai := @OAI.DirectionalTransience.successful_small_variance_bound_oai
