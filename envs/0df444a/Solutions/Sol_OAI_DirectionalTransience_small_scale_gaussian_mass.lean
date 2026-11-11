-- Prove2me | solution 1 for OAI.DirectionalTransience.small_scale_gaussian_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:03:19.90803+00:00
-- url     : https://prove2.me/submissions/1e4942c3-79ac-4ac4-8dfb-a68b6c999f80

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal007
import Theorems.Thm_OAI_DirectionalTransience_recordFluctuationScale_tendsto
import Theorems.Thm_OAI_DirectionalTransience_shared_median_pair_path_limit

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_CoordinateStrip
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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

lemma realPartialSum_succ (X : ℕ → ℝ) (n : ℕ) :
    realPartialSum X (n+1) = realPartialSum X n+X n := by simp [realPartialSum,Finset.sum_range_succ]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SymmetricTruncate
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridOscillation
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

lemma unitRamp_zero {t : ℝ} (ht : t ≤ 0) : unitRamp t = 0 := by
  simp [unitRamp,max_eq_left ht]
lemma unitRamp_one {t : ℝ} (ht : 1 ≤ t) : unitRamp t = 1 := by
  simp [unitRamp,max_eq_right (by linarith : 0 ≤ t),min_eq_left ht]
lemma unitRamp_self {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : unitRamp t = t := by
  simp [unitRamp,max_eq_right ht,min_eq_right ht1]

lemma linearPolygon_formula (x : ℕ → ℝ) (N : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (hN : ⌊t⌋₊ < N) :
    linearPolygon x N t = realPartialSum x ⌊t⌋₊ + (t-⌊t⌋₊)*x ⌊t⌋₊ := by
  let j := ⌊t⌋₊
  have hj : (j:ℝ) ≤ t := Nat.floor_le ht
  have hj1 : t < j+1 := Nat.lt_floor_add_one t
  have hNj : j+1 ≤ N := hN
  have hsplit : N = j+1+(N-(j+1)) := (Nat.add_sub_of_le hNj).symm
  unfold linearPolygon
  rw [hsplit,Finset.sum_range_add,Finset.sum_range_succ]
  have hleft : (∑ k ∈ Finset.range j, unitRamp (t-k)*x k) = realPartialSum x j := by
    unfold realPartialSum
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : (k:ℝ)+1 ≤ j := by exact_mod_cast Finset.mem_range.mp hk
    rw [unitRamp_one (by linarith),one_mul]
  rw [hleft,unitRamp_self (by linarith) (by linarith)]
  have htail : (∑ k ∈ Finset.range (N-(j+1)), unitRamp (t-(j+1+k))*x (j+1+k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    rw [unitRamp_zero (by linarith),zero_mul]
  simpa [j] using congrArg (fun z => realPartialSum x j+(t-j)*x j+z) htail

lemma polygonPath_apply (N : ℕ) (scale : ℝ) (x : ℕ → ℝ) (t : unitInterval) :
    polygonPath N scale x t = linearPolygon x N (scale*t) := by
  simp only [polygonPath,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    ContinuousMap.coe_mk,smul_eq_mul,linearPolygon]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma scaledPolygon_apply (x : ℕ → ℝ) (r n T : ℝ) (t : unitInterval) :
    scaledPolygon x r n T t = linearPolygon x (⌊T*n⌋₊+1) (T*n*t)/r := by
  simp [scaledPolygon,polygonPath_apply,div_eq_inv_mul]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OrderedTimes
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
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

lemma orderedTimes_succ (I : Finset unitInterval) (i : Fin I.card) :
    orderedTimes I i.succ = I.orderEmbOfFin rfl i := by simp [orderedTimes]

lemma continuous_path_measure_ext (μ ν : Measure C(unitInterval,ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ I : Finset unitInterval, μ.map (fun f : C(unitInterval,ℝ) => I.restrict f) =
      ν.map (fun f : C(unitInterval,ℝ) => I.restrict f)) : μ = ν := by
  classical
  let e := TopologicalSpace.denseSeq unitInterval
  let E := fun f : C(unitInterval,ℝ) => fun n => f (e n)
  have hE : Continuous E := continuous_pi (fun n => continuous_eval_const _)
  have hEinj : Function.Injective E := by
    intro f g hfg
    apply ContinuousMap.coe_injective
    exact TopologicalSpace.denseRange_denseSeq unitInterval |>.equalizer
      f.continuous g.continuous hfg
  apply hE.measurableEmbedding hEinj |>.map_injective
  let P := fun J : Finset ℕ => (μ.map E).map J.restrict
  have : ∀ J, IsFiniteMeasure (P J) := fun _ => inferInstance
  apply IsProjectiveLimit.unique (P := P) (fun _ => rfl)
  intro J
  let I := J.image e
  let g := fun f : I → ℝ => fun j : J => f ⟨e j,Finset.mem_image_of_mem e j.2⟩
  have hg : Measurable g := by fun_prop
  have hm : Measurable (J.restrict : (ℕ → ℝ) → (J → ℝ)) := by fun_prop
  change (ν.map E).map J.restrict = (μ.map E).map J.restrict
  rw [Measure.map_map hm hE.measurable,Measure.map_map hm hE.measurable]
  have he : J.restrict ∘ E = g ∘ (fun f : C(unitInterval,ℝ) => I.restrict f) := rfl
  rw [he,← Measure.map_map hg (continuous_path_restrict I).measurable,
    ← Measure.map_map hg (continuous_path_restrict I).measurable,h I]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightIncrement
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
namespace DirectionalTransience

lemma realPartialSum_heightIncrement (F : ℕ → ℝ) (h : ℕ) :
    realPartialSum (heightIncrement F) h = F h-F 0 := by
  induction h with
  | zero => simp [realPartialSum]
  | succ h ih => rw [realPartialSum_succ,ih,heightIncrement]; ring

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightPolygon
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
namespace DirectionalTransience

lemma heightPolygon_formula (F : ℕ → ℝ) (r n T : ℝ) (h : 0 ≤ T*n) (t : unitInterval) :
    heightPolygon F r n T t =
      (F ⌊T*n*(t:ℝ)⌋₊ + (T*n*(t:ℝ)-⌊T*n*(t:ℝ)⌋₊)*
        (F (⌊T*n*(t:ℝ)⌋₊+1)-F ⌊T*n*(t:ℝ)⌋₊))/r := by
  have ht : 0 ≤ T*n*(t:ℝ) := mul_nonneg h t.2.1
  have hN : ⌊T*n*(t:ℝ)⌋₊ < ⌊T*n⌋₊+1 :=
    Nat.lt_succ_of_le (Nat.floor_mono (mul_le_of_le_one_right h t.2.2))
  simp only [heightPolygon,ContinuousMap.add_apply,ContinuousMap.const_apply,scaledPolygon_apply,
    linearPolygon_formula _ _ ht hN,realPartialSum_heightIncrement,heightIncrement]
  ring

lemma heightPolygon_grid (F : ℕ → ℝ) (r n T : ℝ) (h : 0 ≤ T*n)
    (j : ℕ) (t : unitInterval) (ht : T*n*(t:ℝ) = j) :
    heightPolygon F r n T t = F j/r := by
  rw [heightPolygon_formula F r n T h,ht]
  simp

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_GaussianPathFiniteLawSingleton
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
namespace DirectionalTransience

lemma gaussianPathFiniteLaw_singleton (T : ℝ) (t : unitInterval) :
    (gaussianPathFiniteLaw T {t}).map (fun x => x ⟨t,by simp⟩) =
      gaussianReal 0 (Real.toNNReal (T*(t:ℝ))) := by
  let I : Finset unitInterval := {t}
  let z : Fin I.card := ⟨0,by simp [I]⟩
  have hj (j : Fin I.card) : j = z := by apply Fin.ext; have := j.isLt; simp [I] at this; omega
  have htimes0 (j : Fin I.card) : orderedTimes I j.castSucc = 0 := by
    rw [hj j]
    simp [orderedTimes,z]
  have htimes1 (j : Fin I.card) : orderedTimes I j.succ = t := by
    rw [orderedTimes_succ]
    exact Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem I rfl j)
  have hc (x : Fin I.card → ℝ) : incrementCumsum I x ⟨t,by simp [I]⟩ = x z := by
    simp only [incrementCumsum,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk]
    rw [show Finset.Iic ((I.orderIsoOfFin rfl).symm ⟨t,by simp [I]⟩) = {z} by
      ext j; simp only [Finset.mem_Iic,Finset.mem_singleton]; rw [hj j,hj ((I.orderIsoOfFin rfl).symm _)]; simp]
    simp
  change (gaussianPathFiniteLaw T I).map _ = _
  unfold gaussianPathFiniteLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : I → ℝ => x ⟨t,by simp [I]⟩) ∘ incrementCumsum I =
      (fun x : Fin I.card → ℝ => x z) := funext hc
  rw [he]
  have hm := (measurePreserving_eval (fun j : Fin I.card => gaussianReal 0
    (Real.toNNReal (T*((orderedTimes I j.succ:ℝ)-orderedTimes I j.castSucc)))) z).map_eq
  rw [hm,htimes0,htimes1]
  simp

lemma wiener_path_eval (W : ProbabilityMeasure C(unitInterval,ℝ)) (T : ℝ)
    (hW : ∀ I : Finset unitInterval,
      (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw T I)
    (t : unitInterval) :
    (W : Measure C(unitInterval,ℝ)).map (fun g => g t) = gaussianReal 0 (Real.toNNReal (T*(t:ℝ))) := by
  rw [← gaussianPathFiniteLaw_singleton T t,← hW {t},Measure.map_map (by fun_prop) (continuous_path_restrict {t}).measurable]
  rfl

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_QuenchedMoments
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

lemma noDropQuenchedKernel_apply {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) (A : Set (Path d)) (hA : MeasurableSet A) :
    noDropQuenchedKernel ℓ x ω A = (noDropQuenched ℓ x ω)⁻¹ *
      quenchedKernel (ω,x) (A ∩ NoDrop ℓ x) := by
  exact (Measure.smul_apply _ _ _).trans (by rw [Measure.restrict_apply hA]; rfl)

lemma noDropQuenched_ne_top {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) : noDropQuenched ℓ x ω ≠ ⊤ := measure_ne_top _ _

instance noDropQuenchedKernel_finite {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    IsFiniteKernel (noDropQuenchedKernel ℓ x) where
  exists_univ_le := by
    refine ⟨1, by simp, fun ω => ?_⟩
    rw [noDropQuenchedKernel_apply _ _ _ _ MeasurableSet.univ, Set.univ_inter]
    change (noDropQuenched ℓ x ω)⁻¹ * noDropQuenched ℓ x ω ≤ 1
    exact ENNReal.inv_mul_le_one _

lemma noDropQuenchedKernel_probability {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) (hq : noDropQuenched ℓ x ω ≠ 0) :
    IsProbabilityMeasure (noDropQuenchedKernel ℓ x ω) := by
  constructor
  rw [noDropQuenchedKernel_apply _ _ _ _ MeasurableSet.univ, Set.univ_inter]
  exact ENNReal.inv_mul_cancel hq (noDropQuenched_ne_top ℓ x ω)

lemma measurable_quenchedNoDropTest {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (F : Path d → ℝ) (hF : Measurable F) : Measurable (quenchedNoDropTest ℓ x F) :=
  hF.stronglyMeasurable.integral_kernel.measurable

lemma noDrop_mass_smul_kernel {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) : noDropQuenched ℓ x ω • noDropQuenchedKernel ℓ x ω =
      (quenchedKernel (ω,x)).restrict (NoDrop ℓ x) := by
  change noDropQuenched ℓ x ω • ((noDropQuenched ℓ x ω)⁻¹ •
    (quenchedKernel (ω,x)).restrict (NoDrop ℓ x)) = _
  by_cases hq : noDropQuenched ℓ x ω = 0
  · rw [hq, zero_smul]
    exact (Measure.restrict_eq_zero.mpr hq).symm
  · rw [smul_smul, ENNReal.mul_inv_cancel hq (noDropQuenched_ne_top ℓ x ω), one_smul]

lemma noDrop_pair_mass_smul_kernel {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (ω : Environment d) :
    (noDropQuenched ℓ x ω * noDropQuenched ℓ y ω) •
      ((noDropQuenchedKernel ℓ x).prod (noDropQuenchedKernel ℓ y)) ω =
        (sharedPairKernel x y ω).restrict (NoDrop ℓ x ×ˢ NoDrop ℓ y) := by
  rw [Kernel.prod_apply]
  calc
    _ = (noDropQuenched ℓ x ω • noDropQuenchedKernel ℓ x ω).prod
        (noDropQuenched ℓ y ω • noDropQuenchedKernel ℓ y ω) := by
      rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    _ = _ := by
      rw [noDrop_mass_smul_kernel, noDrop_mass_smul_kernel, Measure.prod_restrict,
        sharedPairKernel, Kernel.prod_apply]
      rfl

lemma noDropPairEnvironment_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x y : Lattice d)
    (hp : sharedNoDropMass ν ℓ x y ≠ 0) :
    IsProbabilityMeasure (noDropPairEnvironment ν ℓ x y) := by
  constructor
  rw [noDropPairEnvironment, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp (ne_of_lt ((sharedNoDropMass_le_one ν ℓ x y).trans_lt (by simp)))

lemma noDrop_pair_disintegration {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x y : Lattice d) :
    ((noDropQuenchedKernel ℓ x).prod (noDropQuenchedKernel ℓ y)) ∘ₘ
      noDropPairEnvironment ν ℓ x y = sharedConditionedPairLaw ν ℓ x y := by
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _), noDropPairEnvironment,
    lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul (environmentLaw ν)
      (show Measurable (fun ω => noDropQuenched ℓ x ω * noDropQuenched ℓ y ω) from
        (measurable_noDropQuenched ℓ x).mul (measurable_noDropQuenched ℓ y))
      (((noDropQuenchedKernel ℓ x).prod (noDropQuenchedKernel ℓ y)).measurable_coe hA),
    sharedConditionedPairLaw, Measure.smul_apply,
    Measure.restrict_apply hA, sharedPairLaw,
    Measure.bind_apply (hA.inter ((measurableSet_noDrop ℓ x).prod (measurableSet_noDrop ℓ y)))
      (Kernel.aemeasurable _)]
  congr 1
  apply lintegral_congr
  intro ω
  have hm := congrArg (fun μ : Measure (Path d × Path d) => μ A)
    (noDrop_pair_mass_smul_kernel ℓ x y ω)
  simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
    Pi.mul_apply] using hm

lemma noDropPairEnvironment_ae_positive {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x y : Lattice d) : ∀ᵐ ω ∂noDropPairEnvironment ν ℓ x y,
      noDropQuenched ℓ x ω ≠ 0 ∧ noDropQuenched ℓ y ω ≠ 0 := by
  apply Measure.smul_absolutelyContinuous.ae_le
  apply (ae_withDensity_iff
    (show Measurable (fun ω => noDropQuenched ℓ x ω * noDropQuenched ℓ y ω) from
      (measurable_noDropQuenched ℓ x).mul (measurable_noDropQuenched ℓ y))).mpr
  exact ae_of_all _ fun ω h => ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

lemma integral_kernel_average {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (μ : Measure Ω) (κ : Kernel Ω S) (F : S → ℝ)
    (hF : Integrable F (κ ∘ₘ μ)) :
    ∫ z, F z ∂κ ∘ₘ μ = ∫ ω, ∫ z, F z ∂κ ω ∂μ := by
  rw [Measure.comp_eq_comp_const_apply] at hF ⊢
  exact Kernel.integral_comp hF

lemma noDrop_pair_test_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (hp : sharedNoDropMass ν ℓ x y ≠ 0)
    (F G : Path d → ℝ) (hF : Measurable F) (hG : Measurable G)
    (CF CG : ℝ) (hFb : ∀ X, ‖F X‖ ≤ CF) (hGb : ∀ X, ‖G X‖ ≤ CG) :
    ∫ ω, quenchedNoDropTest ℓ x F ω * quenchedNoDropTest ℓ y G ω
      ∂noDropPairEnvironment ν ℓ x y =
    ∫ P, F P.1 * G P.2 ∂sharedConditionedPairLaw ν ℓ x y := by
  let := sharedConditionedPairLaw_probability ν ℓ x y hp
  have hFG : Integrable (fun P : Path d × Path d => F P.1 * G P.2)
      (sharedConditionedPairLaw ν ℓ x y) := by
    apply Integrable.of_bound ((hF.comp measurable_fst).mul
      (hG.comp measurable_snd)).aestronglyMeasurable (CF*CG)
    exact ae_of_all _ fun P => by
      change ‖F P.1 * G P.2‖ ≤ CF*CG
      rw [norm_mul]
      exact mul_le_mul (hFb P.1) (hGb P.2) (norm_nonneg _) ((norm_nonneg _).trans (hFb P.1))
  rw [← noDrop_pair_disintegration ν ℓ x y] at hFG ⊢
  rw [integral_kernel_average _ _ _ hFG]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only
    rw [Kernel.prod_apply, integral_prod_mul]
    rfl

lemma noDrop_pair_test_first_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (hp : sharedNoDropMass ν ℓ x y ≠ 0)
    (F : Path d → ℝ) (hF : Measurable F) (C : ℝ) (hFb : ∀ X, ‖F X‖ ≤ C) :
    ∫ ω, quenchedNoDropTest ℓ x F ω ∂noDropPairEnvironment ν ℓ x y =
    ∫ P, F P.1 ∂sharedConditionedPairLaw ν ℓ x y := by
  have h := noDrop_pair_test_moment ν ℓ x y hp F (fun _ => 1) hF measurable_const
    C 1 hFb (fun _ => by simp)
  simp only [mul_one] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [noDropPairEnvironment_ae_positive ν ℓ x y] with ω hω
  let := noDropQuenchedKernel_probability ℓ y ω hω.2
  simp [quenchedNoDropTest]

lemma noDrop_pair_test_second_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) (hp : sharedNoDropMass ν ℓ x x ≠ 0)
    (F : Path d → ℝ) (hF : Measurable F) (C : ℝ) (hFb : ∀ X, ‖F X‖ ≤ C) :
    ∫ ω, (quenchedNoDropTest ℓ x F ω)^2 ∂noDropPairEnvironment ν ℓ x x =
    ∫ P, F P.1 * F P.2 ∂sharedConditionedPairLaw ν ℓ x x := by
  simpa only [pow_two] using noDrop_pair_test_moment ν ℓ x x hp F F hF hF C C hFb hFb

lemma measurable_medianFirstHitPath {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] (ℓ : Vector d)
    (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d) (x : Lattice d)
    (r n T : ℝ) : Measurable (medianFirstHitPath ν ℓ hp f x r n T) := by
  apply measurable_heightPolygon
  intro h
  exact (((measurable_of_countable (signedCoordinate f)).comp
    (measurable_recordIndexPosition ℓ h)).comp (by fun_prop)).sub_const _

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SecondMomentConcentration
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

lemma integral_squared_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : Ω → ℝ) (hM : Measurable M)
    (C : ℝ) (hbound : ∀ ω, ‖M ω‖ ≤ C) (b : ℝ) :
    (∫ ω, (M ω-b)^2 ∂μ) = (∫ ω, (M ω)^2 ∂μ)-2*b*(∫ ω, M ω ∂μ)+b^2 := by
  have hi : Integrable M μ := Integrable.of_bound hM.aestronglyMeasurable C (ae_of_all _ hbound)
  have his : Integrable (fun ω => (M ω)^2) μ :=
    Integrable.of_bound (hM.pow_const 2).aestronglyMeasurable (C^2) (ae_of_all _ (fun ω => by
      simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hbound ω) 2))
  have hh : (fun ω => (M ω-b)^2) = (fun ω => (M ω)^2-2*b*M ω+b^2) := by funext ω; ring
  have hid : Integrable (fun ω => (M ω)^2-2*b*M ω) μ := his.sub (hi.const_mul (2*b))
  rw [hh,integral_add hid (integrable_const (b^2)),
    integral_sub his (hi.const_mul (2*b)),integral_const_mul]
  simp

lemma squared_error_tendsto_of_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ)
    (hM : ∀ i, Measurable (M i)) (C : ℝ) (hbound : ∀ i ω, ‖M i ω‖ ≤ C)
    (b : ℝ) (hfirst : Tendsto (fun i => ∫ ω, M i ω ∂μ) atTop (𝓝 b))
    (hsecond : Tendsto (fun i => ∫ ω, (M i ω)^2 ∂μ) atTop (𝓝 (b^2))) :
    Tendsto (fun i => ∫ ω, (M i ω-b)^2 ∂μ) atTop (𝓝 0) := by
  have hh := (hsecond.sub (hfirst.const_mul (2*b))).add_const (b^2)
  have hb : b^2-2*b*b+b^2 = 0 := by ring
  simpa only [integral_squared_error μ _ (hM _) C (hbound _) b,hb] using hh

lemma tendstoInMeasure_of_squared_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (M : ℕ → Ω → ℝ) (b : ℝ)
    (hi : ∀ i, Integrable (fun ω => (M i ω-b)^2) μ)
    (hl : Tendsto (fun i => ∫ ω, (M i ω-b)^2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ M atTop (fun _ => b) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hb (i : ℕ) : μ.real {ω | ε ≤ ‖M i ω-b‖} ≤ (∫ ω, (M i ω-b)^2 ∂μ)/(ε^2) := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ (fun ω => sq_nonneg (M i ω-b))) (hi i) (ε^2)
    have hs : {ω | ε ≤ ‖M i ω-b‖} = {ω | ε^2 ≤ (M i ω-b)^2} := by
      ext ω
      change ε ≤ ‖M i ω-b‖ ↔ ε^2 ≤ (M i ω-b)^2
      simpa only [Real.norm_eq_abs,sq_abs] using (sq_le_sq₀ hε.le (abs_nonneg (M i ω-b))).symm
    rw [hs,mul_comm]
    exact hm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun i => (∫ ω, (M i ω-b)^2 ∂μ)/(ε^2)) atTop (𝓝 0) from by simpa using hl.div_const (ε^2))
    (fun _ => measureReal_nonneg) hb

lemma tendstoInMeasure_of_absolutelyContinuous {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] (hac : μ ≪ ν)
    (M : ℕ → Ω → ℝ) (hM : ∀ i, Measurable (M i)) (b : ℝ)
    (hl : TendstoInMeasure ν M atTop (fun _ => b)) :
    TendstoInMeasure μ M atTop (fun _ => b) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun i => (hM i).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ns',hns',hh⟩ := (hl.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  exact ⟨ns',hns',hac.ae_le hh⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_QuenchedConcentration
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma environment_absolutelyContinuous_noDropPair {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d) :
    environmentLaw ν ≪ noDropPairEnvironment ν ℓ x y := by
  apply Measure.AbsolutelyContinuous.smul_right
    (withDensity_absolutelyContinuous' ((measurable_noDropQuenched ℓ x).mul
      (measurable_noDropQuenched ℓ y)).aemeasurable ?_)
  · exact ENNReal.inv_ne_zero.mpr (ne_top_of_le_ne_top (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (sharedNoDropMass_le_one ν ℓ x y))
  · filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans] with ω hω
    exact mul_ne_zero (hω x).ne' (hω y).ne'

lemma norm_quenchedNoDropTest_le {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (F : Path d → ℝ) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ X, ‖F X‖ ≤ C) (ω : Environment d) :
    ‖quenchedNoDropTest ℓ x F ω‖ ≤ C := by
  by_cases hq : noDropQuenched ℓ x ω = 0
  · have hz : noDropQuenchedKernel ℓ x ω = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [noDropQuenchedKernel_apply _ _ _ _ MeasurableSet.univ,Set.univ_inter]
      change (noDropQuenched ℓ x ω)⁻¹*noDropQuenched ℓ x ω = 0
      simp [hq]
    simpa only [quenchedNoDropTest,hz,integral_zero_measure,norm_zero] using hC
  · let := noDropQuenchedKernel_probability ℓ x ω hq
    simpa only [quenchedNoDropTest,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := noDropQuenchedKernel ℓ x ω) (ae_of_all _ hb)

theorem actual_quenched_concentration_of_pair_moments {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (x : Lattice d)
    (F : ℕ → Path d → ℝ) (hF : ∀ i, Measurable (F i)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ i X, ‖F i X‖ ≤ C) (b : ℝ)
    (hfirst : Tendsto (fun i => ∫ P, F i P.1 ∂sharedConditionedPairLaw ν ℓ x x) atTop (𝓝 b))
    (hsecond : Tendsto (fun i => ∫ P, F i P.1 * F i P.2 ∂sharedConditionedPairLaw ν ℓ x x)
      atTop (𝓝 (b^2))) :
    Tendsto (fun i => ∫ ω, (quenchedNoDropTest ℓ x (F i) ω-b)^2
      ∂noDropPairEnvironment ν ℓ x x) atTop (𝓝 0) ∧
    TendstoInMeasure (environmentLaw ν) (fun i => quenchedNoDropTest ℓ x (F i)) atTop (fun _ => b) := by
  have hp := (sharedNoDropMass_pos ν hue ℓ hℓ htrans x x).ne'
  let := noDropPairEnvironment_probability ν ℓ x x hp
  have hm := fun i => measurable_quenchedNoDropTest ℓ x (F i) (hF i)
  have hmb := fun i => norm_quenchedNoDropTest_le ℓ x (F i) C hC (hb i)
  have h1 : Tendsto (fun i => ∫ ω, quenchedNoDropTest ℓ x (F i) ω ∂noDropPairEnvironment ν ℓ x x)
      atTop (𝓝 b) := by
    simpa only [noDrop_pair_test_first_moment ν ℓ x x hp _ (hF _) C (hb _)] using hfirst
  have h2 : Tendsto (fun i => ∫ ω, (quenchedNoDropTest ℓ x (F i) ω)^2 ∂noDropPairEnvironment ν ℓ x x)
      atTop (𝓝 (b^2)) := by
    simpa only [noDrop_pair_test_second_moment ν ℓ x hp _ (hF _) C (hb _)] using hsecond
  have hl := squared_error_tendsto_of_moments (noDropPairEnvironment ν ℓ x x)
    _ hm C hmb b h1 h2
  refine ⟨hl,?_⟩
  apply tendstoInMeasure_of_absolutelyContinuous (environmentLaw ν)
    (noDropPairEnvironment ν ℓ x x) (environment_absolutelyContinuous_noDropPair ν hue ℓ hℓ htrans x x)
    _ hm b
  apply tendstoInMeasure_of_squared_error (noDropPairEnvironment ν ℓ x x) _ b _ hl
  intro i
  apply Integrable.of_bound ((hm i).sub measurable_const |>.pow_const 2).aestronglyMeasurable ((C+‖b‖)^2)
  apply ae_of_all
  intro ω
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (add_le_add (hmb i ω) (le_refl ‖b‖))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_FiniteConditionalDensityTubeTransfer
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
namespace DirectionalTransience

lemma measureReal_le_add_mass_defect {Ω : Type*} [MeasurableSpace Ω]
    (μ η : Measure Ω) [IsProbabilityMeasure μ] [IsFiniteMeasure η] (hη : η ≤ μ)
    (A : Set Ω) (hA : MeasurableSet A) : μ.real A ≤ η.real A+1-η.real Set.univ := by
  have hc : η.real Aᶜ ≤ μ.real Aᶜ := ENNReal.toReal_mono (measure_ne_top _ _) (hη Aᶜ)
  rw [measureReal_compl hA,measureReal_compl hA,show μ.real Set.univ = 1 from probReal_univ] at hc
  linarith

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SuccessfulAverage
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.noDropQuenchedKernel_finite _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_NonCollapsedSums
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma dyadicCut_pos (j : ℕ) : 0 < dyadicCut j := pow_pos (by norm_num) _
lemma dyadicCut_tendsto : Tendsto dyadicCut atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridOccupation
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

lemma layerGridPoint_coe {a : ℝ} (ha : 0 < a) {j : ℕ} (hj : (j:ℝ) ≤ a) :
    (layerGridPoint a j : ℝ) = (j:ℝ)/a := by
  exact congrArg Subtype.val (Set.projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1)
    ⟨div_nonneg (Nat.cast_nonneg _) ha.le,(div_le_one ha).mpr hj⟩)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma layerGridPoint_tendsto (a : ℕ → ℝ) (j : ℕ → ℕ) (v : unitInterval)
    (h : Tendsto (fun i => (j i:ℝ)/a i) atTop (𝓝 (v:ℝ))) :
    Tendsto (fun i => layerGridPoint (a i) (j i)) atTop (𝓝 v) := by
  have hh := (continuous_projIcc (a := (0:ℝ)) (b := 1) (h := by norm_num)).continuousAt.tendsto.comp h
  simpa only [layerGridPoint,Function.comp_def,Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1) v.2,Subtype.eta] using hh

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_QuenchedGaussian
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma pair_weak_test_moments {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (η : Measure (Ω × Ω)) [IsProbabilityMeasure η] (X : ℕ → Ω → E)
    (hX : ∀ i, Measurable (X i)) (W : ProbabilityMeasure E)
    (μ : ℕ → ProbabilityMeasure (E × E))
    (hμ : ∀ i, (μ i : Measure (E × E))=η.map (fun P => (X i P.1,X i P.2)))
    (hlim : Tendsto μ atTop (𝓝 (W.prod W))) (F : E →ᵇ ℝ) :
    Tendsto (fun i => ∫ P, F (X i P.1) ∂η) atTop (𝓝 (∫ z, F z ∂(W : Measure E))) ∧
    Tendsto (fun i => ∫ P, F (X i P.1)*F (X i P.2) ∂η) atTop
      (𝓝 ((∫ z, F z ∂(W : Measure E))^2)) := by
  let F1 : (E × E) →ᵇ ℝ := F.compContinuous ⟨Prod.fst,continuous_fst⟩
  let F2 : (E × E) →ᵇ ℝ := F.compContinuous ⟨Prod.snd,continuous_snd⟩
  have hf := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim F1
  have hg := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim (F1*F2)
  have hmap (i : ℕ) (G : (E × E) →ᵇ ℝ) :
      (∫ z, G z ∂(μ i : Measure (E × E)))=∫ P, G (X i P.1,X i P.2) ∂η := by
    rw [hμ i,integral_map (by fun_prop) G.continuous.aestronglyMeasurable]
  simp_rw [hmap] at hf hg
  have h1 : (∫ z, F1 z ∂(↑(W.prod W) : Measure (E × E)))=∫ z, F z ∂(W : Measure E) := by
    change (∫ z, F z.1 ∂(W : Measure E).prod (W : Measure E))=_
    rw [integral_fun_fst]
    simp
  have h2 : (∫ z, (F1*F2) z ∂(↑(W.prod W) : Measure (E × E)))=(∫ z, F z ∂(W : Measure E))^2 := by
    change (∫ z, F z.1*F z.2 ∂(W : Measure E).prod (W : Measure E))=_
    rw [integral_prod_mul,pow_two]
  rw [h1] at hf
  rw [h2] at hg
  exact ⟨hf,hg⟩

theorem actual_quenched_gaussian_path_tests {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) (T : ℝ) (hT : 0 < T) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      (∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
        (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw (T/(2*commonMeanWidth ν ℓ)) I) ∧
      ∀ x : Lattice d, ∀ F : C(unitInterval,ℝ) →ᵇ ℝ,
      let M := fun i => quenchedMedianPathTest ν ℓ hp f x (r i) (n i) T F
      let b := ∫ z, F z ∂(W : Measure C(unitInterval,ℝ))
      Tendsto (fun i => ∫ ω, (M i ω-b)^2 ∂noDropPairEnvironment ν ℓ x x) atTop (𝓝 0) ∧
      TendstoInMeasure (environmentLaw ν) M atTop (fun _ => b) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  obtain ⟨W,hW,hlim⟩ := shared_median_pair_path_limit ν hue e f hef htrans r hr T hT
  refine ⟨W,hW,?_⟩
  intro x F
  let η := sharedConditionedPairLaw ν ℓ x x
  have : IsProbabilityMeasure η := sharedConditionedPairLaw_probability ν ℓ x x
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans x x))
  let X := fun i => medianFirstHitPath ν ℓ hp f x (r i) (n i) T
  have hX (i : ℕ) : Measurable (X i) := measurable_medianFirstHitPath _ _ _ _ _ _ _ _
  let μ : ℕ → ProbabilityMeasure RealPathPair := fun i => ⟨η.map (fun P => (X i P.1,X i P.2)),
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance⟩
  have hlim' : Tendsto μ atTop (𝓝 (W.prod W)) := hlim (fun _ => x) μ (fun _ => rfl)
  obtain ⟨hm1,hm2⟩ := pair_weak_test_moments η X hX W μ (fun _ => rfl) hlim' F
  exact actual_quenched_concentration_of_pair_moments ν hue ℓ (signed_direction_unit e) htrans x
    (fun i X' => F (X i X')) (fun i => F.continuous.measurable.comp (hX i)) ‖F‖ (norm_nonneg _)
    (fun i X' => F.norm_coe_le_norm _) _ hm1 hm2

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightTubeWindow
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma measurableSet_heightTubeEndpointEvent {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℕ → Ω → ℝ) (hY : ∀ j, Measurable (Y j)) (H : ℕ) (L R : ℝ) :
    MeasurableSet {x | heightTubeEndpointEvent (fun j => Y j x) H L R} := by
  change MeasurableSet ({x | ∀ j ≤ H, |Y j x| ≤ L} ∩ {x | |Y H x| ≤ R})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (hY j).abs measurable_const
  · exact measurableSet_le (hY H).abs measurable_const

lemma heightPolygon_window_implies_tube (Y : ℕ → ℝ) (r n : ℝ) (hr : 0 < r) (hn : 0 < n)
    (B L ρ δ : ℝ) (hBL : B ≤ L) (τ : unitInterval)
    (hg : ‖heightPolygon Y r n 2‖ < B)
    (he : ∀ t : unitInterval, dist t τ ≤ δ → |heightPolygon Y r n 2 t| < ρ)
    (ht : dist (layerGridPoint (2*n) ⌊n⌋₊) τ ≤ δ) :
    heightTubeEndpointEvent Y ⌊n⌋₊ (L*r) (ρ*r) := by
  have h2n : 0 < 2*n := by positivity
  have hj (j : ℕ) (h : j ≤ ⌊n⌋₊) : (j:ℝ) ≤ 2*n := by
    have h' := (Nat.cast_le (α := ℝ)).mpr h
    have hfloor := Nat.floor_le hn.le
    linarith
  have heval (j : ℕ) (h : j ≤ ⌊n⌋₊) : heightPolygon Y r n 2 (layerGridPoint (2*n) j)=Y j/r := by
    apply heightPolygon_grid _ _ _ _ h2n.le
    rw [layerGridPoint_coe h2n (hj j h),mul_div_cancel₀ _ h2n.ne']
  constructor
  · intro j h
    have hh := (heightPolygon Y r n 2).norm_coe_le_norm (layerGridPoint (2*n) j)
    rw [heval j h,Real.norm_eq_abs,abs_div,abs_of_pos hr] at hh
    exact ((div_le_iff₀ hr).mp (hh.trans (hg.le.trans hBL)))
  · have hh := he _ ht
    rw [heval ⌊n⌋₊ le_rfl,abs_div,abs_of_pos hr] at hh
    exact ((div_lt_iff₀ hr).mp hh).le

lemma half_layer_grid_tendsto (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun i => layerGridPoint (2*n i) ⌊n i⌋₊) atTop
      (𝓝 (⟨(1:ℝ)/2,by norm_num,by norm_num⟩ : unitInterval)) := by
  apply layerGridPoint_tendsto
  have hh := ((tendsto_nat_floor_mul_div_atTop (by norm_num : (0:ℝ)≤1)).comp hn).div_const 2
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [one_mul,Function.comp_def]
  funext i
  ring

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_PositiveQuenchedEvent
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

lemma integral_lower_test_le_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → ℝ) (hF : Measurable F)
    (hFb : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (A : Set Ω) (hA : MeasurableSet A)
    (hs : ∀ x, F x ≠ 0 → x ∈ A) : (∫ x, F x ∂μ) ≤ μ.real A := by
  rw [← integral_indicator_one hA]
  apply integral_mono_ae
  · exact Integrable.of_bound hF.aestronglyMeasurable 1
      (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs,abs_of_nonneg (hFb x).1] using (hFb x).2))
  · exact (integrable_const (1:ℝ)).indicator hA
  · exact ae_of_all _ (fun x => by
      by_cases hx : x ∈ A
      · simpa [hx] using (hFb x).2
      · have hz : F x=0 := by contrapose! hx; exact hs x hx
        simp [hx,hz])

lemma event_lower_mass_of_test_concentration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (M p : ℕ → Ω → ℝ) (b : ℝ) (hb : 0 < b)
    (hlim : TendstoInMeasure μ M atTop (fun _ => b))
    (hbound : ∀ᶠ i in atTop, ∀ᵐ x ∂μ, M i x ≤ p i x) :
    Tendsto (fun i => μ.real {x | p i x < b/2}) atTop (𝓝 0) := by
  have hh := (tendstoInMeasure_iff_measureReal_norm.mp hlim) (b/2) (half_pos hb)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hh
  filter_upwards [hbound] with i hi
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hi] with x hx
  intro hp
  change p i x < b/2 at hp
  change b/2 ≤ ‖M i x-b‖
  rw [Real.norm_eq_abs,abs_of_nonpos (by linarith : M i x-b ≤ 0)]
  linarith

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_GaussianQuenchedTube
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma quenched_median_test_concentration_of_law {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) (T : ℝ) (hT : 0 < T)
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hW : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw (T/(2*commonMeanWidth ν (realPosition (step e)))) I)
    (x : Lattice d) (F : C(unitInterval,ℝ) →ᵇ ℝ) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    TendstoInMeasure (environmentLaw ν)
      (fun i => quenchedMedianPathTest ν ℓ hp f x (r i) (n i) T F) atTop
      (fun _ => ∫ g, F g ∂(W : Measure C(unitInterval,ℝ))) := by
  obtain ⟨W',hW',hh⟩ := actual_quenched_gaussian_path_tests ν hue e f hef htrans r hr T hT
  have he : W'=W := by
    apply Subtype.ext
    apply continuous_path_measure_ext (W' : Measure C(unitInterval,ℝ)) (W : Measure C(unitInterval,ℝ))
    intro I
    rw [hW' I,hW I]
  subst W'
  exact (hh x F).2

lemma measurableSet_medianTubeEndpoint {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d)
    (x : Lattice d) (H : ℕ) (L R : ℝ) : MeasurableSet (medianTubeEndpoint ν ℓ hp f x H L R) := by
  have hm (j : ℕ) : Measurable (fun X : Path d => signedCoordinate f
      (recordIndexPosition ℓ j (fun k => X k-x))-(recordMedian ν ℓ hp f j:ℝ)) :=
    (((measurable_of_countable (signedCoordinate f)).comp
      (measurable_recordIndexPosition ℓ j)).comp (by fun_prop)).sub_const _
  exact measurableSet_heightTubeEndpointEvent _ hm H L R

lemma quenched_gaussian_noDrop_tube_from_test {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hW : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw (2/(2*commonMeanWidth ν (realPosition (step e)))) I)
    (ρ δ B : ℝ) (hδ : 0 < δ) (F : C(unitInterval,ℝ) →ᵇ ℝ)
    (hF : ∀ g, 0 ≤ F g ∧ F g ≤ 1)
    (hFs : ∀ g, F g ≠ 0 → ‖g‖ < B ∧ ∀ t : unitInterval,
      dist t (⟨(1:ℝ)/2,by norm_num,by norm_num⟩ : unitInterval) ≤ δ → |g t| < ρ)
    (hb : 0 < ∫ g, F g ∂(W : Measure C(unitInterval,ℝ)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (bStar : ℕ → ℝ) (hbStar : Tendsto bStar atTop atTop) (x : Lattice d) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    Tendsto (fun i => (environmentLaw ν).real {ω |
      (noDropQuenchedKernel ℓ x ω).real
        (medianTubeEndpoint ν ℓ hp f x ⌊n i⌋₊ (bStar i*r i) (ρ*r i)) <
          (∫ g, F g ∂(W : Measure C(unitInterval,ℝ)))/2}) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let τ : unitInterval := ⟨(1:ℝ)/2,by norm_num,by norm_num⟩
  have hn : Tendsto n atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  have ht' : Tendsto (fun i => dist (layerGridPoint (2*n i) ⌊n i⌋₊) τ) atTop (𝓝 0) := by
    simpa only [τ, dist_self] using (half_layer_grid_tendsto n hn).dist (tendsto_const_nhds (x := τ))
  have ht : ∀ᶠ i in atTop, dist (layerGridPoint (2*n i) ⌊n i⌋₊) τ ≤ δ :=
    (ht'.eventually_lt_const hδ).mono fun _ h => h.le
  have hlim := quenched_median_test_concentration_of_law ν hue e f hef htrans r hr 2 (by norm_num) W hW x F
  apply event_lower_mass_of_test_concentration (environmentLaw ν) _ _ _ hb hlim
  filter_upwards [hr.1.eventually_gt_atTop 0,hn.eventually_gt_atTop 0,
    hbStar.eventually_ge_atTop B,ht] with i hri hni hBi hti
  exact ae_of_all _ (fun ω => by
    apply integral_lower_test_le_event (noDropQuenchedKernel ℓ x ω) _
      (F.continuous.measurable.comp (measurable_medianFirstHitPath ν ℓ hp f x (r i) (n i) 2))
      (fun X => hF _) _ (measurableSet_medianTubeEndpoint ν ℓ hp f x _ _ _)
    intro X hX
    obtain ⟨hg,he⟩ := hFs _ hX
    exact heightPolygon_window_implies_tube _ _ _ hri hni B (bStar i) ρ δ hBi τ hg he hti)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_QuenchedSuccessComparison
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma successQuenchedKernel_apply {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    (ω : Environment d) (A : Set (Path d)) (hA : MeasurableSet A) :
    successQuenchedKernel ℓ x H ω A = (crossingQuenched ℓ x H ω)⁻¹ *
      quenchedKernel (ω,x) (A ∩ Cross ℓ x H) := by
  exact (Measure.smul_apply _ _ _).trans (by rw [Measure.restrict_apply hA]; rfl)

instance successQuenchedKernel_finite {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    IsFiniteKernel (successQuenchedKernel ℓ x H) where
  exists_univ_le := by
    refine ⟨1,by simp,fun ω => ?_⟩
    rw [successQuenchedKernel_apply _ _ _ _ _ MeasurableSet.univ,Set.univ_inter]
    exact ENNReal.inv_mul_le_one _

lemma successQuenchedKernel_probability {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    (ω : Environment d) (hq : crossingQuenched ℓ x H ω ≠ 0) :
    IsProbabilityMeasure (successQuenchedKernel ℓ x H ω) := by
  constructor
  rw [successQuenchedKernel_apply _ _ _ _ _ MeasurableSet.univ,Set.univ_inter]
  exact ENNReal.inv_mul_cancel hq (measure_ne_top _ _)

lemma quenched_success_event_comparison {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    (ω : Environment d) (hq : noDropQuenched ℓ x ω ≠ 0)
    (hsub : NoDrop ℓ x ≤ᵐ[quenchedKernel (ω,x)] Cross ℓ x H)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    |(noDropQuenchedKernel ℓ x ω).real A-(successQuenchedKernel ℓ x H ω).real A| ≤
      1-(noDropQuenched ℓ x ω / crossingQuenched ℓ x H ω).toReal := by
  have hpq : noDropQuenched ℓ x ω ≤ crossingQuenched ℓ x H ω := measure_mono_ae hsub
  have ha : crossingQuenched ℓ x H ω ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hq).trans_le hpq)
  let B := noDropQuenchedKernel ℓ x ω
  let C := successQuenchedKernel ℓ x H ω
  let η := (crossingQuenched ℓ x H ω)⁻¹ • (quenchedKernel (ω,x)).restrict (NoDrop ℓ x)
  let : IsProbabilityMeasure B := noDropQuenchedKernel_probability ℓ x ω hq
  let : IsProbabilityMeasure C := successQuenchedKernel_probability ℓ x H ω ha
  have hηB : η ≤ B := by
    apply Measure.le_iff.mpr
    intro E hE
    rw [noDropQuenchedKernel_apply _ _ _ _ hE]
    change (crossingQuenched ℓ x H ω)⁻¹ * (quenchedKernel (ω,x)).restrict (NoDrop ℓ x) E ≤ _
    rw [Measure.restrict_apply hE]
    exact mul_le_mul' (ENNReal.inv_le_inv.mpr hpq) le_rfl
  have hηC : η ≤ C := by
    apply Measure.le_iff.mpr
    intro E hE
    rw [successQuenchedKernel_apply _ _ _ _ _ hE]
    change (crossingQuenched ℓ x H ω)⁻¹ * (quenchedKernel (ω,x)).restrict (NoDrop ℓ x) E ≤ _
    rw [Measure.restrict_apply hE]
    apply mul_le_mul' le_rfl
    apply measure_mono_ae
    filter_upwards [hsub] with X hX
    exact fun h => ⟨h.1,hX h.2⟩
  let : IsFiniteMeasure η := ⟨lt_of_le_of_lt (hηB Set.univ) (measure_lt_top _ _)⟩
  have hm : η.real Set.univ=(noDropQuenched ℓ x ω / crossingQuenched ℓ x H ω).toReal := by
    change ((crossingQuenched ℓ x H ω)⁻¹ * (quenchedKernel (ω,x)).restrict (NoDrop ℓ x) Set.univ).toReal=_
    rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
    congr 1
    exact (ENNReal.div_eq_inv_mul).symm
  have hB := measureReal_le_add_mass_defect B η hηB A hA
  have hC := measureReal_le_add_mass_defect C η hηC A hA
  have hB' : η.real A ≤ B.real A := ENNReal.toReal_mono (measure_ne_top _ _) (hηB A)
  have hC' : η.real A ≤ C.real A := ENNReal.toReal_mono (measure_ne_top _ _) (hηC A)
  rw [hm] at hB hC
  change |B.real A-C.real A| ≤ _
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma noDrop_success_cost_ae_tendsto {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ=1)
    (htrans : DirectionallyTransient ν ℓ) (x : Lattice d)
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    ∀ᵐ ω ∂environmentLaw ν,
      Tendsto (fun i => 1-(noDropQuenched ℓ x ω / crossingQuenched ℓ x (H i) ω).toReal)
        atTop (𝓝 0) := by
  filter_upwards [crossingQuenched_tendsto_ae ν ℓ htrans,
    quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans] with ω hc hq
  have hh := ENNReal.Tendsto.const_mul (tendsto_inv_iff.mpr ((hc x).comp hH))
    (Or.inr (show noDropQuenched ℓ x ω ≠ ⊤ from measure_ne_top _ _))
  rw [ENNReal.mul_inv_cancel (ne_of_gt (hq x)) (measure_ne_top _ _)] at hh
  have hr := (ENNReal.continuousAt_toReal (by simp : (1:ℝ≥0∞)≠⊤)).tendsto.comp hh
  simpa only [div_eq_mul_inv,ENNReal.toReal_one,sub_self] using
    (tendsto_const_nhds.sub hr : Tendsto (fun i => 1-(noDropQuenched ℓ x ω *
      (crossingQuenched ℓ x (H i) ω)⁻¹).toReal) atTop (𝓝 (1-(1:ℝ≥0∞).toReal)))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProbabilityLowerTransfer
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

lemma probability_lower_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (p q cost : ℕ → Ω → ℝ)
    (c : ℝ) (hc : 0 < c)
    (hp : Tendsto (fun i => μ.real {x | p i x < c}) atTop (𝓝 0))
    (hcost : TendstoInMeasure μ cost atTop (fun _ => 0))
    (hb : ∀ i, ∀ᵐ x ∂μ, |p i x-q i x| ≤ cost i x) :
    Tendsto (fun i => μ.real {x | q i x < c/2}) atTop (𝓝 0) := by
  have hh := (tendstoInMeasure_iff_measureReal_norm.mp hcost) (c/2) (half_pos hc)
  simp only [sub_zero] at hh
  have hlim : Tendsto (fun i => μ.real {x | p i x < c}+μ.real {x | c/2 ≤ ‖cost i x‖}) atTop (𝓝 0) := by
    simpa only [add_zero] using hp.add hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => measureReal_nonneg)
  intro i
  apply le_trans _ (measureReal_union_le {x | p i x < c} {x | c/2 ≤ ‖cost i x‖})
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hb i] with x hx
  intro hqx
  change q i x < c/2 at hqx
  change p i x < c ∨ c/2 ≤ ‖cost i x‖
  by_cases hpx : p i x < c
  · exact Or.inl hpx
  · right
    have hp' : c ≤ p i x := le_of_not_gt hpx
    have h' : p i x-q i x ≤ cost i x := (le_abs_self _).trans hx
    have h'' : cost i x ≤ ‖cost i x‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (cost i x)
    linarith

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_PositiveOpenTest
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma positive_bounded_test_of_open {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (O : Set E) (hO : IsOpen O)
    (hc : Oᶜ.Nonempty) (hpos : 0 < μ O) :
    ∃ F : E →ᵇ ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ 1) ∧
      (∀ x, F x ≠ 0 → x ∈ O) ∧ 0 < ∫ x, F x ∂μ := by
  let f : E → ℝ := fun x => min 1 (Metric.infDist x Oᶜ)
  have hf : Continuous f := continuous_const.min (Metric.continuous_infDist_pt Oᶜ)
  have hb (x : E) : 0 ≤ f x ∧ f x ≤ 1 :=
    ⟨le_min (by norm_num) Metric.infDist_nonneg, min_le_left _ _⟩
  let F : E →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f,hf⟩ 1 (fun x y => by
    change |f x-f y| ≤ 1
    rw [abs_le]
    constructor <;> linarith [(hb x).1,(hb x).2,(hb y).1,(hb y).2])
  have hs : Function.support F = O := by
    ext x
    change f x ≠ 0 ↔ x ∈ O
    have he : 0 < Metric.infDist x Oᶜ ↔ x ∈ O := by
      simpa only [Set.notMem_compl_iff] using (hO.isClosed_compl.notMem_iff_infDist_pos hc).symm
    rw [← (hb x).1.lt_iff_ne']
    exact (lt_min_iff.trans (and_iff_right (by norm_num))).trans he
  refine ⟨F,hb,?_,?_⟩
  · intro x hx
    exact hs ▸ hx
  · apply (integral_pos_iff_support_of_nonneg (fun x => (hb x).1)
      (BoundedContinuousFunction.integrable μ F)).mpr
    change 0 < μ (Function.support F)
    rwa [hs]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_PathWindowTest
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma isOpen_pathWindowEvent (τ : unitInterval) (δ ρ B : ℝ) :
    IsOpen (pathWindowEvent τ δ ρ B) :=
  (ContinuousMap.isOpen_setOfPred_mapsTo (isCompact_closedBall τ δ) isOpen_Ioo).inter
    (isOpen_lt continuous_norm continuous_const)

lemma pathWindowEvent_compl_nonempty (τ : unitInterval) (δ ρ B : ℝ) (hδ : 0 ≤ δ) :
    (pathWindowEvent τ δ ρ B)ᶜ.Nonempty := by
  refine ⟨ContinuousMap.const _ (ρ+1),?_⟩
  intro h
  have hh := h.1 (Metric.mem_closedBall_self hδ)
  change -ρ < ρ+1 ∧ ρ+1 < ρ at hh
  linarith [hh.2]

lemma endpoint_window_covered (τ : unitInterval) (ρ : ℝ) :
    {g : C(unitInterval,ℝ) | |g τ| < ρ} ⊆
      ⋃ n : ℕ, pathWindowEvent τ (1/((n:ℝ)+1)) ρ ((n:ℝ)+1) := by
  intro g hg
  have he : 0 < ρ-|g τ| := sub_pos.mpr hg
  obtain ⟨δ,hδ,hgδ⟩ := Metric.continuousAt_iff.mp g.continuous.continuousAt (ρ-|g τ|) he
  have hn : ∀ᶠ n : ℕ in atTop, 1/((n:ℝ)+1) < δ :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hδ
  have hn' : ∀ᶠ n : ℕ in atTop, ‖g‖ < (n:ℝ)+1 := by
    have hh := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop ‖g‖)
    filter_upwards [hh] with n hn
    linarith
  obtain ⟨n,hn,hbn⟩ := (hn.and hn').exists
  refine Set.mem_iUnion.mpr ⟨n,?_,hbn⟩
  intro t ht
  have hd := hgδ (lt_of_le_of_lt ht hn)
  have hgt : |g t| < ρ := by
    rw [Real.dist_eq] at hd
    have ha := abs_add_le (g t-g τ) (g τ)
    rw [sub_add_cancel] at ha
    linarith
  exact abs_lt.mp hgt

theorem positive_path_window_test (μ : Measure C(unitInterval,ℝ)) [IsFiniteMeasure μ]
    (τ : unitInterval) (ρ : ℝ) (hpos : 0 < μ {g | |g τ| < ρ}) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧ ∃ F : C(unitInterval,ℝ) →ᵇ ℝ,
      (∀ g, 0 ≤ F g ∧ F g ≤ 1) ∧
      (∀ g, F g ≠ 0 → ‖g‖ < B ∧ ∀ t : unitInterval, dist t τ ≤ δ → |g t| < ρ) ∧
      0 < ∫ g, F g ∂μ := by
  have hc := endpoint_window_covered τ ρ
  have hn : ∃ n : ℕ, 0 < μ (pathWindowEvent τ (1/((n:ℝ)+1)) ρ ((n:ℝ)+1)) := by
    by_contra! h
    have hz : ∀ n : ℕ, μ (pathWindowEvent τ (1/((n:ℝ)+1)) ρ ((n:ℝ)+1)) = 0 :=
      fun n => le_antisymm (h n) zero_le
    have hu := measure_iUnion_null hz
    exact (ne_of_gt hpos) (measure_mono_null hc hu)
  obtain ⟨n,hn⟩ := hn
  have hB : 0 < (n:ℝ)+1 := by positivity
  have hδ : 0 < 1/((n:ℝ)+1) := by positivity
  obtain ⟨F,hF,hFs,hFp⟩ := positive_bounded_test_of_open μ
    (pathWindowEvent τ (1/((n:ℝ)+1)) ρ ((n:ℝ)+1)) (isOpen_pathWindowEvent _ _ _ _)
    (pathWindowEvent_compl_nonempty _ _ _ _ hδ.le) hn
  refine ⟨_,_,hδ,hB,F,hF,?_,hFp⟩
  intro g hg
  have hh := hFs g hg
  refine ⟨hh.2,fun t ht => ?_⟩
  exact abs_lt.mpr (hh.1 ht)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma gaussianReal_centered_window_pos (v : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < gaussianReal 0 v {z : ℝ | |z| < ρ} := by
  by_cases hv : v = 0
  · rw [hv,gaussianReal_zero_var]
    simp [hρ]
  · apply pos_iff_ne_zero.mpr
    intro hz
    have hh := gaussianReal_absolutelyContinuous' 0 hv hz
    have hs : {z : ℝ | |z| < ρ} = Set.Ioo (-ρ) ρ := by
      ext z
      change |z| < ρ ↔ -ρ < z ∧ z < ρ
      exact abs_lt
    rw [hs,Real.volume_Ioo,ENNReal.ofReal_eq_zero] at hh
    linarith

theorem brownian_positive_common_time_window (W : ProbabilityMeasure C(unitInterval,ℝ)) (T : ℝ)
    (hW : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw T I)
    (τ : unitInterval) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧ ∃ F : C(unitInterval,ℝ) →ᵇ ℝ,
      (∀ g, 0 ≤ F g ∧ F g ≤ 1) ∧
      (∀ g, F g ≠ 0 → ‖g‖ < B ∧ ∀ t : unitInterval, dist t τ ≤ δ → |g t| < ρ) ∧
      0 < ∫ g, F g ∂(W : Measure C(unitInterval,ℝ)) := by
  apply positive_path_window_test
  have hp := gaussianReal_centered_window_pos (Real.toNNReal (T*(τ:ℝ))) hρ
  rw [← wiener_path_eval W T hW τ] at hp
  simpa only [Measure.map_apply (continuous_eval_const τ).measurable
    (isOpen_lt (continuous_abs) continuous_const).measurableSet,Set.preimage_ofPred_eq] using hp

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_GaussianQuenchedMass
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma quenched_gaussian_success_tube_from_test {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hW : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw (2/(2*commonMeanWidth ν (realPosition (step e)))) I)
    (ρ δ B : ℝ) (hδ : 0 < δ) (F : C(unitInterval,ℝ) →ᵇ ℝ)
    (hF : ∀ g, 0 ≤ F g ∧ F g ≤ 1)
    (hFs : ∀ g, F g ≠ 0 → ‖g‖ < B ∧ ∀ t : unitInterval,
      dist t (⟨(1:ℝ)/2,by norm_num,by norm_num⟩ : unitInterval) ≤ δ → |g t| < ρ)
    (hb : 0 < ∫ g, F g ∂(W : Measure C(unitInterval,ℝ)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (bStar : ℕ → ℝ) (hbStar : Tendsto bStar atTop atTop) (x : Lattice d) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    Tendsto (fun i => (environmentLaw ν).real {ω |
      (successQuenchedKernel ℓ x (⌊n i⌋₊:ℝ) ω).real
        (medianTubeEndpoint ν ℓ hp f x ⌊n i⌋₊ (bStar i*r i) (ρ*r i)) <
          (∫ g, F g ∂(W : Measure C(unitInterval,ℝ)))/4}) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let H := fun i => ⌊n i⌋₊
  let A := fun i => medianTubeEndpoint ν ℓ hp f x (H i) (bStar i*r i) (ρ*r i)
  let p := fun i ω => (noDropQuenchedKernel ℓ x ω).real (A i)
  let q := fun i ω => (successQuenchedKernel ℓ x (H i) ω).real (A i)
  let cost := fun i ω => 1-(noDropQuenched ℓ x ω/crossingQuenched ℓ x (H i) ω).toReal
  have hm (i : ℕ) : Measurable (cost i) := measurable_const.sub
    ((measurable_noDropQuenched ℓ x).div (measurable_crossingQuenched ℓ x (H i))).ennreal_toReal
  have hH : Tendsto H atTop atTop := tendsto_nat_floor_atTop.comp
    (recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1)
  have hc : TendstoInMeasure (environmentLaw ν) cost atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun i => (hm i).aestronglyMeasurable)
      (noDrop_success_cost_ae_tendsto ν hue ℓ (signed_direction_unit e) htrans x H hH)
  have hbound (i : ℕ) : ∀ᵐ ω ∂environmentLaw ν, |p i ω-q i ω| ≤ cost i ω := by
    filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue ℓ (signed_direction_unit e) htrans,
      quenched_noDrop_subset_cross_ae ν ℓ htrans] with ω hq hs
    exact quenched_success_event_comparison ℓ x (H i) ω (ne_of_gt (hq x)) (hs x (H i))
      (A i) (measurableSet_medianTubeEndpoint ν ℓ hp f x _ _ _)
  have hh := probability_lower_transfer (environmentLaw ν) p q cost
    ((∫ g, F g ∂(W : Measure C(unitInterval,ℝ)))/2) (half_pos hb)
    (quenched_gaussian_noDrop_tube_from_test ν hue e f hef htrans W hW ρ δ B hδ F hF hFs hb r hr bStar hbStar x)
    hc hbound
  simpa only [div_div,show (2:ℝ)*2=4 by norm_num] using hh

theorem gaussian_quenched_mass {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) {ρ : ℝ} (hρ : 0 < ρ) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ → ℝ,
      IsGaussianSequence (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) r →
      ∀ bStar : ℕ → ℝ, Tendsto bStar atTop atTop → ∀ x : Lattice d,
      let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
      Tendsto (fun i => (environmentLaw ν).real {ω |
        (successQuenchedKernel ℓ x (⌊n i⌋₊:ℝ) ω).real
          (medianTubeEndpoint ν ℓ hp f x ⌊n i⌋₊ (bStar i*r i) (ρ*r i)) < c}) atTop (𝓝 0) := by
  classical
  dsimp only
  let ℓ := realPosition (step e)
  by_cases hex : ∃ r : ℕ → ℝ, IsGaussianSequence (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) r
  · obtain ⟨r₀,hr₀⟩ := hex
    obtain ⟨W,hW,-⟩ := actual_quenched_gaussian_path_tests ν hue e f hef htrans r₀ hr₀ 2 (by norm_num)
    obtain ⟨δ,B,hδ,hB,F,hF,hFs,hb⟩ := brownian_positive_common_time_window W
      (2/(2*commonMeanWidth ν ℓ)) hW ⟨(1:ℝ)/2,by norm_num,by norm_num⟩ hρ
    refine ⟨(∫ g, F g ∂(W : Measure C(unitInterval,ℝ)))/4,by positivity,?_⟩
    intro r hr bStar hbStar x
    exact quenched_gaussian_success_tube_from_test ν hue e f hef htrans W hW ρ δ B hδ F hF hFs hb r hr bStar hbStar x
  · refine ⟨1,by norm_num,?_⟩
    intro r hr
    exact (hex ⟨r,hr⟩).elim

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_VarianceTailDifference
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

lemma truncated_variance_tail_difference {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S) {z : ℝ} (hz : 0 ≤ z) :
    (3/4:ℝ)*z^2*μ.real {x | z < |S x|} ≤
      truncatedVariance μ S z-truncatedVariance μ S (z/2) := by
  have hi (a : ℝ) := integrable_truncated_square μ S hS a
  let E := {x | z < |S x|}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hS.abs
  have hI : Integrable (E.indicator (fun _ => (3/4:ℝ)*z^2)) μ := (integrable_const _).indicator hE
  have heq : (∫ x, E.indicator (fun _ => (3/4:ℝ)*z^2) x ∂μ) = (3/4:ℝ)*z^2*μ.real E := by
    rw [integral_indicator hE]
    simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm]
  unfold truncatedVariance
  rw [← heq,← integral_sub (hi z) (hi (z/2))]
  apply integral_mono hI ((hi z).sub (hi (z/2)))
  intro x
  change E.indicator (fun _ => (3/4:ℝ)*z^2) x ≤ min ((S x)^2) (z^2)-min ((S x)^2) ((z/2)^2)
  by_cases hx : x ∈ E
  · rw [Set.indicator_of_mem hx]
    have hh : z < |S x| := hx
    rw [min_eq_right (by nlinarith [sq_abs (S x)] : z^2 ≤ (S x)^2),
      min_eq_right (by nlinarith [sq_abs (S x)] : (z/2)^2 ≤ (S x)^2)]
    ring_nf
    rfl
  · rw [Set.indicator_of_notMem hx]
    exact sub_nonneg.mpr (min_le_min_left _ (by nlinarith : (z/2)^2 ≤ z^2))

lemma fluctuation_tail_difference {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    fluctuationScale μ S r*μ.real {x | a*r < |S x|} ≤
      (4/(3*a^2))*((truncatedVariance μ S (a*r)-truncatedVariance μ S (a*r/2))/truncatedVariance μ S r) := by
  have hh := truncated_variance_tail_difference μ S hS (mul_nonneg ha.le hr.le)
  have hm := truncatedVariance_pos μ S hS hne hr
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  unfold fluctuationScale
  rw [div_mul_eq_mul_div,div_le_iff₀ hm]
  rw [mul_assoc,div_mul_cancel₀ _ (ne_of_gt hm)]
  rw [div_mul_eq_mul_div,le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<3) ha2)]
  nlinarith [hh]

lemma dyadicCut_add (j k : ℕ) : dyadicCut (j+k) = dyadicCut j*dyadicCut k := by
  exact pow_add _ _ _
lemma dyadicCut_succ (j : ℕ) : dyadicCut (j+1) = dyadicCut j/2 := by
  simp only [dyadicCut,pow_succ]
  ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma dyadic_profile_gaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (F : ℕ → ℝ) {F₀ : ℝ} (hF₀ : 0 < F₀) (hFle : ∀ j, F₀ ≤ F j)
    (hF : ∀ j, Tendsto (fun n => truncatedVariance μ S (dyadicCut j*r n)/truncatedVariance μ S (r n)) atTop (𝓝 (F j)))
    (hFlim : Tendsto F atTop (𝓝 F₀)) (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      fluctuationScale μ S (dyadicCut j*r n)*μ.real {x | dyadicCut k*(dyadicCut j*r n) < |S x|} < δ := by
  let B := fun j => (4/(3*(dyadicCut k)^2))*((F (j+k)-F (j+k+1))/F j)
  have hB : Tendsto B atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => F (j+k)) atTop (𝓝 F₀) := hFlim.comp (tendsto_add_atTop_nat k)
    have h2 : Tendsto (fun j => F (j+k+1)) atTop (𝓝 F₀) := hFlim.comp ((tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat k))
    simpa only [B,Pi.div_apply,sub_self,zero_div,mul_zero] using tendsto_const_nhds.mul ((h1.sub h2).div hFlim (ne_of_gt hF₀))
  filter_upwards [hB.eventually (gt_mem_nhds hδ)] with j hj
  have hm (n) : truncatedVariance μ S (r n) ≠ 0 := ne_of_gt (truncatedVariance_pos μ S hS hne (hr n))
  have hFj : F j ≠ 0 := ne_of_gt (hF₀.trans_le (hFle j))
  have hlim : Tendsto (fun n => (4/(3*(dyadicCut k)^2))*
      ((truncatedVariance μ S (dyadicCut k*(dyadicCut j*r n))-
        truncatedVariance μ S (dyadicCut k*(dyadicCut j*r n)/2))/
        truncatedVariance μ S (dyadicCut j*r n))) atTop (𝓝 (B j)) := by
    have hh := ((((hF (j+k)).sub (hF (j+k+1))).div (hF j) hFj).const_mul (4/(3*(dyadicCut k)^2)))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    rw [dyadicCut_succ (j+k),dyadicCut_add]
    congr 1
    have heq₁ : dyadicCut k*(dyadicCut j*r n) = dyadicCut j*dyadicCut k*r n := by ring
    have heq₂ : dyadicCut k*(dyadicCut j*r n)/2 = (dyadicCut j*dyadicCut k/2)*r n := by ring
    rw [heq₂,heq₁]
    simp only [Pi.div_apply]
    field_simp [hm n]
  filter_upwards [hlim.eventually (gt_mem_nhds hj)] with n hn
  exact (fluctuation_tail_difference μ S hS hne (mul_pos (dyadicCut_pos j) (hr n)) (dyadicCut_pos k)).trans_lt hn

lemma isGaussianSequence_of_dyadic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (hr0 : ∀ᶠ n in atTop, 0 ≤ r n)
    (hGauss : ∀ k, Tendsto (fun n => fluctuationScale μ S (r n)*μ.real {x | dyadicCut k*r n < |S x|}) atTop (𝓝 0)) :
    IsGaussianSequence μ S r := by
  refine ⟨hr,?_⟩
  intro a ha
  obtain ⟨k,hk⟩ := (dyadicCut_tendsto.eventually (gt_mem_nhds ha)).exists
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hGauss k)
    (Eventually.of_forall fun n => mul_nonneg (fluctuationScale_nonneg μ S _) measureReal_nonneg)
  filter_upwards [hr0] with n hn
  apply mul_le_mul_of_nonneg_left _ (fluctuationScale_nonneg μ S _)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx
  exact (mul_le_mul_of_nonneg_right hk.le hn).trans_lt hx

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma double_gaussian_selection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ)
    (z : ℕ → ℕ → ℝ) (hz : ∀ j, Tendsto (z j) atTop atTop)
    (htail : ∀ k, ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, ∀ᶠ n in atTop,
      fluctuationScale μ S (z j n)*μ.real {x | dyadicCut k*z j n < |S x|} < δ)
    (bad : ℕ → ℕ → ℝ) {δ : ℝ}
    (hbad : ¬ ∀ᶠ j in atTop, ∀ᶠ n in atTop, bad j n < δ) :
    ∃ j n : ℕ → ℕ, Tendsto j atTop atTop ∧
      IsGaussianSequence μ S (fun i => z (j i) (n i)) ∧
      (∀ i, δ ≤ bad (j i) (n i)) := by
  classical
  have hbad' : ∀ J, ∃ j, J ≤ j ∧ ∀ N, ∃ n, N ≤ n ∧ δ ≤ bad j n := by
    simpa only [eventually_atTop,not_exists,not_forall,Classical.not_imp,not_lt,exists_prop] using hbad
  have hex (i : ℕ) : ∃ j n, i ≤ j ∧ (i:ℝ)+1 ≤ z j n ∧ δ ≤ bad j n ∧
      ∀ k ≤ i, fluctuationScale μ S (z j n)*μ.real {x | dyadicCut k*z j n < |S x|} < 1/((i:ℝ)+1) := by
    have ht : ∀ᶠ j in atTop, ∀ k : Fin (i+1), ∀ᶠ n in atTop,
        fluctuationScale μ S (z j n)*μ.real {x | dyadicCut (k:ℕ)*z j n < |S x|} < 1/((i:ℝ)+1) :=
      eventually_all.mpr (fun k => htail k _ (by positivity))
    obtain ⟨J,hJ⟩ := eventually_atTop.mp ht
    obtain ⟨j,hji,hbadj⟩ := hbad' (max i J)
    have hev : ∀ᶠ n in atTop, (i:ℝ)+1 ≤ z j n ∧ ∀ k : Fin (i+1),
        fluctuationScale μ S (z j n)*μ.real {x | dyadicCut (k:ℕ)*z j n < |S x|} < 1/((i:ℝ)+1) :=
      ((hz j).eventually_ge_atTop _).and (eventually_all.mpr (hJ j ((le_max_right ..).trans hji)))
    obtain ⟨N,hN⟩ := eventually_atTop.mp hev
    obtain ⟨n,hn,hbn⟩ := hbadj N
    refine ⟨j,n,(le_max_left ..).trans hji,(hN n hn).1,hbn,?_⟩
    intro k hk
    exact (hN n hn).2 ⟨k,by omega⟩
  choose j n hj hz0 hbadn htailn using hex
  have hjtop : Tendsto j atTop atTop := tendsto_atTop_mono hj tendsto_id
  have hztop : Tendsto (fun i => z (j i) (n i)) atTop atTop := by
    apply tendsto_atTop_mono (fun i : ℕ => (by linarith [hz0 i] : (i:ℝ) ≤ z (j i) (n i)))
    exact tendsto_natCast_atTop_atTop
  refine ⟨j,n,hjtop,?_,hbadn⟩
  apply isGaussianSequence_of_dyadic μ S _ hztop
    (Eventually.of_forall fun i => by have := hz0 i; linarith)
  intro k
  have hlim : Tendsto (fun i : ℕ => 1/((i:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    apply tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun i => mul_nonneg (fluctuationScale_nonneg μ S _) measureReal_nonneg)
  filter_upwards [eventually_ge_atTop k] with i hi
  exact (htailn i k hi).le

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SmallScaleGaussianMass
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma dyadic_inv_tendsto : Tendsto (fun j => (dyadicCut j)⁻¹) atTop atTop :=
  tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr
    ⟨dyadicCut_tendsto,Eventually.of_forall dyadicCut_pos⟩)

theorem small_scale_gaussian_mass_oai {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) {ρ : ℝ} (hρ : 0 < ρ) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let μ := independentConditionedPairLaw ν ℓ
    let S := commonIncrementProcess ℓ f 0
    ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ → ℝ), (∀ n, 0 < r n) → Tendsto r atTop atTop →
      ∀ (F : ℕ → ℝ) (F₀ : ℝ), 0 < F₀ → (∀ j, F₀ ≤ F j) → Tendsto F atTop (𝓝 F₀) →
      (∀ j, Tendsto (fun n => truncatedVariance μ S (dyadicCut j*r n)/truncatedVariance μ S (r n)) atTop (𝓝 (F j))) →
      ∀ b : ℝ, 0 < b → ∀ x : Lattice d, ∀ δ : ℝ, 0 < δ →
        ∀ᶠ j in atTop, ∀ᶠ n in atTop,
          (environmentLaw ν).real {ω |
            (successQuenchedKernel ℓ x (⌊fluctuationScale μ S (dyadicCut j*r n)⌋₊:ℕ) ω).real
              (medianTubeEndpoint ν ℓ hp f x ⌊fluctuationScale μ S (dyadicCut j*r n)⌋₊
                (b*r n) (ρ*(dyadicCut j*r n))) < c} < δ := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ hp
  obtain ⟨c,hc,hGaussian⟩ := gaussian_quenched_mass ν hue e f hef htrans hρ
  refine ⟨c,hc,?_⟩
  intro r hr hrinf F F₀ hF₀ hFle hFlim hF b hb x δ hδ
  let z := fun j n => dyadicCut j*r n
  let bad := fun j n => (environmentLaw ν).real {ω |
    (successQuenchedKernel ℓ x (⌊fluctuationScale μ S (z j n)⌋₊:ℕ) ω).real
      (medianTubeEndpoint ν ℓ hp f x ⌊fluctuationScale μ S (z j n)⌋₊ (b*r n) (ρ*z j n)) < c}
  change ∀ᶠ j in atTop, ∀ᶠ n in atTop, bad j n < δ
  by_contra hbad
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have htail := dyadic_profile_gaussian_tail μ S (measurable_commonIncrementProcess ℓ f 0) hne r hr F hF₀ hFle hF hFlim
  obtain ⟨j,n,hj,hGauss,hbadn⟩ := double_gaussian_selection μ S z
    (fun j => hrinf.const_mul_atTop (dyadicCut_pos j)) (fun k δ hδ => htail k hδ) bad hbad
  have hbStar : Tendsto (fun i => b/dyadicCut (j i)) atTop atTop := by
    simpa only [div_eq_mul_inv,Function.comp_apply] using (dyadic_inv_tendsto.comp hj).const_mul_atTop hb
  have hconc := hGaussian (fun i => z (j i) (n i)) hGauss (fun i => b/dyadicCut (j i)) hbStar x
  have heq (i) : (b/dyadicCut (j i))*z (j i) (n i) = b*r (n i) := by
    dsimp [z]
    field_simp [ne_of_gt (dyadicCut_pos (j i))]
  simp only [heq] at hconc
  have hconc' : Tendsto (fun i => bad (j i) (n i)) atTop (𝓝 0) := hconc
  obtain ⟨i,hi⟩ := (hconc'.eventually (gt_mem_nhds hδ)).exists
  exact (not_lt_of_ge (hbadn i)) hi

end DirectionalTransience

end

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.small_scale_gaussian_mass_oai := @OAI.DirectionalTransience.small_scale_gaussian_mass_oai
