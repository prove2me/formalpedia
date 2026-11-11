-- Prove2me | solution 1 for OAI.DirectionalTransience.clipping_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:03:09.39213+00:00
-- url     : https://prove2.me/submissions/50e1e0ff-27c2-4431-872a-be58e9d3e85e

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Definitions.Def_OAIQ242Bal006
import Theorems.Thm_OAI_DirectionalTransience_curveIncrement_short_block
import Theorems.Thm_OAI_DirectionalTransience_curvePolicy_real_tube_probability
import Theorems.Thm_OAI_DirectionalTransience_recordFluctuationScale_tendsto
import Theorems.Thm_OAI_DirectionalTransience_recordMedian_shortBlock
import Theorems.Thm_OAI_DirectionalTransience_small_scale_gaussian_mass
import Theorems.Thm_OAI_DirectionalTransience_small_scale_tail_moment
import Theorems.Thm_OAI_DirectionalTransience_successful_small_variance_bound

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

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma truncatedVariance_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : truncatedVariance μ S r ≤ truncatedVariance μ S s := by
  apply integral_mono (integrable_truncated_square μ S hS r) (integrable_truncated_square μ S hS s)
  intro x
  exact min_le_min_left _ (pow_le_pow_left₀ hr hrs 2)

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

lemma eventually_floor_horizon_covered (n : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (M : ℕ) (hM : T < (M:ℝ)*δ) :
    ∀ᶠ i in atTop, 0 < ⌊δ*n i⌋₊ ∧ ⌊T*n i⌋₊ < M*⌊δ*n i⌋₊ := by
  have hH := (tendsto_nat_floor_mul_div_atTop hδ.le).comp hn
  have hN := (tendsto_nat_floor_mul_div_atTop hT).comp hn
  have hlt := hN.eventually_lt (hH.const_mul (M:ℝ)) hM
  have hpos := (tendsto_order.mp hH).1 (δ/2) (by linarith)
  filter_upwards [hlt,hpos,hn.eventually (eventually_gt_atTop (0:ℝ))] with i hi hp hni
  change (⌊T*n i⌋₊ : ℝ)/n i < (M:ℝ)*((⌊δ*n i⌋₊ : ℝ)/n i) at hi
  change δ/2 < (⌊δ*n i⌋₊ : ℝ)/n i at hp
  have hfloor : 0 < (⌊δ*n i⌋₊ : ℝ) := (div_pos_iff_of_pos_right hni).mp (lt_trans (by linarith) hp)
  refine ⟨by exact_mod_cast hfloor,?_⟩
  rw [← mul_div_assoc] at hi
  have hc := (div_lt_div_iff_of_pos_right hni).mp hi
  exact_mod_cast hc

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstHitPairGap
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_TubePrefix
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstLayerHitRecordPrefix
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
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

lemma tubePrefix_translation {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (θ z : ℝ) (s : ℕ) :
    (fun X : Path d => fun n => X n-x) ⁻¹' TubePrefix ℓ f 0 θ z s = TubePrefix ℓ f x θ z s := by
  have he (n : ℕ) (X : Path d) : (fun k => X k-x) ∈ TubePrefixAt ℓ f 0 θ z s n ↔
      X ∈ TubePrefixAt ℓ f x θ z s n := by
    simp only [TubePrefixAt,Set.mem_inter_iff,HitAt,Set.mem_ofPred_eq,Strip,Upper,
      dot_realPosition_sub,sub_zero]
    have hz : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot,realPosition]
    rw [hz]
    constructor
    · rintro ⟨⟨hn,hi⟩,hp⟩
      refine ⟨⟨by linarith,fun i hin => ?_⟩,hp⟩
      have hh := hi i hin
      exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
    · rintro ⟨⟨hn,hi⟩,hp⟩
      refine ⟨⟨by linarith,fun i hin => ?_⟩,hp⟩
      have hh := hi i hin
      exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
  ext X
  simp only [Set.mem_preimage,TubePrefix,Set.mem_iUnion,he]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_RecordIndexPrefixHeight
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
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

lemma tubePrefix_zero_of_initial {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (θ z : ℝ) (hz : 0 ≤ z) (X : Path d) (h0 : X 0=x) :
    X ∈ TubePrefix ℓ f x θ z 0 := by
  apply Set.mem_iUnion.mpr
  refine ⟨0,⟨⟨?_,fun i hi => by omega⟩,?_⟩⟩
  · simpa only [Upper,Set.mem_ofPred_eq,Nat.cast_zero,add_zero,h0] using le_rfl
  · intro j hj
    have hj0 : j=0 := by omega
    subst j
    refine ⟨0,le_rfl,by simp [RecordOrZeroPrefix],?_⟩
    simpa [h0,signedCoordinate] using hz

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_EndpointPrefix
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_NonCollapsedSums
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
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
lemma dyadicCut_le_one (j : ℕ) : dyadicCut j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
lemma dyadicCut_antitone : Antitone dyadicCut := by
  intro i j hij
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
lemma dyadicCut_tendsto : Tendsto dyadicCut atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma variance_ratio_unit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    truncatedVariance μ S (a*r)/truncatedVariance μ S r ∈ Icc (0:ℝ) 1 := by
  have hp := truncatedVariance_pos μ S hS hne hr
  constructor
  · exact div_nonneg (truncatedVariance_nonneg _ _ _) hp.le
  · rw [div_le_one hp]
    apply truncatedVariance_mono μ S hS (mul_nonneg ha hr.le)
    nlinarith

lemma exists_dyadic_variance_profile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) :
    ∃ (ns : ℕ → ℕ) (F : ℕ → ℝ) (F₀ : ℝ), StrictMono ns ∧
      (∀ j, Tendsto (fun n => truncatedVariance μ S (dyadicCut j*r (ns n))/truncatedVariance μ S (r (ns n))) atTop (𝓝 (F j))) ∧
      (∀ j, F j ∈ Icc (0:ℝ) 1) ∧ F 0 = 1 ∧ Antitone F ∧
      F₀ ∈ Icc (0:ℝ) 1 ∧ Tendsto F atTop (𝓝 F₀) ∧ (∀ j, F₀ ≤ F j) := by
  let R : ℕ → ℕ → Icc (0:ℝ) 1 := fun n j =>
    ⟨truncatedVariance μ S (dyadicCut j*r n)/truncatedVariance μ S (r n),
      variance_ratio_unit μ S hS hne (hr n) (dyadicCut_pos j).le (dyadicCut_le_one j)⟩
  obtain ⟨f,ns,hns,hlim⟩ := CompactSpace.tendsto_subseq R
  let F := fun j => (f j:ℝ)
  have hF (j) : Tendsto (fun n => truncatedVariance μ S (dyadicCut j*r (ns n))/truncatedVariance μ S (r (ns n))) atTop (𝓝 (F j)) :=
    continuous_subtype_val.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hlim) j)
  have hbounds (j) : F j ∈ Icc (0:ℝ) 1 := (f j).property
  have hFone : F 0 = 1 := by
    have heq : (fun n => truncatedVariance μ S (dyadicCut 0*r (ns n))/truncatedVariance μ S (r (ns n))) = fun _ => (1:ℝ) := by
      funext n
      simp only [dyadicCut,pow_zero,one_mul]
      exact div_self (ne_of_gt (truncatedVariance_pos μ S hS hne (hr (ns n))))
    exact tendsto_nhds_unique (heq ▸ hF 0) tendsto_const_nhds
  have hanti : Antitone F := by
    intro i j hij
    apply le_of_tendsto_of_tendsto (hF j) (hF i)
    exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
      (truncatedVariance_mono μ S hS (mul_nonneg (dyadicCut_pos j).le (hr (ns n)).le)
        (mul_le_mul_of_nonneg_right (dyadicCut_antitone hij) (hr (ns n)).le))
      (truncatedVariance_nonneg μ S _)
  have hb : BddBelow (range F) := ⟨0,fun x ⟨j,hj⟩ => hj ▸ (hbounds j).1⟩
  have hlimF : Tendsto F atTop (𝓝 (⨅ j, F j)) := tendsto_atTop_ciInf hanti hb
  have hinf0 : 0 ≤ ⨅ j, F j := le_ciInf (fun j => (hbounds j).1)
  have hinfj (j) : (⨅ i, F i) ≤ F j := ciInf_le hb j
  exact ⟨ns,F,⨅ j, F j,hns,hF,hbounds,hFone,hanti,⟨hinf0,(hinfj 0).trans (hbounds 0).2⟩,hlimF,hinfj⟩

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

lemma medianDeviation_tail {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) (z : ℝ) :
    {X | z < medianDeviation ℓ f b H X} = MedianTubeFailure ℓ f b H z := by
  ext X
  induction H with
  | zero => simp [medianDeviation,MedianTubeFailure]
  | succ H ih =>
    change z < max _ _ ↔ ∃ j ≤ H+1, z < _
    change z < medianDeviation ℓ f b H X ↔ ∃ j ≤ H, z < _ at ih
    rw [lt_max_iff,ih]
    constructor
    · rintro (⟨j,hj,h⟩ | h)
      · exact ⟨j,by omega,h⟩
      · exact ⟨H+1,le_rfl,h⟩
    · rintro ⟨j,hj,h⟩
      by_cases he : j = H+1
      · exact Or.inr (he ▸ h)
      · exact Or.inl ⟨j,by omega,h⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurveWordDisjoint
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurveEndpointLaw
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma medianDeviation_le_iff {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) (X : Path d) (B : ℝ) :
    medianDeviation ℓ f b H X ≤ B ↔
      ∀ j ≤ H, |signedCoordinate f (recordIndexPosition ℓ j X)-b j| ≤ B := by
  rw [← not_lt]
  change X ∉ {X | B < medianDeviation ℓ f b H X} ↔ _
  rw [medianDeviation_tail]
  simp [MedianTubeFailure]

lemma curvePrefix_ae_eq {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    CurvePrefix (realPosition (step e)) f x b B H =ᵐ[quenchedKernel (ω,x)]
      (Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∩
      {X | medianDeviation (realPosition (step e)) f b H (fun j => X j-x) ≤ B} : Set (Path d)) := by
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  apply propext
  change X ∈ (CurvePrefix (realPosition (step e)) f x b B H : Set (Path d)) ↔ X ∈ (Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∩
      {X | medianDeviation (realPosition (step e)) f b H (fun j => X j-x) ≤ B} : Set (Path d))
  rw [curvePrefix_iff e f x b B hH X h0 hnn,Set.mem_inter_iff,Set.mem_ofPred_eq,
    medianDeviation_le_iff]

lemma curveEndpoint_eq_map {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    curveEndpoint (realPosition (step e)) f x b B H ω =
      ((quenchedKernel (ω,x)).restrict (CurvePrefix (realPosition (step e)) f x b B H)).map
        (fun X => x+recordIndexPosition (realPosition (step e)) H (fun j => X j-x)) := by
  let ℓ := realPosition (step e)
  let Y := fun X : Path d => x+recordIndexPosition ℓ H (fun j => X j-x)
  have hY : Measurable Y := (measurable_const.add
    ((measurable_recordIndexPosition ℓ H).comp (by fun_prop)))
  ext U hU
  rw [curveEndpoint_apply,Measure.map_apply hY hU,Measure.restrict_apply (hY hU)]
  change (∑' n, quenchedKernel (ω,x) ((fun X => X n) ⁻¹' U ∩ CurvePrefixAt ℓ f x b B H n)) =
    quenchedKernel (ω,x) (Y ⁻¹' U ∩ ⋃ n, CurvePrefixAt ℓ f x b B H n)
  rw [Set.inter_iUnion,measure_iUnion]
  · apply tsum_congr; intro n
    apply measure_congr
    filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
    apply propext
    have he (hX : X ∈ CurvePrefixAt ℓ f x b B H n) : Y X = X n := by
      dsimp [Y]
      rw [coordinate_hitAt_record e x X h0 hnn hH hX.1]
      abel
    constructor
    · rintro ⟨hu,hn⟩
      exact ⟨by simpa only [Set.mem_preimage,he hn] using hu,hn⟩
    · rintro ⟨hu,hn⟩
      exact ⟨by simpa only [Set.mem_preimage,he hn] using hu,hn⟩
  · intro n m hnm
    exact (curvePrefixAt_disjoint ℓ f x b B H hnm).mono Set.inter_subset_right Set.inter_subset_right
  · intro n
    exact (hY hU).inter (measurableSet_curvePrefixAt ℓ f x b B H n)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma conditional_selection_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Set Ω) (hN : MeasurableSet N)
    (hμN : μ N ≠ 0) (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G)
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hF0 : ∀ x, 0 ≤ F x) (hFB : ∀ x ∈ N, F x ≤ B)
    (hG0 : ∀ x, 0 ≤ G x) (hGB : ∀ x, G x ≤ B)
    (hGN : ∀ x ∉ N, G x = B) (hFG : ∀ x ∈ N, F x ≤ a+G x) :
    (∫ x, F x ∂μ[|N]) ≤ a+2*∫ x, G x ∂μ := by
  have := cond_isProbabilityMeasure hμN
  have hFi : Integrable F μ[|N] := Integrable.of_bound hF.aestronglyMeasurable B (by
    filter_upwards [ae_cond_mem hN] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hF0 x)] using hFB x hx)
  have hGi : Integrable G μ := Integrable.of_bound hG.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hG0 x)] using hGB x)
  have hGci : Integrable G μ[|N] := Integrable.of_bound hG.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hG0 x)] using hGB x)
  have hI0 : 0 ≤ ∫ x, G x ∂μ := integral_nonneg hG0
  by_cases hq : 1/2 ≤ μ.real N
  · have hq0 : 0 < μ.real N := by linarith
    have hinv : (μ.real N)⁻¹ ≤ (2:ℝ) := by
      rw [inv_eq_one_div,div_le_iff₀ hq0]
      linarith
    have hcondG : (∫ x, G x ∂μ[|N]) ≤ 2*∫ x, G x ∂μ := by
      rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
      calc
        _ ≤ (μ N).toReal⁻¹*(∫ x, G x ∂μ) := mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hGi (Eventually.of_forall hG0)) (by positivity)
        _ ≤ 2*(∫ x, G x ∂μ) := mul_le_mul_of_nonneg_right hinv hI0
    have hh := integral_mono_ae hFi ((integrable_const a).add hGci)
      (by filter_upwards [ae_cond_mem hN] with x hx; exact hFG x hx)
    change (∫ x, F x ∂μ[|N]) ≤ (∫ x, a+G x ∂μ[|N]) at hh
    rw [integral_add (integrable_const a) hGci] at hh
    simp only [integral_const,probReal_univ,one_smul] at hh
    linarith
  · have hIF : (∫ x, F x ∂μ[|N]) ≤ B := by
      simpa only [integral_const,probReal_univ,one_smul] using
        integral_mono_ae hFi (integrable_const B)
          (by filter_upwards [ae_cond_mem hN] with x hx; exact hFB x hx)
    have hIG : B*μ.real Nᶜ ≤ ∫ x, G x ∂μ := by
      calc
        _ = ∫ x in Nᶜ, G x ∂μ := by
          rw [setIntegral_congr_fun hN.compl (fun x hx => hGN x hx)]
          simp [mul_comm]
        _ ≤ _ := setIntegral_le_integral hGi (Eventually.of_forall hG0)
    rw [measureReal_compl hN,probReal_univ] at hIG
    have hq' : μ.real N < 1/2 := lt_of_not_ge hq
    nlinarith

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SelectedEndpointMoment
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
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

lemma capped_selection_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W Y : Ω → ℝ)
    (hW : Measurable W) (hY : Measurable Y) {b A B : ℝ}
    (hA : 0 ≤ A) (hAB : A < B) (hW0 : ∀ x, 0 ≤ W x)
    (hYW : ∀ x, |Y x-b| ≤ W x) (hN : μ {x | W x ≤ B} ≠ 0) :
    (∫ x, (Y x-b)^2 ∂μ[|{x | W x ≤ B}]) ≤ A^2+
      2*∫ x, if A < W x then (min (W x) B)^2 else 0 ∂μ := by
  let N := {x | W x ≤ B}
  let F := fun x => (Y x-b)^2
  let G := fun x => if A < W x then (min (W x) B)^2 else 0
  have hB : 0 ≤ B := hA.trans hAB.le
  apply conditional_selection_moment μ N (measurableSet_le hW measurable_const) hN F G
    (by fun_prop) (by exact Measurable.ite (measurableSet_lt measurable_const hW) (by fun_prop) measurable_const)
    (sq_nonneg A) (sq_nonneg B)
  · intro x; exact sq_nonneg _
  · intro x hx
    have hh := (hYW x).trans hx
    nlinarith [sq_abs (Y x-b),sq_nonneg (B-|Y x-b|),abs_nonneg (Y x-b)]
  · intro x; dsimp [G]; split_ifs <;> positivity
  · intro x
    dsimp [G]
    split_ifs
    · have hm0 : 0 ≤ min (W x) B := le_min (hW0 x) hB
      have hmB : min (W x) B ≤ B := min_le_right _ _
      nlinarith
    · positivity
  · intro x hx
    have hx' : B < W x := lt_of_not_ge hx
    simp [G,hAB.trans hx',min_eq_right hx'.le]
  · intro x hx
    dsimp [F,G]
    by_cases hax : A < W x
    · rw [ite_eq_left hax,min_eq_left hx]
      have hh := hYW x
      nlinarith [sq_abs (Y x-b),sq_nonneg (W x-|Y x-b|),abs_nonneg (Y x-b),sq_nonneg A]
    · rw [ite_eq_right hax]
      have hh := (hYW x).trans (le_of_not_gt hax)
      nlinarith [sq_abs (Y x-b),sq_nonneg (A-|Y x-b|),abs_nonneg (Y x-b)]

lemma conditional_bounded_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E) (hμE : μ E ≠ 0)
    (hμEtop : μ E ≠ ∞) (Y : Ω → ℝ) (hY : Measurable Y) {b ρ : ℝ}
    (hρ : 0 ≤ ρ) (hbound : ∀ x ∈ E, |Y x-b| ≤ ρ) :
    (∫ x, (Y x-b)^2 ∂μ[|E]) ≤ ρ^2 := by
  let : IsProbabilityMeasure μ[|E] := ⟨by simp [ProbabilityTheory.cond,Measure.smul_apply,
    ENNReal.inv_mul_cancel hμE hμEtop]⟩
  have hb : ∀ᵐ x ∂μ[|E], (Y x-b)^2 ≤ ρ^2 := by
    filter_upwards [ae_cond_mem hE] with x hx
    have hh := hbound x hx
    nlinarith [sq_abs (Y x-b),sq_nonneg (ρ-|Y x-b|),abs_nonneg (Y x-b)]
  have hi : Integrable (fun x => (Y x-b)^2) μ[|E] :=
    Integrable.of_bound (by fun_prop) (ρ^2) (hb.mono fun x hx => by simpa using hx)
  simpa using integral_mono_ae hi (integrable_const (ρ^2)) hb

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma selectedEndpointLaw_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W Y : Ω → ℝ)
    (hW : Measurable W) (hY : Measurable Y) (E : Set Ω) (hE : MeasurableSet E)
    {b A B ρ : ℝ} (hA : 0 ≤ A) (hAB : A < B) (hρ : 0 ≤ ρ)
    (hW0 : ∀ x, 0 ≤ W x) (hYW : ∀ x, |Y x-b| ≤ W x)
    (failure strict : Prop) [Decidable failure] [Decidable strict]
    (hN : μ {x | W x ≤ B} ≠ 0) (hμE : strict → μ E ≠ 0)
    (hbound : ∀ x ∈ E, |Y x-b| ≤ ρ) :
    (∫ u, (u-b)^2 ∂selectedEndpointLaw μ {x | W x ≤ B} E Y b failure strict) ≤
      ρ^2+(if strict then 0 else A^2)+
        2*(∫ x, if A < W x then (min (W x) B)^2 else 0 ∂μ) := by
  have htail : 0 ≤ ∫ x, if A < W x then (min (W x) B)^2 else 0 ∂μ :=
    integral_nonneg fun x => by split_ifs <;> positivity
  by_cases hf : failure
  · simp only [selectedEndpointLaw,ite_eq_left hf,integral_dirac,sub_self,zero_pow (by decide : 2 ≠ 0)]
    split_ifs <;> positivity
  simp only [selectedEndpointLaw,ite_eq_right hf]
  by_cases hs : strict
  · simp only [ite_eq_left hs]
    rw [integral_map hY.aemeasurable (by fun_prop)]
    have hh := conditional_bounded_square μ E hE (hμE hs) (measure_ne_top _ _) Y hY hρ hbound
    linarith
  · simp only [ite_eq_right hs]
    rw [integral_map hY.aemeasurable (by fun_prop)]
    have hh := capped_selection_moment μ W Y hW hY hA hAB hW0 hYW hN
    nlinarith [sq_nonneg ρ]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_SelectedKernelMap
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
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

lemma normalizeFinite_map {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) (Y : Ω → A) (hY : Measurable Y) :
    normalizeFinite (μ.map Y) = (normalizeFinite μ).map Y := by
  simp only [normalizeFinite,Measure.map_apply hY MeasurableSet.univ,Set.preimage_univ,
    Measure.map_smul]

lemma normalizeFinite_restrict {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Set Ω) : normalizeFinite (μ.restrict N) = μ[|N] := by
  simp only [normalizeFinite,Measure.restrict_apply_univ,ProbabilityTheory.cond]

lemma selectedFiniteKernel_map_eq {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure Ω) (N : Set Ω) (Z : Ω → A) (hZ : Measurable Z)
    (E : Set A) (hE : MeasurableSet E) (Y : A → ℝ) (hY : Measurable Y)
    (dummy : A) (failure strict : Prop) [Decidable failure] [Decidable strict] :
    (selectedFiniteKernel ((μ.restrict N).map Z) E dummy failure strict).map Y =
      selectedEndpointLaw μ N (N ∩ Z ⁻¹' E) (Y ∘ Z) (Y dummy) failure strict := by
  by_cases hf : failure
  · simp only [selectedFiniteKernel,selectedEndpointLaw,ite_eq_left hf,Measure.map_dirac' hY]
  simp only [selectedFiniteKernel,selectedEndpointLaw,ite_eq_right hf]
  by_cases hs : strict
  · simp only [ite_eq_left hs]
    rw [Measure.restrict_map hZ hE,Measure.restrict_restrict (hZ hE)]
    rw [Set.inter_comm (Z ⁻¹' E) N,normalizeFinite_map _ Z hZ,
      normalizeFinite_restrict,Measure.map_map hY hZ]
  · simp only [ite_eq_right hs]
    rw [normalizeFinite_map _ Z hZ,normalizeFinite_restrict,Measure.map_map hY hZ]

lemma selectedEndpointLaw_cond {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (C N E : Set Ω)
    (hC : MeasurableSet C) (hN : MeasurableSet N) (hE : MeasurableSet E)
    (Y : Ω → ℝ) (b : ℝ) (failure strict : Prop) [Decidable failure] [Decidable strict] :
    selectedEndpointLaw μ[|C] N E Y b failure strict =
      selectedEndpointLaw μ (C ∩ N) (C ∩ E) Y b failure strict := by
  unfold selectedEndpointLaw
  split_ifs with hf hs
  · rfl
  · rw [cond_cond_eq_cond_inter hC hE]
  · rw [cond_cond_eq_cond_inter hC hN]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyLateral
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma curveIncrement_eq_success_map {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    curveIncrement (realPosition (step e)) f x b B H ω =
      ((quenchedKernel (ω,x)).restrict
        (Cross (realPosition (step e)) x H ∩
          {X | medianDeviation (realPosition (step e)) f b H (fun j => X j-x) ≤ B})).map
        (fun X => recordIndexPosition (realPosition (step e)) H (fun j => X j-x)) := by
  rw [curveIncrement,curveEndpoint_eq_map e f x b B hH ω,Measure.map_map]
  · simp only [Function.comp_def,add_sub_cancel_left]
    congr 1
    apply Measure.restrict_congr_set
    simpa only [cross_eq_hit] using curvePrefix_ae_eq e f x b B hH ω
  · exact measurable_of_countable _
  · exact measurable_const.add ((measurable_recordIndexPosition _ _).comp (by fun_prop))

lemma curvePolicy_lateral {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (E : Set (Lattice d))
    (δ α : ℝ≥0∞) (dummy : Lattice d) (ω : Environment d) :
    (curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω).map (signedCoordinate f) =
      selectedEndpointLaw ((quenchedKernel (ω,x))[|Cross (realPosition (step e)) x H])
        {X | medianDeviation (realPosition (step e)) f b H (fun j => X j-x) ≤ B}
        ({X | medianDeviation (realPosition (step e)) f b H (fun j => X j-x) ≤ B} ∩
          (fun X => recordIndexPosition (realPosition (step e)) H (fun j => X j-x)) ⁻¹' E)
        (fun X => signedCoordinate f (recordIndexPosition (realPosition (step e)) H (fun j => X j-x)))
        (signedCoordinate f dummy)
        (curveIncrement (realPosition (step e)) f x b B H ω Set.univ < δ)
        (α * crossingQuenched (realPosition (step e)) x H ω ≤
          curveIncrement (realPosition (step e)) f x b B H ω E) := by
  let ℓ := realPosition (step e)
  let N := {X : Path d | medianDeviation ℓ f b H (fun j => X j-x) ≤ B}
  let Z := fun X : Path d => recordIndexPosition ℓ H (fun j => X j-x)
  have hZ : Measurable Z := (measurable_recordIndexPosition _ _).comp (by fun_prop)
  have hN : MeasurableSet N := measurableSet_le
    ((measurable_medianDeviation ℓ f b H).comp (by fun_prop)) measurable_const
  rw [selectedEndpointLaw_cond _ _ _ _ (measurableSet_cross ℓ x H) hN
    (hN.inter (hZ E.to_countable.measurableSet))]
  change (selectedFiniteKernel _ E dummy _ _).map (signedCoordinate f) = _
  conv_lhs => arg 2; arg 1; rw [curveIncrement_eq_success_map e f x b B hH ω]
  rw [selectedFiniteKernel_map_eq _ _ _ hZ E E.to_countable.measurableSet
    (signedCoordinate f) (measurable_of_countable _) dummy]
  simp only [Set.inter_assoc,Function.comp_def]
  rfl

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma selectedFiniteKernel_supported {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (D : Measure α) (E : Set α) (dummy : α) (failure strict : Prop)
    [Decidable failure] [Decidable strict] (P : α → Prop)
    (hd : P dummy) (hD : ∀ᵐ u ∂D, P u) :
    ∀ᵐ u ∂selectedFiniteKernel D E dummy failure strict, P u := by
  by_cases hf : failure
  · simp only [selectedFiniteKernel,ite_eq_left hf,ae_dirac_eq,Filter.eventually_pure]
    exact hd
  simp only [selectedFiniteKernel,ite_eq_right hf,normalizeFinite]
  rw [ae_iff,Measure.smul_apply,smul_eq_mul]
  have he : ∀ᵐ u ∂(if strict then D.restrict E else D), P u := by
    split_ifs
    · exact hD.filter_mono (ae_mono Measure.restrict_le_self)
    · exact hD
  rw [ae_iff.mp he,mul_zero]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curveIncrement_lateral_bound {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    ∀ᵐ u ∂curveIncrement (realPosition (step e)) f x b B H ω,
      |signedCoordinate f u-b H| ≤ B := by
  have hm : Measurable (fun X : Path d => recordIndexPosition (realPosition (step e)) H (fun j => X j-x)) :=
    (measurable_recordIndexPosition _ _).comp (by fun_prop)
  rw [curveIncrement_eq_success_map e f x b B hH ω,
    ae_map_iff hm.aemeasurable (Set.to_countable _ |>.measurableSet)]
  filter_upwards [ae_restrict_mem (measurableSet_cross _ _ _ |>.inter
    (measurableSet_le ((measurable_medianDeviation _ f b H).comp (by fun_prop)) measurable_const))]
    with X hX
  exact (medianDeviation_le_iff _ f b H _ B).mp hX.2 H le_rfl

lemma curvePolicy_lateral_bound {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) (δ α : ℝ≥0∞) (dummy : Lattice d)
    (hd : signedCoordinate f dummy = b H) (ω : Environment d) :
    ∀ᵐ u ∂curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω,
      |signedCoordinate f u-b H| ≤ B :=
  selectedFiniteKernel_supported _ _ _ _ _ _ (by simpa [hd] using hB)
    (curveIncrement_lateral_bound e f x b B hH ω)

lemma curvePolicy_square_integrable {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) (ω : Environment d) :
    Integrable (fun u => (signedCoordinate f u-b H)^2)
      (curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω) := by
  have := curvePolicy_probability (realPosition (step e)) f x b B H E hδ hα dummy ω
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (B^2)
  filter_upwards [curvePolicy_lateral_bound e f x b hB hH E δ α dummy hd ω] with u hu
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (signedCoordinate f u-b H))]
  nlinarith [sq_abs (signedCoordinate f u-b H),sq_nonneg (B-|signedCoordinate f u-b H|),
    abs_nonneg (signedCoordinate f u-b H)]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightTubeWindow
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
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

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_GaussianQuenchedTube
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma measurableSet_medianTubeEndpoint {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d)
    (x : Lattice d) (H : ℕ) (L R : ℝ) : MeasurableSet (medianTubeEndpoint ν ℓ hp f x H L R) := by
  have hm (j : ℕ) : Measurable (fun X : Path d => signedCoordinate f
      (recordIndexPosition ℓ j (fun k => X k-x))-(recordMedian ν ℓ hp f j:ℝ)) :=
    (((measurable_of_countable (signedCoordinate f)).comp
      (measurable_recordIndexPosition ℓ j)).comp (by fun_prop)).sub_const _
  exact measurableSet_heightTubeEndpointEvent _ hm H L R

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_QuenchedSuccessComparison
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

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BindIntegral
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
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

lemma integral_bind_nonneg_of_integrable {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    (μ : Measure Ω) (Q : Ω → Measure G) (hQ : Measurable Q)
    (F : G → ℝ) (hF : Measurable F) (h0 : ∀ u, 0 ≤ F u)
    (hi : ∀ ω, Integrable F (Q ω)) :
    (∫ u, F u ∂μ.bind Q) = ∫ ω, ∫ u, F u ∂Q ω ∂μ := by
  have he (ω : Ω) : (∫ u, F u ∂Q ω) = (∫⁻ u, ENNReal.ofReal (F u) ∂Q ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hF.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hF.aestronglyMeasurable,
    Measure.lintegral_bind hQ.aemeasurable hF.ennreal_ofReal.aemeasurable]
  simp_rw [he]
  symm
  apply integral_toReal
  · exact ((Measure.measurable_lintegral (hF.ennreal_ofReal)).comp hQ).aemeasurable
  · exact Eventually.of_forall fun ω => (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).mp (hi ω).hasFiniteIntegral

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurveShortBlock
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.successQuenchedKernel_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma curvePolicy_moment {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) {A B ρ : ℝ} (hA : 0 ≤ A) (hAB : A < B) (hρ : 0 ≤ ρ)
    {H : ℕ} (hH : 0 < H) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) (ω : Environment d)
    (ha : crossingQuenched (realPosition (step e)) x H ω ≠ 0) :
    let ℓ := realPosition (step e)
    let E := {u : Lattice d | |signedCoordinate f u-b H| ≤ ρ}
    let W := fun X : Path d => medianDeviation ℓ f b H (fun j => X j-x)
    let μ := (quenchedKernel (ω,x))[|Cross ℓ x H]
    (∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy ℓ f x b B H E δ α dummy ω) ≤
      ρ^2+(if α*crossingQuenched ℓ x H ω ≤ curveIncrement ℓ f x b B H ω E then 0 else A^2)+
        2*(∫ X, if A < W X then (min (W X) B)^2 else 0 ∂μ) := by
  let ℓ := realPosition (step e)
  let E := {u : Lattice d | |signedCoordinate f u-b H| ≤ ρ}
  let W := fun X : Path d => medianDeviation ℓ f b H (fun j => X j-x)
  let Z := fun X : Path d => recordIndexPosition ℓ H (fun j => X j-x)
  let Y := fun X : Path d => signedCoordinate f (Z X)
  let N := {X | W X ≤ B}
  let μ := (quenchedKernel (ω,x))[|Cross ℓ x H]
  have hZ : Measurable Z := (measurable_recordIndexPosition ℓ H).comp (by fun_prop)
  have hW : Measurable W := (measurable_medianDeviation ℓ f b H).comp (by fun_prop)
  have hY : Measurable Y := (measurable_of_countable (signedCoordinate f)).comp hZ
  have hN : MeasurableSet N := measurableSet_le hW measurable_const
  have hEN : MeasurableSet (N ∩ Z ⁻¹' E) := hN.inter (hZ E.to_countable.measurableSet)
  let : IsProbabilityMeasure μ := cond_isProbabilityMeasure ha
  have hNval : μ N = (crossingQuenched ℓ x H ω)⁻¹ *
      curveIncrement ℓ f x b B H ω Set.univ := by
    rw [curveIncrement_eq_success_map e f x b B hH ω,Measure.map_apply hZ MeasurableSet.univ,
      Set.preimage_univ,Measure.restrict_apply_univ]
    exact cond_apply (measurableSet_cross ℓ x H) _ _
  have hEval : μ (N ∩ Z ⁻¹' E) = (crossingQuenched ℓ x H ω)⁻¹ *
      curveIncrement ℓ f x b B H ω E := by
    rw [curveIncrement_eq_success_map e f x b B hH ω,Measure.map_apply hZ E.to_countable.measurableSet,
      Measure.restrict_apply (hZ E.to_countable.measurableSet)]
    rw [show Z ⁻¹' E ∩ (Cross ℓ x H ∩ N) = Cross ℓ x H ∩ (N ∩ Z ⁻¹' E) by ext X; simp only [Set.mem_inter_iff]; tauto]
    exact cond_apply (measurableSet_cross ℓ x H) _ _
  have htail : 0 ≤ ∫ X, if A < W X then (min (W X) B)^2 else 0 ∂μ :=
    integral_nonneg fun X => by split_ifs <;> positivity
  by_cases hf : curveIncrement ℓ f x b B H ω Set.univ < δ
  · change (∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy ℓ f x b B H E δ α dummy ω) ≤ _
    simp only [curvePolicy,selectedFiniteKernel,ite_eq_left hf,integral_dirac,hd,sub_self,
      zero_pow (by decide : 2 ≠ 0)]
    split_ifs <;> positivity
  have hNZ : μ N ≠ 0 := by
    rw [hNval]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
      (ne_of_gt (hδ.trans_le (not_lt.mp hf)))
  have hEZ (hs : α*crossingQuenched ℓ x H ω ≤ curveIncrement ℓ f x b B H ω E) :
      μ (N ∩ Z ⁻¹' E) ≠ 0 := by
    rw [hEval]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
      (ne_of_gt ((ENNReal.mul_pos hα.ne' ha).trans_le hs))
  have hh := selectedEndpointLaw_moment μ W Y hW hY (N ∩ Z ⁻¹' E) hEN hA hAB hρ
    (fun X => medianDeviation_nonneg ℓ f b H _) (fun X =>
      (medianDeviation_le_iff ℓ f b H (fun j => X j-x) (W X)).mp le_rfl H le_rfl)
    (curveIncrement ℓ f x b B H ω Set.univ < δ)
    (α*crossingQuenched ℓ x H ω ≤ curveIncrement ℓ f x b B H ω E)
    hNZ hEZ (fun X hX => hX.2)
  rw [← hd] at hh
  rw [← curvePolicy_lateral e f x b B hH E δ α dummy ω] at hh
  rw [integral_map (measurable_of_countable (signedCoordinate f)).aemeasurable (by fun_prop)] at hh
  simpa only [hd] using hh

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SuccessfulAverageBind
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma successfulAverage_eq_bind {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) (H : ℝ) :
    successfulAverage ν ℓ H = (environmentLaw ν).bind (successQuenchedKernel ℓ 0 H) := by
  apply Measure.ext
  intro A hA
  rw [successfulAverage_apply ν ℓ H A hA,Measure.bind_apply hA (Kernel.measurable _).aemeasurable]
  apply lintegral_congr
  intro ω
  exact (successQuenchedKernel_apply ℓ 0 H ω A hA).symm

lemma successfulAverage_integral {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) (H : ℝ)
    (F : Path d → ℝ) (hF : Measurable F) (h0 : ∀ X, 0 ≤ F X)
    (hi : ∀ ω, Integrable F (successQuenchedKernel ℓ 0 H ω)) :
    (∫ X, F X ∂successfulAverage ν ℓ H) =
      ∫ ω, ∫ X, F X ∂successQuenchedKernel ℓ 0 H ω ∂environmentLaw ν := by
  rw [successfulAverage_eq_bind]
  exact integral_bind_nonneg_of_integrable _ _ (Kernel.measurable _) F hF h0 hi

lemma crossingQuenched_positive_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x H, crossingQuenched ℓ x H ω ≠ 0 := by
  filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans,
    quenched_noDrop_subset_cross_ae ν ℓ htrans] with ω hp hs x H
  exact ne_of_gt ((hp x).trans_le (measure_mono_ae (hs x H)))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_CurvePolicyKernel
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.successQuenchedKernel_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma curvePolicy_average_toMeasure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) :
    (curvePolicy_average ν ℓ f b B hH E hδ hα dummy).toMeasure =
      (environmentLaw ν).bind (curvePolicy ℓ f 0 b B H E δ α dummy) := by
  have := curvePolicy_average_probability ν ℓ f b B hH E hδ hα dummy
  exact Measure.toPMF_toMeasure _

lemma curvePolicy_average_square {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) :
    (∫ u, (signedCoordinate f u-b H)^2 ∂(curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy).toMeasure) =
      ∫ ω, ∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy (realPosition (step e)) f 0 b B H E δ α dummy ω ∂environmentLaw ν := by
  rw [curvePolicy_average_toMeasure]
  exact integral_bind_nonneg_of_integrable _ _
    ((curvePolicy_rows _ f 0 b B hH E δ α dummy).mono (rowSigma_le _) le_rfl)
    _ (measurable_of_countable _) (fun u => sq_nonneg _) (curvePolicy_square_integrable e f 0 b hB hH E hδ hα dummy hd)

lemma curvePolicy_square_outer_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (x : Lattice d) (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    {H : ℕ} (hH : 0 < H) (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) :
    Integrable (fun ω => ∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω)
      (environmentLaw ν) := by
  let Q := curvePolicyKernel (realPosition (step e)) f x b B hH E δ α dummy
  have hm : Measurable (fun ω => ∫ u, (signedCoordinate f u-b H)^2 ∂Q ω) :=
    (measurable_of_countable _).stronglyMeasurable.integral_kernel.measurable
  apply Integrable.of_bound hm.aestronglyMeasurable (B^2)
  apply Eventually.of_forall
  intro ω
  have := curvePolicy_probability (realPosition (step e)) f x b B H E hδ hα dummy ω
  have hi := curvePolicy_square_integrable e f x b hB hH E hδ hα dummy hd ω
  have hh : (∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω) ≤ B^2 := by
    have hb : ∀ᵐ u ∂curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω,
        (signedCoordinate f u-b H)^2 ≤ B^2 := by
      filter_upwards [curvePolicy_lateral_bound e f x b hB hH E δ α dummy hd ω] with u hu
      nlinarith [sq_abs (signedCoordinate f u-b H),sq_nonneg (B-|signedCoordinate f u-b H|),abs_nonneg (signedCoordinate f u-b H)]
    simpa using integral_mono_ae hi (integrable_const (B^2)) hb
  have h0 : 0 ≤ ∫ u, (signedCoordinate f u-b H)^2 ∂Q ω := integral_nonneg (fun u => sq_nonneg (signedCoordinate f u-b H))
  rw [Real.norm_eq_abs,abs_of_nonneg h0]
  exact hh

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_KernelBoundedExpectation
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
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

lemma kernel_bounded_integral {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    (Q : Kernel Ω G) [IsFiniteKernel Q] (F : G → ℝ) (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (h0 : ∀ u, 0 ≤ F u) (hbound : ∀ u, F u ≤ B)
    (hQ : ∀ ω, Q ω Set.univ ≤ 1) :
    ∀ ω, 0 ≤ (∫ u, F u ∂Q ω) ∧ (∫ u, F u ∂Q ω) ≤ B := by
  intro ω
  have hi : Integrable F (Q ω) := Integrable.of_bound hF.aestronglyMeasurable B
    (Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs,abs_of_nonneg (h0 u)] using hbound u)
  refine ⟨integral_nonneg h0,?_⟩
  have hh := integral_mono hi (integrable_const B) (fun u => hbound u)
  rw [integral_const,smul_eq_mul] at hh
  apply hh.trans
  have hm : (Q ω).real Set.univ ≤ 1 := by
    simpa only [measureReal_def,ENNReal.toReal_one] using ENNReal.toReal_mono (by simp : (1:ℝ≥0∞) ≠ ∞) (hQ ω)
  exact mul_le_of_le_one_left hB hm

lemma integrable_kernel_bounded_integral {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Q : Kernel Ω G) [IsFiniteKernel Q]
    (F : G → ℝ) (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (h0 : ∀ u, 0 ≤ F u) (hbound : ∀ u, F u ≤ B)
    (hQ : ∀ ω, Q ω Set.univ ≤ 1) :
    Integrable (fun ω => ∫ u, F u ∂Q ω) μ := by
  apply Integrable.of_bound hF.stronglyMeasurable.integral_kernel.aestronglyMeasurable B
  exact Eventually.of_forall fun ω => by
    obtain ⟨h0',hB'⟩ := kernel_bounded_integral Q F hF hB h0 hbound hQ ω
    simpa only [Real.norm_eq_abs,abs_of_nonneg h0'] using hB'

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyAverageMoment
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma curvePolicy_average_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (b : ℕ → ℝ) {A B ρ : ℝ} (hA : 0 ≤ A) (hAB : A < B) (hρ : 0 ≤ ρ)
    {H : ℕ} (hH : 0 < H) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) :
    let ℓ := realPosition (step e)
    let E := {u : Lattice d | |signedCoordinate f u-b H| ≤ ρ}
    let W := fun X : Path d => medianDeviation ℓ f b H X
    (∫ u, (signedCoordinate f u-b H)^2 ∂(curvePolicy_average ν ℓ f b B hH E hδ hα dummy).toMeasure) ≤
      ρ^2+A^2*(environmentLaw ν).real {ω | ¬ α*crossingQuenched ℓ 0 H ω ≤ curveIncrement ℓ f 0 b B H ω E}+
        2*(∫ X, if A < W X then (min (W X) B)^2 else 0 ∂successfulAverage ν ℓ H) := by
  let ℓ := realPosition (step e)
  let E := {u : Lattice d | |signedCoordinate f u-b H| ≤ ρ}
  let W := fun X : Path d => medianDeviation ℓ f b H X
  let T := fun X : Path d => if A < W X then (min (W X) B)^2 else 0
  let S := {ω | ¬ α*crossingQuenched ℓ 0 H ω ≤ curveIncrement ℓ f 0 b B H ω E}
  have hB : 0 ≤ B := hA.trans hAB.le
  have hW : Measurable W := measurable_medianDeviation ℓ f b H
  have hT : Measurable T := Measurable.ite (measurableSet_lt measurable_const hW)
    ((hW.min measurable_const).pow_const 2) measurable_const
  have hT0 : ∀ X, 0 ≤ T X := fun X => by dsimp [T]; split_ifs <;> positivity
  have hTB : ∀ X, T X ≤ B^2 := by
    intro X
    dsimp [T]
    split_ifs
    · exact pow_le_pow_left₀ (le_min (medianDeviation_nonneg ℓ f b H X) hB) (min_le_right _ _) 2
    · positivity
  have hQ : ∀ ω, successQuenchedKernel ℓ 0 H ω Set.univ ≤ 1 := by
    intro ω
    rw [successQuenchedKernel_apply _ _ _ _ _ MeasurableSet.univ,Set.univ_inter]
    exact ENNReal.inv_mul_le_one _
  have hTi : ∀ ω, Integrable T (successQuenchedKernel ℓ 0 H ω) := fun ω =>
    Integrable.of_bound hT.aestronglyMeasurable (B^2) (Eventually.of_forall fun X => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hT0 X)] using hTB X)
  have hTo := integrable_kernel_bounded_integral (environmentLaw ν) (successQuenchedKernel ℓ 0 H)
    T hT (sq_nonneg B) hT0 hTB hQ
  have hS : MeasurableSet S := (measurableSet_le
    (measurable_const.mul (measurable_crossingQuenched ℓ 0 H))
    ((Measure.measurable_coe E.to_countable.measurableSet).comp
      ((curveIncrement_rows ℓ f 0 b B hH).mono (rowSigma_le _) le_rfl))).compl
  have hI : Integrable (S.indicator (fun _ : Environment d => A^2)) (environmentLaw ν) :=
    (integrable_const (A^2)).indicator hS
  have hi := curvePolicy_square_outer_integrable ν e f 0 b hB hH E hδ hα dummy hd
  have hh := integral_mono_ae hi (((integrable_const (ρ^2)).add hI).add (hTo.const_mul 2)) (by
    filter_upwards [crossingQuenched_positive_ae ν hue ℓ (signed_direction_unit e) htrans] with ω hω
    have hm := curvePolicy_moment e f 0 b hA hAB hρ hH hδ hα dummy hd ω (hω 0 H)
    change (∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy ℓ f 0 b B H E δ α dummy ω) ≤
      ρ^2+S.indicator (fun _ => A^2) ω+2*(∫ X, T X ∂successQuenchedKernel ℓ 0 H ω)
    simp only [sub_zero] at hm
    change (∫ u, (signedCoordinate f u-b H)^2 ∂curvePolicy ℓ f 0 b B H E δ α dummy ω) ≤
      ρ^2+(if α*crossingQuenched ℓ 0 H ω ≤ curveIncrement ℓ f 0 b B H ω E then 0 else A^2)+
        2*(∫ X, T X ∂successQuenchedKernel ℓ 0 H ω) at hm
    simpa only [Set.indicator_apply,S,Set.mem_ofPred_eq,ite_not] using hm)
  simp only [Pi.add_apply] at hh
  have ha₁ := integral_add ((integrable_const (ρ^2)).add hI) (hTo.const_mul 2)
  have ha₂ := integral_add (integrable_const (ρ^2)) hI
  simp only [Pi.add_apply] at ha₁ ha₂
  rw [ha₁,ha₂,integral_const,probReal_univ,one_smul,
    integral_const_mul,integral_indicator hS,integral_const] at hh
  change (∫ u, (signedCoordinate f u-b H)^2 ∂(curvePolicy_average ν ℓ f b B hH E hδ hα dummy).toMeasure) ≤
    ρ^2+A^2*(environmentLaw ν).real S+2*(∫ X, T X ∂successfulAverage ν ℓ H)
  rw [curvePolicy_average_square ν e f b hB hH E hδ hα dummy hd,
    successfulAverage_integral ν ℓ H T hT hT0 hTi]
  simpa only [measureReal_restrict_apply_univ,smul_eq_mul,mul_comm (A^2)] using hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicy_average_zero_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (b : ℕ → ℝ) {B : ℝ} (hB : 0 < B) {H : ℕ} (hH : 0 < H)
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) :
    let ℓ := realPosition (step e)
    let E := {u : Lattice d | |signedCoordinate f u-b H| ≤ 0}
    (∫ u, (signedCoordinate f u-b H)^2 ∂(curvePolicy_average ν ℓ f b B hH E hδ hα dummy).toMeasure) ≤
      2*(∫ X, (min (medianDeviation ℓ f b H X) B)^2 ∂successfulAverage ν ℓ H) := by
  have hm := curvePolicy_average_moment ν hue e f htrans b (A:=0) (ρ:=0)
    le_rfl hB le_rfl hH hδ hα dummy hd
  dsimp only at hm ⊢
  simp only [zero_pow (by omega : 2 ≠ 0),zero_mul,zero_add] at hm
  convert hm using 2
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with X
  split_ifs with h
  · rfl
  · have hz : medianDeviation (realPosition (step e)) f b H X=0 :=
      le_antisymm (not_lt.mp h) (medianDeviation_nonneg _ _ _ _ _)
    simp [hz,min_eq_left hB.le]
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience
lemma signedCoordinate_zsmul {d : ℕ} (e : Direction d) (a : ℤ) (x : Lattice d) :
    signedCoordinate e (a • x) = (a:ℝ)*signedCoordinate e x := by
  simp only [signedCoordinate,Pi.smul_apply,smul_eq_mul,Int.cast_mul]
  split <;> ring
lemma signedHeight_zsmul_other {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1) (a : ℤ) :
    signedHeight e (a • step f) = 0 := by
  simp [signedHeight,Pi.smul_apply,step,hef]
lemma medianDummy_height {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1) (H : ℕ) (b : ℤ) :
    signedHeight e (medianDummy e f H b) = H := by
  rw [medianDummy,signedHeight_add,signedHeight_zsmul_step,signedHeight_zsmul_other e f hef,add_zero]
lemma medianDummy_coordinate {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1) (H : ℕ) (b : ℤ) :
    signedCoordinate f (medianDummy e f H b) = b := by
  rw [medianDummy,signedCoordinate_add,signedCoordinate_zsmul,signedCoordinate_zsmul,
    signedCoordinate_step_other f e hef.symm,signedCoordinate_step_self]
  ring
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

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience
lemma cappedMoment_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hX0 : ∀ x, 0 ≤ X x) {B : ℝ} (hB : 0 < B) :
    0 ≤ cappedMoment μ X B ∧ cappedMoment μ X B ≤ B^2 := by
  rw [cappedMoment_scale μ X hB]
  have hh := cappedMoment_unit_bounds μ (fun x => X x/B) (hX.div_const B)
    (fun x => div_nonneg (hX0 x) hB.le)
  constructor
  · exact mul_nonneg (sq_nonneg B) hh.1
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hh.2 (sq_nonneg B)

lemma cappedMoment_descaled {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) {r B : ℝ} (hr : 0 < r) :
    (∫ x, (min (X x) (B*r))^2 ∂μ)=r^2*cappedMoment μ (fun x => X x/r) B := by
  rw [cappedMoment,←integral_const_mul]
  congr 1
  funext x
  have hh : min (X x) (B*r) = r*min (X x/r) B := by
    rw [mul_min_of_nonneg _ _ hr.le,mul_div_cancel₀ _ hr.ne',mul_comm r B]
  rw [hh]
  ring
lemma cappedTailMoment_descaled {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) {r A B : ℝ} (hr : 0 < r) :
    (∫ x, (if A*r < X x then (min (X x) (B*r))^2 else 0) ∂μ)=
      r^2*cappedTailMoment μ (fun x => X x/r) A B := by
  rw [cappedTailMoment,←integral_const_mul]
  congr 1
  funext x
  simp only [lt_div_iff₀ hr]
  split_ifs
  · have hh : min (X x) (B*r) = r*min (X x/r) B := by
      rw [mul_min_of_nonneg _ _ hr.le,mul_div_cancel₀ _ hr.ne',mul_comm r B]
    rw [hh]
    ring
  · ring
lemma cappedTailMoment_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hX0 : ∀ x, 0 ≤ X x) (A : ℝ) {B : ℝ} (hB : 0 < B) :
    0 ≤ cappedTailMoment μ X A B ∧ cappedTailMoment μ X A B ≤ B^2 := by
  rw [cappedTailMoment_scale μ X A hB]
  have hh := cappedTailMoment_unit_bounds μ (fun x => X x/B) (hX.div_const B)
    (fun x => div_nonneg (hX0 x) hB.le) (A/B)
  constructor
  · exact mul_nonneg (sq_nonneg B) hh.1
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hh.2 (sq_nonneg B)
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ScaledMaxMoment
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
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
lemma exists_block_count {T t : ℝ} (hT : 0 < T) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ J : ℕ, T < (J:ℝ)*t ∧ (J:ℝ)*t ≤ 2*T+1 := by
  refine ⟨⌈2*T/t⌉₊,?_,?_⟩
  · have hh := Nat.le_ceil (2*T/t)
    have hh := mul_le_mul_of_nonneg_right hh ht.le
    rw [div_mul_cancel₀ _ ht.ne'] at hh
    linarith
  · have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*T/t)
    have hh := mul_lt_mul_of_pos_right hh ht
    rw [add_mul,div_mul_cancel₀ _ ht.ne',one_mul] at hh
    linarith

lemma eventually_ceil_horizon_covered (n : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (M : ℕ) (hM : T < (M:ℝ)*δ) :
    ∀ᶠ i in atTop, 0 < ⌊δ*n i⌋₊ ∧ 0 < ⌈T*n i⌉₊ ∧ ⌈T*n i⌉₊ ≤ M*⌊δ*n i⌋₊ := by
  filter_upwards [eventually_floor_horizon_covered n hn hT.le hδ M hM,
    hn.eventually (eventually_gt_atTop (0:ℝ))] with i hi hni
  refine ⟨hi.1,?_,?_⟩
  · exact Nat.ceil_pos.mpr (mul_pos hT hni)
  · exact (Nat.ceil_le_floor_add_one _).trans (by omega)
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_TubeHeightMono
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.successQuenchedKernel_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma tubePrefix_mono_width {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (θ : ℝ) {z w : ℝ} (hzw : z ≤ w) (H : ℕ) :
    TubePrefix ℓ f x θ z H ⊆ TubePrefix ℓ f x θ w H := by
  intro X hX
  obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hX
  refine Set.mem_iUnion.mpr ⟨a,ha.1,?_⟩
  intro j hj
  obtain ⟨k,hk,hr,hb⟩ := ha.2 j hj
  exact ⟨k,hk,hr,hb.trans hzw⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClippingTime
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
lemma exists_clipping_time {a b C D M η ε : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) (hD : 0 < D)
    (hM : 0 < M) (hη : 0 < η) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ a ∧ t ≤ b ∧ t ≤ 1 ∧
      C*Real.sqrt t ≤ η/8 ∧ 2*D*M*t ≤ ε/16 := by
  let t := min a (min b (min 1 (min ((η/(8*C))^2) (ε/(32*D*M)))))
  have ht : 0 < t := by dsimp [t] <;> positivity
  have hta : t ≤ a := min_le_left _ _
  have htb : t ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have htc : t ≤ (η/(8*C))^2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hte : t ≤ ε/(32*D*M) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨t,ht,hta,htb,ht1,?_,?_⟩
  · have hh : Real.sqrt t ≤ η/(8*C) := (Real.sqrt_le_iff).mpr ⟨by positivity,htc⟩
    have hh := (le_div_iff₀ (by positivity : 0 < 8*C)).mp hh
    nlinarith
  · have hh := (le_div_iff₀ (by positivity : 0 < 32*D*M)).mp hte
    nlinarith
end DirectionalTransience

end

section

open MeasureTheory Filter
namespace DirectionalTransience
lemma clipping_error_bound {J D M t r η ε V B : ℝ}
    (hJ : 0 ≤ J) (hD : 0 ≤ D) (hM : 0 < M) (ht : 0 < t) (hr : 0 < r)
    (hη : 0 < η) (hε : 0 < ε) (hJt : J*t ≤ M)
    (hfail : B ≤ D*t^2) (hsmall : 2*D*M*t ≤ ε/16)
    (hV : V/r^2 ≤ 4*(ε*η^2/(1024*M))*t) :
    2*(J*B+(4*J*V)/(η*r/2)^2) < ε := by
  have h1 : 2*J*B ≤ ε/16 := calc
    _ ≤ 2*J*(D*t^2) := mul_le_mul_of_nonneg_left hfail (by positivity)
    _ = 2*D*(J*t)*t := by ring
    _ ≤ 2*D*M*t := by gcongr
    _ ≤ _ := hsmall
  have h2 : 32*J*(V/r^2)/η^2 ≤ ε/8 := calc
    _ ≤ 32*J*(4*(ε*η^2/(1024*M))*t)/η^2 := by gcongr
    _ = (ε/(8*M))*(J*t) := by field_simp <;> ring
    _ ≤ (ε/(8*M))*M := mul_le_mul_of_nonneg_left hJt (by positivity)
    _ = ε/8 := by field_simp
  have he : 2*(J*B+4*J*V/(η*r/2)^2)=2*J*B+32*J*(V/r^2)/η^2 := by
    field_simp
    ring
  rw [he]
  linarith
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

theorem clipping_zero_profile {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrinf : Tendsto r atTop atTop)
    (F : ℕ → ℝ) (hFlim : Tendsto F atTop (𝓝 0))
    (hF : ∀ j, Tendsto (fun n => truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (dyadicCut j*r n)/
      truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r n)) atTop (𝓝 (F j)))
    {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≤ 1 ∧ ∀ᶠ n in atTop, ∃ θ : ℝ,
      (environmentLaw ν).real {ω | quenchedKernel (ω,0)
        (TubePrefix (realPosition (step e)) f 0 θ (η*r n)
          ⌈T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) (r n)⌉₊) < c} < ε := by
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  have hp0 : 0 < p := ENNReal.toReal_pos hp (measure_ne_top _ _)
  let K := 40000/p^2
  have hK : 0 < K := by dsimp [K] <;> positivity
  let M := 2*T+1
  have hM : 0 < M := by dsimp [M] <;> linarith
  let ζ := ε*η^2/(1024*M)
  have hζ : 0 < ζ := by dsimp [ζ] <;> positivity
  obtain ⟨j,hjF,hjb⟩ := ((hFlim.eventually (gt_mem_nhds (div_pos hζ hK))).and
    (dyadicCut_tendsto.eventually (gt_mem_nhds (by positivity : 0 < η/8)))).exists
  let b := dyadicCut j
  have hb : 0 < b := dyadicCut_pos j
  have hbη : b < η/8 := hjb
  have hKF : K*F j < ζ := by
    have hh := (lt_div_iff₀ hK).mp hjF
    simpa only [mul_comm] using hh
  obtain ⟨C,hC,t₁,ht₁,hmed⟩ := recordMedian_shortBlock ν hue e f hef htrans
  obtain ⟨D,hD,t₀,ht₀,hfail⟩ := curveIncrement_short_block ν hue e f hef htrans hb
  obtain ⟨t,ht,htt₀,htt₁,ht1,hCs,hDt⟩ :=
    exists_clipping_time ht₀ ht₁ hC hD hM hη hε
  obtain ⟨J,hJT,hJM⟩ := exists_block_count hT ht ht1
  obtain ⟨δ,hδ,hδ1,R,hR,hfail⟩ := hfail t ht htt₀
  let δe := ENNReal.ofReal δ
  have hδe : 0 < δe := ENNReal.ofReal_pos.mpr hδ
  have hδe1 : δe ≤ 1 := ENNReal.ofReal_le_one.mpr hδ1
  let c := δe^J/2
  have hc : 0 < c := ENNReal.div_pos (pow_ne_zero _ hδe.ne') (by norm_num)
  have hc1 : c ≤ 1 := by
    apply (ENNReal.div_le_iff (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num)).mpr
    exact (pow_le_one₀ (zero_le : (0:ℝ≥0∞) ≤ δe) hδe1).trans (by norm_num)
  let N := fun n => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r n)
  have hN : Tendsto N atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hrinf
  let H := fun n => ⌊t*N n⌋₊
  have hH : Tendsto H atTop atTop := tendsto_nat_floor_atTop.comp (hN.const_mul_atTop ht)
  have hHt : ∀ᶠ n in atTop, (H n:ℝ) ≤ t*N n := by
    filter_upwards [hN.eventually (eventually_ge_atTop (0:ℝ))] with n hn
    exact Nat.floor_le (mul_nonneg ht.le hn)
  let med := fun a => (recordMedian ν ℓ hp f a:ℝ)
  let Q := fun n => successfulAverage ν ℓ (H n)
  let W := fun n X => medianDeviation ℓ f med (H n) X
  let a := fun n => cappedMoment (Q n) (fun X => W n X/r n) b
  have ha : limsup a atTop ≤ K*t*F j := successful_small_variance_bound ν hue e f hef htrans
    r hr hrinf H hH hb hHt (hF j)
  have hab : IsBoundedUnder (· ≤ ·) atTop a := by
    apply isBoundedUnder_of
    refine ⟨b^2,fun n => ?_⟩
    let := successfulAverage_probability ν hue ℓ (signed_direction_unit e) htrans (H n)
    exact (cappedMoment_bounds (Q n) _ ((measurable_medianDeviation ℓ f med (H n)).div_const (r n))
      (fun X => div_nonneg (medianDeviation_nonneg ℓ f med (H n) X) (hr n).le) hb).2
  have hal : limsup a atTop < 2*ζ*t := by
    have hh := mul_lt_mul_of_pos_right hKF ht
    nlinarith
  have hae := eventually_lt_of_limsup_lt hal hab
  refine ⟨c,hc,hc1,?_⟩
  filter_upwards [hae,hHt,eventually_ceil_horizon_covered N hN hT ht J hJT,
    hrinf.eventually (eventually_ge_atTop R)] with n han hhn hcover hrR
  have hrn := hr n
  have hHn : 0 < H n := hcover.1
  let dum := medianDummy e f (H n) (recordMedian ν ℓ hp f (H n))
  have hdh : signedHeight e dum=H n := medianDummy_height e f hef _ _
  have hdb : signedCoordinate f dum=med (H n) := medianDummy_coordinate e f hef _ _
  let E := {u : Lattice d | |signedCoordinate f u-med (H n)| ≤ 0}
  let μ := curvePolicy_average ν ℓ f med (b*r n) hHn E hδe (by norm_num : (0:ℝ≥0∞)<1) dum
  let θ := (∫ u, signedCoordinate f u ∂μ.toMeasure)/(H n:ℝ)
  refine ⟨θ,?_⟩
  have hline := hmed t ht htt₁ (r n) (hr n) (H n) hHn hhn
  have hprob := curvePolicy_real_tube_probability ν e f med (mul_nonneg hb.le (hr n).le)
    (by positivity : 0 ≤ C*Real.sqrt t*r n) hHn (by positivity : 0 < η*r n/2)
    hline E hδe (by norm_num : (0:ℝ≥0∞)<1) hδe1 (by norm_num : (1:ℝ≥0∞)≤1)
    dum hdh hdb J hcover.2.1 hcover.2.2
  have hwidth : η*r n/2+2*(b*r n)+C*Real.sqrt t*r n ≤ η*r n := by
    have hh := mul_le_mul_of_nonneg_right hCs (hr n).le
    have hb' := mul_lt_mul_of_pos_right hbη (hr n)
    nlinarith
  have hlow : (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix ℓ f 0 θ (η*r n) ⌈T*N n⌉₊) < c} ≤
      (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix ℓ f 0 θ (η*r n/2+2*(b*r n)+C*Real.sqrt t*r n) ⌈T*N n⌉₊) < c} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    exact (measure_mono (tubePrefix_mono_width ℓ f 0 θ hwidth _)).trans_lt hω
  have hm := curvePolicy_average_zero_moment ν hue e f htrans med (mul_pos hb (hr n)) hHn
    hδe (by norm_num : (0:ℝ≥0∞)<1) dum hdb
  have hdsc := cappedMoment_descaled (Q n) (W n) (r:=r n) (B:=b) (hr n)
  have hV : (∫ u, (signedCoordinate f u-med (H n))^2 ∂μ.toMeasure)/(r n)^2 ≤ 4*ζ*t := by
    have hh : (∫ u, (signedCoordinate f u-med (H n))^2 ∂μ.toMeasure) ≤ 2*((r n)^2*a n) := by
      change _ ≤ 2*((r n)^2*cappedMoment (Q n) (fun X => W n X/r n) b)
      rw [←hdsc]
      exact hm
    apply (div_le_iff₀ (sq_pos_of_pos (hr n))).mpr
    have hhan := mul_le_mul_of_nonneg_left han.le (sq_nonneg (r n))
    nlinarith
  have hf := hfail (r n) hrR (H n) hHn hhn
  have he := clipping_error_bound (show (0:ℝ)≤J by positivity) hD.le hM ht (hr n) hη hε
    hJM hf hDt hV
  have hprob' : (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix ℓ f 0 θ (η*r n/2+2*(b*r n)+C*Real.sqrt t*r n) ⌈T*N n⌉₊) < c} ≤
      2*((J:ℝ)*(environmentLaw ν).real {ω | curveIncrement ℓ f 0 med (b*r n) (H n) ω Set.univ < δe}+
        (4*(J:ℝ)*(∫ u, (signedCoordinate f u-med (H n))^2 ∂μ.toMeasure))/(η*r n/2)^2) := by
    simpa only [one_mul] using hprob
  exact hlow.trans hprob' |>.trans_lt he
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SmallScaleTailMoment
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma success_medianTube_curveIncrement {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (hp : annealedLaw ν (NoDrop (realPosition (step e)) 0) ≠ 0)
    (x : Lattice d) {H : ℕ} (hH : 0 < H) (B R : ℝ) (ω : Environment d) :
    successQuenchedKernel (realPosition (step e)) x H ω
      (medianTubeEndpoint ν (realPosition (step e)) hp f x H B R) =
    (crossingQuenched (realPosition (step e)) x H ω)⁻¹*
      curveIncrement (realPosition (step e)) f x
        (fun j => (recordMedian ν (realPosition (step e)) hp f j:ℝ)) B H ω
        {u | |signedCoordinate f u-(recordMedian ν (realPosition (step e)) hp f H:ℝ)| ≤ R} := by
  let ℓ := realPosition (step e)
  let b := fun j => (recordMedian ν ℓ hp f j:ℝ)
  let Z := fun X : Path d => recordIndexPosition ℓ H (fun j => X j-x)
  have hZ : Measurable Z := (measurable_recordIndexPosition ℓ H).comp (by fun_prop)
  rw [successQuenchedKernel_apply _ _ _ _ _ (measurableSet_medianTubeEndpoint ν ℓ hp f x H B R),
    curveIncrement_eq_success_map e f x b B hH ω,Measure.map_apply hZ (Set.to_countable _).measurableSet,
    Measure.restrict_apply (hZ (Set.to_countable _).measurableSet)]
  congr 2
  ext X
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_preimage,
    medianTubeEndpoint,heightTubeEndpointEvent,medianDeviation_le_iff]
  tauto

lemma curveGaussian_failure_le {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (hp : annealedLaw ν (NoDrop (realPosition (step e)) 0) ≠ 0)
    {H : ℕ} (hH : 0 < H) (B R : ℝ) {α c : ℝ} (hα : 0 < α) (hαc : α ≤ c) :
    (environmentLaw ν).real {ω | ¬ ENNReal.ofReal α*crossingQuenched (realPosition (step e)) 0 H ω ≤
      curveIncrement (realPosition (step e)) f 0
        (fun j => (recordMedian ν (realPosition (step e)) hp f j:ℝ)) B H ω
        {u | |signedCoordinate f u-(recordMedian ν (realPosition (step e)) hp f H:ℝ)| ≤ R}} ≤
    (environmentLaw ν).real {ω | (successQuenchedKernel (realPosition (step e)) 0 H ω).real
      (medianTubeEndpoint ν (realPosition (step e)) hp f 0 H B R) < c} := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [crossingQuenched_positive_ae ν hue (realPosition (step e)) (signed_direction_unit e) htrans]
    with ω hω
  intro hbad
  have hh : successQuenchedKernel (realPosition (step e)) 0 H ω
      (medianTubeEndpoint ν (realPosition (step e)) hp f 0 H B R) < ENNReal.ofReal α := by
    rw [success_medianTube_curveIncrement ν e f hp 0 hH B R ω]
    apply lt_of_not_ge
    intro hh
    have hh := (ENNReal.mul_le_iff_le_inv (hω 0 H) (measure_ne_top _ _)).mpr hh
    exact hbad (by simpa only [mul_comm] using hh)
  have hh' := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hh
  rw [ENNReal.toReal_ofReal hα.le] at hh'
  exact hh'.trans_le hαc
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_ClippingPositiveNumbers
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
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
lemma exists_large_tail_cut {K ζ : ℝ} (hK : 0 < K) (hζ : 0 < ζ) :
    ∃ A : ℝ, 0 < A ∧ K*(2048/(A/40)^2) < ζ/8 := by
  let A := 40*(Real.sqrt (16384*K/ζ)+1)
  have hA : 0 < A := by dsimp [A] <;> positivity
  refine ⟨A,hA,?_⟩
  have hs := Real.sq_sqrt (show 0 ≤ 16384*K/ζ by positivity)
  have hs0 := Real.sqrt_nonneg (16384*K/ζ)
  have hss : 16384*K < ζ*(A/40)^2 := by
    have he : A/40=Real.sqrt (16384*K/ζ)+1 := by dsimp [A] <;> ring
    rw [he]
    have hd : ζ*(16384*K/ζ)=16384*K := by field_simp
    nlinarith
  have hAp : 0 < (A/40)^2 := by positivity
  rw [←mul_div_assoc,div_lt_iff₀ hAp]
  nlinarith

lemma profile_scale_ratio {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Ω → ℝ) (hS : Measurable S) (hzero : 0 < μ {x | S x ≠ 0})
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) {b F : ℝ} (hb : 0 < b) (hF : 0 < F)
    (hlim : Tendsto (fun n => truncatedVariance μ S (b*r n)/truncatedVariance μ S (r n)) atTop (𝓝 F)) :
    Tendsto (fun n => fluctuationScale μ S (b*r n)/fluctuationScale μ S (r n)) atTop (𝓝 (b^2/F)) := by
  convert tendsto_const_nhds.div hlim hF.ne' using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  have hv := ne_of_gt (truncatedVariance_pos μ S hS hzero (hr n))
  have hvb := ne_of_gt (truncatedVariance_pos μ S hS hzero (mul_pos hb (hr n)))
  dsimp [fluctuationScale]
  field_simp [(hr n).ne',hv,hvb]
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_CurvePositiveScale
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
lemma positive_scale_moment_arithmetic {V z r s ρ A bad tail ζ t : ℝ}
    (hr : 0 < r) (hz : 0 < z) (hζ : 0 < ζ) (hA : 0 < A)
    (hρ : ρ^2 ≤ ζ) (hbad : bad < ζ/A^2) (htail : tail < ζ)
    (hV : V ≤ (ρ*z)^2+(A*z)^2*bad+2*(z^2*tail))
    (hs : s^2 ≤ t) (hsz : z=s*r) : V/r^2 ≤ 4*ζ*t := by
  have hba := (lt_div_iff₀ (sq_pos_of_pos hA)).mp hbad
  have ht' := mul_lt_mul_of_pos_left htail (sq_pos_of_pos hz)
  have hρ' := mul_le_mul_of_nonneg_left hρ (sq_nonneg z)
  have hba' := mul_lt_mul_of_pos_left hba (sq_pos_of_pos hz)
  have hVz : V ≤ z^2*(4*ζ) := by nlinarith only [hV,ht',hρ',hba']
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ r^2*(4*ζ) by positivity)
  rw [hsz] at hVz
  nlinarith only [hVz,hh]

lemma curve_positive_scale {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (hp : annealedLaw ν (NoDrop (realPosition (step e)) 0) ≠ 0)
    {r s b A ρ t C D M η ε : ℝ} (hr : 0 < r) (hs : 0 < s) (hb : 0 < b)
    (hA : 0 < A) (hρ : 0 < ρ) (ht : 0 < t) (hC : 0 < C) (hD : 0 < D)
    (hM : 0 < M) (hη : 0 < η) (hε : 0 < ε)
    (hbη : b < η/8) (hAs : A*s < b) (hst : s^2 ≤ t)
    (hρsq : ρ^2 ≤ ε*η^2/(1024*M)) (hCs : C*Real.sqrt t ≤ η/8)
    (hDt : 2*D*M*t ≤ ε/16)
    {H K J : ℕ} (hH : 0 < H) (hK : 0 < K) (hKJ : K ≤ J*H) (hJt : (J:ℝ)*t ≤ M)
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (hδ1 : δ ≤ 1) (hα1 : α ≤ 1)
    (hline : ∀ j ≤ H, |(recordMedian ν (realPosition (step e)) hp f j:ℝ)-
      (j:ℝ)*(recordMedian ν (realPosition (step e)) hp f H:ℝ)/H| ≤ C*Real.sqrt t*r)
    (hfail : (environmentLaw ν).real {ω | curveIncrement (realPosition (step e)) f 0
      (fun j => (recordMedian ν (realPosition (step e)) hp f j:ℝ)) (b*r) H ω Set.univ < δ} ≤ D*t^2)
    (hbad : (environmentLaw ν).real {ω | ¬ α*crossingQuenched (realPosition (step e)) 0 H ω ≤
      curveIncrement (realPosition (step e)) f 0 (fun j => (recordMedian ν (realPosition (step e)) hp f j:ℝ))
        (b*r) H ω {u | |signedCoordinate f u-(recordMedian ν (realPosition (step e)) hp f H:ℝ)| ≤ ρ*(s*r)}} <
      (ε*η^2/(1024*M))/A^2)
    (htail : cappedTailMoment (successfulAverage ν (realPosition (step e)) H)
      (fun X => medianDeviation (realPosition (step e)) f
        (fun j => (recordMedian ν (realPosition (step e)) hp f j:ℝ)) H X/(s*r)) A (b/s) < ε*η^2/(1024*M)) :
    ∃ θ : ℝ, (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix (realPosition (step e)) f 0 θ (η*r) K) < (α*δ)^J/2} < ε := by
  let ℓ := realPosition (step e)
  let med := fun a => (recordMedian ν ℓ hp f a:ℝ)
  let dum := medianDummy e f H (recordMedian ν ℓ hp f H)
  have hdh : signedHeight e dum=H := medianDummy_height e f hef _ _
  have hdb : signedCoordinate f dum=med H := medianDummy_coordinate e f hef _ _
  let E := {u : Lattice d | |signedCoordinate f u-med H| ≤ ρ*(s*r)}
  let υ := curvePolicy_average ν ℓ f med (b*r) hH E hδ hα dum
  let θ := (∫ u, signedCoordinate f u ∂υ.toMeasure)/(H:ℝ)
  refine ⟨θ,?_⟩
  have hprob := curvePolicy_real_tube_probability ν e f med (mul_nonneg hb.le hr.le)
    (by positivity : 0 ≤ C*Real.sqrt t*r) hH (by positivity : 0 < η*r/2)
    hline E hδ hα hδ1 hα1 dum hdh hdb J hK hKJ
  have hwidth : η*r/2+2*(b*r)+C*Real.sqrt t*r ≤ η*r := by
    have hh := mul_le_mul_of_nonneg_right hCs hr.le
    have hb' := mul_lt_mul_of_pos_right hbη hr
    nlinarith only [hh,hb',mul_pos hη hr]
  have hlow : (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix ℓ f 0 θ (η*r) K) < (α*δ)^J/2} ≤
      (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix ℓ f 0 θ (η*r/2+2*(b*r)+C*Real.sqrt t*r) K) < (α*δ)^J/2} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    exact (measure_mono (tubePrefix_mono_width ℓ f 0 θ hwidth _)).trans_lt hω
  have hzn : 0 < s*r := mul_pos hs hr
  have hAB : A*(s*r) < b*r := by nlinarith only [mul_lt_mul_of_pos_right hAs hr]
  have hm := curvePolicy_average_moment ν hue e f htrans med (mul_nonneg hA.le hzn.le) hAB
    (mul_nonneg hρ.le hzn.le) hH hδ hα dum hdb
  have hdsc := cappedTailMoment_descaled (successfulAverage ν ℓ H)
    (fun X => medianDeviation ℓ f med H X) (r:=s*r) (A:=A) (B:=b/s) hzn
  have hbz : (b/s)*(s*r)=b*r := by field_simp
  rw [hbz] at hdsc
  dsimp only at hm
  rw [hdsc] at hm
  have hV := positive_scale_moment_arithmetic hr hzn (show 0 < ε*η^2/(1024*M) by positivity)
    hA hρsq hbad htail hm hst rfl
  exact (hlow.trans hprob).trans_lt (clipping_error_bound (show (0:ℝ)≤J by positivity)
    hD.le hM ht hr hη hε hJt hfail hDt hV)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

theorem clipping_positive_profile {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrinf : Tendsto r atTop atTop)
    (F : ℕ → ℝ) {F₀ : ℝ} (hF₀ : 0 < F₀) (hF₀1 : F₀ ≤ 1)
    (hFle : ∀ j, F₀ ≤ F j) (hFlim : Tendsto F atTop (𝓝 F₀))
    (hF : ∀ j, Tendsto (fun n => truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (dyadicCut j*r n)/
      truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r n)) atTop (𝓝 (F j)))
    {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≤ 1 ∧ ∀ᶠ n in atTop, ∃ θ : ℝ,
      (environmentLaw ν).real {ω | quenchedKernel (ω,0)
        (TubePrefix (realPosition (step e)) f 0 θ (η*r n)
          ⌈T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) (r n)⌉₊) < c} < ε := by
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  have hp0 : 0 < p := ENNReal.toReal_pos hp (measure_ne_top _ _)
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ hp
  let K := 16000/p^2
  have hK : 0 < K := by dsimp [K] <;> positivity
  let M := 8*T+1
  have hM : 0 < M := by dsimp [M] <;> linarith
  let ζ := ε*η^2/(1024*M)
  have hζ : 0 < ζ := by dsimp [ζ] <;> positivity
  let ρ := Real.sqrt ζ/2
  have hρ : 0 < ρ := by dsimp [ρ] <;> positivity
  have hρsq : ρ^2 ≤ ζ := by
    have hh := Real.sq_sqrt hζ.le
    dsimp [ρ]
    nlinarith only [hh,hζ.le]
  obtain ⟨A,hA,hAK⟩ := exists_large_tail_cut hK hζ
  obtain ⟨B,hBF,hBb⟩ := (((hFlim.div_const F₀).sub_const 1).eventually
    (gt_mem_nhds (show F₀/F₀-1 < ζ/(128*K) by rw [div_self hF₀.ne',sub_self]; positivity))).and
    (dyadicCut_tendsto.eventually (gt_mem_nhds (by positivity : 0 < η/8))) |>.exists
  let b := dyadicCut B
  have hb : 0 < b := dyadicCut_pos B
  have hbη : b < η/8 := hBb
  have hBK : K*(16*(F B/F₀-1)) < ζ/8 := by
    have hh := (lt_div_iff₀ (show 0 < 128*K by positivity)).mp hBF
    nlinarith only [hh]
  obtain ⟨C,hC,t₁,ht₁,hmed⟩ := recordMedian_shortBlock ν hue e f hef htrans
  obtain ⟨D,hD,t₀,ht₀,hfail⟩ := curveIncrement_short_block ν hue e f hef htrans hb
  obtain ⟨τ,hτ,hτ₀,hτ₁,hτ1,hCs,hDt⟩ := exists_clipping_time ht₀ ht₁ hC hD hM hη hε
  obtain ⟨cα,hcα,hGaussian⟩ := small_scale_gaussian_mass ν hue e f hef htrans hρ
  let α := min cα 1
  have hα : 0 < α := lt_min hcα zero_lt_one
  have hα1 : α ≤ 1 := min_le_right _ _
  have hαc : α ≤ cα := min_le_left _ _
  have htail := small_scale_tail_moment ν hue e f hef htrans r hr hrinf F hF₀ hFle hFlim hF
    hA B (show 0 < ζ/4 by positivity)
  have hgauss := hGaussian r hr hrinf F F₀ hF₀ hFle hFlim hF b hb 0 (ζ/A^2) (by positivity)
  have htlim : Tendsto (fun j => 2*(dyadicCut j)^2/F₀) atTop (𝓝 0) := by
    simpa only [zero_pow (by omega : 2 ≠ 0),mul_zero,zero_div] using ((dyadicCut_tendsto.pow 2).const_mul 2).div_const F₀
  obtain ⟨j,hjtail,hjgauss,hjt,hjF,hjA⟩ := (htail.and (hgauss.and
    ((htlim.eventually (gt_mem_nhds hτ)).and ((hFlim.eventually (gt_mem_nhds (by linarith : F₀ < 2*F₀))).and
      (dyadicCut_tendsto.eventually (gt_mem_nhds (div_pos hb hA))))))).exists
  let s := dyadicCut j
  have hs : 0 < s := dyadicCut_pos j
  let t := 2*s^2/F₀
  have ht : 0 < t := by dsimp [t] <;> positivity
  have htt : t ≤ τ := le_of_lt hjt
  have htt₀ : t ≤ t₀ := htt.trans hτ₀
  have htt₁ : t ≤ t₁ := htt.trans hτ₁
  have ht1 : t ≤ 1 := htt.trans hτ1
  have hCs' : C*Real.sqrt t ≤ η/8 := (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htt) hC.le).trans hCs
  have hDt' : 2*D*M*t ≤ ε/16 := (mul_le_mul_of_nonneg_left htt (by positivity)).trans hDt
  have hAs : A*s < b := by
    have hh := (lt_div_iff₀ hA).mp hjA
    simpa only [mul_comm] using hh
  obtain ⟨J,hJT,hJM⟩ := exists_block_count (show 0 < 4*T by positivity) ht ht1
  have hJt : (J:ℝ)*t ≤ M := by dsimp [M] <;> linarith
  obtain ⟨δ,hδ,hδ1,R,hR,hfail⟩ := hfail t ht htt₀
  let δe := ENNReal.ofReal δ
  let αe := ENNReal.ofReal α
  have hδe : 0 < δe := ENNReal.ofReal_pos.mpr hδ
  have hαe : 0 < αe := ENNReal.ofReal_pos.mpr hα
  have hδe1 : δe ≤ 1 := ENNReal.ofReal_le_one.mpr hδ1
  have hαe1 : αe ≤ 1 := ENNReal.ofReal_le_one.mpr hα1
  let c := (αe*δe)^J/2
  have hc : 0 < c := ENNReal.div_pos (pow_ne_zero _ (mul_ne_zero hαe.ne' hδe.ne')) (by norm_num)
  have hc1 : c ≤ 1 := by
    apply (ENNReal.div_le_iff (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num)).mpr
    exact (pow_le_one₀ (zero_le : (0:ℝ≥0∞) ≤ αe*δe)
      ((mul_le_of_le_one_left (zero_le : (0:ℝ≥0∞) ≤ δe) hαe1).trans hδe1)).trans (by norm_num)
  let N := fun n => fluctuationScale μ S (r n)
  let z := fun n => s*r n
  let Nz := fun n => fluctuationScale μ S (z n)
  let H := fun n => ⌊Nz n⌋₊
  have hN : Tendsto N atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hrinf
  have hz : ∀ n, 0 < z n := fun n => mul_pos hs (hr n)
  have hNz : Tendsto Nz atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans z (hrinf.const_mul_atTop hs)
  have hH : Tendsto H atTop atTop := tendsto_nat_floor_atTop.comp hNz
  have hratio := profile_scale_ratio μ S (measurable_commonIncrementProcess ℓ f 0)
    (independent_commonWordIncrement_nonzero ν hue e f hef htrans) r hr hs (hF₀.trans_le (hFle j)) (hF j)
  have hrt : s^2/F j < t := calc
    _ ≤ s^2/F₀ := div_le_div_of_nonneg_left (sq_nonneg s) hF₀ (hFle j)
    _ < 2*(s^2/F₀) := by linarith only [show 0 < s^2/F₀ by positivity]
    _ = t := by dsimp [t] <;> ring
  have hlr : t/4 < s^2/F j := by
    have hh := div_lt_div_of_pos_left (sq_pos_of_pos hs) (hF₀.trans_le (hFle j)) hjF
    have he : t/4=s^2/(2*F₀) := by dsimp [t] <;> ring
    rw [he]
    exact hh
  have hbounds : ∀ᶠ n in atTop, 0 < H n ∧ (H n:ℝ) ≤ t*N n ∧ ⌈T*N n⌉₊ ≤ J*H n ∧ 0 < ⌈T*N n⌉₊ := by
    filter_upwards [hN.eventually (eventually_gt_atTop (0:ℝ)), hratio.eventually (Ioo_mem_nhds hlr hrt),
      eventually_ceil_horizon_covered N hN hT (show 0 < t/4 by positivity) J (by linarith)] with n hNn hn hc
    have hupper : Nz n ≤ t*N n := ((div_lt_iff₀ hNn).mp hn.2).le
    have hlower : t/4*N n ≤ Nz n := ((lt_div_iff₀ hNn).mp hn.1).le
    have hfloor : ⌊t/4*N n⌋₊ ≤ H n := Nat.floor_mono hlower
    exact ⟨hc.1.trans_le hfloor,(Nat.floor_le (fluctuationScale_nonneg μ S (z n))).trans hupper,
      hc.2.2.trans (Nat.mul_le_mul_left J hfloor),hc.2.1⟩
  let med := fun a => (recordMedian ν ℓ hp f a:ℝ)
  let Q := fun n => successfulAverage ν ℓ (H n)
  let W := fun n X => medianDeviation ℓ f med (H n) X
  let tail := fun n => cappedTailMoment (Q n) (fun X => W n X/z n) A (b/s)
  have htailBound : IsBoundedUnder (· ≤ ·) atTop tail := by
    apply isBoundedUnder_of
    refine ⟨(b/s)^2,fun n => ?_⟩
    let := successfulAverage_probability ν hue ℓ (signed_direction_unit e) htrans (H n)
    exact (cappedTailMoment_bounds (Q n) _ ((measurable_medianDeviation ℓ f med (H n)).div_const (z n))
      (fun X => div_nonneg (medianDeviation_nonneg ℓ f med (H n) X) (hz n).le) A (div_pos hb hs)).2
  have htailSmall : limsup tail atTop < ζ := by
    have hh : limsup tail atTop ≤ K*(2048/(A/40)^2+16*(F B/F₀-1))+ζ/4 := hjtail
    nlinarith only [hh,hAK,hBK,hζ]
  have htailEv := eventually_lt_of_limsup_lt htailSmall htailBound
  refine ⟨c,hc,hc1,?_⟩
  filter_upwards [htailEv,hjgauss,hbounds,hrinf.eventually (eventually_ge_atTop R)] with n htn hgn hbds hrR
  have hrn := hr n
  have hzn := hz n
  have hHn : 0 < H n := hbds.1
  have hline := hmed t ht htt₁ (r n) hrn (H n) hHn hbds.2.1
  have hbad := (curveGaussian_failure_le ν hue e f htrans hp hHn (b*r n) (ρ*z n) hα hαc).trans_lt hgn
  have hs2 : s^2 ≤ t := by
    dsimp [t]
    apply (le_div_iff₀ hF₀).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hF₀1 (sq_nonneg s),sq_nonneg s]
  exact curve_positive_scale ν hue e f hef htrans hp hrn hs hb hA hρ ht hC hD hM hη hε
    hbη hAs hs2 hρsq hCs' hDt' hHn hbds.2.2.2 hbds.2.2.1 hJt hδe hαe hδe1 hαe1
    hline (hfail (r n) hrR (H n) hHn hbds.2.1) hbad htn
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_UniformLowerMass
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
lemma uniform_lower_mass_from_sequences (P : ℝ → ℝ≥0∞ → Prop)
    (hmono : ∀ r c c', c' ≤ c → P r c → P r c')
    (hseq : ∀ r : ℕ → ℝ, (∀ n, 0 < r n) → Tendsto r atTop atTop →
      ∃ (ns : ℕ → ℕ) (c : ℝ≥0∞), StrictMono ns ∧ 0 < c ∧ c ≤ 1 ∧ ∀ᶠ n in atTop, P (r (ns n)) c) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≤ 1 ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → P r c := by
  by_contra hn
  push Not at hn
  have hx (n : ℕ) : ∃ r : ℝ, (n:ℝ)+1 ≤ r ∧ ¬ P r (ENNReal.ofReal (dyadicCut n)) :=
    hn _ (ENNReal.ofReal_pos.mpr (dyadicCut_pos n)) (ENNReal.ofReal_le_one.mpr (dyadicCut_le_one n))
      ((n:ℝ)+1) (by positivity)
  choose r hre hrP using hx
  have hr : ∀ n, 0 < r n := fun n => lt_of_lt_of_le (by positivity) (hre n)
  have hrinf : Tendsto r atTop atTop := tendsto_atTop_mono hre
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).atTop_add tendsto_const_nhds)
  obtain ⟨ns,c,hns,hc,hc1,hgood⟩ := hseq r hr hrinf
  have hcn : Tendsto (fun n => ENNReal.ofReal (dyadicCut (ns n))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (dyadicCut_tendsto.comp hns.tendsto_atTop)
  obtain ⟨n,hn,hsmall⟩ := (hgood.and (hcn.eventually (gt_mem_nhds hc))).exists
  exact hrP (ns n) (hmono _ _ _ hsmall.le hn)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

theorem clipping_uniform_origin {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≤ 1 ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∃ θ : ℝ,
      (environmentLaw ν).real {ω | quenchedKernel (ω,0)
        (TubePrefix (realPosition (step e)) f 0 θ (η*r)
          ⌈T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) r⌉₊) < c} < ε := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ hp
  let P := fun r c => ∃ θ : ℝ, (environmentLaw ν).real {ω | quenchedKernel (ω,0)
    (TubePrefix ℓ f 0 θ (η*r) ⌈T*fluctuationScale μ S r⌉₊) < c} < ε
  apply uniform_lower_mass_from_sequences P
  · intro r c c' hcc' hP
    obtain ⟨θ,hθ⟩ := hP
    refine ⟨θ,lt_of_le_of_lt ?_ hθ⟩
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    exact hω.trans_le hcc'
  · intro r hr hrinf
    obtain ⟨ns,F,F₀,hns,hF,hFb,hF1,hFa,hF₀,hFlim,hFle⟩ := exists_dyadic_variance_profile μ S
      (measurable_commonIncrementProcess ℓ f 0) (independent_commonWordIncrement_nonzero ν hue e f hef htrans) r hr
    have hri : Tendsto (fun n => r (ns n)) atTop atTop := hrinf.comp hns.tendsto_atTop
    by_cases hzero : F₀=0
    · have hFlim0 : Tendsto F atTop (𝓝 0) := hzero ▸ hFlim
      obtain ⟨c,hc,hc1,hh⟩ := clipping_zero_profile ν hue e f hef htrans
        (fun n => r (ns n)) (fun n => hr (ns n)) hri F hFlim0 hF hT hη hε
      exact ⟨ns,c,hns,hc,hc1,hh⟩
    · have hpos : 0 < F₀ := lt_of_le_of_ne hF₀.1 (Ne.symm hzero)
      obtain ⟨c,hc,hc1,hh⟩ := clipping_positive_profile ν hue e f hef htrans
        (fun n => r (ns n)) (fun n => hr (ns n)) hri F hpos hF₀.2 hFle hFlim hF hT hη hε
      exact ⟨ns,c,hns,hc,hc1,hh⟩
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience
lemma quenchedTube_translation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (θ z : ℝ) (H : ℕ) (ω : Environment d) :
    quenchedKernel (ω,x) (TubePrefix ℓ f x θ z H) =
      quenchedKernel ((fun y => ω (x+y)),0) (TubePrefix ℓ f 0 θ z H) := by
  have hm : Measurable (fun X : Path d => fun n => X n-x) := by fun_prop
  rw [←tubePrefix_translation,←Measure.map_apply hm (measurableSet_tubePrefix ℓ f 0 θ z H)]
  simpa only [add_zero] using congrArg (fun μ : Measure (Path d) => μ (TubePrefix ℓ f 0 θ z H))
    (quenched_translation ω x 0)
lemma quenchedTube_probability_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (x : Lattice d) (θ z : ℝ) (H : ℕ) (c : ℝ≥0∞) :
    (environmentLaw ν).real {ω | quenchedKernel (ω,x) (TubePrefix ℓ f x θ z H) < c} =
      (environmentLaw ν).real {ω | quenchedKernel (ω,0) (TubePrefix ℓ f 0 θ z H) < c} := by
  have hm : Measurable (fun ω : Environment d => quenchedKernel (ω,0) (TubePrefix ℓ f 0 θ z H)) :=
    (Kernel.measurable_coe _ (measurableSet_tubePrefix ℓ f 0 θ z H)).comp (measurable_id.prodMk measurable_const)
  have he := congrArg (fun μ : Measure (Environment d) => μ {ω | quenchedKernel (ω,0) (TubePrefix ℓ f 0 θ z H) < c})
    (environment_translation ν x)
  rw [Measure.map_apply (by fun_prop) (measurableSet_lt hm measurable_const)] at he
  apply congrArg ENNReal.toReal
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext ω
  exact Iff.of_eq (congrArg (fun y : ℝ≥0∞ => y < c) (quenchedTube_translation ℓ f x θ z H ω))
lemma quenchedTube_zero {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (θ : ℝ) {z : ℝ} (hz : 0 ≤ z) (ω : Environment d) :
    quenchedKernel (ω,x) (TubePrefix ℓ f x θ z 0)=1 := by
  apply (measure_congr ?_).trans measure_univ
  filter_upwards [quenched_initial_ae (ω,x)] with X hX
  exact propext (iff_of_true (tubePrefix_zero_of_initial ℓ f x θ z hz X hX) (Set.mem_univ X))

theorem clipping_uniform_oai {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≤ 1 ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∃ θ : ℝ,
      ∀ (x : Lattice d) (H : ℕ), (H:ℝ) ≤ T*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      (environmentLaw ν).real {ω | quenchedKernel (ω,x)
        (TubePrefix (realPosition (step e)) f x θ (η*r) H) < c} < ε := by
  obtain ⟨c,hc,hc1,R,hR,hh⟩ := clipping_uniform_origin ν hue e f hef htrans hT hη hε
  refine ⟨c,hc,hc1,R,hR,fun r hr => ?_⟩
  obtain ⟨θ,hθ⟩ := hh r hr
  refine ⟨θ,fun x H hH => ?_⟩
  rw [quenchedTube_probability_translation]
  by_cases hH0 : H=0
  · subst H
    have hz : 0 ≤ η*r := mul_nonneg hη.le (hR.le.trans hr)
    simp only [quenchedTube_zero _ _ _ _ hz,not_lt.mpr hc1,Set.ofPred_false,measureReal_empty]
    exact hε
  · apply lt_of_le_of_lt _ hθ
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    exact (quenchedTube_mono_height e f 0 θ (η*r) (Nat.pos_of_ne_zero hH0)
      (by exact_mod_cast hH.trans (Nat.le_ceil _)) ω).trans_lt hω
end DirectionalTransience

end

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.clipping_uniform_oai := @OAI.DirectionalTransience.clipping_uniform_oai
