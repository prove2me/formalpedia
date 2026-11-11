-- Prove2me | solution 1 for OAI.DirectionalTransience.transverse_firstHit_path_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:03:35.997297+00:00
-- url     : https://prove2.me/submissions/a652471f-2d89-45d2-a7c6-59e3a7686938

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Theorems.Thm_OAI_DirectionalTransience_conditioned_wordRadius_integrable
import Theorems.Thm_OAI_DirectionalTransience_gaussian_renewal_path_limit

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordDepartures
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma measurable_regenerationTime {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    Measurable (fun X : Path d => regenerationTimes ℓ X n) := by
  exact Finset.measurable_fun_sum _ fun i _ =>
    (measurable_of_countable List.length).comp (measurable_regenerationWord ℓ i)

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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma wordHeightGain_positive {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (hw : AdmissibleTrueWord ℓ w) : 0 < wordHeightGain ℓ w := by
  simpa only [wordPath_zero, dot, realPosition, Pi.zero_apply, Int.cast_zero,
    zero_mul, Finset.sum_const_zero, wordHeightGain] using (hw.2.1 0 hw.1).2

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_LatticeVector
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma latticeVector_add {d : ℕ} (x y : Lattice d) :
    latticeVector (x+y) = latticeVector x + latticeVector y := by
  ext i
  simp [latticeVector, realPosition]

lemma wordRadius_bound {d : ℕ} (w : List (Direction d)) {j : ℕ} (hj : j ≤ w.length) :
    ‖latticeVector (wordPath 0 w j)‖ ≤ wordRadius w := by
  classical
  exact Finset.le_sup' (fun j => ‖latticeVector (wordPath 0 w j)‖)
    (Finset.mem_range.mpr (by omega))

lemma wordRadius_nonneg {d : ℕ} (w : List (Direction d)) : 0 ≤ wordRadius w := by
  have hh := wordRadius_bound w (j := 0) (by omega)
  simpa only [wordPath_zero, latticeVector_zero, norm_zero] using hh

lemma wordRadius_attained {d : ℕ} (w : List (Direction d)) :
    ∃ j ≤ w.length, wordRadius w = ‖latticeVector (wordPath 0 w j)‖ := by
  classical
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_iff.mpr
    (show w.length+1 ≠ 0 by omega)) (fun j => ‖latticeVector (wordPath 0 w j)‖)
  exact ⟨j, by have := Finset.mem_range.mp hj; omega, he⟩

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordTemplate
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma regeneration_span {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (n j : ℕ) (hj : j ≤ (regenerationWords ℓ X n).length) :
    X (regenerationTimes ℓ X n + j) = X (regenerationTimes ℓ X n) +
      wordPath 0 (regenerationWords ℓ X n) j := by
  have hh := (hX n).2.1 j hj
  rw [iterate_renewSuffix_eq ℓ X h0] at hh
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

lemma regeneration_height_sum {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (n : ℕ) : dot (realPosition (X (regenerationTimes ℓ X n))) ℓ =
      ∑ i ∈ Finset.range n, wordHeightGain ℓ (regenerationWords ℓ X i) := by
  induction n with
  | zero => simp [h0, dot, realPosition]
  | succ n ih =>
    rw [regenerationTimes_succ, regeneration_span ℓ X h0 hX n _ (by rfl),
      dot_realPosition_add, ih, Finset.sum_range_succ, wordHeightGain]

lemma regeneration_radius_sum {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (n : ℕ) : ‖latticeVector (X (regenerationTimes ℓ X n))‖ ≤
      ∑ i ∈ Finset.range n, wordRadius (regenerationWords ℓ X i) := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [regenerationTimes_succ, regeneration_span ℓ X h0 hX n _ (by rfl),
      latticeVector_add, Finset.sum_range_succ]
    exact (norm_add_le _ _).trans (add_le_add ih (wordRadius_bound _ (by rfl)))

lemma regeneration_word_admissible {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (n : ℕ) : AdmissibleTrueWord ℓ (regenerationWords ℓ X n) :=
  ((firstTrueWord_characterization ℓ _ _ (hX n).2.1).mp ⟨(hX n).1, (hX n).2.2⟩).1

lemma regeneration_span_bounds {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (n j : ℕ) (hj : j ≤ (regenerationWords ℓ X n).length) :
    (dot (realPosition (X (regenerationTimes ℓ X n))) ℓ ≤
      dot (realPosition (X (regenerationTimes ℓ X n + j))) ℓ ∧
    dot (realPosition (X (regenerationTimes ℓ X n + j))) ℓ ≤
      dot (realPosition (X (regenerationTimes ℓ X (n+1)))) ℓ) ∧
    ‖latticeVector (X (regenerationTimes ℓ X n + j))‖ ≤
      (∑ i ∈ Finset.range n, wordRadius (regenerationWords ℓ X i)) +
        wordRadius (regenerationWords ℓ X n) := by
  have hw := regeneration_word_admissible ℓ X hX n
  have hlo : 0 ≤ dot (realPosition (wordPath 0 (regenerationWords ℓ X n) j)) ℓ := by
    rcases lt_or_eq_of_le hj with hj' | rfl
    · exact (hw.2.1 j hj').1
    · exact (wordHeightGain_positive ℓ _ hw).le
  have hhi : dot (realPosition (wordPath 0 (regenerationWords ℓ X n) j)) ℓ ≤
      wordHeightGain ℓ (regenerationWords ℓ X n) := by
    rcases lt_or_eq_of_le hj with hj' | rfl
    · exact (hw.2.1 j hj').2.le
    · rfl
  rw [regeneration_span ℓ X h0 hX n j hj, dot_realPosition_add, latticeVector_add]
  constructor
  · rw [regenerationTimes_succ, regeneration_span ℓ X h0 hX n _ (by rfl), dot_realPosition_add]
    exact ⟨le_add_of_nonneg_right hlo, add_le_add (le_refl _) hhi⟩
  · exact (norm_add_le _ _).trans
      (add_le_add (regeneration_radius_sum ℓ X h0 hX n) (wordRadius_bound _ hj))

lemma increasing_cuts_cover (T : ℕ → ℕ) (hT : StrictMono T) (h0 : T 0 = 0) (j : ℕ) :
    ∃ n, T n ≤ j ∧ j < T (n+1) := by
  have hex : ∃ n, j < T n := ⟨j+1, lt_of_lt_of_le (by omega) hT.le_apply⟩
  let n := Nat.find hex
  have hn : j < T n := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    simp [this, h0] at hn
  refine ⟨n-1, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by dsimp only [n] at hn0 ⊢; omega))
  · simpa only [Nat.sub_add_cancel hn0] using hn

lemma regeneration_prefix_radius {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    {K j : ℕ} (hj : j ≤ regenerationTimes ℓ X K) :
    ‖latticeVector (X j)‖ ≤ ∑ i ∈ Finset.range K, wordRadius (regenerationWords ℓ X i) := by
  rcases lt_or_eq_of_le hj with hj' | rfl
  · obtain ⟨n, hn, hn'⟩ := increasing_cuts_cover (regenerationTimes ℓ X)
      (regenerationTimes_strictMono ℓ X hX) (regenerationTimes_zero ℓ X) j
    have hnK : n < K := (regenerationTimes_strictMono ℓ X hX).lt_iff_lt.mp (hn.trans_lt hj')
    have hh := (regeneration_span_bounds ℓ X h0 hX n (j-regenerationTimes ℓ X n)
      (by rw [regenerationTimes_succ] at hn'; omega)).2
    rw [Nat.add_sub_of_le hn, ← Finset.sum_range_succ] at hh
    exact hh.trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega : n+1 ≤ K)) (fun _ _ _ => wordRadius_nonneg _))
  · exact regeneration_radius_sum ℓ X h0 hX K

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SignedCoordinate
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_Regeneration
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_WordCoordinate
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma wordCoordinate_abs_le_radius {d : ℕ} (e : Direction d) (w : List (Direction d)) :
    |wordCoordinate e w| ≤ wordRadius w :=
  (signedCoordinate_abs_le_norm _ _).trans (wordRadius_bound _ (by rfl))

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonTrueRecord
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma commonTimes_zero {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) :
    commonTimes ℓ P 0 = (0,0) := by simp [commonTimes]

lemma commonTimes_succ {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) (n : ℕ) :
    commonTimes ℓ P (n+1) =
      ((commonTimes ℓ P n).1+(commonWords ℓ P n).1.length,
       (commonTimes ℓ P n).2+(commonWords ℓ P n).2.length) := by
  simp [commonTimes,Finset.sum_range_succ]

lemma iterate_renewPairSuffix_eq {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0) (n : ℕ) :
    (renewPairSuffix ℓ)^[n] P =
      ((fun j => P.1 ((commonTimes ℓ P n).1+j)-P.1 (commonTimes ℓ P n).1),
       (fun j => P.2 ((commonTimes ℓ P n).2+j)-P.2 (commonTimes ℓ P n).2)) := by
  induction n with
  | zero => simp [commonTimes_zero,h0,h0']
  | succ n ih =>
    rw [Function.iterate_succ_apply',renewPairSuffix,commonTimes_succ]
    have hw : firstPairWord ℓ ((renewPairSuffix ℓ)^[n] P) = commonWords ℓ P n := rfl
    rw [hw,ih]
    apply Prod.ext <;> funext j
    · change P.1 ((commonTimes ℓ P n).1+((commonWords ℓ P n).1.length+j)) -
        P.1 (commonTimes ℓ P n).1 -
        (P.1 ((commonTimes ℓ P n).1+(commonWords ℓ P n).1.length)-
        P.1 (commonTimes ℓ P n).1) =
        P.1 (((commonTimes ℓ P n).1+(commonWords ℓ P n).1.length)+j) -
          P.1 ((commonTimes ℓ P n).1+(commonWords ℓ P n).1.length)
      rw [Nat.add_assoc]; abel
    · change P.2 ((commonTimes ℓ P n).2+((commonWords ℓ P n).2.length+j)) -
        P.2 (commonTimes ℓ P n).2 -
        (P.2 ((commonTimes ℓ P n).2+(commonWords ℓ P n).2.length)-
        P.2 (commonTimes ℓ P n).2) =
        P.2 (((commonTimes ℓ P n).2+(commonWords ℓ P n).2.length)+j) -
          P.2 ((commonTimes ℓ P n).2+(commonWords ℓ P n).2.length)
      rw [Nat.add_assoc]; abel

lemma commonTrueRecord_suffix_iff {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    {n m j k : ℕ} (hn : CommonTrueRecord ℓ P n m) (hj : 0 < j) (hk : 0 < k) :
    CommonTrueRecord ℓ ((fun a => P.1 (n+a)-P.1 n),(fun a => P.2 (m+a)-P.2 m)) j k ↔
      CommonTrueRecord ℓ P (n+j) (m+k) := by
  simp only [CommonTrueRecord,trueRecord_suffix_iff ℓ P.1 hn.1.1 hj,
    trueRecord_suffix_iff ℓ P.2 hn.2.1.1 hk,dot_realPosition_sub,hn.2.2,
    sub_left_inj]

lemma independent_conditioned_all_firstPairWords {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ n,
      ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n) := by
  apply ae_all_iff.mpr
  intro n
  have he := ((renewPairSuffix_preserves_independent_conditioned ν ℓ htrans height hproj hstep).iterate n).quasiMeasurePreserving.ae (independent_conditioned_firstPairWord_exists ν ℓ htrans height hproj hstep)
  filter_upwards [he] with P hP
  simpa only [commonWords,firstPairWord,dite_eq_left hP] using hP.choose_spec

lemma commonTimes_strictMono {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n)) :
    StrictMono (fun n => (commonTimes ℓ P n).1) ∧ StrictMono (fun n => (commonTimes ℓ P n).2) := by
  constructor <;> apply strictMono_nat_of_lt_succ <;> intro n <;> rw [commonTimes_succ]
  · exact Nat.lt_add_of_pos_right (hP n).2.2.1
  · exact Nat.lt_add_of_pos_right (hP n).2.2.2.1

lemma commonTimes_true {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n)) :
    ∀ n, CommonTrueRecord ℓ P (commonTimes ℓ P n).1 (commonTimes ℓ P n).2 := by
  intro n
  induction n with
  | zero =>
    rw [commonTimes_zero]
    refine ⟨⟨fun j hj => by omega, ?_⟩, ⟨fun j hj => by omega, ?_⟩, ?_⟩
    · simpa only [Function.iterate_zero_apply, NoDrop, FutureNoDrop, Set.mem_ofPred_eq,
        Nat.zero_add,h0] using (hP 0).1.1
    · simpa only [Function.iterate_zero_apply, NoDrop, FutureNoDrop, Set.mem_ofPred_eq,
        Nat.zero_add,h0'] using (hP 0).1.2
    · rw [h0,h0']
  | succ n ih =>
    have ht := (hP n).2.2.2.2.1
    rw [iterate_renewPairSuffix_eq ℓ P h0 h0' n] at ht
    rw [commonTimes_succ]
    exact (commonTrueRecord_suffix_iff ℓ P ih (hP n).2.2.1 (hP n).2.2.2.1).mp ht

lemma commonTimes_no_true_between {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (n j k : ℕ) (hj : (commonTimes ℓ P n).1 < j)
    (hjn : j < (commonTimes ℓ P (n+1)).1) : ¬ CommonTrueRecord ℓ P j k := by
  intro ht
  have hn := commonTimes_true ℓ P h0 h0' hP n
  have hn' := commonTimes_true ℓ P h0 h0' hP (n+1)
  have hk := (commonTrueRecord_time_order ℓ P hn ht).mp hj
  have hkn := (commonTrueRecord_time_order ℓ P ht hn').mp hjn
  have hs := (commonTrueRecord_suffix_iff ℓ P hn
    (show 0 < j-(commonTimes ℓ P n).1 by omega)
    (show 0 < k-(commonTimes ℓ P n).2 by omega)).mpr
    (show CommonTrueRecord ℓ P
      ((commonTimes ℓ P n).1+(j-(commonTimes ℓ P n).1))
      ((commonTimes ℓ P n).2+(k-(commonTimes ℓ P n).2)) by
        simpa only [Nat.add_sub_of_le hj.le,Nat.add_sub_of_le hk.le] using ht)
  rw [← iterate_renewPairSuffix_eq ℓ P h0 h0' n] at hs
  exact (hP n).2.2.2.2.2 _ _ (by omega)
    (by rw [commonTimes_succ] at hjn; exact Nat.sub_lt_left_of_lt_add hj.le hjn)
    (by omega) (by rw [commonTimes_succ] at hkn; exact Nat.sub_lt_left_of_lt_add hk.le hkn) hs

lemma commonTrueRecord_eq_commonTimes {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    {j k : ℕ} (hj : CommonTrueRecord ℓ P j k) :
    ∃ n, commonTimes ℓ P n = (j,k) := by
  have hmono := (commonTimes_strictMono ℓ P hP).1
  have hbig (n : ℕ) : n ≤ (commonTimes ℓ P n).1 := by
    induction n with
    | zero => omega
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hmono (Nat.lt_succ_self n)))
  have hex : ∃ n, j < (commonTimes ℓ P n).1 := ⟨j+1, (Nat.lt_succ_self j).trans_le (hbig _)⟩
  let n := Nat.find hex
  have hn : j < (commonTimes ℓ P n).1 := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    simp only [he,commonTimes_zero,not_lt_zero] at hn
  have hbefore : (commonTimes ℓ P (n-1)).1 ≤ j :=
    le_of_not_gt (Nat.find_min hex (show n-1 < Nat.find hex by change n-1 < n; omega))
  have he : (commonTimes ℓ P (n-1)).1 = j := by
    by_contra he
    exact commonTimes_no_true_between ℓ P h0 h0' hP (n-1) j k
      (lt_of_le_of_ne hbefore he) (by simpa only [Nat.sub_add_cancel hn0] using hn) hj
  refine ⟨n-1, Prod.ext he ?_⟩
  have hrec := commonTimes_true ℓ P h0 h0' hP (n-1)
  apply Nat.le_antisymm
  · by_contra h
    have := (commonTrueRecord_time_order ℓ P hj hrec).mpr (by omega : k < (commonTimes ℓ P (n-1)).2)
    omega
  · by_contra h
    have := (commonTrueRecord_time_order ℓ P hrec hj).mpr (by omega : (commonTimes ℓ P (n-1)).2 < k)
    omega

lemma recordCount_commonTimes {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (n : ℕ) : recordCount ℓ P.1 (commonTimes ℓ P n).1 =
      ∑ i ∈ Finset.range n, wordRecordCount ℓ (commonWords ℓ P i).1 := by
  induction n with
  | zero => simp [commonTimes_zero,recordCount]
  | succ n ih =>
    rw [commonTimes_succ,recordCount_add ℓ P.1 (commonTimes_true ℓ P h0 h0' hP n).1.1,
      ih,Finset.sum_range_succ]
    congr 1
    apply recordCount_congr_prefix
    intro j hj
    have he := congrArg Prod.fst (iterate_renewPairSuffix_eq ℓ P h0 h0' n)
    have hword := (hP n).2.1.1 j hj
    rw [he] at hword
    exact hword

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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma independent_conditioned_true_at_index_lower {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) {r : ℕ} (hr : 0 < r) :
    (annealedLaw ν (NoDrop ℓ 0))^2 ≤ independentConditionedPairLaw ν ℓ
      {P | ∃ n m, CommonTrueRecord ℓ P n m ∧ recordCount ℓ P.1 n = r} := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let A : Set (Path d) := {X | ∃ n, 0 < n ∧ TrueRecord ℓ X n ∧ recordCount ℓ X n = r}
  have hlow : annealedLaw ν (NoDrop ℓ 0) ≤ conditionedLaw ν ℓ A :=
    conditioned_true_at_index_lower ν ℓ htrans hr
  calc
    (annealedLaw ν (NoDrop ℓ 0))^2 ≤ (conditionedLaw ν ℓ A)^2 := pow_le_pow_left' hlow 2
    _ = independentConditionedPairLaw ν ℓ (A ×ˢ A) := by
      rw [independentConditionedPairLaw,Measure.prod_prod,pow_two]
    _ ≤ _ := by
      apply measure_mono_ae
      have hac := conditionedLaw_absolutelyContinuous ν ℓ
      have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
        (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
      have hNN := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_nearest_neighbor ν))).and
        (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_nearest_neighbor ν)))
      filter_upwards [h0,hNN] with P h0 hNN hP
      obtain ⟨n,_,hn,hnr⟩ := hP.1
      obtain ⟨m,_,hm,hmr⟩ := hP.2
      have hs1 (j : ℕ) : height (P.1 (j+1)) ≤ height (P.1 j)+1 := by
        obtain ⟨e,he⟩ := hNN.1 j
        rw [he]; exact hstep _ _
      have hs2 (j : ℕ) : height (P.2 (j+1)) ≤ height (P.2 j)+1 := by
        obtain ⟨e,he⟩ := hNN.2 j
        rw [he]; exact hstep _ _
      have he1 := recordCount_eq_height_at_record ℓ height hproj P.1 hs1 hn.1
      have he2 := recordCount_eq_height_at_record ℓ height hproj P.2 hs2 hm.1
      refine ⟨n,m,⟨hn,hm,?_⟩,hnr⟩
      rw [hproj,hproj,he1,he2,h0.1,h0.2,hnr,hmr]

lemma commonWordWidth_positive {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d)) (P : Path d × Path d)
    (hP : P ∈ FirstPairWordEvent ℓ wv) : 0 < commonWordWidth ℓ wv := by
  have hr : StrictRecord ℓ (wordPath 0 wv.1) wv.1.length :=
    (strictRecord_congr_prefix ℓ le_rfl hP.2.1.1).mp hP.2.2.2.2.1.1.1
  simpa only [commonWordWidth,wordRecordCount,recordCount_zero] using
    recordCount_lt_of_strictRecord ℓ (wordPath 0 wv.1) hP.2.2.1 hr

lemma independent_commonWordWidth_integrable {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    Integrable (fun P => (commonWordWidth ℓ (firstPairWord ℓ P) : ℝ))
      (independentConditionedPairLaw ν ℓ) ∧
    (∫ P, (commonWordWidth ℓ (firstPairWord ℓ P) : ℝ) ∂independentConditionedPairLaw ν ℓ) ≤
      1 / ((annealedLaw ν).real (NoDrop ℓ 0))^2 := by
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ (ne_of_gt hp)
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ (ne_of_gt hp)
  let S : ℕ → (Path d × Path d) → ℕ := fun n P => commonWordWidth ℓ (commonWords ℓ P n)
  have hm : Measurable (commonWordWidth ℓ) := measurable_of_countable _
  have hS (n : ℕ) : Measurable (S n) := hm.comp
    ((measurable_firstPairWord ℓ).comp ((measurable_renewPairSuffix ℓ).iterate n))
  have hind : iIndepFun S (independentConditionedPairLaw ν ℓ) :=
    (common_words_independent ν ℓ htrans height hproj hstep).comp (fun _ => commonWordWidth ℓ) (fun _ => hm)
  have hid (n : ℕ) : IdentDistrib (S n) (S 0) (independentConditionedPairLaw ν ℓ)
      (independentConditionedPairLaw ν ℓ) :=
    (common_words_identDistrib ν ℓ htrans height hproj hstep n).comp hm
  have hall := independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep
  have hpos : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ n, 0 < S n P := by
    filter_upwards [hall] with P hP n
    exact commonWordWidth_positive ℓ _ _ (hP n)
  have hp' : 0 < ((annealedLaw ν).real (NoDrop ℓ 0))^2 :=
    sq_pos_of_pos (ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _))
  apply renewal_mean_bound (independentConditionedPairLaw ν ℓ) S hS hind hid hpos hp'
  intro r hr
  have hlow := independent_conditioned_true_at_index_lower ν ℓ htrans height hproj hstep hr
  change (annealedLaw ν (NoDrop ℓ 0)).toReal ^ 2 ≤ _
  rw [← ENNReal.toReal_pow]
  apply (ENNReal.toReal_mono (measure_ne_top _ _) hlow).trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
  filter_upwards [hall,h0] with P hP h0 hR
  obtain ⟨j,k,hjk,hcount⟩ := hR
  obtain ⟨n,hn⟩ := commonTrueRecord_eq_commonTimes ℓ P h0.1 h0.2 hP hjk
  refine ⟨n,?_⟩
  change (∑ i ∈ Finset.range n, wordRecordCount ℓ (commonWords ℓ P i).1) = r
  rw [← recordCount_commonTimes ℓ P h0.1 h0.2 hP,hn]
  exact hcount

lemma measurable_singleCommonIndex {d : ℕ} (ℓ : Vector d) : Measurable (singleCommonIndex ℓ (d := d)) := by
  classical
  have hlen : Measurable (fun P : Path d × Path d => (firstPairWord ℓ P).1.length) :=
    (measurable_of_countable (fun wv : List (Direction d) × List (Direction d) => wv.1.length)).comp
      (measurable_firstPairWord ℓ)
  apply measurable_find
  intro n
  exact (measurableSet_le hlen ((measurable_regenerationTime ℓ n).comp measurable_fst)).union
    (measurableSet_lt hlen measurable_const)

lemma singleCommonIndex_time {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n))
    (hP : P ∈ FirstPairWordEvent ℓ (firstPairWord ℓ P)) :
    regenerationTimes ℓ P.1 (singleCommonIndex ℓ P) = (firstPairWord ℓ P).1.length := by
  have hmono := regenerationTimes_strictMono ℓ P.1 hX
  obtain ⟨n,hn⟩ := trueRecord_eq_regenerationTime ℓ P.1 h0 hX hP.2.2.2.2.1.1
  have hN : singleCommonIndex ℓ P ≤ n := Nat.find_min' _ (Or.inl hn.ge)
  apply le_antisymm ((hmono.monotone hN).trans hn.le)
  rcases Nat.find_spec (singleCommonIndex_exists_bound ℓ P) with h | h
  · exact h
  · exact h.le.trans hmono.le_apply

lemma singleCommonIndex_le_width {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n))
    (hP : P ∈ FirstPairWordEvent ℓ (firstPairWord ℓ P)) :
    singleCommonIndex ℓ P ≤ commonWordWidth ℓ (firstPairWord ℓ P) := by
  have hs := recordCount_regenerationTimes ℓ P.1 h0 hX (singleCommonIndex ℓ P)
  rw [singleCommonIndex_time ℓ P h0 hX hP,
    recordCount_congr_prefix ℓ hP.2.1.1] at hs
  calc
    singleCommonIndex ℓ P = ∑ _i ∈ Finset.range (singleCommonIndex ℓ P), 1 := by simp
    _ ≤ ∑ i ∈ Finset.range (singleCommonIndex ℓ P), wordRecordCount ℓ (regenerationWords ℓ P.1 i) := by
      exact Finset.sum_le_sum fun i _ => wordRecordCount_positive ℓ _
        (regeneration_word_admissible ℓ P.1 hX i)
    _ = _ := hs.symm

lemma commonWordRadius_le_single_sum {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n))
    (hP : P ∈ FirstPairWordEvent ℓ (firstPairWord ℓ P)) :
    wordRadius (firstPairWord ℓ P).1 ≤
      ∑ i ∈ Finset.range (singleCommonIndex ℓ P), wordRadius (regenerationWords ℓ P.1 i) := by
  obtain ⟨j,hj,he⟩ := wordRadius_attained (firstPairWord ℓ P).1
  rw [he,← hP.2.1.1 j hj]
  apply regeneration_prefix_radius ℓ P.1 h0 hX
  rwa [singleCommonIndex_time ℓ P h0 hX hP]

lemma finite_prefix_sum_eq {α : Type*} [AddCommMonoid α] (f : ℕ → α) {j k : ℕ} (hk : k ≤ j) :
    (∑ i : Fin j, if (i : ℕ) < k then f i else 0) = ∑ i ∈ Finset.range k, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then f i else 0) j]
  calc
    _ = ∑ i ∈ Finset.range k, if i < k then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro i _ hi
      simp only [Finset.mem_range] at hi
      exact ite_eq_right hi
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ite_eq_left (Finset.mem_range.mp hi)

lemma measurableSet_noCommonInPrefix {d : ℕ} (ℓ : Vector d) (j : ℕ) :
    MeasurableSet {p : (Fin j → List (Direction d)) × Path d | NoCommonInPrefix ℓ p.1 p.2} := by
  simp only [NoCommonInPrefix, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  change MeasurableSet ({x : (Fin j → List (Direction d)) × Path d | ∃ m,
    TrueRecord ℓ x.2 m ∧ dot (realPosition (x.2 m)) ℓ =
      ∑ i : Fin j, if (i : ℕ) < k+1 then wordHeightGain ℓ (x.1 i) else 0}ᶜ)
  apply MeasurableSet.compl
  simp only [Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro m
  apply ((measurableSet_trueRecord ℓ m).preimage measurable_snd).inter
  apply measurableSet_eq_fun
  · exact (measurable_of_countable (fun z : Lattice d => dot (realPosition z) ℓ)).comp
      ((measurable_pi_apply m).comp measurable_snd)
  · exact ((measurable_of_countable (fun w : Fin j → List (Direction d) =>
      ∑ i : Fin j, if (i : ℕ) < k+1 then wordHeightGain ℓ (w i) else 0)).comp measurable_fst)

lemma singleCommonIndex_gt_iff {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n))
    (hP : P ∈ FirstPairWordEvent ℓ (firstPairWord ℓ P)) (j : ℕ) :
    j < singleCommonIndex ℓ P ↔
      NoCommonInPrefix ℓ (fun k : Fin j => regenerationWords ℓ P.1 k) P.2 := by
  have htime := singleCommonIndex_time ℓ P h0 hX hP
  have hmono := regenerationTimes_strictMono ℓ P.1 hX
  have hfirst := hP.2.2
  change FirstCommonTrueRecord ℓ P (firstPairWord ℓ P).1.length (firstPairWord ℓ P).2.length at hfirst
  have hlevel (k : Fin j) :
      (∑ i : Fin j, if (i : ℕ) < k+1 then wordHeightGain ℓ (regenerationWords ℓ P.1 i) else 0) =
        dot (realPosition (P.1 (regenerationTimes ℓ P.1 (k+1)))) ℓ := by
    rw [finite_prefix_sum_eq (fun n => wordHeightGain ℓ (regenerationWords ℓ P.1 n))
      (j := j) (k := (k : ℕ)+1) (by omega)]
    exact (regeneration_height_sum ℓ P.1 h0 hX (k+1)).symm
  constructor
  · intro hj k hk
    obtain ⟨m,hm,he⟩ := hk
    rw [hlevel] at he
    have hkpos : 0 < regenerationTimes ℓ P.1 (k+1) := by
      simpa only [regenerationTimes_zero] using hmono (show 0 < (k : ℕ)+1 by omega)
    have hkn : regenerationTimes ℓ P.1 (k+1) < (firstPairWord ℓ P).1.length := by
      rw [← htime]
      exact hmono (by omega)
    have hc : CommonTrueRecord ℓ P (regenerationTimes ℓ P.1 (k+1)) m :=
      ⟨regenerationTimes_true ℓ P.1 h0 hX _,hm,he.symm⟩
    have hmpos : 0 < m := by
      by_contra hm0
      have hm0 : m = 0 := by omega
      have hh := hc.1.1 0 hkpos
      rw [h0,he.symm,hm0,h0'] at hh
      exact (lt_irrefl _ hh)
    exact hfirst.2.2.2 _ _ hkpos hkn hmpos
      ((commonTrueRecord_time_order ℓ P hc hfirst.2.2.1).mp hkn) hc
  · intro hno
    by_contra hj
    have hNj : singleCommonIndex ℓ P ≤ j := by omega
    have hNpos : 0 < singleCommonIndex ℓ P := by
      by_contra hn
      have hn : singleCommonIndex ℓ P = 0 := by omega
      rw [hn,regenerationTimes_zero] at htime
      have := hfirst.1
      omega
    let k : Fin j := ⟨singleCommonIndex ℓ P-1,by omega⟩
    apply hno k
    refine ⟨(firstPairWord ℓ P).2.length,hfirst.2.2.1.2.1,?_⟩
    rw [hlevel,show (k : ℕ)+1 = singleCommonIndex ℓ P by dsimp only [k]; omega,htime]
    exact hfirst.2.2.1.2.2.symm

lemma indepFun_past_product {Ω Ω' α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → α) (g : Ω → β) (hf : Measurable f) (hg : Measurable g)
    (hi : IndepFun f g μ) :
    IndepFun (fun p : Ω × Ω' => f p.1) (fun p : Ω × Ω' => (g p.1,p.2)) (μ.prod ν) := by
  have hp : MeasurePreserving (fun x => (f x,g x)) μ ((μ.map f).prod (μ.map g)) :=
    ⟨hf.prodMk hg, hi.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable⟩
  have ht := (measurePreserving_prodAssoc (μ.map f) (μ.map g) ν).comp
    (hp.prod (MeasurePreserving.id ν))
  apply indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop) |>.mpr
  have hleft : (μ.prod ν).map (fun p => f p.1) = μ.map f := by
    rw [← Function.comp_def, ← Measure.map_map hf measurable_fst, Measure.map_fst_prod,
      measure_univ,one_smul]
  have hright : (μ.prod ν).map (fun p => (g p.1,p.2)) = (μ.map g).prod ν := by
    have h := Measure.map_prod_map μ ν hg (measurable_id : Measurable (id : Ω' → Ω'))
    rw [Measure.map_id] at h
    exact h.symm
  rw [hleft,hright]
  exact ht.map_eq

lemma tsum_nat_lt_ennreal (f : ℕ → ℝ≥0∞) (n : ℕ) :
    (∑' i, if i < n then f i else 0) = ∑ i ∈ Finset.range n, f i := by
  classical
  rw [tsum_eq_sum (s := Finset.range n) (fun i hi => by
    have hi' : ¬ i < n := by simpa using hi
    simp only [ite_eq_right hi'])]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ite_eq_left (Finset.mem_range.mp hi)]

lemma lintegral_stopped_iid_sum {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (W : ℕ → Ω → β) (hW : ∀ i, Measurable (W i))
    (hid : ∀ i, IdentDistrib (W i) (W 0) μ μ) (N : Ω → ℕ) (hN : Measurable N)
    (hind : ∀ i, IndepFun (W i) (fun x => if i < N x then (1 : ℝ≥0∞) else 0) μ)
    (F : β → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, ∑ i ∈ Finset.range (N x), F (W i x) ∂μ) =
      (∫⁻ x, (N x : ℝ≥0∞) ∂μ) * (∫⁻ x, F (W 0 x) ∂μ) := by
  classical
  let E := fun i x => if i < N x then (1 : ℝ≥0∞) else 0
  have hE (i : ℕ) : Measurable (E i) := measurable_const.ite
    (measurableSet_lt measurable_const hN) measurable_const
  have he (x : Ω) : (∑ i ∈ Finset.range (N x), F (W i x)) =
      ∑' i, E i x * F (W i x) := by
    simp only [E,ite_mul,one_mul,zero_mul,tsum_nat_lt_ennreal]
  have hn (x : Ω) : (∑' i, E i x) = (N x : ℝ≥0∞) := by
    simp only [E,tsum_nat_lt_ennreal,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
  simp_rw [he]
  rw [lintegral_tsum (f := fun i x => E i x * F (W i x))
    (fun i => ((hE i).mul (hF.comp (hW i))).aemeasurable)]
  have hf (i : ℕ) : (∫⁻ x, E i x * F (W i x) ∂μ) =
      (∫⁻ x, E i x ∂μ) * (∫⁻ x, F (W 0 x) ∂μ) := by
    calc
      _ = (∫⁻ x, E i x ∂μ) * (∫⁻ x, F (W i x) ∂μ) := by
        simpa only [Pi.mul_apply, Function.comp_apply] using
          lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hE i)
            (hF.comp (hW i)) ((hind i).symm.comp measurable_id hF)
      _ = _ := congrArg (fun a => (∫⁻ x, E i x ∂μ) * a) ((hid i).comp hF).lintegral_eq
  simp_rw [hf]
  rw [ENNReal.tsum_mul_right,← lintegral_tsum (fun i => (hE i).aemeasurable)]
  simp_rw [hn]

lemma independent_conditioned_singleCommonIndex_indep {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (j : ℕ) :
    IndepFun (fun P : Path d × Path d => regenerationWords ℓ P.1 j)
      (fun P => if j < singleCommonIndex ℓ P then (1 : ℝ≥0∞) else 0)
      (independentConditionedPairLaw ν ℓ) := by
  classical
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := inferInstanceAs (IsProbabilityMeasure μ)
  have hpast := (independent_past_current μ (fun n X => regenerationWords ℓ X n)
    (measurable_regenerationWord ℓ) (regenerationWords_independent ν ℓ htrans) j).symm
  have hpi : Measurable (fun X : Path d => fun k : Fin j => regenerationWords ℓ X k) := by
    exact Measurable.of_eval (fun k => measurable_regenerationWord ℓ k)
  have hind := indepFun_past_product μ μ (fun X => regenerationWords ℓ X j)
    (fun X => fun k : Fin j => regenerationWords ℓ X k) (measurable_regenerationWord ℓ j) hpi hpast
  let E := fun p : (Fin j → List (Direction d)) × Path d =>
    if NoCommonInPrefix ℓ p.1 p.2 then (1 : ℝ≥0∞) else 0
  have hE : Measurable E := measurable_const.ite (measurableSet_noCommonInPrefix ℓ j) measurable_const
  have hi := hind.comp measurable_id hE
  apply hi.congr ae_eq_rfl
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
  have hX : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ n,
      ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n) :=
    Measure.quasiMeasurePreserving_fst.ae (conditioned_all_firstWords ν ℓ htrans)
  have hP := independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep
  filter_upwards [h0,hX,hP] with P h0 hX hP
  change E ((fun k : Fin j => regenerationWords ℓ P.1 k),P.2) = _
  dsimp only [E]
  rw [← singleCommonIndex_gt_iff ℓ P h0.1 h0.2 hX (hP 0) j]
  by_cases hh : j < singleCommonIndex ℓ P <;> simp only [hh,ite_true, if_true,ite_false, if_false]

lemma independent_singleCommonIndex_integrable {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    Integrable (fun P => (singleCommonIndex ℓ P : ℝ)) (independentConditionedPairLaw ν ℓ) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  apply (independent_commonWordWidth_integrable ν ℓ htrans height hproj hstep).1.mono'
    (((measurable_of_countable ((↑) : ℕ → ℝ)).comp (measurable_singleCommonIndex ℓ)).aestronglyMeasurable)
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, P.1 0 = 0 :=
    Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))
  have hX : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ n,
      ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n) :=
    Measure.quasiMeasurePreserving_fst.ae (conditioned_all_firstWords ν ℓ htrans)
  have hP := independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep
  filter_upwards [h0,hX,hP] with P h0 hX hP
  change ‖(singleCommonIndex ℓ P : ℝ)‖ ≤ _
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast singleCommonIndex_le_width ℓ P h0 hX (hP 0)

lemma identDistrib_fst {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → β) (hf : Measurable f)
    (hg : Measurable g) (hid : IdentDistrib f g μ μ) :
    IdentDistrib (fun p : Ω × Ω => f p.1) (fun p : Ω × Ω => g p.1) (μ.prod μ) (μ.prod μ) := by
  refine ⟨(hf.comp measurable_fst).aemeasurable,(hg.comp measurable_fst).aemeasurable,?_⟩
  rw [show (fun p : Ω × Ω => f p.1) = f ∘ Prod.fst from rfl,
    show (fun p : Ω × Ω => g p.1) = g ∘ Prod.fst from rfl,
    ← Measure.map_map hf measurable_fst,← Measure.map_map hg measurable_fst,
    Measure.map_fst_prod,measure_univ,one_smul]
  exact hid.map_eq

lemma independent_commonWordRadius_fst_integrable {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    Integrable (fun P => wordRadius (firstPairWord ℓ P).1) (independentConditionedPairLaw ν ℓ) := by
  classical
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := inferInstanceAs (IsProbabilityMeasure μ)
  have hW (i : ℕ) : Measurable (fun P : Path d × Path d => regenerationWords ℓ P.1 i) :=
    (measurable_regenerationWord ℓ i).comp measurable_fst
  have hid (i : ℕ) : IdentDistrib (fun P : Path d × Path d => regenerationWords ℓ P.1 i)
      (fun P => regenerationWords ℓ P.1 0) (independentConditionedPairLaw ν ℓ)
      (independentConditionedPairLaw ν ℓ) :=
    identDistrib_fst μ (fun X => regenerationWords ℓ X i) (firstWord ℓ)
      (measurable_regenerationWord ℓ i) (measurable_firstWord ℓ)
      (regenerationWords_identDistrib ν ℓ htrans i)
  have hwal := lintegral_stopped_iid_sum (independentConditionedPairLaw ν ℓ)
    (fun i P => regenerationWords ℓ P.1 i) hW hid (singleCommonIndex ℓ)
    (measurable_singleCommonIndex ℓ)
    (independent_conditioned_singleCommonIndex_indep ν ℓ htrans height hproj hstep)
    (fun w => ENNReal.ofReal (wordRadius w)) (measurable_of_countable _)
  have hNi := independent_singleCommonIndex_integrable ν ℓ htrans height hproj hstep
  have hRi := (measurePreserving_fst (μ := μ) (ν := μ)).integrable_comp_of_integrable
    (conditioned_wordRadius_integrable ν hue ℓ hℓ htrans)
  have hNfin : (∫⁻ P, (singleCommonIndex ℓ P : ℝ≥0∞) ∂independentConditionedPairLaw ν ℓ) < ∞ := by
    have hh := hNi.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal] at hh
    · simpa using hh
    · exact Filter.Eventually.of_forall fun P => Nat.cast_nonneg _
  have hRfin : (∫⁻ P, ENNReal.ofReal (wordRadius (regenerationWords ℓ P.1 0))
      ∂independentConditionedPairLaw ν ℓ) < ∞ := by
    have hh := hRi.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal] at hh
    · exact hh
    · exact Filter.Eventually.of_forall fun P => wordRadius_nonneg _
  refine ⟨((measurable_of_countable (fun wv : List (Direction d) × List (Direction d) =>
    wordRadius wv.1)).comp (measurable_firstPairWord ℓ)).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun P => wordRadius_nonneg _)]
  apply lt_of_le_of_lt _ (ENNReal.mul_lt_top hNfin hRfin)
  rw [← hwal]
  apply lintegral_mono_ae
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, P.1 0 = 0 :=
    Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))
  have hX : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ n,
      ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n) :=
    Measure.quasiMeasurePreserving_fst.ae (conditioned_all_firstWords ν ℓ htrans)
  have hP := independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep
  filter_upwards [h0,hX,hP] with P h0 hX hP
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => wordRadius_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (commonWordRadius_le_single_sum ℓ P h0 hX (hP 0))

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordIncrement
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma independent_commonWordRadius_snd_integrable {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    Integrable (fun P => wordRadius (firstPairWord ℓ P).2) (independentConditionedPairLaw ν ℓ) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hs : MeasurePreserving Prod.swap (independentConditionedPairLaw ν ℓ)
      (independentConditionedPairLaw ν ℓ) := Measure.measurePreserving_swap
  have hi : Integrable ((fun P : Path d × Path d => wordRadius (firstPairWord ℓ P).1) ∘ Prod.swap)
      (independentConditionedPairLaw ν ℓ) := hs.integrable_comp_of_integrable
        (independent_commonWordRadius_fst_integrable ν hue ℓ hℓ htrans height hproj hstep)
  have heq : ((fun P : Path d × Path d => wordRadius (firstPairWord ℓ P).1) ∘ Prod.swap) =
      (fun P => wordRadius (firstPairWord ℓ P).2) := by
    funext P
    dsimp only [Function.comp_def]
    rw [firstPairWord_swap]
    rfl
  rwa [heq] at hi

lemma commonWordIncrement_abs_le {d : ℕ} (e : Direction d)
    (wv : List (Direction d) × List (Direction d)) :
    |commonWordIncrement e wv| ≤ wordRadius wv.1+wordRadius wv.2 :=
  (abs_sub _ _).trans (add_le_add (wordCoordinate_abs_le_radius e _) (wordCoordinate_abs_le_radius e _))

lemma independent_commonWordIncrement_integrable {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d) :
    Integrable (fun P => commonWordIncrement e (firstPairWord ℓ P)) (independentConditionedPairLaw ν ℓ) := by
  apply ((independent_commonWordRadius_fst_integrable ν hue ℓ hℓ htrans height hproj hstep).add
    (independent_commonWordRadius_snd_integrable ν hue ℓ hℓ htrans height hproj hstep)).mono'
    (((measurable_of_countable (commonWordIncrement e)).comp (measurable_firstPairWord ℓ)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun P => by
    simpa only [Real.norm_eq_abs,Function.comp_apply,Pi.add_apply] using commonWordIncrement_abs_le e (firstPairWord ℓ P)

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

lemma truncatedVariance_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hne : 0 < μ {x | S x ≠ 0}) {r : ℝ} (hr : 0 < r) :
    0 < truncatedVariance μ S r := by
  apply (integral_pos_iff_support_of_nonneg (fun x => le_min (sq_nonneg _) (sq_nonneg _))
    (integrable_truncated_square μ S hS r)).mpr
  apply hne.trans_le (measure_mono _)
  intro x hx
  exact ne_of_gt (lt_min (sq_pos_of_ne_zero hx) (sq_pos_of_pos hr))

lemma min_sq_le_mul_abs {s r : ℝ} (hr : 0 ≤ r) : min (s^2) (r^2) ≤ r*|s| := by
  by_cases hs : |s| ≤ r
  · apply (min_le_left _ _).trans
    nlinarith [sq_abs s,abs_nonneg s]
  · apply (min_le_right _ _).trans
    nlinarith [lt_of_not_ge hs]

lemma truncatedVariance_le_firstMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) {r : ℝ} (hr : 0 ≤ r) :
    truncatedVariance μ S r ≤ r*(∫ x, |S x| ∂μ) := by
  rw [truncatedVariance,← integral_const_mul]
  apply integral_mono (integrable_truncated_square μ S hS r) (hI.abs.const_mul r)
  exact fun _ => min_sq_le_mul_abs hr

lemma integral_abs_pos_of_nonzero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0}) :
    0 < ∫ x, |S x| ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => abs_nonneg _) hI.abs).mpr
  simpa only [Function.support,ne_eq,abs_eq_zero] using hne

lemma fluctuationScale_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0}) {r : ℝ} (hr : 0 < r) :
    r/(∫ x, |S x| ∂μ) ≤ fluctuationScale μ S r := by
  have hM := integral_abs_pos_of_nonzero μ S hI hne
  rw [fluctuationScale,div_le_div_iff₀ hM (truncatedVariance_pos μ S hS hne hr)]
  calc
    r * truncatedVariance μ S r ≤ r*(r * ∫ x, |S x| ∂μ) :=
      mul_le_mul_of_nonneg_left (truncatedVariance_le_firstMoment μ S hS hI hr.le) hr.le
    _ = r^2*(∫ x, |S x| ∂μ) := by ring

lemma fluctuationScale_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0}) :
    Tendsto (fluctuationScale μ S) atTop atTop := by
  apply tendsto_atTop_mono' atTop _
    (tendsto_id.atTop_div_const (integral_abs_pos_of_nonzero μ S hI hne))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact fluctuationScale_lower μ S hS hI hne hr

lemma realPartialSum_zero (X : ℕ → ℝ) : realPartialSum X 0 = 0 := by simp [realPartialSum]
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

lemma partialSumMax_mono (X : ℕ → ℝ) : Monotone (partialSumMax X) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma measurable_symmetricTruncate (z : ℝ) : Measurable (symmetricTruncate z) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_id measurable_const

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

lemma integral_symmetricTruncate_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (z : ℝ)
    (hsym : IdentDistrib S (fun ω => -S ω) μ μ) :
    (∫ ω, symmetricTruncate z (S ω) ∂μ) = 0 := by
  have he := (hsym.comp (measurable_symmetricTruncate z)).integral_eq
  simp only [Function.comp_apply,symmetricTruncate_neg,integral_neg] at he
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

lemma commonTimes_span {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (n : ℕ) :
    P.1 (commonTimes ℓ P (n+1)).1 =
      P.1 (commonTimes ℓ P n).1 + wordPath 0 (commonWords ℓ P n).1 (commonWords ℓ P n).1.length ∧
    P.2 (commonTimes ℓ P (n+1)).2 =
      P.2 (commonTimes ℓ P n).2 + wordPath 0 (commonWords ℓ P n).2 (commonWords ℓ P n).2.length := by
  have he := iterate_renewPairSuffix_eq ℓ P h0 h0' n
  have h1 := (hP n).2.1.1 _ le_rfl
  have h2 := (hP n).2.1.2 _ le_rfl
  rw [he] at h1 h2
  rw [commonTimes_succ]
  constructor
  · exact (sub_eq_iff_eq_add.mp h1).trans (add_comm _ _)
  · exact (sub_eq_iff_eq_add.mp h2).trans (add_comm _ _)

lemma common_coordinate_sum {d : ℕ} (ℓ : Vector d) (e : Direction d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (n : ℕ) :
    signedCoordinate e (P.1 (commonTimes ℓ P n).1) -
      signedCoordinate e (P.2 (commonTimes ℓ P n).2) =
        realPartialSum (fun k => commonIncrementProcess ℓ e k P) n := by
  induction n with
  | zero => simp [commonTimes_zero,h0,h0',signedCoordinate,realPartialSum]
  | succ n ih =>
    obtain ⟨h1,h2⟩ := commonTimes_span ℓ P h0 h0' hP n
    rw [h1,h2,signedCoordinate_add,signedCoordinate_add,realPartialSum_succ,← ih]
    simp only [commonIncrementProcess,commonWordIncrement,wordCoordinate]
    ring

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RecordIndexTime
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma independentConditionedPairLaw_eq_restrict {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) :
    independentConditionedPairLaw ν ℓ =
      ((annealedLaw ν (NoDrop ℓ 0))^2)⁻¹ •
        (independentPairLaw ν).restrict (NoDrop ℓ 0 ×ˢ NoDrop ℓ 0) := by
  rw [independentConditionedPairLaw,conditionedLaw,Measure.prod_smul_left,
    Measure.prod_smul_right,smul_smul,Measure.prod_restrict,← pow_two,← ENNReal.inv_pow]
  rfl

lemma independentConditionedPairLaw_normalization {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : Set (Path d × Path d)) (hA : MeasurableSet A) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ A =
      independentPairLaw ν (A ∩ (NoDrop ℓ 0 ×ˢ NoDrop ℓ 0)) := by
  rw [independentConditionedPairLaw_eq_restrict,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply hA,← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero 2 hp) (ENNReal.pow_ne_top (measure_ne_top _ _)),one_mul]

lemma independentConditionedPairLaw_le_raw {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : Set (Path d × Path d)) (hA : MeasurableSet A) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ A ≤
      independentPairLaw ν A := by
  rw [independentConditionedPairLaw_normalization ν ℓ hp A hA]
  exact measure_mono Set.inter_subset_left

lemma independent_conditioned_record_prefix_lower {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : Set (Path d × Path d))
    (hAm : MeasurableSet A) (hA : PairPrefixDetermined n m A)
    (hr : ∀ P ∈ A, StrictRecord ℓ P.1 n ∧ StrictRecord ℓ P.2 m ∧
      dot (realPosition (P.1 n)) ℓ = dot (realPosition (P.2 m)) ℓ)
    (hD : A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m) ⊆ NoDrop ℓ 0 ×ˢ NoDrop ℓ 0) :
    independentPairLaw ν A ≤ independentConditionedPairLaw ν ℓ
      (A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m)) := by
  have hh := pair_record_event_noDrop_lower (independentPairLaw ν) ℓ
    ((annealedLaw ν (NoDrop ℓ 0))^2)
    (fun f g n m hn hm hrf hrg _ =>
      (independent_pair_record_cylinder_noDrop ν ℓ f g n m hn hm hrf hrg).ge)
    n m hn hm A hA hr
  have he := independentConditionedPairLaw_normalization ν ℓ hp
    (A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m))
    (hAm.inter ((measurableSet_futureNoDrop ℓ n).prod (measurableSet_futureNoDrop ℓ m)))
  rw [Set.inter_eq_left.mpr hD] at he
  rw [← he] at hh
  exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero 2 hp)
    (ENNReal.pow_ne_top (measure_ne_top _ _))).mp hh

lemma recordIndexPrefix_time_lt_iff {d : ℕ} (ℓ : Vector d) (X : Path d)
    {r s n m : ℕ} (hn : X ∈ RecordIndexPrefix ℓ r n)
    (hm : X ∈ RecordIndexPrefix ℓ s m) : n < m ↔ r < s := by
  constructor
  · intro h
    have hh := recordCount_lt_of_strictRecord ℓ X h hm.2.1
    simpa only [hn.2.2.1,hm.2.2.1] using hh
  · intro h
    by_contra hh
    have he := recordCount_mono ℓ X (Nat.le_of_not_gt hh)
    rw [hn.2.2.1,hm.2.2.1] at he
    omega

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SignedHeight
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

lemma max_fourth_increment {m a : ℝ} :
    (max m |a|)^4-m^4 ≤ 2*|a| *((max m |a|)^3-m^3) := by
  by_cases h : |a| ≤ m
  · rw [max_eq_left h]; ring_nf; rfl
  · rw [max_eq_right (le_of_not_ge h)]
    have hp := mul_nonneg (mul_nonneg (abs_nonneg a) (sq_nonneg m))
      (sub_nonneg.mpr (le_of_not_ge h))
    nlinarith [sq_nonneg (|a|^2-m^2)]

lemma partialSumMax_fourth_pathwise (X : ℕ → ℝ) (n : ℕ) :
    (partialSumMax X n)^4 ≤ 2*(partialSumMax X n)^3*|realPartialSum X n|-
      2*∑ k ∈ Finset.range n, (partialSumMax X k)^3*absSlope (realPartialSum X k)*X k := by
  induction n with
  | zero => simp [partialSumMax]
  | succ n ih =>
    have hincr := max_fourth_increment (m := partialSumMax X n)
      (a := realPartialSum X (n+1))
    have hs := mul_le_mul_of_nonneg_left (abs_supporting (realPartialSum X n) (X n))
      (pow_nonneg (partialSumMax_nonneg X n) 3)
    rw [← realPartialSum_succ] at hs
    rw [Finset.sum_range_succ]
    change (max (partialSumMax X n) |realPartialSum X (n+1)|)^4 ≤ _
    change _ ≤ 2*(max (partialSumMax X n) |realPartialSum X (n+1)|)^3 * |realPartialSum X (n+1)|-_
    nlinarith

lemma partialSumMax_fourth_pathwise_bound (X : ℕ → ℝ) (n : ℕ) :
    (partialSumMax X n)^4 ≤ 32*(realPartialSum X n)^4-
      4*∑ k ∈ Finset.range n, (partialSumMax X k)^3*absSlope (realPartialSum X k)*X k := by
  have h := partialSumMax_fourth_pathwise X n
  have hy : 2*(partialSumMax X n)^3*|realPartialSum X n| ≤
      (partialSumMax X n)^4/2+16*(realPartialSum X n)^4 := by
    nlinarith [sq_nonneg ((partialSumMax X n)^2-4*partialSumMax X n*|realPartialSum X n|),
      sq_nonneg ((partialSumMax X n)^2-8*(realPartialSum X n)^2),
      sq_abs (realPartialSum X n)]
  linarith

lemma integrable_partialSumMax_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n p : ℕ) :
    Integrable (fun ω => (partialSumMax (fun k => X k ω) n)^p) μ := by
  apply integrable_of_abs_bound μ _ ((measurable_partialSumMax X hX n).pow_const p) ((n*z)^p)
  intro ω
  rw [abs_of_nonneg (pow_nonneg (partialSumMax_nonneg _ _) _)]
  exact pow_le_pow_left₀ (partialSumMax_nonneg _ _) (partialSumMax_bound _ hz (fun k => hbound k ω) n) p

lemma integrable_realPartialSum_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n p : ℕ) :
    Integrable (fun ω => (realPartialSum (fun k => X k ω) n)^p) μ := by
  apply integrable_of_abs_bound μ _ ((measurable_realPartialSum X hX n).pow_const p) ((n*z)^p)
  intro ω
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) ((abs_partialSum_le_max _ _).trans
    (partialSumMax_bound _ hz (fun k => hbound k ω) n)) p

lemma absSlope_cube (t : ℝ) : (absSlope t)^3 = absSlope t := by
  unfold absSlope
  split <;> norm_num

lemma independent_max_cube_transform {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ) (n : ℕ) :
    IndepFun (fun ω => (partialSumMax (fun k => X k ω) n)^3*absSlope (realPartialSum (fun k => X k ω) n))
      (X n) μ := by
  have hh := (independent_max_transform μ X hX hind n).comp
    (show Measurable (fun x : ℝ => x^3) by fun_prop) measurable_id
  simpa only [Function.comp_def,mul_pow,absSlope_cube,id_eq] using hh

lemma integral_partialSumMax_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => X k ω) n)^4 ∂μ) ≤
      32*∫ ω, (realPartialSum (fun k => X k ω) n)^4 ∂μ := by
  let C (k : ℕ) (ω : Ω) := (partialSumMax (fun j => X j ω) k)^3*absSlope (realPartialSum (fun j => X j ω) k)
  have hC (k : ℕ) : Measurable (C k) := ((measurable_partialSumMax X hX k).pow_const 3).mul
    (measurable_absSlope.comp (measurable_realPartialSum X hX k))
  have hCI (k : ℕ) : Integrable (fun ω => C k ω*X k ω) μ := by
    apply integrable_of_abs_bound μ _ ((hC k).mul (hX k)) ((k*z)^3*z)
    intro ω
    dsimp [C]
    rw [abs_mul,abs_mul,abs_absSlope,mul_one,abs_of_nonneg (pow_nonneg (partialSumMax_nonneg _ _) _)]
    exact mul_le_mul (pow_le_pow_left₀ (partialSumMax_nonneg _ _)
      (partialSumMax_bound _ hz (fun j => hbound j ω) k) 3) (hbound k ω)
      (abs_nonneg _) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hz) 3)
  have hzero (k : ℕ) : ∫ ω, C k ω*X k ω ∂μ = 0 := by
    rw [(independent_max_cube_transform μ X hX hind k).integral_fun_mul_eq_mul_integral
      (hC k).aestronglyMeasurable (hX k).aestronglyMeasurable,hmean,mul_zero]
  have hm := integral_mono (integrable_partialSumMax_pow μ X hX hz hbound n 4)
    (((integrable_realPartialSum_pow μ X hX hz hbound n 4).const_mul 32).sub
      ((integrable_finsetSum (Finset.range n) (fun k _ => hCI k)).const_mul 4))
    (fun ω => partialSumMax_fourth_pathwise_bound (fun k => X k ω) n)
  simp only [Pi.sub_apply] at hm
  rw [integral_sub ((integrable_realPartialSum_pow μ X hX hz hbound n 4).const_mul 32)
    ((integrable_finsetSum (Finset.range n) (fun k _ => hCI k)).const_mul 4),
    integral_const_mul,integral_const_mul,integral_finsetSum _ (fun k _ => hCI k)] at hm
  simpa only [hzero,Finset.sum_const_zero,mul_zero,sub_zero] using hm

lemma independent_partialSum_current {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ) (n : ℕ) :
    IndepFun (fun ω => realPartialSum (fun k => X k ω) n) (X n) μ := by
  have hh := (independent_past_current μ X hX hind n).comp
    (show Measurable (fun v : Fin n → ℝ => ∑ k, v k) by fun_prop) measurable_id
  convert hh using 1
  · funext ω
    exact (Fin.sum_univ_eq_sum_range (fun k => X k ω) n).symm
  · rfl

lemma integrable_pow_mul_of_abs_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F G : Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) {a b : ℝ}
    (ha : ∀ ω, |F ω| ≤ a) (hb : ∀ ω, |G ω| ≤ b) (p q : ℕ) :
    Integrable (fun ω => F ω^p*G ω^q) μ := by
  apply integrable_of_abs_bound μ _ (by fun_prop) (a^p*b^q)
  intro ω
  rw [abs_mul,abs_pow,abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (ha ω) p)
    (pow_le_pow_left₀ (abs_nonneg _) (hb ω) q) (pow_nonneg (abs_nonneg _) _)
    (pow_nonneg ((abs_nonneg (F ω)).trans (ha ω)) _)

lemma integral_independent_add_fourth {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F G : Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) (hind : IndepFun F G μ)
    (hmF : ∫ ω, F ω ∂μ = 0) (hmG : ∫ ω, G ω ∂μ = 0)
    {a b : ℝ} (ha : ∀ ω, |F ω| ≤ a) (hb : ∀ ω, |G ω| ≤ b) :
    (∫ ω, (F ω+G ω)^4 ∂μ) =
      (∫ ω, F ω^4 ∂μ)+6*(∫ ω, F ω^2 ∂μ)*(∫ ω, G ω^2 ∂μ)+(∫ ω, G ω^4 ∂μ) := by
  have hI := integrable_pow_mul_of_abs_bound μ F G hF hG ha hb
  have hF4 : Integrable (fun ω => F ω^4) μ := by simpa using hI 4 0
  have hG4 : Integrable (fun ω => G ω^4) μ := by simpa using hI 0 4
  have h31 : Integrable (fun ω => 4*(F ω^3*G ω^1)) μ := (hI 3 1).const_mul 4
  have h22 : Integrable (fun ω => 6*(F ω^2*G ω^2)) μ := (hI 2 2).const_mul 6
  have h13 : Integrable (fun ω => 4*(F ω^1*G ω^3)) μ := (hI 1 3).const_mul 4
  have hfactor (p q : ℕ) : (∫ ω, F ω^p*G ω^q ∂μ) =
      (∫ ω, F ω^p ∂μ)*(∫ ω, G ω^q ∂μ) :=
    (hind.comp (by fun_prop : Measurable (fun x : ℝ => x^p))
      (by fun_prop : Measurable (fun x : ℝ => x^q))).integral_fun_mul_eq_mul_integral
      (hF.pow_const p).aestronglyMeasurable (hG.pow_const q).aestronglyMeasurable
  have heq : (fun ω => (F ω+G ω)^4) =
      (fun ω => F ω^4+4*(F ω^3*G ω^1)+6*(F ω^2*G ω^2)+4*(F ω^1*G ω^3)+G ω^4) := by
    ext ω; ring
  have h12 : Integrable (fun ω => F ω^4+4*(F ω^3*G ω^1)) μ := hF4.add h31
  have h123 : Integrable (fun ω => F ω^4+4*(F ω^3*G ω^1)+6*(F ω^2*G ω^2)) μ := h12.add h22
  have h1234 : Integrable (fun ω => F ω^4+4*(F ω^3*G ω^1)+6*(F ω^2*G ω^2)+4*(F ω^1*G ω^3)) μ := h123.add h13
  rw [heq,integral_add h1234 hG4,integral_add h123 h13,integral_add h12 h22,
    integral_add hF4 h31]
  simp only [integral_const_mul]
  rw [hfactor 3 1,hfactor 2 2,hfactor 1 3]
  simp only [pow_one,hmF,hmG,mul_zero,zero_mul,add_zero]
  ring

lemma integral_iid_partialSum_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (realPartialSum (fun k => X k ω) n)^4 ∂μ) ≤
      n*(∫ ω, (X 0 ω)^4 ∂μ)+3*(n:ℝ)^2*(∫ ω, (X 0 ω)^2 ∂μ)^2 := by
  have hmeans (k : ℕ) : ∫ ω, X k ω ∂μ = 0 := (hident k).integral_eq.trans hmean
  have hpows (k p : ℕ) : (∫ ω, (X k ω)^p ∂μ) = (∫ ω, (X 0 ω)^p ∂μ) :=
    ((hident k).comp (u := fun x : ℝ => x^p) (by fun_prop)).integral_eq
  have hsq (n : ℕ) : (∫ ω, (realPartialSum (fun k => X k ω) n)^2 ∂μ) =
      n*(∫ ω, (X 0 ω)^2 ∂μ) := by
    rw [integral_partialSum_square_eq_sum μ X hX hind hmeans hbound]
    simp only [hpows,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hsummean (n : ℕ) : ∫ ω, realPartialSum (fun k => X k ω) n ∂μ = 0 := by
    rw [show (fun ω => realPartialSum (fun k => X k ω) n) =
      (fun ω => ∑ k ∈ Finset.range n, X k ω) from rfl,
      integral_finsetSum _ (fun k _ => integrable_of_abs_bound μ _ (hX k) z (hbound k))]
    simp only [hmeans,Finset.sum_const_zero]
  induction n with
  | zero => simp [realPartialSum]
  | succ n ih =>
    simp only [realPartialSum_succ]
    rw [integral_independent_add_fourth μ _ _ (measurable_realPartialSum X hX n) (hX n)
      (independent_partialSum_current μ X hX hind n) (hsummean n) (hmeans n)
      (fun ω => (abs_partialSum_le_max _ _).trans (partialSumMax_bound _ hz (fun k => hbound k ω) n))
      (hbound n),hsq]
    simp only [hpows]
    push_cast
    nlinarith [sq_nonneg (∫ ω, (X 0 ω)^2 ∂μ)]

lemma integral_iid_truncated_max_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z r : ℝ} (hz : 0 ≤ z) (hzr : z ≤ r) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => symmetricTruncate z (X k ω)) n)^4 ∂μ) ≤
      32*(n:ℝ)*z^2*truncatedVariance μ (X 0) r+
        96*(n:ℝ)^2*(truncatedVariance μ (X 0) r)^2 := by
  let Y := fun k ω => symmetricTruncate z (X k ω)
  have hY (k : ℕ) : Measurable (Y k) := (measurable_symmetricTruncate z).comp (hX k)
  have hYb := fun k ω => symmetricTruncate_bound hz (X k ω)
  have hYi : iIndepFun Y μ := hind.comp (fun _ => symmetricTruncate z) (fun _ => measurable_symmetricTruncate z)
  have hYid (k : ℕ) : IdentDistrib (Y k) (Y 0) μ μ := (hident k).comp (measurable_symmetricTruncate z)
  have hYm : ∫ ω, Y 0 ω ∂μ = 0 := integral_symmetricTruncate_zero μ (X 0) z hsym
  have hYmeans (k : ℕ) : ∫ ω, Y k ω ∂μ = 0 := (hYid k).integral_eq.trans hYm
  have hI (p : ℕ) : Integrable (fun ω => (Y 0 ω)^p) μ := by
    apply integrable_of_abs_bound μ _ ((hY 0).pow_const p) (z^p)
    intro ω
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hYb 0 ω) p
  have hvar : (∫ ω, (Y 0 ω)^2 ∂μ) ≤ truncatedVariance μ (X 0) r := by
    apply integral_mono (hI 2) (integrable_truncated_square μ (X 0) (hX 0) r)
    intro ω
    exact (symmetricTruncate_sq_le z _).trans
      (min_le_min le_rfl (pow_le_pow_left₀ hz hzr 2))
  have hfour : (∫ ω, (Y 0 ω)^4 ∂μ) ≤ z^2*(∫ ω, (Y 0 ω)^2 ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono (hI 4) ((hI 2).const_mul (z^2))
    intro ω
    have hs : (Y 0 ω)^2 ≤ z^2 := by
      nlinarith [sq_abs (Y 0 ω),hYb 0 ω,abs_nonneg (Y 0 ω)]
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (Y 0 ω))]
  have hv0 : 0 ≤ ∫ ω, (Y 0 ω)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  calc
    _ ≤ 32*(∫ ω, (realPartialSum (fun k => Y k ω) n)^4 ∂μ) :=
      integral_partialSumMax_fourth_le μ Y hY hYi hYmeans hz hYb n
    _ ≤ 32*(n*(∫ ω, (Y 0 ω)^4 ∂μ)+3*(n:ℝ)^2*(∫ ω, (Y 0 ω)^2 ∂μ)^2) :=
      mul_le_mul_of_nonneg_left (integral_iid_partialSum_fourth_le μ Y hY hYi hYid hYm hz hYb n) (by norm_num)
    _ ≤ 32*(n*(z^2*truncatedVariance μ (X 0) r)+3*(n:ℝ)^2*(truncatedVariance μ (X 0) r)^2) := by
      gcongr
      · exact hfour.trans (mul_le_mul_of_nonneg_left hvar (sq_nonneg z))
    _ = _ := by ring

lemma measureReal_truncated_max_gt_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z r a : ℝ} (hz : 0 ≤ z) (hzr : z ≤ r) (ha : 0 < a) (n : ℕ) :
    μ.real {ω | a < partialSumMax (fun k => symmetricTruncate z (X k ω)) n} ≤
      (32*(n:ℝ)*z^2*truncatedVariance μ (X 0) r+
        96*(n:ℝ)^2*(truncatedVariance μ (X 0) r)^2) / a^4 := by
  let Y := fun k ω => symmetricTruncate z (X k ω)
  have hY (k : ℕ) : Measurable (Y k) := (measurable_symmetricTruncate z).comp (hX k)
  have hYb := fun k ω => symmetricTruncate_bound hz (X k ω)
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ω => pow_nonneg (partialSumMax_nonneg (fun k => Y k ω) n) 4))
    (integrable_partialSumMax_pow μ Y hY hz hYb n 4) (a^4)
  have hmono : μ.real {ω | a < partialSumMax (fun k => Y k ω) n} ≤
      μ.real {ω | a^4 ≤ (partialSumMax (fun k => Y k ω) n)^4} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    exact pow_le_pow_left₀ ha.le hω.le 4
  apply (le_div_iff₀ (pow_pos ha 4)).mpr
  calc
    _ ≤ a^4*μ.real {ω | a^4 ≤ (partialSumMax (fun k => Y k ω) n)^4} := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hmono (pow_nonneg ha.le 4)
    _ ≤ (∫ ω, (partialSumMax (fun k => Y k ω) n)^4 ∂μ) := hb
    _ ≤ _ := integral_iid_truncated_max_fourth_le μ X hX hind hident hsym hz hzr n

lemma measureReal_iid_max_gt_fourth_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z r a : ℝ} (hz : 0 ≤ z) (hzr : z ≤ r) (ha : 0 < a) (n : ℕ) :
    μ.real {ω | a < partialSumMax (fun k => X k ω) n} ≤
      n*μ.real {ω | z < |X 0 ω|}+
      (32*(n:ℝ)*z^2*truncatedVariance μ (X 0) r+
        96*(n:ℝ)^2*(truncatedVariance μ (X 0) r)^2) / a^4 := by
  let A : ℕ → Set Ω := fun k => {ω | z < |X k ω|}
  let B : Set Ω := {ω | a < partialSumMax (fun k => symmetricTruncate z (X k ω)) n}
  have hsub : {ω | a < partialSumMax (fun k => X k ω) n} ⊆
      (⋃ k ∈ Finset.range n, A k) ∪ B := by
    intro ω hω
    by_cases ht : ω ∈ ⋃ k ∈ Finset.range n, A k
    · exact Or.inl ht
    · right
      have hc : ∀ k < n, X k ω = symmetricTruncate z (X k ω) := by
        intro k hk
        have hnot : ¬ z < |X k ω| := fun h => ht (Set.mem_iUnion.mpr
          ⟨k,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hk,h⟩⟩)
        simp only [symmetricTruncate,ite_eq_left (le_of_not_gt hnot)]
      change a < partialSumMax (fun k => symmetricTruncate z (X k ω)) n
      rwa [← partialSumMax_congr n hc]
  have htail (k : ℕ) : μ.real (A k) = μ.real (A 0) := by
    exact congrArg ENNReal.toReal ((hident k).measure_mem_eq
      (show MeasurableSet {x : ℝ | z < |x|} from measurableSet_lt measurable_const measurable_id.abs))
  calc
    _ ≤ μ.real ((⋃ k ∈ Finset.range n, A k) ∪ B) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real (⋃ k ∈ Finset.range n, A k)+μ.real B := measureReal_union_le _ _
    _ ≤ (∑ k ∈ Finset.range n, μ.real (A k))+μ.real B :=
      add_le_add (measureReal_biUnion_finset_le _ _) le_rfl
    _ = n*μ.real {ω | z < |X 0 ω|}+μ.real B := by
      simp only [htail,Finset.sum_const,Finset.card_range,nsmul_eq_mul,A]
    _ ≤ _ := add_le_add le_rfl (measureReal_truncated_max_gt_le μ X hX hind hident hsym hz hzr ha n)

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

lemma shifted_iid_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ) (s : ℕ) :
    IdentDistrib (fun ω k => X (s+k) ω) (fun ω k => X k ω) μ μ := by
  exact IdentDistrib.pi (fun k => (hident _).trans (hident k).symm)
    (hind.precomp (fun _ _ h => Nat.add_left_cancel h)) hind

lemma measureReal_shifted_max {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ) (s H : ℕ) (a : ℝ) :
    μ.real {ω | a < partialSumMax (fun k => X (s+k) ω) H} =
      μ.real {ω | a < partialSumMax (fun k => X k ω) H} := by
  apply congrArg ENNReal.toReal
  exact ((shifted_iid_identDistrib μ X hind hident s).comp
    (measurable_partialSumMax (fun k (f : ℕ → ℝ) => f k)
      (fun k => measurable_pi_apply k) H)).measure_mem_eq measurableSet_Ioi

lemma measureReal_max_scaled_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hne : 0 < μ {ω | X 0 ω ≠ 0}) {r η ε α : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (_hα : 0 ≤ α) (H s : ℕ) (hH : (H : ℝ) ≤ α*fluctuationScale μ (X 0) r) :
    μ.real {ω | ε*r < partialSumMax (fun k => X (s+k) ω) H} ≤
      α*(fluctuationScale μ (X 0) r*μ.real {ω | η*r < |X 0 ω|}) +
      (32*α*η^2+96*α^2)/ε^4 := by
  rw [measureReal_shifted_max μ X hind hident]
  have hm := truncatedVariance_pos μ (X 0) (hX 0) hne hr
  have hn : 0 < fluctuationScale μ (X 0) r := div_pos (sq_pos_of_pos hr) hm
  have hb := measureReal_iid_max_gt_fourth_bound μ X hX hind hident hsym
    (mul_nonneg hη hr.le) (by nlinarith : η*r ≤ r) (mul_pos hε hr) H
  apply hb.trans
  calc
    _ ≤ (α*fluctuationScale μ (X 0) r)*μ.real {ω | η*r < |X 0 ω|} +
        (32*(α*fluctuationScale μ (X 0) r)*(η*r)^2*truncatedVariance μ (X 0) r+
          96*(α*fluctuationScale μ (X 0) r)^2*(truncatedVariance μ (X 0) r)^2)/(ε*r)^4 := by
      gcongr
    _ = _ := by
      unfold fluctuationScale
      field_simp

lemma gaussian_max_block_eventually {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hne : 0 < μ {ω | X 0 ω ≠ 0}) (r : ℕ → ℝ)
    (hr : IsGaussianSequence μ (X 0) r) {α ε ζ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) (hζ : 0 < ζ)
    (H : ℕ → ℕ) (hH : ∀ᶠ i in atTop, (H i : ℝ) ≤ α*fluctuationScale μ (X 0) (r i)) :
    ∀ᶠ i in atTop, ∀ s : ℕ,
      μ.real {ω | ε*r i < partialSumMax (fun k => X (s+k) ω) (H i)} ≤
        128*α^2/ε^4+ζ := by
  have ht := (hr.2 (Real.sqrt α) (Real.sqrt_pos.2 hα)).const_mul α
  have he := (tendsto_order.mp ht).2 ζ (by simpa using hζ)
  filter_upwards [hr.1.eventually (eventually_gt_atTop (0:ℝ)),hH,he] with i hri hHi hti
  intro s
  have hb := measureReal_max_scaled_fourth_le μ X hX hind hident hsym hne hri
    (Real.sqrt_nonneg α) (by simpa using Real.sqrt_le_sqrt hα1) hε hα.le (H i) s hHi
  rw [Real.sq_sqrt hα.le] at hb
  have ha : (32*α*α+96*α^2)/ε^4 = 128*α^2/ε^4 := by ring
  rw [ha] at hb
  linarith

lemma realPartialSum_add (x : ℕ → ℝ) (s n : ℕ) :
    realPartialSum x (s+n) = realPartialSum x s + realPartialSum (fun k => x (s+k)) n := by
  simp only [realPartialSum,Finset.sum_range_add]

lemma grid_oscillation_block {x : ℕ → ℝ} {H j k : ℕ} (hH : 0 < H)
    (hjk : j ≤ k) (hkj : k ≤ j+H) {a : ℝ}
    (hmax : partialSumMax (fun l => x (j/H*H+l)) (2*H) ≤ a) :
    |realPartialSum x k-realPartialSum x j| ≤ 2*a := by
  let s := j/H*H
  have hsj : s ≤ j := Nat.div_mul_le_self j H
  have hsk : s ≤ k := hsj.trans hjk
  have hj2 : j-s ≤ 2*H := by
    have hjrem := Nat.mod_lt j hH
    have hjdecomp : j%H+s = j := by simpa [s,Nat.mul_comm] using Nat.mod_add_div j H
    omega
  have hk2 : k-s ≤ 2*H := by
    have hjrem := Nat.mod_lt j hH
    have hjdecomp : j%H+s = j := by simpa [s,Nat.mul_comm] using Nat.mod_add_div j H
    omega
  have hjb := (abs_partialSum_le_max (fun l => x (s+l)) (j-s)).trans
    ((partialSumMax_mono _ hj2).trans hmax)
  have hkb := (abs_partialSum_le_max (fun l => x (s+l)) (k-s)).trans
    ((partialSumMax_mono _ hk2).trans hmax)
  have hej := realPartialSum_add x s (j-s)
  have hek := realPartialSum_add x s (k-s)
  rw [Nat.add_sub_of_le hsj] at hej
  rw [Nat.add_sub_of_le hsk] at hek
  rw [hej,hek]
  have he : realPartialSum x s + realPartialSum (fun l => x (s+l)) (k-s)-
      (realPartialSum x s + realPartialSum (fun l => x (s+l)) (j-s)) =
      realPartialSum (fun l => x (s+l)) (k-s)-realPartialSum (fun l => x (s+l)) (j-s) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

lemma measureReal_gridOscillation_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    {N H M : ℕ} (hH : 0 < H) (hN : N < M*H) (a : ℝ) :
    μ.real (GridOscillation X N H (2*a)) ≤
      M*μ.real {ω | a < partialSumMax (fun k => X k ω) (2*H)} := by
  let A : ℕ → Set Ω := fun b => {ω | a < partialSumMax (fun k => X (b*H+k) ω) (2*H)}
  have hsub : GridOscillation X N H (2*a) ⊆ ⋃ b ∈ Finset.range M, A b := by
    intro ω hω
    rcases hω with ⟨j,hj,k,_hk,hjk,hkj,hoff⟩
    refine Set.mem_iUnion.mpr ⟨j/H,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr ?_,?_⟩⟩
    · exact (Nat.div_lt_iff_lt_mul hH).2 (hj.trans_lt hN)
    · by_contra h
      exact (not_le_of_gt hoff) (grid_oscillation_block hH hjk hkj (le_of_not_gt h))
  calc
    _ ≤ μ.real (⋃ b ∈ Finset.range M, A b) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ b ∈ Finset.range M, μ.real (A b) := measureReal_biUnion_finset_le _ _
    _ = _ := by
      simp only [A,measureReal_shifted_max μ X hind hident,Finset.sum_const,
        Finset.card_range,nsmul_eq_mul]

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

lemma gaussian_gridOscillation_eventually {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T δ ε ζ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hε : 0 < ε) (hζ : 0 < ζ) (M : ℕ) (hM : T < (M:ℝ)*δ) :
    ∀ᶠ i in atTop,
      μ.real (GridOscillation X ⌊T*fluctuationScale μ (X 0) (r i)⌋₊
        ⌊δ*fluctuationScale μ (X 0) (r i)⌋₊ (ε*r i)) ≤
        M*(8192*δ^2/ε^4+ζ) := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  have hlen : ∀ᶠ i in atTop, ((2*⌊δ*n i⌋₊ : ℕ) : ℝ) ≤ (2*δ)*n i := by
    filter_upwards [hn.eventually (eventually_gt_atTop (0:ℝ))] with i hni
    have hf := Nat.floor_le (mul_nonneg hδ.le hni.le)
    push_cast
    linarith
  have hb := gaussian_max_block_eventually μ X hX hind hident hsym hne r hr
    (by linarith : 0 < 2*δ) (by linarith : 2*δ ≤ 1) (by linarith : 0 < ε/2)
    hζ (fun i => 2*⌊δ*n i⌋₊) hlen
  filter_upwards [hb,eventually_floor_horizon_covered n hn hT hδ M hM] with i hi hcov
  have hm := measureReal_gridOscillation_le μ X hind hident hcov.1 hcov.2 ((ε/2)*r i)
  have he : 2*((ε/2)*r i) = ε*r i := by ring
  rw [he] at hm
  apply hm.trans
  have hb0 := hi 0
  simp only [zero_add] at hb0
  have hec : 128*(2*δ)^2/(ε/2)^4 = 8192*δ^2/ε^4 := by ring
  rw [hec] at hb0
  exact mul_le_mul_of_nonneg_left hb0 (Nat.cast_nonneg M)

theorem gaussian_grid_modulus {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T ε β : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in atTop,
      μ.real (GridOscillation X ⌊T*fluctuationScale μ (X 0) (r i)⌋₊
        ⌊δ*fluctuationScale μ (X 0) (r i)⌋₊ (ε*r i)) ≤ β := by
  have he4 : 0 < ε^4 := pow_pos hε 4
  have hT2 : 0 < T+2 := by linarith
  let δ := min (1/2:ℝ) (β*ε^4/(32768*(T+2)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos (mul_pos hβ he4) (by positivity))
  have hδ1 : δ ≤ 1/2 := min_le_left _ _
  have hbudget : δ*(32768*(T+2)) ≤ β*ε^4 :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  let M := ⌈T/δ⌉₊+1
  have hMpos : 0 < (M:ℝ) := by dsimp [M] <;> positivity
  have hceil := Nat.le_ceil (T/δ)
  have hM : T < (M:ℝ)*δ := by
    have h := (div_le_iff₀ hδ).1 hceil
    dsimp [M]
    push_cast
    nlinarith
  have hMb : (M:ℝ) ≤ T/δ+2 := by
    have hc := Nat.ceil_lt_add_one (div_nonneg hT hδ.le)
    dsimp [M]
    push_cast
    linarith
  have hMδ : (M:ℝ)*δ^2 ≤ (T+2)*δ := by
    have hm : (M:ℝ)*δ ≤ T+2*δ := by
      have hc := mul_le_mul_of_nonneg_right hMb hδ.le
      field_simp at hc
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hm hδ.le]
  have hsmall : (M:ℝ)*(8192*δ^2/ε^4) ≤ β/2 := by
    rw [← mul_div_assoc,div_le_iff₀ he4]
    nlinarith
  have hζ : 0 < β/(2*(M:ℝ)) := div_pos hβ (by positivity)
  refine ⟨δ,hδ,?_⟩
  have hb := gaussian_gridOscillation_eventually μ X hX hind hident hsym hI hne r hr
    hT hδ hδ1 hε hζ M hM
  filter_upwards [hb] with i hi
  apply hi.trans
  rw [mul_add]
  have he : (M:ℝ)*(β/(2*(M:ℝ))) = β/2 := by field_simp
  rw [he]
  linarith

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
lemma renewalCount_monotone (L : ℕ → ℕ) : Monotone (renewalCount L) := by
  intro a b hab
  exact Nat.findGreatest_mono (fun _ h => h.trans hab) hab

lemma linear_error_uniform (f : ℕ → ℝ) (c : ℝ)
    (hf : Tendsto (fun k : ℕ => f k/k) atTop (𝓝 c))
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ k : ℕ, (k : ℝ) ≤ T*a → |f k-c*k| ≤ ε*a := by
  have hδ : 0 < ε/(T+1) := div_pos hε (by linarith)
  obtain ⟨K,hK⟩ := (Metric.tendsto_atTop.1 hf) (ε/(T+1)) hδ
  let C := ∑ k ∈ Finset.range (K+1), |f k-c*k|
  filter_upwards [eventually_ge_atTop (max 0 (C/ε))] with a ha k hk
  have ha0 : 0 ≤ a := (le_max_left _ _).trans ha
  by_cases hkK : k ≤ K
  · have h1 : |f k-c*k| ≤ C := Finset.single_le_sum (fun j _ => abs_nonneg (f j-c*j))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hkK))
    exact h1.trans (by simpa [mul_comm] using (div_le_iff₀ hε).1 ((le_max_right _ _).trans ha))
  · have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have he : f k/(k : ℝ)-c = (f k-c*k)/k := by field_simp
    have hbound := hK k (by omega)
    rw [Real.dist_eq,he,abs_div,abs_of_pos hkpos] at hbound
    have hh := (div_lt_iff₀ hkpos).1 hbound
    have h2 : (ε/(T+1))*(k : ℝ) ≤ ε*a := by
      calc
        _ ≤ (ε/(T+1))*(T*a) := mul_le_mul_of_nonneg_left hk hδ.le
        _ ≤ ε*a := by
          have hd : T/(T+1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
          calc
            _ = (ε*a)*(T/(T+1)) := by ring
            _ ≤ ε*a := mul_le_of_le_one_right (mul_nonneg hε.le ha0) hd
    exact hh.le.trans h2

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWidthProcess
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma renewalCount_uniform (L : ℕ → ℕ) (hL : ∀ k, 0 < L k) {c : ℝ} (hc : 0 < c)
    (hmean : Tendsto (fun k : ℕ => (renewalSum L k : ℝ)/k) atTop (𝓝 c))
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, 0 < a ∧ ∀ h : ℕ, (h : ℝ) ≤ T*a →
      |(renewalCount L h : ℝ)/a-(h : ℝ)/(c*a)| ≤ ε := by
  have hlinear := linear_error_uniform (fun k => (renewalSum L k : ℝ)) c hmean
    (T := T+1) (ε := ε*c/2) (by linarith) (by positivity)
  filter_upwards [hlinear,eventually_ge_atTop (max 1 (2/ε))] with a ha ha'
  have ha1 : 1 ≤ a := (le_max_left _ _).trans ha'
  have ha0 : 0 < a := by linarith
  refine ⟨ha0,fun h hh => ?_⟩
  let k := renewalCount L h
  have hk : (k : ℝ) ≤ T*a := (Nat.cast_le.2 (renewalCount_le L h)).trans hh
  have hk' : (k+1 : ℝ) ≤ (T+1)*a := by linarith
  have haK := ha k (by nlinarith : (k : ℝ) ≤ (T+1)*a)
  have haK' := ha (k+1) (by simpa using hk')
  have hlo : (renewalSum L k : ℝ) ≤ (h : ℝ) := by exact_mod_cast renewalCount_lower L h
  have hup : (h : ℝ) < (renewalSum L (k+1) : ℝ) := by exact_mod_cast renewalCount_upper L hL h
  have hbig : 2 ≤ ε*a := by simpa [mul_comm] using (div_le_iff₀ hε).1 ((le_max_right _ _).trans ha')
  have he : (k : ℝ)/a-(h : ℝ)/(c*a) = (c*k-h)/(c*a) := by field_simp
  rw [he,abs_div,abs_of_pos (mul_pos hc ha0),div_le_iff₀ (mul_pos hc ha0)]
  rcases abs_le.mp haK with ⟨haK1,haK2⟩
  rcases abs_le.mp haK' with ⟨haK1',haK2'⟩
  push_cast at haK1' haK2'
  apply abs_le.2
  constructor <;> nlinarith

lemma measurable_renewalCount {Ω : Type*} [MeasurableSpace Ω]
    (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k)) (h : ℕ) :
    Measurable (fun ω => renewalCount (fun k => L k ω) h) := by
  classical
  apply measurable_findGreatest
  intro k _
  exact measurableSet_le (Finset.measurable_sum _ (fun j _ => hL j)) measurable_const

lemma measure_tendsto_zero_of_ae_eventually_notMem {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : ℕ → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (he : ∀ᵐ ω ∂μ, ∀ᶠ i in atTop, ω ∉ A i) :
    Tendsto (fun i => μ (A i)) atTop (𝓝 0) := by
  let F := fun i => (A i).indicator (fun _ => (1 : ℝ))
  have hF : ∀ i, Measurable (F i) := fun i => measurable_const.indicator (hA i)
  have hc : TendstoInMeasure μ F atTop 0 := by
    apply tendstoInMeasure_of_tendsto_ae (fun i => (hF i).aestronglyMeasurable)
    filter_upwards [he] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with i hi
    simp [F,hi]
  have h := (tendstoInMeasure_iff_norm.1 hc) 1 zero_lt_one
  have hi : ∀ i, {ω | (1:ℝ) ≤ ‖F i ω-(0 : Ω → ℝ) ω‖} = A i := by
    intro i
    ext ω
    by_cases hω : ω ∈ A i <;> simp [F,hω]
  simpa only [hi] using h

lemma renewalCount_uniform_in_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (L : ℕ → Ω → ℕ)
    (hL : ∀ k, Measurable (L k)) (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω)
    {c : ℝ} (hc : 0 < c)
    (hmean : ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => (renewalSum (fun j => L j ω) k : ℝ)/k)
      atTop (𝓝 c)) (n : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    Tendsto (fun i => μ {ω | ∃ h : ℕ, (h : ℝ) ≤ T*n i ∧
      ε < |(renewalCount (fun j => L j ω) h : ℝ)/n i-(h : ℝ)/(c*n i)|}) atTop (𝓝 0) := by
  apply measure_tendsto_zero_of_ae_eventually_notMem
  · intro i
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro h
    exact (MeasurableSet.const _).inter
      (measurableSet_lt measurable_const ((((measurable_of_countable (fun j : ℕ => (j : ℝ))).comp (measurable_renewalCount L hL h)).div_const _).sub
        measurable_const).abs)
  · filter_upwards [hpos,hmean] with ω hpos hmean
    have h := hn.eventually (renewalCount_uniform (fun j => L j ω) hpos hc hmean hT hε)
    filter_upwards [h] with i hi
    rintro ⟨h,hh,hbad⟩
    exact (not_lt_of_ge (hi.2 h hh)) hbad

lemma measurable_commonWidthProcess {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    Measurable (commonWidthProcess ℓ (d := d) n) :=
  (measurable_of_countable (commonWordWidth ℓ)).comp
    ((measurable_firstPairWord ℓ).comp ((measurable_renewPairSuffix ℓ).iterate n))

lemma commonMeanWidth_ge_one {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) : 1 ≤ commonMeanWidth ν ℓ := by
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hi := (independent_commonWordWidth_integrable ν ℓ htrans height hproj hstep).1
  have he := integral_mono_ae (integrable_const (1:ℝ)) hi (by
    filter_upwards [independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep] with P hP
    exact_mod_cast commonWordWidth_positive ℓ _ _ (hP 0))
  simpa [commonMeanWidth,commonWidthProcess,commonWords] using he

lemma commonWidth_strongLaw {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentConditionedPairLaw ν ℓ,
      Tendsto (fun n : ℕ => (renewalSum (fun k => commonWidthProcess ℓ k P) n : ℝ)/n)
        atTop (𝓝 (commonMeanWidth ν ℓ)) := by
  have hi := (independent_commonWordWidth_integrable ν ℓ htrans height hproj hstep).1
  have hind := (common_words_independent ν ℓ htrans height hproj hstep).comp
    (fun _ wv => (commonWordWidth ℓ wv : ℝ)) (fun _ => measurable_of_countable _)
  have hid (n : ℕ) := (common_words_identDistrib ν ℓ htrans height hproj hstep n).comp
    (measurable_of_countable (fun wv => (commonWordWidth ℓ wv : ℝ)))
  have h := strong_law_ae_real _ hi (fun i j hij => hind.indepFun hij) hid
  simpa only [renewalSum,Nat.cast_sum,commonWidthProcess,commonMeanWidth,commonWords,Function.comp_apply] using h

lemma abs_convex_sub_le {a b z q A : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ha : |a-z| ≤ A) (hb : |b-z| ≤ A) : |(1-q)*a+q*b-z| ≤ A := by
  have he : (1-q)*a+q*b-z = (1-q)*(a-z)+q*(b-z) := by ring
  rw [he]
  calc
    _ ≤ |(1-q)*(a-z)|+|q*(b-z)| := abs_add_le _ _
    _ = (1-q)*|a-z|+q*|b-z| := by rw [abs_mul,abs_mul,abs_of_nonneg hq,abs_of_nonneg (by linarith : 0 ≤ 1-q)]
    _ ≤ (1-q)*A+q*A := add_le_add (mul_le_mul_of_nonneg_left ha (by linarith))
      (mul_le_mul_of_nonneg_left hb hq)
    _ = A := by ring

theorem transverse_common_boundary_path_limit {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    letI : IsProbabilityMeasure (independentConditionedPairLaw ν (realPosition (step e))) :=
      independentConditionedPairLaw_probability ν _
        (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i P => scaledPolygon
        (renewalRewardIncrement (fun k => commonIncrementProcess (realPosition (step e)) f k P)
          (fun k => commonWidthProcess (realPosition (step e)) k P)) (r i)
        (fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)) T)
        atTop id (fun _ => independentConditionedPairLaw ν (realPosition (step e))) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) =
          gaussianPathFiniteLaw (T/commonMeanWidth ν (realPosition (step e))) I := by
  let ℓ := realPosition (step e)
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  apply gaussian_renewal_path_limit _ _ (measurable_commonIncrementProcess ℓ f)
    (commonIncrements_independent ν ℓ htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) f)
    (commonIncrements_identDistrib ν ℓ htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) f)
    (independent_commonWordIncrement_symmetric ν ℓ htrans f)
    (independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e)
      htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f)
    (independent_commonWordIncrement_nonzero ν hue e f hef htrans)
    _ (measurable_commonWidthProcess ℓ) _
    (commonMeanWidth_ge_one ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e))
    (commonWidth_strongLaw ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e))
    r hr hT
  filter_upwards [independent_conditioned_all_firstPairWords ν ℓ htrans
    (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)] with P hP k
  exact commonWordWidth_positive ℓ _ _ (hP k)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

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

theorem renewal_selected_mark_small {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ℕ → Ω → α)
    (hW : ∀ k, Measurable (W k)) (hind : iIndepFun W μ)
    (hident : ∀ k, IdentDistrib (W k) (W 0) μ μ)
    (L : α → ℕ) (hL : Measurable L) (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L (W k ω))
    (hI : Integrable (fun ω => (L (W 0 ω) : ℝ)) μ)
    (R : α → ℝ) (hR : Measurable R) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (h : ℕ → ℕ) :
    TendstoInMeasure μ (fun i ω => R (W (renewalCount (fun j => L (W j ω)) (h i)) ω)/r i)
      atTop 0 := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs]
  have ht := width_mark_tail_tendsto μ (fun ω => L (W 0 ω)) (hL.comp (hW 0)) hI
    (fun ω => R (W 0 ω)) (hR.comp (hW 0)) (fun i => ε*r i) (hr.const_mul_atTop hε)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ ht
  filter_upwards [hr.eventually (eventually_gt_atTop (0:ℝ))] with i hri
  have he : {ω | ε ≤ |R (W (renewalCount (fun j => L (W j ω)) (h i)) ω)/r i|} =
      {ω | W (renewalCount (fun j => L (W j ω)) (h i)) ω ∈ {a | ε*r i ≤ |R a|}} := by
    ext ω
    simp only [Set.mem_ofPred_eq,abs_div,abs_of_pos hri,le_div_iff₀ hri]
  rw [he]
  exact renewal_selected_event_bound μ W hW hind hident L hL hpos hI
    {a | ε*r i ≤ |R a|} (measurableSet_le measurable_const hR.abs) (h i)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstHitPairGap
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma recordCount_commonTimes_second {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep1 : ∀ n, height (P.1 (n+1)) ≤ height (P.1 n)+1)
    (hstep2 : ∀ n, height (P.2 (n+1)) ≤ height (P.2 n)+1) (n : ℕ) :
    recordCount ℓ P.2 (commonTimes ℓ P n).2 =
      renewalSum (fun j => commonWidthProcess ℓ j P) n := by
  have ht := commonTimes_true ℓ P h0 h0' hP n
  have h1 := recordCount_eq_height_at_record ℓ height hproj P.1 hstep1 ht.1.1
  have h2 := recordCount_eq_height_at_record ℓ height hproj P.2 hstep2 ht.2.1.1
  have he := ht.2.2
  rw [hproj,hproj] at he
  have he' : height (P.1 (commonTimes ℓ P n).1) = height (P.2 (commonTimes ℓ P n).2) := by
    exact_mod_cast he
  rw [h1,h2,h0,h0',add_right_inj] at he'
  have hc : recordCount ℓ P.1 (commonTimes ℓ P n).1 = recordCount ℓ P.2 (commonTimes ℓ P n).2 := by
    exact_mod_cast he'
  rw [← hc,recordCount_commonTimes ℓ P h0 h0' hP n]
  rfl

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

lemma firstHit_common_boundary_error {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (P : Path d × Path d) (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep1 : ∀ n, height (P.1 (n+1)) ≤ height (P.1 n)+1)
    (hstep2 : ∀ n, height (P.2 (n+1)) ≤ height (P.2 n)+1)
    {h : ℕ} (hs1 : 0 < h → P.1 ∈ RecordIndexPrefix ℓ h (recordIndexTime ℓ h P.1))
    (hs2 : 0 < h → P.2 ∈ RecordIndexPrefix ℓ h (recordIndexTime ℓ h P.2)) :
    |(signedCoordinate e (recordIndexPosition ℓ h P.1)-
      signedCoordinate e (recordIndexPosition ℓ h P.2))-
      realPartialSum (fun j => commonIncrementProcess ℓ e j P)
        (renewalCount (fun j => commonWidthProcess ℓ j P) h)| ≤
      wordRadius (commonWords ℓ P (renewalCount (fun j => commonWidthProcess ℓ j P) h)).1 +
      wordRadius (commonWords ℓ P (renewalCount (fun j => commonWidthProcess ℓ j P) h)).2 := by
  by_cases hh : h = 0
  · subst h
    simpa only [recordIndexPosition,recordIndexTime_zero,h0,h0',sub_self,renewalCount_zero,
      realPartialSum_zero,abs_zero] using add_nonneg
        (wordRadius_nonneg (commonWords ℓ P 0).1) (wordRadius_nonneg (commonWords ℓ P 0).2)
  have hh' : 0 < h := Nat.pos_of_ne_zero hh
  let k := renewalCount (fun j => commonWidthProcess ℓ j P) h
  have hpos (j : ℕ) : 0 < commonWidthProcess ℓ j P := commonWordWidth_positive ℓ _ _ (hP j)
  have hlow := renewalCount_lower (fun j => commonWidthProcess ℓ j P) h
  have hupp := renewalCount_upper (fun j => commonWidthProcess ℓ j P) hpos h
  have hc1 (n : ℕ) : recordCount ℓ P.1 (commonTimes ℓ P n).1 =
      renewalSum (fun j => commonWidthProcess ℓ j P) n :=
    recordCount_commonTimes ℓ P h0 h0' hP n
  have hc2 := recordCount_commonTimes_second ℓ P h0 h0' hP height hproj hstep1 hstep2
  have ht := commonTimes_true ℓ P h0 h0' hP k
  have hb1 := recordTime_between ℓ P.1 ht.1.1 (hs1 hh')
    (by rw [hc1]; exact hlow) (k := (commonTimes ℓ P (k+1)).1) (by rw [hc1]; exact hupp)
  have hb2 := recordTime_between ℓ P.2 ht.2.1.1 (hs2 hh')
    (by rw [hc2]; exact hlow) (k := (commonTimes ℓ P (k+1)).2) (by rw [hc2]; exact hupp)
  have he := iterate_renewPairSuffix_eq ℓ P h0 h0' k
  have hw1 := (hP k).2.1.1
  have hw2 := (hP k).2.1.2
  rw [he] at hw1 hw2
  have herr1 := coordinate_prefix_bound e P.1 (commonWords ℓ P k).1 hw1 hb1.1
    (by rw [commonTimes_succ] at hb1; exact hb1.2.le)
  have herr2 := coordinate_prefix_bound e P.2 (commonWords ℓ P k).2 hw2 hb2.1
    (by rw [commonTimes_succ] at hb2; exact hb2.2.le)
  rw [← common_coordinate_sum ℓ e P h0 h0' hP k]
  change |(_-_)-(_-_)| ≤ _
  calc
    _ = |(signedCoordinate e (P.1 (recordIndexTime ℓ h P.1))-
        signedCoordinate e (P.1 (commonTimes ℓ P k).1))-
        (signedCoordinate e (P.2 (recordIndexTime ℓ h P.2))-
        signedCoordinate e (P.2 (commonTimes ℓ P k).2))| := by dsimp only [recordIndexPosition]; congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add herr1 herr2)

lemma measurable_firstHitPairGap {d : ℕ} (ℓ : Vector d) (e : Direction d) (h : ℕ) :
    Measurable (firstHitPairGap ℓ e h) :=
  ((measurable_of_countable (signedCoordinate e)).comp
    ((measurable_recordIndexPosition ℓ h).comp measurable_fst)).sub
    ((measurable_of_countable (signedCoordinate e)).comp
    ((measurable_recordIndexPosition ℓ h).comp measurable_snd))

lemma independent_firstHit_decoration_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ h : ℕ,
      |firstHitPairGap ℓ e h P-realPartialSum (fun j => commonIncrementProcess ℓ e j P)
        (renewalCount (fun j => commonWidthProcess ℓ j P) h)| ≤
      wordRadius (commonWords ℓ P (renewalCount (fun j => commonWidthProcess ℓ j P) h)).1 +
      wordRadius (commonWords ℓ P (renewalCount (fun j => commonWidthProcess ℓ j P) h)).2 := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
  have hNN := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_nearest_neighbor ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_nearest_neighbor ν)))
  have hs : ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ h, 0 < h →
      X ∈ RecordIndexPrefix ℓ h (recordIndexTime ℓ h X) := by
    apply ae_all_iff.mpr
    intro h
    by_cases hh : 0 < h
    · exact (conditioned_recordIndexTime_spec ν ℓ htrans hh).mono (fun _ hX _ => hX)
    · exact Eventually.of_forall (fun _ hh' => (hh hh').elim)
  have hs' := (Measure.quasiMeasurePreserving_fst.ae hs).and (Measure.quasiMeasurePreserving_snd.ae hs)
  filter_upwards [h0,hNN,hs',independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep]
    with P h0 hNN hs' hP h
  apply firstHit_common_boundary_error ℓ e P h0.1 h0.2 hP height hproj _ _ (hs'.1 h) (hs'.2 h)
  · intro n
    obtain ⟨u,hu⟩ := hNN.1 n
    rw [hu]
    exact hstep _ _
  · intro n
    obtain ⟨u,hu⟩ := hNN.2 n
    rw [hu]
    exact hstep _ _

theorem independent_firstHit_decoration_small {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (h : ℕ → ℕ) :
    TendstoInMeasure (independentConditionedPairLaw ν ℓ) (fun i P =>
      (firstHitPairGap ℓ e (h i) P-realPartialSum (fun j => commonIncrementProcess ℓ e j P)
        (renewalCount (fun j => commonWidthProcess ℓ j P) (h i)))/r i) atTop 0 := by
  let μ := independentConditionedPairLaw ν ℓ
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let W := fun k P => commonWords ℓ P k
  let R := fun wv : List (Direction d) × List (Direction d) => wordRadius wv.1+wordRadius wv.2
  have hpos : ∀ᵐ P ∂μ, ∀ k, 0 < commonWordWidth ℓ (W k P) := by
    filter_upwards [independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep] with P hP k
    exact commonWordWidth_positive ℓ _ _ (hP k)
  have ht := renewal_selected_mark_small μ W
    (fun k => (measurable_firstPairWord ℓ).comp ((measurable_renewPairSuffix ℓ).iterate k))
    (common_words_independent ν ℓ htrans height hproj hstep)
    (common_words_identDistrib ν ℓ htrans height hproj hstep)
    (commonWordWidth ℓ) (measurable_of_countable _) hpos
    (independent_commonWordWidth_integrable ν ℓ htrans height hproj hstep).1
    R (measurable_of_countable _) r hr h
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have ht' := tendstoInMeasure_iff_measureReal_norm.mp ht ε hε
  simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] at ht' ⊢
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ ht'
  apply Eventually.of_forall
  intro i
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae _)
  filter_upwards [independent_firstHit_decoration_bound ν ℓ e htrans height hproj hstep] with P hP ha
  refine ha.trans ?_
  rw [abs_div,abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  exact (hP (h i)).trans (le_abs_self _)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AlignedRecordPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma alignedRecordPrefix_order {d : ℕ} (ℓ : Vector d) {P : Path d × Path d} {q q' : ℕ × ℕ}
    (hP : P ∈ AlignedRecordPrefix ℓ q) (hQ : P ∈ AlignedRecordPrefix ℓ q') :
    (q.1 < q'.1 ↔ q.2 < q'.2) ∧ (q.1 = q'.1 ↔ q.2 = q'.2) := by
  obtain ⟨⟨r,_,hr,hr'⟩,_⟩ := hP
  obtain ⟨⟨s,_,hs,hs'⟩,_⟩ := hQ
  have h1 := recordIndexPrefix_time_lt_iff ℓ P.1 hr hs
  have h2 := recordIndexPrefix_time_lt_iff ℓ P.2 hr' hs'
  have h3 := recordIndexPrefix_time_lt_iff ℓ P.1 hs hr
  have h4 := recordIndexPrefix_time_lt_iff ℓ P.2 hs' hr'
  exact ⟨h1.trans h2.symm,by omega⟩

lemma measurableSet_firstPairTest {α : Type*} [MeasurableSpace α]
    (A : ℕ × ℕ → Set α) (hA : ∀ q, MeasurableSet (A q)) (q : ℕ × ℕ) :
    MeasurableSet (FirstPairTest A q) := by
  simp only [FirstPairTest,Set.ofPred_forall]
  exact (hA q).inter (MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => (hA _).compl)

lemma firstPairTest_prefix {d : ℕ} (A : ℕ × ℕ → Set (Path d × Path d))
    (hA : ∀ q, PairPrefixDetermined q.1 q.2 (A q)) (q : ℕ × ℕ) :
    PairPrefixDetermined q.1 q.2 (FirstPairTest A q) := by
  intro P Q h1 h2
  simp only [FirstPairTest,Set.mem_inter_iff,Set.mem_ofPred_eq,hA q P Q h1 h2]
  apply and_congr Iff.rfl
  exact forall_congr' fun j => forall_congr' fun hj => forall_congr' fun k =>
    forall_congr' fun hk => not_congr (hA (j,k) P Q
      (fun i hi => h1 i (hi.trans hj.le)) (fun i hi => h2 i (hi.trans hk.le)))

lemma firstPairTest_disjoint {d : ℕ} (ℓ : Vector d) (A : ℕ × ℕ → Set (Path d × Path d))
    (hA : ∀ q, A q ⊆ AlignedRecordPrefix ℓ q) :
    Pairwise (fun q q' => Disjoint (FirstPairTest A q) (FirstPairTest A q')) := by
  intro q q' hne
  apply Set.disjoint_left.mpr
  intro P hP hQ
  have hord := alignedRecordPrefix_order ℓ (hA q hP.1) (hA q' hQ.1)
  rcases lt_trichotomy q.1 q'.1 with h | h | h
  · exact hQ.2 q.1 h q.2 (hord.1.mp h) hP.1
  · exact hne (Prod.ext h (hord.2.mp h))
  · exact hP.2 q'.1 h q'.2 ((alignedRecordPrefix_order ℓ (hA q' hQ.1) (hA q hP.1)).1.mp h) hQ.1

lemma iUnion_firstPairTest {α : Type*} (A : ℕ × ℕ → Set α) :
    (⋃ q, FirstPairTest A q) = ⋃ q, A q := by
  classical
  apply Set.Subset.antisymm
  · intro P hP
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hP
    exact Set.mem_iUnion.mpr ⟨q,hq.1⟩
  · intro P hP
    have hx : ∃ n, ∃ m, P ∈ A (n,m) := by
      obtain ⟨⟨n,m⟩,h⟩ := Set.mem_iUnion.mp hP
      exact ⟨n,m,h⟩
    obtain ⟨m,hm⟩ := Nat.find_spec hx
    exact Set.mem_iUnion.mpr ⟨(Nat.find hx,m),hm,fun j hj k _ h => Nat.find_min hx hj ⟨k,h⟩⟩

theorem independent_exact_cut_transfer {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : ℕ × ℕ → Set (Path d × Path d)) (hAm : ∀ q, MeasurableSet (A q))
    (hAp : ∀ q, PairPrefixDetermined q.1 q.2 (A q))
    (hA : ∀ q, A q ⊆ AlignedRecordPrefix ℓ q) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ (⋃ q, A q) ≤
      independentConditionedPairLaw ν ℓ
        (⋃ q, A q ∩ {P | CommonTrueRecord ℓ P q.1 q.2}) := by
  let F := FirstPairTest A
  let B (q : ℕ × ℕ) := F q ∩ (FutureNoDrop ℓ q.1 ×ˢ FutureNoDrop ℓ q.2)
  have hFm (q) : MeasurableSet (F q) := measurableSet_firstPairTest A hAm q
  have hBm (q) : MeasurableSet (B q) := (hFm q).inter
    ((measurableSet_futureNoDrop ℓ q.1).prod (measurableSet_futureNoDrop ℓ q.2))
  have hBd : Pairwise (fun q q' => Disjoint (B q) (B q')) := by
    intro q q' hne
    exact (firstPairTest_disjoint ℓ A hA hne).mono Set.inter_subset_left Set.inter_subset_left
  have hforce (q) : independentPairLaw ν (F q) ≤ independentConditionedPairLaw ν ℓ (B q) := by
    by_cases hq : 0 < q.1 ∧ 0 < q.2
    · apply independent_conditioned_record_prefix_lower ν ℓ hp hq.1 hq.2 _
        (hFm q) (firstPairTest_prefix A hAp q)
      · intro P hP
        obtain ⟨⟨r,_,hr,hr'⟩,he⟩ := hA q hP.1
        exact ⟨hr.2.1,hr'.2.1,he⟩
      · rintro P ⟨hP,hD⟩
        obtain ⟨⟨r,_,hr,hr'⟩,_⟩ := hA q hP.1
        exact ⟨recordIndexPrefix_noDrop ℓ r q.1 ⟨hr,hD.1⟩,
          recordIndexPrefix_noDrop ℓ r q.2 ⟨hr',hD.2⟩⟩
    · have he : F q = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro P hP
        obtain ⟨⟨r,_,hr,hr'⟩,_⟩ := hA q hP.1
        exact hq ⟨hr.1,hr'.1⟩
      rw [he,measure_empty]
      exact bot_le
  rw [← iUnion_firstPairTest A]
  calc
    _ ≤ independentPairLaw ν (⋃ q, F q) :=
      independentConditionedPairLaw_le_raw ν ℓ hp _ (MeasurableSet.iUnion hFm)
    _ = ∑' q, independentPairLaw ν (F q) := measure_iUnion (firstPairTest_disjoint ℓ A hA) hFm
    _ ≤ ∑' q, independentConditionedPairLaw ν ℓ (B q) := ENNReal.tsum_le_tsum hforce
    _ = independentConditionedPairLaw ν ℓ (⋃ q, B q) := (measure_iUnion hBd hBm).symm
    _ ≤ _ := by
      apply measure_mono
      intro P hP
      obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hP
      obtain ⟨⟨r,_,hr,hr'⟩,he⟩ := hA q hq.1.1
      exact Set.mem_iUnion.mpr ⟨q,hq.1.1,⟨hr.2.1,hq.2.1⟩,⟨hr'.2.1,hq.2.2⟩,he⟩

lemma recordOrZeroPrefix_time {d : ℕ} (ℓ : Vector d) {r n : ℕ} {X : Path d}
    (hX : X ∈ RecordOrZeroPrefix ℓ r n) : recordIndexTime ℓ r X = n := by
  by_cases hr : r = 0
  · subst r
    have : n = 0 := by simpa [RecordOrZeroPrefix] using hX
    rw [this,recordIndexTime_zero]
  · exact recordIndexTime_eq ℓ r n X (by simpa [RecordOrZeroPrefix,hr] using hX)

lemma measurableSet_pairOscillationTest {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (J : Set (ℕ × ℕ)) (z : ℝ) (q : ℕ × ℕ) : MeasurableSet (PairOscillationTest ℓ e J z q) := by
  have hm1 (n : ℕ) : Measurable (fun P : Path d × Path d => signedCoordinate e (P.1 n)) :=
    (measurable_of_countable (signedCoordinate e)).comp ((measurable_pi_apply n).comp measurable_fst)
  have hm2 (n : ℕ) : Measurable (fun P : Path d × Path d => signedCoordinate e (P.2 n)) :=
    (measurable_of_countable (signedCoordinate e)).comp ((measurable_pi_apply n).comp measurable_snd)
  have hh1 : Measurable (fun P : Path d × Path d => dot (realPosition (P.1 q.1)) ℓ) :=
    (measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp ((measurable_pi_apply q.1).comp measurable_fst)
  have hh2 : Measurable (fun P : Path d × Path d => dot (realPosition (P.2 q.2)) ℓ) :=
    (measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp ((measurable_pi_apply q.2).comp measurable_snd)
  simp only [PairOscillationTest,Set.ofPred_exists,Set.ofPred_and]
  refine MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun r =>
    MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
    (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter ?_)))
  exact (measurable_fst (measurableSet_recordIndexPrefix ℓ r q.1)).inter
    ((measurable_snd (measurableSet_recordIndexPrefix ℓ r q.2)).inter
    ((measurable_fst (measurableSet_recordOrZeroPrefix ℓ s a)).inter
    ((measurable_snd (measurableSet_recordOrZeroPrefix ℓ s b)).inter
    ((measurableSet_eq_fun hh1 hh2).inter
    (measurableSet_lt measurable_const (((hm1 q.1).sub (hm2 q.2)).sub ((hm1 a).sub (hm2 b))).abs)))))

lemma pairOscillationTest_prefix {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (J : Set (ℕ × ℕ)) (z : ℝ) (q : ℕ × ℕ) :
    PairPrefixDetermined q.1 q.2 (PairOscillationTest ℓ e J z q) := by
  have hdir (P Q : Path d × Path d) (h1 : ∀ n ≤ q.1, P.1 n = Q.1 n)
      (h2 : ∀ n ≤ q.2, P.2 n = Q.2 n) (hP : P ∈ PairOscillationTest ℓ e J z q) :
      Q ∈ PairOscillationTest ℓ e J z q := by
    obtain ⟨s,r,a,b,hJ,hr,ha,hb,hr1,hr2,hs1,hs2,he,hz⟩ := hP
    refine ⟨s,r,a,b,hJ,hr,ha,hb,
      (recordIndexPrefix_prefix ℓ r q.1 P.1 Q.1 h1).mp hr1,
      (recordIndexPrefix_prefix ℓ r q.2 P.2 Q.2 h2).mp hr2,
      (recordOrZeroPrefix_prefix ℓ s a P.1 Q.1 (fun n hn => h1 n (hn.trans ha))).mp hs1,
      (recordOrZeroPrefix_prefix ℓ s b P.2 Q.2 (fun n hn => h2 n (hn.trans hb))).mp hs2,?_,?_⟩
    · rwa [← h1 q.1 le_rfl,← h2 q.2 le_rfl]
    · rwa [← h1 q.1 le_rfl,← h2 q.2 le_rfl,← h1 a ha,← h2 b hb]
  intro P Q h1 h2
  exact ⟨hdir P Q h1 h2,hdir Q P (fun n hn => (h1 n hn).symm) (fun n hn => (h2 n hn).symm)⟩

lemma pairOscillationTest_aligned {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (J : Set (ℕ × ℕ)) (z : ℝ) (q : ℕ × ℕ) :
    PairOscillationTest ℓ e J z q ⊆ AlignedRecordPrefix ℓ q := by
  rintro P ⟨_,r,_,_,_,hr,_,_,hr1,hr2,_,_,he,_⟩
  exact ⟨⟨r,hr,hr1,hr2⟩,he⟩

lemma independent_firstHit_aligned {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ r, 0 < r →
      P.1 ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r P.1) ∧
      P.2 ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r P.2) ∧
      dot (realPosition (recordIndexPosition ℓ r P.1)) ℓ =
        dot (realPosition (recordIndexPosition ℓ r P.2)) ℓ := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hs : ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ r, 0 < r →
      X ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r X) :=
    ae_all_iff.mpr fun r => ae_all_iff.mpr fun hr => conditioned_recordIndexTime_spec ν ℓ htrans hr
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
  have hNN := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_nearest_neighbor ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_nearest_neighbor ν)))
  have hs' := (Measure.quasiMeasurePreserving_fst.ae hs).and (Measure.quasiMeasurePreserving_snd.ae hs)
  filter_upwards [h0,hNN,hs'] with P h0 hNN hs r hr
  have h1 := hs.1 r hr
  have h2 := hs.2 r hr
  refine ⟨h1,h2,?_⟩
  have hs1 (j : ℕ) : height (P.1 (j+1)) ≤ height (P.1 j)+1 := by
    obtain ⟨v,hv⟩ := hNN.1 j
    rw [hv]; exact hstep _ _
  have hs2 (j : ℕ) : height (P.2 (j+1)) ≤ height (P.2 j)+1 := by
    obtain ⟨v,hv⟩ := hNN.2 j
    rw [hv]; exact hstep _ _
  change dot (realPosition (P.1 _)) ℓ = dot (realPosition (P.2 _)) ℓ
  rw [hproj,hproj,recordCount_eq_height_at_record ℓ height hproj P.1 hs1 h1.2.1,
    recordCount_eq_height_at_record ℓ height hproj P.2 hs2 h2.2.1,h0.1,h0.2,h1.2.2.1,h2.2.2.1]

lemma firstHitPairGap_prefix_test {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (J : Set (ℕ × ℕ)) (hJ : ∀ sr ∈ J, sr.1 ≤ sr.2) {z : ℝ} (hz : 0 ≤ z)
    {P : Path d × Path d}
    (hs : ∀ r, 0 < r → P.1 ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r P.1) ∧
      P.2 ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r P.2) ∧
      dot (realPosition (recordIndexPosition ℓ r P.1)) ℓ =
        dot (realPosition (recordIndexPosition ℓ r P.2)) ℓ)
    {s r : ℕ} (hsr : (s,r) ∈ J) (hbad : z < |firstHitPairGap ℓ e r P-firstHitPairGap ℓ e s P|) :
    P ∈ PairOscillationTest ℓ e J z (recordIndexTime ℓ r P.1,recordIndexTime ℓ r P.2) := by
  have hsr' := hJ _ hsr
  have hr : 0 < r := by
    by_contra! hr
    have : s = r := by omega
    simp only [this,sub_self,abs_zero] at hbad
    exact (not_lt_of_ge hz) hbad
  have h1 := hs r hr
  have hprev (X : Path d) (hX : ∀ a, 0 < a → X ∈ RecordIndexPrefix ℓ a (recordIndexTime ℓ a X)) :
      recordIndexTime ℓ s X ≤ recordIndexTime ℓ r X ∧
      X ∈ RecordOrZeroPrefix ℓ s (recordIndexTime ℓ s X) := by
    by_cases hs0 : s = 0
    · simp [hs0,recordIndexTime_zero,RecordOrZeroPrefix]
    · refine ⟨?_,by simpa [RecordOrZeroPrefix,hs0] using hX s (Nat.pos_of_ne_zero hs0)⟩
      by_contra! hh
      have := (recordIndexPrefix_time_lt_iff ℓ X (hX r hr) (hX s (Nat.pos_of_ne_zero hs0))).mp hh
      omega
  have hp1 := hprev P.1 (fun a ha => (hs a ha).1)
  have hp2 := hprev P.2 (fun a ha => (hs a ha).2.1)
  exact ⟨s,r,recordIndexTime ℓ s P.1,recordIndexTime ℓ s P.2,hsr,hr,hp1.1,hp2.1,
    h1.1,h1.2.1,hp1.2,hp2.2,h1.2.2,hbad⟩

theorem independent_firstHit_oscillation_transfer {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (J : Set (ℕ × ℕ)) (hJ : ∀ sr ∈ J, sr.1 ≤ sr.2) {z : ℝ} (hz : 0 ≤ z) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ
      {P | ∃ s r, (s,r) ∈ J ∧ z < |firstHitPairGap ℓ e r P-firstHitPairGap ℓ e s P|} ≤
    independentConditionedPairLaw ν ℓ {P | ∃ s r, (s,r) ∈ J ∧
      CommonTrueRecord ℓ P (recordIndexTime ℓ r P.1) (recordIndexTime ℓ r P.2) ∧
      z < |firstHitPairGap ℓ e r P-firstHitPairGap ℓ e s P|} := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  calc
    _ ≤ (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ
        (⋃ q, PairOscillationTest ℓ e J z q) := by
      apply mul_le_mul_right
      apply measure_mono_ae
      filter_upwards [independent_firstHit_aligned ν ℓ htrans height hproj hstep] with P hP hh
      obtain ⟨s,r,hsr,hbad⟩ := hh
      exact Set.mem_iUnion.mpr ⟨_,firstHitPairGap_prefix_test ℓ e J hJ hz hP hsr hbad⟩
    _ ≤ independentConditionedPairLaw ν ℓ
        (⋃ q, PairOscillationTest ℓ e J z q ∩ {P | CommonTrueRecord ℓ P q.1 q.2}) :=
      independent_exact_cut_transfer ν ℓ hp _ (measurableSet_pairOscillationTest ℓ e J z)
        (pairOscillationTest_prefix ℓ e J z) (pairOscillationTest_aligned ℓ e J z)
    _ ≤ _ := by
      apply measure_mono
      intro P hP
      obtain ⟨q,hq,htrue⟩ := Set.mem_iUnion.mp hP
      obtain ⟨s,r,a,b,hsr,_,_,_,hr1,hr2,hs1,hs2,_,hbad⟩ := hq
      have he1 := recordIndexTime_eq ℓ r q.1 P.1 hr1
      have he2 := recordIndexTime_eq ℓ r q.2 P.2 hr2
      have hs1' := recordOrZeroPrefix_time ℓ hs1
      have hs2' := recordOrZeroPrefix_time ℓ hs2
      refine ⟨s,r,hsr,by simpa only [he1,he2,Set.mem_ofPred_eq] using htrue,?_⟩
      simpa only [firstHitPairGap,recordIndexPosition,he1,he2,hs1',hs2'] using hbad

lemma commonBoundaryGap_eq_at_true {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (P : Path d × Path d) (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    {r : ℕ} (hs : 0 < r → P.1 ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r P.1))
    (ht : CommonTrueRecord ℓ P (recordIndexTime ℓ r P.1) (recordIndexTime ℓ r P.2)) :
    firstHitPairGap ℓ e r P = commonBoundaryGap ℓ e r P := by
  by_cases hr : r = 0
  · simp only [hr,firstHitPairGap,recordIndexPosition,recordIndexTime_zero,h0,h0',
      sub_self,commonBoundaryGap,renewalCount_zero,realPartialSum_zero]
  obtain ⟨k,hk⟩ := commonTrueRecord_eq_commonTimes ℓ P h0 h0' hP ht
  have hc : renewalSum (fun j => commonWidthProcess ℓ j P) k = r := by
    change (∑ i ∈ Finset.range k, wordRecordCount ℓ (commonWords ℓ P i).1) = r
    rw [← recordCount_commonTimes ℓ P h0 h0' hP k,hk]
    exact (hs (Nat.pos_of_ne_zero hr)).2.2.1
  have hpos (j : ℕ) : 0 < commonWidthProcess ℓ j P := commonWordWidth_positive ℓ _ _ (hP j)
  rw [commonBoundaryGap,← hc,renewalCount_at_sum _ hpos,← common_coordinate_sum ℓ e P h0 h0' hP k,hk]
  rw [hc]
  rfl

lemma independent_commonBoundary_at_true {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ r,
      CommonTrueRecord ℓ P (recordIndexTime ℓ r P.1) (recordIndexTime ℓ r P.2) →
      firstHitPairGap ℓ e r P = commonBoundaryGap ℓ e r P := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
  filter_upwards [h0,independent_firstHit_aligned ν ℓ htrans height hproj hstep,
    independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep] with P h0 hs hP r ht
  exact commonBoundaryGap_eq_at_true ℓ e P h0.1 h0.2 hP (fun hr => (hs r hr).1) ht

theorem independent_firstHit_gap_transfer {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (J : Set (ℕ × ℕ)) (hJ : ∀ sr ∈ J, sr.1 ≤ sr.2) {z : ℝ} (hz : 0 ≤ z) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ
      {P | ∃ s r, (s,r) ∈ J ∧ z < |firstHitPairGap ℓ e r P-firstHitPairGap ℓ e s P|} ≤
    independentConditionedPairLaw ν ℓ {P | ∃ s r, (s,r) ∈ J ∧
      z < |commonBoundaryGap ℓ e r P-commonBoundaryGap ℓ e s P|+
        |firstHitPairGap ℓ e s P-commonBoundaryGap ℓ e s P|} := by
  apply (independent_firstHit_oscillation_transfer ν ℓ e htrans height hproj hstep J hJ hz).trans
  apply measure_mono_ae
  filter_upwards [independent_commonBoundary_at_true ν ℓ e htrans height hproj hstep] with P hP hh
  obtain ⟨s,r,hJ,ht,hbad⟩ := hh
  refine ⟨s,r,hJ,hbad.trans_le ?_⟩
  rw [hP r ht,abs_sub_comm (firstHitPairGap ℓ e s P)]
  exact abs_sub_le _ (commonBoundaryGap ℓ e s P) _

lemma heightBlockRelation_order (H b : ℕ) :
    ∀ sr ∈ HeightBlockRelation H b, sr.1 ≤ sr.2 := by
  rintro ⟨s,r⟩ ⟨_,hs⟩
  change s = r / b * b at hs
  simpa only [hs] using Nat.div_mul_le_self r b

lemma heightGap_subset {Ω : Type*} (F B : ℕ → Ω → ℝ) {H b M : ℕ}
    (hM : H/b ≤ M) {a : ℝ} :
    HeightGapEvent F B H (6*a) ⊆
      HeightOscillation F (HeightBlockRelation H b) (2*a) ∪
        HeightOscillation B (HeightBlockRelation H b) a ∪ BlockDecoration F B M b a := by
  rintro ω ⟨h,hh,hbig⟩
  by_contra hnot
  have hnot : ω ∉ HeightOscillation F (HeightBlockRelation H b) (2*a) ∧
      ω ∉ HeightOscillation B (HeightBlockRelation H b) a ∧ ω ∉ BlockDecoration F B M b a := by
    simpa only [Set.mem_union,not_or,and_assoc] using hnot
  let s := h/b*b
  have hsJ : (s,h) ∈ HeightBlockRelation H b := ⟨hh,rfl⟩
  have ha : |F h ω-F s ω| ≤ 2*a := le_of_not_gt (fun hb => hnot.1 ⟨s,h,hsJ,hb⟩)
  have hb : |B h ω-B s ω| ≤ a := le_of_not_gt (fun hb => hnot.2.1 ⟨s,h,hsJ,hb⟩)
  have hd : |F s ω-B s ω| ≤ a := le_of_not_gt (fun hb => hnot.2.2
    ⟨h/b,(Nat.div_le_div_right hh).trans hM,hb⟩)
  have he := (abs_sub_le (F h ω) (F s ω) (B h ω)).trans
    (add_le_add le_rfl (abs_sub_le (F s ω) (B s ω) (B h ω)))
  rw [abs_sub_comm (B s ω)] at he
  have hapos : 0 ≤ a := (abs_nonneg _).trans hb
  linarith

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightIncrement
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma block_transfer_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F B : ℕ → Ω → ℝ) {q : ℝ} (hq : 0 ≤ q) {H b M : ℕ} (hM : H/b ≤ M)
    {a : ℝ}
    (htransfer : q*μ.real (HeightOscillation F (HeightBlockRelation H b) (2*a)) ≤
      μ.real {ω | ∃ s h, (s,h) ∈ HeightBlockRelation H b ∧
        2*a < |B h ω-B s ω|+|F s ω-B s ω|}) :
    q*μ.real (HeightGapEvent F B H (6*a)) ≤
      (q+1)*(μ.real (HeightOscillation B (HeightBlockRelation H b) a)+
        μ.real (BlockDecoration F B M b a)) := by
  have hs : {ω | ∃ s h, (s,h) ∈ HeightBlockRelation H b ∧
      2*a < |B h ω-B s ω|+|F s ω-B s ω|} ⊆
      HeightOscillation B (HeightBlockRelation H b) a ∪ BlockDecoration F B M b a := by
    rintro ω ⟨s,h,hsj,hbig⟩
    by_cases hb : a < |B h ω-B s ω|
    · exact Or.inl ⟨s,h,hsj,hb⟩
    · apply Or.inr
      refine ⟨h/b,(Nat.div_le_div_right hsj.1).trans hM,?_⟩
      rw [← hsj.2]
      have := le_of_not_gt hb
      linarith
  have ht := htransfer.trans ((measureReal_mono hs (measure_ne_top _ _)).trans
    (measureReal_union_le (μ := μ) _ _))
  have hg := (measureReal_mono (heightGap_subset F B hM (a := a)) (measure_ne_top _ _)).trans
    ((measureReal_union_le (μ := μ) _ _).trans
      (add_le_add (measureReal_union_le (μ := μ) _ _) le_rfl))
  have hmul := mul_le_mul_of_nonneg_left hg hq
  nlinarith

lemma blockDecoration_finite_union {Ω : Type*} (F B : ℕ → Ω → ℝ) (M b : ℕ) (z : ℝ) :
    BlockDecoration F B M b z = ⋃ j ∈ Finset.range (M+1), {ω | z < |F (j*b) ω-B (j*b) ω|} := by
  ext ω
  simp only [BlockDecoration,Set.mem_ofPred_eq,Set.mem_iUnion,Finset.mem_range,Nat.lt_succ_iff,exists_prop]

lemma blockDecoration_small {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F B : ℕ → Ω → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (hdec : ∀ h : ℕ → ℕ, TendstoInMeasure μ (fun i ω => (F (h i) ω-B (h i) ω)/r i) atTop 0)
    (M : ℕ) (b : ℕ → ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i => μ.real (BlockDecoration F B M (b i) (a*r i))) atTop (𝓝 0) := by
  have hj (j : ℕ) : Tendsto (fun i => μ.real {ω | a*r i < |F (j*b i) ω-B (j*b i) ω|}) atTop (𝓝 0) := by
    have ht := tendstoInMeasure_iff_measureReal_norm.mp (hdec (fun i => j*b i)) a ha
    simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] at ht
    apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ ht
    filter_upwards [hr.eventually (eventually_gt_atTop (0:ℝ))] with i hri
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    simp only [Set.mem_ofPred_eq,abs_div,abs_of_pos hri]
    exact ((lt_div_iff₀ hri).2 hω).le
  have ht := tendsto_finsetSum (Finset.range (M+1)) (fun j _ => hj j)
  simp only [Finset.sum_const_zero] at ht
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro i
  rw [blockDecoration_finite_union]
  exact measureReal_biUnion_finset_le _ _

lemma renewal_height_block_subset {Ω : Type*} (X : ℕ → Ω → ℝ) (L : ℕ → Ω → ℕ)
    {n T c δ z : ℝ} (hn : 1 ≤ n) (hT : 0 ≤ T) (hc : 1 ≤ c) (hδ : 0 ≤ δ) (hδn : 4 ≤ δ*n) :
    HeightOscillation (fun h ω => realPartialSum (fun k => X k ω)
      (renewalCount (fun k => L k ω) h)) (HeightBlockRelation (⌊T*n⌋₊+1) ⌊(δ/4)*n⌋₊) z ⊆
    {ω | ∃ h : ℕ, (h:ℝ) ≤ (T+1)*n ∧
      δ/8 < |(renewalCount (fun j => L j ω) h : ℝ)/n-(h:ℝ)/(c*n)|} ∪
      GridOscillation X ⌊(T+1)*n⌋₊ ⌊δ*n⌋₊ z := by
  rintro ω ⟨s,h,hsj,hbad⟩
  by_cases hclock : ω ∈ {ω | ∃ h : ℕ, (h:ℝ) ≤ (T+1)*n ∧
      δ/8 < |(renewalCount (fun j => L j ω) h : ℝ)/n-(h:ℝ)/(c*n)|}
  · exact Or.inl hclock
  apply Or.inr
  let C := renewalCount (fun k => L k ω)
  have hn0 : 0 < n := by linarith
  have hc0 : 0 < c := by linarith
  have hs : s ≤ h := heightBlockRelation_order _ _ _ hsj
  have hH : (h:ℝ) ≤ (T+1)*n := by
    have := (show (h:ℝ) ≤ (⌊T*n⌋₊:ℝ)+1 by exact_mod_cast hsj.1)
    have hf := Nat.floor_le (mul_nonneg hT hn0.le)
    nlinarith
  have hsH := (Nat.cast_le.mpr hs).trans hH
  have hb : (h:ℝ)-(s:ℝ) ≤ (δ/4)*n := by
    have hrem : h-s = h % ⌊(δ/4)*n⌋₊ := by
      have he : s = h / ⌊(δ/4)*n⌋₊ * ⌊(δ/4)*n⌋₊ := hsj.2
      have heq : h % ⌊(δ/4)*n⌋₊ + h / ⌊(δ/4)*n⌋₊ * ⌊(δ/4)*n⌋₊ = h := by
        simpa only [Nat.mul_comm] using Nat.mod_add_div h ⌊(δ/4)*n⌋₊
      omega
    have hb0 : 0 < ⌊(δ/4)*n⌋₊ := by
      apply Nat.succ_le_iff.mp
      apply Nat.le_floor
      norm_num
      linarith
    have hh : h-s ≤ ⌊(δ/4)*n⌋₊ := by rw [hrem]; exact (Nat.mod_lt _ hb0).le
    have hh' : (h:ℝ)-(s:ℝ) ≤ (⌊(δ/4)*n⌋₊:ℝ) := by
      rw [← Nat.cast_sub hs]
      exact_mod_cast hh
    exact hh'.trans (Nat.floor_le (mul_nonneg (by positivity) hn0.le))
  have hclock' (j : ℕ) (hj : (j:ℝ) ≤ (T+1)*n) : |(C j:ℝ)-(j:ℝ)/c| ≤ δ*n/8 := by
    have he : |(C j:ℝ)/n-(j:ℝ)/(c*n)| ≤ δ/8 :=
      le_of_not_gt (fun hh => hclock ⟨j,hj,hh⟩)
    have heq : ((C j:ℝ)/n-(j:ℝ)/(c*n))*n = (C j:ℝ)-(j:ℝ)/c := by field_simp
    have he' := mul_le_mul_of_nonneg_right he hn0.le
    have he'' : |((C j:ℝ)/n-(j:ℝ)/(c*n))*n| ≤ δ/8*n := by
      simpa only [abs_mul,abs_of_pos hn0] using he'
    rw [heq] at he''
    convert he'' using 1 <;> first | rfl | ring
  have hch := (abs_le.mp (hclock' h hH)).2
  have hcs := (abs_le.mp (hclock' s hsH)).1
  have hdiv : ((h:ℝ)-(s:ℝ))/c ≤ (h:ℝ)-(s:ℝ) := div_le_self (sub_nonneg.mpr (Nat.cast_le.mpr hs)) hc
  have hd : (C h:ℝ)-(C s:ℝ) ≤ δ*n := by
    have he : (h:ℝ)/c-(s:ℝ)/c = ((h:ℝ)-(s:ℝ))/c := (sub_div _ _ _).symm
    have hδn := mul_nonneg hδ hn0.le
    linarith
  have hC := renewalCount_monotone (fun k => L k ω) hs
  have hdiff : C h-C s ≤ ⌊δ*n⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_sub hC]
    exact hd
  refine ⟨C s,?_,C h,?_,hC,by omega,hbad⟩
  · exact (renewalCount_le _ _).trans (Nat.le_floor hsH)
  · exact (renewalCount_le _ _).trans (Nat.le_floor hH)

lemma gaussian_renewal_block_modulus {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k))
    (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω) {c : ℝ} (hc : 1 ≤ c)
    (hmean : ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => (renewalSum (fun j => L j ω) k : ℝ)/k)
      atTop (𝓝 c)) (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T a β : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in atTop,
      μ.real (HeightOscillation (fun h ω => realPartialSum (fun k => X k ω)
        (renewalCount (fun k => L k ω) h))
        (HeightBlockRelation (⌊T*fluctuationScale μ (X 0) (r i)⌋₊+1)
          ⌊δ*fluctuationScale μ (X 0) (r i)⌋₊) (a*r i)) ≤ β := by
  let n := fun i => fluctuationScale μ (X 0) (r i)
  have hn : Tendsto n atTop atTop := (fluctuationScale_tendsto μ (X 0) (hX 0) hI hne).comp hr.1
  obtain ⟨δ,hδ,hgrid⟩ := gaussian_grid_modulus μ X hX hind hident hsym hI hne r hr
    (by linarith : 0 ≤ T+1) ha (by linarith : 0 < β/2)
  let A := fun i => {ω | ∃ h : ℕ, (h:ℝ) ≤ (T+1)*n i ∧
    δ/8 < |(renewalCount (fun j => L j ω) h : ℝ)/n i-(h:ℝ)/(c*n i)|}
  have hclock : Tendsto (fun i => μ (A i)) atTop (𝓝 0) :=
    renewalCount_uniform_in_probability μ L hL hpos (by linarith) hmean n hn
      (by linarith) (by positivity)
  have hclockR : Tendsto (fun i => μ.real (A i)) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero,Function.comp_def,Measure.real] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hclock
  have hevent := (tendsto_order.mp hclockR).2 (β/2) (by linarith)
  refine ⟨δ/4,by positivity,?_⟩
  filter_upwards [hgrid,hevent,hn.eventually (eventually_ge_atTop (1:ℝ)),
    (hn.const_mul_atTop hδ).eventually (eventually_ge_atTop (4:ℝ))] with i hg ha hni hdni
  have hs := renewal_height_block_subset X L hni hT hc hδ.le hdni (z := a*r i)
  have hh := (measureReal_mono hs (measure_ne_top _ _)).trans (measureReal_union_le (μ := μ) _ _)
  change μ.real (A i) < β/2 at ha
  change μ.real (GridOscillation X ⌊(T+1)*n i⌋₊ ⌊δ*n i⌋₊ (a*r i)) ≤ β/2 at hg
  exact hh.trans (by linarith)

theorem heightGap_small_of_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F B : ℕ → Ω → ℝ)
    (r n : ℕ → ℝ) (hr : Tendsto r atTop atTop) (hn : Tendsto n atTop atTop)
    {q T : ℝ} (hq : 0 < q) (hT : 0 ≤ T)
    (htransfer : ∀ J : Set (ℕ × ℕ), (∀ sr ∈ J, sr.1 ≤ sr.2) → ∀ z, 0 ≤ z →
      q*μ.real (HeightOscillation F J z) ≤
        μ.real {ω | ∃ s h, (s,h) ∈ J ∧ z < |B h ω-B s ω|+|F s ω-B s ω|})
    (hdec : ∀ h : ℕ → ℕ, TendstoInMeasure μ (fun i ω => (F (h i) ω-B (h i) ω)/r i) atTop 0)
    (hmod : ∀ a β : ℝ, 0 < a → 0 < β → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in atTop,
      μ.real (HeightOscillation B (HeightBlockRelation (⌊T*n i⌋₊+1) ⌊δ*n i⌋₊) (a*r i)) ≤ β)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun i => μ.real (HeightGapEvent F B (⌊T*n i⌋₊+1) (ε*r i))) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  · intro β hβ
    let a := ε/6
    let b := β*q/(4*(q+1))
    have ha : 0 < a := by dsimp [a] <;> positivity
    have hb : 0 < b := by dsimp [b] <;> positivity
    obtain ⟨δ,hδ,hm⟩ := hmod a b ha hb
    obtain ⟨M,hM⟩ := exists_nat_gt ((T+1)/δ)
    have hM' : T+1 < (M:ℝ)*δ := (div_lt_iff₀ hδ).mp hM
    have hcovered := eventually_floor_horizon_covered n hn (by linarith : 0 ≤ T+1) hδ M hM'
    have hd := blockDecoration_small μ F B r hr hdec M (fun i => ⌊δ*n i⌋₊) ha
    have hdevent := (tendsto_order.mp hd).2 b hb
    filter_upwards [hm,hcovered,hdevent,hr.eventually (eventually_gt_atTop (0:ℝ)),
      hn.eventually (eventually_ge_atTop (1:ℝ))] with i hmi hci hdi hri hni
    have hH : ⌊T*n i⌋₊+1 ≤ ⌊(T+1)*n i⌋₊ := by
      apply Nat.le_floor
      push_cast
      have hf := Nat.floor_le (mul_nonneg hT (by linarith : 0 ≤ n i))
      nlinarith
    have hdiv : (⌊T*n i⌋₊+1)/⌊δ*n i⌋₊ ≤ M := by
      exact ((Nat.div_lt_iff_lt_mul hci.1).mpr (hH.trans_lt hci.2)).le
    have hz : 0 ≤ 2*(a*r i) := by positivity
    have ht := block_transfer_bound μ F B hq.le hdiv
      (htransfer _ (heightBlockRelation_order _ _) (2*(a*r i)) hz)
    have he : 6*(a*r i) = ε*r i := by dsimp [a] <;> ring
    rw [he] at ht
    have hfin : q*μ.real (HeightGapEvent F B (⌊T*n i⌋₊+1) (ε*r i)) < q*β := by
      have hbq : (q+1)*(2*b) = q*β/2 := by dsimp [b]; field_simp <;> ring
      have := mul_lt_mul_of_pos_left (add_lt_add_of_le_of_lt hmi hdi) (by linarith : 0 < q+1)
      rw [← two_mul,hbq] at this
      nlinarith
    exact (mul_lt_mul_iff_of_pos_left hq).mp hfin

theorem transverse_firstHit_uniform_error {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    Tendsto (fun i => (independentConditionedPairLaw ν (realPosition (step e))).real
      (HeightGapEvent (firstHitPairGap (realPosition (step e)) f)
        (commonBoundaryGap (realPosition (step e)) f)
        (⌊T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)⌋₊+1) (ε*r i))) atTop (𝓝 0) := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ (ne_of_gt hp)
  have hi := independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e)
    htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hn := (fluctuationScale_tendsto μ (commonIncrementProcess ℓ f 0)
    (measurable_commonIncrementProcess ℓ f 0) hi hne).comp hr.1
  apply heightGap_small_of_transfer μ (firstHitPairGap ℓ f) (commonBoundaryGap ℓ f)
    r _ hr.1 hn (q := (annealedLaw ν (NoDrop ℓ 0)).toReal^2)
    (sq_pos_of_pos (ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _))) hT _ _ _ hε
  · intro J hJ z hz
    have hh := independent_firstHit_gap_transfer ν ℓ f htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) J hJ hz
    have hh' := ENNReal.toReal_mono (measure_ne_top _ _) hh
    simpa only [HeightOscillation,Measure.real,ENNReal.toReal_mul,ENNReal.toReal_pow,μ] using hh'
  · intro h
    exact independent_firstHit_decoration_small ν ℓ f htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) r hr.1 h
  · intro a β ha hβ
    apply gaussian_renewal_block_modulus μ (commonIncrementProcess ℓ f)
      (measurable_commonIncrementProcess ℓ f)
      (commonIncrements_independent ν ℓ htrans (signedHeight e)
        (signedHeight_projection e) (signedHeight_step_le e) f)
      (commonIncrements_identDistrib ν ℓ htrans (signedHeight e)
        (signedHeight_projection e) (signedHeight_step_le e) f)
      (independent_commonWordIncrement_symmetric ν ℓ htrans f) hi hne
      (commonWidthProcess ℓ) (measurable_commonWidthProcess ℓ) _
      (commonMeanWidth_ge_one ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e))
      (commonWidth_strongLaw ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e))
      r hr hT ha hβ
    filter_upwards [independent_conditioned_all_firstPairWords ν ℓ htrans
      (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)] with P hP k
    exact commonWordWidth_positive ℓ _ _ (hP k)

lemma realPartialSum_heightIncrement (F : ℕ → ℝ) (h : ℕ) :
    realPartialSum (heightIncrement F) h = F h-F 0 := by
  induction h with
  | zero => simp [realPartialSum]
  | succ h ih => rw [realPartialSum_succ,ih,heightIncrement]; ring

lemma height_polygon_difference_le (F B : ℕ → ℝ) (h0 : F 0 = B 0)
    {r n T a : ℝ} (hr : 0 < r) (hn : 0 ≤ n) (hT : 0 ≤ T)
    (hgap : ∀ h ≤ ⌊T*n⌋₊+1, |F h-B h| ≤ a*r) :
    ‖scaledPolygon (heightIncrement F) r n T-scaledPolygon (heightIncrement B) r n T‖ ≤ a := by
  apply (ContinuousMap.norm_le_of_nonempty _).mpr
  intro t
  let u := T*n*(t:ℝ)
  let j := ⌊u⌋₊
  have hu : 0 ≤ u := mul_nonneg (mul_nonneg hT hn) t.2.1
  have huT : u ≤ T*n := mul_le_of_le_one_right (mul_nonneg hT hn) t.2.2
  have hj : j < ⌊T*n⌋₊+1 := Nat.lt_succ_of_le (Nat.floor_mono huT)
  have hj0 : (j:ℝ) ≤ u := Nat.floor_le hu
  have hj1 : u < (j:ℝ)+1 := Nat.lt_floor_add_one u
  have hdet := abs_convex_sub_le (q := u-j) (by linarith) (by linarith)
    (z := (0:ℝ)) (by simpa only [sub_zero] using hgap j hj.le)
    (by simpa only [sub_zero] using hgap (j+1) hj)
  have he : linearPolygon (heightIncrement F) (⌊T*n⌋₊+1) u-
      linearPolygon (heightIncrement B) (⌊T*n⌋₊+1) u =
      (1-(u-j))*(F j-B j)+(u-j)*(F (j+1)-B (j+1)) := by
    rw [linearPolygon_formula _ _ hu hj,linearPolygon_formula _ _ hu hj,
      realPartialSum_heightIncrement,realPartialSum_heightIncrement]
    simp only [heightIncrement,h0]
    dsimp only [j]
    ring
  rw [sub_zero,← he] at hdet
  simp only [ContinuousMap.sub_apply,Real.norm_eq_abs,scaledPolygon_apply]
  rw [← sub_div,abs_div,abs_of_pos hr]
  exact (div_le_iff₀ hr).2 hdet

lemma height_polygon_difference_small {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F B : ℕ → Ω → ℝ)
    (h0 : ∀ᵐ ω ∂μ, F 0 ω = B 0 ω) (r n : ℕ → ℝ)
    (hr : Tendsto r atTop atTop) (hn : Tendsto n atTop atTop) {T : ℝ} (hT : 0 ≤ T)
    (hgap : ∀ ε, 0 < ε → Tendsto (fun i => μ.real
      (HeightGapEvent F B (⌊T*n i⌋₊+1) (ε*r i))) atTop (𝓝 0)) :
    TendstoInMeasure μ (fun i ω => scaledPolygon (heightIncrement (fun h => F h ω)) (r i) (n i) T-
      scaledPolygon (heightIncrement (fun h => B h ω)) (r i) (n i) T) atTop 0 := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  simp only [Pi.zero_apply,sub_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ (hgap (ε/2) (by linarith))
  filter_upwards [hr.eventually (eventually_gt_atTop (0:ℝ)),
    hn.eventually (eventually_ge_atTop (0:ℝ))] with i hri hni
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae _)
  filter_upwards [h0] with ω h0 hbig
  by_contra hnot
  have hb (h : ℕ) (hh : h ≤ ⌊T*n i⌋₊+1) : |F h ω-B h ω| ≤ ε/2*r i :=
    le_of_not_gt (fun hbad => hnot ⟨h,hh,hbad⟩)
  have hh := height_polygon_difference_le (fun h => F h ω) (fun h => B h ω) h0 hri hni hT hb
  change ε ≤ ‖scaledPolygon (heightIncrement (fun h => F h ω)) (r i) (n i) T-
    scaledPolygon (heightIncrement (fun h => B h ω)) (r i) (n i) T‖ at hbig
  linarith

theorem transverse_firstHit_path_error {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    TendstoInMeasure (independentConditionedPairLaw ν (realPosition (step e))) (fun i P =>
      scaledPolygon (heightIncrement (fun h => firstHitPairGap (realPosition (step e)) f h P))
        (r i) (fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)) T-
      scaledPolygon (renewalRewardIncrement (fun k => commonIncrementProcess (realPosition (step e)) f k P)
        (fun k => commonWidthProcess (realPosition (step e)) k P))
        (r i) (fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)) T) atTop 0 := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ (ne_of_gt hp)
  have hi := independent_commonWordIncrement_integrable ν hue ℓ (signed_direction_unit e)
    htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hn := (fluctuationScale_tendsto μ (commonIncrementProcess ℓ f 0)
    (measurable_commonIncrementProcess ℓ f 0) hi hne).comp hr.1
  apply height_polygon_difference_small μ (firstHitPairGap ℓ f) (commonBoundaryGap ℓ f) _ r _ hr.1 hn hT
  · exact fun ε hε => transverse_firstHit_uniform_error ν hue e f hef htrans r hr hT hε

  · let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ (ne_of_gt hp)
    have hac := conditionedLaw_absolutelyContinuous ν ℓ
    have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
      (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
    filter_upwards [h0] with P hP
    simp only [firstHitPairGap,recordIndexPosition,recordIndexTime_zero,hP.1,hP.2,sub_self,
      commonBoundaryGap,renewalCount_zero,realPartialSum_zero]

theorem transverse_firstHit_path_limit_oai {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    letI : IsProbabilityMeasure (independentConditionedPairLaw ν (realPosition (step e))) :=
      independentConditionedPairLaw_probability ν _
        (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i P => scaledPolygon
        (heightIncrement (fun h => firstHitPairGap (realPosition (step e)) f h P)) (r i)
        (fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)) T)
        atTop id (fun _ => independentConditionedPairLaw ν (realPosition (step e))) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun f : C(unitInterval,ℝ) => I.restrict f) =
          gaussianPathFiniteLaw (T/commonMeanWidth ν (realPosition (step e))) I := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  obtain ⟨W,hW,hf⟩ := transverse_common_boundary_path_limit ν hue e f hef htrans r hr hT
  refine ⟨W,?_,hf⟩
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ id hW
  · exact transverse_firstHit_path_error ν hue e f hef htrans r hr hT
  · intro i
    exact (measurable_scaledPolygon _
      (measurable_heightIncrement (firstHitPairGap ℓ f) (measurable_firstHitPairGap ℓ f)) _ _ _).aemeasurable

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.transverse_firstHit_path_limit_oai := @OAI.DirectionalTransience.transverse_firstHit_path_limit_oai
