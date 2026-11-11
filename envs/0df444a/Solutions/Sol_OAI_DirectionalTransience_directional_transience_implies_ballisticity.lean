-- Prove2me | solution 1 for OAI.DirectionalTransience.directional_transience_implies_ballisticity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:53:44.334968+00:00
-- url     : https://prove2.me/submissions/52539b36-46b7-45c8-bc2d-3187c639a031

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Theorems.Thm_OAI_DirectionalTransience_conditioned_wordRadius_integrable
import Theorems.Thm_OAI_DirectionalTransience_crossing_failure_rapidDecay
import Theorems.Thm_OAI_DirectionalTransience_stripTime_rapidDecay

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

lemma height_le_recordCount {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hstep : ∀ n, dot (realPosition (X (n+1))) ℓ ≤ dot (realPosition (X n)) ℓ + 1)
    (n : ℕ) : dot (realPosition (X n)) ℓ - dot (realPosition (X 0)) ℓ ≤
      (recordCount ℓ X n : ℝ) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      by_cases hr : StrictRecord ℓ X (n+1)
      · rw [recordCount_succ, ite_eq_left hr, Nat.cast_add, Nat.cast_one]
        have := ih n (by omega)
        linarith [hstep n]
      · obtain ⟨j, hj, hjh⟩ : ∃ j < n+1,
            dot (realPosition (X (n+1))) ℓ ≤ dot (realPosition (X j)) ℓ := by
          simpa only [StrictRecord, not_forall, exists_prop, not_lt] using hr
        have hle : (recordCount ℓ X j : ℝ) ≤ (recordCount ℓ X (n+1) : ℝ) :=
          Nat.cast_le.mpr (recordCount_mono ℓ X hj.le)
        linarith [ih j hj]

lemma wordHeightGain_le_recordCount {d : ℕ} (ℓ : Vector d)
    (hℓ : ∀ i, |ℓ i| ≤ 1) (w : List (Direction d)) :
    wordHeightGain ℓ w ≤ (wordRecordCount ℓ w : ℝ) := by
  have hs (n : ℕ) : dot (realPosition (wordPath 0 w (n+1))) ℓ ≤
      dot (realPosition (wordPath 0 w n)) ℓ + 1 := by
    rcases wordPath_step_or_stay 0 w n with he | ⟨e, he⟩
    · rw [he]; linarith
    · rw [he, dot_realPosition_add, dot_step]
      have hl := (abs_le.mp (hℓ e.1))
      split <;> linarith
  simpa only [wordHeightGain, wordRecordCount, wordPath_zero, dot, realPosition,
    Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, sub_zero] using
    height_le_recordCount ℓ (wordPath 0 w) hs w.length

lemma wordHeightGain_positive {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (hw : AdmissibleTrueWord ℓ w) : 0 < wordHeightGain ℓ w := by
  simpa only [wordPath_zero, dot, realPosition, Pi.zero_apply, Int.cast_zero,
    zero_mul, Finset.sum_const_zero, wordHeightGain] using (hw.2.1 0 hw.1).2

lemma conditioned_wordHeightGain_moments {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hℓ : ∀ i, |ℓ i| ≤ 1) (htrans : DirectionallyTransient ν ℓ) :
    Integrable (fun X => wordHeightGain ℓ (firstWord ℓ X)) (conditionedLaw ν ℓ) ∧
      0 < (∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂conditionedLaw ν ℓ) ∧
      (∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂conditionedLaw ν ℓ) ≤
        1 / (annealedLaw ν).real (NoDrop ℓ 0) := by
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ (ne_of_gt hp)
  have hm : Measurable (fun X => wordHeightGain ℓ (firstWord ℓ X)) :=
    (measurable_of_countable (wordHeightGain ℓ)).comp (measurable_firstWord ℓ)
  have hpos : ∀ᵐ X ∂conditionedLaw ν ℓ, 0 < wordHeightGain ℓ (firstWord ℓ X) := by
    filter_upwards [conditioned_all_firstWords ν ℓ htrans] with X hX
    have he := hX 0
    simp only [Function.iterate_zero, id_eq, regenerationWords] at he
    exact wordHeightGain_positive ℓ _
      ((firstTrueWord_characterization ℓ _ X he.2.1).mp ⟨he.1, he.2.2⟩).1
  obtain ⟨hcount, hbound⟩ := conditioned_wordRecordCount_integrable ν ℓ htrans
  have hint : Integrable (fun X => wordHeightGain ℓ (firstWord ℓ X)) (conditionedLaw ν ℓ) := by
    apply hcount.mono' hm.aestronglyMeasurable
    filter_upwards [hpos] with X hX
    rw [Real.norm_eq_abs, abs_of_pos hX]
    exact wordHeightGain_le_recordCount ℓ hℓ _
  refine ⟨hint, ?_, (integral_mono_ae hint hcount
    (Filter.Eventually.of_forall fun X => wordHeightGain_le_recordCount ℓ hℓ _)).trans hbound⟩
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun _ h => h.le) hint]
  have he : Function.support (fun X => wordHeightGain ℓ (firstWord ℓ X)) =ᵐ[conditionedLaw ν ℓ]
      Set.univ := by
    filter_upwards [hpos] with X hX
    apply propext
    change (wordHeightGain ℓ (firstWord ℓ X) ≠ 0) ↔ True
    exact iff_true_intro (ne_of_gt hX)
  rw [measure_congr he, measure_univ]
  exact zero_lt_one

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

lemma wordRadius_bound {d : ℕ} (w : List (Direction d)) {j : ℕ} (hj : j ≤ w.length) :
    ‖latticeVector (wordPath 0 w j)‖ ≤ wordRadius w := by
  classical
  exact Finset.le_sup' (fun j => ‖latticeVector (wordPath 0 w j)‖)
    (Finset.mem_range.mpr (by omega))

lemma measurable_wordRadius {d : ℕ} : Measurable (wordRadius (d := d)) := measurable_of_countable _

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

lemma conditioned_regenerationSupport {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ RegenerationSupport ℓ := by
  filter_upwards [(conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν),
    conditioned_all_firstWords ν ℓ htrans] with X h0 hX
  exact ⟨h0,hX⟩

lemma prefix_favourable_gain {d : ℕ} (μ : Measure (Path d))
    (E B : Set (Path d)) (n : ℕ) (p : ℝ≥0∞)
    (hE : PrefixDetermined n E)
    (hfav : ∀ f ∈ E, ∃ A : Set (Path d), MeasurableSet A ∧ A ⊆ pathCylinder f n ∧
      Disjoint B A ∧ μ A = μ (pathCylinder f n)*p) :
    μ (B∩E)+μ E*p ≤ μ E := by
  classical
  rw [measure_partition_prefix μ (B∩E) n, measure_partition_prefix μ E n,
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro f
  let g := extendPrefix n f
  by_cases hg : g ∈ E
  · obtain ⟨A,hA,hAC,hBA,hm⟩ := hfav g hg
    have hc : E ∩ pathCylinder g n = pathCylinder g n := by
      rw [prefixDetermined_inter_cylinder E n hE g, ite_eq_left hg]
    have he : (B∩E)∩pathCylinder g n = B∩pathCylinder g n := by rw [Set.inter_assoc, hc]
    change μ ((B∩E)∩pathCylinder g n)+μ (E∩pathCylinder g n)*p ≤ μ (E∩pathCylinder g n)
    rw [he,hc,← hm]
    have hd : Disjoint (B∩pathCylinder g n) A := hBA.mono_left Set.inter_subset_left
    rw [← measure_union hd hA]
    exact measure_mono (Set.union_subset Set.inter_subset_right hAC)
  · have hc : E∩pathCylinder g n = ∅ := by
      rw [prefixDetermined_inter_cylinder E n hE g, ite_eq_right hg]
    have he : (B∩E)∩pathCylinder g n = ∅ := by rw [Set.inter_assoc,hc,Set.inter_empty]
    change μ ((B∩E)∩pathCylinder g n)+μ (E∩pathCylinder g n)*p ≤ μ (E∩pathCylinder g n)
    rw [he,hc,measure_empty,zero_mul,zero_add]

lemma stopping_prefix_favourable_gain {d : ℕ} (μ : Measure (Path d))
    (E : ℕ → Set (Path d)) (B : Set (Path d)) (p : ℝ≥0∞)
    (hE : ∀ n, PrefixDetermined n (E n)) (hm : ∀ n, MeasurableSet (E n))
    (hd : Pairwise (fun n m => Disjoint (E n) (E m))) (hB : MeasurableSet B)
    (hsub : B ⊆ ⋃ n,E n)
    (hfav : ∀ n f, f ∈ E n → ∃ A : Set (Path d), MeasurableSet A ∧ A ⊆ pathCylinder f n ∧
      Disjoint B A ∧ μ A = μ (pathCylinder f n)*p) :
    μ B+μ (⋃ n,E n)*p ≤ μ (⋃ n,E n) := by
  have hBu : B = ⋃ n,B∩E n := by
    ext X
    simp only [Set.mem_iUnion,Set.mem_inter_iff]
    exact ⟨fun h => by obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (hsub h); exact ⟨n,h,hn⟩,
      fun ⟨_,h,_⟩ => h⟩
  have hdb : Pairwise (fun n m => Disjoint (B∩E n) (B∩E m)) :=
    fun n m hnm => (hd hnm).mono Set.inter_subset_right Set.inter_subset_right
  rw [hBu,measure_iUnion hdb (fun n => hB.inter (hm n)),
    measure_iUnion hd hm,← ENNReal.tsum_mul_right,← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun n => prefix_favourable_gain μ (E n) B n p (hE n) (hfav n)

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

lemma annealed_ge_noDrop_mul_conditioned {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    (annealedLaw ν).real (NoDrop ℓ 0)*(conditionedLaw ν ℓ).real A ≤ (annealedLaw ν).real A := by
  have hh : annealedLaw ν (NoDrop ℓ 0)*conditionedLaw ν ℓ A = annealedLaw ν (A ∩ NoDrop ℓ 0) := by
    rw [conditionedLaw,Measure.smul_apply,Measure.restrict_apply hA,smul_eq_mul,
      ← mul_assoc,ENNReal.mul_inv_cancel hp (measure_ne_top _ _),one_mul]
  have he : (annealedLaw ν).real (NoDrop ℓ 0)*(conditionedLaw ν ℓ).real A =
      (annealedLaw ν).real (A ∩ NoDrop ℓ 0) := by
    simpa only [measureReal_def,ENNReal.toReal_mul] using congrArg ENNReal.toReal hh
  rw [he]
  exact measureReal_mono Set.inter_subset_left

lemma unit_direction_coordinate_bound {d : ℕ} (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1) :
    ∀ i, |ℓ i| ≤ 1 := by
  intro i
  have hh : ℓ i*ℓ i ≤ ∑ j : Fin d, ℓ j*ℓ j :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (ℓ j)) (Finset.mem_univ i)
  change ℓ i*ℓ i ≤ dot ℓ ℓ at hh
  rw [hℓ] at hh
  nlinarith [sq_abs (ℓ i),abs_nonneg (ℓ i)]

lemma increment_sublinear_of_average (f : ℕ → ℝ) (m : ℝ)
    (h : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f i) / n) atTop (𝓝 m)) :
    Tendsto (fun n : ℕ => f n / n) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => ((n : ℝ)+1)/n) atTop (𝓝 1) := by
    have hh := (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [inv_one, inv_div] using hh
  have hh := ((h.comp (tendsto_add_atTop_nat 1)).mul hr).sub h
  simp only [mul_one, sub_self] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hnp : (n : ℝ)+1 ≠ 0 := by positivity
  simp only [Function.comp_apply, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

lemma wordCoordinate_abs_le_radius {d : ℕ} (e : Direction d) (w : List (Direction d)) :
    |wordCoordinate e w| ≤ wordRadius w :=
  (signedCoordinate_abs_le_norm _ _).trans (wordRadius_bound _ (by rfl))

lemma conditioned_wordCoordinate_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (e : Direction d) :
    Integrable (fun X => wordCoordinate e (firstWord ℓ X)) (conditionedLaw ν ℓ) := by
  apply (conditioned_wordRadius_integrable ν hue ℓ hℓ htrans).mono'
    (((measurable_of_countable (wordCoordinate e)).comp (measurable_firstWord ℓ)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun X => by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using wordCoordinate_abs_le_radius e (firstWord ℓ X)

lemma conditioned_coordinate_positive_mean {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) : ∃ e : Direction d,
      0 < ∫ X, wordCoordinate e (firstWord ℓ X) ∂conditionedLaw ν ℓ := by
  let μ := conditionedLaw ν ℓ
  have hint (i : Fin d) : Integrable (fun X =>
      wordCoordinate (i,true) (firstWord ℓ X) * ℓ i) μ :=
    (conditioned_wordCoordinate_integrable ν hue ℓ hℓ htrans (i,true)).mul_const _
  have hid : (∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂μ) =
      ∑ i : Fin d, (∫ X, wordCoordinate (i,true) (firstWord ℓ X) ∂μ) * ℓ i := by
    change (∫ X, ∑ i : Fin d, wordCoordinate (i,true) (firstWord ℓ X) * ℓ i ∂μ) = _
    rw [integral_finsetSum _ (fun i _ => hint i)]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_mul_const _ _
  have hpos := (conditioned_wordHeightGain_moments ν ℓ
    (unit_direction_coordinate_bound ℓ hℓ) htrans).2.1
  change 0 < ∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂μ at hpos
  rw [hid] at hpos
  have hex : ∃ i : Fin d, (∫ X, wordCoordinate (i,true) (firstWord ℓ X) ∂μ) ≠ 0 := by
    by_contra! hn
    simp only [hn, zero_mul, Finset.sum_const_zero, lt_self_iff_false] at hpos
  obtain ⟨i,hi⟩ := hex
  rcases lt_or_gt_of_ne hi with hi | hi
  · refine ⟨(i,false), ?_⟩
    have he : (fun X => wordCoordinate (i,false) (firstWord ℓ X)) =
        fun X => -wordCoordinate (i,true) (firstWord ℓ X) := by
      ext X; simp [wordCoordinate, signedCoordinate]
    rw [he, integral_neg]
    exact neg_pos.mpr hi
  · exact ⟨(i,true), hi⟩

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_FixedQuenchedKernel
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

lemma conditioned_word_spatial_strong_laws {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (e : Direction d) :
    ∀ᵐ X ∂conditionedLaw ν ℓ,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, wordCoordinate e (regenerationWords ℓ X i))/n)
        atTop (𝓝 (∫ Y, wordCoordinate e (firstWord ℓ Y) ∂conditionedLaw ν ℓ)) ∧
      Tendsto (fun n : ℕ => wordRadius (regenerationWords ℓ X n)/n) atTop (𝓝 0) := by
  have hi := regenerationWords_independent ν ℓ htrans
  have hd := regenerationWords_identDistrib ν ℓ htrans
  have hmc : Measurable (wordCoordinate e) := measurable_of_countable _
  have hc := strong_law_ae_real (fun n X => wordCoordinate e (regenerationWords ℓ X n))
    (conditioned_wordCoordinate_integrable ν hue ℓ hℓ htrans e)
    (fun i j hij => (hi.indepFun hij).comp hmc hmc) (fun i => (hd i).comp hmc)
  have hr := strong_law_ae_real (fun n X => wordRadius (regenerationWords ℓ X n))
    (conditioned_wordRadius_integrable ν hue ℓ hℓ htrans)
    (fun i j hij => (hi.indepFun hij).comp measurable_wordRadius measurable_wordRadius)
    (fun i => (hd i).comp measurable_wordRadius)
  filter_upwards [hc,hr] with X hX hR
  exact ⟨hX, increment_sublinear_of_average _ _ hR⟩

lemma increasing_cuts_index_tendsto (T K : ℕ → ℕ) (hT : StrictMono T)
    (hK : ∀ n, T (K n) ≤ n ∧ n < T (K n+1)) : Tendsto K atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [eventually_ge_atTop (T M)] with n hn
  by_contra hm
  have hh := hT.monotone (show K n+1 ≤ M by omega)
  exact (not_lt_of_ge (hh.trans hn)) (hK n).2

lemma scalar_cut_interpolation (T : ℕ → ℕ) (hT : StrictMono T) (hT0 : T 0 = 0)
    (Y f R : ℕ → ℝ) (m : ℝ) (hm : 0 < m)
    (hY : ∀ n, Y (T n) = ∑ i ∈ Finset.range n, f i)
    (herr : ∀ k n, T k ≤ n → n < T (k+1) → |Y n-Y (T k)| ≤ R k)
    (hf : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f i)/n) atTop (𝓝 m))
    (hR : Tendsto (fun n : ℕ => R n/n) atTop (𝓝 0)) : Tendsto Y atTop atTop := by
  choose K hK using increasing_cuts_cover T hT hT0
  have hKt := increasing_cuts_index_tendsto T K hT hK
  have hh := (hf.sub hR).comp hKt
  simp only [sub_zero] at hh
  have hmul := hh.pos_mul_atTop hm (tendsto_natCast_atTop_atTop.comp hKt)
  apply tendsto_atTop_mono' _ _ hmul
  filter_upwards [hKt.eventually (eventually_gt_atTop (0 : ℕ))] with n hn
  have hk : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have he := neg_le_of_abs_le (herr (K n) n (hK n).1 (hK n).2)
  simp only [Function.comp_apply, sub_mul, div_mul_cancel₀ _ hk]
  rw [← hY]
  linarith only [he]

lemma regeneration_coordinate_sum {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (X : Path d) (hX : X ∈ RegenerationSupport ℓ) (n : ℕ) :
    signedCoordinate e (X (regenerationTimes ℓ X n)) =
      ∑ i ∈ Finset.range n, wordCoordinate e (regenerationWords ℓ X i) := by
  induction n with
  | zero => simp [hX.1, signedCoordinate]
  | succ n ih =>
    rw [regenerationTimes_succ, regeneration_span ℓ X hX.1 hX.2 n _ (by rfl),
      signedCoordinate_add, ih, Finset.sum_range_succ, wordCoordinate]

lemma conditioned_coordinate_transience {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (e : Direction d)
    (he : 0 < ∫ X, wordCoordinate e (firstWord ℓ X) ∂conditionedLaw ν ℓ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, Tendsto (fun n => signedCoordinate e (X n)) atTop atTop := by
  filter_upwards [conditioned_regenerationSupport ν ℓ htrans,
    conditioned_word_spatial_strong_laws ν hue ℓ hℓ htrans e] with X hX hlim
  apply scalar_cut_interpolation (regenerationTimes ℓ X)
    (regenerationTimes_strictMono ℓ X hX.2) (regenerationTimes_zero ℓ X)
    (fun n => signedCoordinate e (X n)) (fun n => wordCoordinate e (regenerationWords ℓ X n))
    (fun n => wordRadius (regenerationWords ℓ X n)) _ he
    (regeneration_coordinate_sum ℓ e X hX) _ hlim.1 hlim.2
  intro k n hlo hhi
  have hnk : n = regenerationTimes ℓ X k+(n-regenerationTimes ℓ X k) := by omega
  have hlen : n-regenerationTimes ℓ X k ≤ (regenerationWords ℓ X k).length := by
    rw [regenerationTimes_succ] at hhi
    omega
  have hh := regeneration_span ℓ X hX.1 hX.2 k _ hlen
  rw [← hnk] at hh
  rw [hh, signedCoordinate_add, add_sub_cancel_left]
  exact (signedCoordinate_abs_le_norm _ _).trans (wordRadius_bound _ hlen)

lemma conditioned_to_annealed_transience {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ u : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (hu : ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ TransientPaths u) : DirectionallyTransient ν u := by
  let B := NoDrop ℓ 0 ∩ (TransientPaths u)ᶜ
  have hB : MeasurableSet B := (measurableSet_noDrop ℓ 0).inter (measurableSet_transientPaths u).compl
  have hBD : B ⊆ NoDrop ℓ 0 := Set.inter_subset_left
  have hcB : conditionedLaw ν ℓ B = 0 :=
    measure_mono_null Set.inter_subset_right (ae_iff.mp hu)
  have haB : annealedLaw ν B = 0 := by
    rw [conditionedLaw_apply_of_subset ν ℓ B hB hBD] at hcB
    exact (mul_eq_zero.mp hcB).resolve_left (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
  have hwords : ∀ᵐ X ∂annealedLaw ν, ∀ w : List (Direction d),
      (∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
        dot (realPosition (wordPath 0 w w.length)) ℓ) →
      X ∈ wordCylinder 0 w →
      (fun j => X (w.length+j)-wordPath 0 w w.length) ∉ B := by
    apply ae_all_iff.mpr
    intro w
    by_cases hw : ∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
      dot (realPosition (wordPath 0 w w.length)) ℓ
    · have hz := annealed_record_suffix ν ℓ w hw B hB hBD
      rw [haB, mul_zero] at hz
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with X hX _ hcy
      exact fun hh => hX ⟨hh,hcy⟩
    · exact Filter.Eventually.of_forall fun _ h _ => (hw h).elim
  filter_upwards [annealed_initial ν, annealed_nearest_neighbor ν,
    annealed_trueRecords_unbounded ν ℓ htrans, hwords] with X h0 hnn hrec hwords
  obtain ⟨n,_,hn⟩ := hrec 0
  obtain ⟨w,hw,hcy⟩ := exists_word_prefix X hnn n
  rw [h0] at hcy
  have hwend : wordPath 0 w w.length = X n := by rw [← hw]; exact (hcy _ le_rfl).symm
  have hwrec : ∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
      dot (realPosition (wordPath 0 w w.length)) ℓ := by
    intro y hy
    obtain ⟨j,hj,rfl⟩ := (wordDepartures_mem_iff 0 y w).mp hy
    rw [← hcy j hj.le, hwend]
    exact hn.1 j (by omega)
  have hnot := hwords w hwrec hcy
  have hD : (fun j => X (w.length+j)-wordPath 0 w w.length) ∈ NoDrop ℓ 0 := by
    intro j
    rw [hwend, hw, dot_realPosition_sub]
    have hh := hn.2 j
    simpa only [dot, realPosition, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero,
      sub_nonneg] using hh
  have ht : (fun j => X (n+j)-X n) ∈ TransientPaths u := by
    by_contra hh
    apply hnot
    refine ⟨hD, ?_⟩
    change (fun j => X (w.length+j)-wordPath 0 w w.length) ∉ TransientPaths u
    rw [hwend, hw]
    exact hh
  have hraw : (fun j => X (n+j)) ∈ TransientPaths u := by
    change (fun j => X (n+j)) ∈ (fun Z : Path d => fun j => Z j-X n) ⁻¹' TransientPaths u at ht
    rwa [transientPaths_translation] at ht
  change Tendsto (fun j => dot (realPosition (X j)) u) atTop atTop
  change Tendsto (fun j => dot (realPosition (X (n+j))) u) atTop atTop at hraw
  exact (tendsto_add_atTop_iff_nat n).mp (by simpa only [Nat.add_comm] using hraw)

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

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstLayerHitRecordIndexTime
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
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

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CrossTranslation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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
namespace DirectionalTransience

lemma cross_translation {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    (fun X : Path d => fun n => X n-x) ⁻¹' Cross ℓ 0 H = Cross ℓ x H := by
  ext X
  have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot,realPosition]
  simp only [Cross,Set.mem_preimage,Set.mem_ofPred_eq,hzero,zero_add,dot_realPosition_sub]
  constructor
  · rintro ⟨n,hn,hpre⟩
    exact ⟨n,by linarith,fun j hj => by have := hpre j hj; linarith⟩
  · rintro ⟨n,hn,hpre⟩
    exact ⟨n,by linarith,fun j hj => by have := hpre j hj; linarith⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicy
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma crossingQuenched_translation {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (H : ℝ) (ω : Environment d) :
    crossingQuenched ℓ x H ω = crossingQuenched ℓ 0 H (fun y => ω (x+y)) := by
  have hm : Measurable (fun X : Path d => fun j => X j-x) := by fun_prop
  have he := congrArg (fun μ : Measure (Path d) => μ (Cross ℓ 0 H)) (quenched_translation ω x 0)
  rw [Measure.map_apply hm (measurableSet_cross _ _ _),cross_translation] at he
  simpa only [add_zero,crossingQuenched] using he

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_FreshCrossing
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma annealed_crossing_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    (∫⁻ ω, crossingQuenched ℓ x H ω ∂environmentLaw ν)=annealedLaw ν (Cross ℓ 0 H) := by
  simp_rw [crossingQuenched_translation ℓ x]
  rw [← lintegral_map (measurable_crossingQuenched ℓ 0 H) (by fun_prop),environment_translation,
    annealed_apply ν (measurableSet_cross ℓ 0 H)]
  rfl

lemma annealed_record_cylinder_cross {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Path d) (n : ℕ) (hn : 0<n) (hr : StrictRecord ℓ f n)
    (H : ℝ) (hH : 0<H) :
    annealedLaw ν ((fun X : Path d => fun j => X (n+j)) ⁻¹' Cross ℓ (f n) H ∩ pathCylinder f n)=
      annealedLaw ν (pathCylinder f n)*annealedLaw ν (Cross ℓ 0 H) := by
  by_cases hf : f 0=0
  · let S : Set (Lattice d) := {y | ∃ j<n, y=f j}
    let T := Strip ℓ (f n) H
    have hST : Disjoint S T := by
      apply Set.disjoint_left.mpr
      rintro y ⟨j,hj,rfl⟩ hy
      exact (not_le_of_gt (hr j hj)) hy.1
    have hS0 : (0 : Lattice d) ∈ S := ⟨0,hn,hf.symm⟩
    have hm : @Measurable _ _ (rowSigma S) _
        (fun ω : Environment d => quenchedKernel (ω,0) (pathCylinder f n)) := by
      apply measurable_of_row_locality _
        ((Kernel.measurable_coe _ (measurableSet_pathCylinder f n)).comp
          (measurable_id.prodMk measurable_const)) S 0 hS0
      intro ω η hωη
      exact pathCylinder_weight_locality S ω η hωη 0 f n (fun j hj => ⟨j,hj,rfl⟩)
    rw [annealed_apply ν ((measurableSet_cross ℓ (f n) H).preimage (by fun_prop) |>.inter
      (measurableSet_pathCylinder f n))]
    simp_rw [quenched_prefix_future _ _ _ hf n (measurableSet_cross ℓ (f n) H)]
    change (∫⁻ ω, quenchedKernel (ω,0) (pathCylinder f n)*crossingQuenched ℓ (f n) H ω
      ∂environmentLaw ν)=_
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hST) hm
      (measurable_crossingQuenched_rows ℓ (f n) hH),annealed_crossing_translation,
      ← annealed_apply ν (measurableSet_pathCylinder f n)]
  · have hzero : annealedLaw ν (pathCylinder f n)=0 := by
      rw [annealed_apply ν (measurableSet_pathCylinder f n)]
      simp_rw [quenched_pathCylinder_zero _ _ _ hf n]
      simp
    rw [measure_mono_null Set.inter_subset_right hzero,hzero,zero_mul]

lemma annealed_record_event_cross {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (n : ℕ) (hn : 0<n) (A : Set (Path d)) (hA : PrefixDetermined n A)
    (hr : ∀ X ∈ A, StrictRecord ℓ X n) (H : ℝ) (hH : 0<H) :
    annealedLaw ν (A ∩ FutureEvent (fun x => Cross ℓ x H) n)=
      annealedLaw ν A*annealedLaw ν (Cross ℓ 0 H) := by
  rw [measure_partition_prefix (annealedLaw ν) (A ∩ _) n,
    measure_partition_prefix (annealedLaw ν) A n,← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro f
  let g := extendPrefix n f
  by_cases hg : g ∈ A
  · have he : (A ∩ FutureEvent (fun x => Cross ℓ x H) n) ∩ pathCylinder g n =
        (fun X : Path d => fun j => X (n+j)) ⁻¹' Cross ℓ (g n) H ∩ pathCylinder g n := by
      ext X
      constructor
      · rintro ⟨⟨_,hc⟩,hX⟩
        exact ⟨by simpa only [FutureEvent,Set.mem_ofPred_eq,Set.mem_preimage,hX n le_rfl] using hc,hX⟩
      · rintro ⟨hc,hX⟩
        exact ⟨⟨(hA X g hX).mpr hg,by simpa only [FutureEvent,Set.mem_ofPred_eq,Set.mem_preimage,hX n le_rfl] using hc⟩,hX⟩
    have hAc : A ∩ pathCylinder g n=pathCylinder g n := by
      rw [prefixDetermined_inter_cylinder A n hA g,ite_eq_left hg]
    rw [he,hAc]
    exact annealed_record_cylinder_cross ν ℓ g n hn (hr g hg) H hH
  · have hzero : A ∩ pathCylinder g n=∅ := by
      rw [prefixDetermined_inter_cylinder A n hA g,ite_eq_right hg]
    have he : (A ∩ FutureEvent (fun x => Cross ℓ x H) n) ∩ pathCylinder g n=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨⟨hXA,_⟩,hX⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hzero) X ⟨hXA,hX⟩
    rw [he,hzero,measure_empty,zero_mul]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CrossingGap
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma signedHeight_zero {d : ℕ} (e : Direction d) : signedHeight e (0 : Lattice d) = 0 := by
  simp [signedHeight]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RapidDecay
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma RapidDecay.of_le {a b : ℕ → ℝ} (hb : RapidDecay b) (ha : ∀ n, 0 ≤ a n)
    (hle : ∀ᶠ n in atTop, a n ≤ b n) : RapidDecay a := by
  intro m
  apply (hb m).of_norm_bounded_eventually_nat
  filter_upwards [hle] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (ha n))]
  exact mul_le_mul_of_nonneg_left hn (by positivity)

lemma RapidDecay.add {a b : ℕ → ℝ} (ha : RapidDecay a) (hb : RapidDecay b) :
    RapidDecay (fun n : ℕ => a n+b n) := by
  intro m
  simpa only [mul_add] using (ha m).add (hb m)

lemma RapidDecay.const_mul {a : ℕ → ℝ} (ha : RapidDecay a) (c : ℝ) :
    RapidDecay (fun n : ℕ => c*a n) := by
  intro m
  simpa only [mul_left_comm] using (ha m).mul_left c

lemma RapidDecay.pow_mul {a : ℕ → ℝ} (ha : RapidDecay a) (k : ℕ) :
    RapidDecay (fun n : ℕ => (n+1:ℝ)^k*a n) := by
  intro m
  simpa only [pow_add,mul_assoc] using ha (m+k)

lemma RapidDecay.shift {a : ℕ → ℝ} (ha : RapidDecay a) (ha0 : ∀ n, 0 ≤ a n) (k : ℕ) :
    RapidDecay (fun n : ℕ => a (n+k)) := by
  intro m
  apply ((summable_nat_add_iff k).mpr (ha m)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (ha0 _))]
  apply mul_le_mul_of_nonneg_right _ (ha0 _)
  exact pow_le_pow_left₀ (by positivity) (by push_cast <;> linarith) m

lemma rapidDecay_geometric (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r<1) : RapidDecay (fun n : ℕ => r^n) := by
  intro m
  have hs := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r := r) m (by simpa [Real.norm_eq_abs,abs_of_nonneg hr0] using hr1)).mul_left ((2:ℝ)^m)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (2*(n:ℝ))^m*r^n := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith) m) (pow_nonneg hr0 _)
    _ = _ := by rw [mul_pow,mul_assoc]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CrossingSurplus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma annealed_record_event_cross_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (n : ℕ) (hn : 0<n)
    (A : Set (Path d)) (_ : MeasurableSet A) (hA : PrefixDetermined n A)
    (hr : ∀ X ∈ A, StrictRecord ℓ X n) (H : ℝ) (hH : 0<H) :
    (annealedLaw ν).real ((A ∩ FutureEvent (fun x => Cross ℓ x H) n) \ FutureNoDrop ℓ n)=
      (annealedLaw ν).real A*(annealedLaw ν).real (Cross ℓ 0 H \ NoDrop ℓ 0) := by
  let μ := annealedLaw ν
  have hsub : ∀ᵐ X ∂μ, X ∈ A ∩ FutureNoDrop ℓ n → X ∈ A ∩ FutureEvent (fun x => Cross ℓ x H) n := by
    filter_upwards [htrans] with X ht hX
    refine ⟨hX.1,?_⟩
    apply noDrop_subset_cross_of_tendsto ℓ (X n) (fun j => X (n+j))
    · exact ht.comp (by
        change Tendsto (fun i : ℕ => n+i) atTop atTop
        simpa only [Nat.add_comm] using tendsto_add_atTop_nat n)
    · exact hX.2
  have hraw : ∀ᵐ X ∂μ, X ∈ NoDrop ℓ 0 → X ∈ Cross ℓ 0 H := by
    filter_upwards [htrans] with X ht hX
    exact noDrop_subset_cross_of_tendsto ℓ 0 X ht hX H
  have hi : ((A ∩ FutureEvent (fun x => Cross ℓ x H) n) ∩ FutureNoDrop ℓ n : Set (Path d)) =ᵐ[μ]
      (A ∩ FutureNoDrop ℓ n : Set (Path d)) := by
    filter_upwards [hsub] with X hX
    exact propext ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨hX h,h.2⟩⟩
  have hi0 : (Cross ℓ 0 H ∩ NoDrop ℓ 0 : Set (Path d)) =ᵐ[μ] NoDrop ℓ 0 := by
    filter_upwards [hraw] with X hX
    exact propext ⟨And.right,fun h => ⟨hX h,h⟩⟩
  have hf := congrArg ENNReal.toReal (annealed_record_event_cross ν ℓ n hn A hA hr H hH)
  have hp := congrArg ENNReal.toReal (annealed_record_event_noDrop ν ℓ n hn A hA hr)
  have hs := measureReal_inter_add_sdiff (μ := μ) (s := A ∩ FutureEvent (fun x => Cross ℓ x H) n)
    (measurableSet_futureNoDrop ℓ n)
  have hs0 := measureReal_inter_add_sdiff (μ := μ) (s := Cross ℓ 0 H) (measurableSet_noDrop ℓ 0)
  rw [measureReal_congr hi] at hs
  rw [measureReal_congr hi0] at hs0
  simp only [ENNReal.toReal_mul] at hf hp
  change μ.real (A ∩ FutureEvent (fun x => Cross ℓ x H) n)=μ.real A*μ.real (Cross ℓ 0 H) at hf
  change μ.real (A ∩ FutureNoDrop ℓ n)=μ.real A*μ.real (NoDrop ℓ 0) at hp
  change μ.real _=μ.real A*μ.real _
  rw [← hs0,mul_add,← hp] at hf
  linarith

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridTrials
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma measurableSet_dropBetween {d : ℕ} (ℓ : Vector d) (n m : ℕ) :
    MeasurableSet (DropBetween ℓ n m) := by
  simp only [DropBetween,Set.ofPred_exists,Set.ofPred_and]
  exact MeasurableSet.iUnion fun r => (MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter (measurableSet_lt
      ((measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp (measurable_pi_apply r))
      ((measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp (measurable_pi_apply n))))

lemma dropBetween_prefix {d : ℕ} (ℓ : Vector d) (n m : ℕ) (hn : n ≤ m) :
    PrefixDetermined m (DropBetween ℓ n m) := by
  intro X Y hXY
  constructor <;> rintro ⟨r,h1,h2,h3⟩
  · exact ⟨r,h1,h2,by simpa only [← hXY r h2.le,← hXY n hn] using h3⟩
  · exact ⟨r,h1,h2,by simpa only [hXY r h2.le,hXY n hn] using h3⟩

lemma dropBetween_not_futureNoDrop {d : ℕ} (ℓ : Vector d) (n m : ℕ) (X : Path d)
    (h : X ∈ DropBetween ℓ n m) : X ∉ FutureNoDrop ℓ n := by
  rintro hD
  obtain ⟨r,hnr,hrm,hr⟩ := h
  have hh := hD (r-n)
  rw [Nat.add_sub_of_le hnr] at hh
  exact (not_lt_of_ge hh) hr

lemma gridPrefix_hit {d : ℕ} (e : Direction d) (B k n : ℕ) :
    GridPrefix e B k n ⊆ {X | X 0=0} ∩ FirstLayerHit (signedHeight e) (((k+1)*B:ℕ):ℤ) n := by
  cases k with
  | zero => simpa only [GridPrefix,Nat.zero_add,one_mul] using (Set.Subset.refl (GridPrefix e B 0 n))
  | succ k => exact Set.inter_subset_left

lemma measurableSet_gridPrefix {d : ℕ} (e : Direction d) (B k n : ℕ) :
    MeasurableSet (GridPrefix e B k n) := by
  induction k generalizing n with
  | zero =>
    exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
      (measurableSet_firstLayerHit _ _ _)
  | succ k ih =>
    exact ((measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
      (measurableSet_firstLayerHit _ _ _)).inter (MeasurableSet.iUnion fun j =>
        MeasurableSet.iUnion fun _ => (ih j).inter (measurableSet_dropBetween _ _ _))

lemma measurableSet_gridReached {d : ℕ} (e : Direction d) (B k : ℕ) :
    MeasurableSet (GridReached e B k) := MeasurableSet.iUnion (measurableSet_gridPrefix e B k)

lemma gridPrefix_prefix {d : ℕ} (e : Direction d) (B k n : ℕ) :
    PrefixDetermined n (GridPrefix e B k n) := by
  have hz (m : ℕ) : PrefixDetermined m {X : Path d | X 0=0} := by
    intro X Y hXY
    simp only [Set.mem_ofPred_eq,hXY 0 (Nat.zero_le _)]
  induction k generalizing n with
  | zero => exact prefixDetermined_inter (hz _) (firstLayerHit_prefix _ _ _)
  | succ k ih =>
    apply prefixDetermined_inter (prefixDetermined_inter (hz _) (firstLayerHit_prefix _ _ _))
    intro X Y hXY
    simp only [Set.mem_iUnion,Set.mem_inter_iff]
    apply exists_congr
    intro j
    apply exists_congr
    intro hj
    exact and_congr ((prefixDetermined_mono hj.le (ih j)) X Y hXY)
      ((dropBetween_prefix _ j n hj.le) X Y hXY)

lemma gridPrefix_disjoint {d : ℕ} (e : Direction d) (B k : ℕ) :
    Pairwise (fun n m => Disjoint (GridPrefix e B k n) (GridPrefix e B k m)) := by
  intro n m hnm
  exact (firstLayerHit_disjoint (signedHeight e) (((k+1)*B:ℕ):ℤ) hnm).mono
    (fun X hX => (gridPrefix_hit e B k n hX).2)
    (fun X hX => (gridPrefix_hit e B k m hX).2)

lemma gridPrefix_record {d : ℕ} (e : Direction d) (B k n : ℕ) (hB : 0<B)
    (X : Path d) (hX : X ∈ GridPrefix e B k n) :
    0<n ∧ StrictRecord (realPosition (step e)) X n := by
  have hh := gridPrefix_hit e B k n hX
  refine ⟨?_,firstLayerHit_record _ _ (signedHeight_projection e) _ _ X hh.2⟩
  by_contra hn
  have hn0 : n=0 := by omega
  have he := hh.2.1
  rw [hn0,hh.1,signedHeight_zero] at he
  have hpos : (0:ℤ)<((k+1)*B:ℕ) := by exact_mod_cast (Nat.mul_pos (Nat.succ_pos k) hB)
  omega

lemma gridReached_succ_subset {d : ℕ} (e : Direction d) (B k : ℕ) :
    GridReached e B (k+1) ⊆ GridReached e B k := by
  intro X hX
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hX
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hm.2
  obtain ⟨_,hn⟩ := Set.mem_iUnion.mp hn
  exact Set.mem_iUnion.mpr ⟨n,hn.1⟩

lemma gridReached_succ_failure {d : ℕ} (e : Direction d) (B k n : ℕ) (X : Path d)
    (hX : X ∈ GridReached e B (k+1)) (hn : X ∈ GridPrefix e B k n) :
    X ∉ FutureNoDrop (realPosition (step e)) n := by
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hX
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hm.2
  obtain ⟨_,hj⟩ := Set.mem_iUnion.mp hj
  have heq : j=n := by
    by_contra hh
    exact Set.disjoint_left.mp (gridPrefix_disjoint e B k hh) hj.1 hn
  subst j
  exact dropBetween_not_futureNoDrop _ n m X hj.2

lemma gridReached_contraction {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (B k : ℕ) (hB : 0<B) :
    (annealedLaw ν).real (GridReached e B (k+1)) ≤
      (1-(annealedLaw ν).real (NoDrop (realPosition (step e)) 0))*
        (annealedLaw ν).real (GridReached e B k) := by
  let ℓ := realPosition (step e)
  let μ := annealedLaw ν
  have hg := stopping_prefix_favourable_gain μ (GridPrefix e B k) (GridReached e B (k+1))
    (μ (NoDrop ℓ 0)) (gridPrefix_prefix e B k) (measurableSet_gridPrefix e B k)
    (gridPrefix_disjoint e B k) (measurableSet_gridReached e B (k+1))
    (gridReached_succ_subset e B k) (by
      intro n f hf
      have hr := gridPrefix_record e B k n hB f hf
      let A := (fun X : Path d => fun j => X (n+j)) ⁻¹' NoDrop ℓ (f n) ∩ pathCylinder f n
      refine ⟨A,(measurableSet_noDrop ℓ (f n)).preimage (by fun_prop) |>.inter
        (measurableSet_pathCylinder f n),Set.inter_subset_right,?_,?_⟩
      · apply Set.disjoint_left.mpr
        intro X hX hA
        apply gridReached_succ_failure e B k n X hX ((gridPrefix_prefix e B k n X f hA.2).mpr hf)
        change ∀ j, dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n+j))) ℓ
        have hh : ∀ j, dot (realPosition (f n)) ℓ ≤ dot (realPosition (X (n+j))) ℓ := hA.1
        simpa only [hA.2 n le_rfl] using hh
      · exact annealed_record_cylinder_noDrop ν ℓ f n hr.1 hr.2)
  have hr := ENNReal.toReal_mono (measure_ne_top μ _) hg
  rw [ENNReal.toReal_add (measure_ne_top μ _)
    (ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)),ENNReal.toReal_mul] at hr
  change μ.real (GridReached e B (k+1))+μ.real (GridReached e B k)*μ.real (NoDrop ℓ 0) ≤
    μ.real (GridReached e B k) at hr
  change μ.real _≤(1-μ.real (NoDrop ℓ 0))*μ.real _
  nlinarith

lemma gridReached_geometric {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (B k : ℕ) (hB : 0<B) :
    (annealedLaw ν).real (GridReached e B k) ≤
      (1-(annealedLaw ν).real (NoDrop (realPosition (step e)) 0))^k := by
  have hp : (annealedLaw ν).real (NoDrop (realPosition (step e)) 0) ≤ 1 := measureReal_le_one
  induction k with
  | zero =>
    rw [pow_zero]
    exact measureReal_le_one
  | succ k ih =>
    exact (gridReached_contraction ν e B k hB).trans (by
      simpa only [pow_succ,mul_comm] using mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_NaturalTailIntegrable
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma natural_integrable_of_coarse_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℕ) (hf : Measurable f)
    (T : ℕ → ℕ) (hT : ∀ k, ∃ n, k ≤ T n)
    (hs : Summable (fun n => (T (n+1):ℝ)*μ.real {x | T n < f x})) :
    Integrable (fun x => (f x:ℝ)) μ := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n => {x | T n < f x}.indicator (fun _ => (T (n+1):ℝ≥0∞))
  have hE (n : ℕ) : MeasurableSet {x | T n < f x} := measurableSet_lt measurable_const hf
  have hF (n : ℕ) : Measurable (F n) := measurable_const.indicator (hE n)
  have hpoint (x : Ω) : (f x:ℝ≥0∞) ≤ (T 0:ℝ≥0∞)+∑' n,F n x := by
    by_cases hh : f x ≤ T 0
    · exact (by exact_mod_cast hh : (f x:ℝ≥0∞) ≤ T 0).trans (le_add_right le_rfl)
    · have hex := hT (f x)
      have hb := Nat.find_spec hex
      cases hk : Nat.find hex with
      | zero => exact (hh (hk ▸ hb)).elim
      | succ n =>
        have hlo : T n < f x := Nat.lt_of_not_ge (Nat.find_min hex (by omega : n < Nat.find hex))
        have hterm : F n x=(T (n+1):ℝ≥0∞) := Set.indicator_of_mem (show x ∈ {x | T n < f x} from hlo) _
        calc
          _ ≤ (T (n+1):ℝ≥0∞) := by exact_mod_cast (show f x ≤ T (n+1) by simpa only [hk] using hb)
          _ = F n x := hterm.symm
          _ ≤ ∑' i,F i x := ENNReal.le_tsum (f := fun index => F index x) n
          _ ≤ _ := le_add_left le_rfl
  have hIf (n : ℕ) : (∫⁻ x,F n x ∂μ) = (T (n+1):ℝ≥0∞)*μ {x | T n < f x} := by
    dsimp only [F]
    rw [lintegral_indicator (hE n),lintegral_const,Measure.restrict_apply_univ]
  have hfinite : (∑' n,(T (n+1):ℝ≥0∞)*μ {x | T n < f x}) < ⊤ := by
    have he (n : ℕ) : (T (n+1):ℝ≥0∞)*μ {x | T n < f x} =
        ENNReal.ofReal ((T (n+1):ℝ)*μ.real {x | T n < f x}) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,measureReal_def,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg) hs]
    exact ENNReal.ofReal_lt_top
  refine ⟨((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp hf).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => Nat.cast_nonneg (f x)))).mpr ?_⟩
  calc
    (∫⁻ x,ENNReal.ofReal (f x:ℝ) ∂μ) ≤ ∫⁻ x,(T 0:ℝ≥0∞)+∑' n,F n x ∂μ :=
      lintegral_mono (fun x => by simpa only [ENNReal.ofReal_natCast] using hpoint x)
    _ = (T 0:ℝ≥0∞)+∑' n,(T (n+1):ℝ≥0∞)*μ {x | T n < f x} := by
      rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one,
        lintegral_tsum (fun n => (hF n).aemeasurable)]
      simp_rw [hIf]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top _,hfinite⟩

lemma natural_integrable_of_polynomial_rapid_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℕ) (hf : Measurable f)
    (A q : ℕ) (hA : 0 < A) (hq : 0 < q)
    (ht : RapidDecay (fun n => μ.real {x | A*(n+1)^q < f x})) :
    Integrable (fun x => (f x:ℝ)) μ := by
  apply natural_integrable_of_coarse_tail μ f hf (fun n => A*(n+1)^q)
  · intro k
    refine ⟨k,?_⟩
    have hpow : k+1 ≤ (k+1)^q := by
      obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
      rw [pow_succ]
      have hp : 1 ≤ (k+1)^q := Nat.one_le_pow _ _ (by omega)
      nlinarith
    nlinarith
  · have hs := (ht q).mul_left ((A:ℝ)*2^q)
    apply hs.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg)]
    have hbound : (A*(n+1+1)^q:ℕ) ≤ (A:ℝ)*2^q*(n+1:ℝ)^q := by
      push_cast
      calc
        _ ≤ (A:ℝ)*(2*(n+1:ℝ))^q := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n]) _) (Nat.cast_nonneg _)
        _ = _ := by rw [mul_pow,mul_assoc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hbound
      (show 0 ≤ μ.real {x | A*(n+1)^q < f x} from measureReal_nonneg)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RapidDecaySubsequence
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma RapidDecay.comp_strictMono {a : ℕ → ℝ} (ha : RapidDecay a) (ha0 : ∀ n, 0 ≤ a n)
    (f : ℕ → ℕ) (hf : StrictMono f) : RapidDecay (fun n => a (f n)) := by
  intro m
  apply ((ha m).comp_injective hf.injective).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (ha0 _))]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
    (by exact_mod_cast Nat.add_le_add_right (hf.id_le n) 1) m) (ha0 _)

lemma square_pred_strictMono : StrictMono (fun n : ℕ => (n+1)^2-1) := by
  intro n m hnm
  have h : (n+1)^2 < (m+1)^2 := by nlinarith
  change (n+1)^2-1 < (m+1)^2-1
  have hs : 1 ≤ (n+1)^2 := by nlinarith
  omega

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WidthGridTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma measureReal_iUnion_disjoint {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (A : ℕ → Set α) (hm : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (fun n m => Disjoint (A n) (A m))) :
    μ.real (⋃ n,A n)=∑' n,μ.real (A n) := by
  rw [measureReal_def,measure_iUnion hd hm]
  exact ENNReal.tsum_toReal_eq (fun n => measure_ne_top μ (A n))

lemma lateGridFailure_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (B j : ℕ) (hB : 0 < B) (hj : 0 < j) :
    (annealedLaw ν).real (LateGridFailure e B j)  ≤
      (annealedLaw ν).real (Cross (realPosition (step e)) 0 B \ NoDrop (realPosition (step e)) 0) := by
  let ℓ := realPosition (step e)
  let μ := annealedLaw ν
  let A := fun n => {X : Path d | X 0=0} ∩ FirstLayerHit (signedHeight e) (j*B:ℕ) n
  let F := fun n => (A n ∩ FutureEvent (fun x => Cross ℓ x B) n) \ FutureNoDrop ℓ n
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter (measurableSet_firstLayerHit _ _ _)
  have hFm (n : ℕ) : MeasurableSet (F n) :=
    ((hAm n).inter (measurableSet_futureEvent _ (fun _ => measurableSet_cross _ _ _) _)).diff
      (measurableSet_futureNoDrop _ _)
  have hAd : Pairwise (fun n m => Disjoint (A n) (A m)) :=
    fun n m hnm => (firstLayerHit_disjoint (signedHeight e) (j*B:ℕ) hnm).mono
      Set.inter_subset_right Set.inter_subset_right
  have hFd : Pairwise (fun n m => Disjoint (F n) (F m)) :=
    fun n m hnm => (hAd hnm).mono (Set.Subset.trans Set.sdiff_subset Set.inter_subset_left)
      (Set.Subset.trans Set.sdiff_subset Set.inter_subset_left)
  have hf (n : ℕ) : μ.real (F n)=μ.real (A n)*μ.real (Cross ℓ 0 B \ NoDrop ℓ 0) := by
    by_cases hn : 0 < n
    · apply annealed_record_event_cross_failure ν ℓ htrans n hn (A n) (hAm n)
      · apply prefixDetermined_inter
        · intro X Y hXY
          simp only [Set.mem_ofPred_eq,hXY 0 (Nat.zero_le n)]
        · exact firstLayerHit_prefix _ _ _
      · exact fun X hX => firstLayerHit_record _ _ (signedHeight_projection e) _ _ X hX.2
      · exact_mod_cast hB
    · have hz : n=0 := by omega
      have hAe : A n=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro X hX
        have hh := hX.2.1
        rw [hz,hX.1,signedHeight_zero] at hh
        have hpos : 0 < j*B := Nat.mul_pos hj hB
        exact (Nat.ne_of_gt hpos) (by exact_mod_cast hh.symm)
      have hFe : F n=∅ := by simp [F,hAe]
      simp only [hAe,hFe,measureReal_empty,zero_mul]
  change μ.real (⋃ n,F n) ≤ _
  rw [measureReal_iUnion_disjoint μ F hFm hFd]
  simp_rw [hf]
  rw [tsum_mul_right,← measureReal_iUnion_disjoint μ A hAm hAd]
  exact mul_le_of_le_one_left measureReal_nonneg measureReal_le_one

lemma firstLayerHit_time_lt {d : ℕ} (h : Lattice d → ℤ) (H K : ℤ) (hHK : H < K)
    (X : Path d) (n m : ℕ) (hn : X ∈ FirstLayerHit h H n) (hm : X ∈ FirstLayerHit h K m) : n < m := by
  by_contra hh
  rcases lt_or_eq_of_le (Nat.le_of_not_lt hh) with hlt | rfl
  · have hk := hn.2 m hlt
    rw [hm.1] at hk
    omega
  · have hh := hm.1
    rw [hn.1] at hh
    exact (ne_of_lt hHK) hh

lemma noTruePastHeight_grid_cover {d : ℕ} (e : Direction d) (B k : ℕ) (hB : 0 < B)
    (X : Path d) (hNN : ∀ n, ∃ f, X (n+1)=X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e)))
    (hX : X ∈ NoTruePastHeight e ((k+1)*B)) :
    X ∈ GridReached e B k ∪ ⋃ j ∈ Finset.range k, LateGridFailure e B (j+1) := by
  induction k with
  | zero =>
    obtain ⟨h0,n,hn,_⟩ := hX
    exact Or.inl (Set.mem_iUnion.mpr ⟨n,h0,by simpa using hn⟩)
  | succ k ih =>
    obtain ⟨h0,m,hm,hnot⟩ := hX
    obtain ⟨n,hn⟩ := noDrop_firstLayerHit_exists e X h0 hNN ht
      (show 0 < (k+1)*B by positivity)
    have hnm : n < m := firstLayerHit_time_lt _ _ _ (by exact_mod_cast
      (show (k+1)*B < (k+1+1)*B by nlinarith)) X n m hn hm
    have hprev : X ∈ NoTruePastHeight e ((k+1)*B) :=
      ⟨h0,n,hn,fun t ht htn => hnot t ht (htn.trans hnm.le)⟩
    rcases ih hprev with hg | hbad
    · obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hg
      have hqn : q=n := by
        by_contra hh
        exact Set.disjoint_left.mp (firstLayerHit_disjoint (signedHeight e) ((k+1)*B:ℕ) hh)
          (gridPrefix_hit e B k q hq).2 hn
      subst q
      by_cases hdrop : X ∈ DropBetween (realPosition (step e)) n m
      · exact Or.inl (Set.mem_iUnion.mpr ⟨m,⟨h0,by simpa [Nat.add_assoc] using hm⟩,
          Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨hnm,hq,hdrop⟩⟩⟩)
      · apply Or.inr
        refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self k),?_⟩⟩
        apply Set.mem_iUnion.mpr
        refine ⟨n,⟨⟨h0,hn⟩,?_⟩,?_⟩
        · refine ⟨m-n,?_,?_⟩
          · change dot (realPosition (X n)) (realPosition (step e))+B ≤ dot (realPosition (X (n+(m-n)))) (realPosition (step e))
            rw [Nat.add_sub_of_le hnm.le,signedHeight_projection,signedHeight_projection,hn.1,hm.1]
            push_cast
            ring_nf
            exact le_rfl
          · intro i hi
            rw [signedHeight_projection,signedHeight_projection]
            by_contra hh
            apply hdrop
            exact ⟨n+i,by omega,by omega,by simpa only [signedHeight_projection] using lt_of_not_ge hh⟩
        · have hr := gridPrefix_record e B k n hB X hq
          exact fun hD => hnot n hr.1 hnm.le ⟨hr.2,hD⟩
    · apply Or.inr
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hbad
      obtain ⟨hj,hbad⟩ := Set.mem_iUnion.mp hj
      exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr
        ((Finset.mem_range.mp hj).trans (Nat.lt_succ_self k)),hbad⟩⟩

lemma noTruePastHeight_grid_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (B k : ℕ) (hB : 0 < B) :
    (annealedLaw ν).real (NoTruePastHeight e ((k+1)*B))  ≤
      (1-(annealedLaw ν).real (NoDrop (realPosition (step e)) 0))^k +
      k*(annealedLaw ν).real (Cross (realPosition (step e)) 0 B \ NoDrop (realPosition (step e)) 0) := by
  calc
    _  ≤  (annealedLaw ν).real (GridReached e B k ∪ ⋃ j ∈ Finset.range k, LateGridFailure e B (j+1)) := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono_ae
      filter_upwards [annealed_nearest_neighbor ν,htrans] with X hNN ht
      exact noTruePastHeight_grid_cover e B k hB X hNN ht
    _  ≤  (annealedLaw ν).real (GridReached e B k)+
        ∑ j ∈ Finset.range k, (annealedLaw ν).real (LateGridFailure e B (j+1)) :=
      (measureReal_union_le _ _).trans (add_le_add le_rfl
        (measureReal_biUnion_finset_le (μ := annealedLaw ν) (Finset.range k) (fun j => LateGridFailure e B (j+1))))
    _  ≤  _ := add_le_add (gridReached_geometric ν e B k hB) (by
      simpa using Finset.sum_le_sum (s := Finset.range k) (fun j _ => lateGridFailure_bound ν e htrans B (j+1) hB (by omega)))

lemma noTruePastSquare_rapidDecay {d : ℕ} (hd : 2 ≤ d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    RapidDecay (fun N => (annealedLaw ν).real (NoTruePastHeight e ((N+1)^2))) := by
  have hp := noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans
  have hp' : 0 < (annealedLaw ν).real (NoDrop (realPosition (step e)) 0) :=
    ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  have hgeom := rapidDecay_geometric (1-(annealedLaw ν).real (NoDrop (realPosition (step e)) 0))
    (sub_nonneg.mpr measureReal_le_one) (by linarith)
  have hbad := ((crossing_failure_rapidDecay hd ν hue e htrans).shift
    (fun _ => measureReal_nonneg) 1).pow_mul 1
  apply (hgeom.add hbad).of_le (fun _ => measureReal_nonneg)
  apply Eventually.of_forall
  intro N
  have hh := noTruePastHeight_grid_bound ν e htrans (N+1) N (by omega)
  simp only [pow_two,pow_one] at hh ⊢
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith : (N:ℝ) ≤ N+1)
    measureReal_nonneg))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_DurationTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma firstWordEvent_of_length_pos {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hpos : 0 < (firstWord ℓ X).length) : X ∈ FirstWordEvent ℓ (firstWord ℓ X) := by
  apply firstWordEvent_self
  by_contra hh
  simp only [firstWord,dite_eq_right hh,List.length_nil] at hpos
  omega

lemma duration_tail_cover {d : ℕ} (e : Direction d) (H T : ℕ) (hH : 0 < H)
    (X : Path d) (hNN : ∀ n, ∃ f, X (n+1)=X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e)))
    (hτ : T < (firstWord (realPosition (step e)) X).length) :
    X ∈ NoTruePastHeight e H ∪ StripUntil e H T := by
  have hw := firstWordEvent_of_length_pos (realPosition (step e)) X (by omega)
  have h0 : X 0=0 := by simpa using hw.2.1 0 (Nat.zero_le _)
  obtain ⟨n,hn⟩ := noDrop_firstLayerHit_exists e X h0 hNN ht hH
  by_cases hnT : n ≤ T
  · exact Or.inl ⟨h0,n,hn,fun t ht htn => hw.2.2.2.2 t ht (by omega)⟩
  · apply Or.inr
    refine ⟨h0,fun j hj => ⟨?_,hn.2 j (by omega)⟩⟩
    have hh := hw.1 j
    simp only [signedHeight_projection,signedHeight_zero,Int.cast_zero] at hh
    exact_mod_cast hh

lemma raw_duration_tail_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H T : ℕ) (hH : 0 < H) :
    (annealedLaw ν).real {X | T < (firstWord (realPosition (step e)) X).length} ≤
      (annealedLaw ν).real (NoTruePastHeight e H)+(annealedLaw ν).real (StripUntil e H T) := by
  apply le_trans ?_ (measureReal_union_le _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [annealed_nearest_neighbor ν,htrans] with X hNN ht
  exact duration_tail_cover e H T hH X hNN ht

lemma duration_polynomial_rapidDecay {d : ℕ} (hd : 2 ≤ d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℕ, 0 < A ∧ RapidDecay (fun N =>
      (conditionedLaw ν (realPosition (step e))).real
        {X | A*(N+1)^(4*d+2) < (firstWord (realPosition (step e)) X).length}) := by
  obtain ⟨A,hA,htime⟩ := stripTime_rapidDecay hd ν hue e htrans
  have ht := htime.comp_strictMono (fun _ => measureReal_nonneg) _ square_pred_strictMono
  have ht' : RapidDecay (fun N => (annealedLaw ν).real
      (StripUntil e ((N+1)^2) (A*(N+1)^(4*d+2)))) := by
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    ext N
    have hsq : 1 ≤ (N+1)^2 := Nat.one_le_pow _ _ (by omega)
    rw [Nat.sub_add_cancel hsq,← pow_mul,show 2*(2*d+1)=4*d+2 by omega]
  have hw := noTruePastSquare_rapidDecay hd ν hue e htrans
  have hraw : RapidDecay (fun N => (annealedLaw ν).real
      {X | A*(N+1)^(4*d+2) < (firstWord (realPosition (step e)) X).length}) := by
    apply (hw.add ht').of_le (fun _ => measureReal_nonneg)
    exact Eventually.of_forall (fun N => raw_duration_tail_bound ν e htrans ((N+1)^2) _ (by positivity))
  have hp := noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans
  have hp' : 0 < (annealedLaw ν).real (NoDrop (realPosition (step e)) 0) :=
    ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  refine ⟨A,hA,(hraw.const_mul (((annealedLaw ν).real (NoDrop (realPosition (step e)) 0))⁻¹)).of_le
    (fun _ => measureReal_nonneg) ?_⟩
  apply Eventually.of_forall
  intro N
  have hh := annealed_ge_noDrop_mul_conditioned ν (realPosition (step e)) hp.ne'
    {X | A*(N+1)^(4*d+2) < (firstWord (realPosition (step e)) X).length}
    (measurableSet_lt measurable_const ((measurable_of_countable List.length).comp (measurable_firstWord _)))
  exact (le_inv_mul_iff₀ hp').mpr hh

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_DurationMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma conditioned_wordDuration_integrable {d : ℕ} (hd : 2 ≤ d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    Integrable (fun X => ((firstWord (realPosition (step e)) X).length:ℝ))
      (conditionedLaw ν (realPosition (step e))) := by
  let : IsProbabilityMeasure (conditionedLaw ν (realPosition (step e))) :=
    conditionedLaw_probability ν _ (noDrop_positive_of_directionallyTransient ν _ htrans).ne'
  obtain ⟨A,hA,ht⟩ := duration_polynomial_rapidDecay hd ν hue e htrans
  exact natural_integrable_of_polynomial_rapid_tail _ _
    ((measurable_of_countable List.length).comp (measurable_firstWord _)) A (4*d+2) hA (by omega) ht

lemma conditioned_wordDuration_mean_positive {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (hint : Integrable (fun X => ((firstWord ℓ X).length:ℝ)) (conditionedLaw ν ℓ)) :
    0 < ∫ X, ((firstWord ℓ X).length:ℝ) ∂conditionedLaw ν ℓ := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) :=
    conditionedLaw_probability ν _ (noDrop_positive_of_directionallyTransient ν _ htrans).ne'
  have hge : (1:ℝ) ≤ ∫ X, ((firstWord ℓ X).length:ℝ) ∂conditionedLaw ν ℓ := by
    calc
      (1:ℝ) = ∫ X, (1:ℝ) ∂conditionedLaw ν ℓ := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hint (by
        filter_upwards [conditioned_firstWord_exists ν ℓ htrans] with X hX
        have hh := (firstWordEvent_self ℓ X hX).2.2.1
        exact_mod_cast hh)
  linarith

lemma conditioned_word_temporal_strong_law {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (hint : Integrable (fun X => ((firstWord ℓ X).length:ℝ)) (conditionedLaw ν ℓ)) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, Tendsto
      (fun n : ℕ => (regenerationTimes ℓ X n:ℝ)/n) atTop
      (𝓝 (∫ Y, ((firstWord ℓ Y).length:ℝ) ∂conditionedLaw ν ℓ)) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) :=
    conditionedLaw_probability ν _ (noDrop_positive_of_directionallyTransient ν _ htrans).ne'
  have hm : Measurable (fun w : List (Direction d) => (w.length:ℝ)) := measurable_of_countable _
  have ht := strong_law_ae_real (fun n X => ((regenerationWords ℓ X n).length:ℝ)) hint
    (fun i j hij => ((regenerationWords_independent ν ℓ htrans).indepFun hij).comp hm hm)
    (fun i => (regenerationWords_identDistrib ν ℓ htrans i).comp hm)
  simpa only [regenerationTimes,Nat.cast_sum,regenerationWords,Function.iterate_zero,id_eq] using ht

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma scalar_cut_speed (T : ℕ → ℕ) (hT : StrictMono T) (hT0 : T 0=0)
    (Y R : ℕ → ℝ) (m t : ℝ) (ht : 0 < t)
    (hTime : Tendsto (fun n : ℕ => (T n:ℝ)/n) atTop (𝓝 t))
    (hSpace : Tendsto (fun n : ℕ => Y (T n)/n) atTop (𝓝 m))
    (hR : Tendsto (fun n : ℕ => R n/n) atTop (𝓝 0))
    (herr : ∀ k n, T k ≤ n → n < T (k+1) → |Y n-Y (T k)| ≤ R k) :
    Tendsto (fun n : ℕ => Y n/n) atTop (𝓝 (m/t)) := by
  choose K hK using increasing_cuts_cover T hT hT0
  have hKt := increasing_cuts_index_tendsto T K hT hK
  have hr : Tendsto (fun n : ℕ => ((n:ℝ)+1)/n) atTop (𝓝 1) := by
    have hh := (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1).inv₀ (by norm_num : (1:ℝ) ≠ 0)
    simpa only [inv_one,inv_div] using hh
  have hsucc : Tendsto (fun n : ℕ => (T (n+1):ℝ)/n) atTop (𝓝 t) := by
    have hh := (hTime.comp (tendsto_add_atTop_nat 1)).mul hr
    simp only [mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
    simp only [Function.comp_def,Nat.cast_add,Nat.cast_one]
    field_simp
  have hden : Tendsto (fun n : ℕ => (n:ℝ)/K n) atTop (𝓝 t) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (hTime.comp hKt) (hsucc.comp hKt)
    · intro n
      change (T (K n):ℝ)/(K n:ℝ) ≤ (n:ℝ)/(K n:ℝ)
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hK n).1) (Nat.cast_nonneg _)
    · intro n
      change (n:ℝ)/(K n:ℝ) ≤ (T (K n+1):ℝ)/(K n:ℝ)
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hK n).2.le) (Nat.cast_nonneg _)
  have hnum : Tendsto (fun n : ℕ => Y n/K n) atTop (𝓝 m) := by
    have hlo := (hSpace.sub hR).comp hKt
    have hhi := (hSpace.add hR).comp hKt
    simp only [sub_zero,add_zero] at hlo hhi
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    · intro n
      have hh := (abs_le.mp (herr (K n) n (hK n).1 (hK n).2)).1
      have hb : Y (T (K n))-R (K n) ≤ Y n := by linarith
      simpa only [sub_div,Function.comp_def] using div_le_div_of_nonneg_right hb (Nat.cast_nonneg (K n))
    · intro n
      have hh := (abs_le.mp (herr (K n) n (hK n).1 (hK n).2)).2
      have hb : Y n ≤ Y (T (K n))+R (K n) := by linarith
      simpa only [add_div,Function.comp_def] using div_le_div_of_nonneg_right hb (Nat.cast_nonneg (K n))
  apply (hnum.div hden ht.ne').congr'
  filter_upwards [hKt.eventually (eventually_gt_atTop (0:ℕ)),eventually_gt_atTop (0:ℕ)] with n hn hn'
  have hk : (K n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn'.ne'
  change (Y n/(K n:ℝ))/((n:ℝ)/(K n:ℝ)) = Y n/(n:ℝ)
  field_simp

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma measurableSet_velocityPaths {d : ℕ} (v : Vector d) : MeasurableSet (VelocityPaths v) := by
  apply measurableSet_tendsto
  intro n
  exact (measurable_of_countable (fun y : Lattice d => fun i => (y i:ℝ)/(n:ℝ))).comp
    (measurable_pi_apply n)

lemma velocityPaths_of_suffix {d : ℕ} (v : Vector d) (X : Path d) (n : ℕ)
    (ht : (fun j => X (n+j)-X n) ∈ VelocityPaths v) : X ∈ VelocityPaths v := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hh := tendsto_pi_nhds.mp ht i
  have hz : Tendsto (fun j : ℕ => (X n i:ℝ)/j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)) :
        Tendsto (fun j : ℕ => (X n i:ℝ)*(j:ℝ)⁻¹) atTop (𝓝 ((X n i:ℝ)*0)))
  have hs : Tendsto (fun j : ℕ => (X (n+j) i:ℝ)/j) atTop (𝓝 (v i)) := by
    convert hh.add hz using 1 <;> first | (with_reducible_and_instances rfl) | (simp [Pi.sub_apply,Int.cast_sub,sub_div])
  have hp := hs.mul (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (n:ℝ))
  simp only [mul_one] at hp
  apply (tendsto_add_atTop_iff_nat n).mp
  apply hp.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with j hj
  have hj' : (j:ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  change (X (n+j) i:ℝ)/(j:ℝ) * ((j:ℝ)/((j:ℝ)+(n:ℝ))) =
    (X (j+n) i:ℝ)/(j+n:ℕ)
  rw [Nat.add_comm j n]
  simp only [Nat.cast_add]
  field_simp
  ring

lemma conditioned_to_annealed_velocity {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (v : Vector d)
    (hv : ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ VelocityPaths v) : HasVelocity ν v := by
  let B := NoDrop ℓ 0 ∩ (VelocityPaths v)ᶜ
  have hB : MeasurableSet B := (measurableSet_noDrop ℓ 0).inter (measurableSet_velocityPaths v).compl
  have hBD : B ⊆ NoDrop ℓ 0 := Set.inter_subset_left
  have hcB : conditionedLaw ν ℓ B=0 := measure_mono_null Set.inter_subset_right (ae_iff.mp hv)
  have haB : annealedLaw ν B=0 := by
    rw [conditionedLaw_apply_of_subset ν ℓ B hB hBD] at hcB
    exact (mul_eq_zero.mp hcB).resolve_left (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
  have hwords : ∀ᵐ X ∂annealedLaw ν, ∀ w : List (Direction d),
      (∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
        dot (realPosition (wordPath 0 w w.length)) ℓ) →
      X ∈ wordCylinder 0 w →
      (fun j => X (w.length+j)-wordPath 0 w w.length) ∉ B := by
    apply ae_all_iff.mpr
    intro w
    by_cases hw : ∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
      dot (realPosition (wordPath 0 w w.length)) ℓ
    · have hz := annealed_record_suffix ν ℓ w hw B hB hBD
      rw [haB,mul_zero] at hz
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with X hX _ hcy
      exact fun hh => hX ⟨hh,hcy⟩
    · exact Eventually.of_forall fun _ h _ => (hw h).elim
  filter_upwards [annealed_initial ν,annealed_nearest_neighbor ν,
    annealed_trueRecords_unbounded ν ℓ htrans,hwords] with X h0 hNN hrec hwords
  obtain ⟨n,_,hn⟩ := hrec 0
  obtain ⟨w,hw,hcy⟩ := exists_word_prefix X hNN n
  rw [h0] at hcy
  have hwend : wordPath 0 w w.length=X n := by rw [← hw]; exact (hcy _ le_rfl).symm
  have hwrec : ∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
      dot (realPosition (wordPath 0 w w.length)) ℓ := by
    intro y hy
    obtain ⟨j,hj,rfl⟩ := (wordDepartures_mem_iff 0 y w).mp hy
    rw [← hcy j hj.le,hwend]
    exact hn.1 j (by omega)
  have hnot := hwords w hwrec hcy
  have hD : (fun j => X (w.length+j)-wordPath 0 w w.length) ∈ NoDrop ℓ 0 := by
    intro j
    rw [hwend,hw,dot_realPosition_sub]
    have hh := hn.2 j
    simpa only [dot,realPosition,Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero,
      sub_nonneg] using hh
  apply velocityPaths_of_suffix v X n
  by_contra hh
  apply hnot
  refine ⟨hD,?_⟩
  change (fun j => X (w.length+j)-wordPath 0 w w.length) ∉ VelocityPaths v
  rw [hwend,hw]
  exact hh

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_VelocityWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma conditioned_velocity_from_duration {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ=1)
    (htrans : DirectionallyTransient ν ℓ)
    (hint : Integrable (fun X => ((firstWord ℓ X).length:ℝ)) (conditionedLaw ν ℓ)) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ VelocityPaths (renewalVelocity ν ℓ) := by
  have ht := conditioned_wordDuration_mean_positive ν ℓ htrans hint
  filter_upwards [conditioned_regenerationSupport ν ℓ htrans,
    conditioned_word_temporal_strong_law ν ℓ htrans hint,
    ae_all_iff.mpr (fun i : Fin d => conditioned_word_spatial_strong_laws ν hue ℓ hℓ htrans (i,true))]
      with X hX hTime hSpace
  apply tendsto_pi_nhds.mpr
  intro i
  change Tendsto (fun n : ℕ => signedCoordinate (i,true) (X n)/n) atTop (𝓝 _)
  apply scalar_cut_speed (regenerationTimes ℓ X) (regenerationTimes_strictMono ℓ X hX.2)
    (regenerationTimes_zero ℓ X) (fun n => signedCoordinate (i,true) (X n))
    (fun n => wordRadius (regenerationWords ℓ X n)) _ _ ht hTime
  · simpa only [regeneration_coordinate_sum ℓ (i,true) X hX] using (hSpace i).1
  · exact (hSpace i).2
  · intro k n hlo hhi
    have hnk : n=regenerationTimes ℓ X k+(n-regenerationTimes ℓ X k) := by omega
    have hlen : n-regenerationTimes ℓ X k ≤ (regenerationWords ℓ X k).length := by
      rw [regenerationTimes_succ] at hhi
      omega
    have hh := regeneration_span ℓ X hX.1 hX.2 k _ hlen
    rw [← hnk] at hh
    rw [hh,signedCoordinate_add,add_sub_cancel_left]
    exact (signedCoordinate_abs_le_norm _ _).trans (wordRadius_bound _ hlen)

lemma renewalVelocity_projection {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ=1)
    (htrans : DirectionallyTransient ν ℓ) :
    dot (renewalVelocity ν ℓ) ℓ =
      (∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂conditionedLaw ν ℓ) /
        (∫ X, ((firstWord ℓ X).length:ℝ) ∂conditionedLaw ν ℓ) := by
  have hint (i : Fin d) : Integrable (fun X => wordCoordinate (i,true) (firstWord ℓ X)*ℓ i)
      (conditionedLaw ν ℓ) := (conditioned_wordCoordinate_integrable ν hue ℓ hℓ htrans (i,true)).mul_const _
  have hid : (∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂conditionedLaw ν ℓ) =
      ∑ i : Fin d, (∫ X, wordCoordinate (i,true) (firstWord ℓ X) ∂conditionedLaw ν ℓ)*ℓ i := by
    change (∫ X, ∑ i : Fin d, wordCoordinate (i,true) (firstWord ℓ X)*ℓ i ∂conditionedLaw ν ℓ)=_
    rw [integral_finsetSum _ (fun i _ => hint i)]
    exact Finset.sum_congr rfl (fun i _ => integral_mul_const _ _)
  rw [hid,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  change (_ / _)*_=(_*_)/_
  ring

lemma velocity_from_integrable_words {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ=1)
    (htrans : DirectionallyTransient ν ℓ)
    (hint : Integrable (fun X => ((firstWord ℓ X).length:ℝ)) (conditionedLaw ν ℓ)) :
    0 < dot (renewalVelocity ν ℓ) ℓ ∧ HasVelocity ν (renewalVelocity ν ℓ) := by
  constructor
  · rw [renewalVelocity_projection ν hue ℓ hℓ htrans]
    exact div_pos (conditioned_wordHeightGain_moments ν ℓ (unit_direction_coordinate_bound ℓ hℓ) htrans).2.1
      (conditioned_wordDuration_mean_positive ν ℓ htrans hint)
  · exact conditioned_to_annealed_velocity ν ℓ htrans _
      (conditioned_velocity_from_duration ν hue ℓ hℓ htrans hint)

lemma signed_coordinate_ballisticity {d : ℕ} (hd : 2 ≤ d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ v : Vector d, 0 < dot v (realPosition (step e)) ∧ HasVelocity ν v := by
  exact ⟨renewalVelocity ν (realPosition (step e)),velocity_from_integrable_words ν hue _
    (signed_direction_unit e) htrans (conditioned_wordDuration_integrable hd ν hue e htrans)⟩

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma velocityPaths_projection {d : ℕ} (v ℓ : Vector d) (X : Path d)
    (hX : X ∈ VelocityPaths v) :
    Tendsto (fun n : ℕ => dot (realPosition (X n)) ℓ/(n:ℝ)) atTop (𝓝 (dot v ℓ)) := by
  have hh := tendsto_finsetSum Finset.univ (fun i _ =>
    (tendsto_pi_nhds.mp hX i).mul_const (ℓ i))
  simpa only [dot,realPosition,Finset.sum_div,div_mul_eq_mul_div] using hh

lemma conditioned_word_height_strong_law {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hℓ : dot ℓ ℓ=1) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, Tendsto
      (fun n : ℕ => dot (realPosition (X (regenerationTimes ℓ X n))) ℓ/n) atTop
      (𝓝 (∫ Y, wordHeightGain ℓ (firstWord ℓ Y) ∂conditionedLaw ν ℓ)) := by
  have hm : Measurable (wordHeightGain ℓ) := measurable_of_countable _
  have ht := strong_law_ae_real (fun n X => wordHeightGain ℓ (regenerationWords ℓ X n))
    (conditioned_wordHeightGain_moments ν ℓ (unit_direction_coordinate_bound ℓ hℓ) htrans).1
    (fun i j hij => ((regenerationWords_independent ν ℓ htrans).indepFun hij).comp hm hm)
    (fun i => (regenerationWords_identDistrib ν ℓ htrans i).comp hm)
  filter_upwards [conditioned_regenerationSupport ν ℓ htrans,ht] with X hX ht
  simpa only [regeneration_height_sum ℓ X hX.1 hX.2,regenerationWords,Function.iterate_zero,id_eq] using ht

lemma velocity_positive_original_direction {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ=1)
    (htrans : DirectionallyTransient ν ℓ) (e : Direction d)
    (he : 0 < ∫ X, wordCoordinate e (firstWord ℓ X) ∂conditionedLaw ν ℓ)
    (v : Vector d) (hv : HasVelocity ν v) (hve : 0 < dot v (realPosition (step e))) :
    0 < dot v ℓ := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) :=
    conditionedLaw_probability ν _ (noDrop_positive_of_directionallyTransient ν _ htrans).ne'
  have hvc : ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ VelocityPaths v :=
    (conditionedLaw_absolutelyContinuous ν ℓ).ae_le hv
  have hfull := (conditioned_regenerationSupport ν ℓ htrans).and
    ((conditioned_word_height_strong_law ν ℓ hℓ htrans).and
      ((conditioned_word_spatial_strong_laws ν hue ℓ hℓ htrans e).and hvc))
  obtain ⟨X,hX,hH,hC,hvX⟩ := hfull.exists
  have hT := (regenerationTimes_strictMono ℓ X hX.2).tendsto_atTop
  have hvH := (velocityPaths_projection v ℓ X hvX).comp hT
  have hvC := (velocityPaths_projection v (realPosition (step e)) X hvX).comp hT
  simp only [Function.comp_def,dot_signed_direction] at hvC
  have hC' : Tendsto (fun n : ℕ => signedCoordinate e (X (regenerationTimes ℓ X n))/n)
      atTop (𝓝 (∫ Y, wordCoordinate e (firstWord ℓ Y) ∂conditionedLaw ν ℓ)) := by
    simpa only [regeneration_coordinate_sum ℓ e X hX] using hC.1
  have hp := hH.mul hvC
  have hq := hC'.mul hvH
  have hid : (fun n : ℕ =>
      (dot (realPosition (X (regenerationTimes ℓ X n))) ℓ/(n:ℝ)) *
      (signedCoordinate e (X (regenerationTimes ℓ X n))/(regenerationTimes ℓ X n:ℝ))) =
      (fun n : ℕ => (signedCoordinate e (X (regenerationTimes ℓ X n))/(n:ℝ)) *
      (dot (realPosition (X (regenerationTimes ℓ X n))) ℓ/(regenerationTimes ℓ X n:ℝ))) := by
    funext n
    ring
  simp only [Function.comp_def] at hp hq
  rw [hid] at hp
  have hlim := tendsto_nhds_unique hp hq
  have hh := (conditioned_wordHeightGain_moments ν ℓ
    (unit_direction_coordinate_bound ℓ hℓ) htrans).2.1
  have hm : 0 < (∫ X, wordCoordinate e (firstWord ℓ X) ∂conditionedLaw ν ℓ)*dot v ℓ := by
    rw [← hlim]
    exact mul_pos hh hve
  exact (mul_pos_iff.mp hm).resolve_right (fun h => (not_lt_of_ge he.le h.1)) |>.2

theorem directional_transience_implies_ballisticity_unit {d : ℕ} (hd : 2 ≤ d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (ℓ : Vector d) (hℓ : dot ℓ ℓ=1) (htrans : DirectionallyTransient ν ℓ) :
    ∃ v : Vector d, 0 < dot v ℓ ∧ HasVelocity ν v := by
  obtain ⟨e,he⟩ := conditioned_coordinate_positive_mean ν hue ℓ hℓ htrans
  have hte : DirectionallyTransient ν (realPosition (step e)) := by
    apply conditioned_to_annealed_transience ν ℓ _ htrans
    simpa only [TransientPaths,Set.mem_ofPred_eq,dot_signed_direction] using
      conditioned_coordinate_transience ν hue ℓ hℓ htrans e he
  obtain ⟨v,hve,hv⟩ := signed_coordinate_ballisticity hd ν hue e hte
  exact ⟨v,velocity_positive_original_direction ν hue ℓ hℓ htrans e he v hv hve,hv⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

theorem directional_transience_implies_ballisticity_oai : MainStatement := by
  intro d hd ν hν hue ℓ hℓ htrans
  exact directional_transience_implies_ballisticity_unit hd ν hue ℓ hℓ htrans

end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.directional_transience_implies_ballisticity_oai := @OAI.DirectionalTransience.directional_transience_implies_ballisticity_oai
