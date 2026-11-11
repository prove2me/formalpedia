-- Prove2me | solution 1 for OAI.DirectionalTransience.spatial_confinement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:53:51.593898+00:00
-- url     : https://prove2.me/submissions/5fc06259-4b50-4a65-9852-45c1bf174a4a

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Theorems.Thm_OAI_DirectionalTransience_conditioned_wordRadius_integrable

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_LowerClip
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

lemma prefixMax_nonneg (z : ℕ → ℝ) (n : ℕ) : 0 ≤ prefixMax z n := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih.trans (le_max_left _ _)

lemma le_prefixMax (z : ℕ → ℝ) {j n : ℕ} (hj : j < n) : z j ≤ prefixMax z n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
    · exact (ih h).trans (le_max_left _ _)
    · exact le_max_right _ _

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

lemma wordPath_replicate {d : ℕ} (x : Lattice d) (e : Direction d) (N : ℕ) :
    wordPath x (List.replicate N e) N = x + N • step e := by
  induction N generalizing x with
  | zero => simp
  | succ N ih =>
    simp only [List.replicate_succ, wordPath, ih, succ_nsmul]
    abel

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

lemma nonnegative_interval_count (a : ℝ) (ha : 0 ≤ a) (K : ℕ)
    (u b : ℕ → ℝ) (hu : ∀ i, 0 ≤ u i) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hw : ∀ i, b i ≠ 0 → ∃ k, 0 < k ∧ k ≤ K ∧
      a * (k : ℝ) ≤ ∑ j ∈ Finset.range k, u (i+j))
    (M : ℕ) : a * (∑ i ∈ Finset.range M, b i) ≤
      ∑ i ∈ Finset.range (M+K), u i := by
  induction M using Nat.strong_induction_on generalizing u b with
  | h M ih =>
    by_cases hM : M = 0
    · subst M
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Nat.zero_add]
      exact Finset.sum_nonneg fun i _ => hu i
    by_cases hb0 : b 0 = 0
    · have hrec := ih (M-1) (by omega) (fun i => u (1+i)) (fun i => b (1+i))
        (fun i => hu _) (fun i => hb _) (by
          intro i hi
          obtain ⟨k,hk,hkK,hku⟩ := hw (1+i) hi
          exact ⟨k,hk,hkK,by simpa only [Nat.add_assoc] using hku⟩)
      have hfirst : (∑ i ∈ Finset.range M, b i) = ∑ i ∈ Finset.range (M-1), b (1+i) := by
        conv_lhs => rw [show M = 1+(M-1) by omega, Finset.sum_range_add, Finset.sum_range_one,
          hb0, zero_add]
      rw [hfirst]
      calc
        _ ≤ ∑ i ∈ Finset.range (M-1+K), u (1+i) := hrec
        _ ≤ u 0 + ∑ i ∈ Finset.range (M-1+K), u (1+i) := le_add_of_nonneg_left (hu 0)
        _ = _ := by
          conv_rhs => rw [show M+K = 1+(M-1+K) by omega, Finset.sum_range_add,
            Finset.sum_range_one]
    · obtain ⟨k,hk,hkK,hkw⟩ := hw 0 hb0
      simp only [Nat.zero_add] at hkw
      by_cases hkM : k ≤ M
      · have hrec := ih (M-k) (by omega) (fun i => u (k+i)) (fun i => b (k+i))
          (fun i => hu _) (fun i => hb _) (by
            intro i hi
            obtain ⟨l,hl,hlK,hlu⟩ := hw (k+i) hi
            exact ⟨l,hl,hlK,by simpa only [Nat.add_assoc] using hlu⟩)
        have hbfirst : (∑ i ∈ Finset.range k, b i) ≤ (k : ℝ) := by
          calc
            _ ≤ ∑ i ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hb i).2
            _ = _ := by simp
        calc
          _ = a * (∑ i ∈ Finset.range k, b i) +
              a * (∑ i ∈ Finset.range (M-k), b (k+i)) := by
            conv_lhs => arg 2; rw [show M = k+(M-k) by omega, Finset.sum_range_add]
            rw [mul_add]
          _ ≤ (∑ i ∈ Finset.range k, u i) +
              (∑ i ∈ Finset.range (M-k+K), u (k+i)) :=
            add_le_add ((mul_le_mul_of_nonneg_left hbfirst ha).trans hkw) hrec
          _ = _ := by
            conv_rhs => rw [show M+K = k+(M-k+K) by omega, Finset.sum_range_add]
      · have hbfirst : (∑ i ∈ Finset.range M, b i) ≤ (k : ℝ) := by
          calc
            _ ≤ ∑ i ∈ Finset.range M, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hb i).2
            _ = (M : ℝ) := by simp
            _ ≤ k := Nat.cast_le.mpr (by omega)
        exact ((mul_le_mul_of_nonneg_left hbfirst ha).trans hkw).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            (fun i _ _ => hu i))

lemma stationary_initial_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (f : Ω → ℝ) (hf : Measurable f) (hfi : Integrable f μ) (hfn : ∀ x, 0 ≤ f x)
    (K : ℕ) (a : ℝ) (ha : 0 < a) :
    a * μ.real {x | ∃ k, 0 < k ∧ k ≤ K ∧
      a * (k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)} ≤ ∫ x, f x ∂μ := by
  classical
  let B : Set Ω := {x | ∃ k, 0 < k ∧ k ≤ K ∧
    a * (k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)}
  have hB : MeasurableSet B := by
    simp only [B, Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro k
    have hs : Measurable (fun x => ∑ j ∈ Finset.range k, f (T^[j] x)) :=
      Finset.measurable_fun_sum _ (fun j _ => hf.comp (hT.iterate j).measurable)
    by_cases h0 : 0 < k
    · by_cases hk : k ≤ K
      · simpa only [h0, hk, true_and] using measurableSet_lt measurable_const hs
      · simp only [hk, false_and, and_false, Set.ofPred_false]; exact MeasurableSet.empty
    · simp only [h0, false_and, Set.ofPred_false]; exact MeasurableSet.empty
  let b : Ω → ℝ := B.indicator (fun _ => (1 : ℝ))
  have hbi : Integrable b μ := integrable_const _ |>.indicator hB
  have hb (x : Ω) : 0 ≤ b x ∧ b x ≤ 1 := by
    simp only [b, Set.indicator]; split <;> norm_num
  have hcomp (g : Ω → ℝ) (hg : Integrable g μ) (n : ℕ) :
      Integrable (fun x => g (T^[n] x)) μ ∧ (∫ x, g (T^[n] x) ∂μ) = ∫ x, g x ∂μ := by
    refine ⟨(hT.iterate n).integrable_comp_of_integrable hg, ?_⟩
    have hgm : AEStronglyMeasurable g (μ.map (T^[n])) := by
      rw [(hT.iterate n).map_eq]
      exact hg.aestronglyMeasurable
    rw [← integral_map (hT.iterate n).measurable.aemeasurable hgm, (hT.iterate n).map_eq]
  have hbi' : (∫ x, b x ∂μ) = μ.real B := by
    exact integral_indicator_one hB
  have hbme (M : ℕ) : (∫ x, ∑ i ∈ Finset.range M, b (T^[i] x) ∂μ) = M * μ.real B := by
    rw [integral_finsetSum _ (fun i _ => (hcomp b hbi i).1)]
    simp_rw [(hcomp b hbi _).2, hbi']
    simp
  have hfme (M : ℕ) : (∫ x, ∑ i ∈ Finset.range M, f (T^[i] x) ∂μ) = M * ∫ x, f x ∂μ := by
    rw [integral_finsetSum _ (fun i _ => (hcomp f hfi i).1)]
    simp_rw [(hcomp f hfi _).2]
    simp
  have hbound (M : ℕ) : a * ((M : ℝ) * μ.real B) ≤ ((M+K : ℕ) : ℝ) * ∫ x, f x ∂μ := by
    have hpt (x : Ω) : a * (∑ i ∈ Finset.range M, b (T^[i] x)) ≤
        ∑ i ∈ Finset.range (M+K), f (T^[i] x) := by
      apply nonnegative_interval_count a ha.le K _ _ (fun i => hfn _) (fun i => hb _)
      intro i hi
      have hmem : T^[i] x ∈ B := by
        by_contra h
        exact hi (Set.indicator_of_notMem h _)
      obtain ⟨k, hk, hkK, hkg⟩ := hmem
      refine ⟨k, hk, hkK, ?_⟩
      simpa only [← Function.iterate_add_apply, Nat.add_comm] using hkg.le
    have hintb : Integrable (fun x => a * ∑ i ∈ Finset.range M, b (T^[i] x)) μ :=
      (integrable_finsetSum _ (fun i _ => (hcomp b hbi i).1)).const_mul a
    have hintf : Integrable (fun x => ∑ i ∈ Finset.range (M+K), f (T^[i] x)) μ :=
      integrable_finsetSum _ (fun i _ => (hcomp f hfi i).1)
    have h := integral_mono hintb hintf hpt
    simpa only [integral_const_mul, hbme, hfme] using h
  change a * μ.real B ≤ ∫ x, f x ∂μ
  by_contra h
  have hδ : 0 < a * μ.real B - ∫ x, f x ∂μ := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨M, hM⟩ := exists_nat_gt ((K : ℝ) * (∫ x, f x ∂μ) /
    (a * μ.real B - ∫ x, f x ∂μ))
  have hgt := (div_lt_iff₀ hδ).mp hM
  have hle := hbound M
  push_cast at hle
  nlinarith

lemma integrable_min_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun x => min (f x) s) μ := by
  apply (integrable_const s).mono' (hf.min measurable_const).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hfn x) hs)]
    exact min_le_right _ _

lemma truncatedMean_mul_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {s c : ℝ} (hs : 0 ≤ s) (hc : 1 ≤ c) :
    truncatedMean μ f (c*s) ≤ c * truncatedMean μ f s := by
  rw [truncatedMean, truncatedMean, ← integral_const_mul]
  apply integral_mono (integrable_min_nonneg μ f hf hfn _ (mul_nonneg (by linarith) hs))
    ((integrable_min_nonneg μ f hf hfn s hs).const_mul c)
  intro x
  dsimp only
  by_cases h : f x ≤ s
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (le_mul_of_one_le_left (hfn x) hc)
  · rw [min_eq_right (le_of_not_ge h)]
    exact min_le_right _ _

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

lemma stationary_initial_average_truncated_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (f : Ω → ℝ) (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (K : ℕ) (a : ℝ) (ha : 0 < a) :
    a * μ.real {x | ∃ k, 0 < k ∧ k ≤ K ∧
      a * (k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)} ≤
      2 * truncatedMean μ f (a*K) := by
  let g : Ω → ℝ := fun x => min (f x) (a*K)
  have hg : Measurable g := hf.min measurable_const
  have hgn (x : Ω) : 0 ≤ g x := le_min (hfn x) (mul_nonneg ha.le (Nat.cast_nonneg _))
  have hgi : Integrable g μ := integrable_min_nonneg μ f hf hfn _
    (mul_nonneg ha.le (Nat.cast_nonneg _))
  have hsub : {x | ∃ k, 0 < k ∧ k ≤ K ∧
        a * (k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)} ⊆
      {x | ∃ k, 0 < k ∧ k ≤ K ∧
        (a/2) * (k : ℝ) < ∑ j ∈ Finset.range k, g (T^[j] x)} := by
    intro x hx
    obtain ⟨k,hk,hkK,hs⟩ := hx
    refine ⟨k,hk,hkK,?_⟩
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    by_cases ht : ∀ j ∈ Finset.range k, f (T^[j] x) ≤ a*K
    · have he : (∑ j ∈ Finset.range k, g (T^[j] x)) =
          ∑ j ∈ Finset.range k, f (T^[j] x) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact min_eq_left (ht j hj)
      rw [he]
      nlinarith
    · obtain ⟨j,hj,hjt⟩ : ∃ j ∈ Finset.range k, a*K < f (T^[j] x) := by
        simpa only [not_forall, not_le, exists_prop] using ht
      have hle : a*(k : ℝ) ≤ ∑ j ∈ Finset.range k, g (T^[j] x) := by
        calc
          _ ≤ a*K := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hkK) ha.le
          _ = g (T^[j] x) := (min_eq_right hjt.le).symm
          _ ≤ _ := Finset.single_le_sum (fun i (_ : i ∈ Finset.range k) => hgn (T^[i] x)) hj
      nlinarith
  have hme := measureReal_mono (μ := μ) hsub
  have hb := stationary_initial_average_bound μ T hT g hg hgi hgn K (a/2) (by linarith)
  change (a/2) * _ ≤ truncatedMean μ f (a*K) at hb
  have hm := mul_le_mul_of_nonneg_left hme (show 0 ≤ a/2 by linarith)
  linarith

lemma latticeVector_add {d : ℕ} (x y : Lattice d) :
    latticeVector (x+y) = latticeVector x + latticeVector y := by
  ext i
  simp [latticeVector, realPosition]

lemma latticeVector_step_norm {d : ℕ} (e : Direction d) : ‖latticeVector (step e)‖ = 1 := by
  have hs : ‖latticeVector (step e)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [latticeVector, realPosition, step,
      Int.cast_ite, Int.cast_one, Int.cast_neg, Int.cast_zero, ite_pow, zero_pow (by norm_num : 2 ≠ 0)]
    simp
  nlinarith [norm_nonneg (latticeVector (step e))]

lemma wordRadius_bound {d : ℕ} (w : List (Direction d)) {j : ℕ} (hj : j ≤ w.length) :
    ‖latticeVector (wordPath 0 w j)‖ ≤ wordRadius w := by
  classical
  exact Finset.le_sup' (fun j => ‖latticeVector (wordPath 0 w j)‖)
    (Finset.mem_range.mpr (by omega))

lemma wordRadius_nonneg {d : ℕ} (w : List (Direction d)) : 0 ≤ wordRadius w := by
  have hh := wordRadius_bound w (j := 0) (by omega)
  simpa only [wordPath_zero, latticeVector_zero, norm_zero] using hh

lemma measurable_wordRadius {d : ℕ} : Measurable (wordRadius (d := d)) := measurable_of_countable _

lemma affine_envelope_of_average_limit (H : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (hlim : Tendsto (fun n : ℕ => H n / n) atTop (𝓝 L)) :
    ∃ C0 : ℕ, ∀ n : ℕ, (L/2)*n-C0 ≤ H n ∧ H n ≤ (2*L)*n+C0 := by
  have hevent : ∀ᶠ n : ℕ in atTop, L/2 < H n / n ∧ H n / n < 2*L :=
    hlim.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨N,hN⟩ := (eventually_atTop.1 hevent)
  let M := max N 1
  let B : ℝ := (∑ j ∈ Finset.range M, |H j|) + 2*L*M
  obtain ⟨C0,hC0⟩ := exists_nat_ge B
  refine ⟨C0, fun n => ?_⟩
  by_cases hn : M ≤ n
  · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by dsimp [M] at hn; omega)
    obtain ⟨hl,hu⟩ := hN n (by dsimp [M] at hn; omega)
    have hl' := (lt_div_iff₀ hn0).mp hl
    have hu' := (div_lt_iff₀ hn0).mp hu
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) C0]
  · have hn' : n ∈ Finset.range M := Finset.mem_range.mpr (by omega)
    have hnM : (n : ℝ) ≤ M := Nat.cast_le.mpr (by omega)
    have hs : |H n| ≤ ∑ j ∈ Finset.range M, |H j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (H j)) hn'
    have hs0 : 0 ≤ ∑ j ∈ Finset.range M, |H j| :=
      Finset.sum_nonneg fun j _ => abs_nonneg (H j)
    dsimp only [B] at hC0
    constructor <;> nlinarith [le_abs_self (H n), neg_abs_le (H n),
      Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) M]

lemma uniform_affine_envelope_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℕ → Ω → ℝ) (L : ℝ) (hL : 0 < L)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => H n x / n) atTop (𝓝 L))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C0 : ℕ, 1-ε < μ.real {x | ∀ n : ℕ, (L/2)*n-C0 ≤ H n x ∧
      H n x ≤ (2*L)*n+C0} := by
  let E : ℕ → Set Ω := fun C0 => {x | ∀ n : ℕ, (L/2)*n-C0 ≤ H n x ∧
    H n x ≤ (2*L)*n+C0}
  have hmono : Monotone E := by
    intro i j hij x hx n
    have hi := hx n
    have hij' : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
    constructor <;> linarith
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ C0, E C0 := by
    filter_upwards [hlim] with x hx
    obtain ⟨C0,hC0⟩ := affine_envelope_of_average_limit (fun n => H n x) L hL hx
    exact Set.mem_iUnion.mpr ⟨C0,hC0⟩
  have hme : μ (⋃ C0, E C0) = 1 := by
    rw [← measure_univ (μ := μ)]
    apply measure_congr
    filter_upwards [hae] with x hx
    exact propext (iff_true_intro hx)
  have ht := (ENNReal.tendsto_toReal (measure_ne_top μ (⋃ C0, E C0))).comp
    (tendsto_measure_iUnion_atTop (μ := μ) hmono)
  rw [hme, ENNReal.toReal_one] at ht
  have he := ht.eventually (Ioi_mem_nhds (show 1-ε < 1 by linarith))
  obtain ⟨C0,hC0⟩ := he.exists
  exact ⟨C0,hC0⟩

lemma conditioned_height_template {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hℓ : ∀ i, |ℓ i| ≤ 1) (htrans : DirectionallyTransient ν ℓ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ C0 : ℕ,
      1-ε < (conditionedLaw ν ℓ).real {X | ∀ k : ℕ,
        c*k-C0 ≤ ∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j) ∧
        (∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) ≤ C*k+C0} := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  obtain ⟨hint,hpositive,_⟩ := conditioned_wordHeightGain_moments ν ℓ hℓ htrans
  let L := ∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂conditionedLaw ν ℓ
  have hmeas : Measurable (wordHeightGain ℓ) := measurable_of_countable _
  have hlim : ∀ᵐ X ∂conditionedLaw ν ℓ, Tendsto
      (fun k : ℕ => (∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) / k)
      atTop (𝓝 L) := by
    exact strong_law_ae_real _ hint
      (fun i j hij => ((regenerationWords_independent ν ℓ htrans).indepFun hij).comp hmeas hmeas)
      (fun i => (regenerationWords_identDistrib ν ℓ htrans i).comp hmeas)
  obtain ⟨C0,hC0⟩ := uniform_affine_envelope_probability (conditionedLaw ν ℓ)
    (fun k X => ∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j))
    L hpositive hlim ε hε
  exact ⟨L/2,2*L,by linarith,by linarith,C0,hC0⟩

lemma truncated_template_failure_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (η a : ℝ) (ha : 0 < a) (C1 N : ℕ) (hC1 : 1 ≤ C1)
    (hI : truncatedMean μ f (a*N) < 2*η*a) :
    μ.real {x | ∃ k, 0 < k ∧ k ≤ C1*N ∧
      a*(k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)} < 4*C1*η := by
  have hb := stationary_initial_average_truncated_bound μ T hT f hf hfn (C1*N) a ha
  have hc : (1 : ℝ) ≤ C1 := by exact_mod_cast hC1
  have hs := truncatedMean_mul_le μ f hf hfn
    (mul_nonneg ha.le (Nat.cast_nonneg N)) hc
  have he : a*(C1*N : ℕ) = (C1 : ℝ)*(a*N) := by push_cast <;> ring
  rw [he] at hb
  have hC1pos : (0 : ℝ) < C1 := lt_of_lt_of_le zero_lt_one hc
  have hmul := mul_lt_mul_of_pos_left hI hC1pos
  have hh : a * μ.real {x | ∃ k, 0 < k ∧ k ≤ C1*N ∧
      a*(k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)} < a*(4*C1*η) := by
    nlinarith
  exact (mul_lt_mul_iff_right₀ ha).mp hh

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

lemma measurableSet_wordTemplate {d : ℕ} (ℓ : Vector d) (c C C0 a : ℝ) (K : ℕ) :
    MeasurableSet (WordTemplate ℓ c C C0 a K) := by
  simp only [WordTemplate, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro _
  have hL : Measurable (fun X => ∑ j ∈ Finset.range k,
      wordHeightGain ℓ (regenerationWords ℓ X j)) :=
    Finset.measurable_fun_sum _ fun j _ =>
      (measurable_of_countable (wordHeightGain ℓ)).comp (measurable_regenerationWord ℓ j)
  have hR : Measurable (fun X => ∑ j ∈ Finset.range k,
      wordRadius (regenerationWords ℓ X j)) :=
    Finset.measurable_fun_sum _ fun j _ => measurable_wordRadius.comp (measurable_regenerationWord ℓ j)
  exact (measurableSet_le measurable_const hL).inter
    ((measurableSet_le hL measurable_const).inter (measurableSet_le hR measurable_const))

lemma controlled_template_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (c C C0 η a : ℝ) (ha : 0 < a) (C1 N : ℕ) (hC1 : 1 ≤ C1)
    (hheight : (19/20 : ℝ) < (conditionedLaw ν ℓ).real {X | ∀ k : ℕ,
      c*k-C0 ≤ ∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j) ∧
      (∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) ≤ C*k+C0})
    (hsmall : 4*C1*η < 1/10)
    (hI : truncatedMean (conditionedLaw ν ℓ) (fun X => wordRadius (firstWord ℓ X)) (a*N) < 2*η*a) :
    (4/5 : ℝ) < (conditionedLaw ν ℓ).real (WordTemplate ℓ c C C0 a (C1*N)) := by
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let E : Set (Path d) := {X | ∀ k : ℕ,
    c*k-C0 ≤ ∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j) ∧
      (∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) ≤ C*k+C0}
  let F : Set (Path d) := {X | ∃ k, 0 < k ∧ k ≤ C1*N ∧
    a*k < ∑ j ∈ Finset.range k, wordRadius (regenerationWords ℓ X j)}
  have hf : μ.real F < 4*C1*η := truncated_template_failure_bound μ _
    (renewSuffix_preserves_conditioned ν ℓ htrans) _
    (measurable_wordRadius.comp (measurable_firstWord ℓ)) (fun _ => wordRadius_nonneg _)
    η a ha C1 N hC1 hI
  have hsub : E ⊆ WordTemplate ℓ c C C0 a (C1*N) ∪ F := by
    intro X hX
    by_cases hF : X ∈ F
    · exact Or.inr hF
    · left
      intro k hk
      refine ⟨(hX k).1,(hX k).2, ?_⟩
      by_contra h
      have hk0 : 0 < k := by
        by_contra hk0
        have he : k = 0 := by omega
        simp [he] at h
      exact hF ⟨k,hk0,hk,lt_of_not_ge h⟩
  have hu := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  change 19/20 < μ.real E at hheight
  change 4/5 < μ.real (WordTemplate ℓ c C C0 a (C1*N))
  linarith

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

lemma prefixMax_mono (z : ℕ → ℝ) : Monotone (prefixMax z) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

lemma prefixMax_le_iff (z : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    prefixMax z n ≤ r ↔ 0 ≤ r ∧ ∀ j < n, z j ≤ r := by
  induction n with
  | zero => simp [prefixMax]
  | succ n ih =>
    simp only [prefixMax, max_le_iff, ih]
    constructor
    · rintro ⟨⟨hr,h⟩,hn⟩
      refine ⟨hr,fun j hj => ?_⟩
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | rfl
      · exact h j hj'
      · exact hn
    · rintro ⟨hr,h⟩
      exact ⟨⟨hr,fun j hj => h j (by omega)⟩,h n (by omega)⟩

lemma prefixMax_congr (z w : ℕ → ℝ) (n : ℕ) (h : ∀ j < n, z j = w j) :
    prefixMax z n = prefixMax w n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prefixMax, prefixMax, ih (fun j hj => h j (by omega)), h n (by omega)]

lemma runningHeight_nonneg {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) :
    0 ≤ runningHeight ℓ X n := prefixMax_nonneg _ _

lemma height_le_runningHeight {d : ℕ} (ℓ : Vector d) (X : Path d) {j n : ℕ} (hj : j ≤ n) :
    dot (realPosition (X j)) ℓ ≤ runningHeight ℓ X n := le_prefixMax (j := j) (n := n+1) (fun k => dot (realPosition (X k)) ℓ) (by omega)

lemma runningHeight_mono {d : ℕ} (ℓ : Vector d) (X : Path d) : Monotone (runningHeight ℓ X) :=
  fun _ _ h => prefixMax_mono _ (Nat.add_le_add_right h 1)

lemma runningHeight_le {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ j ≤ n, dot (realPosition (X j)) ℓ ≤ r) : runningHeight ℓ X n ≤ r :=
  (prefixMax_le_iff _ _ _).mpr ⟨hr,fun j hj => h j (Nat.le_of_lt_succ hj)⟩

lemma runningHeight_congr {d : ℕ} (ℓ : Vector d) {X Y : Path d} (n : ℕ)
    (h : ∀ j ≤ n, X j = Y j) : runningHeight ℓ X n = runningHeight ℓ Y n := by
  apply prefixMax_congr
  intro j hj
  rw [h j (Nat.le_of_lt_succ hj)]

lemma measurable_runningHeight {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    Measurable (fun X : Path d => runningHeight ℓ X n) := by
  have hh (k : ℕ) : Measurable (fun X : Path d => prefixMax
      (fun j => dot (realPosition (X j)) ℓ) k) := by
    induction k with
    | zero => exact measurable_const
    | succ k ih => exact ih.max (by unfold dot realPosition; fun_prop)
  exact hh (n+1)

lemma tiltedCoordinate_add {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a : ℝ) (x y : Lattice d) :
    tiltedCoordinate ℓ u b a (x+y) = tiltedCoordinate ℓ u b a x + tiltedCoordinate ℓ u b a y := by
  simp only [tiltedCoordinate, signedCoordinate_add, dot_realPosition_add]
  ring

lemma tiltedCoordinate_zero {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a : ℝ) :
    tiltedCoordinate ℓ u b a 0 = 0 := by simp [tiltedCoordinate, signedCoordinate, dot, realPosition]

lemma measurable_heightRatio {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a : ℝ) (n : ℕ) :
    Measurable (fun X : Path d => heightRatio ℓ u b a X n) := by
  unfold heightRatio
  apply Measurable.div
  · exact (measurable_of_countable (tiltedCoordinate ℓ u b a)).comp (measurable_pi_apply n)
  · exact measurable_const.mul (measurable_const.add (measurable_runningHeight ℓ n))

lemma measurableSet_admissiblePrefix {d : ℕ} (n : ℕ) : MeasurableSet (AdmissiblePrefix (d := d) n) := by
  simp only [AdmissiblePrefix, Set.ofPred_and, Set.ofPred_forall, Set.ofPred_exists]
  refine (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter ?_
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun e => by
    exact measurableSet_eq_fun (measurable_pi_apply (j+1)) ((show Measurable (fun X : Path d => X j) from measurable_pi_apply j).add_const (step e))

lemma measurableSet_boundedHeightPrefix {d : ℕ} (ℓ : Vector d) (H : ℝ) (n : ℕ) :
    MeasurableSet (BoundedHeightPrefix ℓ H n) := by
  simp only [BoundedHeightPrefix, Set.ofPred_forall, Set.ofPred_and]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  have hh : Measurable (fun X : Path d => dot (realPosition (X j)) ℓ) := by unfold dot realPosition; fun_prop
  exact (measurableSet_le measurable_const hh).inter (measurableSet_le hh measurable_const)

lemma measurableSet_ratioExceed {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) (n : ℕ) :
    MeasurableSet (RatioExceed ℓ u b a H t n) :=
  ((measurableSet_admissiblePrefix n).inter (measurableSet_boundedHeightPrefix ℓ H n)).inter
    (measurableSet_lt measurable_const (measurable_heightRatio ℓ u b a n))

lemma measurableSet_ratioHit {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) :
    MeasurableSet (RatioHit ℓ u b a H t) :=
  MeasurableSet.iUnion fun n => measurableSet_ratioExceed ℓ u b a H t n

lemma measurableSet_firstRatioExceed {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) (n : ℕ) :
    MeasurableSet (FirstRatioExceed ℓ u b a H t n) := by
  apply (measurableSet_ratioExceed ℓ u b a H t n).inter
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le (measurable_heightRatio ℓ u b a j) measurable_const

lemma admissiblePrefix_mono {d : ℕ} {m n : ℕ} (hmn : m ≤ n) :
    AdmissiblePrefix (d := d) n ⊆ AdmissiblePrefix m :=
  fun _ h => ⟨h.1,fun j hj => h.2 j (hj.trans_le hmn)⟩

lemma boundedHeightPrefix_mono {d : ℕ} (ℓ : Vector d) (H : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    BoundedHeightPrefix ℓ H n ⊆ BoundedHeightPrefix ℓ H m :=
  fun _ h j hj => h j (hj.trans hmn)

lemma ratioHit_eq_first {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) :
    RatioHit ℓ u b a H t = ⋃ n, FirstRatioExceed ℓ u b a H t n := by
  ext X
  constructor
  · intro hX
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    have hex : ∃ n, t < heightRatio ℓ u b a X n := ⟨n,hn.2⟩
    let k := Nat.find hex
    have hk : k ≤ n := Nat.find_min' hex hn.2
    refine Set.mem_iUnion.mpr ⟨k,⟨⟨admissiblePrefix_mono hk hn.1.1,
      boundedHeightPrefix_mono ℓ H hk hn.1.2⟩,Nat.find_spec hex⟩,?_⟩
    intro j hj
    exact le_of_not_gt (Nat.find_min hex hj)
  · intro hX
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    exact Set.mem_iUnion.mpr ⟨n,hn.1⟩

lemma firstRatioExceed_disjoint {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) :
    Pairwise (fun n m => Disjoint (FirstRatioExceed ℓ u b a H t n) (FirstRatioExceed ℓ u b a H t m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  rintro X ⟨hn,hprevn⟩ ⟨hm,hprevm⟩
  rcases lt_or_gt_of_ne hnm with h | h
  · exact (not_le_of_gt hn.2) (hprevm n h)
  · exact (not_le_of_gt hm.2) (hprevn m h)

lemma ratioHit_antitone {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H : ℝ) {s t : ℝ} (hst : s ≤ t) :
    RatioHit ℓ u b a H t ⊆ RatioHit ℓ u b a H s := by
  intro X hX
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
  exact Set.mem_iUnion.mpr ⟨n,hn.1,hst.trans_lt hn.2⟩

lemma firstRatioExceed_record {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ)
    (ha : 0 < a) (ht : 0 < t) (X : Path d) (n : ℕ)
    (hX : X ∈ FirstRatioExceed ℓ u b a H t n) :
    0 < n ∧ ∀ j < n, tiltedCoordinate ℓ u b a (X j) < tiltedCoordinate ℓ u b a (X n) := by
  have hd (j : ℕ) : 0 < a*(1+runningHeight ℓ X j) := mul_pos ha (by linarith [runningHeight_nonneg ℓ X j])
  have hn0 : 0 < n := by
    by_contra h
    have hn : n = 0 := by omega
    have hz : heightRatio ℓ u b a X n = 0 := by
      simp only [heightRatio, hn, hX.1.1.1.1, tiltedCoordinate_zero, zero_div]
    have hh : t < heightRatio ℓ u b a X n := hX.1.2
    rw [hz] at hh
    linarith
  refine ⟨hn0,fun j hj => ?_⟩
  have hlo := (div_le_iff₀ (hd j)).mp (hX.2 j hj)
  have hhi := (lt_div_iff₀ (hd n)).mp hX.1.2
  have hM := runningHeight_mono ℓ X hj.le
  have hm := mul_le_mul_of_nonneg_left hM (mul_nonneg ht.le ha.le)
  nlinarith

lemma prefixDetermined_admissiblePrefix {d : ℕ} (n : ℕ) :
    PrefixDetermined n (AdmissiblePrefix (d := d) n) := by
  intro X Y hXY
  simp only [AdmissiblePrefix, Set.mem_ofPred_eq]
  rw [hXY 0 (by omega)]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  rw [hXY j (by omega), hXY (j+1) (by omega)]

lemma prefixDetermined_boundedHeightPrefix {d : ℕ} (ℓ : Vector d) (H : ℝ) (n : ℕ) :
    PrefixDetermined n (BoundedHeightPrefix ℓ H n) := by
  intro X Y hXY
  simp only [BoundedHeightPrefix, Set.mem_ofPred_eq]
  exact forall_congr' fun j => forall_congr' fun hj => by rw [hXY j hj]

lemma heightRatio_congr {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a : ℝ) {X Y : Path d}
    (n : ℕ) (hXY : ∀ j ≤ n, X j = Y j) : heightRatio ℓ u b a X n = heightRatio ℓ u b a Y n := by
  rw [heightRatio, heightRatio, hXY n le_rfl, runningHeight_congr ℓ n hXY]

lemma prefixDetermined_firstRatioExceed {d : ℕ} (ℓ : Vector d) (u : Direction d)
    (b a H t : ℝ) (n : ℕ) : PrefixDetermined n (FirstRatioExceed ℓ u b a H t n) := by
  apply prefixDetermined_inter
  · apply prefixDetermined_inter
    · exact prefixDetermined_inter (prefixDetermined_admissiblePrefix n)
        (prefixDetermined_boundedHeightPrefix ℓ H n)
    · intro X Y hXY
      simp only [Set.mem_ofPred_eq, heightRatio_congr ℓ u b a n hXY]
  · intro X Y hXY
    simp only [Set.mem_ofPred_eq]
    exact forall_congr' fun j => forall_congr' fun hj => by
      rw [heightRatio_congr ℓ u b a j (fun k hk => hXY k (by omega))]

lemma firstRatioExceed_overshoot {d : ℕ} (ℓ : Vector d) (u : Direction d)
    (hℓ : ∀ i, |ℓ i| ≤ 1) (b a H t : ℝ) (hb : 0 ≤ b) (ha : 1 ≤ a) (ht : 0 < t)
    (X : Path d) (n : ℕ) (hX : X ∈ FirstRatioExceed ℓ u b a H t n) :
    heightRatio ℓ u b a X n ≤ t+b+1 := by
  have ha0 : 0 < a := by linarith
  have hn := (firstRatioExceed_record ℓ u b a H t ha0 ht X n hX).1
  obtain ⟨e,he⟩ := hX.1.1.1.2 (n-1) (by omega)
  have hn' : n-1+1 = n := by omega
  rw [hn'] at he
  have hs : signedCoordinate u (step e) ≤ 1 :=
    (le_abs_self _).trans ((signedCoordinate_abs_le_norm _ _).trans_eq (latticeVector_step_norm _))
  have hl : dot (realPosition (step e)) ℓ ≤ 1 := by
    rw [dot_step]
    split
    · exact (le_abs_self _).trans (hℓ _)
    · exact (neg_le_abs _).trans (hℓ _)
  have hstep : tiltedCoordinate ℓ u b a (step e) ≤ 1+b*a := by
    have hh := mul_le_mul_of_nonneg_left hl (mul_nonneg hb ha0.le)
    dsimp only [tiltedCoordinate]
    linarith
  have hd (j : ℕ) : 0 < a*(1+runningHeight ℓ X j) :=
    mul_pos ha0 (by linarith [runningHeight_nonneg ℓ X j])
  have hprev := (div_le_iff₀ (hd (n-1))).mp (hX.2 (n-1) (by omega))
  have hm := mul_le_mul_of_nonneg_left (runningHeight_mono ℓ X (Nat.sub_le n 1))
    (mul_nonneg ht.le ha0.le)
  have hend : tiltedCoordinate ℓ u b a (X n) ≤
      t*(a*(1+runningHeight ℓ X n)) + 1+b*a := by
    rw [he, tiltedCoordinate_add]
    nlinarith
  apply (div_le_iff₀ (hd n)).mpr
  have hm0 := runningHeight_nonneg ℓ X n
  have hba := mul_nonneg hb ha0.le
  have hprod := mul_nonneg (show 0 ≤ b*a+a by positivity) hm0
  nlinarith

lemma annealed_prefix_avoiding_suffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (f : Path d) (n : ℕ) (hn : 0 < n)
    (A : Set (Path d)) (hA : MeasurableSet A)
    (hfresh : ∀ j < n, f j ≠ f n)
    (havoid : ∀ X ∈ A, ∀ k, ∀ j < n, f n + X k ≠ f j) :
    annealedLaw ν ((fun X : Path d => fun k => X (n+k)-f n) ⁻¹' A ∩ pathCylinder f n) =
      annealedLaw ν (pathCylinder f n) * annealedLaw ν A := by
  by_cases hf : f 0 = 0
  · let S : Set (Lattice d) := {y | ∃ j < n, y = f j}
    let T : Set (Lattice d) := Sᶜ
    let B : Set (Path d) := (fun X : Path d => fun k => X k-f n) ⁻¹' A
    have hB : MeasurableSet B := hA.preimage (by fun_prop)
    have hBT : B ⊆ Stay T := by
      intro X hX k
      rintro ⟨j,hj,hjk⟩
      have hh := havoid (fun k => X k-f n) hX k j hj
      have he : f n + (X k-f n) = X k := by abel
      rw [he, hjk] at hh
      exact hh rfl
    have hnT : f n ∈ T := by
      rintro ⟨j,hj,hjn⟩
      exact hfresh j hj hjn.symm
    have hS0 : (0 : Lattice d) ∈ S := ⟨0,hn,hf.symm⟩
    have hm : @Measurable _ _ (rowSigma S) _
        (fun ω : Environment d => quenchedKernel (ω,0) (pathCylinder f n)) := by
      apply measurable_of_row_locality _
        ((Kernel.measurable_coe _ (measurableSet_pathCylinder f n)).comp
          (measurable_id.prodMk measurable_const)) S 0 hS0
      intro ω η hωη
      exact pathCylinder_weight_locality S ω η hωη 0 f n (fun j hj => ⟨j,hj,rfl⟩)
    rw [annealed_apply ν ((hA.preimage (by fun_prop)).inter (measurableSet_pathCylinder f n))]
    have hh (ω : Environment d) : quenchedKernel (ω,0)
        ((fun X : Path d => fun k => X (n+k)-f n) ⁻¹' A ∩ pathCylinder f n) =
        quenchedKernel (ω,0) (pathCylinder f n) * quenchedKernel (ω,f n) B :=
      quenched_prefix_future ω 0 f hf n hB
    simp_rw [hh]
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν disjoint_compl_right) hm
      (measurable_quenched_stay_event_rows T (f n) hnT B hB hBT),
      annealed_event_translation ν (f n) A hA,
      ← annealed_apply ν (measurableSet_pathCylinder f n)]
  · have hz : annealedLaw ν (pathCylinder f n) = 0 := by
      rw [annealed_apply ν (measurableSet_pathCylinder f n)]
      simp_rw [quenched_pathCylinder_zero _ _ _ hf n]
      simp
    rw [measure_mono_null Set.inter_subset_right hz, hz, zero_mul]

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

lemma measurableSet_regenerationSupport {d : ℕ} (ℓ : Vector d) :
    MeasurableSet (RegenerationSupport ℓ) := by
  have hm (n : ℕ) : MeasurableSet {X : Path d | ((renewSuffix ℓ)^[n] X) ∈
      FirstWordEvent ℓ (regenerationWords ℓ X n)} := by
    have he : {X : Path d | ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n)} =
        ⋃ w : List (Direction d), {X | regenerationWords ℓ X n = w} ∩
          ((renewSuffix ℓ)^[n]) ⁻¹' FirstWordEvent ℓ w := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨fun h => ⟨_,rfl,h⟩,fun ⟨w,hw,h⟩ => hw ▸ h⟩
    rw [he]
    exact MeasurableSet.iUnion fun w =>
      ((measurable_regenerationWord ℓ n) (measurableSet_singleton w)).inter
      ((measurableSet_firstWordEvent ℓ w).preimage ((measurable_renewSuffix ℓ).iterate n))
  unfold RegenerationSupport
  rw [Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
    (MeasurableSet.iInter hm)

lemma conditioned_regenerationSupport {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ RegenerationSupport ℓ := by
  filter_upwards [(conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν),
    conditioned_all_firstWords ν ℓ htrans] with X h0 hX
  exact ⟨h0,hX⟩

lemma regenerationSupport_noDrop {d : ℕ} (ℓ : Vector d) : RegenerationSupport ℓ ⊆ NoDrop ℓ 0 :=
  fun _ h => (h.2 0).1

lemma template_span_estimates {d : ℕ} (ℓ : Vector d) (c C C0 a : ℝ) (K : ℕ) (X : Path d)
    (hX : X ∈ RegenerationSupport ℓ) (ht : X ∈ WordTemplate ℓ c C C0 a K)
    {k j : ℕ} (hk : k < K) (hj : j ≤ (regenerationWords ℓ X k).length) :
    c*k-C0 ≤ dot (realPosition (X (regenerationTimes ℓ X k+j))) ℓ ∧
    dot (realPosition (X (regenerationTimes ℓ X k+j))) ℓ ≤ C*(k+1)+C0 ∧
    ‖latticeVector (X (regenerationTimes ℓ X k+j))‖ ≤ a*(k+1) := by
  obtain ⟨⟨hlo,hhi⟩,hR⟩ := regeneration_span_bounds ℓ X hX.1 hX.2 k j hj
  rw [regeneration_height_sum ℓ X hX.1 hX.2 k] at hlo
  rw [regeneration_height_sum ℓ X hX.1 hX.2 (k+1)] at hhi
  rw [← Finset.sum_range_succ] at hR
  refine ⟨(ht k hk.le).1.trans hlo,?_,?_⟩
  · exact hhi.trans (by simpa only [Nat.cast_add, Nat.cast_one] using (ht (k+1) hk).2.1)
  · exact hR.trans (by simpa only [Nat.cast_add, Nat.cast_one] using (ht (k+1) hk).2.2)

lemma tiltedCoordinate_nsmul {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a : ℝ)
    (x : Lattice d) (n : ℕ) :
    tiltedCoordinate ℓ u b a (n • x) = n * tiltedCoordinate ℓ u b a x := by
  rw [tiltedCoordinate, signedCoordinate_nsmul, dot_realPosition_nsmul, tiltedCoordinate]
  ring

lemma template_tilted_lower {d : ℕ} (ℓ : Vector d) (u e : Direction d)
    (c C C0 a b : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a) (K M : ℕ) (X : Path d)
    (hX : X ∈ RegenerationSupport ℓ) (ht : X ∈ WordTemplate ℓ c C C0 a K)
    {k j : ℕ} (hk : k < K) (hj : j ≤ (regenerationWords ℓ X k).length) :
    a*((b*c-1)*k + (b*((M : ℝ)*dot (realPosition (step e)) ℓ)-b*C0-1)) - M ≤
      tiltedCoordinate ℓ u b a (M • step e + X (regenerationTimes ℓ X k+j)) := by
  obtain ⟨hlo,_,hR⟩ := template_span_estimates ℓ c C C0 a K X hX ht hk hj
  have hcoord : -a*(k+1) ≤ signedCoordinate u (X (regenerationTimes ℓ X k+j)) :=
    by
      have habs := signedCoordinate_abs_le_norm u (X (regenerationTimes ℓ X k+j))
      have hneg := neg_abs_le (signedCoordinate u (X (regenerationTimes ℓ X k+j)))
      linarith
  have hscript : -(1 : ℝ) ≤ signedCoordinate u (step e) := by
    have hh := signedCoordinate_abs_le_norm u (step e)
    rw [latticeVector_step_norm] at hh
    exact (neg_le_neg hh).trans (neg_abs_le _)
  have hM := mul_le_mul_of_nonneg_left hscript (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hh := mul_le_mul_of_nonneg_left hlo (mul_nonneg hb ha)
  rw [tiltedCoordinate_add, tiltedCoordinate_nsmul]
  dsimp only [tiltedCoordinate]
  nlinarith

lemma wordPath_replicate_prefix {d : ℕ} (x : Lattice d) (e : Direction d) (M j : ℕ)
    (hj : j ≤ M) : wordPath x (List.replicate M e) j = x + j • step e := by
  induction M generalizing x j with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp
  | succ M ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.replicate_succ, wordPath]
      rw [ih (x+step e) j (by omega), succ_nsmul]
      abel

lemma measurableSet_forwardTemplate {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (c C C0 a : ℝ) (K M : ℕ) : MeasurableSet (ForwardTemplate ℓ e c C C0 a K M) :=
  (((measurableSet_regenerationSupport ℓ).inter
    (measurableSet_wordTemplate ℓ c C C0 a K)).preimage (by fun_prop)).inter
      (measurableSet_wordCylinder 0 (List.replicate M e))

lemma forwardTemplate_script {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (c C C0 a : ℝ) (K M : ℕ) {X : Path d}
    (hX : X ∈ ForwardTemplate ℓ e c C C0 a K M) {j : ℕ} (hj : j ≤ M) :
    X j = j • step e := by
  have hh := hX.2 j (by simpa only [List.length_replicate] using hj)
  rw [wordPath_replicate_prefix _ _ _ _ hj, zero_add] at hh
  exact hh

lemma forwardTemplate_noDrop {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (c C C0 a : ℝ) (K M : ℕ) (he : 0 ≤ dot (realPosition (step e)) ℓ) :
    ForwardTemplate ℓ e c C C0 a K M ⊆ NoDrop ℓ 0 := by
  intro X hX j
  have hz : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot, realPosition]
  rw [hz]
  by_cases hj : j ≤ M
  · rw [forwardTemplate_script ℓ e c C C0 a K M hX hj, dot_realPosition_nsmul]
    exact mul_nonneg (Nat.cast_nonneg _) he
  · have hs := regenerationSupport_noDrop ℓ hX.1.1 (j-M)
    change dot (realPosition 0) ℓ ≤ dot (realPosition (X (M+(j-M))-M • step e)) ℓ at hs
    rw [Nat.add_sub_of_le (by omega), dot_realPosition_sub, dot_realPosition_nsmul, hz] at hs
    exact (mul_nonneg (Nat.cast_nonneg M) he).trans (sub_nonneg.mp hs)

lemma forwardTemplate_control {d : ℕ} (ℓ : Vector d) (u e : Direction d)
    (c C C0 a b D H : ℝ) (K M : ℕ)
    (ha : 1 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ dot (realPosition (step e)) ℓ)
    (hbc : 1 ≤ b*c) (hM : 0 ≤ (M : ℝ)*dot (realPosition (step e)) ℓ-C0)
    (hconst : (M : ℝ) ≤ a*(b*((M : ℝ)*dot (realPosition (step e)) ℓ)-b*C0-1))
    (hstep : 0 ≤ tiltedCoordinate ℓ u b a (step e))
    (hD : (M : ℝ)+1 ≤ D) (hDc : 1 ≤ D*c)
    (hH : H < (M : ℝ)*dot (realPosition (step e)) ℓ+c*K-C0)
    {X : Path d} (hX : X ∈ ForwardTemplate ℓ e c C C0 a K M) (n : ℕ) :
    0 ≤ dot (realPosition (X n)) ℓ ∧
    ((0 ≤ tiltedCoordinate ℓ u b a (X n) ∧
      signedCoordinate u (X n) ≤ a*D*(1+dot (realPosition (X n)) ℓ)) ∨
      H < dot (realPosition (X n)) ℓ) := by
  have ha0 : 0 ≤ a := by linarith
  have hD0 : 0 ≤ D := by linarith [Nat.cast_nonneg M (α := ℝ)]
  have hnonneg : 0 ≤ dot (realPosition (X n)) ℓ := by
    simpa [dot, realPosition] using
      forwardTemplate_noDrop ℓ e c C C0 a K M he hX n
  refine ⟨hnonneg,?_⟩
  by_cases hn : n < M
  · left
    rw [forwardTemplate_script ℓ e c C C0 a K M hX hn.le, tiltedCoordinate_nsmul,
      signedCoordinate_nsmul]
    refine ⟨mul_nonneg (Nat.cast_nonneg n) hstep,?_⟩
    have hcoord : signedCoordinate u (step e) ≤ 1 := by
      have hh := signedCoordinate_abs_le_norm u (step e)
      rw [latticeVector_step_norm] at hh
      exact (le_abs_self _).trans hh
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast hn.le
    have hu := mul_le_mul_of_nonneg_left hcoord (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hbase : (M : ℝ) ≤ a*D := by nlinarith [Nat.cast_nonneg M (α := ℝ)]
    have hg := mul_nonneg (mul_nonneg ha0 hD0) hnonneg
    have hx := forwardTemplate_script ℓ e c C C0 a K M hX hn.le
    rw [hx] at hnonneg hg
    nlinarith
  · let Y : Path d := fun j => X (M+j)-M • step e
    have hY : Y ∈ RegenerationSupport ℓ := hX.1.1
    have ht : Y ∈ WordTemplate ℓ c C C0 a K := hX.1.2
    have hx (j : ℕ) : X (M+j) = M • step e + Y j := by dsimp only [Y]; abel
    have hnM : M ≤ n := by omega
    have hnm : M+(n-M) = n := Nat.add_sub_of_le hnM
    by_cases hcut : n-M < regenerationTimes ℓ Y K
    · obtain ⟨k,hk,hk'⟩ := increasing_cuts_cover (regenerationTimes ℓ Y)
        (regenerationTimes_strictMono ℓ Y hY.2) (regenerationTimes_zero ℓ Y) (n-M)
      have hkK : k < K := (regenerationTimes_strictMono ℓ Y hY.2).lt_iff_lt.mp (hk.trans_lt hcut)
      have hj : n-M-regenerationTimes ℓ Y k ≤ (regenerationWords ℓ Y k).length := by
        rw [regenerationTimes_succ] at hk'
        omega
      have heq : regenerationTimes ℓ Y k+(n-M-regenerationTimes ℓ Y k) = n-M :=
        Nat.add_sub_of_le hk
      have hlow := template_tilted_lower ℓ u e c C C0 a b hb ha0 K M Y hY ht hkK hj
      rw [heq] at hlow
      obtain ⟨hh,_,hr⟩ := template_span_estimates ℓ c C C0 a K Y hY ht hkK hj
      rw [heq] at hh hr
      left
      rw [← hnm, hx]
      refine ⟨?_,?_⟩
      · have hprod : 0 ≤ a*((b*c-1)*k) := mul_nonneg ha0 (mul_nonneg (by linarith) (Nat.cast_nonneg k))
        nlinarith
      · have hcoord : signedCoordinate u (M • step e + Y (n-M)) ≤ M+a*(k+1) := by
          rw [signedCoordinate_add, signedCoordinate_nsmul]
          have hu := (le_abs_self (signedCoordinate u (step e))).trans (signedCoordinate_abs_le_norm u (step e))
          rw [latticeVector_step_norm] at hu
          have hv := (le_abs_self (signedCoordinate u (Y (n-M)))).trans (signedCoordinate_abs_le_norm u (Y (n-M)))
          have hmul := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
          linarith
        have hheight : (M : ℝ)*dot (realPosition (step e)) ℓ+c*k-C0 ≤
            dot (realPosition (M • step e + Y (n-M))) ℓ := by
          rw [dot_realPosition_add, dot_realPosition_nsmul]
          linarith
        have hscaled := mul_le_mul_of_nonneg_left hheight (mul_nonneg ha0 hD0)
        have hDk := mul_le_mul_of_nonneg_right hDc (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
        have hDM := mul_nonneg hD0 hM
        have hbase : (M : ℝ) ≤ a*(D-1) := by nlinarith [Nat.cast_nonneg M (α := ℝ)]
        have hka := mul_le_mul_of_nonneg_left hDk ha0
        have hMa := mul_nonneg ha0 hDM
        nlinarith
    · right
      have hh := (regenerationTimes_true ℓ Y hY.1 hY.2 K).2 (n-M-regenerationTimes ℓ Y K)
      change dot (realPosition (Y (regenerationTimes ℓ Y K))) ℓ ≤
        dot (realPosition (Y (regenerationTimes ℓ Y K+(n-M-regenerationTimes ℓ Y K)))) ℓ at hh
      rw [Nat.add_sub_of_le (le_of_not_gt hcut)] at hh
      have hlo := (ht K le_rfl).1
      rw [← regeneration_height_sum ℓ Y hY.1 hY.2 K] at hlo
      rw [← hnm, hx, dot_realPosition_add, dot_realPosition_nsmul]
      linarith

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

lemma annealed_eq_noDrop_mul_conditioned {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    annealedLaw ν A = annealedLaw ν (NoDrop ℓ 0) * conditionedLaw ν ℓ A := by
  rw [conditionedLaw_apply_of_subset ν ℓ A hA hAD, ← mul_assoc,
    ENNReal.mul_inv_cancel hp (measure_ne_top _ _), one_mul]

lemma forwardTemplate_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (e : Direction d)
    (he : 0 < dot (realPosition (step e)) ℓ) (c C C0 a : ℝ) (K M : ℕ) :
    annealedLaw ν (ForwardTemplate ℓ e c C C0 a K M) =
      annealedLaw ν (wordCylinder 0 (List.replicate M e)) *
      annealedLaw ν (NoDrop ℓ 0) * conditionedLaw ν ℓ (WordTemplate ℓ c C C0 a K) := by
  let A := RegenerationSupport ℓ ∩ WordTemplate ℓ c C C0 a K
  have hA : MeasurableSet A := (measurableSet_regenerationSupport ℓ).inter
    (measurableSet_wordTemplate ℓ c C C0 a K)
  have hAD : A ⊆ NoDrop ℓ 0 := fun _ h => regenerationSupport_noDrop ℓ h.1
  have hrecord : ∀ y ∈ wordDepartures 0 (List.replicate M e),
      dot (realPosition y) ℓ < dot (realPosition (wordPath 0 (List.replicate M e) (List.replicate M e).length)) ℓ := by
    intro y hy
    obtain ⟨j,hj,rfl⟩ := (wordDepartures_mem_iff 0 y (List.replicate M e)).mp hy
    simp only [List.length_replicate] at hj ⊢
    rw [wordPath_replicate_prefix _ _ _ _ hj.le, wordPath_replicate,
      zero_add, zero_add, dot_realPosition_nsmul, dot_realPosition_nsmul]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hj) he
  have hf := annealed_record_suffix ν ℓ (List.replicate M e) hrecord A hA hAD
  simp only [List.length_replicate, wordPath_replicate, zero_add] at hf
  change annealedLaw ν (ForwardTemplate ℓ e c C C0 a K M) =
    annealedLaw ν (wordCylinder 0 (List.replicate M e)) * annealedLaw ν A at hf
  rw [hf, annealed_eq_noDrop_mul_conditioned ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)) A hA hAD, ← mul_assoc]
  congr 1
  apply measure_congr
  filter_upwards [conditioned_regenerationSupport ν ℓ htrans] with X hX
  apply propext
  change (X ∈ RegenerationSupport ℓ ∧ X ∈ WordTemplate ℓ c C C0 a K) ↔ X ∈ WordTemplate ℓ c C C0 a K
  simp only [hX,true_and]

lemma tilted_height_avoids_prefix {d : ℕ} (ℓ : Vector d) (u : Direction d)
    (b a H : ℝ) (f Z : Path d) (n : ℕ)
    (hrecord : ∀ j < n, tiltedCoordinate ℓ u b a (f j) < tiltedCoordinate ℓ u b a (f n))
    (hf : f ∈ BoundedHeightPrefix ℓ H n)
    (hZ : ∀ k, 0 ≤ tiltedCoordinate ℓ u b a (Z k) ∨ H < dot (realPosition (Z k)) ℓ) :
    ∀ k j, j < n → f n+Z k ≠ f j := by
  intro k j hj heq
  rcases hZ k with htilt | hheight
  · have h := hrecord j hj
    rw [← heq, tiltedCoordinate_add] at h
    linarith
  · have hlo := (hf n le_rfl).1
    have hhi := (hf j hj.le).2
    rw [← heq, dot_realPosition_add] at hhi
    linarith

lemma controlled_suffix_caps_ratio {d : ℕ} (ℓ : Vector d) (u : Direction d)
    (hℓ : ∀ i, |ℓ i| ≤ 1) (b a D H t : ℝ)
    (hb : 0 ≤ b) (ha : 1 ≤ a) (hD : 0 ≤ D) (ht : 0 < t)
    (f X : Path d) (n : ℕ) (hf : f ∈ FirstRatioExceed ℓ u b a H t n)
    (hX : X ∈ pathCylinder f n)
    (hcontrol : ∀ k, (signedCoordinate u (X (n+k)-f n) ≤
      a*D*(1+dot (realPosition (X (n+k)-f n)) ℓ)) ∨
      H < dot (realPosition (X (n+k)-f n)) ℓ) :
    X ∉ RatioHit ℓ u b a H (t+(2*b+1+D)) := by
  intro hhit
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hhit
  have ha0 : 0 < a := by linarith
  have hscale : 0 ≤ a*D := mul_nonneg ha0.le hD
  by_cases hkn : k < n
  · have he := heightRatio_congr ℓ u b a k (fun j hj => hX j (by omega))
    have hlo := hf.2 k hkn
    have hkbound : t+(2*b+1+D) < heightRatio ℓ u b a X k := hk.2
    rw [he] at hkbound
    linarith [show 0 ≤ 2*b+1+D by linarith]
  · have hnk : n ≤ k := by omega
    have hkm : n+(k-n) = k := Nat.add_sub_of_le hnk
    have hz := hcontrol (k-n)
    rw [hkm, dot_realPosition_sub] at hz
    have hlaunch := (hf.1.1.2 n le_rfl).1
    have htop := (hk.1.2 k le_rfl).2
    rcases hz with hcoord | hhigh
    · have hs : signedCoordinate u (X k) = signedCoordinate u (f n) +
          signedCoordinate u (X k-f n) := by
        rw [← signedCoordinate_add]
        congr 1
        abel
      have hratio := firstRatioExceed_overshoot ℓ u hℓ b a H t hb ha ht f n hf
      have denom (j : ℕ) : 0 < a*(1+runningHeight ℓ X j) :=
        mul_pos ha0 (by linarith [runningHeight_nonneg ℓ X j])
      have hne : runningHeight ℓ f n = runningHeight ℓ X n :=
        runningHeight_congr ℓ n (fun j hj => (hX j hj).symm)
      have hm := runningHeight_mono ℓ X hnk
      have hheight := height_le_runningHeight ℓ X (show k ≤ k from le_rfl)
      have hprev : signedCoordinate u (f n) ≤ (t+b+1)*(a*(1+runningHeight ℓ X n)) := by
        have hfden : 0 < a*(1+runningHeight ℓ f n) := by rw [hne]; exact denom n
        have hh := (div_le_iff₀ hfden).mp hratio
        dsimp only [heightRatio, tiltedCoordinate] at hh
        rw [hne] at hh
        have hpos := mul_nonneg (mul_nonneg hb ha0.le) hlaunch
        linarith
      have hlaunchscale := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ (t+b+1)*a by positivity)
      have hrelscale := mul_le_mul_of_nonneg_left (show 1+dot (realPosition (X k)) ℓ -
          dot (realPosition (f n)) ℓ ≤ 1+runningHeight ℓ X k by linarith) hscale
      have hheightscale := mul_le_mul_of_nonneg_left hheight (mul_nonneg hb ha0.le)
      have hbound : heightRatio ℓ u b a X k ≤ t+(2*b+1+D) := by
        apply (div_le_iff₀ (denom k)).mpr
        dsimp only [tiltedCoordinate]
        nlinarith
      exact (not_le_of_gt hk.2) hbound
    · linarith

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

lemma ratio_threshold_contraction {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (u : Direction d) (hℓ : ∀ i, |ℓ i| ≤ 1)
    (b a D H t : ℝ) (hb : 0 ≤ b) (ha : 1 ≤ a) (hD : 0 ≤ D) (ht : 0 < t)
    (A : Set (Path d)) (hA : MeasurableSet A)
    (hcontrol : ∀ Z ∈ A, ∀ k, (0 ≤ tiltedCoordinate ℓ u b a (Z k) ∧
      signedCoordinate u (Z k) ≤ a*D*(1+dot (realPosition (Z k)) ℓ)) ∨
      H < dot (realPosition (Z k)) ℓ) :
    (annealedLaw ν).real (RatioHit ℓ u b a H (t+(2*b+1+D))) ≤
      (1-(annealedLaw ν).real A)*(annealedLaw ν).real (RatioHit ℓ u b a H t) := by
  let μ := annealedLaw ν
  let B := RatioHit ℓ u b a H (t+(2*b+1+D))
  have hsub : B ⊆ ⋃ n, FirstRatioExceed ℓ u b a H t n := by
    rw [← ratioHit_eq_first]
    exact ratioHit_antitone ℓ u b a H (by linarith)
  have hg := stopping_prefix_favourable_gain μ (FirstRatioExceed ℓ u b a H t) B (μ A)
    (prefixDetermined_firstRatioExceed ℓ u b a H t)
    (measurableSet_firstRatioExceed ℓ u b a H t)
    (firstRatioExceed_disjoint ℓ u b a H t)
    (measurableSet_ratioHit ℓ u b a H _) hsub (by
      intro n f hf
      let F := (fun X : Path d => fun k => X (n+k)-f n) ⁻¹' A ∩ pathCylinder f n
      have hF : MeasurableSet F := (hA.preimage (by fun_prop)).inter (measurableSet_pathCylinder f n)
      obtain ⟨hn,hrecord⟩ := firstRatioExceed_record ℓ u b a H t (by linarith) ht f n hf
      refine ⟨F,hF,Set.inter_subset_right,?_,?_⟩
      · apply Set.disjoint_left.mpr
        intro X hB hF
        apply controlled_suffix_caps_ratio ℓ u hℓ b a D H t hb ha hD ht f X n hf hF.2
        · intro k
          rcases hcontrol _ hF.1 k with h | h
          · exact Or.inl h.2
          · exact Or.inr h
        · exact hB
      · exact annealed_prefix_avoiding_suffix ν f n hn A hA
          (fun j hj he => by have hh := hrecord j hj; rw [he] at hh; exact (lt_irrefl _) hh)
          (fun Z hZ => tilted_height_avoids_prefix ℓ u b a H f Z n hrecord hf.1.1.2
            (fun k => (hcontrol Z hZ k).imp And.left id)))
  rw [← ratioHit_eq_first] at hg
  have hpne : μ (RatioHit ℓ u b a H t)*μ A ≠ ∞ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) hg
  rw [ENNReal.toReal_add (measure_ne_top _ _) hpne,ENNReal.toReal_mul] at hr
  change (μ B).toReal ≤ (1-(μ A).toReal)*(μ (RatioHit ℓ u b a H t)).toReal
  nlinarith

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

lemma ratio_hit_geometric {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (u : Direction d) (hℓ : ∀ i, |ℓ i| ≤ 1)
    (b a D H ε : ℝ) (hb : 0 ≤ b) (ha : 1 ≤ a) (hD : 0 ≤ D)
    (_hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A : Set (Path d)) (hA : MeasurableSet A) (hp : ε ≤ (annealedLaw ν).real A)
    (hcontrol : ∀ Z ∈ A, ∀ k, (0 ≤ tiltedCoordinate ℓ u b a (Z k) ∧
      signedCoordinate u (Z k) ≤ a*D*(1+dot (realPosition (Z k)) ℓ)) ∨
      H < dot (realPosition (Z k)) ℓ) (j : ℕ) :
    (annealedLaw ν).real (RatioHit ℓ u b a H (1+j*(2*b+1+D))) ≤ (1-ε)^j := by
  induction j with
  | zero => simp [measureReal_le_one]
  | succ j ih =>
    have ht : 0 < 1+(j : ℝ)*(2*b+1+D) := by positivity
    have hc := ratio_threshold_contraction ν ℓ u hℓ b a D H _ hb ha hD ht A hA hcontrol
    have hcoef : 0 ≤ 1-(annealedLaw ν).real A := sub_nonneg.mpr measureReal_le_one
    have hmul := mul_le_mul_of_nonneg_left ih hcoef
    have hpow := mul_le_mul_of_nonneg_right (show 1-(annealedLaw ν).real A ≤ 1-ε by linarith)
      (pow_nonneg (by linarith : 0 ≤ 1-ε) j)
    have he : 1+(j+1 : ℕ)*(2*b+1+D) = (1+(j : ℝ)*(2*b+1+D))+(2*b+1+D) := by
      push_cast <;> ring
    rw [he,pow_succ]
    nlinarith

lemma forwardTemplate_probability_lower {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (e : Direction d)
    (he : 0 < dot (realPosition (step e)) ℓ) (c C C0 a : ℝ) (K M : ℕ)
    (κ : ℝ≥0) (hκ : ∀ᵐ ω ∂environmentLaw ν, ∀ x e, κ ≤ (ω x).1 e)
    (hg : (4/5 : ℝ) ≤ (conditionedLaw ν ℓ).real (WordTemplate ℓ c C C0 a K)) :
    (κ : ℝ)^M*(annealedLaw ν).real (NoDrop ℓ 0)*(4/5) ≤
      (annealedLaw ν).real (ForwardTemplate ℓ e c C C0 a K M) := by
  have heq := congrArg ENNReal.toReal (forwardTemplate_probability ν ℓ htrans e he c C C0 a K M)
  simp only [ENNReal.toReal_mul] at heq
  change _ ≤ (annealedLaw ν (ForwardTemplate ℓ e c C C0 a K M)).toReal
  rw [heq]
  have hlo := ENNReal.toReal_mono (measure_ne_top _ _)
    (annealed_wordCylinder_lower ν κ hκ (List.replicate M e))
  simp only [List.length_replicate, ENNReal.toReal_pow, ENNReal.coe_toReal] at hlo
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right hlo measureReal_nonneg) hg (by norm_num)
    (mul_nonneg measureReal_nonneg measureReal_nonneg)

lemma ratio_hit_union_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hℓ : ∀ i, |ℓ i| ≤ 1) (b a D H ε : ℝ)
    (hb : 0 ≤ b) (ha : 1 ≤ a) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A : Set (Path d)) (hA : MeasurableSet A) (hp : ε ≤ (annealedLaw ν).real A)
    (hcontrol : ∀ u Z, Z ∈ A → ∀ k, (0 ≤ tiltedCoordinate ℓ u b a (Z k) ∧
      signedCoordinate u (Z k) ≤ a*D*(1+dot (realPosition (Z k)) ℓ)) ∨
      H < dot (realPosition (Z k)) ℓ) (j : ℕ) :
    (annealedLaw ν).real (⋃ u : Direction d, RatioHit ℓ u b a H (1+j*(2*b+1+D))) ≤
      (2*d : ℕ)*(1-ε)^j := by
  classical
  have h := measureReal_iUnion_fintype_le (μ := annealedLaw ν)
    (fun u : Direction d => RatioHit ℓ u b a H (1+j*(2*b+1+D)))
  refine h.trans ?_
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun u _ =>
    ratio_hit_geometric ν ℓ u hℓ b a D H ε hb ha hD hε hε1 A hA hp (hcontrol u) j)
  simpa [Direction, Fintype.card_prod, mul_comm] using hs

lemma unit_direction_coordinate_bound {d : ℕ} (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1) :
    ∀ i, |ℓ i| ≤ 1 := by
  intro i
  have hh : ℓ i*ℓ i ≤ ∑ j : Fin d, ℓ j*ℓ j :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (ℓ j)) (Finset.mem_univ i)
  change ℓ i*ℓ i ≤ dot ℓ ℓ at hh
  rw [hℓ] at hh
  nlinarith [sq_abs (ℓ i),abs_nonneg (ℓ i)]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ConfinementTemplates
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

theorem strip_templates {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ b a D ε : ℝ, 0 ≤ b  ∧  1 ≤ a  ∧  0 ≤ D  ∧  0 < ε  ∧  ε ≤ 1  ∧
      ∀ H : ℝ, ∃ A : Set (Path d), MeasurableSet A  ∧  ε ≤ (annealedLaw ν).real A  ∧
        ∀ u Z, Z ∈ A  →  ∀ k,
          (0 ≤ tiltedCoordinate (realPosition (step e)) u b a (Z k)  ∧
            signedCoordinate u (Z k) ≤ a*D*(1+dot (realPosition (Z k)) (realPosition (step e)))) ∨
          H < dot (realPosition (Z k)) (realPosition (step e)) := by
  let ℓ := realPosition (step e)
  have hℓ := unit_direction_coordinate_bound ℓ (signed_direction_unit e)
  have he : dot (realPosition (step e)) ℓ=1 := signed_direction_unit e
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  have := conditionedLaw_probability ν ℓ hp.ne'
  obtain ⟨c,C,hc,hC,C0,hheight⟩ := conditioned_height_template ν ℓ hℓ htrans (1/20) (by norm_num)
  norm_num only at hheight
  let M := C0+2
  let b : ℝ := 1+1/c
  have hb : 1 ≤ b := by dsimp only [b] <;> linarith [one_div_pos.mpr hc]
  have hbc : 1 ≤ b*c := by dsimp only [b]; rw [add_mul,one_mul,one_div_mul_cancel hc.ne']; linarith
  have hMM : (M:ℝ)=(C0:ℝ)+2 := by simp [M]
  have hMpos : (2:ℝ) ≤ M := by rw [hMM]; linarith [Nat.cast_nonneg (α := ℝ) C0]
  let R : Path d  →  ℝ := fun X => wordRadius (firstWord ℓ X)
  have hR := conditioned_wordRadius_integrable ν hue ℓ (signed_direction_unit e) htrans
  let m := ∫ X, R X ∂conditionedLaw ν ℓ
  have hm : 0 ≤  m := integral_nonneg fun X => wordRadius_nonneg _
  let a := max (M:ℝ) (100*(m+1))
  have hMa : (M:ℝ) ≤ a := le_max_left _ _
  have hma : 100*(m+1) ≤ a := le_max_right _ _
  have ha : 1 ≤ a := by linarith
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hIa (K : ℕ) : truncatedMean (conditionedLaw ν ℓ) R (a*K) < 2*(1/100:ℝ)*a := by
    have hi : truncatedMean (conditionedLaw ν ℓ) R (a*K) ≤  m :=
      integral_mono (integrable_min_nonneg _ R
        (measurable_wordRadius.comp (measurable_firstWord ℓ)) (fun X => wordRadius_nonneg _) _ (by positivity))
        hR (fun _ => min_le_left _ _)
    linarith
  let D : ℝ := (M:ℝ)+1+1/c
  have hD : (M:ℝ)+1 ≤ D := by dsimp only [D] <;> linarith [one_div_pos.mpr hc]
  have hDc : 1 ≤ D*c := by
    dsimp only [D]
    rw [add_mul,one_div_mul_cancel hc.ne']
    have := mul_nonneg (show 0 ≤ (M:ℝ)+1 by positivity) hc.le
    linarith
  obtain ⟨κ,hκ,hrows⟩ := environment_uniform_elliptic ν hue
  let ε : ℝ := (κ:ℝ)^M*(annealedLaw ν).real (NoDrop ℓ 0)*(4/5)
  have hε : 0 < ε := by
    exact mul_pos (mul_pos (pow_pos (NNReal.coe_pos.mpr hκ) M)
      (ENNReal.toReal_pos hp.ne' (measure_ne_top _ _))) (by norm_num)
  have hA (H : ℝ) : ∃ A : Set (Path d), MeasurableSet A  ∧  ε ≤ (annealedLaw ν).real A  ∧
      ∀ u Z, Z ∈ A  →  ∀ k, (0 ≤ tiltedCoordinate ℓ u b a (Z k)  ∧
        signedCoordinate u (Z k) ≤ a*D*(1+dot (realPosition (Z k)) ℓ)) ∨ H < dot (realPosition (Z k)) ℓ := by
    obtain ⟨K,hK⟩ := exists_nat_gt ((H+(C0:ℝ))/c)
    have hK' := (div_lt_iff₀ hc).mp hK
    have hg : (4/5:ℝ) ≤ (conditionedLaw ν ℓ).real (WordTemplate ℓ c C C0 a K) := by
      have h := controlled_template_probability ν ℓ htrans c C C0 (1/100) a ha0 1 K (by norm_num)
        hheight (by norm_num) (hIa K)
      simpa only [one_mul] using h.le
    refine ⟨ForwardTemplate ℓ e c C C0 a K M,measurableSet_forwardTemplate ℓ e c C C0 a K M,
      forwardTemplate_probability_lower ν ℓ htrans e (by rw [he]; norm_num) c C C0 a K M κ hrows hg,?_⟩
    intro u Z hZ k
    apply (forwardTemplate_control ℓ u e c C C0 a b D H K M ha (by linarith) (by rw [he]; norm_num)
      hbc ?_ ?_ ?_ hD hDc ?_ hZ k).2
    · rw [he,mul_one,hMM]; linarith
    · rw [he,mul_one,hMM]
      have hba : a ≤ a*(2*b-1) := by nlinarith
      nlinarith
    · have hstep : -1 ≤ signedCoordinate u (step e) := by
        have h := signedCoordinate_abs_le_norm u (step e)
        rw [latticeVector_step_norm] at h
        exact (abs_le.mp h).1
      dsimp only [tiltedCoordinate]
      rw [he,mul_one]
      nlinarith
    · rw [he,mul_one]; linarith
  have hε1 : ε ≤ 1 := by
    obtain ⟨A,_,hA,_⟩ := hA 0
    exact hA.trans measureReal_le_one
  exact ⟨b,a,D,ε,by linarith,ha,by linarith,hε,hε1,hA⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SpatialConfinement
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma stripExcursion_subset_ratio {d : ℕ} (ℓ : Vector d) (X : Path d)
    (h0 : X 0 = 0) (hNN : ∀ n, ∃ e : Direction d, X (n+1) = X n+step e)
    (b a D : ℝ) (hb : 0 ≤ b) (ha : 1 ≤ a) (hD : 0 ≤ D) (N : ℕ) :
    X ∈ StripExcursion ℓ N (a*(2*b+2+D)*(N+1)^2) →
    X ∈ ⋃ u : Direction d, RatioHit ℓ u b a N (1+N*(2*b+1+D)) := by
  rintro ⟨n,hn,u,hu⟩
  refine Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨n,⟨⟨h0,fun j _ => hNN j⟩,hn⟩,?_⟩⟩
  have hm := runningHeight_le ℓ X n N (Nat.cast_nonneg _) (fun j hj => (hn j hj).2)
  have hm0 := runningHeight_nonneg ℓ X n
  have ht : 0 ≤ 1+(N:ℝ)*(2*b+1+D) := by positivity
  have hfactor : 1+(N:ℝ)*(2*b+1+D) ≤ (2*b+2+D)*(N+1) := by nlinarith
  have hbnd : (1+(N:ℝ)*(2*b+1+D))*(a*(1+runningHeight ℓ X n)) ≤
      a*(2*b+2+D)*(N+1)^2 := by
    calc
      _ ≤ (1+(N:ℝ)*(2*b+1+D))*(a*(1+N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) ht
      _ ≤ ((2*b+2+D)*(N+1))*(a*(1+N)) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = _ := by ring
  change _ < tiltedCoordinate ℓ u b a (X n)/(a*(1+runningHeight ℓ X n))
  apply (lt_div_iff₀ (mul_pos (by linarith) (by linarith))).mpr
  have hz := mul_nonneg (mul_nonneg hb (show 0 ≤ a by linarith)) (hn n le_rfl).1
  dsimp only [tiltedCoordinate]
  linarith

theorem spatial_confinement_oai {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ε ≤ 1 ∧ ∀ N : ℕ,
      (annealedLaw ν).real (StripExcursion (realPosition (step e)) N (C*(N+1)^2)) ≤
        (2*d : ℕ)*(1-ε)^N := by
  obtain ⟨b,a,D,ε,hb,ha,hD,hε,hε1,hA⟩ := strip_templates ν hue e htrans
  refine ⟨a*(2*b+2+D),ε,mul_pos (by linarith) (by linarith),hε,hε1,?_⟩
  intro N
  obtain ⟨A,hAm,hAp,hAc⟩ := hA N
  apply le_trans ?_ (ratio_hit_union_bound ν (realPosition (step e))
    (unit_direction_coordinate_bound _ (signed_direction_unit e)) b a D N ε hb ha hD hε.le hε1 A hAm hAp hAc N)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [annealed_initial ν,annealed_nearest_neighbor ν] with X h0 hNN
  exact stripExcursion_subset_ratio _ X h0 hNN b a D hb ha hD N

end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.spatial_confinement_oai := @OAI.DirectionalTransience.spatial_confinement_oai
