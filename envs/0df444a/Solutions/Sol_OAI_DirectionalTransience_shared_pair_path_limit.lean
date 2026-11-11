-- Prove2me | solution 1 for OAI.DirectionalTransience.shared_pair_path_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:04:51.097052+00:00
-- url     : https://prove2.me/submissions/54020b5e-460e-42e1-b29c-d2f3d45f9936

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal007
import Theorems.Thm_OAI_DirectionalTransience_normalJointPast_product_identification
import Theorems.Thm_OAI_DirectionalTransience_recordFluctuationScale_tendsto
import Theorems.Thm_OAI_DirectionalTransience_shared_finite_past_cross_bound
import Theorems.Thm_OAI_DirectionalTransience_shared_first_hit_occupation_vanishes
import Theorems.Thm_OAI_DirectionalTransience_shared_limit_finite_past_identity
import Theorems.Thm_OAI_DirectionalTransience_shared_path_marginal_limits

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WeakVaryingParameter
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.enat_borel
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

lemma weak_map_varying_parameter {E A B : Type*}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    [SecondCountableTopology E] [SecondCountableTopology A]
    (μ : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E) (hμ : Tendsto μ atTop (𝓝 ν))
    (a : ℕ → A) (a₀ : A) (ha : Tendsto a atTop (𝓝 a₀))
    (f : E × A → B) (hf : Continuous f) :
    Tendsto (fun i => (μ i).map (f := (fun point => f (point, a i))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
      atTop (𝓝 (ν.map (f := (fun point => f (point, a₀))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) := by
  have hh := (ProbabilityMeasure.continuous_map hf).tendsto (ν.prod (diracProba a₀)) |>.comp
    (ProbabilityMeasure.continuous_prod.tendsto (ν,diracProba a₀) |>.comp
      (hμ.prodMk_nhds (continuous_diracProba.tendsto a₀ |>.comp ha)))
  have hid (V : ProbabilityMeasure E) (u : A) :
      (V.prod (diracProba u)).map (f := f) hf.aemeasurable =
        V.map (f := (fun point => f (point, u))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) := by
    apply Subtype.ext
    change ((V : Measure E).prod (Measure.dirac u)).map f = _
    rw [Measure.prod_dirac,Measure.map_map hf.measurable (by fun_prop)]
    rfl
  change Tendsto (fun i => ((μ i).prod (diracProba (a i))).map (f := f) hf.aemeasurable)
    atTop (𝓝 ((ν.prod (diracProba a₀)).map (f := f) hf.aemeasurable)) at hh
  simpa only [hid] using hh

end DirectionalTransience

end

end

end OAI
end

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

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordIncrement
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

lemma realPartialSum_succ (X : ℕ → ℝ) (n : ℕ) :
    realPartialSum X (n+1) = realPartialSum X n+X n := by simp [realPartialSum,Finset.sum_range_succ]

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

lemma isOpen_continuousOscillation (ε δ : ℝ) : IsOpen (ContinuousOscillation ε δ) := by
  have he : ContinuousOscillation ε δ =
      ⋃ (s : unitInterval) (t : unitInterval) (_h : dist s t ≤ δ), {f : C(unitInterval,ℝ) | ε < |f s-f t|} := by
    ext f
    simp only [ContinuousOscillation,Set.mem_ofPred_eq,Set.mem_iUnion,exists_prop]
  rw [he]
  exact isOpen_iUnion (fun s => isOpen_iUnion (fun t => isOpen_iUnion (fun _ =>
    isOpen_lt continuous_const ((continuous_eval_const s).sub
      (continuous_eval_const t)).abs)))

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_PathCompact
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

lemma continuousOscillation_mono {ε δ δ' : ℝ} (hδ : δ ≤ δ') :
    ContinuousOscillation ε δ ⊆ ContinuousOscillation ε δ' := by
  rintro f ⟨s,t,hst,h⟩
  exact ⟨s,t,hst.trans hδ,h⟩

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

lemma orderedTimes_succ (I : Finset unitInterval) (i : Fin I.card) :
    orderedTimes I i.succ = I.orderEmbOfFin rfl i := by simp [orderedTimes]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWidthProcess
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
namespace DirectionalTransience

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

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridLinear
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
namespace DirectionalTransience

lemma weak_sequence_tight {E : Type*} [MetricSpace E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (hμ : Tendsto μ atTop (𝓝 ν)) :
    IsTightMeasureSet (Set.range (fun n => (μ n : Measure E))) := by
  have hc : IsCompact (closure (Set.range μ)) :=
    hμ.isCompact_insert_range.closure_of_subset (Set.subset_insert _ _)
  have h := isTightMeasureSet_of_isCompact_closure hc
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_CompactPathModulus
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.array_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
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
namespace DirectionalTransience

lemma compact_path_modulus (K : Set C(unitInterval,ℝ)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ Disjoint K (ContinuousOscillation ε δ) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun p : K × unitInterval => p.1.1 p.2) :=
    continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨δ,hδ,hm⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) ε hε
  refine ⟨δ/2,by positivity,Set.disjoint_left.mpr ?_⟩
  rintro f hf ⟨s,t,hst,hbig⟩
  have hd : dist ((⟨f,hf⟩ : K),s) ((⟨f,hf⟩ : K),t) < δ := by
    simpa only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using hst.trans_lt (half_lt_self hδ)
  have hh := hm hd
  exact (not_lt_of_ge hbig.le) (by simpa only [Real.dist_eq] using hh)

lemma tight_path_modulus (μ : ℕ → Measure C(unitInterval,ℝ))
    (ht : IsTightMeasureSet (Set.range μ)) {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) :
    ∃ δ, 0 < δ ∧ ∀ i, μ i (ContinuousOscillation ε δ) ≤ ENNReal.ofReal β := by
  obtain ⟨K,hK,hKm⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht (ENNReal.ofReal β) (ENNReal.ofReal_pos.mpr hβ)
  obtain ⟨δ,hδ,hd⟩ := compact_path_modulus K hK hε
  have hsub : ContinuousOscillation ε δ ⊆ Kᶜ := by
    intro f hf hfK
    exact Set.disjoint_left.mp hd hfK hf
  exact ⟨δ,hδ,fun i => (measure_mono hsub).trans (hKm _ (Set.mem_range_self i))⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_RecordLinearPath
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
namespace DirectionalTransience

lemma measurable_recordLinearPath {d : ℕ} (ℓ : Vector d) (f : Direction d) (θ r n T : ℝ) :
    Measurable (recordLinearPath ℓ f θ r n T) :=
  measurable_heightPolygon _ (fun h =>
    ((measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ h)).sub_const ((h:ℝ)*θ)) _ _ _

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FinitePastDecorrelation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma measurable_sharedLinearPairPath {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (x y : Lattice d) : Measurable (sharedLinearPairPath ℓ f θ r n T x y) := by
  exact ((measurable_recordLinearPath ℓ f θ r n T).comp (by fun_prop)).prodMk
    ((measurable_recordLinearPath ℓ f θ r n T).comp (by fun_prop))

lemma recordLinearPath_grid {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (h : 0 ≤ T*n) (x : Lattice d) (X : Path d)
    (j : ℕ) (t : unitInterval) (ht : T*n*(t:ℝ) = j) :
    recordLinearPath ℓ f θ r n T (fun k => X k-x) t = centeredFirstHit ℓ f θ r j x X :=
  heightPolygon_grid _ r n T h j t ht

lemma jointPastIncrementMap_grid {d q : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (h : 0 ≤ T*n) (x y : Lattice d) (P : Path d × Path d)
    (j : Fin q → ℕ) (H k : ℕ) (a : JointPastTimes q)
    (hj : ∀ z, T*n*(a.1 z:ℝ) = j z) (hH : T*n*(a.2.1:ℝ) = H)
    (hk : T*n*(a.2.2:ℝ) = H+k) (b : Bool) :
    jointPastIncrementMap b (sharedLinearPairPath ℓ f θ r n T x y P,a) =
      (centeredPastCoordinates ℓ f θ r j x y P,
        centeredHitIncrement ℓ f θ r H k (pairSide b (x,y)) (pairSide b P)) := by
  apply Prod.ext
  · funext z
    apply Prod.ext
    · exact recordLinearPath_grid ℓ f θ r n T h x P.1 (j z) (a.1 z) (hj z)
    · exact recordLinearPath_grid ℓ f θ r n T h y P.2 (j z) (a.1 z) (hj z)
  · cases b <;> simp only [jointPastIncrementMap,ContinuousMap.coe_mk,sharedLinearPairPath,
      Bool.false_eq_true,ite_false, if_false,ite_true, if_true,pairSide]
    · rw [recordLinearPath_grid ℓ f θ r n T h x P.1 (H+k) a.2.2 (by simpa using hk),
        recordLinearPath_grid ℓ f θ r n T h x P.1 H a.2.1 hH]
      simp only [centeredFirstHit,centeredHitIncrement,Nat.cast_add]
      ring
    · rw [recordLinearPath_grid ℓ f θ r n T h y P.2 (H+k) a.2.2 (by simpa using hk),
        recordLinearPath_grid ℓ f θ r n T h y P.2 H a.2.1 hH]
      simp only [centeredFirstHit,centeredHitIncrement,Nat.cast_add]
      ring

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_ContinuousCrossPast
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.array_secondCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma jointCrossPastTest_apply {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℝ)
    (G g : ℝ →ᵇ ℝ) (P : RealPathPair) (a : JointPastTimes q) :
    jointCrossPastTest F G g (P,a)=F (fun z => (P.1 (a.1 z),P.2 (a.1 z)))*
      (g (P.1 a.2.1-P.2 a.2.1)*(G (P.1 a.2.2-P.1 a.2.1)*G (P.2 a.2.2-P.2 a.2.1))) := by
  simp only [jointCrossPastTest,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
    jointPastProductTest,BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.const_apply,
    jointPastIncrementMap,jointPastGapMap,ContinuousMap.coe_mk,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,sub_zero]
  ring

lemma weak_joint_cross_past_integral {q : ℕ} (μ : ℕ → ProbabilityMeasure RealPathPair)
    (V : ProbabilityMeasure RealPathPair) (hμ : Tendsto μ atTop (𝓝 V))
    (a : ℕ → JointPastTimes q) (a₀ : JointPastTimes q) (ha : Tendsto a atTop (𝓝 a₀))
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G g : ℝ →ᵇ ℝ) :
    Tendsto (fun i => ∫ P, jointCrossPastTest F G g (P,a i) ∂(μ i : Measure RealPathPair))
      atTop (𝓝 (∫ P, jointCrossPastTest F G g (P,a₀) ∂(V : Measure RealPathPair))) := by
  have hm := weak_map_varying_parameter μ V hμ a a₀ ha (fun z : RealPathPair × JointPastTimes q => z) continuous_id
  have hh := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hm) (jointCrossPastTest F G g)
  have he (U : ProbabilityMeasure RealPathPair) (u : JointPastTimes q) :
      (∫ z, jointCrossPastTest F G g z ∂(U.map (f := (fun path => (path,u))) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure _)) =
      ∫ P, jointCrossPastTest F G g (P,u) ∂(U : Measure RealPathPair) := by
    change (∫ z, jointCrossPastTest F G g z ∂(U : Measure RealPathPair).map (fun P => (P,u))) = _
    exact integral_map ((continuous_id.prodMk continuous_const).measurable.aemeasurable)
      (jointCrossPastTest F G g).continuous.aestronglyMeasurable
  simpa only [he] using hh

lemma jointPastGapMap_grid {d q : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (h : 0≤T*n) (x : Lattice d) (P : Path d × Path d)
    (H : ℕ) (a : JointPastTimes q) (hH : T*n*(a.2.1:ℝ)=H) :
    jointPastGapMap (sharedLinearPairPath ℓ f θ r n T x x P,a)=
      physicalFirstHitGap ℓ f x x H P/r := by
  change recordLinearPath ℓ f θ r n T (fun j => P.1 j-x) a.2.1-
    recordLinearPath ℓ f θ r n T (fun j => P.2 j-x) a.2.1 = _
  rw [recordLinearPath_grid ℓ f θ r n T h x P.1 H _ hH,
    recordLinearPath_grid ℓ f θ r n T h x P.2 H _ hH]
  have hz : signedCoordinate f (0 : Lattice d)=0 := by simp [signedCoordinate]
  simp only [physicalFirstHitGap,firstHitPairGap,sub_self,centeredFirstHit,hz,zero_add]
  simp only [sub_eq_add_neg,add_comm]
  ring

lemma jointCrossPastTest_grid {d q : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (h : 0≤T*n) (x : Lattice d) (P : Path d × Path d)
    (j : Fin q → ℕ) (H k : ℕ) (a : JointPastTimes q)
    (hj : ∀ z, T*n*(a.1 z:ℝ)=j z) (hH : T*n*(a.2.1:ℝ)=H)
    (hk : T*n*(a.2.2:ℝ)=H+k) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G g : ℝ →ᵇ ℝ) :
    jointCrossPastTest F G g (sharedLinearPairPath ℓ f θ r n T x x P,a)=
      F (centeredPastCoordinates ℓ f θ r j x x P)*
        (g (physicalFirstHitGap ℓ f x x H P/r)*
        (G (centeredHitIncrement ℓ f θ r H k x P.1)*G (centeredHitIncrement ℓ f θ r H k x P.2))) := by
  simp only [jointCrossPastTest,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk]
  rw [jointPastIncrementMap_grid ℓ f θ r n T h x x P j H k a hj hH hk false,
    jointPastIncrementMap_grid ℓ f θ r n T h x x P j H k a hj hH hk true,
    jointPastGapMap_grid ℓ f θ r n T h x P H a hH]
  simp only [jointPastProductTest,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
    BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.const_apply,ContinuousMap.coe_mk,
    sub_zero,pairSide,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  ring

end DirectionalTransience

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

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma symmetricClip_eq_self (w : ℝ≥0) {z : ℝ} (hz : |z|≤w) : symmetricClip w z=z := by
  obtain ⟨hl,hr⟩ := abs_le.mp hz
  simp only [symmetricClip_apply,min_eq_right hr,max_eq_right hl]

lemma symmetricClip_nat_eventually (z : ℝ) : ∀ᶠ n : ℕ in atTop, symmetricClip n z=z := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop |z|] with n hn
  exact symmetricClip_eq_self n hn

lemma clippedBCF_apply (F : ℝ →ᵇ ℝ) (w : ℝ≥0) (z : ℝ) : clippedBCF F w z=F (symmetricClip w z) := rfl

lemma clippedBCF_uniformContinuous (F : ℝ →ᵇ ℝ) (w : ℝ≥0) : UniformContinuous (clippedBCF F w) := by
  have hF := isCompact_Icc.uniformContinuousOn_of_continuous (F.continuous.continuousOn (s := Set.Icc (-(w:ℝ)) w))
  have h := hF.comp (symmetricClip_uniformContinuous w).uniformContinuousOn (s := Set.univ) (by
    intro z hz
    exact abs_le.mp (symmetricClip_bound w z))
  exact uniformContinuousOn_univ.mp h

lemma clippedBCF_norm_bound (F : ℝ →ᵇ ℝ) (w : ℝ≥0) (z : ℝ) : ‖clippedBCF F w z‖≤‖F‖ :=
  F.norm_coe_le_norm _

lemma clippedBCF_nat_tendsto (F : ℝ →ᵇ ℝ) (z : ℝ) :
    Tendsto (fun n : ℕ => clippedBCF F n z) atTop (𝓝 (F z)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [symmetricClip_nat_eventually z] with n hn
  simp only [clippedBCF_apply,hn]

lemma integral_clippedBCF_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (F : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, clippedBCF F n (X ω) ∂μ) atTop (𝓝 (∫ ω, F (X ω) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (clippedBCF F n).continuous.measurable.comp hX |>.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all μ (fun ω => clippedBCF_norm_bound F n (X ω))
  · exact ae_of_all μ (fun ω => clippedBCF_nat_tendsto F (X ω))

lemma integral_weighted_clippedBCF_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X A : Ω → ℝ) (hX : Measurable X) (hA : Measurable A)
    (C : ℝ) (hC : 0≤C) (hAb : ∀ ω, ‖A ω‖≤C) (F : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, A ω*clippedBCF F n (X ω) ∂μ) atTop
      (𝓝 (∫ ω, A ω*F (X ω) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => C*‖F‖)
  · intro n
    exact (hA.mul ((clippedBCF F n).continuous.measurable.comp hX)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    apply ae_of_all
    intro ω
    rw [norm_mul]
    exact mul_le_mul (hAb ω) (clippedBCF_norm_bound F n (X ω)) (norm_nonneg _) hC
  · exact ae_of_all μ (fun ω => tendsto_const_nhds.mul (clippedBCF_nat_tendsto F (X ω)))

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

open MeasureTheory Filter
namespace DirectionalTransience

lemma integrable_bounded_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G)
    (C D : ℝ) (hC : 0≤C) (hFb : ∀ ω, ‖F ω‖≤C) (hGb : ∀ ω, ‖G ω‖≤D) :
    Integrable (fun ω => F ω*G ω) μ :=
  Integrable.of_bound (hF.mul hG).aestronglyMeasurable (C*D) (ae_of_all _ fun ω => by
    rw [norm_mul]; exact mul_le_mul (hFb ω) (hGb ω) (norm_nonneg _) hC)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FinitePastCrossBound
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

theorem shared_limit_finite_past_cross_bound {d q : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (hn : ∀ i, 0 < fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i))
    (T : ℝ) (hT : 0<T) (x : ℕ → Lattice d)
    (H : ℕ → ℕ) (hH : ∀ i, 0<H i) (j : ℕ → Fin q → ℕ) (hj : ∀ i z, j i z≤H i)
    (u : ℕ → JointPastTimes q) (u₀ : JointPastTimes q) (hu : Tendsto u atTop (𝓝 u₀))
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V)) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ)
    (g : ℝ →ᵇ ℝ) (hg : UniformContinuous g) (hgb : ∀ z, |g z|≤1)
    {a t : ℝ} (ha : 0<a) (ht : 0<t) (hgzero : ∀ z, |z|≤a → g z=0) (w : ℝ≥0) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i z, T*n i*(u i |>.1 z : ℝ)=j i z) →
    (∀ i, T*n i*(u i |>.2.1 : ℝ)=H i) →
    (∀ i, T*n i*(u i |>.2.2 : ℝ)=H i+⌊t*n i⌋₊) →
    (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
    |∫ P, jointCrossPastTest F (symmetricClip w) g (P,u₀) ∂(V : Measure RealPathPair)| ≤
      ‖F‖*(16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t))) := by
  dsimp only
  intro huj huH huk hμ
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  have hc := (weak_joint_cross_past_integral μ V hweak u u₀ hu F (symmetricClip w) g).abs
  apply le_of_forall_pos_le_add
  intro ε hε
  apply le_of_tendsto hc
  have hh := shared_finite_past_cross_bound ν hue e f hef htrans r hrpos hr x x (fun _ => rfl)
    H hH j hj F g hg hgb ha ht hgzero w hε
  filter_upwards [hh] with i hi
  have he : (∫ P, jointCrossPastTest F (symmetricClip w) g (P,u i) ∂(μ i : Measure RealPathPair)) =
      ∫ P, F (centeredPastCoordinates ℓ f (θ i) (r i) (j i) (x i) (x i) P)*
        (g (physicalFirstHitGap ℓ f (x i) (x i) (H i) P/r i)*
        (symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) ⌊t*n i⌋₊ (x i) P.1)*
         symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) ⌊t*n i⌋₊ (x i) P.2)))
        ∂sharedConditionedPairLaw ν ℓ (x i) (x i) := by
    rw [hμ i]
    have htest : Continuous (fun P : RealPathPair => jointCrossPastTest F (symmetricClip w) g (P,u i)) :=
      (jointCrossPastTest F (symmetricClip w) g).continuous.comp (continuous_id.prodMk continuous_const)
    rw [integral_map (measurable_sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i)).aemeasurable
      htest.aestronglyMeasurable]
    apply integral_congr_ae
    apply ae_of_all
    intro P
    exact jointCrossPastTest_grid ℓ f (θ i) (r i) (n i) T (mul_nonneg hT.le (hn i).le)
      (x i) P (j i) (H i) ⌊t*n i⌋₊ (u i) (huj i) (huH i) (huk i) F (symmetricClip w) g
  rw [he]
  exact hi

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridOccupation
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
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

lemma layerGridPoint_floor_dist {a : ℝ} (ha : 0 < a) (t : unitInterval) :
    dist t (layerGridPoint a ⌊a*(t:ℝ)⌋₊) ≤ 1/a := by
  have h0 : 0 ≤ a*(t:ℝ) := mul_nonneg ha.le t.2.1
  have hlo := Nat.floor_le h0
  have hhi := Nat.lt_floor_add_one (a*(t:ℝ))
  have hja : (⌊a*(t:ℝ)⌋₊:ℝ) ≤ a := hlo.trans (mul_le_of_le_one_right ha.le t.2.2)
  rw [Subtype.dist_eq,Real.dist_eq,layerGridPoint_coe ha hja,
    abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ ha).mpr (by nlinarith))) ]
  apply (le_div_iff₀ ha).mpr
  have he : ((t:ℝ)-(⌊a*(t:ℝ)⌋₊:ℝ)/a)*a = (t:ℝ)*a-(⌊a*(t:ℝ)⌋₊:ℝ) := by field_simp
  rw [he]
  linarith

lemma volume_layer_cell_le {a : ℝ} (ha : 0 < a) (j : ℕ) :
    volume {t : unitInterval | ⌊a*(t:ℝ)⌋₊ = j} ≤ ENNReal.ofReal (1/a) := by
  rw [unitInterval.volume_apply]
  calc
    volume (Subtype.val '' {t : unitInterval | ⌊a*(t:ℝ)⌋₊ = j}) ≤
        volume (Set.Icc ((j:ℝ)/a) (((j:ℝ)+1)/a)) := by
      apply measure_mono
      rintro _ ⟨t,ht,rfl⟩
      have hlo := Nat.floor_le (mul_nonneg ha.le t.2.1)
      have hhi := Nat.lt_floor_add_one (a*(t:ℝ))
      rw [ht] at hlo hhi
      exact ⟨(div_le_iff₀ ha).mpr (by nlinarith),
        (le_div_iff₀ ha).mpr (by nlinarith)⟩
    _ = ENNReal.ofReal (1/a) := by rw [Real.volume_Icc]; congr 1; ring

lemma continuous_layerGap : Continuous (fun z : RealPathPair × unitInterval => layerGap z.1 z.2) :=
  (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)).sub
    (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd))

lemma gap_grid_close {a ε δ : ℝ} (ha : 0 < a) (hδ : 1/a ≤ δ)
    (P : RealPathPair) (t : unitInterval)
    (h1 : P.1 ∉ ContinuousOscillation ε δ) (h2 : P.2 ∉ ContinuousOscillation ε δ) :
    |layerGap P t-layerGap P (layerGridPoint a ⌊a*(t:ℝ)⌋₊)| ≤ 2*ε := by
  have hd := (layerGridPoint_floor_dist ha t).trans hδ
  have hm1 : |P.1 t-P.1 (layerGridPoint a ⌊a*(t:ℝ)⌋₊)| ≤ ε :=
    le_of_not_gt (fun h => h1 ⟨t,_,hd,h⟩)
  have hm2 : |P.2 t-P.2 (layerGridPoint a ⌊a*(t:ℝ)⌋₊)| ≤ ε :=
    le_of_not_gt (fun h => h2 ⟨t,_,hd,h⟩)
  calc
    |layerGap P t-layerGap P (layerGridPoint a ⌊a*(t:ℝ)⌋₊)| =
        |(P.2 t-P.2 (layerGridPoint a ⌊a*(t:ℝ)⌋₊))-
          (P.1 t-P.1 (layerGridPoint a ⌊a*(t:ℝ)⌋₊))| := by congr 1; dsimp [layerGap]; ring
    _ ≤ |P.2 t-P.2 (layerGridPoint a ⌊a*(t:ℝ)⌋₊)|+
          |P.1 t-P.1 (layerGridPoint a ⌊a*(t:ℝ)⌋₊)| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le
        (P.2 t-P.2 (layerGridPoint a ⌊a*(t:ℝ)⌋₊)) 0
        (P.1 t-P.1 (layerGridPoint a ⌊a*(t:ℝ)⌋₊))
    _ ≤ 2*ε := by linarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma IsGaussianSequence.comp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {S : Ω → ℝ} {r : ℕ → ℝ} (hr : IsGaussianSequence μ S r)
    {v : ℕ → ℕ} (hv : Tendsto v atTop atTop) : IsGaussianSequence μ S (r ∘ v) :=
  ⟨hr.1.comp hv,fun a ha => (hr.2 a ha).comp hv⟩

lemma layerGridPoint_tendsto (a : ℕ → ℝ) (j : ℕ → ℕ) (v : unitInterval)
    (h : Tendsto (fun i => (j i:ℝ)/a i) atTop (𝓝 (v:ℝ))) :
    Tendsto (fun i => layerGridPoint (a i) (j i)) atTop (𝓝 v) := by
  have hh := (continuous_projIcc (a := (0:ℝ)) (b := 1) (h := by norm_num)).continuousAt.tendsto.comp h
  simpa only [layerGridPoint,Function.comp_def,Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1) v.2,Subtype.eta] using hh

lemma interiorPastGrid_tendsto {q : ℕ} (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (v : Fin q → unitInterval) (s t : unitInterval) (hst : s ≤ t) :
    Tendsto (fun i => interiorPastGrid (a i) v s t) atTop (𝓝 (v,s,t)) := by
  have hH : Tendsto (fun i => ((⌊(s:ℝ)*a i⌋₊+1:ℕ):ℝ)/a i) atTop (𝓝 (s:ℝ)) := by
    have hh := ((tendsto_nat_floor_mul_div_atTop s.2.1).comp ha).add
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).div_atTop ha)
    simpa [Nat.cast_add,add_div] using hh
  apply Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.mpr
    intro z
    exact layerGridPoint_tendsto a _ (v z) ((tendsto_nat_floor_mul_div_atTop (v z).2.1).comp ha)
  · apply Tendsto.prodMk_nhds
    · exact layerGridPoint_tendsto a _ s hH
    · apply layerGridPoint_tendsto a _ t
      have hh := hH.add ((tendsto_nat_floor_mul_div_atTop (sub_nonneg.mpr (show (s:ℝ)≤t from hst))).comp ha)
      simpa [Nat.cast_add,add_div] using hh

lemma interiorPastGrid_eventually {q : ℕ} (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s ≤ t) (ht : (t:ℝ)<1) :
    ∀ᶠ i in atTop, 0<a i ∧
      (∀ z, ⌊(v z:ℝ)*a i⌋₊≤⌊(s:ℝ)*a i⌋₊+1) ∧
      (((⌊(s:ℝ)*a i⌋₊+1)+⌊((t:ℝ)-s)*a i⌋₊:ℕ):ℝ)≤a i ∧
      (∀ z, a i*(interiorPastGrid (a i) v s t |>.1 z:ℝ)=⌊(v z:ℝ)*a i⌋₊) ∧
      a i*(interiorPastGrid (a i) v s t |>.2.1:ℝ)=(⌊(s:ℝ)*a i⌋₊+1:ℕ) ∧
      a i*(interiorPastGrid (a i) v s t |>.2.2:ℝ)=
        ((⌊(s:ℝ)*a i⌋₊+1:ℕ):ℝ)+⌊((t:ℝ)-s)*a i⌋₊ := by
  filter_upwards [ha.eventually_gt_atTop 0,ha.eventually_ge_atTop (1/(1-(t:ℝ)))] with i hi hi'
  have he : 1≤(1-(t:ℝ))*a i := (div_le_iff₀ (sub_pos.mpr ht)).mp hi' |>.trans_eq (mul_comm _ _)
  have hf := Nat.floor_le (mul_nonneg s.2.1 hi.le)
  have hg := Nat.floor_le (mul_nonneg (sub_nonneg.mpr (show (s:ℝ)≤t from hst)) hi.le)
  have htot : (((⌊(s:ℝ)*a i⌋₊+1)+⌊((t:ℝ)-s)*a i⌋₊:ℕ):ℝ)≤a i := by
    push_cast
    nlinarith
  have hH : ((⌊(s:ℝ)*a i⌋₊+1:ℕ):ℝ)≤a i := by
    have := Nat.cast_nonneg (α := ℝ) ⌊((t:ℝ)-s)*a i⌋₊
    push_cast at htot ⊢
    linarith
  have hj (z : Fin q) : (⌊(v z:ℝ)*a i⌋₊:ℝ)≤a i :=
    (Nat.floor_le (mul_nonneg (v z).2.1 hi.le)).trans
      (mul_le_of_le_one_left hi.le (v z).2.2)
  have hid (j : ℕ) (hh : (j:ℝ)≤a i) : a i*(layerGridPoint (a i) j:ℝ)=j := by
    rw [layerGridPoint_coe hi hh,mul_div_cancel₀ _ hi.ne']
  have hvs (z : Fin q) : (v z : ℝ) ≤ (s : ℝ) := hv z
  refine ⟨hi,fun z => (Nat.floor_mono (mul_le_mul_of_nonneg_right (hvs z) hi.le)).trans (Nat.le_succ _),htot,?_,hid _ hH,?_⟩
  · exact fun z => hid _ (hj z)
  · simpa only [Nat.cast_add,interiorPastGrid] using hid _ htot

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_SharedInteriorCross
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

lemma shared_limit_interior_cross_bound {d q : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (T : ℝ) (hT : 0 < T) (x : ℕ → Lattice d)
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V))
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (g : ℝ →ᵇ ℝ) (hg : UniformContinuous g)
    (hgb : ∀ z, |g z| ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) (hgzero : ∀ z, |z| ≤ ρ → g z=0) (w : ℝ≥0) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
    |∫ P, jointCrossPastTest F (symmetricClip w) g (P,(v,s,t)) ∂(V : Measure RealPathPair)| ≤
      ‖F‖*(16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*ρ^2/(9*(T*((t:ℝ)-s))))) := by
  dsimp only
  intro hμ
  let ℓ := realPosition (step e)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let a := fun i => T*n i
  let H := fun i => ⌊(s:ℝ)*a i⌋₊+1
  let k := fun i => ⌊T*((t:ℝ)-s)*n i⌋₊
  let j := fun i z => ⌊(v z:ℝ)*a i⌋₊
  have hn : Tendsto n atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  have ha : Tendsto a atTop atTop := hn.const_mul_atTop hT
  have he := interiorPastGrid_eventually a ha v s t hv hst.le ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp (he.and (hr.1.eventually_gt_atTop 0))
  let u := fun i => i+N
  have hu : Tendsto u atTop atTop := tendsto_add_atTop_nat N
  have hgood (i : ℕ) := (hN (u i) (Nat.le_add_left N i)).1
  have hrpos (i : ℕ) := (hN (u i) (Nat.le_add_left N i)).2
  have hnpos (i : ℕ) : 0 < n (u i) := (mul_pos_iff_of_pos_left hT).mp (hgood i).1
  apply shared_limit_finite_past_cross_bound ν hue e f hef htrans (r ∘ u) hrpos (hr.comp hu) hnpos T hT
    (x ∘ u) (H ∘ u) (fun _ => Nat.succ_pos _) (j ∘ u) (fun i z => (hgood i).2.1 z)
    (fun i => interiorPastGrid (a (u i)) v s t) (v,s,t)
    ((interiorPastGrid_tendsto a ha v s t hst.le).comp hu)
    (μ ∘ u) V (hweak.comp hu) F g hg hgb hρ
    (mul_pos hT (sub_pos.mpr (show (s:ℝ) < t from hst))) hgzero w
  · exact fun i z => (hgood i).2.2.2.1 z
  · exact fun i => (hgood i).2.2.2.2.1
  · intro i
    change a (u i)*(interiorPastGrid (a (u i)) v s t |>.2.2:ℝ) = (H (u i):ℝ)+(k (u i):ℝ)
    have heq : ((t:ℝ)-s)*a (u i)=T*((t:ℝ)-s)*n (u i) := by dsimp [a] <;> ring
    simpa only [H,k,heq] using (hgood i).2.2.2.2.2
  · exact fun i => hμ (u i)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ConditionalLawTests
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

lemma product_law_of_uc_decorrelation {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (γ : Measure ℝ) [IsProbabilityMeasure γ]
    (Z : Ω → E) (X : Ω → ℝ) (hZ : Measurable Z) (hX : Measurable X)
    (h : ∀ (F : E →ᵇ ℝ) (G : ℝ →ᵇ ℝ), UniformContinuous G →
      (∫ ω, F (Z ω)*(G (X ω)-(∫ z, G z ∂γ)) ∂μ)=0) :
    μ.map (fun ω => (Z ω,X ω))=(μ.map Z).prod γ := by
  apply Measure.eq_prod_of_integral_mul_boundedContinuousFunction
  intro F G
  rw [integral_map (hZ.prodMk hX).aemeasurable (by fun_prop : Measurable (fun z : E × ℝ => F z.1*G z.2)).aestronglyMeasurable,
    integral_map hZ.aemeasurable F.continuous.aestronglyMeasurable]
  have hiF : Integrable (fun ω => F (Z ω)) μ :=
    Integrable.of_bound (F.continuous.measurable.comp hZ).aestronglyMeasurable ‖F‖
      (ae_of_all _ (fun ω => F.norm_coe_le_norm _))
  have hi (G' : ℝ →ᵇ ℝ) : Integrable (fun ω => F (Z ω)*G' (X ω)) μ := by
    apply integrable_bounded_mul μ _ _ (F.continuous.measurable.comp hZ)
      (G'.continuous.measurable.comp hX) ‖F‖ ‖G'‖ (norm_nonneg _) ?_ ?_
    · exact fun ω => F.norm_coe_le_norm _
    · exact fun ω => G'.norm_coe_le_norm _
  have he (n : ℕ) : (∫ ω, F (Z ω)*clippedBCF G n (X ω) ∂μ)=
      (∫ ω, F (Z ω) ∂μ)*(∫ z, clippedBCF G n z ∂γ) := by
    have hh := h F (clippedBCF G n) (clippedBCF_uniformContinuous G n)
    simp_rw [mul_sub] at hh
    rw [integral_sub (hi _) (hiF.mul_const _),integral_mul_const] at hh
    exact sub_eq_zero.mp hh
  have hl := integral_weighted_clippedBCF_tendsto μ X (fun ω => F (Z ω)) hX
    (F.continuous.measurable.comp hZ) ‖F‖ (norm_nonneg _) (fun ω => F.norm_coe_le_norm _) G
  have hr := (integral_clippedBCF_tendsto γ id measurable_id G).const_mul (∫ ω, F (Z ω) ∂μ)
  exact tendsto_nhds_unique hl (hr.congr (fun n => (he n).symm))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma shared_limit_interior_past_identity {d q : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (T : ℝ) (hT : 0 < T) (x : ℕ → Lattice d)
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V))
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G : ℝ →ᵇ ℝ) (hG : UniformContinuous G) (b : Bool) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
    (∫ P, jointPastProductTest F G (∫ z, G z ∂gaussianReal 0
        (Real.toNNReal (T*((t:ℝ)-s)/(2*commonMeanWidth ν ℓ))))
      (jointPastIncrementMap b (P,(v,s,t))) ∂(V : Measure RealPathPair))=0 := by
  dsimp only
  intro hμ
  let ℓ := realPosition (step e)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let a := fun i => T*n i
  let H := fun i => ⌊(s:ℝ)*a i⌋₊+1
  let k := fun i => ⌊T*((t:ℝ)-s)*n i⌋₊
  let j := fun i z => ⌊(v z:ℝ)*a i⌋₊
  have hn : Tendsto n atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  have ha : Tendsto a atTop atTop := hn.const_mul_atTop hT
  have he := interiorPastGrid_eventually a ha v s t hv hst.le ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let u := fun i => i+N
  have hu : Tendsto u atTop atTop := tendsto_add_atTop_nat N
  have hgood (i : ℕ) := hN (u i) (Nat.le_add_left N i)
  have hnpos (i : ℕ) : 0 < n (u i) := (mul_pos_iff_of_pos_left hT).mp (hgood i).1
  have hk (i : ℕ) : (k (u i):ℝ) ≤ T*n (u i) := by
    have hh := (hgood i).2.2.1
    have hn0 : (0:ℝ) ≤ (H (u i):ℝ) := Nat.cast_nonneg _
    have heq : ((t:ℝ)-s)*a (u i)=T*((t:ℝ)-s)*n (u i) := by dsimp [a] <;> ring
    rw [heq] at hh
    change ((H (u i)+k (u i):ℕ):ℝ) ≤ a (u i) at hh
    push_cast at hh
    exact le_trans (by linarith) hh
  have hkconv : Tendsto (fun i => (k (u i):ℝ)/n (u i)) atTop (𝓝 (T*((t:ℝ)-s))) :=
    ((tendsto_nat_floor_mul_div_atTop (mul_nonneg hT.le (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le)))).comp hn).comp hu
  apply shared_limit_finite_past_identity ν hue e f hef htrans (r ∘ u) (hr.comp hu) hnpos T hT
    (k ∘ u) hk (T*((t:ℝ)-s)) hkconv (x ∘ u) (x ∘ u) (fun _ => rfl)
    (H ∘ u) (fun _ => Nat.succ_pos _) (j ∘ u) (fun i z => (hgood i).2.1 z)
    (fun i => interiorPastGrid (a (u i)) v s t) (v,s,t)
    ((interiorPastGrid_tendsto a ha v s t hst.le).comp hu)
    (μ ∘ u) V (hweak.comp hu) F G hG b
  · exact fun i z => (hgood i).2.2.2.1 z
  · exact fun i => (hgood i).2.2.2.2.1
  · intro i
    change a (u i)*(interiorPastGrid (a (u i)) v s t |>.2.2:ℝ) = (H (u i):ℝ)+(k (u i):ℝ)
    have heq : ((t:ℝ)-s)*a (u i)=T*((t:ℝ)-s)*n (u i) := by dsimp [a] <;> ring
    simpa only [H,k,heq] using (hgood i).2.2.2.2.2
  · exact fun i => hμ (u i)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_JointPastMoments
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.array_secondCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
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

lemma normal_past_of_uc_tests (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0)
    (h : ∀ (q : ℕ) (v : Fin q → unitInterval) (s t : unitInterval),
      (∀ z, v z ≤ s) → s < t → (t:ℝ) < 1 → ∀ (b : Bool)
      (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G : ℝ →ᵇ ℝ), UniformContinuous G →
      (∫ P, jointPastProductTest F G (∫ z, G z ∂gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s)))
        (jointPastIncrementMap b (P,(v,s,t))) ∂μ)=0) : NormalJointPast μ c := by
  intro q v s t hv hst ht b
  apply product_law_of_uc_decorrelation μ _ (pairPastCoordinates v) (pairPathIncrement b s t)
    (pairPastCoordinates v).continuous.measurable (pairPathIncrement b s t).continuous.measurable
  intro F G hG
  exact h q v s t hv hst ht b F G hG

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairWeakUniqueness
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

lemma weak_limit_of_tight_identification {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → ProbabilityMeasure E) (W : ProbabilityMeasure E)
    (ht : IsTightMeasureSet (Set.range (fun i => (μ i : Measure E))))
    (hid : ∀ (j : ℕ → ℕ), Tendsto j atTop atTop → ∀ V : ProbabilityMeasure E,
      Tendsto (μ ∘ j) atTop (𝓝 V) → V=W) : Tendsto μ atTop (𝓝 W) := by
  have hc : IsCompact (closure (Set.range μ)) := isCompact_closure_of_isTightMeasureSet (by
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp)
  apply Filter.tendsto_of_subseq_tendsto
  intro j hj
  obtain ⟨V,hV,k,hk,hlim⟩ := hc.tendsto_subseq (fun n => subset_closure (Set.mem_range_self (j n)))
  have he := hid (j ∘ k) (hj.comp hk.tendsto_atTop) V hlim
  exact ⟨k,he ▸ hlim⟩

lemma pair_weak_tight {E F : Type*}
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
    (μ : ℕ → ProbabilityMeasure (E × F)) (W : ProbabilityMeasure E) (V : ProbabilityMeasure F)
    (hf : Tendsto (fun i => (μ i).map (f := Prod.fst) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 W))
    (hg : Tendsto (fun i => (μ i).map (f := Prod.snd) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 V)) :
    IsTightMeasureSet (Set.range (fun i => (μ i : Measure (E × F)))) := by
  apply IsTightMeasureSet.prodMk
  · convert weak_sequence_tight hf using 1
    all_goals try with_reducible_and_instances rfl
    ext M
    simp only [Set.mem_image,Set.mem_range,exists_exists_eq_and,Measure.fst]
    rfl
  · convert weak_sequence_tight hg using 1
    all_goals try with_reducible_and_instances rfl
    ext M
    simp only [Set.mem_image,Set.mem_range,exists_exists_eq_and,Measure.snd]
    rfl

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SharedLimitNormalPast
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.array_secondCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma shared_limit_normalJointPast {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (T : ℝ) (hT : 0 < T) (x : ℕ → Lattice d)
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V)) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
    NormalJointPast (V : Measure RealPathPair) (Real.toNNReal (T/(2*commonMeanWidth ν ℓ))) := by
  dsimp only
  intro hμ
  apply normal_past_of_uc_tests
  intro q v s t hv hst ht b F G hG
  have hh := shared_limit_interior_past_identity ν hue e f hef htrans r hr T hT x μ V hweak
    v s t hv hst ht F G hG b hμ
  have hc := commonMeanWidth_ge_one ν (realPosition (step e)) htrans
    (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)
  have he : Real.toNNReal (T*((t:ℝ)-s)/(2*commonMeanWidth ν (realPosition (step e)))) =
      Real.toNNReal (T/(2*commonMeanWidth ν (realPosition (step e)))) * Real.toNNReal ((t:ℝ)-s) := by
    rw [← Real.toNNReal_mul (by positivity : 0 ≤ T/(2*commonMeanWidth ν (realPosition (step e))))]
    congr 1
    ring
  simpa only [he] using hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma gap_open_measure_le_grid (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    {a ρ δ : ℝ} (ha : 0 < a) (hδ : 1/a ≤ δ) :
    (μ.prod volume) {z : RealPathPair × unitInterval | |layerGap z.1 z.2| < ρ/2} ≤
      ENNReal.ofReal (gridOccupationMass μ a ρ) +
        μ {P | P.1 ∈ ContinuousOscillation (ρ/4) δ ∨ P.2 ∈ ContinuousOscillation (ρ/4) δ} := by
  let E := fun j => {P : RealPathPair | |layerGap P (layerGridPoint a j)| ≤ ρ}
  let C := fun j => {t : unitInterval | ⌊a*(t:ℝ)⌋₊ = j}
  let B := {P : RealPathPair | P.1 ∈ ContinuousOscillation (ρ/4) δ ∨ P.2 ∈ ContinuousOscillation (ρ/4) δ}
  have hsub : {z : RealPathPair × unitInterval | |layerGap z.1 z.2| < ρ/2} ⊆
      (⋃ j ∈ Finset.range (⌊a⌋₊+1), E j ×ˢ C j) ∪ (B ×ˢ Set.univ) := by
    rintro ⟨P,t⟩ ht
    change |layerGap P t| < ρ/2 at ht
    by_cases hB : P ∈ B
    · exact Or.inr ⟨hB,Set.mem_univ _⟩
    · have h1 : P.1 ∉ ContinuousOscillation (ρ/4) δ := fun h => hB (Or.inl h)
      have h2 : P.2 ∉ ContinuousOscillation (ρ/4) δ := fun h => hB (Or.inr h)
      have hc := gap_grid_close ha hδ P t h1 h2
      have hj : ⌊a*(t:ℝ)⌋₊ ∈ Finset.range (⌊a⌋₊+1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (mul_le_of_le_one_right ha.le t.2.2)))
      apply Or.inl
      apply Set.mem_iUnion.mpr
      refine ⟨⌊a*(t:ℝ)⌋₊,Set.mem_iUnion.mpr ⟨hj,?_,rfl⟩⟩
      have hab := abs_sub_le (layerGap P (layerGridPoint a ⌊a*(t:ℝ)⌋₊)) (layerGap P t) 0
      rw [sub_zero,sub_zero,abs_sub_comm] at hab
      change |layerGap P (layerGridPoint a ⌊a*(t:ℝ)⌋₊)| ≤ ρ
      linarith only [hab,hc,ht]
  have hsum : (∑ j ∈ Finset.range (⌊a⌋₊+1), μ (E j))*ENNReal.ofReal (1/a) =
      ENNReal.ofReal (gridOccupationMass μ a ρ) := by
    rw [show gridOccupationMass μ a ρ =
      (∑ j ∈ Finset.range (⌊a⌋₊+1), μ.real (E j))*(1/a) by dsimp [gridOccupationMass,E]; ring]
    rw [ENNReal.ofReal_mul (Finset.sum_nonneg (fun j hj => measureReal_nonneg)),
      ENNReal.ofReal_sum_of_nonneg (fun j hj => measureReal_nonneg)]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
  calc
    _ ≤ (μ.prod volume) ((⋃ j ∈ Finset.range (⌊a⌋₊+1), E j ×ˢ C j) ∪ (B ×ˢ Set.univ)) := measure_mono hsub
    _ ≤ (μ.prod volume) (⋃ j ∈ Finset.range (⌊a⌋₊+1), E j ×ˢ C j) + (μ.prod volume) (B ×ˢ Set.univ) :=
      measure_union_le _ _
    _ ≤ (∑ j ∈ Finset.range (⌊a⌋₊+1), μ (E j)*ENNReal.ofReal (1/a))+μ B := by
      apply add_le_add
      · apply (measure_biUnion_finset_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [Measure.prod_prod]
        exact mul_le_mul le_rfl (volume_layer_cell_le ha j) (by positivity) (by positivity)
      · simp only [Measure.prod_prod,measure_univ,mul_one,le_refl]
    _ = _ := by rw [← Finset.sum_mul,hsum]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem joint_limit_diagonal_time_zero (μ : ℕ → ProbabilityMeasure RealPathPair)
    (V : ProbabilityMeasure RealPathPair) (hweak : Tendsto μ atTop (𝓝 V))
    (ht : IsTightMeasureSet (Set.range (fun i => (μ i : Measure RealPathPair))))
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (hocc : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ i in atTop, gridOccupationMass (μ i) (a i) ρ ≤ ε) :
    ((V : Measure RealPathPair).prod volume) {z : RealPathPair × unitInterval | layerGap z.1 z.2 = 0} = 0 := by
  have ht1 : IsTightMeasureSet (Set.range (fun i => (μ i : Measure RealPathPair).map Prod.fst)) := by
    convert ht.map (f := Prod.fst) continuous_fst using 1
    all_goals try with_reducible_and_instances rfl
    ext η
    simp
  have ht2 : IsTightMeasureSet (Set.range (fun i => (μ i : Measure RealPathPair).map Prod.snd)) := by
    convert ht.map (f := Prod.snd) continuous_snd using 1
    all_goals try with_reducible_and_instances rfl
    ext η
    simp
  let U : ProbabilityMeasure unitInterval := ⟨volume,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hprod : Tendsto (fun i => (μ i).prod U) atTop (𝓝 (V.prod U)) :=
    ProbabilityMeasure.continuous_prod.tendsto (V,U) |>.comp (hweak.prodMk_nhds tendsto_const_nhds)
  apply le_antisymm _ (by positivity)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  simp only [zero_add]
  have he : 0 < (ε:ℝ)/3 := by exact div_pos hε (by norm_num)
  obtain ⟨ρ,hρ,hocc⟩ := hocc ((ε:ℝ)/3) he
  obtain ⟨δ1,hd1,hm1⟩ := tight_path_modulus _ ht1 (by positivity : 0 < ρ/4) he
  obtain ⟨δ2,hd2,hm2⟩ := tight_path_modulus _ ht2 (by positivity : 0 < ρ/4) he
  let δ := min δ1 δ2
  have hd : 0 < δ := lt_min hd1 hd2
  have hb (i : ℕ) : (μ i : Measure RealPathPair)
      {P | P.1 ∈ ContinuousOscillation (ρ/4) δ ∨ P.2 ∈ ContinuousOscillation (ρ/4) δ} ≤
        ENNReal.ofReal ((ε:ℝ)/3)+ENNReal.ofReal ((ε:ℝ)/3) := by
    apply (measure_union_le _ _).trans
    apply add_le_add
    · have hs : {P : RealPathPair | P.1 ∈ ContinuousOscillation (ρ/4) δ} ⊆
          Prod.fst ⁻¹' ContinuousOscillation (ρ/4) δ1 := fun P h =>
        continuousOscillation_mono (min_le_left _ _) h
      apply (measure_mono hs).trans
      rw [← Measure.map_apply measurable_fst (isOpen_continuousOscillation _ _).measurableSet]
      exact hm1 i
    · have hs : {P : RealPathPair | P.2 ∈ ContinuousOscillation (ρ/4) δ} ⊆
          Prod.snd ⁻¹' ContinuousOscillation (ρ/4) δ2 := fun P h =>
        continuousOscillation_mono (min_le_right _ _) h
      apply (measure_mono hs).trans
      rw [← Measure.map_apply measurable_snd (isOpen_continuousOscillation _ _).measurableSet]
      exact hm2 i
  have hinv : Tendsto (fun i => 1/a i) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop ha
  have hevent : ∀ᶠ i in atTop,
      ((↑((μ i).prod U)) : Measure (RealPathPair × unitInterval))
        {z | |layerGap z.1 z.2| < ρ/2} ≤ (ε:ℝ≥0∞) := by
    filter_upwards [hocc,ha.eventually_gt_atTop 0,hinv.eventually_lt_const hd] with i hi hai hdi
    have hg := gap_open_measure_le_grid (ρ := ρ) (μ i) hai hdi.le
    have hc := hg.trans (add_le_add (ENNReal.ofReal_le_ofReal hi) (hb i))
    have heq : ENNReal.ofReal ((ε:ℝ)/3)+(ENNReal.ofReal ((ε:ℝ)/3)+ENNReal.ofReal ((ε:ℝ)/3)) = ε := by
      rw [← ENNReal.ofReal_add he.le,← ENNReal.ofReal_add he.le]
      have heq : (ε:ℝ)/3+((ε:ℝ)/3+(ε:ℝ)/3) = ε := by ring
      rw [heq,ENNReal.ofReal_coe_nnreal]
      all_goals positivity
    exact hc.trans_eq heq
  have hopen : IsOpen {z : RealPathPair × unitInterval | |layerGap z.1 z.2| < ρ/2} :=
    isOpen_lt continuous_layerGap.abs continuous_const
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hprod hopen
  have hlim : liminf (fun i => ((↑((μ i).prod U)) : Measure (RealPathPair × unitInterval))
      {z | |layerGap z.1 z.2| < ρ/2}) atTop ≤ (ε:ℝ≥0∞) :=
    (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)).trans (limsup_le_of_le (by isBoundedDefault) hevent)
  apply (measure_mono (show {z : RealPathPair × unitInterval | layerGap z.1 z.2 = 0} ⊆
    {z | |layerGap z.1 z.2| < ρ/2} from ?_)).trans (hport.trans hlim)
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  rw [hz,abs_zero]
  positivity

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_JointPathIndependence
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
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

lemma wiener_path_initial_zero (W : ProbabilityMeasure C(unitInterval,ℝ)) (T : ℝ)
    (hW : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw T I) :
    ∀ᵐ P ∂(W : Measure C(unitInterval,ℝ)),P 0=0 := by
  have he := wiener_path_eval W T hW 0
  have he0 : ((0:unitInterval):ℝ)=0 := rfl
  simp only [he0,mul_zero,Real.toNNReal_zero,gaussianReal_zero_var] at he
  have hh : ∀ᵐ x ∂(W : Measure C(unitInterval,ℝ)).map (fun P => P 0),x=0 := by
    rw [he]
    simp
  exact (ae_map_iff (continuous_eval_const 0).measurable.aemeasurable (by measurability)).mp hh

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SharedLimitOccupation
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.array_secondCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma shared_gap_at_grid {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (h : 0 < T*n) (x : Lattice d) (P : Path d × Path d)
    (j : ℕ) (hj : (j:ℝ) ≤ T*n) :
    layerGap (sharedLinearPairPath ℓ f θ r n T x x P) (layerGridPoint (T*n) j) =
      -(physicalFirstHitGap ℓ f x x j P)/r := by
  have ht : T*n*(layerGridPoint (T*n) j : ℝ) = j := by
    rw [layerGridPoint_coe h hj]
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ h.ne'
  dsimp only [layerGap,sharedLinearPairPath]
  rw [recordLinearPath_grid ℓ f θ r n T h.le x P.1 j _ ht,
    recordLinearPath_grid ℓ f θ r n T h.le x P.2 j _ ht]
  have hz : signedCoordinate f (0 : Lattice d) = 0 := by simp [signedCoordinate]
  simp only [centeredFirstHit,physicalFirstHitGap,firstHitPairGap,sub_self,hz,zero_add]
  simp only [sub_eq_add_neg,add_comm]
  ring

lemma shared_gridOccupation_eq {d : ℕ} (ν : Measure (Row d)) (e f : Direction d)
    (θ r n T ρ : ℝ) (hr : 0 < r) (h : 0 < T*n) (x : Lattice d) :
    gridOccupationMass ((sharedConditionedPairLaw ν (realPosition (step e)) x x).map
      (sharedLinearPairPath (realPosition (step e)) f θ r n T x x)) (T*n) ρ =
      firstHitOccupationMean ν e f x x (ρ*r) (⌊T*n⌋₊+1)/(T*n) := by
  unfold gridOccupationMass firstHitOccupationMean
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : (j:ℝ) ≤ T*n := (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).trans (Nat.floor_le h.le)
  have hs : MeasurableSet {P : RealPathPair | |layerGap P (layerGridPoint (T*n) j)| ≤ ρ} :=
    (isClosed_le (show Continuous (fun P : RealPathPair => |layerGap P (layerGridPoint (T*n) j)|) from
      (continuous_layerGap.comp (continuous_id.prodMk continuous_const)).abs) continuous_const).measurableSet
  rw [Measure.real,Measure.map_apply (measurable_sharedLinearPairPath _ _ _ _ _ _ _ _) hs]
  congr 2
  ext P
  change |layerGap (sharedLinearPairPath _ _ _ _ _ _ _ _ P) (layerGridPoint (T*n) j)| ≤ ρ ↔ _
  rw [shared_gap_at_grid _ _ _ _ _ _ h _ _ j hjn,abs_div,abs_neg,abs_of_pos hr]
  exact div_le_iff₀ hr

theorem shared_limit_diagonal_time_zero {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x : ℕ → Lattice d) {T : ℝ} (hT : 0 < T)
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V)) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i, (μ i : Measure RealPathPair) = (sharedConditionedPairLaw ν ℓ (x i) (x i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
    ((V : Measure RealPathPair).prod volume) {z : RealPathPair × unitInterval | layerGap z.1 z.2 = 0} = 0 := by
  dsimp only
  intro hμ
  let ℓ := realPosition (step e)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  have hn : Tendsto n atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  apply joint_limit_diagonal_time_zero μ V hweak (weak_sequence_tight hweak) (fun i => T*n i) (hn.const_mul_atTop hT)
  intro ε hε
  obtain ⟨ρ,hρ,ho⟩ := shared_first_hit_occupation_vanishes ν hue e f hef htrans r hr x hT (mul_pos hε hT)
  refine ⟨ρ,hρ,?_⟩
  filter_upwards [ho,hr.1.eventually_gt_atTop 0,hn.eventually_gt_atTop 0] with i hi hri hni
  rw [hμ i,shared_gridOccupation_eq ν e f _ _ _ _ ρ hri (mul_pos hT hni)]
  calc
    _ = (firstHitOccupationMean ν e f (x i) (x i) (ρ*r i) (⌊T*n i⌋₊+1)/n i)/T := by
      rw [div_div,mul_comm T]
    _ ≤ ε := (div_le_iff₀ hT).mpr hi

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma shared_limit_product {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (T : ℝ) (hT : 0 < T) (x : ℕ → Lattice d)
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V))
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hW : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g)=
        gaussianPathFiniteLaw (T/(2*commonMeanWidth ν (realPosition (step e)))) I)
    (hf : (V : Measure RealPathPair).map Prod.fst=W)
    (hg : (V : Measure RealPathPair).map Prod.snd=W) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
    (V : Measure RealPathPair)=(W : Measure C(unitInterval,ℝ)).prod W := by
  dsimp only
  intro hμ
  let ℓ := realPosition (step e)
  let c := Real.toNNReal (T/(2*commonMeanWidth ν ℓ))
  have hc := commonMeanWidth_ge_one ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)
  have h := shared_limit_normalJointPast ν hue e f hef htrans r hr T hT x μ V hweak hμ
  have hz := shared_limit_diagonal_time_zero ν hue e f hef htrans r hr x hT μ V hweak hμ
  have hcross : SeparatedCrossBound (V : Measure RealPathPair)
      (commonMeanWidth ν ℓ/(9*T)) (16*‖symmetricClip 1‖^2) := by
    intro q v s t hv hst ht F g hg hgb ρ hρ hgzero
    have hh := shared_limit_interior_cross_bound ν hue e f hef htrans r hr T hT x μ V hweak
      v s t hv hst ht F g hg hgb hρ hgzero 1 hμ
    have hexp : -(commonMeanWidth ν ℓ/(9*T))*ρ^2/((t:ℝ)-s) =
        -commonMeanWidth ν ℓ*ρ^2/(9*(T*((t:ℝ)-s))) := by
      field_simp
    rw [hexp]
    simpa only [jointCrossPastTest_apply,pairPastCoordinates,pairPathIncrement,
      ContinuousMap.coe_mk,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,mul_assoc] using hh
  have hW0 := wiener_path_initial_zero W _ hW
  have h0f : ∀ᵐ P ∂(V : Measure RealPathPair),P.1 0=0 := by
    have hh : ∀ᵐ P ∂(V : Measure RealPathPair).map Prod.fst,P 0=0 := by rw [hf]; exact hW0
    exact (ae_map_iff measurable_fst.aemeasurable ((isClosed_eq (continuous_eval_const 0) continuous_const).measurableSet)).mp hh
  have h0g : ∀ᵐ P ∂(V : Measure RealPathPair),P.2 0=0 := by
    have hh : ∀ᵐ P ∂(V : Measure RealPathPair).map Prod.snd,P 0=0 := by rw [hg]; exact hW0
    exact (ae_map_iff measurable_snd.aemeasurable ((isClosed_eq (continuous_eval_const 0) continuous_const).measurableSet)).mp hh
  have he := normalJointPast_product_identification (V : Measure RealPathPair) c h
    (by positivity : 0 < commonMeanWidth ν ℓ/(9*T)) (by positivity : 0 ≤ 16*‖symmetricClip 1‖^2)
    hcross (by
      have hs : {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0} =
          {z : RealPathPair × unitInterval | layerGap z.1 z.2=0} := by
        ext z
        change z.1.1 z.2-z.1.2 z.2=0 ↔ z.1.2 z.2-z.1.1 z.2=0
        rw [sub_eq_zero,sub_eq_zero,eq_comm]
      rw [hs]
      exact hz) (h0f.and h0g)
  simpa only [hf,hg] using he

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_SharedPairPathLimit
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.array_secondCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma probability_law_tendsto {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (X : ℕ → Ω → E)
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (W : ProbabilityMeasure E)
    (h : TendstoInDistribution X atTop id μ W) :
    Tendsto (β := ProbabilityMeasure E) (fun i => (⟨(μ i).map (X i),
      (Measure.isProbabilityMeasure_map_iff (hX i)).mpr inferInstance⟩ : ProbabilityMeasure E))
      atTop (𝓝 W) := by
  have hh := h.tendsto
  have he : (⟨(W : Measure E).map id,
      (Measure.isProbabilityMeasure_map_iff h.aemeasurable_limit).mpr inferInstance⟩ : ProbabilityMeasure E)=W := by
    apply Subtype.ext
    exact Measure.map_id
  simpa only [he] using hh

theorem shared_pair_path_limit_oai {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (T : ℝ) (hT : 0 < T) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      (∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
        (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw (T/(2*commonMeanWidth ν ℓ)) I) ∧
      ∀ x : ℕ → Lattice d,
      ∀ μ : ℕ → ProbabilityMeasure RealPathPair,
      (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
        (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
      Tendsto μ atTop (𝓝 (W.prod W)) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  obtain ⟨W,hW,hlim⟩ := shared_path_marginal_limits ν hue e f hef htrans r hr hT.le
  refine ⟨W,hW,?_⟩
  intro x μ hμ
  let η := fun i => sharedConditionedPairLaw ν ℓ (x i) (x i)
  have : ∀ i, IsProbabilityMeasure (η i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans _ _))
  let X := fun i (P : Path d × Path d) => recordLinearPath ℓ f (θ i) (r i) (n i) T (fun j => P.1 j-x i)
  let Y := fun i (P : Path d × Path d) => recordLinearPath ℓ f (θ i) (r i) (n i) T (fun j => P.2 j-x i)
  have hX (i : ℕ) : Measurable (X i) := (measurable_recordLinearPath _ _ _ _ _ _).comp (by fun_prop)
  have hY (i : ℕ) : Measurable (Y i) := (measurable_recordLinearPath _ _ _ _ _ _).comp (by fun_prop)
  obtain ⟨hf,hg⟩ := hlim x x (fun _ => rfl)
  have hMf : Tendsto (fun i => (μ i).map (f := Prod.fst) measurable_fst.aemeasurable) atTop (𝓝 W) := by
    have hh := probability_law_tendsto η X (fun i => (hX i).aemeasurable) W hf
    apply hh.congr'
    filter_upwards [] with i
    symm
    apply Subtype.ext
    change (μ i : Measure RealPathPair).map Prod.fst=_
    rw [hμ i,Measure.map_map measurable_fst (measurable_sharedLinearPairPath _ _ _ _ _ _ _ _)]
    rfl
  have hMg : Tendsto (fun i => (μ i).map (f := Prod.snd) measurable_snd.aemeasurable) atTop (𝓝 W) := by
    have hh := probability_law_tendsto η Y (fun i => (hY i).aemeasurable) W hg
    apply hh.congr'
    filter_upwards [] with i
    symm
    apply Subtype.ext
    change (μ i : Measure RealPathPair).map Prod.snd=_
    rw [hμ i,Measure.map_map measurable_snd (measurable_sharedLinearPairPath _ _ _ _ _ _ _ _)]
    rfl
  apply weak_limit_of_tight_identification μ (W.prod W) (pair_weak_tight μ W W hMf hMg)
  intro j hj V hV
  have hVf : (V : Measure RealPathPair).map Prod.fst=W := by
    have he := tendsto_nhds_unique
      ((ProbabilityMeasure.continuous_map continuous_fst).tendsto V |>.comp hV) (hMf.comp hj)
    exact congrArg (fun M : ProbabilityMeasure C(unitInterval,ℝ) => (M : Measure C(unitInterval,ℝ))) he
  have hVg : (V : Measure RealPathPair).map Prod.snd=W := by
    have he := tendsto_nhds_unique
      ((ProbabilityMeasure.continuous_map continuous_snd).tendsto V |>.comp hV) (hMg.comp hj)
    exact congrArg (fun M : ProbabilityMeasure C(unitInterval,ℝ) => (M : Measure C(unitInterval,ℝ))) he
  apply Subtype.ext
  exact shared_limit_product ν hue e f hef htrans (r ∘ j) (hr.comp hj) T hT (x ∘ j)
    (μ ∘ j) V hV W hW hVf hVg (fun i => hμ (j i))

end DirectionalTransience

end

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.shared_pair_path_limit_oai := @OAI.DirectionalTransience.shared_pair_path_limit_oai
