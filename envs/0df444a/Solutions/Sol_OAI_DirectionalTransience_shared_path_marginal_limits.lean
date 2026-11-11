-- Prove2me | solution 1 for OAI.DirectionalTransience.shared_path_marginal_limits
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:04:54.698579+00:00
-- url     : https://prove2.me/submissions/87eb8c62-9fe5-4ae7-9cbf-638262777533

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal007
import Theorems.Thm_OAI_DirectionalTransience_recordFluctuationScale_tendsto
import Theorems.Thm_OAI_DirectionalTransience_recordMedianSlope_small
import Theorems.Thm_OAI_DirectionalTransience_transverse_firstHit_linear_path_limit

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_CoordinateStrip
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

lemma abs_step_le_one {d : ℕ} (e : Direction d) (i : Fin d) :
    |step e i| ≤ (1 : ℤ) := by
  simp only [step]
  split_ifs <;> norm_num

lemma nearestNeighborPrefix_bound {d : ℕ} (f : Path d) (n : ℕ)
    (hf : NearestNeighborPrefix f n) {k : ℕ} (hk : k ≤ n) :
    f k ∈ LatticeBall (f 0) k := by
  induction k with
  | zero => simp [LatticeBall]
  | succ k ih =>
    obtain ⟨e, he⟩ := hf k (by omega)
    intro i
    rw [he]
    have hb := ih (by omega) i
    change |f k i + step e i - f 0 i| ≤ ((k + 1 : ℕ) : ℤ)
    calc
      _ = |(f k i - f 0 i) + step e i| := by congr 1; ring
      _ ≤ |f k i - f 0 i| + |step e i| := abs_add_le _ _
      _ ≤ (k : ℤ) + 1 := add_le_add hb (abs_step_le_one e i)
      _ = _ := by norm_cast

lemma edgeWeight_eq_zero_of_not_neighbor {d : ℕ} (ω : Environment d) (x y : Lattice d)
    (h : ¬ ∃ e : Direction d, y = x + step e) : edgeWeight ω x y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e _
  exact ite_eq_right (fun he => h ⟨e, he⟩)

lemma quenched_pathCylinder_locality {d : ℕ} (ω η : Environment d) (x : Lattice d)
    (n : ℕ) (hωη : Set.EqOn ω η (LatticeBall x n)) (f : Path d) :
    quenchedKernel (ω, x) (pathCylinder f n) =
      quenchedKernel (η, x) (pathCylinder f n) := by
  classical
  by_cases hstart : f 0 = x
  · rw [quenched_pathCylinder _ _ _ hstart, quenched_pathCylinder _ _ _ hstart]
    by_cases hpath : NearestNeighborPrefix f n
    · apply Finset.prod_congr rfl
      intro k hk
      have hn := (Finset.mem_range.mp hk).le
      have hb := nearestNeighborPrefix_bound f n hpath hn
      have hmem : f k ∈ LatticeBall x n := by
        intro i
        have h := hb i
        rw [hstart] at h
        exact h.trans (by exact_mod_cast hn)
      simp only [edgeWeight, hωη hmem]
    · unfold NearestNeighborPrefix at hpath
      push Not at hpath
      obtain ⟨k, hk, hbad⟩ := hpath
      have hbad' : ¬ ∃ e : Direction d, f (k + 1) = f k + step e := by
        simpa using hbad
      rw [Finset.prod_eq_zero (Finset.mem_range.mpr hk)
        (edgeWeight_eq_zero_of_not_neighbor ω _ _ hbad'),
        Finset.prod_eq_zero (Finset.mem_range.mpr hk)
        (edgeWeight_eq_zero_of_not_neighbor η _ _ hbad')]
  · rw [quenched_pathCylinder_zero _ _ _ hstart, quenched_pathCylinder_zero _ _ _ hstart]

lemma quenched_prefix_locality {d : ℕ} (ω η : Environment d) (x : Lattice d)
    (n : ℕ) (hωη : Set.EqOn ω η (LatticeBall x n))
    (C : Set ((i : Finset.Iic n) → Lattice d)) :
    quenchedKernel (ω, x) ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C) =
      quenchedKernel (η, x) ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C) := by
  have hm (f : (i : Finset.Iic n) → Lattice d) (_ : f ∈ C) :
      MeasurableSet ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f}) :=
    (Preorder.measurable_frestrictLe n) (measurableSet_singleton f)
  rw [← tsum_measure_preimage_singleton C.to_countable hm,
    ← tsum_measure_preimage_singleton C.to_countable hm]
  apply tsum_congr
  intro f
  rw [restrict_prefix_fiber]
  exact quenched_pathCylinder_locality ω η x n hωη _

lemma noDropFinite_measurable {d : ℕ} (ℓ : Vector d) (x : Lattice d) (n : ℕ) :
    Measurable (noDropFinite ℓ x n) :=
  (Kernel.measurable_coe _ (measurableSet_stayUntil _ n)).comp
    (measurable_id.prodMk measurable_const)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClippedInverse
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

lemma quenched_stayUntil_ball_locality {d : ℕ} (ω η : Environment d) (x : Lattice d)
    (S : Set (Lattice d)) (n : ℕ) (hωη : Set.EqOn ω η (LatticeBall x n)) :
    quenchedKernel (ω, x) (StayUntil S n) = quenchedKernel (η, x) (StayUntil S n) := by
  let C : Set ((i : Finset.Iic n) → Lattice d) := {f | ∀ i, f i ∈ S}
  have hC : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C = StayUntil S n := by
    ext X
    exact ⟨fun h i hi => h ⟨i, Finset.mem_Iic.mpr hi⟩,
      fun h i => h i (Finset.mem_Iic.mp i.2)⟩
  rw [← hC]
  exact quenched_prefix_locality ω η x n hωη C

lemma noDropFinite_measurable_ball {d : ℕ} (ℓ : Vector d) (x : Lattice d) (n : ℕ) :
    @Measurable _ _ (rowSigma (LatticeBall x n)) _ (noDropFinite ℓ x n) := by
  apply measurable_of_row_locality _ (noDropFinite_measurable ℓ x n) _ x
    (by simp [LatticeBall])
  intro ω η h
  exact quenched_stayUntil_ball_locality ω η x _ n h

lemma noDropFinite_translation {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Lattice d) (n : ℕ) :
    noDropFinite ℓ x n ω = noDropFinite ℓ 0 n (fun a => ω (x + a)) := by
  let S : Set (Lattice d) := {y | dot (realPosition (0 : Lattice d)) ℓ ≤ dot (realPosition y) ℓ}
  have hm : Measurable (fun X : Path d => fun j => X j - x) := by fun_prop
  have h := congrArg (fun μ : Measure (Path d) => μ (StayUntil S n))
    (quenched_translation ω x 0)
  rw [Measure.map_apply hm (measurableSet_stayUntil S n)] at h
  have he : (fun X : Path d => fun j => X j - x) ⁻¹' StayUntil S n =
      StayUntil {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ} n := by
    ext X
    simp only [StayUntil, S, Set.mem_preimage, Set.mem_ofPred_eq, dot_realPosition_sub]
    simp only [dot, realPosition, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero]
    constructor <;> intro h j hj <;> have hh := h j hj <;> linarith
  simpa only [he, add_zero, noDropFinite] using h

lemma noDropQuenched_le_finite {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) (n : ℕ) : noDropQuenched ℓ x ω ≤ noDropFinite ℓ x n ω :=
  measure_mono (fun _ h i _ => h i)

lemma noDropFinite_tendsto {d : ℕ} (ℓ : Vector d) (x : Lattice d) (ω : Environment d) :
    Tendsto (fun n => noDropFinite ℓ x n ω) atTop (𝓝 (noDropQuenched ℓ x ω)) := by
  let S : Set (Lattice d) := {y | dot (realPosition x) ℓ ≤ dot (realPosition y) ℓ}
  have he : (⋂ n, StayUntil S n) = NoDrop ℓ x := by
    ext X
    exact ⟨fun h i => Set.mem_iInter.mp h i i le_rfl,
      fun h => Set.mem_iInter.mpr fun _ i _ => h i⟩
  have h := tendsto_measure_iInter_atTop
    (μ := quenchedKernel (ω, x)) (s := fun n => StayUntil S n)
    (fun n => (measurableSet_stayUntil S n).nullMeasurableSet)
    (fun _ _ hmn _ h j hj => h j (hj.trans hmn)) ⟨0, measure_ne_top _ _⟩
  simpa only [he, Function.comp_def, noDropFinite, noDropQuenched] using h

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

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_WeightedAnnealed
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
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
namespace DirectionalTransience

lemma weighted_record_suffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (w : List (Direction d)) (J : ℝ)
    (hrecord : ∀ y ∈ wordDepartures 0 w,
      dot (realPosition y) ℓ < dot (realPosition (wordPath 0 w w.length)) ℓ)
    (hJ : J < dot (realPosition (wordPath 0 w w.length)) ℓ)
    (g : Environment d → ℝ≥0∞)
    (hg : @Measurable _ _ (rowSigma {z | dot (realPosition z) ℓ ≤ J}) _ g)
    (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    (∫⁻ ω, g ω * quenchedKernel (ω,0) ((fun X : Path d => fun j => X (w.length+j)-
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) ∂environmentLaw ν) =
      (∫⁻ ω, g ω * ENNReal.ofReal (wordWeight ω 0 w) ∂environmentLaw ν) *
        annealedLaw ν A := by
  let y := wordPath 0 w w.length
  let S : Set (Lattice d) := ↑(wordDepartures 0 w) ∪ {z | dot (realPosition z) ℓ ≤ J}
  let T : Set (Lattice d) := {z | dot (realPosition y) ℓ ≤ dot (realPosition z) ℓ}
  let B : Set (Path d) := (fun X : Path d => fun j => X j - y) ⁻¹' A
  have hB : MeasurableSet B := hA.preimage (by fun_prop)
  have hBT : B ⊆ Stay T := by
    intro X hX j
    have h := hAD hX j
    change dot (realPosition y) ℓ ≤ dot (realPosition (X j)) ℓ
    change dot (realPosition 0) ℓ ≤ dot (realPosition (X j - y)) ℓ at h
    rw [dot_realPosition_sub] at h
    have hz : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot, realPosition]
    rw [hz] at h
    linarith
  have hST : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    rcases hz with hz | hz
    · exact (not_le_of_gt (hrecord z hz)) hz'
    · exact (not_le_of_gt hJ) (hz'.trans hz)
  have hw (ω : Environment d) : quenchedKernel (ω,0)
      ((fun X : Path d => fun j => X (w.length+j)-y) ⁻¹' A ∩ wordCylinder 0 w) =
      ENNReal.ofReal (wordWeight ω 0 w) * quenchedKernel (ω,y) B := by
    have hh := quenched_prefix_future ω 0 (wordPath 0 w) (by simp) w.length hB
    change quenchedKernel (ω,0) (_ ∩ wordCylinder 0 w) =
      quenchedKernel (ω,0) (wordCylinder 0 w) * quenchedKernel (ω,y) B at hh
    rwa [quenched_wordCylinder] at hh
  change (∫⁻ ω, g ω * quenchedKernel (ω,0)
    ((fun X : Path d => fun j => X (w.length+j)-y) ⁻¹' A ∩ wordCylinder 0 w)
    ∂environmentLaw ν) = _
  simp_rw [hw, ← mul_assoc]
  have hh := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hST)
    ((hg.mono (rowSigma_mono Set.subset_union_right) le_rfl).mul
      ((measurable_wordWeight_on 0 w (fun _ hz => Or.inl hz)).ennreal_ofReal))
    (measurable_quenched_stay_event_rows T y (show dot (realPosition y) ℓ ≤ dot (realPosition y) ℓ from le_rfl) B hB hBT)
  simp only [Pi.mul_apply] at hh
  rw [hh]
  rw [annealed_event_translation ν y A hA]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

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

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_RegenerationWords
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FirstHighRecord
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
namespace DirectionalTransience

lemma measurableSet_firstHighRecord {d : ℕ} (ℓ : Vector d) (J : ℝ) (n : ℕ) :
    MeasurableSet {X : Path d | FirstHighRecord ℓ J X n} := by
  have hm j : MeasurableSet {X : Path d | J < dot (realPosition (X j)) ℓ} :=
    measurableSet_lt measurable_const ((measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp (measurable_pi_apply j))
  simp only [FirstHighRecord, Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_trueRecord ℓ n).inter ((hm n).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => by
      simpa only [imp_iff_not_or,Set.ofPred_or,Set.compl_ofPred] using
        (hm j).compl.union (measurableSet_trueRecord ℓ j).compl))

lemma firstHighRecord_unique {d : ℕ} (ℓ : Vector d) (J : ℝ) (X : Path d)
    {m n : ℕ} (hm : FirstHighRecord ℓ J X m) (hn : FirstHighRecord ℓ J X n) : m = n := by
  rcases lt_trichotomy m n with h | h | h
  · exact False.elim (hn.2.2 m h hm.2.1 hm.1)
  · exact h
  · exact False.elim (hm.2.2 n h hn.2.1 hn.1)

lemma annealed_exists_firstHighRecord {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (J : ℝ) :
    ∀ᵐ X ∂annealedLaw ν, ∃ n, FirstHighRecord ℓ J X n := by
  filter_upwards [htrans, annealed_trueRecords_unbounded ν ℓ htrans] with X ht hu
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_gt_atTop J))
  obtain ⟨n,hn,htrue⟩ := hu N
  have he : ∃ n, TrueRecord ℓ X n ∧ J < dot (realPosition (X n)) ℓ :=
    ⟨n,htrue,hN n hn.le⟩
  exact ⟨Nat.find he, (Nat.find_spec he).1, (Nat.find_spec he).2,
    fun j hj hjJ hjT => Nat.find_min he hj ⟨hjT,hjJ⟩⟩

lemma highWord_characterization {d : ℕ} (ℓ : Vector d) (J : ℝ)
    (w : List (Direction d)) (X : Path d) (hX : X ∈ wordCylinder 0 w) :
    (X ∈ NoDrop ℓ 0 ∧ FirstHighRecord ℓ J X w.length) ↔
      AdmissibleHighWord ℓ J w ∧
        (fun j => X (w.length+j)-wordPath 0 w w.length) ∈ NoDrop ℓ 0 := by
  have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot,realPosition]
  have hrec (j : ℕ) (hj : j ≤ w.length) := strictRecord_congr_prefix ℓ hj hX
  have hsuf : (fun j => X (w.length+j)-wordPath 0 w w.length) ∈ NoDrop ℓ 0 ↔
      X ∈ FutureNoDrop ℓ w.length := by
    rw [← hX w.length le_rfl]
    exact suffix_noDrop_iff ℓ X w.length
  constructor
  · rintro ⟨hD,hT,hJ,hfirst⟩
    refine ⟨⟨(hrec _ le_rfl).mp hT.1, ?_, ?_, ?_⟩, hsuf.mpr hT.2⟩
    · simpa only [hX _ le_rfl] using hJ
    · intro j hj
      simpa only [hzero,hX j hj] using hD j
    · intro j hj hjJ hjR
      have hfail := hfirst j hj (by simpa only [hX j hj.le] using hjJ)
      obtain ⟨k,hjk,hkn,hdrop⟩ := (not_trueRecord_before_true_iff ℓ X hj
        ((hrec j hj.le).mpr hjR) hT).mp hfail
      exact ⟨k,hjk,hkn,by simpa only [hX k hkn.le,hX j hj.le] using hdrop⟩
  · rintro ⟨⟨hR,hJ,hprefix,hfail⟩,hD⟩
    have ht : TrueRecord ℓ X w.length := ⟨(hrec _ le_rfl).mpr hR,hsuf.mp hD⟩
    refine ⟨(noDrop_iff_prefix_and_future ℓ 0 X w.length ht.2).mpr ?_, ht, ?_, ?_⟩
    · intro j hj
      simpa only [hzero,hX j hj] using hprefix j hj
    · simpa only [hX _ le_rfl] using hJ
    · intro j hj hjJ hjT
      obtain ⟨k,hjk,hkn,hk⟩ := hfail j hj (by simpa only [hX j hj.le] using hjJ)
        ((hrec j hj.le).mp hjT.1)
      have hd := hjT.2 (k-j)
      change dot (realPosition (X j)) ℓ ≤ dot (realPosition (X (j+(k-j)))) ℓ at hd
      rw [Nat.add_sub_of_le hjk.le] at hd
      have hk' := hk
      rw [← hX k hkn.le, ← hX j hj.le] at hk'
      exact (not_lt_of_ge hd) hk'

lemma measurableSet_highWordEvent {d : ℕ} (ℓ : Vector d) (J : ℝ) (w : List (Direction d)) :
    MeasurableSet (HighWordEvent ℓ J w) :=
  (measurableSet_noDrop ℓ 0).inter ((measurableSet_wordCylinder 0 w).inter
    (measurableSet_firstHighRecord ℓ J w.length))

lemma highWordEvent_disjoint {d : ℕ} (ℓ : Vector d) (J : ℝ) :
    Pairwise (fun u v : List (Direction d) => Disjoint (HighWordEvent ℓ J u) (HighWordEvent ℓ J v)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  rintro X ⟨_,hcu,hu⟩ ⟨_,hcv,hv⟩
  have hlen := firstHighRecord_unique ℓ J X hu hv
  apply huv (word_eq_of_paths 0 u v hlen ?_)
  intro j hj
  exact (hcu j hj).symm.trans (hcv j (hlen ▸ hj))

lemma highWordEvent_nil {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) :
    HighWordEvent ℓ J ([] : List (Direction d)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro X ⟨_,hc,hT⟩
  have h0 := hc 0 (by simp)
  have hj := hT.2.1
  simp only [List.length_nil,h0,wordPath_zero] at hj
  have hz : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot,realPosition]
  rw [hz] at hj
  exact (not_lt_of_ge hJ) hj

lemma highWordEvent_eq {d : ℕ} (ℓ : Vector d) (J : ℝ) (w : List (Direction d))
    (hw : AdmissibleHighWord ℓ J w) :
    HighWordEvent ℓ J w = (fun X : Path d => fun j => X (w.length+j)-
      wordPath 0 w w.length) ⁻¹' NoDrop ℓ 0 ∩ wordCylinder 0 w := by
  ext X
  constructor
  · rintro ⟨hD,hc,hT⟩
    exact ⟨((highWord_characterization ℓ J w X hc).mp ⟨hD,hT⟩).2,hc⟩
  · rintro ⟨hD,hc⟩
    have h := (highWord_characterization ℓ J w X hc).mpr ⟨hw,hD⟩
    exact ⟨h.1,hc,h.2⟩

lemma highWordEvent_empty {d : ℕ} (ℓ : Vector d) (J : ℝ) (w : List (Direction d))
    (hw : ¬ AdmissibleHighWord ℓ J w) : HighWordEvent ℓ J w = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro X ⟨hD,hc,hT⟩
  exact hw ((highWord_characterization ℓ J w X hc).mp ⟨hD,hT⟩).1

lemma highWord_eq_iff {d : ℕ} (ℓ : Vector d) (J : ℝ) (X : Path d) (w : List (Direction d))
    (hw : w ≠ []) : highWord ℓ J X = w ↔ X ∈ HighWordEvent ℓ J w := by
  unfold highWord
  split_ifs with h
  · constructor
    · intro he
      exact he ▸ h.choose_spec
    · intro hX
      by_contra hne
      exact (Set.disjoint_left.mp (highWordEvent_disjoint ℓ J hne)) h.choose_spec hX
  · simp only [eq_comm (a := ([] : List (Direction d))), hw, false_iff]
    exact fun hX => h ⟨w,hX⟩

lemma highWord_nil_iff {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) (X : Path d) :
    highWord ℓ J X = [] ↔ ¬ ∃ w, X ∈ HighWordEvent ℓ J w := by
  unfold highWord
  split_ifs with h
  · simp only [h,not_true_eq_false,iff_false]
    intro he
    have hh := h.choose_spec
    rw [he,highWordEvent_nil ℓ J hJ] at hh
    exact hh
  · simp [h]

lemma measurable_highWord {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) :
    Measurable (highWord ℓ J) := by
  apply measurable_to_countable'
  intro w
  by_cases hw : w = []
  · subst w
    have he : highWord ℓ J ⁻¹' {[]} = (⋃ w, HighWordEvent ℓ J w)ᶜ := by
      ext X
      simp only [Set.mem_preimage,Set.mem_singleton_iff,highWord_nil_iff ℓ J hJ,
        Set.mem_compl_iff,Set.mem_iUnion]
    rw [he]
    exact (MeasurableSet.iUnion (measurableSet_highWordEvent ℓ J)).compl
  · have he : highWord ℓ J ⁻¹' {w} = HighWordEvent ℓ J w := by
      ext X
      exact highWord_eq_iff ℓ J X w hw
    rw [he]
    exact measurableSet_highWordEvent ℓ J w

lemma measurable_highSuffix {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) :
    Measurable (highSuffix ℓ J) := by
  apply Measurable.of_eval
  intro j
  have hf : Measurable (fun X : Path d => (highWord ℓ J X).length) :=
    (measurable_of_countable List.length).comp (measurable_highWord ℓ J hJ)
  have heval : Measurable (fun p : Path d × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  exact (heval.comp (measurable_id.prodMk (hf.add_const j))).sub
    (heval.comp (measurable_id.prodMk hf))

lemma highSuffix_on_highWordEvent {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J)
    (w : List (Direction d)) (X : Path d) (hX : X ∈ HighWordEvent ℓ J w) :
    highSuffix ℓ J X = fun j => X (w.length+j)-wordPath 0 w w.length := by
  have hw : w ≠ [] := by
    intro he
    rw [he,highWordEvent_nil ℓ J hJ] at hX
    exact hX
  unfold highSuffix
  rw [(highWord_eq_iff ℓ J X w hw).mpr hX,hX.2.1 w.length le_rfl]

lemma conditioned_highWord_exists {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (J : ℝ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, ∃ w, X ∈ HighWordEvent ℓ J w := by
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  filter_upwards [conditionedLaw_noDrop ν ℓ,hac.ae_le (annealed_initial ν),
    hac.ae_le (annealed_nearest_neighbor ν),hac.ae_le (annealed_exists_firstHighRecord ν ℓ htrans J)]
    with X hD h0 hNN hT
  obtain ⟨n,hn⟩ := hT
  obtain ⟨w,hw,hc⟩ := exists_word_prefix X hNN n
  exact ⟨w,hD,by simpa only [h0] using hc,hw.symm ▸ hn⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WeightedConditioned
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
namespace DirectionalTransience

lemma weightedConditioned_apply_subset {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g : Environment d → ℝ≥0∞) (A : Set (Path d)) (hA : MeasurableSet A)
    (hAD : A ⊆ NoDrop ℓ 0) :
    weightedConditioned ν ℓ g A = (annealedLaw ν (NoDrop ℓ 0))⁻¹ * weightedAnnealed ν g A := by
  simp only [weightedConditioned,Measure.smul_apply,Measure.restrict_apply hA,
    Set.inter_eq_left.mpr hAD,smul_eq_mul]

lemma weightedConditioned_highWord_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (g : Environment d → ℝ≥0∞)
    (hg : @Measurable _ _ (rowSigma {z | dot (realPosition z) ℓ ≤ J}) _ g)
    (w : List (Direction d)) (A : Set (Path d)) (hA : MeasurableSet A) :
    weightedConditioned ν ℓ g (HighWordEvent ℓ J w ∩ highSuffix ℓ J ⁻¹' A) =
      weightedConditioned ν ℓ g (HighWordEvent ℓ J w) * conditionedLaw ν ℓ A := by
  have hg' : Measurable g := hg.mono (rowSigma_le _) le_rfl
  by_cases hw : AdmissibleHighWord ℓ J w
  · let F := fun X : Path d => fun j => X (w.length+j)-wordPath 0 w w.length
    have hF : Measurable F := by fun_prop
    have hFD : ∀ B : Set (Path d), B ⊆ NoDrop ℓ 0 →
        F ⁻¹' B ∩ wordCylinder 0 w ⊆ NoDrop ℓ 0 := by
      intro B hBD X hX
      exact ((highWord_characterization ℓ J w X hX.2).mpr ⟨hw,hBD hX.1⟩).1
    have hrec : ∀ y ∈ wordDepartures 0 w,
        dot (realPosition y) ℓ < dot (realPosition (wordPath 0 w w.length)) ℓ := by
      intro y hy
      obtain ⟨j,hj,rfl⟩ := (wordDepartures_mem_iff 0 y w).mp hy
      exact hw.1 j hj
    have hf (B : Set (Path d)) (hB : MeasurableSet B) (hBD : B ⊆ NoDrop ℓ 0) :
        weightedConditioned ν ℓ g (F ⁻¹' B ∩ wordCylinder 0 w) =
          (∫⁻ ω, g ω * ENNReal.ofReal (wordWeight ω 0 w) ∂environmentLaw ν) *
            conditionedLaw ν ℓ B := by
      rw [weightedConditioned_apply_subset ν ℓ g _ ((hB.preimage hF).inter
        (measurableSet_wordCylinder 0 w)) (hFD B hBD),
        weightedAnnealed_apply ν g hg' _ ((hB.preimage hF).inter (measurableSet_wordCylinder 0 w)),
        weighted_record_suffix ν ℓ w J hrec hw.2.1 g hg B hB hBD,
        conditionedLaw_apply_of_subset ν ℓ B hB hBD]
      ac_rfl
    have he : HighWordEvent ℓ J w ∩ highSuffix ℓ J ⁻¹' A =
        F ⁻¹' (A ∩ NoDrop ℓ 0) ∩ wordCylinder 0 w := by
      ext X
      constructor
      · rintro ⟨hX,hXA⟩
        have hXD := (Set.ext_iff.mp (highWordEvent_eq ℓ J w hw) X).mp hX
        exact ⟨⟨by simpa only [Set.mem_preimage,highSuffix_on_highWordEvent ℓ J hJ w X hX] using hXA,hXD.1⟩,hXD.2⟩
      · rintro ⟨⟨hXA,hXD⟩,hc⟩
        have hX := (Set.ext_iff.mp (highWordEvent_eq ℓ J w hw) X).mpr ⟨hXD,hc⟩
        exact ⟨hX,by simpa only [Set.mem_preimage,highSuffix_on_highWordEvent ℓ J hJ w X hX] using hXA⟩
    have hmass : weightedConditioned ν ℓ g (HighWordEvent ℓ J w) =
        ∫⁻ ω, g ω * ENNReal.ofReal (wordWeight ω 0 w) ∂environmentLaw ν := by
      rw [highWordEvent_eq ℓ J w hw,hf _ (measurableSet_noDrop ℓ 0) Set.Subset.rfl]
      have hD : conditionedLaw ν ℓ (NoDrop ℓ 0) = 1 := by
        rw [conditionedLaw_apply_of_subset ν ℓ _ (measurableSet_noDrop ℓ 0) Set.Subset.rfl]
        exact ENNReal.inv_mul_cancel hp (measure_ne_top _ _)
      rw [hD,mul_one]
    rw [he,hf _ (hA.inter (measurableSet_noDrop ℓ 0)) Set.inter_subset_right,
      conditionedLaw_inter_noDrop ν ℓ A hA,hmass]
  · simp [highWordEvent_empty ℓ J w hw]

lemma weightedConditioned_highSuffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (J : ℝ) (hJ : 0 ≤ J)
    (g : Environment d → ℝ≥0∞)
    (hg : @Measurable _ _ (rowSigma {z | dot (realPosition z) ℓ ≤ J}) _ g)
    (hgle : ∀ ω, g ω ≤ 1) :
    (weightedConditioned ν ℓ g).map (highSuffix ℓ J) =
      weightedConditioned ν ℓ g Set.univ • conditionedLaw ν ℓ := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hle := weightedConditioned_le ν ℓ g (hg.mono (rowSigma_le _) le_rfl) hgle
  have he : ∀ᵐ X ∂weightedConditioned ν ℓ g, ∃ w, X ∈ HighWordEvent ℓ J w :=
    (Measure.absolutelyContinuous_of_le hle).ae_le (conditioned_highWord_exists ν ℓ htrans J)
  have hpart (B : Set (Path d)) (hB : MeasurableSet B) :
      weightedConditioned ν ℓ g B =
        ∑' w : List (Direction d), weightedConditioned ν ℓ g (HighWordEvent ℓ J w ∩ B) := by
    rw [← measure_iUnion (fun u v huv => (highWordEvent_disjoint ℓ J huv).mono
      Set.inter_subset_left Set.inter_subset_left)
        (fun w => (measurableSet_highWordEvent ℓ J w).inter hB)]
    apply measure_congr
    filter_upwards [he] with X ⟨w,hw⟩
    apply propext
    exact ⟨fun hX => Set.mem_iUnion.mpr ⟨w,hw,hX⟩,
      fun hX => (Set.mem_iUnion.mp hX).choose_spec.2⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_highSuffix ℓ J hJ) hA,
    hpart _ (hA.preimage (measurable_highSuffix ℓ J hJ))]
  simp_rw [weightedConditioned_highWord_factor ν ℓ J hJ hp g hg _ A hA]
  rw [ENNReal.tsum_mul_right,Measure.smul_apply,smul_eq_mul]
  have hm := hpart Set.univ MeasurableSet.univ
  simp only [Set.inter_univ] at hm
  rw [← hm]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma levyProkhorov_map_distance_le {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F G : Ω → E)
    (hF : Measurable F) (hG : Measurable G) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : μ {ω | δ ≤ dist (F ω) (G ω)} ≤ ENNReal.ofReal δ) :
    levyProkhorovDist (μ.map F) (μ.map G) ≤ δ := by
  haveI : IsProbabilityMeasure (μ.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  haveI : IsProbabilityMeasure (μ.map G) := Measure.isProbabilityMeasure_map hG.aemeasurable
  apply levyProkhorovDist_le_of_forall_le _ _ hδ
  intro ε B hε hB
  rw [Measure.map_apply hF hB,Measure.map_apply hG Metric.isOpen_thickening.measurableSet]
  have hs : F ⁻¹' B ⊆ G ⁻¹' Metric.thickening ε B ∪ {ω | δ ≤ dist (F ω) (G ω)} := by
    intro ω hω
    by_cases hh : δ ≤ dist (F ω) (G ω)
    · exact Or.inr hh
    · exact Or.inl (Metric.mem_thickening_iff.mpr ⟨F ω,hω,by
        rw [dist_comm]; exact (lt_of_not_ge hh).trans hε⟩)
  exact (measure_mono hs).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (hbad.trans (ENNReal.ofReal_le_ofReal hε.le))))

lemma weak_map_of_varying_close {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (F G : ℕ → Ω → E) (hF : ∀ i, Measurable (F i)) (hG : ∀ i, Measurable (G i))
    (ν : ProbabilityMeasure E)
    (hlim : Tendsto (fun i => ProbabilityMeasure.map (⟨μ i, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Ω) (f := (F i)) (by first | exact (hF i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
      atTop (𝓝 ν))
    (hclose : ∀ ε, 0 < ε → Tendsto (fun i => (μ i).real
      {ω | ε ≤ dist (F i ω) (G i ω)}) atTop (𝓝 0)) :
    Tendsto (fun i => ProbabilityMeasure.map (⟨μ i, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Ω) (f := (G i)) (by first | exact (hG i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
      atTop (𝓝 ν) := by
  let A i := ProbabilityMeasure.map (⟨μ i, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Ω) (f := (F i)) (by first | exact (hF i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let B i := ProbabilityMeasure.map (⟨μ i, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Ω) (f := (G i)) (by first | exact (hG i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hd : Tendsto (fun i => dist (LevyProkhorov.ofMeasure (A i))
      (LevyProkhorov.ofMeasure (B i))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [(hclose (ε/2) (by positivity)).eventually_lt_const
      (by positivity : 0 < ε/2)] with i hi
    have hb : μ i {ω | ε/2 ≤ dist (F i ω) (G i ω)} ≤ ENNReal.ofReal (ε/2) := by
      have hh := ENNReal.ofReal_le_ofReal hi.le
      simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh
    have h := levyProkhorov_map_distance_le (μ i) (F i) (G i) (hF i) (hG i) (by positivity) hb
    rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg]
    exact h.trans_lt (half_lt_self hε)
  have hA := LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto ν |>.comp hlim
  have hB := hA.congr_dist hd
  exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto
    (LevyProkhorov.ofMeasure ν) |>.comp hB

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_WeakLimitBoundedFreshMap
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
namespace DirectionalTransience

lemma weak_limit_of_bounded_fresh_map {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (η : ℕ → Measure Ω)
    [∀ i, IsProbabilityMeasure (η i)] (S : Ω → Ω) (hS : Measurable S)
    (hmap : ∀ i, (η i).map S = μ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hdom : ∀ i, η i ≤ C • μ) (F : ℕ → Ω → E) (hF : ∀ i, Measurable (F i))
    (W : ProbabilityMeasure E)
    (hlim : Tendsto (fun i => ProbabilityMeasure.map (⟨μ,(by first | exact Measure.isProbabilityMeasure_map (by first | exact hS.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Ω)
      (f := (F i)) (by first | exact (hF i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 W))
    (hclose : ∀ ε, 0 < ε → Tendsto (fun i => μ.real
      {ω | ε ≤ dist (F i (S ω)) (F i ω)}) atTop (𝓝 0)) :
    Tendsto (fun i => ProbabilityMeasure.map (⟨η i,(by first | exact Measure.isProbabilityMeasure_map (by first | exact hS.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Ω)
      (f := (F i)) (by first | exact (hF i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 W) := by
  apply weak_map_of_varying_close η (fun i => F i ∘ S) F
    (fun i => (hF i).comp hS) hF W
  · have he (i : ℕ) : ProbabilityMeasure.map (⟨η i,(by first | exact Measure.isProbabilityMeasure_map (by first | exact hS.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Ω)
        (f := (F i ∘ S)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) =
        ProbabilityMeasure.map (⟨μ,(by first | exact Measure.isProbabilityMeasure_map (by first | exact hS.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Ω) (f := (F i)) (by first | exact (hF i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) := by
      apply Subtype.ext
      change (η i).map (F i ∘ S) = μ.map (F i)
      rw [← Measure.map_map (hF i) hS,hmap]
    simpa only [he] using hlim
  · intro ε hε
    have hb (i : ℕ) : (η i).real {ω | ε ≤ dist (F i (S ω)) (F i ω)} ≤
        C.toReal * μ.real {ω | ε ≤ dist (F i (S ω)) (F i ω)} := by
      have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top hC (measure_ne_top _ _)) (hdom i {ω | ε ≤ dist (F i (S ω)) (F i ω)})
      simpa only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,Measure.real] using hh
    exact squeeze_zero (fun _ => measureReal_nonneg) hb
      (by simpa only [mul_zero] using (hclose ε hε).const_mul C.toReal)

lemma normalized_weightedConditioned_highSuffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (J : ℝ) (hJ : 0 ≤ J)
    (g : Environment d → ℝ≥0∞)
    (hg : @Measurable _ _ (rowSigma {z | dot (realPosition z) ℓ ≤ J}) _ g)
    (hgle : ∀ ω, g ω ≤ 1) (hpos : weightedConditioned ν ℓ g Set.univ ≠ 0) :
    (normalizedMeasure (weightedConditioned ν ℓ g)).map (highSuffix ℓ J) = conditionedLaw ν ℓ := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let : IsFiniteMeasure (weightedConditioned ν ℓ g) :=
    weightedConditioned_finite ν ℓ g (hg.mono (rowSigma_le _) le_rfl) hgle
  rw [normalizedMeasure,Measure.map_smul,
    weightedConditioned_highSuffix ν ℓ htrans J hJ g hg hgle,
    smul_smul,ENNReal.inv_mul_cancel hpos (measure_ne_top _ _),one_smul]

lemma normalized_weightedConditioned_le {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g : Environment d → ℝ≥0∞) (hg : Measurable g) (hgle : ∀ ω, g ω ≤ 1)
    (c : ℝ≥0∞) (hc : c ≤ weightedConditioned ν ℓ g Set.univ) :
    normalizedMeasure (weightedConditioned ν ℓ g) ≤ c⁻¹ • conditionedLaw ν ℓ := by
  intro A
  change (weightedConditioned ν ℓ g Set.univ)⁻¹ * weightedConditioned ν ℓ g A ≤ c⁻¹ * conditionedLaw ν ℓ A
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr hc) (weightedConditioned_le ν ℓ g hg hgle A)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_HighRecordCount
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

lemma measurable_highRecordCount {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) :
    Measurable (highRecordCount ℓ J) := by
  have h₁ : Measurable (fun p : Path d × ℕ => recordCount ℓ p.1 p.2) :=
    measurable_from_prod_countable_left (fun n => measurable_recordCount ℓ n)
  have h₂ : Measurable (fun X : Path d => (X, (highWord ℓ J X).length)) :=
    measurable_id.prodMk ((measurable_of_countable List.length).comp (measurable_highWord ℓ J hJ))
  change Measurable ((fun p : Path d × ℕ => recordCount ℓ p.1 p.2) ∘
    (fun X : Path d => (X, (highWord ℓ J X).length)))
  exact h₁.comp h₂

lemma measurable_highRecordPosition {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) :
    Measurable (highRecordPosition ℓ J) := by
  exact (measurable_from_prod_countable_left (f := fun p : Path d × ℕ => p.1 p.2)
    (fun n => measurable_pi_apply n)).comp
      (measurable_id.prodMk ((measurable_of_countable List.length).comp (measurable_highWord ℓ J hJ)))

lemma conditioned_highSuffix_recordPosition {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (J : ℝ) (hJ : 0 ≤ J) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ j,
      recordIndexPosition ℓ j (highSuffix ℓ J X) =
        recordIndexPosition ℓ (j+highRecordCount ℓ J X) X-highRecordPosition ℓ J X := by
  filter_upwards [conditioned_highWord_exists ν ℓ htrans J,
    (conditionedLaw_absolutelyContinuous ν ℓ).ae_le htrans] with X hw ht j
  obtain ⟨w,hw⟩ := hw
  have hne : w ≠ [] := by
    intro h
    rw [h,highWordEvent_nil ℓ J hJ] at hw
    exact hw
  have he := (highWord_eq_iff ℓ J X w hne).mpr hw
  have hn : 0 < w.length := List.length_pos_iff.mpr hne
  have hh := recordIndexPosition_suffix ℓ X hw.1 ht hn hw.2.2.1 j
  have hPos : highRecordPosition ℓ J X = X w.length := by simp only [highRecordPosition,he]
  have hCnt : highRecordCount ℓ J X = recordCount ℓ X w.length := by simp only [highRecordCount,he]
  have hS : highSuffix ℓ J X = fun k => X (w.length+k)-X w.length := by
    funext k
    change X ((highWord ℓ J X).length+k)-X (highWord ℓ J X).length = _
    rw [he]
  rw [hCnt,hPos,hS,hh,add_sub_cancel_right]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_NoDropApproxError
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
namespace DirectionalTransience

lemma noDropFinite_lower_rows {d : ℕ} (e : Direction d) (y : Lattice d)
    (hy : signedHeight e y = 0) (J : ℕ) :
    @Measurable _ _ (rowSigma {z | dot (realPosition z) (realPosition (step e)) ≤ (J:ℝ)}) _
      (noDropFinite (realPosition (step e)) y J) := by
  apply (noDropFinite_measurable_ball _ y J).mono (rowSigma_mono ?_) le_rfl
  intro z hz
  change dot (realPosition z) (realPosition (step e)) ≤ (J:ℝ)
  rw [signedHeight_projection]
  have hh := abs_le.mp (hz e.1)
  have hc : signedHeight e z ≤ (J:ℤ) := by
    simp only [signedHeight] at hy ⊢
    cases he : e.2 <;> simp only [he,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hy ⊢ <;> omega
  exact_mod_cast hc

lemma noDropApproxError_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (y : Lattice d) (J : ℕ) :
    (∫⁻ ω, noDropFinite ℓ y J ω-noDropQuenched ℓ y ω ∂environmentLaw ν) =
      noDropApproxError ν ℓ J := by
  simp_rw [noDropFinite_translation ℓ _ y J,noDropQuenched_translation ℓ _ y]
  have hh := lintegral_map ((noDropFinite_measurable ℓ 0 J).sub (measurable_noDropQuenched ℓ 0))
    (show Measurable (fun ω : Environment d => fun a => ω (y+a)) by fun_prop)
    (μ := environmentLaw ν)
  rw [environment_translation] at hh
  exact hh.symm

lemma noDropApproxError_le_one {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (J : ℕ) : noDropApproxError ν ℓ J ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂environmentLaw ν :=
      lintegral_mono (fun _ => tsub_le_self.trans prob_le_one)
    _ = 1 := by simp

lemma noDropApproxError_tendsto {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) : Tendsto (noDropApproxError ν ℓ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (μ := environmentLaw ν)
    (f := fun _ => (0 : ℝ≥0∞)) (fun _ => (1 : ℝ≥0∞))
    (fun J => (noDropFinite_measurable ℓ 0 J).sub (measurable_noDropQuenched ℓ 0))
    (fun _ => ae_of_all _ (fun _ => tsub_le_self.trans prob_le_one))
    (by simp) (ae_of_all _ (fun ω => ?_))
  · change Tendsto (fun J => ∫⁻ ω, noDropFinite ℓ 0 J ω-noDropQuenched ℓ 0 ω ∂environmentLaw ν)
      atTop (𝓝 0)
    simpa only [lintegral_zero,Pi.sub_apply] using h
  · have ht := ENNReal.Tendsto.sub (noDropFinite_tendsto ℓ 0 ω)
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => noDropQuenched ℓ 0 ω) atTop (𝓝 (noDropQuenched ℓ 0 ω)))
      (Or.inl (measure_ne_top _ _))
    simpa only [Pi.sub_apply,tsub_self] using ht

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma normalizedMeasure_upper_le {Ω : Type*} [MeasurableSpace Ω]
    (μ η : Measure Ω) (hμη : μ ≤ η) (δ c : ℝ≥0∞)
    (hc : c ≤ μ Set.univ) (A : Set Ω) (hA : η A ≤ μ A+δ) :
    normalizedMeasure η A ≤ normalizedMeasure μ A+c⁻¹*δ := by
  change (η Set.univ)⁻¹*η A ≤ (μ Set.univ)⁻¹*μ A+c⁻¹*δ
  calc
    _ ≤ (μ Set.univ)⁻¹*η A := mul_le_mul_left (ENNReal.inv_le_inv.mpr (hμη Set.univ)) _
    _ ≤ (μ Set.univ)⁻¹*(μ A+δ) := mul_le_mul_right hA _
    _ = (μ Set.univ)⁻¹*μ A+(μ Set.univ)⁻¹*δ := mul_add _ _ _
    _ ≤ (μ Set.univ)⁻¹*μ A+c⁻¹*δ :=
      add_le_add le_rfl (mul_le_mul_left (ENNReal.inv_le_inv.mpr hc) δ)

lemma levyProkhorov_normalized_map_le {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ η : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hμη : μ ≤ η) (δ c : ℝ≥0∞) (hc : 0 < c) (hδ : δ ≠ ⊤)
    (hcmass : c ≤ μ Set.univ) (hbound : ∀ A, MeasurableSet A → η A ≤ μ A+δ)
    (F : Ω → E) (hF : Measurable F) :
    levyProkhorovDist ((normalizedMeasure η).map F) ((normalizedMeasure μ).map F) ≤ (c⁻¹*δ).toReal := by
  let : IsProbabilityMeasure (normalizedMeasure μ) := normalizedMeasure_probability μ
    (ne_of_gt (hc.trans_le hcmass))
  let : IsProbabilityMeasure (normalizedMeasure η) := normalizedMeasure_probability η
    (ne_of_gt (hc.trans_le (hcmass.trans (hμη Set.univ))))
  let : IsProbabilityMeasure ((normalizedMeasure μ).map F) := by first | exact Measure.isProbabilityMeasure_map (by first | exact hF.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : IsProbabilityMeasure ((normalizedMeasure η).map F) := by first | exact Measure.isProbabilityMeasure_map (by first | exact hF.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  apply levyProkhorovDist_le_of_forall_le _ _ ENNReal.toReal_nonneg
  intro ε B hε hB
  rw [Measure.map_apply hF hB]
  have hb := normalizedMeasure_upper_le μ η hμη δ c hcmass (F ⁻¹' B)
    (hbound _ (hB.preimage hF))
  have he : c⁻¹*δ ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc.ne') hδ)]
    exact ENNReal.ofReal_le_ofReal hε.le
  have hBsub : (normalizedMeasure μ) (F ⁻¹' B) ≤
      ((normalizedMeasure μ).map F) (Metric.thickening ε B) := by
    rw [Measure.map_apply hF Metric.isOpen_thickening.measurableSet]
    exact measure_mono (Set.preimage_mono (Metric.self_subset_thickening (ENNReal.toReal_nonneg.trans_lt hε) B))
  exact hb.trans (add_le_add hBsub he)

lemma weak_limit_of_uniform_approximation {E : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → ProbabilityMeasure E) (η : ℕ → ℕ → ProbabilityMeasure E)
    (W : ProbabilityMeasure E) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hlim : ∀ J, Tendsto (η J) atTop (𝓝 W))
    (hclose : ∀ J i, levyProkhorovDist (μ i : Measure E) (η J i : Measure E) ≤ δ J) :
    Tendsto μ atTop (𝓝 W) := by
  have hW : Tendsto (fun i => LevyProkhorov.ofMeasure (μ i)) atTop (𝓝 (LevyProkhorov.ofMeasure W)) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨J,hJ⟩ := (hδ.eventually_lt_const (half_pos hε)).exists
    have hη := LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto W |>.comp (hlim J)
    filter_upwards [(Metric.tendsto_nhds.mp hη) (ε/2) (half_pos hε)] with i hi
    exact (dist_triangle _ (LevyProkhorov.ofMeasure (η J i)) _).trans_lt
      (by
        have hc := hclose J i
        dsimp only [Function.comp_apply] at hi
        change dist (LevyProkhorov.ofMeasure (μ i)) (LevyProkhorov.ofMeasure (η J i)) ≤ δ J at hc
        linarith)
  exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto
    (LevyProkhorov.ofMeasure W) |>.comp hW

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma weightedConditioned_apply {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g : Environment d → ℝ≥0∞) (hg : Measurable g)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    weightedConditioned ν ℓ g A = (annealedLaw ν (NoDrop ℓ 0))⁻¹ *
      ∫⁻ ω, g ω * quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0) ∂environmentLaw ν := by
  rw [weightedConditioned,Measure.smul_apply,Measure.restrict_apply hA,
    weightedAnnealed_apply ν g hg _ (hA.inter (measurableSet_noDrop ℓ 0))]
  rfl

lemma weightedConditioned_mono {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g h : Environment d → ℝ≥0∞) (hg : Measurable g) (hh : Measurable h)
    (hgh : ∀ ω, g ω ≤ h ω) : weightedConditioned ν ℓ g ≤ weightedConditioned ν ℓ h := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [weightedConditioned_apply ν ℓ g hg A hA,weightedConditioned_apply ν ℓ h hh A hA]
  exact mul_le_mul_right (lintegral_mono (fun ω => mul_le_mul_left (hgh ω) _)) _

lemma weightedConditioned_approx {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g h : Environment d → ℝ≥0∞) (hg : Measurable g) (hh : Measurable h)
    (hgh : ∀ ω, g ω ≤ h ω) (A : Set (Path d)) (hA : MeasurableSet A) :
    weightedConditioned ν ℓ h A ≤ weightedConditioned ν ℓ g A+
      (annealedLaw ν (NoDrop ℓ 0))⁻¹ * ∫⁻ ω, h ω-g ω ∂environmentLaw ν := by
  rw [weightedConditioned_apply ν ℓ g hg A hA,weightedConditioned_apply ν ℓ h hh A hA,← mul_add]
  apply mul_le_mul_right
  have hQ : Measurable (fun ω : Environment d => quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0)) :=
    (Kernel.measurable_coe _ (hA.inter (measurableSet_noDrop ℓ 0))).comp
      (measurable_id.prodMk measurable_const)
  rw [← lintegral_add_left (show Measurable (fun ω => g ω * quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0)) from hg.mul hQ) (fun ω => h ω-g ω)]
  apply lintegral_mono
  intro ω
  calc
    _ = (g ω+(h ω-g ω))*quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0) := by
      rw [add_tsub_cancel_of_le (hgh ω)]
    _ = g ω*quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0)+
        (h ω-g ω)*quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0) := add_mul _ _ _
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' prob_le_one)

lemma weightedConditioned_noDrop_mass {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (y : Lattice d) :
    weightedConditioned ν ℓ (noDropQuenched ℓ y) Set.univ =
      (annealedLaw ν (NoDrop ℓ 0))⁻¹ * sharedNoDropMass ν ℓ 0 y := by
  rw [weightedConditioned_apply ν ℓ _ (measurable_noDropQuenched ℓ y) _ MeasurableSet.univ]
  simp only [Set.univ_inter,sharedNoDropMass,noDropQuenched]
  congr 1
  apply lintegral_congr
  intro ω
  exact mul_comm _ _

lemma weightedConditioned_noDrop_approx {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (y : Lattice d) (J : ℕ) (A : Set (Path d)) (hA : MeasurableSet A) :
    weightedConditioned ν ℓ (noDropFinite ℓ y J) A ≤
      weightedConditioned ν ℓ (noDropQuenched ℓ y) A+
      (annealedLaw ν (NoDrop ℓ 0))⁻¹ * noDropApproxError ν ℓ J := by
  simpa only [noDropApproxError_translation ν ℓ y J] using
    weightedConditioned_approx ν ℓ _ _ (measurable_noDropQuenched ℓ y)
      (noDropFinite_measurable ℓ y J) (fun ω => noDropQuenched_le_finite ℓ y ω J) A hA

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

lemma heightPolygon_segment (F : ℕ → ℝ) (r n T : ℝ) (h : 0 ≤ T*n)
    (j : ℕ) (t : unitInterval) (hjt : (j:ℝ) ≤ T*n*(t:ℝ)) (htj : T*n*(t:ℝ) ≤ (j:ℝ)+1) :
    heightPolygon F r n T t =
      (F j+(T*n*(t:ℝ)-j)*(F (j+1)-F j))/r := by
  by_cases he : T*n*(t:ℝ) = (j:ℝ)+1
  · rw [heightPolygon_grid F r n T h (j+1) t (by simpa using he),he]
    congr 1
    ring
  · have hj : ⌊T*n*(t:ℝ)⌋₊ = j := Nat.floor_eq_iff (mul_nonneg h t.2.1) |>.mpr ⟨hjt,lt_of_le_of_ne htj he⟩
    rw [heightPolygon_formula F r n T h,hj]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightPolygonTranslateApply
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
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
namespace DirectionalTransience

lemma heightPolygon_translate_apply (F : ℕ → ℝ) (r n T : ℝ) (hn : 0 ≤ n) (hT : 0 ≤ T)
    (H : ℕ) (c : ℝ) (t u : unitInterval)
    (hu : (T+1)*n*(u:ℝ) = T*n*(t:ℝ)+(H:ℝ)) :
    heightPolygon (fun k => F (k+H)+c) r n T t =
      heightPolygon F r n (T+1) u+c/r := by
  let j := ⌊T*n*(t:ℝ)⌋₊
  have h0 : 0 ≤ T*n*(t:ℝ) := mul_nonneg (mul_nonneg hT hn) t.2.1
  have hj0 : (j:ℝ) ≤ T*n*(t:ℝ) := Nat.floor_le h0
  have hj1 : T*n*(t:ℝ) ≤ (j:ℝ)+1 := (Nat.lt_floor_add_one _).le
  rw [heightPolygon_formula _ _ _ _ (mul_nonneg hT hn),
    heightPolygon_segment F r n (T+1) (mul_nonneg (by linarith) hn) (j+H) u
      (by rw [hu]; push_cast <;> linarith)
      (by rw [hu]; push_cast <;> linarith),hu]
  simp only [Nat.cast_add,Nat.add_assoc,Nat.add_comm 1 H]
  dsimp only [j]
  ring

lemma heightPolygon_translate_norm_le (F : ℕ → ℝ) (r n T : ℝ)
    (hn : 0 < n) (hT : 0 ≤ T) (H : ℕ) (hH : (H:ℝ) ≤ n) (c ε δ : ℝ)
    (hδ : (H:ℝ)/n ≤ δ)
    (hmod : heightPolygon F r n (T+1) ∉ ContinuousOscillation ε δ) :
    ‖heightPolygon (fun k => F (k+H)+c) r n T-heightPolygon F r n T‖ ≤ ε+|c/r| := by
  have hL : 0 < T+1 := by linarith
  have hLn : 0 < (T+1)*n := mul_pos hL hn
  apply (ContinuousMap.norm_le_of_nonempty _).mpr
  intro t
  let s : unitInterval := ⟨T/(T+1)*(t:ℝ),mul_nonneg (div_nonneg hT hL.le) t.2.1,
    (mul_le_of_le_one_right (div_nonneg hT hL.le) t.2.2).trans
      ((div_le_one hL).mpr (by linarith))⟩
  let u : unitInterval := ⟨(T*n*(t:ℝ)+(H:ℝ))/((T+1)*n),
    div_nonneg (add_nonneg (mul_nonneg (mul_nonneg hT hn.le) t.2.1) (Nat.cast_nonneg _)) hLn.le,
    (div_le_one hLn).mpr (by nlinarith [mul_le_of_le_one_right (mul_nonneg hT hn.le) t.2.2])⟩
  have hs : (T+1)*n*(s:ℝ) = T*n*(t:ℝ) := by dsimp [s]; field_simp
  have hu : (T+1)*n*(u:ℝ) = T*n*(t:ℝ)+(H:ℝ) := by dsimp [u]; field_simp
  have hdist : dist u s ≤ δ := by
    have he : (u:ℝ)-(s:ℝ) = (H:ℝ)/((T+1)*n) := by dsimp [u,s]; field_simp <;> ring
    rw [Subtype.dist_eq,Real.dist_eq,he,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hLn.le)]
    exact (div_le_div_of_nonneg_left (Nat.cast_nonneg H) hn (by nlinarith)).trans hδ
  have hm : |heightPolygon F r n (T+1) u-heightPolygon F r n (T+1) s| ≤ ε :=
    le_of_not_gt (fun h => hmod ⟨u,s,hdist,h⟩)
  have hsval := heightPolygon_translate_apply F r n T hn.le hT 0 0 t s (by simpa using hs)
  simp only [add_zero,zero_div] at hsval
  simp only [ContinuousMap.sub_apply,Real.norm_eq_abs]
  rw [heightPolygon_translate_apply F r n T hn.le hT H c t u hu,hsval]
  calc
    |heightPolygon F r n (T+1) u+c/r-heightPolygon F r n (T+1) s|
      = |(heightPolygon F r n (T+1) u-heightPolygon F r n (T+1) s)+c/r| := by ring_nf
    _ ≤ |heightPolygon F r n (T+1) u-heightPolygon F r n (T+1) s|+|c/r| := abs_add_le _ _
    _ ≤ ε+|c/r| := by gcongr

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightPolygonRandomShiftSmall
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
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
namespace DirectionalTransience

lemma heightPolygon_random_shift_small {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : ℕ → ℕ → Ω → ℝ)
    (hF : ∀ i k, Measurable (F i k)) (r n : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (H : Ω → ℕ) (hH : Measurable H) (c : ℕ → Ω → ℝ)
    (hc : TendstoInMeasure μ (fun i ω => c i ω/r i) atTop 0)
    {T : ℝ} (hT : 0 ≤ T)
    (ht : IsTightMeasureSet (Set.range (fun i => μ.map
      (fun ω => heightPolygon (fun k => F i k ω) (r i) (n i) (T+1))))) :
    TendstoInMeasure μ (fun i ω =>
      heightPolygon (fun k => F i (k+H ω) ω+c i ω) (r i) (n i) T-
        heightPolygon (fun k => F i k ω) (r i) (n i) T) atTop 0 := by
  have hhn : TendstoInMeasure μ (fun i ω => (H ω:ℝ)/n i) atTop 0 := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun i => (((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hH).div_const _).aestronglyMeasurable)
    exact ae_of_all _ (fun _ => tendsto_const_nhds.div_atTop hn)
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  simp only [Pi.zero_apply,sub_zero]
  apply Metric.tendsto_nhds.2
  intro β hβ
  obtain ⟨δ,hδ,hmod⟩ := tight_path_modulus _ ht (by positivity : 0 < ε/4)
    (by positivity : 0 < β/4)
  have hht := (tendstoInMeasure_iff_measureReal_norm.1 hhn) (min δ 1) (by positivity)
  have hct := (tendstoInMeasure_iff_measureReal_norm.1 hc) (ε/4) (by positivity)
  simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] at hht hct
  filter_upwards [hn.eventually (eventually_gt_atTop (0:ℝ)),
    hht.eventually_lt_const (by positivity : 0 < β/4),
    hct.eventually_lt_const (by positivity : 0 < β/4)] with i hni hhi hci
  let A := {ω | min δ 1 ≤ |(H ω:ℝ)/n i|}
  let B := {ω | heightPolygon (fun k => F i k ω) (r i) (n i) (T+1) ∈ ContinuousOscillation (ε/4) δ}
  let C := {ω | ε/4 ≤ |c i ω/r i|}
  have hb : μ.real B ≤ β/4 := by
    have hm := hmod i
    rw [Measure.map_apply (measurable_heightPolygon _ (hF i) _ _ _)
      (isOpen_continuousOscillation _ _).measurableSet] at hm
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hm
  have hs : {ω | ε ≤ ‖heightPolygon (fun k => F i (k+H ω) ω+c i ω) (r i) (n i) T-
        heightPolygon (fun k => F i k ω) (r i) (n i) T‖} ⊆ A ∪ B ∪ C := by
    intro ω hω
    by_contra hh
    have ha : ω ∉ A := fun h => hh (Or.inl (Or.inl h))
    have hb' : ω ∉ B := fun h => hh (Or.inl (Or.inr h))
    have hc' : ω ∉ C := fun h => hh (Or.inr h)
    have ha' : (H ω:ℝ)/n i < min δ 1 := by
      simpa only [A,Set.mem_ofPred_eq,not_le,abs_of_nonneg
        (div_nonneg (Nat.cast_nonneg _) hni.le)] using ha
    have hHi : (H ω:ℝ) ≤ n i := ((div_lt_one hni).mp (ha'.trans_le (min_le_right _ _))).le
    have hnorm := heightPolygon_translate_norm_le (fun k => F i k ω) (r i) (n i) T
      hni hT (H ω) hHi (c i ω) (ε/4) δ (ha'.le.trans (min_le_left _ _)) hb'
    have hcc : |c i ω/r i| < ε/4 := lt_of_not_ge hc'
    simp only [Set.mem_ofPred_eq] at hω
    linarith
  have hm := (measureReal_mono (μ := μ) hs (measure_ne_top _ _)).trans
    ((measureReal_union_le (μ := μ) (s₁ := A ∪ B) (s₂ := C)).trans
      (add_le_add (measureReal_union_le (μ := μ) (s₁ := A) (s₂ := B)) le_rfl))
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  dsimp only [A,C] at hm
  linarith

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_RecordLinearPath
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma recordLinearPath_suffix_small {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (f : Direction d)
    (θ r n : ℕ → ℝ) (hr : Tendsto r atTop atTop) (hn : Tendsto n atTop atTop)
    (hθ : Tendsto (fun i => θ i/r i) atTop (𝓝 0))
    (J : ℝ) (hJ : 0 ≤ J) {T : ℝ} (hT : 0 ≤ T)
    (ht : IsTightMeasureSet (Set.range (fun i => (conditionedLaw ν ℓ).map
      (recordLinearPath ℓ f (θ i) (r i) (n i) (T+1))))) :
    TendstoInMeasure (conditionedLaw ν ℓ) (fun i X =>
      recordLinearPath ℓ f (θ i) (r i) (n i) T (highSuffix ℓ J X)-
        recordLinearPath ℓ f (θ i) (r i) (n i) T X) atTop 0 := by
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let H := highRecordCount ℓ J
  let D := fun X => signedCoordinate f (highRecordPosition ℓ J X)
  have hH : Measurable H := measurable_highRecordCount ℓ J hJ
  have hD : Measurable D := (measurable_of_countable (signedCoordinate f)).comp (measurable_highRecordPosition ℓ J hJ)
  let F := fun i h X => signedCoordinate f (recordIndexPosition ℓ h X)-(h:ℝ)*θ i
  have hF : ∀ i h, Measurable (F i h) := fun i h =>
    ((measurable_of_countable (signedCoordinate f)).comp (measurable_recordIndexPosition ℓ h)).sub_const ((h:ℝ)*θ i)
  let c := fun i X => (H X:ℝ)*θ i-D X
  have hc : TendstoInMeasure μ (fun i X => c i X/r i) atTop 0 := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro i
      exact (((((measurable_of_countable (fun k : ℕ => (k:ℝ))).comp hH).mul_const _).sub hD).div_const _).aestronglyMeasurable
    · apply ae_of_all
      intro X
      have hh := (hθ.const_mul (H X:ℝ)).sub (tendsto_const_nhds.div_atTop hr :
        Tendsto (fun i => D X/r i) atTop (𝓝 0))
      simpa only [mul_zero,sub_zero,Pi.zero_apply,c,sub_div,mul_div_assoc] using hh
  have hs := heightPolygon_random_shift_small μ F hF r n hn H hH c hc hT ht
  apply hs.congr _ (Filter.EventuallyEq.rfl)
  intro i
  filter_upwards [conditioned_highSuffix_recordPosition ν ℓ htrans J hJ] with X hX
  congr 1
  congr 1
  funext h
  dsimp only [recordLinearPath,F,c,H,D]
  rw [hX h,signedCoordinate_sub,Nat.cast_add]
  ring

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma weighted_recordLinearPath_limit {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (f : Direction d)
    (θ r n : ℕ → ℝ) (hr : Tendsto r atTop atTop) (hn : Tendsto n atTop atTop)
    (hθ : Tendsto (fun i => θ i/r i) atTop (𝓝 0))
    {T : ℝ} (hT : 0 ≤ T)
    (ht : IsTightMeasureSet (Set.range (fun i => (conditionedLaw ν ℓ).map
      (recordLinearPath ℓ f (θ i) (r i) (n i) (T+1)))))
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hlim :
      letI : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
        (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
      TendstoInDistribution (fun i => recordLinearPath ℓ f (θ i) (r i) (n i) T)
        atTop id (fun _ => conditionedLaw ν ℓ) W)
    (J : ℝ) (hJ : 0 ≤ J) (g : ℕ → Environment d → ℝ≥0∞)
    (hg : ∀ i, @Measurable _ _ (rowSigma {z | dot (realPosition z) ℓ ≤ J}) _ (g i))
    (hgle : ∀ i ω, g i ω ≤ 1) (c : ℝ≥0∞) (hc : 0 < c)
    (hcmass : ∀ i, c ≤ weightedConditioned ν ℓ (g i) Set.univ) :
    letI : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
    letI : ∀ i, IsFiniteMeasure (weightedConditioned ν ℓ (g i)) := fun i =>
      weightedConditioned_finite ν ℓ (g i) ((hg i).mono (rowSigma_le _) le_rfl) (hgle i)
    letI : ∀ i, IsProbabilityMeasure (normalizedMeasure (weightedConditioned ν ℓ (g i))) := fun i =>
      normalizedMeasure_probability (weightedConditioned ν ℓ (g i))
        (ne_of_gt (hc.trans_le (hcmass i)))
    TendstoInDistribution (fun i => recordLinearPath ℓ f (θ i) (r i) (n i) T)
      atTop id (fun i => normalizedMeasure (weightedConditioned ν ℓ (g i))) W := by
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let : ∀ i, IsFiniteMeasure (weightedConditioned ν ℓ (g i)) := fun i =>
    weightedConditioned_finite ν ℓ (g i) ((hg i).mono (rowSigma_le _) le_rfl) (hgle i)
  let η := fun i => normalizedMeasure (weightedConditioned ν ℓ (g i))
  let : ∀ i, IsProbabilityMeasure (η i) := fun i => normalizedMeasure_probability _
    (ne_of_gt (hc.trans_le (hcmass i)))
  let F := fun i => recordLinearPath ℓ f (θ i) (r i) (n i) T
  have hF : ∀ i, Measurable (F i) := fun i => measurable_recordLinearPath _ _ _ _ _ _
  have hl : Tendsto (fun i => ProbabilityMeasure.map (⟨μ,(by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_recordLinearPath <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure (Path d))
      (f := (F i)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 W) := by
    have hh := hlim.tendsto
    change Tendsto (fun i => ProbabilityMeasure.map (⟨μ,(by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_recordLinearPath <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure (Path d))
      (f := (F i)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 (W.map (f := id) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) at hh
    have he : W.map (f := id) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = W := Subtype.ext Measure.map_id
    rw [he] at hh
    exact hh
  have hs := recordLinearPath_suffix_small ν ℓ htrans f θ r n hr hn hθ J hJ hT ht
  have hclose : ∀ ε, 0 < ε → Tendsto (fun i => μ.real
      {X | ε ≤ dist (F i (highSuffix ℓ J X)) (F i X)}) atTop (𝓝 0) := by
    intro ε hε
    simpa only [Pi.zero_apply,sub_zero,dist_eq_norm,F] using
      (tendstoInMeasure_iff_measureReal_norm.mp hs ε hε)
  refine ⟨fun i => (hF i).aemeasurable,measurable_id.aemeasurable,?_⟩
  have hout := weak_limit_of_bounded_fresh_map μ η (highSuffix ℓ J)
    (measurable_highSuffix ℓ J hJ)
    (fun i => normalized_weightedConditioned_highSuffix ν ℓ htrans J hJ (g i) (hg i)
      (hgle i) (ne_of_gt (hc.trans_le (hcmass i)))) c⁻¹ (ENNReal.inv_ne_top.mpr hc.ne')
    (fun i => normalized_weightedConditioned_le ν ℓ (g i) ((hg i).mono (rowSigma_le _) le_rfl)
      (hgle i) c (hcmass i)) F hF W hl hclose
  change Tendsto (fun i => ProbabilityMeasure.map (⟨η i,(by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_recordLinearPath <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure (Path d))
    (f := (F i)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop (𝓝 (W.map (f := id) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)))
  have he : W.map (f := id) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = W := Subtype.ext Measure.map_id
  rw [he]
  exact hout

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma noDropWeighted_recordLinearPath_limit {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (θ r n : ℕ → ℝ) (hr : Tendsto r atTop atTop) (hn : Tendsto n atTop atTop)
    (hθ : Tendsto (fun i => θ i/r i) atTop (𝓝 0))
    {T : ℝ} (hT : 0 ≤ T)
    (ht : IsTightMeasureSet (Set.range (fun i => (conditionedLaw ν (realPosition (step e))).map
      (recordLinearPath (realPosition (step e)) f (θ i) (r i) (n i) (T+1)))))
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hlim :
      letI : IsProbabilityMeasure (conditionedLaw ν (realPosition (step e))) :=
        conditionedLaw_probability ν _ (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
      TendstoInDistribution (fun i => recordLinearPath (realPosition (step e)) f (θ i) (r i) (n i) T)
        atTop id (fun _ => conditionedLaw ν (realPosition (step e))) W)
    (y : ℕ → Lattice d) (hy : ∀ i, signedHeight e (y i) = 0)
    (c : ℝ≥0∞) (hc : 0 < c)
    (hcmass : ∀ i, c ≤ weightedConditioned ν (realPosition (step e))
      (noDropQuenched (realPosition (step e)) (y i)) Set.univ) :
    letI : IsProbabilityMeasure (conditionedLaw ν (realPosition (step e))) :=
      conditionedLaw_probability ν _ (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
    letI : ∀ i, IsFiniteMeasure (weightedConditioned ν (realPosition (step e))
      (noDropQuenched (realPosition (step e)) (y i))) := fun _i =>
      weightedConditioned_finite ν _ _ (measurable_noDropQuenched _ _) (fun _ => prob_le_one)
    letI : ∀ i, IsProbabilityMeasure (normalizedMeasure (weightedConditioned ν (realPosition (step e))
      (noDropQuenched (realPosition (step e)) (y i)))) := fun i =>
        normalizedMeasure_probability _ (ne_of_gt (hc.trans_le (hcmass i)))
    TendstoInDistribution (fun i => recordLinearPath (realPosition (step e)) f (θ i) (r i) (n i) T)
      atTop id (fun i => normalizedMeasure (weightedConditioned ν (realPosition (step e))
        (noDropQuenched (realPosition (step e)) (y i)))) W := by
  let ℓ := realPosition (step e)
  let p := annealedLaw ν (NoDrop ℓ 0)
  have hp : p ≠ 0 := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let μ i := weightedConditioned ν ℓ (noDropQuenched ℓ (y i))
  let η J i := weightedConditioned ν ℓ (noDropFinite ℓ (y i) J)
  let : ∀ i, IsFiniteMeasure (μ i) := fun i => weightedConditioned_finite ν ℓ _
    (measurable_noDropQuenched ℓ (y i)) (fun _ => prob_le_one)
  let : ∀ J i, IsFiniteMeasure (η J i) := fun J i => weightedConditioned_finite ν ℓ _
    (noDropFinite_measurable ℓ (y i) J) (fun _ => prob_le_one)
  let : ∀ i, IsProbabilityMeasure (normalizedMeasure (μ i)) := fun i =>
    normalizedMeasure_probability _ (ne_of_gt (hc.trans_le (hcmass i)))
  have hmono (J i : ℕ) : μ i ≤ η J i := weightedConditioned_mono ν ℓ _ _
    (measurable_noDropQuenched ℓ (y i)) (noDropFinite_measurable ℓ (y i) J)
    (fun ω => noDropQuenched_le_finite ℓ (y i) ω J)
  have heta (J i : ℕ) : c ≤ η J i Set.univ := (hcmass i).trans (hmono J i Set.univ)
  let : ∀ J i, IsProbabilityMeasure (normalizedMeasure (η J i)) := fun J i =>
    normalizedMeasure_probability _ (ne_of_gt (hc.trans_le (heta J i)))
  let F i := recordLinearPath ℓ f (θ i) (r i) (n i) T
  have hF : ∀ i, Measurable (F i) := fun i => measurable_recordLinearPath _ _ _ _ _ _
  let A i : ProbabilityMeasure C(unitInterval,ℝ) :=
    ProbabilityMeasure.map (⟨normalizedMeasure (μ i),(by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_recordLinearPath <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure (Path d)) (f := (F i)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let B J i : ProbabilityMeasure C(unitInterval,ℝ) :=
    ProbabilityMeasure.map (⟨normalizedMeasure (η J i),(by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_recordLinearPath <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure (Path d)) (f := (F i)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have heW : W.map (f := id) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = W := Subtype.ext Measure.map_id
  have hB (J : ℕ) : Tendsto (B J) atTop (𝓝 W) := by
    have h := weighted_recordLinearPath_limit ν ℓ htrans f θ r n hr hn hθ hT ht W hlim
      (J:ℝ) (Nat.cast_nonneg J) (fun i => noDropFinite ℓ (y i) J)
      (fun i => noDropFinite_lower_rows e (y i) (hy i) J) (fun _ _ => prob_le_one) c hc (heta J)
    have hh := h.tendsto
    change Tendsto (B J) atTop (𝓝 (W.map (f := id) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) at hh
    rwa [heW] at hh
  have hd : Tendsto (fun J => (c⁻¹*(p⁻¹*noDropApproxError ν ℓ J)).toReal) atTop (𝓝 0) := by
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (noDropApproxError_tendsto ν ℓ)).const_mul ((c⁻¹).toReal*(p⁻¹).toReal)
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_zero,mul_zero,Function.comp_def,mul_assoc] using h
  have hclose (J i : ℕ) : levyProkhorovDist (A i : Measure C(unitInterval,ℝ)) (B J i : Measure C(unitInterval,ℝ)) ≤
      (c⁻¹*(p⁻¹*noDropApproxError ν ℓ J)).toReal := by
    rw [levyProkhorovDist_comm]
    exact levyProkhorov_normalized_map_le (μ i) (η J i) (hmono J i)
      (p⁻¹*noDropApproxError ν ℓ J) c hc
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp)
        (ne_of_lt ((noDropApproxError_le_one ν ℓ J).trans_lt (by simp))))
      (hcmass i) (fun A hA => weightedConditioned_noDrop_approx ν ℓ (y i) J A hA) (F i) (hF i)
  refine ⟨fun i => (hF i).aemeasurable,measurable_id.aemeasurable,?_⟩
  change Tendsto A atTop (𝓝 (W.map (f := id) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)))
  rw [heW]
  exact weak_limit_of_uniform_approximation A B W _ hd hB hclose

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SharedConditionedPairLawFst
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma sharedConditionedPairLaw_fst {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (y : Lattice d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    (sharedConditionedPairLaw ν ℓ 0 y).map Prod.fst =
      normalizedMeasure (weightedConditioned ν ℓ (noDropQuenched ℓ y)) := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA,sharedConditionedPairLaw,Measure.smul_apply,
    Measure.restrict_apply (hA.preimage measurable_fst)]
  have he : Prod.fst ⁻¹' A ∩ (NoDrop ℓ 0 ×ˢ NoDrop ℓ y) =
      (A ∩ NoDrop ℓ 0) ×ˢ NoDrop ℓ y := by ext Z; exact and_assoc.symm
  rw [he,sharedPairLaw_rectangle ν 0 y _ _ (hA.inter (measurableSet_noDrop ℓ 0))
    (measurableSet_noDrop ℓ y),normalizedMeasure,Measure.smul_apply,
    weightedConditioned_noDrop_mass,weightedConditioned_apply ν ℓ _ (measurable_noDropQuenched ℓ y) A hA]
  simp only [smul_eq_mul]
  have hc : (((annealedLaw ν (NoDrop ℓ 0))⁻¹ * sharedNoDropMass ν ℓ 0 y)⁻¹ *
      (annealedLaw ν (NoDrop ℓ 0))⁻¹) = (sharedNoDropMass ν ℓ 0 y)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)))
      (Or.inl (ENNReal.inv_ne_top.mpr hp)),inv_inv,mul_right_comm,
      ENNReal.mul_inv_cancel hp (measure_ne_top _ _),one_mul]
  rw [← mul_assoc,hc]
  congr 1
  apply lintegral_congr
  intro ω
  exact mul_comm _ _

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

lemma sharedPairLaw_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (z x y : Lattice d) :
    (sharedPairLaw ν (z+x) (z+y)).map
      (fun Z : Path d × Path d => ((fun j => Z.1 j-z),(fun j => Z.2 j-z))) = sharedPairLaw ν x y := by
  have hm : Measurable (fun X : Path d => fun j => X j-z) := by fun_prop
  have hpair : Measurable (fun Z : Path d × Path d => ((fun j => Z.1 j-z),(fun j => Z.2 j-z))) := by fun_prop
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hpair (hA.prod hB)]
  have he : (fun Z : Path d × Path d => ((fun j => Z.1 j-z),(fun j => Z.2 j-z))) ⁻¹' (A ×ˢ B) =
      ((fun X : Path d => fun j => X j-z) ⁻¹' A) ×ˢ ((fun X : Path d => fun j => X j-z) ⁻¹' B) := rfl
  rw [he,sharedPairLaw_rectangle ν (z+x) (z+y) _ _ (hA.preimage hm) (hB.preimage hm),
    sharedPairLaw_rectangle ν x y A B hA hB]
  have ht (ω : Environment d) (a : Lattice d) (C : Set (Path d)) (hC : MeasurableSet C) :
      quenchedKernel (ω,z+a) ((fun X : Path d => fun j => X j-z) ⁻¹' C) =
        quenchedKernel ((fun b => ω (z+b)),a) C := by
    rw [← Measure.map_apply hm hC,quenched_translation]
  simp_rw [ht _ x A hA,ht _ y B hB]
  have henv : Measurable (fun ω : Environment d => fun b => ω (z+b)) := by fun_prop
  have hprod : Measurable (fun ω : Environment d => quenchedKernel (ω,x) A * quenchedKernel (ω,y) B) :=
    ((Kernel.measurable_coe _ hA).comp (measurable_id.prodMk measurable_const)).mul
      ((Kernel.measurable_coe _ hB).comp (measurable_id.prodMk measurable_const))
  rw [← lintegral_map hprod henv,environment_translation]

lemma sharedNoDropMass_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (z x y : Lattice d) :
    sharedNoDropMass ν ℓ (z+x) (z+y) = sharedNoDropMass ν ℓ x y := by
  rw [sharedNoDropMass_eq,sharedNoDropMass_eq,← sharedPairLaw_translation ν z x y,
    Measure.map_apply (by fun_prop) ((measurableSet_noDrop ℓ x).prod (measurableSet_noDrop ℓ y))]
  congr 1
  change NoDrop ℓ (z+x) ×ˢ NoDrop ℓ (z+y) =
    ((fun X : Path d => fun j => X j-z) ⁻¹' NoDrop ℓ x) ×ˢ
      ((fun X : Path d => fun j => X j-z) ⁻¹' NoDrop ℓ y)
  rw [noDrop_translation,noDrop_translation]

lemma sharedConditionedPairLaw_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (z x y : Lattice d) :
    (sharedConditionedPairLaw ν ℓ (z+x) (z+y)).map
      (fun Z : Path d × Path d => ((fun j => Z.1 j-z),(fun j => Z.2 j-z))) =
        sharedConditionedPairLaw ν ℓ x y := by
  have hm : Measurable (fun Z : Path d × Path d => ((fun j => Z.1 j-z),(fun j => Z.2 j-z))) := by fun_prop
  have he : (fun Z : Path d × Path d => ((fun j => Z.1 j-z),(fun j => Z.2 j-z))) ⁻¹'
      (NoDrop ℓ x ×ˢ NoDrop ℓ y) = NoDrop ℓ (z+x) ×ˢ NoDrop ℓ (z+y) := by
    change ((fun X : Path d => fun j => X j-z) ⁻¹' NoDrop ℓ x) ×ˢ
      ((fun X : Path d => fun j => X j-z) ⁻¹' NoDrop ℓ y) = _
    rw [noDrop_translation,noDrop_translation]
  rw [sharedConditionedPairLaw,Measure.map_smul,← he,← Measure.restrict_map hm
      ((measurableSet_noDrop ℓ x).prod (measurableSet_noDrop ℓ y)),sharedPairLaw_translation,
      sharedNoDropMass_translation]
  rfl

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma tendstoInDistribution_pullback {Ω Ω' E E' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace E'] [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] (μ : ℕ → Measure Ω) (η : ℕ → Measure Ω')
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (η i)]
    (S : ℕ → Ω → Ω') (hS : ∀ i, Measurable (S i)) (hm : ∀ i, (μ i).map (S i) = η i)
    (F : ℕ → Ω' → E) (hF : ∀ i, Measurable (F i)) (G : E' → E)
    (W : Measure E') [IsProbabilityMeasure W]
    (hlim : TendstoInDistribution F atTop G η W) :
    TendstoInDistribution (fun i => F i ∘ S i) atTop G μ W := by
  refine ⟨fun i => ((hF i).comp (hS i)).aemeasurable,hlim.aemeasurable_limit,?_⟩
  apply hlim.tendsto.congr'
  apply Eventually.of_forall
  intro i
  apply Subtype.ext
  change (η i).map (F i) = (μ i).map (F i ∘ S i)
  rw [← Measure.map_map (hF i) (hS i),hm]

lemma distribution_sequence_tight {Ω E Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : ℕ → Ω → E) (G : Ω' → E) (W : Measure Ω') [IsProbabilityMeasure W]
    (h : TendstoInDistribution X atTop G μ W) :
    IsTightMeasureSet (Set.range (fun i => (μ i).map (X i))) := by
  let A : ℕ → ProbabilityMeasure E := fun i => ⟨(μ i).map (X i), Measure.isProbabilityMeasure_map (h.forall_aemeasurable i)⟩
  let B : ProbabilityMeasure E := ⟨W.map G, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩
  have hh : Tendsto A atTop (𝓝 B) := h.tendsto
  have ht := weak_sequence_tight (E := E) (μ := A) (ν := B) hh
  exact ht

theorem shared_first_zero_path_limit {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      (∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
        (fun g : C(unitInterval,ℝ) => I.restrict g) =
          gaussianPathFiniteLaw (T/(2*commonMeanWidth ν ℓ)) I) ∧
      ∀ y : ℕ → Lattice d, (∀ i, signedHeight e (y i) = 0) →
        letI : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ 0 (y i)) := fun i =>
          sharedConditionedPairLaw_probability ν ℓ 0 (y i)
            (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans 0 (y i)))
        TendstoInDistribution (fun i Z => recordLinearPath ℓ f
          (recordMedianSlope ν ℓ hp f (r i)) (r i)
          (fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)) T Z.1)
          atTop id (fun i => sharedConditionedPairLaw ν ℓ 0 (y i)) W := by
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let θ i := recordMedianSlope ν ℓ hp f (r i)
  let n i := fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  obtain ⟨W,hW,hWf⟩ := transverse_firstHit_linear_path_limit ν hue e f hef htrans r hr hT
  obtain ⟨W',hW',_⟩ := transverse_firstHit_linear_path_limit ν hue e f hef htrans r hr (show 0 ≤ T+1 by linarith)
  have ht : IsTightMeasureSet (Set.range (fun i => (conditionedLaw ν ℓ).map
      (recordLinearPath ℓ f (θ i) (r i) (n i) (T+1)))) := by
    have hh := distribution_sequence_tight _ _ _ _ hW'
    change IsTightMeasureSet (Set.range (fun i => (conditionedLaw ν ℓ).map
      (fun X => heightPolygon (fun h => signedCoordinate f (recordIndexPosition ℓ h X)-
        (h:ℝ)*θ i) (r i) (n i) (T+1))))
    exact hh
  refine ⟨W,hWf,?_⟩
  intro y hy
  let : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ 0 (y i)) := fun i =>
    sharedConditionedPairLaw_probability ν ℓ 0 (y i)
      (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans 0 (y i)))
  obtain ⟨c₀,hc₀,hc₀m⟩ := sharedNoDropMass_uniform_positive ν hue ℓ (signed_direction_unit e) htrans
  let c := (annealedLaw ν (NoDrop ℓ 0))⁻¹*c₀
  have hc : 0 < c := ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hc₀.ne'
  have hcmass (i : ℕ) : c ≤ weightedConditioned ν ℓ (noDropQuenched ℓ (y i)) Set.univ := by
    rw [weightedConditioned_noDrop_mass]
    exact mul_le_mul_right (hc₀m 0 (y i)) _
  let μ i := normalizedMeasure (weightedConditioned ν ℓ (noDropQuenched ℓ (y i)))
  let : ∀ i, IsFiniteMeasure (weightedConditioned ν ℓ (noDropQuenched ℓ (y i))) := fun i =>
    weightedConditioned_finite ν ℓ _ (measurable_noDropQuenched ℓ (y i)) (fun _ => prob_le_one)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => normalizedMeasure_probability _
    (ne_of_gt (hc.trans_le (hcmass i)))
  have hlim := noDropWeighted_recordLinearPath_limit ν e f htrans θ r n hr.1
    (recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1)
    (recordMedianSlope_small ν hue e f hef htrans r hr) hT ht W hW y hy c hc hcmass
  exact tendstoInDistribution_pullback (fun i => sharedConditionedPairLaw ν ℓ 0 (y i)) μ
    (fun _ => Prod.fst) (fun _ => measurable_fst) (fun i => sharedConditionedPairLaw_fst ν ℓ (y i) hp)
    (fun i => recordLinearPath ℓ f (θ i) (r i) (n i) T)
    (fun i => measurable_recordLinearPath _ _ _ _ _ _) id W hlim

end DirectionalTransience

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

theorem shared_path_marginal_limits_oai {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let F := fun i => recordLinearPath ℓ f (recordMedianSlope ν ℓ hp f (r i)) (r i)
      (fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)) T
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      (∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
        (fun g : C(unitInterval,ℝ) => I.restrict g) =
          gaussianPathFiniteLaw (T/(2*commonMeanWidth ν ℓ)) I) ∧
      ∀ x y : ℕ → Lattice d, (∀ i, signedHeight e (x i) = signedHeight e (y i)) →
        letI : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (x i) (y i)) := fun i =>
          sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
            (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
        TendstoInDistribution (fun i Z => F i (fun j => Z.1 j-x i))
          atTop id (fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)) W ∧
        TendstoInDistribution (fun i Z => F i (fun j => Z.2 j-y i))
          atTop id (fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)) W := by
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let F := fun i => recordLinearPath ℓ f (recordMedianSlope ν ℓ hp f (r i)) (r i)
    (fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)) T
  have hF (i : ℕ) : Measurable (F i) := measurable_recordLinearPath _ _ _ _ _ _
  obtain ⟨W,hW,hlim⟩ := shared_first_zero_path_limit ν hue e f hef htrans r hr hT
  have hfirst (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i)) :
      letI : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (x i) (y i)) := fun i =>
        sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
          (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
      TendstoInDistribution (fun i Z => F i (fun j => Z.1 j-x i))
        atTop id (fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)) W := by
    let : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (x i) (y i)) := fun i =>
      sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
        (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
    let : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ 0 (y i-x i)) := fun i =>
      sharedConditionedPairLaw_probability ν ℓ 0 (y i-x i)
        (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans 0 (y i-x i)))
    have hy : ∀ i, signedHeight e (y i-x i) = 0 := fun i => by rw [signedHeight_sub,← hxy i,sub_self]
    have hm (i : ℕ) : (sharedConditionedPairLaw ν ℓ (x i) (y i)).map
        (fun Z : Path d × Path d => ((fun j => Z.1 j-x i),(fun j => Z.2 j-x i))) =
          sharedConditionedPairLaw ν ℓ 0 (y i-x i) := by
      simpa only [add_zero,add_sub_cancel] using sharedConditionedPairLaw_translation ν ℓ (x i) 0 (y i-x i)
    exact tendstoInDistribution_pullback _ _ _ (fun _ => by fun_prop) hm
      (fun i Z => F i Z.1) (fun i => (hF i).comp measurable_fst) id W (hlim _ hy)
  refine ⟨W,hW,fun x y hxy => ?_⟩
  let : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (x i) (y i)) := fun i =>
    sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
      (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
  let : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (y i) (x i)) := fun i =>
    sharedConditionedPairLaw_probability ν ℓ (y i) (x i)
      (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (y i) (x i)))
  refine ⟨hfirst x y hxy,?_⟩
  exact tendstoInDistribution_pullback _ _ (fun _ => Prod.swap) (fun _ => measurable_swap)
    (fun i => sharedConditionedPairLaw_swap ν ℓ (x i) (y i))
    (fun i Z => F i (fun j => Z.1 j-y i)) (fun i => (hF i).comp (by fun_prop)) id W
    (hfirst y x (fun i => (hxy i).symm))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.shared_path_marginal_limits_oai := @OAI.DirectionalTransience.shared_path_marginal_limits_oai
