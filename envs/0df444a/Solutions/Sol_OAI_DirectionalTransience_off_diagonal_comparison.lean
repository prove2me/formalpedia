-- Prove2me | solution 1 for OAI.DirectionalTransience.off_diagonal_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:04:13.13372+00:00
-- url     : https://prove2.me/submissions/e8cb08c2-4c1a-4e45-963d-e722aea0a932

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal004
import Definitions.Def_OAIQ242Bal007
import Theorems.Thm_OAI_DirectionalTransience_recordFluctuationScale_tendsto
import Theorems.Thm_OAI_DirectionalTransience_shared_endpoint_limits

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordDepartures
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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

lemma fresh_rows_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    {f g : Environment d → ℝ}
    (hf : @Measurable _ _ (rowSigma S) _ f)
    (hg : @Measurable _ _ (rowSigma T) _ g) :
    (∫ ω, f ω * g ω ∂environmentLaw ν) =
      (∫ ω, f ω ∂environmentLaw ν) * (∫ ω, g ω ∂environmentLaw ν) := by
  have hi : IndepFun f g (environmentLaw ν) := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    exact (Indep_iff _ _ _).mp (environment_indep_rows ν hST) _ _ (hf hs) (hg ht)
  exact hi.integral_fun_mul_eq_mul_integral
    (hf.mono (rowSigma_le S) le_rfl).aestronglyMeasurable
    (hg.mono (rowSigma_le T) le_rfl).aestronglyMeasurable

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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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

lemma integrable_of_nonneg_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ a, 0 ≤ f a ∧ f a ≤ B) : Integrable f μ := by
  exact (MemLp.of_bound (p := 1) hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hb a).1] using (hb a).2)).integrable le_rfl

lemma latticeBall_disjoint_of_coordinate_gap {d : ℕ} (i : Fin d)
    {x y : Lattice d} {n : ℕ} (hxy : (2 * n : ℤ) < |x i - y i|) :
    Disjoint (LatticeBall x n) (LatticeBall y n) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hx := hz i
  have hy := hz' i
  have hh := abs_add_le (x i - z i) (z i - y i)
  rw [sub_add_sub_cancel] at hh
  rw [abs_sub_comm (x i) (z i)] at hh
  omega

lemma noDropQuenched_toReal_le_one {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) : (noDropQuenched ℓ x ω).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono (show (1 : ℝ≥0∞) ≠ ∞ by simp)
    (show noDropQuenched ℓ x ω ≤ 1 from prob_le_one)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightSlab
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_FixedQuenchedKernel
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma annealedFrom_noDrop {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) :
    annealedFrom ν x (NoDrop ℓ x) = annealedLaw ν (NoDrop ℓ 0) := by
  rw [annealedFrom_apply ν x _ (measurableSet_noDrop ℓ x)]
  exact annealed_noDrop_translation ν ℓ x

lemma conditionedFrom_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    IsProbabilityMeasure (conditionedFrom ν ℓ x) := by
  constructor
  simp only [conditionedFrom, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul, annealedFrom_noDrop]
  exact ENNReal.inv_mul_cancel hp (measure_ne_top _ _)

lemma noDrop_real_integral_translation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x : Lattice d) :
    (∫ ω, (noDropQuenched ℓ x ω).toReal ∂environmentLaw ν) =
      ∫ ω, (noDropQuenched ℓ 0 ω).toReal ∂environmentLaw ν := by
  conv_lhs => enter [2, ω]; rw [noDropQuenched_translation ℓ ω x]
  have h := integral_map (μ := environmentLaw ν)
    (show AEMeasurable (fun ω : Environment d => fun a => ω (x + a)) (environmentLaw ν) from
      (by fun_prop : Measurable (fun ω : Environment d => fun a => ω (x + a))).aemeasurable)
    ((measurable_noDropQuenched ℓ 0).ennreal_toReal.aestronglyMeasurable)
  rw [environment_translation] at h
  exact h.symm

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonTrueRecord
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma noDropFinite_real_integral_translation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x : Lattice d) (n : ℕ) :
    (∫ ω, (noDropFinite ℓ x n ω).toReal ∂environmentLaw ν) =
      ∫ ω, (noDropFinite ℓ 0 n ω).toReal ∂environmentLaw ν := by
  conv_lhs => enter [2, ω]; rw [noDropFinite_translation ℓ ω x n]
  have h := integral_map (μ := environmentLaw ν)
    (show AEMeasurable (fun ω : Environment d => fun a => ω (x + a)) (environmentLaw ν) from
      (by fun_prop : Measurable (fun ω : Environment d => fun a => ω (x + a))).aemeasurable)
    ((noDropFinite_measurable ℓ 0 n).ennreal_toReal.aestronglyMeasurable)
  rw [environment_translation] at h
  exact h.symm

lemma noDropFinite_toReal_le_one {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (n : ℕ) (ω : Environment d) : (noDropFinite ℓ x n ω).toReal ≤ 1 := by
  exact (ENNReal.toReal_mono (by simp) (show noDropFinite ℓ x n ω ≤ 1 from prob_le_one)).trans
    (by simp)

lemma noDrop_real_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) :
    Integrable (fun ω => (noDropQuenched ℓ x ω).toReal) (environmentLaw ν) :=
  integrable_of_nonneg_bound _ (measurable_noDropQuenched ℓ x).ennreal_toReal
    (fun ω => ⟨ENNReal.toReal_nonneg, noDropQuenched_toReal_le_one ℓ x ω⟩)

lemma noDropFinite_real_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) (n : ℕ) :
    Integrable (fun ω => (noDropFinite ℓ x n ω).toReal) (environmentLaw ν) :=
  integrable_of_nonneg_bound _ (noDropFinite_measurable ℓ x n).ennreal_toReal
    (fun ω => ⟨ENNReal.toReal_nonneg, noDropFinite_toReal_le_one ℓ x n ω⟩)

lemma noDropFinite_real_integral_tendsto {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x : Lattice d) :
    Tendsto (fun n => ∫ ω, (noDropFinite ℓ x n ω).toReal ∂environmentLaw ν) atTop
      (𝓝 (∫ ω, (noDropQuenched ℓ x ω).toReal ∂environmentLaw ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro n
    exact (noDropFinite_measurable ℓ x n).ennreal_toReal.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact noDropFinite_toReal_le_one ℓ x n ω
  · exact Filter.Eventually.of_forall fun ω =>
      (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (noDropFinite_tendsto ℓ x ω)

lemma sharedNoDropMass_toReal {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) :
    (sharedNoDropMass ν ℓ x y).toReal =
      ∫ ω, (noDropQuenched ℓ x ω).toReal * (noDropQuenched ℓ y ω).toReal
        ∂environmentLaw ν := by
  have h := integral_toReal (μ := environmentLaw ν)
    (((measurable_noDropQuenched ℓ x).mul (measurable_noDropQuenched ℓ y)).aemeasurable)
    (Filter.Eventually.of_forall fun ω => ENNReal.mul_lt_top (measure_ne_top _ _).lt_top
      (measure_ne_top _ _).lt_top)
  simpa only [Pi.mul_apply, ENNReal.toReal_mul, sharedNoDropMass] using h.symm

lemma sharedNoDropMass_mixing {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x y : Lattice d, Disjoint (LatticeBall x n) (LatticeBall y n) →
      |(sharedNoDropMass ν ℓ x y).toReal -
        (annealedLaw ν (NoDrop ℓ 0)).toReal ^ 2| < ε := by
  let μ := environmentLaw ν
  let b := ∫ ω, (noDropQuenched ℓ 0 ω).toReal ∂μ
  let a := fun n => ∫ ω, (noDropFinite ℓ 0 n ω).toReal ∂μ
  have hb : 0 ≤ b ∧ b ≤ 1 := ⟨integral_nonneg fun _ => ENNReal.toReal_nonneg,
    (integral_mono (noDrop_real_integrable ν ℓ 0) (integrable_const (1 : ℝ))
      (fun ω => noDropQuenched_toReal_le_one ℓ 0 ω)).trans (by simp)⟩
  have ha n : 0 ≤ a n ∧ a n ≤ 1 := ⟨integral_nonneg fun _ => ENNReal.toReal_nonneg,
    (integral_mono (noDropFinite_real_integrable ν ℓ 0 n) (integrable_const (1 : ℝ))
      (fun ω => noDropFinite_toReal_le_one ℓ 0 n ω)).trans (by simp)⟩
  have hba n : b ≤ a n := integral_mono (noDrop_real_integrable ν ℓ 0)
    (noDropFinite_real_integrable ν ℓ 0 n) (fun ω =>
      ENNReal.toReal_mono (measure_ne_top _ _) (noDropQuenched_le_finite ℓ 0 ω n))
  have hlim : Tendsto (fun n => 2 * (a n - b)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [a, b, μ, sub_self, mul_zero] using
      ((noDropFinite_real_integral_tendsto ν ℓ 0).sub_const b).const_mul 2
  obtain ⟨n,hn⟩ := (hlim.eventually_lt_const hε).exists
  refine ⟨n, fun x y hxy => ?_⟩
  let f := fun z ω => (noDropFinite ℓ z n ω).toReal
  let g := fun z ω => (noDropQuenched ℓ z ω).toReal
  have hfi z : Integrable (f z) μ := noDropFinite_real_integrable ν ℓ z n
  have hgi z : Integrable (g z) μ := noDrop_real_integrable ν ℓ z
  have hfg z ω : g z ω ≤ f z ω :=
    ENNReal.toReal_mono (measure_ne_top _ _) (noDropQuenched_le_finite ℓ z ω n)
  have hf z ω : 0 ≤ f z ω ∧ f z ω ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, noDropFinite_toReal_le_one ℓ z n ω⟩
  have hg z ω : 0 ≤ g z ω ∧ g z ω ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, noDropQuenched_toReal_le_one ℓ z ω⟩
  have hfp : Integrable (fun ω => f x ω * f y ω) μ :=
    integrable_of_nonneg_bound _
      (((noDropFinite_measurable ℓ x n).ennreal_toReal).mul
        ((noDropFinite_measurable ℓ y n).ennreal_toReal))
      (fun ω => ⟨mul_nonneg (hf x ω).1 (hf y ω).1,
        by simpa only [one_mul] using mul_le_mul (hf x ω).2 (hf y ω).2 (hf y ω).1 zero_le_one⟩)
  have hgp : Integrable (fun ω => g x ω * g y ω) μ :=
    integrable_of_nonneg_bound _
      (((measurable_noDropQuenched ℓ x).ennreal_toReal).mul
        ((measurable_noDropQuenched ℓ y).ennreal_toReal))
      (fun ω => ⟨mul_nonneg (hg x ω).1 (hg y ω).1,
        by simpa only [one_mul] using mul_le_mul (hg x ω).2 (hg y ω).2 (hg y ω).1 zero_le_one⟩)
  have he : (∫ ω, f x ω * f y ω ∂μ) = a n ^ 2 := by
    rw [fresh_rows_factor ν hxy (noDropFinite_measurable_ball ℓ x n).ennreal_toReal
      (noDropFinite_measurable_ball ℓ y n).ennreal_toReal]
    rw [noDropFinite_real_integral_translation ν ℓ x,
      noDropFinite_real_integral_translation ν ℓ y]
    simp only [a,μ,pow_two]
  have hu := integral_mono hgp hfp (fun ω =>
    mul_le_mul (hfg x ω) (hfg y ω) (hg y ω).1 (hf x ω).1)
  have hl := integral_mono hfp (hgp.add (((hfi x).sub (hgi x)).add ((hfi y).sub (hgi y))))
    (fun ω => by
      change f x ω * f y ω ≤ g x ω * g y ω + (f x ω - g x ω + (f y ω - g y ω))
      nlinarith [(mul_nonneg (sub_nonneg.mpr (hfg x ω)) (sub_nonneg.mpr (hf y ω).2)),
        (mul_nonneg (sub_nonneg.mpr (hfg y ω)) (sub_nonneg.mpr (hg x ω).2))])
  have hix := integral_sub (hfi x) (hgi x)
  have hiy := integral_sub (hfi y) (hgi y)
  have hia := integral_add ((hfi x).sub (hgi x)) ((hfi y).sub (hgi y))
  have hio := integral_add hgp (((hfi x).sub (hgi x)).add ((hfi y).sub (hgi y)))
  simp only [Pi.add_apply, Pi.sub_apply] at hl hix hiy hia hio
  rw [hio, hia, hix, hiy, he] at hl
  simp only [f, g, μ, noDropFinite_real_integral_translation ν ℓ,
    noDrop_real_integral_translation ν ℓ] at hl
  change a n ^ 2 ≤ (∫ ω, g x ω * g y ω ∂μ) + (a n - b + (a n - b)) at hl
  rw [he] at hu
  have hbmass : b = (annealedLaw ν (NoDrop ℓ 0)).toReal := by
    rw [annealed_apply ν (measurableSet_noDrop ℓ 0)]
    exact integral_toReal (measurable_noDropQuenched ℓ 0).aemeasurable
      (Filter.Eventually.of_forall fun ω => (measure_ne_top _ _).lt_top)
  rw [sharedNoDropMass_toReal, ← hbmass, abs_lt]
  change -ε < (∫ ω, g x ω * g y ω ∂μ) - b ^ 2 ∧
    (∫ ω, g x ω * g y ω ∂μ) - b ^ 2 < ε
  have hpow : b ^ 2 ≤ a n ^ 2 := pow_le_pow_left₀ hb.1 (hba n) 2
  have hdiff : a n ^ 2 - b ^ 2 ≤ 2 * (a n - b) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hba n))
      (show 0 ≤ 2 - (a n + b) by linarith [(ha n).2,hb.2])]
  constructor <;> linarith

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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CrossTranslation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma annealedFrom_cross_error_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    annealedFrom ν x (Cross ℓ x H \ NoDrop ℓ x) =
      annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0) := by
  have hm := (measurableSet_cross ℓ 0 H).diff (measurableSet_noDrop ℓ 0)
  have hp : (fun X : Path d => fun n => X n-x) ⁻¹' (Cross ℓ 0 H \ NoDrop ℓ 0) =
      Cross ℓ x H \ NoDrop ℓ x := by
    rw [Set.preimage_sdiff,cross_translation,noDrop_translation]
    simp only [add_zero]
  rw [annealedFrom_apply ν x _ ((measurableSet_cross ℓ x H).diff (measurableSet_noDrop ℓ x)),← hp]
  exact annealed_event_translation ν x _ hm

lemma cross_error_tendsto_zero {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) :
    Tendsto (fun H : ℕ => annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0)) atTop (𝓝 0) := by
  have he : (⋂ H : ℕ, Cross ℓ 0 H \ NoDrop ℓ 0) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro X hX
    exact (Set.mem_iInter.mp hX 0).2 (iInter_cross_subset_noDrop ℓ 0
      (Set.mem_iInter.mpr fun H => (Set.mem_iInter.mp hX H).1))
  have hh := tendsto_measure_iInter_atTop (μ := annealedLaw ν)
    (s := fun H : ℕ => Cross ℓ 0 H \ NoDrop ℓ 0)
    (fun H => ((measurableSet_cross ℓ 0 H).diff (measurableSet_noDrop ℓ 0)).nullMeasurableSet)
    (fun H K h => Set.sdiff_subset_sdiff_left (cross_antitone ℓ 0 (Nat.cast_le.mpr h)))
    ⟨0,measure_ne_top _ _⟩
  simpa only [he,measure_empty,Function.comp_def] using hh

lemma pair_cross_noDrop_error_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (H : ℝ) (μ : Measure (Path d × Path d))
    (hx : μ.map Prod.fst = annealedFrom ν x) (hy : μ.map Prod.snd = annealedFrom ν y) :
    μ ((Cross ℓ x H ×ˢ Cross ℓ y H) \ (NoDrop ℓ x ×ˢ NoDrop ℓ y)) ≤
      2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0) := by
  have hm z := (measurableSet_cross ℓ z H).diff (measurableSet_noDrop ℓ z)
  calc
    _ ≤ μ (Prod.fst ⁻¹' (Cross ℓ x H \ NoDrop ℓ x)) +
        μ (Prod.snd ⁻¹' (Cross ℓ y H \ NoDrop ℓ y)) := by
      apply (measure_mono (s := _) (t := (Prod.fst ⁻¹' (Cross ℓ x H \ NoDrop ℓ x)) ∪
        (Prod.snd ⁻¹' (Cross ℓ y H \ NoDrop ℓ y))) ?_).trans (measure_union_le _ _)
      intro P hP
      by_cases hD : P.1 ∈ NoDrop ℓ x
      · exact Or.inr ⟨hP.1.2,fun h => hP.2 ⟨hD,h⟩⟩
      · exact Or.inl ⟨hP.1.1,hD⟩
    _ = annealedFrom ν x (Cross ℓ x H \ NoDrop ℓ x) +
        annealedFrom ν y (Cross ℓ y H \ NoDrop ℓ y) := by
      rw [← Measure.map_apply measurable_fst (hm x),← Measure.map_apply measurable_snd (hm y),hx,hy]
    _ = _ := by rw [annealedFrom_cross_error_translation,annealedFrom_cross_error_translation,two_mul]

lemma independent_cross_noDrop_error_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (H : ℝ) :
    ((annealedFrom ν x).prod (annealedFrom ν y))
      ((Cross ℓ x H ×ˢ Cross ℓ y H) \ (NoDrop ℓ x ×ˢ NoDrop ℓ y)) ≤
      2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0) := by
  apply pair_cross_noDrop_error_bound ν ℓ x y H
  · simp only [Measure.map_fst_prod,measure_univ,one_smul]
  · simp only [Measure.map_snd_prod,measure_univ,one_smul]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SurvivingLane
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
namespace DirectionalTransience

lemma measurableSet_survivingLane {d : ℕ} (U T A : Set (Lattice d)) :
    MeasurableSet (SurvivingLane U T A) :=
  (measurableSet_stay U).inter (measurableSet_hit _ _)

lemma future_stay_iff {d : ℕ} {U : Set (Lattice d)} {X : Path d} {n : ℕ}
    (hpre : ∀ j < n, X j ∈ U) :
    (fun j => X (n+j)) ∈ Stay U ↔ X ∈ Stay U := by
  constructor
  · intro h j
    by_cases hj : j < n
    · exact hpre j hj
    · have hh := h (j-n)
      simpa only [Nat.add_sub_of_le (by omega : n ≤ j)] using hh
  · intro h j
    exact h (n+j)

lemma future_hit_iff {d : ℕ} {S T A : Set (Lattice d)} (hST : Disjoint S T)
    {X : Path d} {n : ℕ} (hpre : ∀ j < n, X j ∈ S) :
    (fun j => X (n+j)) ∈ Hit S (T ∩ A) ↔ X ∈ Hit S (T ∩ A) := by
  constructor
  · intro h
    obtain ⟨m,hm⟩ := Set.mem_iUnion.mp h
    refine Set.mem_iUnion.mpr ⟨n+m,hm.1,?_⟩
    intro j hj
    by_cases hjn : j < n
    · exact hpre j hjn
    · have hh := hm.2 (j-n) (by omega)
      simpa only [Nat.add_sub_of_le (by omega : n ≤ j)] using hh
  · intro h
    obtain ⟨m,hm⟩ := Set.mem_iUnion.mp h
    have hnm : n ≤ m := by
      by_contra! h
      exact Set.disjoint_left.mp hST (hpre m h) hm.1.1
    refine Set.mem_iUnion.mpr ⟨m-n,?_,?_⟩
    · simpa only [Nat.add_sub_of_le hnm] using hm.1
    · intro j hj
      exact hm.2 (n+j) (by omega)

lemma hit_survival_factorization {d : ℕ} (ω : Environment d) (x : Lattice d)
    (U S V : Set (Lattice d)) (hS : S ⊆ U) :
    quenchedKernel (ω,x) (Hit (S \ V) V ∩ Stay U) =
      ∫⁻ z, quenchedKernel (ω,z) (Stay U) ∂hitKernel (S \ V) V (ω,x) := by
  rw [hitKernel_future ω x Set.disjoint_sdiff_left (fun _ => Stay U)
    (fun _ => measurableSet_stay U)]
  congr 1
  ext X
  simp only [Hit,Set.mem_inter_iff,Set.mem_iUnion]
  constructor
  · rintro ⟨⟨n,hn⟩,hD⟩
    exact ⟨n,hn,fun j => hD (n+j)⟩
  · rintro ⟨n,hn,hD⟩
    exact ⟨⟨n,hn⟩,(future_stay_iff (fun j hj => hS (hn.2 j hj).1)).mp hD⟩

lemma hit_laneError_factorization {d : ℕ} (ω : Environment d) (x : Lattice d)
    (U T A V : Set (Lattice d)) :
    quenchedKernel (ω,x) (Hit ((U \ T) \ V) V ∩ (Stay U \ SurvivingLane U T A)) =
      ∫⁻ z, quenchedKernel (ω,z) (Stay U \ SurvivingLane U T A)
        ∂hitKernel ((U \ T) \ V) V (ω,x) := by
  rw [hitKernel_future ω x Set.disjoint_sdiff_left (fun _ => Stay U \ SurvivingLane U T A)
    (fun _ => (measurableSet_stay U).diff (measurableSet_survivingLane U T A))]
  congr 1
  ext X
  have hh (n : ℕ) (hn : X ∈ HitAt ((U \ T) \ V) V n) :
      (fun j => X (n+j)) ∈ Stay U \ SurvivingLane U T A ↔ X ∈ Stay U \ SurvivingLane U T A := by
    have hd := future_stay_iff (fun j hj => (hn.2 j hj).1.1)
    have he := future_hit_iff (A := A) Set.disjoint_sdiff_left (fun j hj => (hn.2 j hj).1)
    change (_ ∧ ¬(_ ∧ _)) ↔ (_ ∧ ¬(_ ∧ _))
    rw [hd,he]
  simp only [Hit,Set.mem_inter_iff,Set.mem_iUnion]
  constructor
  · rintro ⟨⟨n,hn⟩,hD⟩
    exact ⟨n,hn,(hh n hn).mpr hD⟩
  · rintro ⟨n,hn,hD⟩
    exact ⟨⟨n,hn⟩,(hh n hn).mp hD⟩

lemma hitKernel_ae_target {d : ℕ} (S V : Set (Lattice d)) (z : State d) :
    ∀ᵐ y ∂hitKernel S V z, y ∈ V := by
  apply ae_iff.mpr
  rw [hitKernel_apply]
  have he : V ∩ {a | a ∉ V} = ∅ := by ext a; simp
  rw [he]
  simp only [HitAt,Set.mem_empty_iff_false,false_and,Set.ofPred_false,measure_empty,tsum_zero]

lemma quenched_lowLane_visit_bound {d : ℕ} (ω : Environment d) (x : Lattice d)
    (U T A V : Set (Lattice d))
    (hlow : ∀ z ∈ V, quenchedKernel (ω,z) (Stay U) ≤
      2 * quenchedKernel (ω,z) (Stay U \ SurvivingLane U T A)) :
    quenchedKernel (ω,x) (Hit ((U \ T) \ V) V ∩ Stay U) ≤
      2 * quenchedKernel (ω,x) (Stay U \ SurvivingLane U T A) := by
  rw [hit_survival_factorization ω x U (U \ T) V Set.sdiff_subset]
  calc
    _ ≤ ∫⁻ z, 2 * quenchedKernel (ω,z) (Stay U \ SurvivingLane U T A)
        ∂hitKernel ((U \ T) \ V) V (ω,x) := by
      apply lintegral_mono_ae
      filter_upwards [hitKernel_ae_target ((U \ T) \ V) V (ω,x)] with z hz
      exact hlow z hz
    _ = 2 * quenchedKernel (ω,x)
        (Hit ((U \ T) \ V) V ∩ (Stay U \ SurvivingLane U T A)) := by
      rw [lintegral_const_mul _ (measurable_of_countable _),hit_laneError_factorization]
    _ ≤ _ := mul_le_mul_right (measure_mono Set.inter_subset_right) 2

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma survivingLane_disjoint {d : ℕ} (U T A B : Set (Lattice d)) (hAB : Disjoint A B) :
    Disjoint (SurvivingLane U T A) (SurvivingLane U T B) := by
  apply Set.disjoint_left.mpr
  intro X hA hB
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hA.2
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hB.2
  have he : n = m := by
    by_contra h
    exact Set.disjoint_left.mp (hitAt_pairwise_disjoint (S := U \ T) (T := T)
      Set.disjoint_sdiff_left h) ⟨hn.1.1,hn.2⟩ ⟨hm.1.1,hm.2⟩
  subst m
  exact Set.disjoint_left.mp hAB hn.1.2 hm.1.2

lemma measure_low_complement_or {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D A B : Set Ω) (hAB : Disjoint A B) :
    μ D ≤ 2*μ (D \ A) ∨ μ D ≤ 2*μ (D \ B) := by
  have hh : μ D ≤ μ (D \ A)+μ (D \ B) := by
    apply (measure_mono (s := D) (t := (D \ A) ∪ (D \ B)) ?_).trans (measure_union_le _ _)
    intro x hx
    by_cases ha : x ∈ A
    · exact Or.inr ⟨hx,fun hb => Set.disjoint_left.mp hAB ha hb⟩
    · exact Or.inl ⟨hx,ha⟩
  rcases le_total (μ (D \ A)) (μ (D \ B)) with h | h
  · right
    exact (hh.trans (add_le_add h le_rfl)).trans_eq (two_mul _).symm
  · left
    exact (hh.trans (add_le_add le_rfl h)).trans_eq (two_mul _).symm

lemma measurableSet_prefixContact {d : ℕ} (S : Set (Lattice d)) :
    MeasurableSet (PrefixContact S) := by
  simp only [PrefixContact,Set.ofPred_exists,Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro m
  refine (measurableSet_eq_fun (by fun_prop) (by fun_prop)).inter ?_
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      ((measurable_pi_apply j).comp measurable_fst) S.to_countable.measurableSet
  · exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      ((measurable_pi_apply j).comp measurable_snd) S.to_countable.measurableSet

lemma prefix_visit_first {d : ℕ} (S V : Set (Lattice d)) (X : Path d)
    {n : ℕ} (hn : X n ∈ V) (hpre : ∀ j < n, X j ∈ S) :
    X ∈ Hit (S \ V) V := by
  classical
  let h : ∃ j, X j ∈ V := ⟨n,hn⟩
  let m := Nat.find h
  have hm : m ≤ n := Nat.find_min' h hn
  refine Set.mem_iUnion.mpr ⟨m,Nat.find_spec h,?_⟩
  intro j hj
  exact ⟨hpre j (hj.trans_le hm),Nat.find_min h hj⟩

lemma quenched_pair_contact_bound {d : ℕ} (ω : Environment d) (x y : Lattice d)
    (U T A B : Set (Lattice d)) (hAB : Disjoint A B) :
    ((quenchedKernel (ω,x)).prod (quenchedKernel (ω,y)))
      (PrefixContact (U \ T) ∩ (Stay U ×ˢ Stay U)) ≤
      2 * (quenchedKernel (ω,x) (Stay U \ SurvivingLane U T A) * quenchedKernel (ω,y) (Stay U) +
        quenchedKernel (ω,x) (Stay U) * quenchedKernel (ω,y) (Stay U \ SurvivingLane U T B)) := by
  let V := fun C : Set (Lattice d) => {z | quenchedKernel (ω,z) (Stay U) ≤
    2*quenchedKernel (ω,z) (Stay U \ SurvivingLane U T C)}
  let E := fun C : Set (Lattice d) => Hit ((U \ T) \ V C) (V C) ∩ Stay U
  have hlow : ∀ z, z ∈ V A ∨ z ∈ V B := fun z =>
    measure_low_complement_or _ _ _ _ (survivingLane_disjoint U T A B hAB)
  have hsub : PrefixContact (U \ T) ∩ (Stay U ×ˢ Stay U) ⊆
      (E A ×ˢ Stay U) ∪ (Stay U ×ˢ E B) := by
    intro Z hZ
    obtain ⟨n,m,he,hpre,hpre'⟩ := hZ.1
    rcases hlow (Z.1 n) with h | h
    · exact Or.inl ⟨⟨prefix_visit_first _ _ _ h hpre,hZ.2.1⟩,hZ.2.2⟩
    · rw [he] at h
      exact Or.inr ⟨hZ.2.1,⟨prefix_visit_first _ _ _ h hpre',hZ.2.2⟩⟩
  have hE (C : Set (Lattice d)) : MeasurableSet (E C) :=
    (measurableSet_hit _ _).inter (measurableSet_stay U)
  calc
    _ ≤ ((quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))) (E A ×ˢ Stay U) +
        ((quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))) (Stay U ×ˢ E B) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ = quenchedKernel (ω,x) (E A)*quenchedKernel (ω,y) (Stay U) +
        quenchedKernel (ω,x) (Stay U)*quenchedKernel (ω,y) (E B) := by
      rw [Measure.prod_prod,Measure.prod_prod]
    _ ≤ (2*quenchedKernel (ω,x) (Stay U \ SurvivingLane U T A))*quenchedKernel (ω,y) (Stay U) +
        quenchedKernel (ω,x) (Stay U)*(2*quenchedKernel (ω,y) (Stay U \ SurvivingLane U T B)) := by
      apply add_le_add
      · exact mul_le_mul_left (quenched_lowLane_visit_bound ω x U T A (V A) (fun _ hz => hz)) _
      · exact mul_le_mul_right (quenched_lowLane_visit_bound ω y U T B (V B) (fun _ hz => hz)) _
    _ = _ := by ring

lemma shared_pair_contact_bound {d : ℕ} (ν : Measure (Row d)) (x y : Lattice d)
    (U T A B : Set (Lattice d)) (hAB : Disjoint A B) :
    sharedPairLaw ν x y (PrefixContact (U \ T) ∩ (Stay U ×ˢ Stay U)) ≤
      2 * (sharedPairLaw ν x y ((Stay U \ SurvivingLane U T A) ×ˢ Stay U) +
        sharedPairLaw ν x y (Stay U ×ˢ (Stay U \ SurvivingLane U T B))) := by
  have hD := measurableSet_stay U
  have hA := hD.diff (measurableSet_survivingLane U T A)
  have hB := hD.diff (measurableSet_survivingLane U T B)
  conv_lhs => rw [sharedPairLaw,Measure.bind_apply ((measurableSet_prefixContact _).inter (hD.prod hD)) (Kernel.aemeasurable _)]
  rw [sharedPairLaw_rectangle ν x y _ _ hA hD,sharedPairLaw_rectangle ν x y _ _ hD hB]
  have hm (C D : Set (Path d)) (hC : MeasurableSet C) (hD : MeasurableSet D) :
      Measurable (fun ω : Environment d => quenchedKernel (ω,x) C * quenchedKernel (ω,y) D) :=
    ((Kernel.measurable_coe _ hC).comp (measurable_id.prodMk measurable_const)).mul
      ((Kernel.measurable_coe _ hD).comp (measurable_id.prodMk measurable_const))
  rw [← lintegral_add_left (hm _ _ hA hD)]
  rw [← lintegral_const_mul _ (show Measurable (fun ω : Environment d =>
    quenchedKernel (ω,x) (Stay U \ SurvivingLane U T A)*quenchedKernel (ω,y) (Stay U) +
    quenchedKernel (ω,x) (Stay U)*quenchedKernel (ω,y) (Stay U \ SurvivingLane U T B)) from
      (hm _ _ hA hD).add (hm _ _ hD hB))]
  apply lintegral_mono
  intro ω
  dsimp only
  rw [sharedPairKernel,Kernel.prod_apply]
  exact quenched_pair_contact_bound ω x y U T A B hAB

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentPairLaw
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstLayerHitRecordIndexTime
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma firstLayerHit_recordIndexTime {d : ℕ} (e : Direction d) (X : Path d)
    (h0 : X 0 = 0) (hD : X ∈ NoDrop (realPosition (step e)) 0)
    (hnn : ∀ n, ∃ f, X (n+1) = X n+step f) {k n : ℕ} (hk : 0 < k)
    (hX : X ∈ FirstLayerHit (signedHeight e) k n) :
    recordIndexTime (realPosition (step e)) k X = n := by
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
  apply recordIndexTime_eq ℓ k n X
  refine ⟨hn,hr,?_,fun j _ => hD j⟩
  rw [hX.1,h0,hz,zero_add] at hc
  exact_mod_cast hc.symm

lemma noDrop_firstLayerHit_exists {d : ℕ} (e : Direction d) (X : Path d)
    (h0 : X 0 = 0) (hnn : ∀ n, ∃ f, X (n+1) = X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e))) {k : ℕ} (hk : 0 < k) :
    ∃ n, X ∈ FirstLayerHit (signedHeight e) k n := by
  apply firstLayerHit_exists (signedHeight e) (signedHeight_step_le e) X hnn
  · simpa only [TransientPaths,Set.mem_ofPred_eq,signedHeight_projection] using ht
  · rw [h0]
    simp only [signedHeight,Pi.zero_apply,ite_self,neg_zero]
    exact_mod_cast hk

lemma survivingLane_record_iff {d : ℕ} (e : Direction d) (x : Lattice d)
    (X : Path d) (h0 : X 0 = x) (hD : X ∈ NoDrop (realPosition (step e)) x)
    (hnn : ∀ n, ∃ f, X (n+1) = X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e))) {k : ℕ} (hk : 0 < k)
    (A : Set (Lattice d)) :
    X ∈ SurvivingLane {z | dot (realPosition x) (realPosition (step e)) ≤
        dot (realPosition z) (realPosition (step e))} (Upper (realPosition (step e)) x k) A ↔
      recordIndexPosition (realPosition (step e)) k (fun j => X j-x)+x ∈ A := by
  let ℓ := realPosition (step e)
  let Y : Path d := fun j => X j-x
  have hy0 : Y 0 = 0 := by simp [Y,h0]
  have hyD : Y ∈ NoDrop ℓ 0 := by
    change X ∈ (fun Z : Path d => fun j => Z j-x) ⁻¹' NoDrop ℓ 0
    rw [noDrop_translation]
    simpa only [add_zero] using hD
  have hyn : ∀ n, ∃ f, Y (n+1) = Y n+step f := by
    intro n
    obtain ⟨f,hf⟩ := hnn n
    refine ⟨f,?_⟩
    simp only [Y,hf]
    abel
  have hyt : Y ∈ TransientPaths ℓ := by
    change Tendsto (fun n => dot (realPosition (X n-x)) ℓ) atTop atTop
    simp only [dot_realPosition_sub]
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-dot (realPosition x) ℓ) ht
  obtain ⟨n,hn⟩ := noDrop_firstLayerHit_exists e Y hy0 hyn hyt hk
  have hi := firstLayerHit_recordIndexTime e Y hy0 hyD hyn hk hn
  have he : recordIndexPosition ℓ k Y+x = X n := by
    change X (recordIndexTime (realPosition (step e)) k Y)-x+x = _
    rw [hi,sub_add_cancel]
  rw [he]
  have hend : dot (realPosition (X n)) ℓ = dot (realPosition x) ℓ+k := by
    have hh := congrArg (fun z : ℤ => (z : ℝ)) hn.1
    rw [← signedHeight_projection e] at hh
    change dot (realPosition (X n-x)) ℓ = (k : ℝ) at hh
    rw [dot_realPosition_sub] at hh
    linarith
  have hpre (j : ℕ) (hj : j < n) : dot (realPosition (X j)) ℓ < dot (realPosition x) ℓ+k := by
    have hh : (signedHeight e (Y j) : ℝ) < (k : ℝ) := by exact_mod_cast hn.2 j hj
    rw [← signedHeight_projection e] at hh
    change dot (realPosition (X j-x)) ℓ < _ at hh
    rw [dot_realPosition_sub] at hh
    linarith
  constructor
  · rintro ⟨_,hh⟩
    obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hh
    have hm' : m = n := by
      by_contra h
      rcases lt_or_gt_of_ne h with h | h
      · exact (not_lt_of_ge hm.1.1) (hpre m h)
      · exact (hm.2 n h).2 hend.ge
    simpa only [hm'] using hm.1.2
  · intro hA
    refine ⟨hD,Set.mem_iUnion.mpr ⟨n,⟨hend.ge,hA⟩,fun j hj => ?_⟩⟩
    exact ⟨hD j,not_le.mpr (hpre j hj)⟩

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_HitWord
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
namespace DirectionalTransience

lemma wordDepartures_subset_trace {d : ℕ} (x : Lattice d) (w : List (Direction d)) :
    (wordDepartures x w : Set (Lattice d)) ⊆ wordTrace x w := by
  intro z hz
  obtain ⟨j,hj,he⟩ := (wordDepartures_mem_iff x z w).mp hz
  exact ⟨j,hj.le,he.symm⟩

lemma hitWords_contact_iff {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (hST : Disjoint S T) (u : HitWord x S T) (v : HitWord y S T)
    {P : Path d × Path d} (hu : P.1 ∈ wordCylinder x u.val) (hv : P.2 ∈ wordCylinder y v.val) :
    P ∈ PrefixContact S ↔ ¬ Disjoint (wordTrace x u.val) (wordTrace y v.val) := by
  have h1 := hitWord_prefix x S T u hu
  have h2 := hitWord_prefix y S T v hv
  constructor
  · rintro ⟨n,m,he,hn,hm⟩ hdis
    have hn' : n ≤ u.val.length := by
      by_contra h
      exact Set.disjoint_left.mp hST (hn _ (by omega)) h1.1
    have hm' : m ≤ v.val.length := by
      by_contra h
      exact Set.disjoint_left.mp hST (hm _ (by omega)) h2.1
    exact Set.disjoint_left.mp hdis ⟨n,hn',(hu n hn').symm⟩
      ⟨m,hm',(hv m hm').symm.trans he.symm⟩
  · intro hdis
    obtain ⟨z,hz1,hz2⟩ := Set.not_disjoint_iff.mp hdis
    obtain ⟨n,hn,he⟩ := hz1
    obtain ⟨m,hm,hf⟩ := hz2
    exact ⟨n,m,(hu n hn).trans (he.trans (hf.symm.trans (hv m hm).symm)),
      fun j hj => h1.2 j (hj.trans_le hn),fun j hj => h2.2 j (hj.trans_le hm)⟩

lemma annealedFrom_wordCylinder {d : ℕ} (ν : Measure (Row d)) (x : Lattice d)
    (w : List (Direction d)) :
    annealedFrom ν x (wordCylinder x w) =
      ∫⁻ ω, ENNReal.ofReal (wordWeight ω x w) ∂environmentLaw ν := by
  rw [annealedFrom_apply ν x _ (measurableSet_wordCylinder x w)]
  exact lintegral_congr fun ω => quenched_wordCylinder ω x w

lemma disjoint_word_pair_weight {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x y : Lattice d) (u v : List (Direction d))
    (hdis : Disjoint (wordDepartures x u : Set (Lattice d)) (wordDepartures y v : Set (Lattice d))) :
    sharedPairLaw ν x y (wordCylinder x u ×ˢ wordCylinder y v) =
      ((annealedFrom ν x).prod (annealedFrom ν y)) (wordCylinder x u ×ˢ wordCylinder y v) := by
  rw [sharedPairLaw_rectangle ν x y _ _ (measurableSet_wordCylinder x u)
    (measurableSet_wordCylinder y v),Measure.prod_prod,annealedFrom_wordCylinder,
    annealedFrom_wordCylinder]
  simp_rw [quenched_wordCylinder]
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le _) (rowSigma_le _) (environment_indep_rows ν hdis)
    (measurable_wordWeight_on x u (fun _ hz => hz)).ennreal_ofReal
    (measurable_wordWeight_on y v (fun _ hz => hz)).ennreal_ofReal

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurableSet_hitWordsEvent {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (E : Set (HitWord x S T × HitWord y S T)) : MeasurableSet (hitWordsEvent x y S T E) := by
  apply MeasurableSet.iUnion
  intro w
  apply MeasurableSet.iUnion
  intro _
  exact (measurableSet_wordCylinder x w.1.val).prod (measurableSet_wordCylinder y w.2.val)

lemma hitWordsEvent_diff_contact {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (hST : Disjoint S T) (E : Set (HitWord x S T × HitWord y S T)) :
    hitWordsEvent x y S T E \ PrefixContact S =
      hitWordsEvent x y S T {w ∈ E | Disjoint (wordTrace x w.1.val) (wordTrace y w.2.val)} := by
  ext P
  constructor
  · rintro ⟨hP,hc⟩
    obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hP
    obtain ⟨he,hcy⟩ := Set.mem_iUnion.mp hw
    exact Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨⟨he,not_not.mp
      (fun h => hc ((hitWords_contact_iff x y S T hST w.1 w.2 hcy.1 hcy.2).mpr h))⟩,hcy⟩⟩
  · intro hP
    obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hP
    obtain ⟨he,hcy⟩ := Set.mem_iUnion.mp hw
    exact ⟨Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨he.1,hcy⟩⟩,
      fun hc => (hitWords_contact_iff x y S T hST w.1 w.2 hcy.1 hcy.2).mp hc he.2⟩

lemma hitWords_pair_cylinders_disjoint {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (hST : Disjoint S T) : Pairwise (fun u v : HitWord x S T × HitWord y S T =>
      Disjoint (wordCylinder x u.1.val ×ˢ wordCylinder y u.2.val)
        (wordCylinder x v.1.val ×ˢ wordCylinder y v.2.val)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro P hu hv
  by_cases he : u.1 = v.1
  · have he' : u.2 ≠ v.2 := fun h => huv (Prod.ext he h)
    exact Set.disjoint_left.mp (hitWord_cylinders_disjoint y S T hST he') hu.2 hv.2
  · exact Set.disjoint_left.mp (hitWord_cylinders_disjoint x S T hST he) hu.1 hv.1

lemma hitWordsEvent_measure {d : ℕ} (μ : Measure (Path d × Path d))
    (x y : Lattice d) (S T : Set (Lattice d)) (hST : Disjoint S T)
    (E : Set (HitWord x S T × HitWord y S T)) :
    μ (hitWordsEvent x y S T E) = ∑' w : E,
      μ (wordCylinder x w.val.1.val ×ˢ wordCylinder y w.val.2.val) := by
  have he : hitWordsEvent x y S T E = ⋃ w : E,
      wordCylinder x w.val.1.val ×ˢ wordCylinder y w.val.2.val := by
    ext P
    simp only [hitWordsEvent,Set.mem_iUnion,Subtype.exists]
  rw [he]
  apply measure_iUnion
  · intro u v huv
    exact hitWords_pair_cylinders_disjoint x y S T hST (fun he => huv (Subtype.ext he))
  · intro w
    exact (measurableSet_wordCylinder x w.val.1.val).prod (measurableSet_wordCylinder y w.val.2.val)

theorem raw_prefix_off_contact_equal {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x y : Lattice d) (S T : Set (Lattice d)) (hST : Disjoint S T)
    (E : Set (HitWord x S T × HitWord y S T)) :
    sharedPairLaw ν x y (hitWordsEvent x y S T E \ PrefixContact S) =
      ((annealedFrom ν x).prod (annealedFrom ν y)) (hitWordsEvent x y S T E \ PrefixContact S) := by
  rw [hitWordsEvent_diff_contact x y S T hST E,
    hitWordsEvent_measure _ x y S T hST,hitWordsEvent_measure _ x y S T hST]
  apply tsum_congr
  intro w
  apply disjoint_word_pair_weight
  exact w.property.2.mono (wordDepartures_subset_trace x w.val.1.val)
    (wordDepartures_subset_trace y w.val.2.val)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWidthProcess
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GaussianAbsTail
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
namespace DirectionalTransience

lemma gaussian_abs_tail (v : ℝ≥0) (hv : 0 < (v : ℝ)) (a : ℝ) (ha : 0 ≤ a) :
    (gaussianReal 0 v).real {z | a ≤ |z|} ≤ 2*Real.exp (-a^2/(2*v)) := by
  have hu := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) a
    (div_nonneg ha hv.le) (integrable_exp_mul_gaussianReal (a/v))
  have hl := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) (-a)
    (neg_nonpos.mpr (div_nonneg ha hv.le)) (integrable_exp_mul_gaussianReal (-(a/v)))
  rw [mgf_id_gaussianReal] at hu hl
  simp only [zero_mul,zero_add,← Real.exp_add] at hu hl
  have he1 : -(a/(v:ℝ))*a+v*(a/v)^2/2 = -a^2/(2*v) := by field_simp <;> ring
  have he2 : -(-(a/(v:ℝ)))*(-a)+v*(-(a/v))^2/2 = -a^2/(2*v) := by field_simp <;> ring
  rw [he1] at hu
  rw [he2] at hl
  have he : {z : ℝ | a ≤ |z|} = {z : ℝ | a ≤ z} ∪ {z : ℝ | z ≤ -a} := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_union,le_abs]
    exact or_congr Iff.rfl (by constructor <;> intro h <;> linarith)
  rw [he]
  exact (measureReal_union_le _ _).trans (by simpa only [id_eq,two_mul] using add_le_add hu hl)

lemma distribution_closed_limsup {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (F : ℕ → Ω → ℝ)
    (hF : ∀ i, Measurable (F i)) (η : Measure ℝ) [IsProbabilityMeasure η]
    (hlim : TendstoInDistribution F atTop id μ η) (A : Set ℝ) (hA : IsClosed A) :
    limsup (fun i => μ i (F i ⁻¹' A)) atTop ≤ η A := by
  let P : ℕ → ProbabilityMeasure ℝ := fun i => ⟨(μ i).map (F i),
    (Measure.isProbabilityMeasure_map_iff (hF i).aemeasurable).mpr inferInstance⟩
  have hp : Tendsto P atTop (𝓝 (⟨η,(by first | exact Measure.isProbabilityMeasure_map (by first | exact (hF i).aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure ℝ)) := by
    simpa only [Measure.map_id] using hlim.tendsto
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hp hA
  change limsup (fun i => ((μ i).map (F i)) A) atTop ≤ η A at hh
  simpa only [Measure.map_apply (hF _) hA.measurableSet] using hh

lemma distribution_abs_limsup {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (F : ℕ → Ω → ℝ)
    (hF : ∀ i, Measurable (F i)) (v : ℝ≥0) (hv : 0 < (v : ℝ))
    (hlim : TendstoInDistribution F atTop id μ (gaussianReal 0 v)) (a : ℝ) (ha : 0 ≤ a) :
    limsup (fun i => (μ i).real {ω | a ≤ |F i ω|}) atTop ≤ 2*Real.exp (-a^2/(2*v)) := by
  have hh := distribution_closed_limsup μ F hF (gaussianReal 0 v) hlim {z | a ≤ |z|}
    (isClosed_le continuous_const continuous_abs)
  have he : limsup (fun i => (μ i).real {ω | a ≤ |F i ω|}) atTop =
      (limsup (fun i => μ i {ω | a ≤ |F i ω|}) atTop).toReal := by
    exact ENNReal.limsup_toReal_eq (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      (Eventually.of_forall fun i => prob_le_one)
  rw [he]
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hh).trans (gaussian_abs_tail v hv a ha)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurable_scaledRecordEndpoint {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (k : ℕ) (x : Lattice d) : Measurable (scaledRecordEndpoint ℓ f θ r k x) := by
  unfold scaledRecordEndpoint
  exact ((((measurable_of_countable (signedCoordinate f)).comp
    (measurable_recordIndexPosition ℓ k)).comp (by fun_prop)).sub_const _).div_const _

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_NormalizedRestrictionContact
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
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
namespace DirectionalTransience

lemma normalized_restriction_contact_le {Ω : Type*} [MeasurableSpace Ω]
    (μ η : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (D C A R : Set Ω) (hC : MeasurableSet C)
    (hA : MeasurableSet A) (hAR : A ⊆ R) (c γ δ : ℝ≥0∞)
    (hc : 0 < c) (hcD : c ≤ μ D) (hη : η D ≤ μ D+γ)
    (hδ : η (R \ D) ≤ δ) (he : μ (A \ C) = η (A \ C)) :
    normalizedMeasure (μ.restrict D) A ≤ normalizedMeasure (η.restrict D) A +
      normalizedMeasure (μ.restrict D) C + c⁻¹*(γ+δ) := by
  have ha : μ D ≠ 0 := ne_of_gt (hc.trans_le hcD)
  have hfin : μ D ≠ ⊤ := measure_ne_top _ _
  have hmass : ∀ (ξ : Measure Ω), ξ.restrict D Set.univ = ξ D := by
    intro ξ
    rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
  have hraw : μ (A ∩ D) ≤ μ (C ∩ D) + η (A ∩ D) + δ := by
    calc
      _ ≤ μ (C ∩ D)+μ (A \ C) := by
        apply (measure_mono (s := A ∩ D) (t := (C ∩ D) ∪ (A \ C)) ?_).trans (measure_union_le _ _)
        intro z hz
        by_cases hzC : z ∈ C
        · exact Or.inl ⟨hzC,hz.2⟩
        · exact Or.inr ⟨hz.1,hzC⟩
      _ = μ (C ∩ D)+η (A \ C) := by rw [he]
      _ ≤ μ (C ∩ D)+(η (A ∩ D)+δ) := by
        apply add_le_add le_rfl
        calc
          _ ≤ η ((A ∩ D) ∪ (R \ D)) := by
            apply measure_mono
            intro z hz
            by_cases hzD : z ∈ D
            · exact Or.inl ⟨hz.1,hzD⟩
            · exact Or.inr ⟨hAR hz.1,hzD⟩
          _ ≤ η (A ∩ D)+η (R \ D) := measure_union_le _ _
          _ ≤ _ := add_le_add le_rfl hδ
      _ = _ := (add_assoc _ _ _).symm
  have hηA : (η.restrict D) A ≤ (μ D+γ)* normalizedMeasure (η.restrict D) A := by
    by_cases hz : η D = 0
    · have hzero : η (A ∩ D) = 0 := measure_mono_null Set.inter_subset_right hz
      rw [Measure.restrict_apply hA,hzero]
      exact zero_le
    · have heq : (η.restrict D) A = η D * normalizedMeasure (η.restrict D) A := by
        change _ = η D*((η.restrict D Set.univ)⁻¹*(η.restrict D) A)
        rw [hmass,← mul_assoc,ENNReal.mul_inv_cancel hz (measure_ne_top _ _),one_mul]
      rw [heq]
      exact mul_le_mul_left hη _
  have hprob : normalizedMeasure (η.restrict D) A ≤ 1 := by
    by_cases hz : η D = 0
    · change (η.restrict D Set.univ)⁻¹*(η.restrict D) A ≤ 1
      rw [hmass,Measure.restrict_apply hA,measure_mono_null Set.inter_subset_right hz]
      simp
    · let := normalizedMeasure_probability (η.restrict D) (by rw [hmass]; exact hz)
      exact prob_le_one
  have hmid : μ (A ∩ D) ≤ μ D * (normalizedMeasure (η.restrict D) A +
      normalizedMeasure (μ.restrict D) C) + (γ+δ) := by
    calc
      _ ≤ μ (C ∩ D) + (μ D+γ)*normalizedMeasure (η.restrict D) A + δ :=
        hraw.trans (add_le_add (add_le_add le_rfl (by simpa only [Measure.restrict_apply hA] using hηA)) le_rfl)
      _ ≤ μ (C ∩ D) + (μ D*normalizedMeasure (η.restrict D) A+γ) + δ := by
        rw [add_mul]
        exact add_le_add (add_le_add le_rfl (add_le_add le_rfl
          (by simpa only [mul_one] using mul_le_mul_right hprob γ))) le_rfl
      _ = _ := by
        have hCeq : μ D * normalizedMeasure (μ.restrict D) C = μ (C ∩ D) := by
          change μ D*((μ.restrict D Set.univ)⁻¹*(μ.restrict D) C) = _
          rw [hmass,← mul_assoc,ENNReal.mul_inv_cancel ha hfin,one_mul,Measure.restrict_apply hC]
        rw [mul_add,hCeq]
        ac_rfl
  change (μ.restrict D Set.univ)⁻¹*(μ.restrict D) A ≤ _
  rw [hmass,Measure.restrict_apply hA]
  calc
    _ ≤ (μ D)⁻¹*(μ D*(normalizedMeasure (η.restrict D) A+normalizedMeasure (μ.restrict D) C)+(γ+δ)) :=
      mul_le_mul_right hmid _
    _ = normalizedMeasure (η.restrict D) A + normalizedMeasure (μ.restrict D) C + (μ D)⁻¹*(γ+δ) := by
      rw [mul_add,← mul_assoc,ENNReal.inv_mul_cancel ha hfin,one_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_left (ENNReal.inv_le_inv.mpr hcD) _)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_NormalizedSharedRestrict
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
namespace DirectionalTransience

lemma normalized_shared_restrict {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) (x y : Lattice d) :
    normalizedMeasure ((sharedPairLaw ν x y).restrict (NoDrop ℓ x ×ˢ NoDrop ℓ y)) =
      sharedConditionedPairLaw ν ℓ x y := by
  unfold normalizedMeasure sharedConditionedPairLaw
  rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,← sharedNoDropMass_eq]

lemma normalized_independent_restrict {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) :
    normalizedMeasure (((annealedFrom ν x).prod (annealedFrom ν y)).restrict
      (NoDrop ℓ x ×ˢ NoDrop ℓ y)) = (conditionedFrom ν ℓ x).prod (conditionedFrom ν ℓ y) := by
  unfold normalizedMeasure conditionedFrom
  rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Measure.prod_prod,
    annealedFrom_noDrop,annealedFrom_noDrop,Measure.prod_smul_left,Measure.prod_smul_right,
    smul_smul,Measure.prod_restrict,ENNReal.mul_inv]
  · exact Or.inr (measure_ne_top _ _)
  · exact Or.inl (measure_ne_top _ _)

lemma hitWordsEvent_subset_hit {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (E : Set (HitWord x S T × HitWord y S T)) :
    hitWordsEvent x y S T E ⊆ Hit S T ×ˢ Hit S T := by
  intro P hP
  obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hP
  obtain ⟨_,hcy⟩ := Set.mem_iUnion.mp hw
  exact ⟨Set.mem_iUnion.mpr ⟨w.1.val.length,hitWord_prefix x S T w.1 hcy.1⟩,
    Set.mem_iUnion.mpr ⟨w.2.val.length,hitWord_prefix y S T w.2 hcy.2⟩⟩

theorem conditioned_prefix_comparison {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d)
    (hxy : dot (realPosition x) ℓ = dot (realPosition y) ℓ) (H : ℝ)
    (E : Set (HitWord x (Strip ℓ x H) (Upper ℓ x H) × HitWord y (Strip ℓ x H) (Upper ℓ x H))) :
    sharedConditionedPairLaw ν ℓ x y (hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) E) ≤
      ((conditionedFrom ν ℓ x).prod (conditionedFrom ν ℓ y))
        (hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) E) +
      sharedConditionedPairLaw ν ℓ x y (PrefixContact (Strip ℓ x H)) +
      (sharedNoDropMass ν ℓ x y)⁻¹ *
        ((annealedLaw ν (NoDrop ℓ 0))^2-sharedNoDropMass ν ℓ x y +
          2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0)) := by
  have hs : Strip ℓ x H = Strip ℓ y H := by unfold Strip; rw [hxy]
  have ht : Upper ℓ x H = Upper ℓ y H := by unfold Upper; rw [hxy]
  have hsub : hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) E ⊆ Cross ℓ x H ×ˢ Cross ℓ y H := by
    intro P hP
    have hh := hitWordsEvent_subset_hit x y _ _ E hP
    rw [cross_eq_hit,cross_eq_hit]
    exact ⟨hh.1,by simpa only [hs,ht] using hh.2⟩
  have hmass : ((annealedFrom ν x).prod (annealedFrom ν y)) (NoDrop ℓ x ×ˢ NoDrop ℓ y) =
      (annealedLaw ν (NoDrop ℓ 0))^2 := by
    rw [Measure.prod_prod,annealedFrom_noDrop,annealedFrom_noDrop,pow_two]
  have hh := normalized_restriction_contact_le (sharedPairLaw ν x y)
    ((annealedFrom ν x).prod (annealedFrom ν y))
    (NoDrop ℓ x ×ˢ NoDrop ℓ y) (PrefixContact (Strip ℓ x H))
    (hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) E) (Cross ℓ x H ×ˢ Cross ℓ y H)
    (measurableSet_prefixContact _) (measurableSet_hitWordsEvent _ _ _ _ _) hsub
    (sharedNoDropMass ν ℓ x y)
    ((annealedLaw ν (NoDrop ℓ 0))^2-sharedNoDropMass ν ℓ x y)
    (2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0))
    (sharedNoDropMass_pos ν hue ℓ hℓ htrans x y)
    (le_of_eq (sharedNoDropMass_eq ν ℓ x y))
    (by rw [hmass,← sharedNoDropMass_eq]; exact le_add_tsub)
    (independent_cross_noDrop_error_bound ν ℓ x y H)
    (raw_prefix_off_contact_equal ν x y _ _ (disjoint_strip_upper ℓ x H) E)
  simpa only [normalized_shared_restrict,normalized_independent_restrict] using hh

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_RegularPath
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma conditionedFrom_regularPath {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (x : Lattice d) :
    ∀ᵐ X ∂conditionedFrom ν ℓ x, X ∈ RegularPath ℓ x ∧ X ∈ NoDrop ℓ x := by
  have hac : conditionedFrom ν ℓ x ≪ annealedFrom ν x :=
    Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  have hD : ∀ᵐ X ∂conditionedFrom ν ℓ x, X ∈ NoDrop ℓ x := by
    exact Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem (measurableSet_noDrop ℓ x))
  have hR : ∀ᵐ X ∂conditionedFrom ν ℓ x, X ∈ RegularPath ℓ x :=
    hac.ae_le (annealedFrom_regularPath ν ℓ htrans x)
  exact hR.and hD

lemma open_lane_record_iff {d : ℕ} (e f : Direction d) (x : Lattice d) (X : Path d)
    (hX : X ∈ RegularPath (realPosition (step e)) x)
    (hD : X ∈ NoDrop (realPosition (step e)) x) {k : ℕ} (hk : 0 < k)
    (θ r a : ℝ) (hr : 0 < r) :
    X ∈ SurvivingLane {z | dot (realPosition x) (realPosition (step e)) ≤ dot (realPosition z) (realPosition (step e))}
      (Upper (realPosition (step e)) x k)
      {z | |signedCoordinate f z-(signedCoordinate f x+(k:ℝ)*θ)| < a*r} ↔
      |scaledRecordEndpoint (realPosition (step e)) f θ r k x X| < a := by
  rw [survivingLane_record_iff e x X hX.1 hD hX.2.1 hX.2.2 hk]
  change |signedCoordinate f (_+x)-(signedCoordinate f x+(k:ℝ)*θ)| < a*r ↔ _
  rw [signedCoordinate_add]
  have he (z : Lattice d) : signedCoordinate f z+signedCoordinate f x-(signedCoordinate f x+(k:ℝ)*θ) =
      signedCoordinate f z-(k:ℝ)*θ := by ring
  rw [he]
  simp only [scaledRecordEndpoint,abs_div,abs_of_pos hr]
  exact (div_lt_iff₀ hr).symm

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PrefixVariation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
namespace DirectionalTransience

lemma regularPath_cross {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    {X : Path d} (hX : X ∈ RegularPath ℓ x) (hD : X ∈ NoDrop ℓ x) : X ∈ Cross ℓ x H := by
  obtain ⟨n,hn⟩ := (hX.2.2.eventually_ge_atTop (dot (realPosition x) ℓ+H)).exists
  exact ⟨n,hn,fun j _ => hD j⟩

lemma hitWordsEvent_compl_on {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (hST : Disjoint S T) (E : Set (HitWord x S T × HitWord y S T))
    {Z : Path d × Path d} (hZ : Z ∈ hitWordsEvent x y S T Set.univ) :
    Z ∈ hitWordsEvent x y S T Eᶜ ↔ Z ∉ hitWordsEvent x y S T E := by
  obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hZ
  obtain ⟨_,hw⟩ := Set.mem_iUnion.mp hw
  have hu (v : HitWord x S T × HitWord y S T)
      (hv : Z ∈ wordCylinder x v.1.val ×ˢ wordCylinder y v.2.val) : v = w := by
    by_contra h
    exact Set.disjoint_left.mp (hitWords_pair_cylinders_disjoint x y S T hST h) hv hw
  constructor
  · intro hc he
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hc
    obtain ⟨hv,hcy⟩ := Set.mem_iUnion.mp hv
    obtain ⟨u,hu'⟩ := Set.mem_iUnion.mp he
    obtain ⟨hu',hcy'⟩ := Set.mem_iUnion.mp hu'
    rw [hu v hcy] at hv
    rw [hu u hcy'] at hu'
    exact hv hu'
  · intro hn
    refine Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨?_,hw⟩⟩
    exact fun h => hn (Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨h,hw⟩⟩)

lemma regularPath_hitWords_cover {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (hxy : dot (realPosition x) ℓ = dot (realPosition y) ℓ) (H : ℝ)
    {Z : Path d × Path d}
    (hZ : (Z.1 ∈ RegularPath ℓ x ∧ Z.1 ∈ NoDrop ℓ x) ∧
      (Z.2 ∈ RegularPath ℓ y ∧ Z.2 ∈ NoDrop ℓ y)) :
    Z ∈ hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) Set.univ := by
  have hx := regularPath_cross ℓ x H hZ.1.1 hZ.1.2
  have hy := regularPath_cross ℓ y H hZ.2.1 hZ.2.2
  rw [cross_eq_hit] at hx hy
  have hs : Strip ℓ y H = Strip ℓ x H := by unfold Strip; rw [hxy]
  have ht : Upper ℓ y H = Upper ℓ x H := by unfold Upper; rw [hxy]
  rw [hs,ht] at hy
  obtain ⟨u,hu⟩ := (hitWord_cover x _ _ Z.1 hZ.1.1.1 hZ.1.1.2.1).mp hx
  obtain ⟨v,hv⟩ := (hitWord_cover y _ _ Z.2 hZ.2.1.1 hZ.2.1.2.1).mp hy
  exact Set.mem_iUnion.mpr ⟨(u,v),Set.mem_iUnion.mpr ⟨Set.mem_univ _,hu,hv⟩⟩

lemma prefix_event_real_compl {d : ℕ} (μ : Measure (Path d × Path d)) [IsProbabilityMeasure μ]
    (x y : Lattice d) (S T : Set (Lattice d)) (hST : Disjoint S T)
    (hcover : ∀ᵐ Z ∂μ, Z ∈ hitWordsEvent x y S T Set.univ)
    (E : Set (HitWord x S T × HitWord y S T)) :
    μ.real (hitWordsEvent x y S T Eᶜ) = 1-μ.real (hitWordsEvent x y S T E) := by
  have he : μ (hitWordsEvent x y S T Eᶜ) = μ (hitWordsEvent x y S T E)ᶜ := by
    apply measure_congr
    filter_upwards [hcover] with Z hZ
    exact propext (hitWordsEvent_compl_on x y S T hST E hZ)
  change (μ _).toReal = _
  rw [he]
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using
    (measureReal_compl (μ := μ) (measurableSet_hitWordsEvent x y S T E))

lemma prefixVariation_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d)
    (hxy : dot (realPosition x) ℓ = dot (realPosition y) ℓ) (H : ℝ) :
    prefixVariation ν ℓ x y H ≤
      (sharedConditionedPairLaw ν ℓ x y).real (PrefixContact (Strip ℓ x H)) +
      ((sharedNoDropMass ν ℓ x y)⁻¹ *
        ((annealedLaw ν (NoDrop ℓ 0))^2-sharedNoDropMass ν ℓ x y +
          2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0))).toReal := by
  let μ := sharedConditionedPairLaw ν ℓ x y
  let η := (conditionedFrom ν ℓ x).prod (conditionedFrom ν ℓ y)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hp₂ := ne_of_gt (sharedNoDropMass_pos ν hue ℓ hℓ htrans x y)
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ x y hp₂
  let : IsProbabilityMeasure (conditionedFrom ν ℓ x) := conditionedFrom_probability ν ℓ x hp
  let : IsProbabilityMeasure (conditionedFrom ν ℓ y) := conditionedFrom_probability ν ℓ y hp
  have hc₁ : ∀ᵐ Z ∂μ, Z ∈ hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) Set.univ :=
    (sharedConditioned_regularPath ν ℓ htrans x y).mono fun _ h => regularPath_hitWords_cover ℓ x y hxy H h
  have hc₂ : ∀ᵐ Z ∂η, Z ∈ hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) Set.univ := by
    have hmeas : MeasurableSet {Z : Path d × Path d |
        (Z.1 ∈ RegularPath ℓ x ∧ Z.1 ∈ NoDrop ℓ x) ∧
        (Z.2 ∈ RegularPath ℓ y ∧ Z.2 ∈ NoDrop ℓ y)} :=
      ((measurableSet_regularPath ℓ x).inter (measurableSet_noDrop ℓ x)).prod
        ((measurableSet_regularPath ℓ y).inter (measurableSet_noDrop ℓ y))
    have hr := (Measure.ae_prod_iff_ae_ae hmeas).mpr (show ∀ᵐ X ∂conditionedFrom ν ℓ x,
      ∀ᵐ Y ∂conditionedFrom ν ℓ y, (X ∈ RegularPath ℓ x ∧ X ∈ NoDrop ℓ x) ∧
        (Y ∈ RegularPath ℓ y ∧ Y ∈ NoDrop ℓ y) from
      (conditionedFrom_regularPath ν ℓ htrans x).mono fun X hX =>
        (conditionedFrom_regularPath ν ℓ htrans y).mono fun Y hY => ⟨hX,hY⟩)
    exact hr.mono fun _ h => regularPath_hitWords_cover ℓ x y hxy H h
  let δ := (sharedNoDropMass ν ℓ x y)⁻¹ *
        ((annealedLaw ν (NoDrop ℓ 0))^2-sharedNoDropMass ν ℓ x y +
          2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0))
  have hδ : δ ≠ ∞ := by
    apply ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp₂)
    finiteness
  let F := hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H)
  have hb E : μ.real (F E) ≤ η.real (F E)+μ.real (PrefixContact (Strip ℓ x H))+δ.toReal := by
    have hh := conditioned_prefix_comparison ν hue ℓ hℓ htrans x y hxy H E
    have hh' := ENNReal.toReal_mono (show η (F E)+μ (PrefixContact (Strip ℓ x H))+δ ≠ ∞ by finiteness) hh
    simpa only [Measure.real,ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_add (by finiteness : η (F E)+μ (PrefixContact (Strip ℓ x H)) ≠ ∞) hδ] using hh'
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨E,rfl⟩
  have hb₁ := hb E
  have hb₂ := hb Eᶜ
  rw [prefix_event_real_compl μ x y _ _ (disjoint_strip_upper ℓ x H) hc₁,
    prefix_event_real_compl η x y _ _ (disjoint_strip_upper ℓ x H) hc₂] at hb₂
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma sharedNoDropMass_tendsto_gap {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (x y : ℕ → Lattice d)
    (hgap : Tendsto (fun i => |signedCoordinate f (y i-x i)|) atTop atTop) :
    Tendsto (fun i => (sharedNoDropMass ν ℓ (x i) (y i)).toReal) atTop
      (𝓝 ((annealedLaw ν (NoDrop ℓ 0)).toReal^2)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := sharedNoDropMass_mixing ν ℓ hε
  filter_upwards [hgap.eventually_gt_atTop (2*(N:ℝ))] with i hi
  rw [Real.dist_eq]
  apply hN
  apply latticeBall_disjoint_of_coordinate_gap f.1
  have he : |signedCoordinate f (y i-x i)| = (|(x i) f.1-(y i) f.1| : ℝ) := by
    simp only [signedCoordinate,Pi.sub_apply,apply_ite abs,abs_neg,ite_self,Int.cast_sub]
    exact abs_sub_comm _ _
  rw [he] at hi
  exact_mod_cast hi

lemma prefix_error_tendsto_zero {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (f : Direction d)
    (x y : ℕ → Lattice d) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (hgap : Tendsto (fun i => |signedCoordinate f (y i-x i)|) atTop atTop) :
    Tendsto (fun i => ((sharedNoDropMass ν ℓ (x i) (y i))⁻¹ *
      ((annealedLaw ν (NoDrop ℓ 0))^2-sharedNoDropMass ν ℓ (x i) (y i) +
        2*annealedLaw ν (Cross ℓ 0 (H i) \ NoDrop ℓ 0))).toReal) atTop (𝓝 0) := by
  let p := annealedLaw ν (NoDrop ℓ 0)
  let q := fun i => sharedNoDropMass ν ℓ (x i) (y i)
  have hp : p ≠ 0 := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hpfin : p^2 ≠ ∞ := by finiteness
  have hqfin (i : ℕ) : q i ≠ ∞ := ne_of_lt ((sharedNoDropMass_le_one ν ℓ (x i) (y i)).trans_lt (by simp))
  have hq : Tendsto q atTop (𝓝 (p^2)) := (ENNReal.tendsto_toReal_iff hqfin hpfin).mp (by
    simpa only [ENNReal.toReal_pow] using sharedNoDropMass_tendsto_gap ν ℓ f x y hgap)
  have hdiff : Tendsto (fun i => p^2-q i) atTop (𝓝 0) := by
    simpa only [tsub_self,Function.comp_def] using (ENNReal.tendsto_sub (Or.inl hpfin)).comp
      (tendsto_const_nhds.prodMk_nhds hq)
  have herr : Tendsto (fun i => 2*annealedLaw ν (Cross ℓ 0 (H i) \ NoDrop ℓ 0)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using ENNReal.Tendsto.const_mul ((cross_error_tendsto_zero ν ℓ).comp hH)
      (Or.inr (by norm_num : (2:ℝ≥0∞) ≠ ∞))
  have hinv : Tendsto (fun i => (q i)⁻¹) atTop (𝓝 (p^2)⁻¹) := tendsto_inv_iff.mpr hq
  have hsum := hdiff.add herr
  rw [zero_add] at hsum
  have hprod := ENNReal.Tendsto.mul hinv (Or.inr ENNReal.zero_ne_top) hsum
    (Or.inr (ENNReal.inv_ne_top.mpr (pow_ne_zero _ hp)))
  rw [mul_zero] at hprod
  simpa only [ENNReal.toReal_zero,Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hprod

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SharedConditionedContactBound
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
namespace DirectionalTransience

theorem shared_conditioned_contact_bound {d : ℕ} (ν : Measure (Row d))
    (ℓ : Vector d) (x y : Lattice d) (hxy : dot (realPosition x) ℓ = dot (realPosition y) ℓ)
    (T A B : Set (Lattice d)) (hAB : Disjoint A B) :
    let U := {z | dot (realPosition x) ℓ ≤ dot (realPosition z) ℓ}
    sharedConditionedPairLaw ν ℓ x y (PrefixContact (U \ T)) ≤
      2 * (sharedConditionedPairLaw ν ℓ x y (Prod.fst ⁻¹' (SurvivingLane U T A)ᶜ) +
        sharedConditionedPairLaw ν ℓ x y (Prod.snd ⁻¹' (SurvivingLane U T B)ᶜ)) := by
  let U := {z | dot (realPosition x) ℓ ≤ dot (realPosition z) ℓ}
  have hx : NoDrop ℓ x = Stay U := rfl
  have hy : NoDrop ℓ y = Stay U := by unfold NoDrop Stay U; rw [← hxy]; rfl
  have hA := measurableSet_survivingLane U T A
  have hB := measurableSet_survivingLane U T B
  change _ ≤ 2*(_+_)
  rw [sharedConditionedPairLaw,Measure.smul_apply,Measure.restrict_apply (measurableSet_prefixContact _)]
  rw [Measure.smul_apply,Measure.restrict_apply (hA.compl.preimage measurable_fst),
    Measure.smul_apply,Measure.restrict_apply (hB.compl.preimage measurable_snd),hx,hy]
  have heA : Prod.fst ⁻¹' (SurvivingLane U T A)ᶜ ∩ (Stay U ×ˢ Stay U) =
      (Stay U \ SurvivingLane U T A) ×ˢ Stay U := by ext Z; change (¬_ ∧ _ ∧ _) ↔ ((_ ∧ ¬_) ∧ _); tauto
  have heB : Prod.snd ⁻¹' (SurvivingLane U T B)ᶜ ∩ (Stay U ×ˢ Stay U) =
      Stay U ×ˢ (Stay U \ SurvivingLane U T B) := by ext Z; change (¬_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ ¬_); tauto
  rw [heA,heB]
  simp only [smul_eq_mul]
  calc
    _ ≤ (sharedNoDropMass ν ℓ x y)⁻¹ * (2*(sharedPairLaw ν x y
        ((Stay U \ SurvivingLane U T A) ×ˢ Stay U) + sharedPairLaw ν x y
        (Stay U ×ˢ (Stay U \ SurvivingLane U T B)))) :=
      mul_le_mul_right (shared_pair_contact_bound ν x y U T A B hAB) _
    _ = _ := by ring

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_CoordinateLanesDisjoint
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
namespace DirectionalTransience

lemma coordinate_lanes_disjoint {d : ℕ} (f : Direction d) (x y : Lattice d)
    (c R : ℝ) (hR : 0 < R) (hxy : R ≤ |signedCoordinate f (y-x)|) :
    Disjoint {z | |signedCoordinate f z-(signedCoordinate f x+c)| < R/3}
      {z | |signedCoordinate f z-(signedCoordinate f y+c)| < R/3} := by
  apply Set.disjoint_left.mpr
  intro z hx hy
  change |signedCoordinate f z-(signedCoordinate f x+c)| < R/3 at hx
  change |signedCoordinate f z-(signedCoordinate f y+c)| < R/3 at hy
  have he : signedCoordinate f (y-x) =
      (signedCoordinate f z-(signedCoordinate f x+c))-(signedCoordinate f z-(signedCoordinate f y+c)) := by
    rw [signedCoordinate_sub]
    ring
  have hh := abs_sub (signedCoordinate f z-(signedCoordinate f x+c))
    (signedCoordinate f z-(signedCoordinate f y+c))
  rw [← he] at hh
  have hlt := add_lt_add hx hy
  have h := hxy.trans hh
  linarith

lemma shared_contact_endpoint_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (x y : Lattice d) (hxy : signedHeight e x = signedHeight e y)
    {k : ℕ} (hk : 0 < k) (θ : ℝ) {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hsep : a*r ≤ |signedCoordinate f (y-x)|) :
    let ℓ := realPosition (step e)
    let μ := sharedConditionedPairLaw ν ℓ x y
    μ.real (PrefixContact (Strip ℓ x k)) ≤ 2*(
      μ.real {Z | a/3 ≤ |scaledRecordEndpoint ℓ f θ r k x Z.1|}+
      μ.real {Z | a/3 ≤ |scaledRecordEndpoint ℓ f θ r k y Z.2|}) := by
  let ℓ := realPosition (step e)
  let μ := sharedConditionedPairLaw ν ℓ x y
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ x y
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans x y))
  let U := {z | dot (realPosition x) ℓ ≤ dot (realPosition z) ℓ}
  let T := Upper ℓ x k
  let A := {z | |signedCoordinate f z-(signedCoordinate f x+(k:ℝ)*θ)| < (a/3)*r}
  let B := {z | |signedCoordinate f z-(signedCoordinate f y+(k:ℝ)*θ)| < (a/3)*r}
  have hp : dot (realPosition x) ℓ = dot (realPosition y) ℓ := by
    simp only [ℓ,signedHeight_projection,hxy]
  have hAB : Disjoint A B := by
    have hh := coordinate_lanes_disjoint f x y ((k:ℝ)*θ) (a*r) (mul_pos ha hr) hsep
    have he : a / 3 * r = a * r / 3 := by ring
    simpa only [A,B,he] using hh
  have hS : U \ T = Strip ℓ x k := by
    ext z
    change (dot (realPosition x) ℓ ≤ dot (realPosition z) ℓ ∧
      ¬ dot (realPosition x) ℓ + (k:ℝ) ≤ dot (realPosition z) ℓ) ↔
      (dot (realPosition x) ℓ ≤ dot (realPosition z) ℓ ∧
      dot (realPosition z) ℓ < dot (realPosition x) ℓ + (k:ℝ))
    exact and_congr_right fun _ => not_le
  have he₁ : μ (Prod.fst ⁻¹' (SurvivingLane U T A)ᶜ) =
      μ {Z | a/3 ≤ |scaledRecordEndpoint ℓ f θ r k x Z.1|} := by
    apply measure_congr
    filter_upwards [sharedConditioned_regularPath ν ℓ htrans x y] with Z hZ
    apply propext
    exact not_congr (open_lane_record_iff e f x Z.1 hZ.1.1 hZ.1.2 hk θ r (a/3) hr) |>.trans not_lt
  have he₂ : μ (Prod.snd ⁻¹' (SurvivingLane U T B)ᶜ) =
      μ {Z | a/3 ≤ |scaledRecordEndpoint ℓ f θ r k y Z.2|} := by
    apply measure_congr
    filter_upwards [sharedConditioned_regularPath ν ℓ htrans x y] with Z hZ
    have hU : U = {z | dot (realPosition y) ℓ ≤ dot (realPosition z) ℓ} := by unfold U; rw [hp]
    have hT : T = Upper ℓ y k := by unfold T Upper; rw [hp]
    apply propext
    change (Z.2 ∉ SurvivingLane U T B) ↔ _
    rw [hU,hT]
    exact not_congr (open_lane_record_iff e f y Z.2 hZ.2.1 hZ.2.2 hk θ r (a/3) hr) |>.trans not_lt
  have hb := shared_conditioned_contact_bound ν ℓ x y hp T A B hAB
  change μ (PrefixContact (U \ T)) ≤ 2*(_+_) at hb
  rw [hS,he₁,he₂] at hb
  have hh := ENNReal.toReal_mono (show 2*(μ _+μ _) ≠ ∞ by finiteness) hb
  simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_ofNat,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] using hh

theorem shared_contact_limsup {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i))
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hsep : ∀ i, a*r i ≤ |signedCoordinate f (y i-x i)|) :
    let ℓ := realPosition (step e)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    limsup (fun i => (sharedConditionedPairLaw ν ℓ (x i) (y i)).real
      (PrefixContact (Strip ℓ (x i) (⌊t*n i⌋₊ : ℝ)))) atTop ≤
      8*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t)) := by
  let ℓ := realPosition (step e)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)) f (r i)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
  let F := fun i (Z : Path d × Path d) => scaledRecordEndpoint ℓ f (θ i) (r i) ⌊t*n i⌋₊ (x i) Z.1
  let G := fun i (Z : Path d × Path d) => scaledRecordEndpoint ℓ f (θ i) (r i) ⌊t*n i⌋₊ (y i) Z.2
  have hF (i : ℕ) : Measurable (F i) := (measurable_scaledRecordEndpoint _ _ _ _ _ _).comp measurable_fst
  have hG (i : ℕ) : Measurable (G i) := (measurable_scaledRecordEndpoint _ _ _ _ _ _).comp measurable_snd
  let p := fun i => (μ i).real {Z | a/3 ≤ |F i Z|}
  let q := fun i => (μ i).real {Z | a/3 ≤ |G i Z|}
  let c := fun i => (μ i).real (PrefixContact (Strip ℓ (x i) (⌊t*n i⌋₊ : ℝ)))
  have hM : 0 < commonMeanWidth ν ℓ := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    (commonMeanWidth_ge_one ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e))
  have hv : 0 < t/(2*commonMeanWidth ν ℓ) := div_pos ht (mul_pos (by norm_num) hM)
  have hh := shared_endpoint_limits ν hue e f hef htrans r hrpos hr x y hxy ht
  have hcoe : ((t/(2*commonMeanWidth ν (realPosition (step e)))).toNNReal : ℝ) =
      t/(2*commonMeanWidth ν ℓ) := Real.coe_toNNReal _ hv.le
  let R := 2*Real.exp (-(a/3)^2/(2*(t/(2*commonMeanWidth ν ℓ))))
  have hp : limsup p atTop ≤ R := by
    have hh' := distribution_abs_limsup μ F hF _ (by simpa only [hcoe] using hv)
      hh.1 (a/3) (by positivity)
    simpa only [hcoe] using hh'
  have hq : limsup q atTop ≤ R := by
    have hh' := distribution_abs_limsup μ G hG _ (by simpa only [hcoe] using hv)
      hh.2 (a/3) (by positivity)
    simpa only [hcoe] using hh'
  have hn := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  have hk : ∀ᶠ i in atTop, 0 < ⌊t*n i⌋₊ := by
    have hn' : Tendsto (fun i => t*n i) atTop atTop := hn.const_mul_atTop ht
    filter_upwards [hn'.eventually_ge_atTop 1] with i hi
    exact Nat.floor_pos.mpr hi
  have hb : ∀ᶠ i in atTop, c i ≤ 2*(p i+q i) := hk.mono fun i hi =>
    shared_contact_endpoint_bound ν hue e f htrans (x i) (y i) (hxy i) hi (θ i) (hrpos i) ha (hsep i)
  have hb₁ : IsBoundedUnder (· ≤ ·) atTop p := by
    refine ⟨1, ?_⟩
    change ∀ᶠ i in atTop, _ ≤ (1:ℝ)
    exact Eventually.of_forall fun i => measureReal_le_one
  have hb₂ : IsBoundedUnder (· ≤ ·) atTop q := by
    refine ⟨1, ?_⟩
    change ∀ᶠ i in atTop, _ ≤ (1:ℝ)
    exact Eventually.of_forall fun i => measureReal_le_one
  have hc₁ : IsCoboundedUnder (· ≤ ·) atTop c :=
    (show IsBoundedUnder (· ≥ ·) atTop c from ⟨0,
      (show ∀ᶠ i in atTop, 0 ≤ c i from Eventually.of_forall fun i => measureReal_nonneg)⟩).isCoboundedUnder_le
  have hc₂ : IsBoundedUnder (· ≤ ·) atTop c := by
    refine ⟨1, ?_⟩
    change ∀ᶠ i in atTop, _ ≤ (1:ℝ)
    exact Eventually.of_forall fun i => measureReal_le_one
  have hc : limsup c atTop ≤ 4*R := (limsup_le_iff hc₁ hc₂).mpr (by
    intro b hb'
    have hp' := eventually_lt_of_limsup_lt (hp.trans_lt (show R < R+(b-4*R)/8 by linarith)) hb₁
    have hq' := eventually_lt_of_limsup_lt (hq.trans_lt (show R < R+(b-4*R)/8 by linarith)) hb₂
    filter_upwards [hb,hp',hq'] with i hi hp' hq'
    linarith)
  have he : -(a/3)^2/(2*(t/(2*commonMeanWidth ν ℓ))) = -commonMeanWidth ν ℓ*a^2/(9*t) := by
    field_simp
    ring
  simpa only [R,he,← mul_assoc,show (4:ℝ)*2=8 by norm_num] using hc

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PrefixVariationNonneg
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
namespace DirectionalTransience

lemma prefixVariation_nonneg {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x y : Lattice d) (H : ℝ) : 0 ≤ prefixVariation ν ℓ x y H := by
  apply Real.sSup_nonneg
  rintro _ ⟨E,rfl⟩
  exact abs_nonneg _

theorem off_diagonal_comparison_oai {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0 < r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i))
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hsep : ∀ i, a*r i ≤ |signedCoordinate f (y i-x i)|) :
    let ℓ := realPosition (step e)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    limsup (fun i => prefixVariation ν ℓ (x i) (y i) (⌊t*n i⌋₊ : ℝ)) atTop ≤
      8*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t)) := by
  let ℓ := realPosition (step e)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let H := fun i => ⌊t*n i⌋₊
  let v := fun i => prefixVariation ν ℓ (x i) (y i) (H i)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
  let c := fun i => (μ i).real (PrefixContact (Strip ℓ (x i) (H i)))
  let δ := fun i => ((sharedNoDropMass ν ℓ (x i) (y i))⁻¹ *
      ((annealedLaw ν (NoDrop ℓ 0))^2-sharedNoDropMass ν ℓ (x i) (y i) +
        2*annealedLaw ν (Cross ℓ 0 (H i) \ NoDrop ℓ 0))).toReal
  let R := 8*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t))
  have hgap : Tendsto (fun i => |signedCoordinate f (y i-x i)|) atTop atTop :=
    tendsto_atTop_mono hsep (hr.1.const_mul_atTop ha)
  have hn := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  have hH : Tendsto H atTop atTop := tendsto_nat_floor_atTop.comp (hn.const_mul_atTop ht)
  have hδ : Tendsto δ atTop (𝓝 0) := prefix_error_tendsto_zero ν ℓ htrans f x y H hH hgap
  have hb (i : ℕ) : v i ≤ c i+δ i := prefixVariation_bound ν hue ℓ (signed_direction_unit e)
    htrans (x i) (y i) (by simp only [ℓ,signedHeight_projection,hxy i]) (H i)
  have hc : limsup c atTop ≤ R := shared_contact_limsup ν hue e f hef htrans r hrpos hr x y hxy ha ht hsep
  have hcb : IsBoundedUnder (· ≤ ·) atTop c := by
    refine ⟨1, ?_⟩
    change ∀ᶠ i in atTop, c i ≤ 1
    exact Eventually.of_forall fun i => measureReal_le_one
  have hvb : IsBoundedUnder (· ≤ ·) atTop v := by
    refine ⟨2, ?_⟩
    change ∀ᶠ i in atTop, v i ≤ 2
    filter_upwards [hδ.eventually_lt_const (by norm_num : (0:ℝ)<1)] with i hi
    have hh : c i ≤ 1 := measureReal_le_one
    linarith [hb i]
  have hvc : IsCoboundedUnder (· ≤ ·) atTop v :=
    (show IsBoundedUnder (· ≥ ·) atTop v from ⟨0,
      (show ∀ᶠ i in atTop, 0 ≤ v i from Eventually.of_forall fun i => prefixVariation_nonneg ν ℓ (x i) (y i) (H i))⟩).isCoboundedUnder_le
  apply (limsup_le_iff hvc hvb).mpr
  intro b hb'
  have hc' := eventually_lt_of_limsup_lt (hc.trans_lt (show R < R+(b-R)/3 by linarith)) hcb
  have hδ' := hδ.eventually_lt_const (show (0:ℝ)<(b-R)/3 by linarith)
  filter_upwards [hc',hδ'] with i hi hi'
  linarith [hb i]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.off_diagonal_comparison_oai := @OAI.DirectionalTransience.off_diagonal_comparison_oai
