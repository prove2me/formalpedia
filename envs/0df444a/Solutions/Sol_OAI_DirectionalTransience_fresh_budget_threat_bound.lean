-- Prove2me | solution 1 for OAI.DirectionalTransience.fresh_budget_threat_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:53:46.341219+00:00
-- url     : https://prove2.me/submissions/4f301bf2-ad62-464e-af44-d9fd832a22be

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Definitions.Def_OAIQ242Bal006

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

lemma clippedInverse_measurable (δ lam : ℝ) : Measurable (clippedInverse δ lam) :=
  (measurable_id.ennreal_toReal.max measurable_const).pow_const _

lemma clippedInverse_bounds (lam : ℝ) {δ : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam)
    (q : ℝ≥0∞) : 0 ≤ clippedInverse δ lam q ∧ clippedInverse δ lam q ≤ δ ^ (-lam) := by
  exact ⟨Real.rpow_nonneg (hδ.le.trans (le_max_right _ _)) _,
    Real.rpow_le_rpow_of_nonpos hδ (le_max_right _ _) (neg_nonpos.mpr hlam)⟩

lemma clippedInverse_antitone {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam)
    {q r : ℝ≥0∞} (hr : r ≠ ∞) (hqr : q ≤ r) :
    clippedInverse δ lam r ≤ clippedInverse δ lam q := by
  apply Real.rpow_le_rpow_of_nonpos (hδ.trans_le (le_max_right _ _))
    (max_le_max (ENNReal.toReal_mono hr hqr) le_rfl) (neg_nonpos.mpr hlam)

lemma clippedInverse_tendsto {α : Type*} {l : Filter α} {f : α → ℝ≥0∞}
    {q : ℝ≥0∞} (hq : q ≠ ∞) {δ : ℝ} (hδ : 0 < δ) (lam : ℝ)
    (hf : Tendsto f l (𝓝 q)) :
    Tendsto (fun a => clippedInverse δ lam (f a)) l (𝓝 (clippedInverse δ lam q)) :=
  (((ENNReal.tendsto_toReal hq).comp hf).max tendsto_const_nhds).rpow_const
    (Or.inl (ne_of_gt (hδ.trans_le (le_max_right _ _))))

lemma noDrop_clipped_inverse_L1 {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam) :
    Tendsto (fun n => ∫ ω, |clippedInverse δ lam (noDropQuenched ℓ x ω) -
      clippedInverse δ lam (noDropFinite ℓ x n ω)| ∂environmentLaw ν) atTop (𝓝 0) := by
  have hm (n : ℕ) := ((clippedInverse_measurable δ lam).comp (measurable_noDropQuenched ℓ x)).sub
    ((clippedInverse_measurable δ lam).comp (noDropFinite_measurable ℓ x n))
  have ht := tendsto_integral_of_dominated_convergence
    (μ := environmentLaw ν) (f := fun _ => (0 : ℝ))
    (fun _ => δ ^ (-lam)) (fun n => (hm n).abs.aestronglyMeasurable)
    (integrable_const _) (fun n => ?_) (Filter.Eventually.of_forall fun ω => ?_)
  · simpa using ht
  · exact Filter.Eventually.of_forall fun ω => by
      have hq := clippedInverse_bounds lam hδ hlam (noDropQuenched ℓ x ω)
      have hn := clippedInverse_bounds lam hδ hlam (noDropFinite ℓ x n ω)
      have hle := clippedInverse_antitone hδ hlam (measure_ne_top _ _)
        (noDropQuenched_le_finite ℓ x ω n)
      change clippedInverse δ lam (noDropFinite ℓ x n ω) ≤
        clippedInverse δ lam (noDropQuenched ℓ x ω) at hle
      simp only [Real.norm_eq_abs, abs_abs, Pi.sub_apply, Function.comp_apply]
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      linarith
  · have h := clippedInverse_tendsto (measure_ne_top _ _) hδ lam (noDropFinite_tendsto ℓ x ω)
    simpa only [noDropQuenched, sub_self, abs_zero, Pi.sub_apply, Function.comp_apply] using
      ((tendsto_const_nhds (x := clippedInverse δ lam (noDropQuenched ℓ x ω))).sub h).abs

lemma fresh_rows_prod {d : ℕ} {ι : Type*} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (s : Finset ι) (S : ι → Set (Lattice d)) (f : ι → Environment d → ℝ)
    (hS : (s : Set ι).Pairwise (fun i j => Disjoint (S i) (S j)))
    (hf : ∀ i ∈ s, @Measurable _ _ (rowSigma (S i)) _ (f i)) :
    (∫ ω, ∏ i ∈ s, f i ω ∂environmentLaw ν) =
      ∏ i ∈ s, ∫ ω, f i ω ∂environmentLaw ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hp : (s : Set ι).Pairwise (fun i j => Disjoint (S i) (S j)) :=
      hS.mono (by intro i hi; exact Finset.mem_insert_of_mem hi)
    have hm : @Measurable _ _ (rowSigma (⋃ i ∈ s, S i)) _
        (fun ω => ∏ i ∈ s, f i ω) := by
      apply Finset.measurable_fun_prod
      intro i hi
      exact (hf i (Finset.mem_insert_of_mem hi)).mono
        (rowSigma_mono (Set.subset_iUnion₂_of_subset i hi Set.Subset.rfl)) le_rfl
    have hd : Disjoint (S a) (⋃ i ∈ s, S i) := by
      apply Set.disjoint_iUnion_right.mpr
      intro i
      apply Set.disjoint_iUnion_right.mpr
      intro hi
      exact hS (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)
        (ne_of_mem_of_not_mem hi ha).symm
    simp only [Finset.prod_insert ha]
    rw [fresh_rows_factor ν hd (hf a (Finset.mem_insert_self _ _)) hm,
      ih hp (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma nonneg_prod_le_const {ι : Type*} (s : Finset ι) (f : ι → ℝ) {B : ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ B) :
    0 ≤ ∏ i ∈ s, f i ∧ ∏ i ∈ s, f i ≤ B ^ s.card := by
  refine ⟨Finset.prod_nonneg (fun i hi => (hf i hi).1), ?_⟩
  simpa only [Finset.prod_const] using
    Finset.prod_le_prod (fun i hi => (hf i hi).1) (fun i hi => (hf i hi).2)

lemma prod_difference_bound {ι : Type*} (s : Finset ι) (f g : ι → ℝ) {B : ℝ}
    (hB : 1 ≤ B) (hf : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ f i ∧ f i ≤ B) :
    (∏ i ∈ s, f i) ≤ (∏ i ∈ s, g i) + B ^ s.card * ∑ i ∈ s, (f i - g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hft i (hi : i ∈ s) := hf i (Finset.mem_insert_of_mem hi)
    have ih := ih hft
    have hP := nonneg_prod_le_const s g (fun i hi =>
      ⟨(hft i hi).1, (hft i hi).2.1.trans (hft i hi).2.2⟩)
    have hsum : 0 ≤ ∑ i ∈ s, (f i - g i) := by
      exact Finset.sum_nonneg fun i hi => sub_nonneg.mpr (hft i hi).2.1
    have hdiff : 0 ≤ f a - g a := sub_nonneg.mpr hfa.2.1
    have hb : 0 ≤ B ^ s.card := pow_nonneg (zero_le_one.trans hB) _
    have hbn : B ^ s.card ≤ B ^ s.card * B :=
      le_mul_of_one_le_right hb hB
    simp only [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      pow_succ]
    calc
      f a * (∏ i ∈ s, f i) ≤
          f a * ((∏ i ∈ s, g i) + B ^ s.card * ∑ i ∈ s, (f i - g i)) :=
        mul_le_mul_of_nonneg_left ih (hfa.1.trans hfa.2.1)
      _ = g a * (∏ i ∈ s, g i) + (f a - g a) * (∏ i ∈ s, g i) +
          f a * (B ^ s.card * ∑ i ∈ s, (f i - g i)) := by ring
      _ ≤ g a * (∏ i ∈ s, g i) + (f a - g a) * B ^ s.card +
          B * (B ^ s.card * ∑ i ∈ s, (f i - g i)) := by
        gcongr
        · exact hP.2
        · exact hfa.2.2
      _ ≤ g a * (∏ i ∈ s, g i) + (f a - g a) * (B ^ s.card * B) +
          B * (B ^ s.card * ∑ i ∈ s, (f i - g i)) := by
        gcongr
      _ = _ := by ring

lemma clipped_inverse_integral_translation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x : Lattice d) (δ lam : ℝ) :
    (∫ ω, clippedInverse δ lam (noDropQuenched ℓ x ω) ∂environmentLaw ν) =
      ∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν := by
  conv_lhs => enter [2, ω]; rw [noDropQuenched_translation ℓ ω x]
  have h := integral_map (μ := environmentLaw ν)
    (show AEMeasurable (fun ω : Environment d => fun a => ω (x + a)) (environmentLaw ν) from
      (by fun_prop : Measurable (fun ω : Environment d => fun a => ω (x + a))).aemeasurable)
    (((clippedInverse_measurable δ lam).comp (measurable_noDropQuenched ℓ 0)).aestronglyMeasurable)
  rw [environment_translation] at h
  exact h.symm

lemma clipped_inverse_finite_integral_translation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x : Lattice d) (δ lam : ℝ) (n : ℕ) :
    (∫ ω, clippedInverse δ lam (noDropFinite ℓ x n ω) ∂environmentLaw ν) =
      ∫ ω, clippedInverse δ lam (noDropFinite ℓ 0 n ω) ∂environmentLaw ν := by
  conv_lhs => enter [2, ω]; rw [noDropFinite_translation ℓ ω x n]
  have h := integral_map (μ := environmentLaw ν)
    (show AEMeasurable (fun ω : Environment d => fun a => ω (x + a)) (environmentLaw ν) from
      (by fun_prop : Measurable (fun ω : Environment d => fun a => ω (x + a))).aemeasurable)
    (((clippedInverse_measurable δ lam).comp (noDropFinite_measurable ℓ 0 n)).aestronglyMeasurable)
  rw [environment_translation] at h
  exact h.symm

lemma integrable_of_nonneg_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ a, 0 ≤ f a ∧ f a ≤ B) : Integrable f μ := by
  exact (MemLp.of_bound (p := 1) hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hb a).1] using (hb a).2)).integrable le_rfl

lemma clipped_inverse_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {f : Environment d → ℝ≥0∞} (hf : Measurable f) {δ lam : ℝ}
    (hδ : 0 < δ) (hlam : 0 ≤ lam) :
    Integrable (fun ω => clippedInverse δ lam (f ω)) (environmentLaw ν) :=
  integrable_of_nonneg_bound _ ((clippedInverse_measurable δ lam).comp hf)
    (fun _ => clippedInverse_bounds lam hδ hlam _)

lemma clipped_inverse_integral_gap {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam) (n : ℕ) :
    (∫ ω, clippedInverse δ lam (noDropQuenched ℓ x ω) -
      clippedInverse δ lam (noDropFinite ℓ x n ω) ∂environmentLaw ν) =
    ∫ ω, |clippedInverse δ lam (noDropQuenched ℓ 0 ω) -
      clippedInverse δ lam (noDropFinite ℓ 0 n ω)| ∂environmentLaw ν := by
  have hi y := clipped_inverse_integrable ν (measurable_noDropQuenched ℓ y) hδ hlam
  have hj y := clipped_inverse_integrable ν (noDropFinite_measurable ℓ y n) hδ hlam
  rw [integral_sub (hi x) (hj x), clipped_inverse_integral_translation,
    clipped_inverse_finite_integral_translation, ← integral_sub (hi 0) (hj 0)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => (abs_of_nonneg (sub_nonneg.mpr
    (clippedInverse_antitone hδ hlam (measure_ne_top _ _)
      (noDropQuenched_le_finite ℓ 0 ω n)))).symm

lemma separated_clipped_inverse_product {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x : Fin k → Lattice d,
      (Pairwise fun i j => Disjoint (LatticeBall (x i) n) (LatticeBall (x j) n)) →
      (∫ ω, ∏ i, clippedInverse δ lam (noDropQuenched ℓ (x i) ω) ∂environmentLaw ν) ≤
        (∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν) ^ k + ε := by
  classical
  let B := max 1 (δ ^ (-lam))
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hlim := (noDrop_clipped_inverse_L1 ν ℓ 0 hδ hlam).const_mul (B ^ k * (k : ℝ))
  simp only [mul_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hε).exists
  refine ⟨n, fun x hx => ?_⟩
  let f : Fin k → Environment d → ℝ := fun i ω =>
    clippedInverse δ lam (noDropQuenched ℓ (x i) ω)
  let g : Fin k → Environment d → ℝ := fun i ω =>
    clippedInverse δ lam (noDropFinite ℓ (x i) n ω)
  have hf i : Measurable (f i) :=
    (clippedInverse_measurable δ lam).comp (measurable_noDropQuenched ℓ (x i))
  have hg i : Measurable (g i) :=
    (clippedInverse_measurable δ lam).comp (noDropFinite_measurable ℓ (x i) n)
  have hfb i ω : 0 ≤ f i ω ∧ f i ω ≤ B :=
    ⟨(clippedInverse_bounds lam hδ hlam _).1,
      (clippedInverse_bounds lam hδ hlam _).2.trans (le_max_right _ _)⟩
  have hgb i ω : 0 ≤ g i ω ∧ g i ω ≤ B :=
    ⟨(clippedInverse_bounds lam hδ hlam _).1,
      (clippedInverse_bounds lam hδ hlam _).2.trans (le_max_right _ _)⟩
  have hgf i ω : g i ω ≤ f i ω := clippedInverse_antitone hδ hlam
    (measure_ne_top _ _) (noDropQuenched_le_finite ℓ (x i) ω n)
  have hfi i := integrable_of_nonneg_bound (environmentLaw ν) (hf i) (hfb i)
  have hgi i := integrable_of_nonneg_bound (environmentLaw ν) (hg i) (hgb i)
  have hfpi : Integrable (fun ω => ∏ i, f i ω) (environmentLaw ν) :=
    integrable_of_nonneg_bound _ (Finset.measurable_fun_prod _ (fun i _ => hf i))
      (fun ω => by
        simpa using nonneg_prod_le_const Finset.univ (fun i => f i ω)
          (fun i _ => hfb i ω))
  have hgpi : Integrable (fun ω => ∏ i, g i ω) (environmentLaw ν) :=
    integrable_of_nonneg_bound _ (Finset.measurable_fun_prod _ (fun i _ => hg i))
      (fun ω => by
        simpa using nonneg_prod_le_const Finset.univ (fun i => g i ω)
          (fun i _ => hgb i ω))
  have hsum : Integrable (fun ω => ∑ i, (f i ω - g i ω)) (environmentLaw ν) :=
    integrable_finsetSum _ (fun i _ => (hfi i).sub (hgi i))
  have hbd := integral_mono hfpi (hgpi.add (hsum.const_mul (B ^ k)))
    (fun ω => by
      simpa using prod_difference_bound Finset.univ
        (fun i => f i ω) (fun i => g i ω) hB
        (fun i _ => ⟨(hgb i ω).1, hgf i ω, (hfb i ω).2⟩))
  simp only [Pi.add_apply] at hbd
  rw [integral_add hgpi (hsum.const_mul (B ^ k)), integral_const_mul,
    integral_finsetSum (f := fun i ω => f i ω - g i ω) _
      (fun i _ => (hfi i).sub (hgi i))] at hbd
  have hprod : (∫ ω, ∏ i, g i ω ∂environmentLaw ν) =
      (∫ ω, clippedInverse δ lam (noDropFinite ℓ 0 n ω) ∂environmentLaw ν) ^ k := by
    rw [fresh_rows_prod ν Finset.univ (fun i => LatticeBall (x i) n) g
      (fun i _ j _ hij => hx hij) (fun i _ =>
        (clippedInverse_measurable δ lam).comp (noDropFinite_measurable_ball ℓ (x i) n))]
    simp only [g, clipped_inverse_finite_integral_translation ν ℓ _ δ lam n,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hgap i : (∫ ω, f i ω - g i ω ∂environmentLaw ν) =
      ∫ ω, |clippedInverse δ lam (noDropQuenched ℓ 0 ω) -
        clippedInverse δ lam (noDropFinite ℓ 0 n ω)| ∂environmentLaw ν :=
    clipped_inverse_integral_gap ν ℓ (x i) hδ hlam n
  simp only [hprod, hgap, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hbd
  have hle : (∫ ω, clippedInverse δ lam (noDropFinite ℓ 0 n ω) ∂environmentLaw ν) ≤
      ∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν :=
    integral_mono (clipped_inverse_integrable ν (noDropFinite_measurable ℓ 0 n) hδ hlam)
      (clipped_inverse_integrable ν (measurable_noDropQuenched ℓ 0) hδ hlam)
      (fun ω => clippedInverse_antitone hδ hlam (measure_ne_top _ _)
        (noDropQuenched_le_finite ℓ 0 ω n))
  have hpow := pow_le_pow_left₀
    (integral_nonneg (fun ω => (clippedInverse_bounds lam hδ hlam _).1)) hle k
  change (∫ ω, ∏ i, f i ω ∂environmentLaw ν) ≤ _
  exact hbd.trans (add_le_add hpow (by simpa only [mul_assoc] using hn.le))

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

lemma noDrop_real_inverse_moment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
      Integrable (fun ω => (noDropQuenched ℓ 0 ω).toReal ^ (-lam)) (environmentLaw ν) := by
  obtain ⟨p, hp, hm⟩ := noDrop_inverse_moment ν hue ℓ hℓ htrans
  let lam := min p 1
  have hlam : 0 < lam := lt_min hp zero_lt_one
  have hfin : (∫⁻ ω, noDropQuenched ℓ 0 ω ^ (-lam) ∂environmentLaw ν) < ∞ := by
    apply lt_of_le_of_lt (lintegral_mono (fun ω => ?_)) hm
    exact ENNReal.rpow_le_rpow_of_exponent_ge (prob_le_one)
      (neg_le_neg (min_le_left p 1))
  refine ⟨lam, hlam, min_le_right _ _, ?_⟩
  simpa only [ENNReal.toReal_rpow] using
    integrable_toReal_of_lintegral_ne_top
      ((measurable_noDropQuenched ℓ 0).pow_const (-lam)).aemeasurable hfin.ne

lemma prod_max_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    (∏ i ∈ s, max (f i) δ) ≤ (∏ i ∈ s, f i) + δ := by
  classical
  by_cases h : ∀ i ∈ s, δ ≤ f i
  · have heq : (∏ i ∈ s, max (f i) δ) = ∏ i ∈ s, f i :=
      Finset.prod_congr rfl (fun i hi => max_eq_left (h i hi))
    rw [heq]
    exact le_add_of_nonneg_right hδ
  · push Not at h
    obtain ⟨i, hi, hif⟩ := h
    have hp := Finset.prod_le_prod_of_subset_of_le_one
      (show {i} ⊆ s from Finset.singleton_subset_iff.mpr hi)
      (f := fun j => max (f j) δ)
      (fun j hj => (hf j hj).1.trans (le_max_left _ _))
      (fun j hj _ => max_le (hf j hj).2 hδ1)
    simp only [Finset.prod_singleton, max_eq_right hif.le] at hp
    exact hp.trans (le_add_of_nonneg_left (Finset.prod_nonneg (fun j hj => (hf j hj).1)))

lemma noDropQuenched_toReal_le_one {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) : (noDropQuenched ℓ x ω).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono (show (1 : ℝ≥0∞) ≠ ∞ by simp)
    (show noDropQuenched ℓ x ω ≤ 1 from prob_le_one)

lemma noDropProduct_bounds {d k : ℕ} (ℓ : Vector d) (x : Fin k → Lattice d)
    (ω : Environment d) : 0 ≤ noDropProduct ℓ x ω ∧ noDropProduct ℓ x ω ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg),
    Finset.prod_le_one (fun _ _ => ENNReal.toReal_nonneg)
      (fun _ _ => noDropQuenched_toReal_le_one ℓ _ ω)⟩

lemma clippedNoDropProduct_bounds {d k : ℕ} (ℓ : Vector d) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : Fin k → Lattice d) (ω : Environment d) :
    δ ^ k ≤ clippedNoDropProduct ℓ δ x ω ∧ clippedNoDropProduct ℓ δ x ω ≤ 1 := by
  constructor
  · have h := Finset.prod_le_prod (s := Finset.univ)
      (f := fun _ : Fin k => δ) (g := fun i => max (noDropQuenched ℓ (x i) ω).toReal δ)
      (fun _ _ => hδ) (fun _ _ => le_max_right _ _)
    simpa [clippedNoDropProduct] using h
  · exact Finset.prod_le_one (fun _ _ => hδ.trans (le_max_right _ _))
      (fun _ _ => max_le (noDropQuenched_toReal_le_one ℓ _ ω) hδ1)

lemma clippedNoDropProduct_error {d k : ℕ} (ℓ : Vector d) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (x : Fin k → Lattice d) (ω : Environment d) :
    clippedNoDropProduct ℓ δ x ω ≤ noDropProduct ℓ x ω + δ := by
  exact prod_max_bound Finset.univ (fun i => (noDropQuenched ℓ (x i) ω).toReal)
    hδ hδ1 (fun _ _ => ⟨ENNReal.toReal_nonneg,
      noDropQuenched_toReal_le_one ℓ _ ω⟩)

lemma clippedNoDropProduct_measurable {d k : ℕ} (ℓ : Vector d) (δ : ℝ) :
    Measurable (fun z : Environment d × (Fin k → Lattice d) => clippedNoDropProduct ℓ δ z.2 z.1) := by
  apply measurable_from_prod_countable_left
  intro x
  exact Finset.measurable_fun_prod _ (fun i _ =>
    (measurable_noDropQuenched ℓ (x i)).ennreal_toReal.max measurable_const)

lemma clippedNoDropProduct_inverse {d k : ℕ} (ℓ : Vector d) {δ : ℝ}
    (hδ : 0 ≤ δ) (lam : ℝ) (x : Fin k → Lattice d) (ω : Environment d) :
    clippedNoDropProduct ℓ δ x ω ^ (-lam) =
      ∏ i, clippedInverse δ lam (noDropQuenched ℓ (x i) ω) := by
  exact (Real.finsetProd_rpow Finset.univ _
    (fun _ _ => hδ.trans (le_max_right _ _)) _).symm

lemma separated_noDropProduct_inverse_bound {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) {δ lam : ℝ}
    (hδ : 0 < δ) (hlam : 0 ≤ lam)
    (hpos : ∀ᵐ ω ∂environmentLaw ν, 0 < noDropQuenched ℓ 0 ω)
    (hmom : Integrable (fun ω => (noDropQuenched ℓ 0 ω).toReal ^ (-lam)) (environmentLaw ν))
    (k : ℕ) :
    ∃ n : ℕ, ∀ x : Fin k → Lattice d,
      (Pairwise fun i j => Disjoint (LatticeBall (x i) n) (LatticeBall (x j) n)) →
      (∫ ω, clippedNoDropProduct ℓ δ x ω ^ (-lam) ∂environmentLaw ν) ≤
        2 * (max 1 (∫ ω, (noDropQuenched ℓ 0 ω).toReal ^ (-lam) ∂environmentLaw ν)) ^ k := by
  obtain ⟨n, hn⟩ := separated_clipped_inverse_product ν ℓ hδ hlam k (show (0 : ℝ) < 1 by norm_num)
  refine ⟨n, fun x hx => ?_⟩
  simp_rw [clippedNoDropProduct_inverse ℓ hδ.le]
  have hle : (∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν) ≤
      ∫ ω, (noDropQuenched ℓ 0 ω).toReal ^ (-lam) ∂environmentLaw ν := by
    apply integral_mono_ae (clipped_inverse_integrable ν (measurable_noDropQuenched ℓ 0) hδ hlam) hmom
    filter_upwards [hpos] with ω hω
    exact Real.rpow_le_rpow_of_nonpos (ENNReal.toReal_pos hω.ne' (measure_ne_top _ _))
      (le_max_left _ _) (neg_nonpos.mpr hlam)
  have hnonneg : 0 ≤ ∫ ω, clippedInverse δ lam (noDropQuenched ℓ 0 ω) ∂environmentLaw ν :=
    integral_nonneg (fun ω => (clippedInverse_bounds lam hδ hlam
      (noDropQuenched ℓ 0 ω)).1)
  have hp := pow_le_pow_left₀ hnonneg (hle.trans (le_max_right 1 _)) k
  have h1 := one_le_pow₀ (n := k) (le_max_left 1
    (∫ ω, (noDropQuenched ℓ 0 ω).toReal ^ (-lam) ∂environmentLaw ν))
  have h := hn x hx
  nlinarith

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

lemma convexOn_rpow_nonpos_Ici {δ p : ℝ} (hδ : 0 < δ) (hp : p ≤ 0) :
    ConvexOn ℝ (Set.Ici δ) (fun x : ℝ => x ^ p) := by
  refine ⟨convex_Ici δ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 := hδ.trans_le hx
  have hy0 := hδ.trans_le hy
  have hz : 0 < a • x + b • y :=
    hδ.trans_le ((convex_Ici δ) hx hy ha hb hab)
  have hl := (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).2 hx0 hy0 ha hb hab
  have he := convexOn_exp.2 (Set.mem_univ (p * Real.log x))
    (Set.mem_univ (p * Real.log y)) ha hb hab
  simp only [smul_eq_mul] at hl he hz ⊢
  rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hy0]
  calc
    Real.exp (Real.log (a * x + b * y) * p) ≤
      Real.exp (a * (p * Real.log x) + b * (p * Real.log y)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonpos_right hl hp]
    _ ≤ a * Real.exp (Real.log x * p) + b * Real.exp (Real.log y * p) := by
      simpa only [mul_comm p] using he

lemma inverse_jensen_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {δ B lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam) (hb : ∀ x, δ ≤ f x ∧ f x ≤ B) :
    (∫ x, f x ∂μ) ^ (-lam) ≤ ∫ x, (f x) ^ (-lam) ∂μ := by
  have hi : Integrable f μ :=
    (MemLp.of_bound (p := 1) hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hδ.le.trans (hb x).1)] using
          (hb x).2)).integrable le_rfl
  have hj : Integrable (fun x => (f x) ^ (-lam)) μ :=
    (MemLp.of_bound (p := 1) (hf.pow_const _).aestronglyMeasurable (δ ^ (-lam))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hδ.le.trans (hb x).1) _)]
        exact Real.rpow_le_rpow_of_nonpos hδ (hb x).1 (neg_nonpos.mpr hlam))).integrable le_rfl
  exact (convexOn_rpow_nonpos_Ici hδ (neg_nonpos.mpr hlam)).map_integral_le
    (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hδ.trans_le hx))))
    isClosed_Ici (Filter.Eventually.of_forall fun x => (hb x).1) hi hj

lemma inverse_mixture_markov {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) (π : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (F : Ω → A → ℝ) (hF : Measurable (Function.uncurry F)) (Q : Ω → ℝ)
    {δ₀ δ lam s K : ℝ} (hδ₀ : 0 < δ₀) (hlam : 0 ≤ lam) (hs : 0 < s) (hδs : δ ≤ s)
    (hb : ∀ ω a, δ₀ ≤ F ω a ∧ F ω a ≤ 1)
    (hQ : ∀ ω, (∫ a, F ω a ∂π) ≤ Q ω + δ)
    (hE : (∫ ω, ∫ a, (F ω a) ^ (-lam) ∂π ∂μ) ≤ K) :
    μ {ω | Q ω < 2 * s} ≤ ENNReal.ofReal ((3 * s) ^ lam * K) := by
  have hGi : Integrable (fun z : Ω × A => F z.1 z.2 ^ (-lam)) (μ.prod π) :=
    (MemLp.of_bound (p := 1) (hF.pow_const _).aestronglyMeasurable (δ₀ ^ (-lam))
      (Filter.Eventually.of_forall fun z => by
        change ‖F z.1 z.2 ^ (-lam)‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hδ₀.le.trans (hb z.1 z.2).1) _)]
        exact Real.rpow_le_rpow_of_nonpos hδ₀ (hb z.1 z.2).1
          (neg_nonpos.mpr hlam))).integrable le_rfl
  have hJi ω : Integrable (F ω) π :=
    (MemLp.of_bound (p := 1) (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun a => by
        change ‖F ω a‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (hδ₀.le.trans (hb ω a).1)]
        exact (hb ω a).2)).integrable le_rfl
  have hJpos ω : 0 < ∫ a, F ω a ∂π := by
    have hl := integral_mono (integrable_const δ₀) (hJi ω) (fun a => (hb ω a).1)
    have hl' : δ₀ ≤ ∫ a, F ω a ∂π := by simpa using hl
    exact hδ₀.trans_le hl'
  have hp : 0 < 3 * s := mul_pos (by norm_num) hs
  have hMeas := (hGi.integral_prod_left.const_mul ((3 * s) ^ lam)).measure_le_integral
    (Filter.Eventually.of_forall fun ω => mul_nonneg (Real.rpow_nonneg hp.le _)
      (integral_nonneg (fun a => Real.rpow_nonneg (hδ₀.le.trans (hb ω a).1) _)))
    (s := {ω | Q ω < 2 * s}) (fun ω hω => by
      have hJle : (∫ a, F ω a ∂π) ≤ 3 * s := by
        change Q ω < 2 * s at hω
        linarith [hQ ω]
      have hj := inverse_jensen_bounded π
        (hF.comp (measurable_const.prodMk measurable_id)) hδ₀ hlam (hb ω)
      have hr := Real.rpow_le_rpow_of_nonpos (hJpos ω) hJle (neg_nonpos.mpr hlam)
      calc
        1 = (3 * s) ^ lam * (3 * s) ^ (-lam) := by
          rw [← Real.rpow_add hp, add_neg_cancel, Real.rpow_zero]
        _ ≤ (3 * s) ^ lam * ∫ a, F ω a ^ (-lam) ∂π :=
          mul_le_mul_of_nonneg_left (hr.trans hj) (Real.rpow_nonneg hp.le _))
  rw [integral_const_mul] at hMeas
  exact hMeas.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hp.le _)))

theorem separated_initial_inverse_moment {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d)
    (hℓ : dot ℓ ℓ = 1) (htrans : DirectionallyTransient ν ℓ) (e : Fin d) :
    ∃ lam C : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < C ∧
      ∀ Bstar : ℝ, 0 < Bstar → ∀ k : ℕ, 1 ≤ k → ∃ G : ℕ,
      ∀ (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π],
        (∀ᵐ x ∂π, Pairwise fun i j => (G : ℤ) ≤ |x i e - x j e|) →
        ∀ s : ℝ, Real.exp (-Bstar) ≤ s →
        (environmentLaw ν) {ω | (∫ x, noDropProduct ℓ x ω ∂π) < 2 * s} ≤
          ENNReal.ofReal (Real.exp (C * k) * s ^ lam) := by
  classical
  obtain ⟨lam, hlam, hlam1, hmom⟩ := noDrop_real_inverse_moment ν hue ℓ hℓ htrans
  let M := max 1 (∫ ω, (noDropQuenched ℓ 0 ω).toReal ^ (-lam) ∂environmentLaw ν)
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let C := Real.log (6 * M)
  have hC : 0 < C := Real.log_pos (by linarith)
  refine ⟨lam, C, hlam, hlam1, hC, ?_⟩
  intro Bstar hBstar k hk
  let δ := Real.exp (-Bstar)
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hBstar.le)
  have hpos : ∀ᵐ ω ∂environmentLaw ν, 0 < noDropQuenched ℓ 0 ω := by
    filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans] with ω hω
    exact hω 0
  obtain ⟨n, hn⟩ := separated_noDropProduct_inverse_bound ν ℓ hδ hlam.le hpos hmom k
  refine ⟨2 * n + 1, ?_⟩
  intro π hπ hsep s hs
  have hs0 : 0 < s := hδ.trans_le hs
  let F : Environment d → (Fin k → Lattice d) → ℝ := fun ω x => clippedNoDropProduct ℓ δ x ω
  have hF : Measurable (Function.uncurry F) := clippedNoDropProduct_measurable ℓ δ
  have hb ω x : δ ^ k ≤ F ω x ∧ F ω x ≤ 1 :=
    clippedNoDropProduct_bounds ℓ hδ.le hδ1 x ω
  have hGi : Integrable (fun z : Environment d × (Fin k → Lattice d) =>
      F z.1 z.2 ^ (-lam)) ((environmentLaw ν).prod π) := by
    apply integrable_of_nonneg_bound _ (hF.pow_const _)
    intro z
    exact ⟨Real.rpow_nonneg ((pow_pos hδ k).le.trans (hb z.1 z.2).1) _,
      Real.rpow_le_rpow_of_nonpos (pow_pos hδ k) (hb z.1 z.2).1 (neg_nonpos.mpr hlam.le)⟩
  have hE : (∫ ω, ∫ x, F ω x ^ (-lam) ∂π ∂environmentLaw ν) ≤ 2 * M ^ k := by
    rw [integral_integral_swap hGi]
    have hh := integral_mono_ae hGi.integral_prod_right (integrable_const (2 * M ^ k))
      (hsep.mono fun x hx => hn x (fun i j hij => latticeBall_disjoint_of_coordinate_gap e
        (by have h := hx hij; omega)))
    simpa using hh
  have hQ ω : (∫ x, F ω x ∂π) ≤ (∫ x, noDropProduct ℓ x ω ∂π) + δ := by
    have hI : Integrable (noDropProduct ℓ · ω) π :=
      integrable_of_nonneg_bound π (measurable_of_countable _) (fun x => noDropProduct_bounds ℓ x ω)
    have hJ : Integrable (F ω) π :=
      integrable_of_nonneg_bound π (measurable_of_countable _) (fun x =>
        ⟨(pow_pos hδ k).le.trans (hb ω x).1, (hb ω x).2⟩)
    calc
      (∫ x, F ω x ∂π) ≤ ∫ x, noDropProduct ℓ x ω + δ ∂π :=
        integral_mono hJ (hI.add (integrable_const δ)) (clippedNoDropProduct_error ℓ hδ.le hδ1 · ω)
      _ = (∫ x, noDropProduct ℓ x ω ∂π) + δ := by simp [integral_add hI (integrable_const δ)]
  have hmark := inverse_mixture_markov (environmentLaw ν) π F hF
    (fun ω => ∫ x, noDropProduct ℓ x ω ∂π) (pow_pos hδ k) hlam.le hs0 hs hb hQ hE
  apply hmark.trans (ENNReal.ofReal_le_ofReal ?_)
  have h3 : (3 : ℝ) ^ lam ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 3 by norm_num) hlam1
  have h6 : (6 : ℝ) ≤ 6 ^ k := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 6 by norm_num) hk
    simpa only [pow_one] using h
  have hexp : Real.exp (C * k) = (6 * M) ^ k := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by positivity : 0 < 6 * M)]
  rw [hexp, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hs0.le, mul_pow]
  have hsp : 0 ≤ s ^ lam := Real.rpow_nonneg hs0.le _
  calc
    3 ^ lam * s ^ lam * (2 * M ^ k) ≤ 6 * M ^ k * s ^ lam := by
      nlinarith [mul_le_mul_of_nonneg_right h3 (mul_nonneg hsp (pow_nonneg hM0 k))]
    _ ≤ 6 ^ k * M ^ k * s ^ lam := by gcongr

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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma commonWordWidth_positive {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d)) (P : Path d × Path d)
    (hP : P ∈ FirstPairWordEvent ℓ wv) : 0 < commonWordWidth ℓ wv := by
  have hr : StrictRecord ℓ (wordPath 0 wv.1) wv.1.length :=
    (strictRecord_congr_prefix ℓ le_rfl hP.2.1.1).mp hP.2.2.2.2.1.1.1
  simpa only [commonWordWidth,wordRecordCount,recordCount_zero] using
    recordCount_lt_of_strictRecord ℓ (wordPath 0 wv.1) hP.2.2.1 hr

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

lemma integrable_truncated_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S) (r : ℝ) :
    Integrable (fun x => min ((S x)^2) (r^2)) μ := by
  apply (integrable_const (r^2)).mono' ((hS.pow_const 2).min measurable_const).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
    exact min_le_right _ _

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

lemma measureReal_partialSumMax_gt_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z : ℝ} (hz : 0 < z) (n : ℕ) :
    μ.real {ω | z < partialSumMax (fun k => X k ω) n} ≤
      5*(n : ℝ)*truncatedVariance μ (X 0) z / z^2 := by
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ω => le_min
      (sq_nonneg (partialSumMax (fun k => X k ω) n)) (sq_nonneg z)))
    (integrable_truncated_square μ _ (measurable_partialSumMax X hX n) z) (z^2)
  have hmono : μ.real {ω | z < partialSumMax (fun k => X k ω) n} ≤
      μ.real {ω | z^2 ≤ min ((partialSumMax (fun k => X k ω) n)^2) (z^2)} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    change z < partialSumMax (fun k => X k ω) n at hω
    change z^2 ≤ min ((partialSumMax (fun k => X k ω) n)^2) (z^2)
    apply le_min
    · nlinarith only [mul_self_le_mul_self hz.le hω.le]
    · exact le_rfl
  apply (le_div_iff₀ (sq_pos_of_pos hz)).mpr
  calc
    μ.real {ω | z < partialSumMax (fun k => X k ω) n} * z^2 ≤
      z^2 * μ.real {ω | z^2 ≤ min ((partialSumMax (fun k => X k ω) n)^2) (z^2)} := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hmono (sq_nonneg z)
    _ ≤ ∫ ω, min ((partialSumMax (fun k => X k ω) n)^2) (z^2) ∂μ := hb
    _ ≤ _ := integral_partialSumMax_capped_le μ X hX hind hident hsym hz.le n

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

lemma independent_common_maximal_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d)
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (independentConditionedPairLaw ν ℓ).real
      {P | r < partialSumMax (fun k => commonIncrementProcess ℓ e k P) n} ≤
      5*(n : ℝ)/fluctuationScale (independentConditionedPairLaw ν ℓ)
        (commonIncrementProcess ℓ e 0) r := by
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  rw [fluctuationScale,div_div_eq_mul_div]
  exact measureReal_partialSumMax_gt_le _ _ (measurable_commonIncrementProcess ℓ e)
    (commonIncrements_independent ν ℓ htrans height hproj hstep e)
    (commonIncrements_identDistrib ν ℓ htrans height hproj hstep e)
    (independent_commonWordIncrement_symmetric ν ℓ htrans e) hr n

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

lemma commonIndex_le_recordCount {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (n : ℕ) : n ≤ recordCount ℓ P.1 (commonTimes ℓ P n).1 := by
  rw [recordCount_commonTimes ℓ P h0 h0' hP n]
  calc
    n = ∑ i ∈ Finset.range n, 1 := by simp
    _ ≤ ∑ i ∈ Finset.range n, wordRecordCount ℓ (commonWords ℓ P i).1 :=
      Finset.sum_le_sum fun i _ => commonWordWidth_positive ℓ _ _ (hP i)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RecordIndexTime
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

lemma common_record_gap_le_max {d : ℕ} (ℓ : Vector d) (e : Direction d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    {j k H : ℕ} (hr : CommonTrueRecord ℓ P j k) (hH : recordCount ℓ P.1 j ≤ H) :
    |signedCoordinate e (P.1 j)-signedCoordinate e (P.2 k)| ≤
      partialSumMax (fun n => commonIncrementProcess ℓ e n P) H := by
  obtain ⟨n, hn⟩ := commonTrueRecord_eq_commonTimes ℓ P h0 h0' hP hr
  have hcoord := common_coordinate_sum ℓ e P h0 h0' hP n
  have hnle := commonIndex_le_recordCount ℓ P h0 h0' hP n
  rw [hn] at hcoord hnle
  rw [hcoord]
  exact (abs_partialSum_le_max _ n).trans (partialSumMax_mono _ (hnle.trans hH))

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

lemma measurableSet_pairRecordDeviation {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) (n m : ℕ) : MeasurableSet (PairRecordDeviation ℓ e H z n m) := by
  simp only [PairRecordDeviation,Set.ofPred_and,Set.ofPred_exists]
  refine (MeasurableSet.iUnion fun r => (MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter ((measurableSet_recordIndexPrefix ℓ r n).prod
      (measurableSet_recordIndexPrefix ℓ r m)))).inter ?_
  exact (measurableSet_eq_fun
    ((measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp
      ((measurable_pi_apply n).comp measurable_fst))
    ((measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp
      ((measurable_pi_apply m).comp measurable_snd))).inter
    (measurableSet_lt measurable_const
      (((measurable_of_countable (signedCoordinate e)).comp
        ((measurable_pi_apply n).comp measurable_fst)).sub
       ((measurable_of_countable (signedCoordinate e)).comp
        ((measurable_pi_apply m).comp measurable_snd))).abs)

lemma measurableSet_firstPairRecordDeviation {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) (q : ℕ × ℕ) : MeasurableSet (FirstPairRecordDeviation ℓ e H z q) := by
  simp only [FirstPairRecordDeviation,Set.ofPred_forall]
  exact (measurableSet_pairRecordDeviation ℓ e H z q.1 q.2).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
        (measurableSet_pairRecordDeviation ℓ e H z j k).compl)

lemma pairRecordDeviation_prefix {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) {j k n m : ℕ} (hj : j ≤ n) (hk : k ≤ m) :
    PairPrefixDetermined n m (PairRecordDeviation ℓ e H z j k) := by
  intro P Q h1 h2
  have hrec1 (r : ℕ) := recordIndexPrefix_prefix ℓ r j P.1 Q.1 (fun i hi => h1 i (hi.trans hj))
  have hrec2 (r : ℕ) := recordIndexPrefix_prefix ℓ r k P.2 Q.2 (fun i hi => h2 i (hi.trans hk))
  simp only [PairRecordDeviation,Set.mem_ofPred_eq,hrec1,hrec2,h1 j hj,h2 k hk]

lemma firstPairRecordDeviation_prefix {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) (q : ℕ × ℕ) :
    PairPrefixDetermined q.1 q.2 (FirstPairRecordDeviation ℓ e H z q) := by
  intro P Q h1 h2
  have he := pairRecordDeviation_prefix ℓ e H z le_rfl le_rfl P Q h1 h2
  simp only [FirstPairRecordDeviation,Set.mem_inter_iff,Set.mem_ofPred_eq,he]
  apply and_congr Iff.rfl
  exact forall_congr' fun j => forall_congr' fun hj => forall_congr' fun k =>
    forall_congr' fun hk => not_congr
      (pairRecordDeviation_prefix ℓ e H z hj.le hk.le P Q h1 h2)

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

lemma pairRecordDeviation_time_order {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) {P : Path d × Path d} {n m j k : ℕ}
    (hP : P ∈ PairRecordDeviation ℓ e H z n m)
    (hQ : P ∈ PairRecordDeviation ℓ e H z j k) :
    (n < j ↔ m < k) ∧ (n = j ↔ m = k) := by
  obtain ⟨⟨r,_,_,hr,hr'⟩,_⟩ := hP
  obtain ⟨⟨s,_,_,hs,hs'⟩,_⟩ := hQ
  have h1 := recordIndexPrefix_time_lt_iff ℓ P.1 hr hs
  have h2 := recordIndexPrefix_time_lt_iff ℓ P.2 hr' hs'
  refine ⟨h1.trans h2.symm,?_⟩
  have h3 := recordIndexPrefix_time_lt_iff ℓ P.1 hs hr
  have h4 := recordIndexPrefix_time_lt_iff ℓ P.2 hs' hr'
  omega

lemma firstPairRecordDeviation_disjoint {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) : Pairwise (fun q q' =>
      Disjoint (FirstPairRecordDeviation ℓ e H z q) (FirstPairRecordDeviation ℓ e H z q')) := by
  intro q q' hne
  apply Set.disjoint_left.mpr
  intro P hP hQ
  have hord := pairRecordDeviation_time_order ℓ e H z hP.1 hQ.1
  rcases lt_trichotomy q.1 q'.1 with h | h | h
  · exact hQ.2 q.1 h q.2 (hord.1.mp h) hP.1
  · exact hne (Prod.ext h (hord.2.mp h))
  · have hh := (pairRecordDeviation_time_order ℓ e H z hQ.1 hP.1).1.mp h
    exact hP.2 q'.1 h q'.2 hh hQ.1

lemma iUnion_firstPairRecordDeviation {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) :
    (⋃ q, FirstPairRecordDeviation ℓ e H z q) = ⋃ n, ⋃ m, PairRecordDeviation ℓ e H z n m := by
  classical
  apply Set.Subset.antisymm
  · intro P hP
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hP
    exact Set.mem_iUnion.mpr ⟨q.1,Set.mem_iUnion.mpr ⟨q.2,hq.1⟩⟩
  · intro P hP
    have hx : ∃ n, ∃ m, P ∈ PairRecordDeviation ℓ e H z n m := by
      simpa only [Set.mem_iUnion] using hP
    obtain ⟨m,hm⟩ := Nat.find_spec hx
    apply Set.mem_iUnion.mpr
    refine ⟨(Nat.find hx,m),hm,?_⟩
    intro j hj k _ h
    exact Nat.find_min hx hj ⟨k,h⟩

lemma firstPairRecordDeviation_force_lower {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (e : Direction d) (H : ℕ) (z : ℝ) (q : ℕ × ℕ) :
    independentPairLaw ν (FirstPairRecordDeviation ℓ e H z q) ≤
      independentConditionedPairLaw ν ℓ
        (FirstPairRecordDeviation ℓ e H z q ∩ (FutureNoDrop ℓ q.1 ×ˢ FutureNoDrop ℓ q.2)) := by
  by_cases hq : 0 < q.1 ∧ 0 < q.2
  · apply independent_conditioned_record_prefix_lower ν ℓ hp hq.1 hq.2 _
      (measurableSet_firstPairRecordDeviation ℓ e H z q)
      (firstPairRecordDeviation_prefix ℓ e H z q)
    · intro P hP
      obtain ⟨r,_,_,hr,hr'⟩ := hP.1.1
      exact ⟨hr.2.1,hr'.2.1,hP.1.2.1⟩
    · rintro P ⟨hP,hF⟩
      obtain ⟨r,_,_,hr,hr'⟩ := hP.1.1
      exact ⟨recordIndexPrefix_noDrop ℓ r q.1 ⟨hr,hF.1⟩,
        recordIndexPrefix_noDrop ℓ r q.2 ⟨hr',hF.2⟩⟩
  · have he : FirstPairRecordDeviation ℓ e H z q = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro P hP
      obtain ⟨r,_,_,hr,hr'⟩ := hP.1.1
      exact hq ⟨hr.1,hr'.1⟩
    rw [he,measure_empty]
    exact bot_le

lemma independent_pair_deviation_transfer {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d) (H : ℕ) (z : ℝ) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ
      (⋃ n, ⋃ m, PairRecordDeviation ℓ e H z n m) ≤
    independentConditionedPairLaw ν ℓ
      {P | z < partialSumMax (fun n => commonIncrementProcess ℓ e n P) H} := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let A := FirstPairRecordDeviation ℓ e H z
  let B (q : ℕ × ℕ) := A q ∩ (FutureNoDrop ℓ q.1 ×ˢ FutureNoDrop ℓ q.2)
  have hAm (q) : MeasurableSet (A q) := measurableSet_firstPairRecordDeviation ℓ e H z q
  have hBm (q) : MeasurableSet (B q) := (hAm q).inter
    ((measurableSet_futureNoDrop ℓ q.1).prod (measurableSet_futureNoDrop ℓ q.2))
  have hBd : Pairwise (fun q q' => Disjoint (B q) (B q')) := by
    intro q q' hne
    exact (firstPairRecordDeviation_disjoint ℓ e H z hne).mono
      Set.inter_subset_left Set.inter_subset_left
  rw [← iUnion_firstPairRecordDeviation]
  calc
    _ ≤ independentPairLaw ν (⋃ q, A q) :=
      independentConditionedPairLaw_le_raw ν ℓ hp _ (MeasurableSet.iUnion hAm)
    _ = ∑' q, independentPairLaw ν (A q) :=
      measure_iUnion (firstPairRecordDeviation_disjoint ℓ e H z) hAm
    _ ≤ ∑' q, independentConditionedPairLaw ν ℓ (B q) :=
      ENNReal.tsum_le_tsum (firstPairRecordDeviation_force_lower ν ℓ hp e H z)
    _ = independentConditionedPairLaw ν ℓ (⋃ q, B q) := (measure_iUnion hBd hBm).symm
    _ ≤ _ := by
      apply measure_mono_ae
      have hac := conditionedLaw_absolutelyContinuous ν ℓ
      have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
        (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
      filter_upwards [h0,independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep]
        with P h0 hP hB
      obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hB
      obtain ⟨r,_,hrH,hr,hr'⟩ := hq.1.1.1
      have htrue : CommonTrueRecord ℓ P q.1 q.2 :=
        ⟨⟨hr.2.1,hq.2.1⟩,⟨hr'.2.1,hq.2.2⟩,hq.1.1.2.1⟩
      exact hq.1.1.2.2.trans_le (common_record_gap_le_max ℓ e P h0.1 h0.2 hP htrue
        (hr.2.2.1.trans_le hrH))

lemma independent_firstHit_pair_maximum {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d) (H : ℕ) (z : ℝ) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ
      {P | ∃ r, 0 < r ∧ r ≤ H ∧
        z < |signedCoordinate e (recordIndexPosition ℓ r P.1) -
          signedCoordinate e (recordIndexPosition ℓ r P.2)|} ≤
    independentConditionedPairLaw ν ℓ
      {P | z < partialSumMax (fun n => commonIncrementProcess ℓ e n P) H} := by
  apply le_trans ?_ (independent_pair_deviation_transfer ν ℓ htrans
    height hproj hstep e H z)
  apply mul_le_mul_right
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  have hs : ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ r, 0 < r →
      X ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r X) :=
    ae_all_iff.mpr fun r => ae_all_iff.mpr fun hr =>
      conditioned_recordIndexTime_spec ν ℓ htrans hr
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
  have hNN := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_nearest_neighbor ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_nearest_neighbor ν)))
  have hs' := (Measure.quasiMeasurePreserving_fst.ae hs).and
    (Measure.quasiMeasurePreserving_snd.ae hs)
  apply measure_mono_ae
  filter_upwards [h0,hNN,hs'] with P h0 hNN hs hP
  obtain ⟨r,hr,hrH,hrz⟩ := hP
  have h1 := hs.1 r hr
  have h2 := hs.2 r hr
  have hs1 (j : ℕ) : height (P.1 (j+1)) ≤ height (P.1 j)+1 := by
    obtain ⟨v,hv⟩ := hNN.1 j
    rw [hv]; exact hstep _ _
  have hs2 (j : ℕ) : height (P.2 (j+1)) ≤ height (P.2 j)+1 := by
    obtain ⟨v,hv⟩ := hNN.2 j
    rw [hv]; exact hstep _ _
  refine Set.mem_iUnion.mpr ⟨recordIndexTime ℓ r P.1,Set.mem_iUnion.mpr
    ⟨recordIndexTime ℓ r P.2,⟨r,hr,hrH,h1,h2⟩,?_,hrz⟩⟩
  rw [hproj,hproj,recordCount_eq_height_at_record ℓ height hproj P.1 hs1 h1.2.1,
    recordCount_eq_height_at_record ℓ height hproj P.2 hs2 h2.2.1,h0.1,h0.2,h1.2.2.1,h2.2.2.1]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IntegerMedian
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

lemma integerMedian_spec (μ : Measure ℤ) [IsProbabilityMeasure μ] :
    (1/2 : ℝ≥0∞) ≤ μ (Set.Iic (integerMedian μ)) ∧
    (1/2 : ℝ≥0∞) ≤ μ (Set.Ici (integerMedian μ)) :=
  (exists_integer_median μ).choose_spec

lemma median_family_symmetrization {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ι → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (b : ι → ℝ)
    (hb : ∀ i, (1/2 : ℝ≥0∞) ≤ μ {x | f i x ≤ b i} ∧
      (1/2 : ℝ≥0∞) ≤ μ {x | b i ≤ f i x}) (s : Set ι) (z : ℝ) :
    (1/2 : ℝ≥0∞) * μ {x | ∃ i ∈ s, z < |f i x-b i|} ≤
      μ.prod μ {P | ∃ i ∈ s, z < |f i P.1-f i P.2|} := by
  classical
  let A : Set Ω := {x | ∃ i ∈ s, z < |f i x-b i|}
  let E : Set (Ω × Ω) := {P | ∃ i ∈ s, z < |f i P.1-f i P.2|}
  have hA : MeasurableSet A := by
    simp only [A,Set.ofPred_exists,Set.ofPred_and]
    exact MeasurableSet.iUnion fun i => (MeasurableSet.const _).inter
      (measurableSet_lt measurable_const ((hf i).sub_const (b i)).abs)
  have hE : MeasurableSet E := by
    simp only [E,Set.ofPred_exists,Set.ofPred_and]
    exact MeasurableSet.iUnion fun i => (MeasurableSet.const _).inter
      (measurableSet_lt measurable_const
        (((hf i).comp measurable_fst).sub ((hf i).comp measurable_snd)).abs)
  change (1/2 : ℝ≥0∞) * μ A ≤ μ.prod μ E
  rw [Measure.prod_apply hE]
  calc
    _ = ∫⁻ x, A.indicator (fun _ => (1/2 : ℝ≥0∞)) x ∂μ := by
      rw [lintegral_indicator hA,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        obtain ⟨i,hi,hlarge⟩ := hx
        rcases (lt_abs.mp hlarge) with hright | hleft
        · apply (hb i).1.trans (measure_mono ?_)
          intro y hy
          change f i y ≤ b i at hy
          refine ⟨i,hi,?_⟩
          exact lt_of_lt_of_le (by linarith : z < f i x-f i y) (le_abs_self _)
        · apply (hb i).2.trans (measure_mono ?_)
          intro y hy
          change b i ≤ f i y at hy
          refine ⟨i,hi,?_⟩
          exact lt_of_lt_of_le (by linarith : z < -(f i x-f i y)) (neg_le_abs _)
      · rw [Set.indicator_of_notMem hx]
        exact bot_le

lemma signedIntegerCoordinate_cast {d : ℕ} (e : Direction d) (x : Lattice d) :
    (signedIntegerCoordinate e x : ℝ) = signedCoordinate e x := by
  simp only [signedIntegerCoordinate,signedCoordinate]
  split <;> simp

lemma recordMedian_spec {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (e : Direction d) (r : ℕ) :
    (1/2 : ℝ≥0∞) ≤ conditionedLaw ν ℓ
      {X | signedCoordinate e (recordIndexPosition ℓ r X) ≤ (recordMedian ν ℓ hp e r : ℝ)} ∧
    (1/2 : ℝ≥0∞) ≤ conditionedLaw ν ℓ
      {X | (recordMedian ν ℓ hp e r : ℝ) ≤ signedCoordinate e (recordIndexPosition ℓ r X)} := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let f : Path d → ℤ := fun X => signedIntegerCoordinate e (recordIndexPosition ℓ r X)
  have hf : Measurable f := (measurable_of_countable (signedIntegerCoordinate e)).comp (measurable_recordIndexPosition ℓ r)
  let : IsProbabilityMeasure ((conditionedLaw ν ℓ).map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  have h := integerMedian_spec ((conditionedLaw ν ℓ).map f)
  rw [Measure.map_apply hf measurableSet_Iic,Measure.map_apply hf measurableSet_Ici] at h
  have he (X : Path d) : signedCoordinate e (recordIndexPosition ℓ r X) = (f X : ℝ) :=
    (signedIntegerCoordinate_cast e _).symm
  simp only [he,Int.cast_le] at ⊢
  exact h

lemma conditioned_firstHit_median_maximum {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d) (H : ℕ) (z : ℝ) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * (1/2 : ℝ≥0∞) * conditionedLaw ν ℓ
      {X | ∃ r, 0 < r ∧ r ≤ H ∧
        z < |signedCoordinate e (recordIndexPosition ℓ r X) -
          (recordMedian ν ℓ (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)) e r : ℝ)|} ≤
    independentConditionedPairLaw ν ℓ
      {P | z < partialSumMax (fun n => commonIncrementProcess ℓ e n P) H} := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  have hs := median_family_symmetrization (conditionedLaw ν ℓ)
    (fun r X => signedCoordinate e (recordIndexPosition ℓ r X))
    (fun r => (measurable_of_countable (signedCoordinate e)).comp (measurable_recordIndexPosition ℓ r))
    (fun r => (recordMedian ν ℓ hp e r : ℝ)) (recordMedian_spec ν ℓ hp e)
    {r | 0 < r ∧ r ≤ H} z
  simp only [Set.mem_ofPred_eq,and_assoc] at hs
  rw [mul_assoc]
  exact (mul_le_mul_right hs _).trans
    (independent_firstHit_pair_maximum ν ℓ htrans height hproj hstep e H z)

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstLayerHitRecordIndexTime
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
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

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_MedianAeConst
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
namespace DirectionalTransience
lemma median_eq_of_ae_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → ℝ) {c b : ℝ} (hF : ∀ᵐ x ∂μ, F x = c)
    (hl : (1/2 : ℝ≥0∞) ≤ μ {x | F x ≤ b})
    (hr : (1/2 : ℝ≥0∞) ≤ μ {x | b ≤ F x}) : b = c := by
  apply le_antisymm
  · by_contra! hh
    have hz : μ {x | b ≤ F x} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hF] with x hx
      simpa only [Set.mem_ofPred_eq,hx,not_le] using hh
    rw [hz] at hr
    norm_num at hr
  · by_contra! hh
    have hz : μ {x | F x ≤ b} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hF] with x hx
      simpa only [Set.mem_ofPred_eq,hx,not_le] using hh
    rw [hz] at hl
    norm_num at hl

lemma recordMedian_zero {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d) :
    recordMedian ν ℓ hp f 0 = 0 := by
  have hx := (conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν)
  have h0 : ∀ᵐ X ∂conditionedLaw ν ℓ, signedCoordinate f (recordIndexPosition ℓ 0 X) = 0 := by
    filter_upwards [hx] with X hX
    simp [recordIndexPosition,recordIndexTime_zero,hX,signedCoordinate]
  have he := median_eq_of_ae_const _ _ h0 (recordMedian_spec ν ℓ hp f 0).1
    (recordMedian_spec ν ℓ hp f 0).2
  exact_mod_cast he

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_MedianTubeFailure
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
namespace DirectionalTransience

lemma measurableSet_medianTubeFailure {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) (z : ℝ) : MeasurableSet (MedianTubeFailure ℓ f b H z) := by
  simp only [MedianTubeFailure,Set.ofPred_exists,Set.ofPred_and]
  exact MeasurableSet.iUnion fun j => (MeasurableSet.const (j ≤ H)).inter
    (measurableSet_lt measurable_const ((((measurable_of_countable (signedCoordinate f)).comp
      (measurable_recordIndexPosition ℓ j)).sub_const (b j)).abs))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ConvolutionCentersClose
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
namespace DirectionalTransience

lemma conditioned_median_max_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (f : Direction d)
    (H : ℕ) {z : ℝ} (hz : 0 < z) :
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    p^2/2 * (conditionedLaw ν ℓ).real {X | ∃ j, 0 < j ∧ j ≤ H ∧
      z < |signedCoordinate f (recordIndexPosition ℓ j X)-(recordMedian ν ℓ hp f j:ℝ)|} ≤
    5*(H:ℝ)/fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) z := by
  dsimp only
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) := independentConditionedPairLaw_probability ν ℓ hp
  have hh := conditioned_firstHit_median_maximum ν ℓ htrans height hproj hstep f H z
  have hh' := ENNReal.toReal_mono (measure_ne_top _ _) hh
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_div,ENNReal.toReal_ofNat,ENNReal.toReal_one] at hh'
  have heq : (annealedLaw ν (NoDrop ℓ 0)).toReal^2*(1/2:ℝ) =
      (annealedLaw ν (NoDrop ℓ 0)).toReal^2/2 := by ring
  rw [heq] at hh'
  exact hh'.trans (independent_common_maximal_probability ν ℓ htrans height hproj hstep f hz H)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SuccessfulAverageTubeTransfer
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
namespace DirectionalTransience

lemma conditioned_median_tube_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ) {z : ℝ} (hz : 0 < z) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    p^2/2 * (conditionedLaw ν ℓ).real
      (MedianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H z) ≤
      5*(H:ℝ)/fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) z := by
  dsimp only
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have he : MedianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H z =ᵐ[conditionedLaw ν ℓ]
      {X | ∃ j, 0 < j ∧ j ≤ H ∧ z < |signedCoordinate f (recordIndexPosition ℓ j X)-(recordMedian ν ℓ hp f j:ℝ)|} := by
    filter_upwards [(conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν)] with X hX
    apply propext
    constructor
    · rintro ⟨j,hj,hbad⟩
      have hj0 : 0 < j := by
        by_contra hn
        have hjz : j = 0 := by omega
        simp [hjz,recordIndexPosition,recordIndexTime_zero,hX,recordMedian_zero,signedCoordinate] at hbad
        linarith
      exact ⟨j,hj0,hj,hbad⟩
    · rintro ⟨j,_,hj,hbad⟩
      exact ⟨j,hj,hbad⟩
  rw [measureReal_congr he]
  exact conditioned_median_max_bound ν ℓ htrans (signedHeight e) (signedHeight_projection e)
    (signedHeight_step_le e) f H hz

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_MixtureSmallMassProbability
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
namespace DirectionalTransience

lemma relativeGoodMass_translation {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (hA : MeasurableSet A) (ω : Environment d) (x : Lattice d) :
    relativeGoodMass ℓ A ω x =
      (quenchedKernel ((fun y => ω (x+y)),0)).real (Aᶜ ∩ NoDrop ℓ 0) := by
  have hm : Measurable (fun X : Path d => fun n => X n-x) := by fun_prop
  have he : ((fun X : Path d => fun n => X n-x) ⁻¹' Aᶜ) ∩ NoDrop ℓ x =
      (fun X : Path d => fun n => X n-x) ⁻¹' (Aᶜ ∩ NoDrop ℓ 0) := by
    rw [Set.preimage_inter,noDrop_translation,add_zero]
  have hmap : (quenchedKernel (ω,x)).map (fun X : Path d => fun n => X n-x) =
      quenchedKernel ((fun y => ω (x+y)),0) := by
    simpa only [add_zero] using quenched_translation ω x 0
  rw [relativeGoodMass,Measure.real,he,← Measure.map_apply hm (hA.compl.inter (measurableSet_noDrop ℓ 0)),hmap]
  rfl

lemma measurable_relativeGoodMass {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (hA : MeasurableSet A) : Measurable (Function.uncurry (relativeGoodMass ℓ A)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hm : Measurable (fun X : Path d => fun n => X n-x) := by fun_prop
  have hs : MeasurableSet (((fun X : Path d => fun n => X n-x) ⁻¹' Aᶜ) ∩ NoDrop ℓ x) :=
    (hA.compl.preimage hm).inter (measurableSet_noDrop ℓ x)
  exact ((Kernel.measurable_coe quenchedKernel hs).comp
      (measurable_id.prodMk measurable_const)).ennreal_toReal

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_QuenchedRegularPathAe
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
namespace DirectionalTransience

lemma quenched_regularPath_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x, ∀ᵐ X ∂quenchedKernel (ω,x), X ∈ RegularPath ℓ x := by
  filter_upwards [quenched_directionallyTransient_ae ν ℓ htrans] with ω hω
  intro x
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x),hω x] with X h0 hn ht
  exact ⟨h0,hn,ht⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_FiniteWordGeometry
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma wordFirstHitTime_zero {d : ℕ} (e : Direction d) (x : Lattice d)
    (w : List (Direction d)) : wordFirstHitTime e x 0 w = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply wordFirstHitTime_le
  simp

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetClipping
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma signedHeight_sub' {d : ℕ} (e : Direction d) (x y : Lattice d) :
    signedHeight e (x-y) = signedHeight e x-signedHeight e y := by
  simp only [signedHeight,Pi.sub_apply]
  split <;> ring

lemma recordOrZeroPrefix_wordFirstHit {d : ℕ} (e : Direction d) (x : Lattice d)
    (X : Path d) (h0 : X 0 = x) (hnn : ∀ n, ∃ f, X (n+1)=X n+step f)
    (w : List (Direction d)) (hw : X ∈ wordCylinder x w) (s a : ℕ)
    (ha : a ≤ w.length)
    (hrec : (fun n => X n-x) ∈ RecordOrZeroPrefix (realPosition (step e)) s a) :
    wordFirstHitTime e x s w = a := by
  by_cases hs : s=0
  · subst s
    have ha0 : a=0 := by simpa [RecordOrZeroPrefix] using hrec
    rw [ha0,wordFirstHitTime_zero]
  · have hr : (fun n => X n-x) ∈ RecordIndexPrefix (realPosition (step e)) s a := by
      simpa only [RecordOrZeroPrefix,ite_eq_right hs] using hrec
    have hstep (n : ℕ) : signedHeight e (X (n+1)-x) ≤ signedHeight e (X n-x)+1 := by
      obtain ⟨g,hg⟩ := hnn n
      rw [signedHeight_sub',signedHeight_sub',hg]
      have hh := signedHeight_step_le e (X n) g
      omega
    have ht := recordCount_eq_height_at_record (realPosition (step e)) (signedHeight e)
      (signedHeight_projection e) (fun n => X n-x) hstep hr.2.1
    have hheight : signedHeight e (X a) = signedHeight e x+s := by
      rw [hr.2.2.1,h0,sub_self] at ht
      simp only [signedHeight_sub'] at ht
      have hz : signedHeight e (0 : Lattice d)=0 := by simp [signedHeight]
      rw [hz] at ht
      omega
    have hwa : signedHeight e x+s ≤ signedHeight e (wordPath x w a) := by
      rw [← hw a ha,hheight]
    apply le_antisymm (wordFirstHitTime_le e x s w hwa)
    by_contra hn
    have hn' : wordFirstHitTime e x s w < a := by omega
    have hlt := hr.2.1 _ hn'
    simp only [signedHeight_projection,signedHeight_sub'] at hlt
    have hlt' : signedHeight e (X (wordFirstHitTime e x s w)) < signedHeight e (X a) := by
      have hh : signedHeight e (X (wordFirstHitTime e x s w))-signedHeight e x <
          signedHeight e (X a)-signedHeight e x := by exact_mod_cast hlt
      omega
    rw [hw _ (hn'.le.trans ha),hheight] at hlt'
    exact hlt'.not_ge (wordFirstHitTime_spec e x s w ⟨a,hwa⟩)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetThreat
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma regularPath_translate_zero {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    {X : Path d} (hX : X ∈ RegularPath ℓ x) :
    (fun n => X n-x) ∈ RegularPath ℓ 0 := by
  refine ⟨by simp only [hX.1,sub_self],?_,?_⟩
  · intro n
    obtain ⟨g,hg⟩ := hX.2.1 n
    refine ⟨g,?_⟩
    dsimp only
    rw [hg]
    abel
  · change X ∈ (fun Z : Path d => fun n => Z n-x) ⁻¹' TransientPaths ℓ
    rw [transientPaths_translation]
    exact hX.2.2

lemma regular_noDrop_hit {d : ℕ} (e : Direction d) (x : Lattice d)
    {X : Path d} (hX : X ∈ RegularPath (realPosition (step e)) x)
    (hD : X ∈ NoDrop (realPosition (step e)) x) (H : ℕ) :
    X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) := by
  by_cases hH : H=0
  · subst H
    exact Set.mem_iUnion.mpr ⟨0,⟨by simp [Upper,hX.1],fun i hi => by omega⟩⟩
  · have hY := regularPath_translate_zero _ x hX
    obtain ⟨n,hn⟩ := noDrop_firstLayerHit_exists e (fun n => X n-x)
      hY.1 hY.2.1 hY.2.2 (Nat.pos_of_ne_zero hH)
    apply Set.mem_iUnion.mpr
    refine ⟨n,⟨?_,?_⟩⟩
    · change dot (realPosition x) (realPosition (step e))+(H:ℝ) ≤
        dot (realPosition (X n)) (realPosition (step e))
      rw [signedHeight_projection,signedHeight_projection]
      have hh := hn.1
      simp only [signedHeight_sub'] at hh
      exact_mod_cast (show signedHeight e x+(H:ℤ) ≤ signedHeight e (X n) by omega)
    · intro i hi
      refine ⟨hD i,?_⟩
      rw [signedHeight_projection,signedHeight_projection]
      have hh := hn.2 i hi
      simp only [signedHeight_sub'] at hh
      exact_mod_cast (show signedHeight e (X i) < signedHeight e x+(H:ℤ) by omega)

lemma regular_noDrop_word_record {d : ℕ} (e : Direction d) (x : Lattice d)
    {X : Path d} (hX : X ∈ RegularPath (realPosition (step e)) x)
    (hD : X ∈ NoDrop (realPosition (step e)) x) (H s : ℕ) (hs : s ≤ H)
    (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H))
    (hw : X ∈ wordCylinder x w.val) :
    wordFirstHitPosition e x s w.val-x =
      recordIndexPosition (realPosition (step e)) s (fun n => X n-x) := by
  by_cases hs0 : s=0
  · subst s
    simp only [wordFirstHitPosition,wordFirstHitTime_zero,wordPath_zero,
      sub_self,recordIndexPosition,recordIndexTime_zero,hX.1]
  · have hY := regularPath_translate_zero _ x hX
    have hYD : (fun n => X n-x) ∈ NoDrop (realPosition (step e)) 0 := by
      change X ∈ (fun Z : Path d => fun n => Z n-x) ⁻¹' NoDrop _ 0
      rwa [noDrop_translation,add_zero]
    obtain ⟨n,hn⟩ := noDrop_firstLayerHit_exists e (fun n => X n-x)
      hY.1 hY.2.1 hY.2.2 (Nat.pos_of_ne_zero hs0)
    have hnlen : n ≤ w.val.length := by
      by_contra! hgt
      have hh := hn.2 _ hgt
      dsimp only at hh
      rw [hw _ le_rfl,signedHeight_sub',wordPath_hit_exact] at hh
      omega
    have hrec := firstLayerHit_recordPrefix e (fun n => X n-x) hY.1 hYD
      hY.2.1 (Nat.pos_of_ne_zero hs0) hn
    have ht := recordOrZeroPrefix_wordFirstHit e x X hX.1 hX.2.1 w.val hw s n hnlen
      (by simpa only [RecordOrZeroPrefix,ite_eq_right hs0] using hrec)
    simp only [wordFirstHitPosition,ht,recordIndexPosition,
      firstLayerHit_recordIndexTime e _ hY.1 hYD hY.2.1 (Nat.pos_of_ne_zero hs0) hn,
      hw n hnlen]

lemma good_noDrop_le_WordEnvelope {d : ℕ} (e f : Direction d) (x : Lattice d)
    (ω : Environment d) (hreg : ∀ᵐ X ∂quenchedKernel (ω,x), X ∈ RegularPath (realPosition (step e)) x)
    (H h : ℕ) (hh : h ≤ H) (b : ℕ → ℝ) (z : ℝ) :
    relativeGoodMass (realPosition (step e)) (MedianTubeFailure (realPosition (step e)) f b H z) ω x ≤
      (rawWordLaw (realPosition (step e)) h ω x).real {w | WordEnvelope e f x h b z w} := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  rw [rawWordLaw,Measure.map_apply measurable_subtype_coe (Set.to_countable _).measurableSet,
    successfulWordLaw_event ω x _ _ (disjoint_strip_upper _ _ _)]
  apply measure_mono_ae
  filter_upwards [hreg] with X hX
  intro hgood
  obtain ⟨w,hw⟩ := (hitWord_cover x _ _ X hX.1 hX.2.1).mp (regular_noDrop_hit e x hX hgood.2 h)
  refine Set.mem_iUnion.mpr ⟨⟨w,?_⟩,hw⟩
  intro s hs
  change |signedCoordinate f (wordFirstHitPosition e x s w.val-x)- b s| ≤ z
  rw [regular_noDrop_word_record e x hX hgood.2 h s hs w hw]
  exact le_of_not_gt fun hbad => hgood.1 ⟨s,hs.trans hh,hbad⟩

lemma tupleEnvelope_budget {d k : ℕ} (e f : Direction d) (x : Fin k → Lattice d)
    (H : ℕ) (b : ℕ → ℝ) (z : ℝ) (w : Fin k → List (Direction d))
    (hw : ∀ j, WordEnvelope e f (x j) H b z (w j)) :
    TupleRelativeBudget e f x H (2*z) w := by
  intro s hs i j
  calc
    _ = |(relativeWordDisplacement e f (x i) s (w i)-b s)-
      (relativeWordDisplacement e f (x j) s (w j)-b s)| := by congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (by linarith [hw i s hs,hw j s hs])

lemma tupleGood_le_relativeBudget {d k : ℕ} (e f : Direction d)
    (ω : Environment d) (hreg : ∀ x, ∀ᵐ X ∂quenchedKernel (ω,x), X ∈ RegularPath (realPosition (step e)) x)
    (H h : ℕ) (hh : h ≤ H) (b : ℕ → ℝ) (z : ℝ) (x : Fin k → Lattice d) :
    (∏ j, relativeGoodMass (realPosition (step e)) (MedianTubeFailure (realPosition (step e)) f b H z) ω (x j)) ≤
      (relativeBudgetWordLaw e f h (2*z) ω x).real Set.univ := by
  calc
    _ ≤ ∏ j, (rawWordLaw (realPosition (step e)) h ω (x j)).real
        {w | WordEnvelope e f (x j) h b z w} :=
      Finset.prod_le_prod (fun _ _ => measureReal_nonneg)
        (fun j _ => good_noDrop_le_WordEnvelope e f (x j) ω (hreg _) H h hh b z)
    _ = (rawTupleWordLaw (realPosition (step e)) h ω x).real
        {w | ∀ j, WordEnvelope e f (x j) h b z (w j)} := by
      have he := Measure.pi_pi (fun j => rawWordLaw (realPosition (step e)) h ω (x j))
        (fun j => {w | WordEnvelope e f (x j) h b z w})
      have hr := congrArg ENNReal.toReal he
      simpa only [rawTupleWordLaw,Set.pi,Set.mem_univ,forall_true_left,Set.mem_ofPred,
        ENNReal.toReal_prod,Measure.real] using hr.symm
    _ ≤ _ := by
      rw [relativeBudgetWordLaw,measureReal_restrict_apply MeasurableSet.univ,Set.univ_inter]
      exact measureReal_mono fun w hw => tupleEnvelope_budget e f x h b z w hw

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma relativeBadMass_eq {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Lattice d) : relativeBadMass ℓ A ω x =
      (quenchedKernel (ω,x)).real (((fun X : Path d => fun n => X n-x) ⁻¹' A) ∩ NoDrop ℓ x) := by
  simp only [relativeBadMass,relativeGoodMass,compl_compl]

lemma good_add_bad_noDrop {d : ℕ} (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A)
    (ω : Environment d) (x : Lattice d) :
    relativeGoodMass ℓ A ω x + relativeBadMass ℓ A ω x = (noDropQuenched ℓ x ω).toReal := by
  have ht : MeasurableSet ((fun X : Path d => fun n => X n-x) ⁻¹' A) := hA.preimage (by fun_prop)
  have he : NoDrop ℓ x \ ((fun X : Path d => fun n => X n-x) ⁻¹' A) =
      ((fun X : Path d => fun n => X n-x) ⁻¹' Aᶜ) ∩ NoDrop ℓ x := by
    ext X
    change (X ∈ NoDrop ℓ x ∧ ¬ (fun n => X n-x) ∈ A) ↔
      (¬ (fun n => X n-x) ∈ A) ∧ X ∈ NoDrop ℓ x
    tauto
  simpa only [relativeGoodMass,relativeBadMass_eq,noDropQuenched,he,
    Set.inter_comm,Measure.real] using
      (measureReal_sdiff_add_inter (μ := quenchedKernel (ω,x)) (s := NoDrop ℓ x) ht)

lemma relativeBadMass_nonneg {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Lattice d) : 0 ≤ relativeBadMass ℓ A ω x := measureReal_nonneg

lemma relativeBadMass_le_one {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Lattice d) : relativeBadMass ℓ A ω x ≤ 1 := measureReal_le_one

lemma relativeGoodMass_le_noDrop {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Lattice d) : relativeGoodMass ℓ A ω x ≤ (noDropQuenched ℓ x ω).toReal :=
  measureReal_mono Set.inter_subset_right

lemma measurable_relativeBadMass {d : ℕ} (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A) :
    Measurable (Function.uncurry (relativeBadMass ℓ A)) := measurable_relativeGoodMass ℓ Aᶜ hA.compl

lemma relativeBadMass_mean {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A) (x : Lattice d) :
    (∫ ω, relativeBadMass ℓ A ω x ∂environmentLaw ν) = (annealedLaw ν).real (A ∩ NoDrop ℓ 0) := by
  let F : Environment d → ℝ := fun ω => (quenchedKernel (ω,0)).real (A ∩ NoDrop ℓ 0)
  have hF : Measurable F := ((Kernel.measurable_coe quenchedKernel
    (hA.inter (measurableSet_noDrop ℓ 0))).comp (measurable_id.prodMk measurable_const)).ennreal_toReal
  have he (ω : Environment d) : relativeBadMass ℓ A ω x = F (fun y => ω (x+y)) := by
    simpa only [relativeBadMass,F,compl_compl] using relativeGoodMass_translation ℓ Aᶜ hA.compl ω x
  simp_rw [he]
  have hm : Measurable (fun ω : Environment d => fun y => ω (x+y)) := by fun_prop
  rw [← integral_map hm.aemeasurable hF.aestronglyMeasurable,environment_translation]
  change (∫ ω, (quenchedKernel (ω,0) (A ∩ NoDrop ℓ 0)).toReal ∂environmentLaw ν) = _
  rw [Measure.real,annealed_apply ν (hA.inter (measurableSet_noDrop ℓ 0))]
  exact integral_toReal ((Kernel.measurable_coe quenchedKernel (hA.inter (measurableSet_noDrop ℓ 0))).comp
    (measurable_id.prodMk measurable_const)).aemeasurable (ae_of_all _ fun _ => measure_lt_top _ _)

lemma measurable_sum_relativeBadMass {d k : ℕ} (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A) :
    Measurable (fun p : Environment d × (Fin k → Lattice d) => ∑ j, relativeBadMass ℓ A p.1 (p.2 j)) := by
  apply Finset.measurable_sum
  intro j _
  exact (measurable_relativeBadMass ℓ A hA).comp
    (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

lemma sum_relativeBadMass_bounds {d k : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Fin k → Lattice d) :
    0 ≤ ∑ j, relativeBadMass ℓ A ω (x j) ∧ ∑ j, relativeBadMass ℓ A ω (x j) ≤ k := by
  exact ⟨Finset.sum_nonneg (fun _ _ => relativeBadMass_nonneg _ _ _ _),
    (Finset.sum_le_sum (fun _ _ => relativeBadMass_le_one _ _ _ _)).trans_eq (by simp)⟩

lemma tupleBadMass_nonneg {d k : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) : 0 ≤ tupleBadMass ℓ A π ω :=
  integral_nonneg fun x => (sum_relativeBadMass_bounds ℓ A ω x).1

lemma integrable_sum_relativeBadMass {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A)
    (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π] :
    Integrable (fun p : Environment d × (Fin k → Lattice d) => ∑ j, relativeBadMass ℓ A p.1 (p.2 j))
      ((environmentLaw ν).prod π) := by
  apply (integrable_const (k:ℝ)).mono' (measurable_sum_relativeBadMass ℓ A hA).aestronglyMeasurable
  exact ae_of_all _ fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sum_relativeBadMass_bounds ℓ A p.1 p.2).1]
    exact (sum_relativeBadMass_bounds ℓ A p.1 p.2).2

lemma tupleBadMass_mean {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A)
    (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] :
    (∫ ω, tupleBadMass ℓ A π ω ∂environmentLaw ν) = (k:ℝ)*(annealedLaw ν).real (A ∩ NoDrop ℓ 0) := by
  change (∫ ω, ∫ x, ∑ j, relativeBadMass ℓ A ω (x j) ∂π ∂environmentLaw ν) = _
  rw [integral_integral_swap (integrable_sum_relativeBadMass ν ℓ A hA π)]
  have he (x : Fin k → Lattice d) :
      (∫ ω, ∑ j, relativeBadMass ℓ A ω (x j) ∂environmentLaw ν) =
        (k:ℝ)*(annealedLaw ν).real (A ∩ NoDrop ℓ 0) := by
    rw [integral_finsetSum]
    · simp only [relativeBadMass_mean ν ℓ A hA]
      simp
    · intro j _
      apply (integrable_const (1:ℝ)).mono'
        ((measurable_relativeBadMass ℓ A hA).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      exact ae_of_all _ fun ω => by
        change ‖relativeBadMass ℓ A ω (x j)‖ ≤ 1
        rw [Real.norm_eq_abs,abs_of_nonneg (relativeBadMass_nonneg _ _ _ _)]
        exact relativeBadMass_le_one _ _ _ _
  simp_rw [he]
  simp

lemma product_noDrop_le_good_bad {d k : ℕ} (ℓ : Vector d) (A : Set (Path d)) (hA : MeasurableSet A)
    (ω : Environment d) (x : Fin k → Lattice d) :
    noDropProduct ℓ x ω ≤ (∏ j, relativeGoodMass ℓ A ω (x j)) +
      ∑ j, relativeBadMass ℓ A ω (x j) := by
  have hh := prod_difference_bound Finset.univ
    (fun j : Fin k => (noDropQuenched ℓ (x j) ω).toReal)
    (fun j => relativeGoodMass ℓ A ω (x j)) le_rfl
    (fun j _ => ⟨measureReal_nonneg,relativeGoodMass_le_noDrop _ _ _ _,
      noDropQuenched_toReal_le_one _ _ _⟩)
  have he (j : Fin k) : (noDropQuenched ℓ (x j) ω).toReal-relativeGoodMass ℓ A ω (x j) =
      relativeBadMass ℓ A ω (x j) := by linarith [good_add_bad_noDrop ℓ A hA ω (x j)]
  simpa only [noDropProduct,one_pow,one_mul,he] using hh

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SingleThreat
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma noDropMass_le_budget_bad {d k : ℕ} (e f : Direction d) (ω : Environment d)
    (hreg : ∀ x, ∀ᵐ X ∂quenchedKernel (ω,x), X ∈ RegularPath (realPosition (step e)) x)
    (H h : ℕ) (hh : h ≤ H) (b : ℕ → ℝ) (z : ℝ)
    (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π] :
    (∫ x, noDropProduct (realPosition (step e)) x ω ∂π) ≤
      relativeBudgetMass e f h (2*z) π ω +
        tupleBadMass (realPosition (step e)) (MedianTubeFailure (realPosition (step e)) f b H z) π ω := by
  let A := MedianTubeFailure (realPosition (step e)) f b H z
  have hI (F : (Fin k → Lattice d) → ℝ) (B : ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ B) : Integrable F π := by
    apply (integrable_const B).mono' (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hF x).1]; exact (hF x).2
  have hq := hI (fun x => noDropProduct (realPosition (step e)) x ω) 1
    (fun x => noDropProduct_bounds _ x ω)
  have hm := hI (fun x => (relativeBudgetWordLaw e f h (2*z) ω x).real Set.univ) 1
    (fun x => ⟨measureReal_nonneg,by
      exact (ENNReal.toReal_mono ENNReal.one_ne_top (relativeBudgetWordLaw_le_one e f h (2*z) ω x)).trans_eq ENNReal.toReal_one⟩)
  have hb := hI (fun x => ∑ j, relativeBadMass (realPosition (step e)) A ω (x j)) k
    (fun x => sum_relativeBadMass_bounds _ A ω x)
  change _ ≤ (∫ x, (relativeBudgetWordLaw e f h (2*z) ω x).real Set.univ ∂π) +
    ∫ x, ∑ j, relativeBadMass (realPosition (step e)) A ω (x j) ∂π
  rw [← integral_add hm hb]
  apply integral_mono hq (hm.add hb)
  intro x
  exact (product_noDrop_le_good_bad _ A (measurableSet_medianTubeFailure _ f b H z) ω x).trans
    (add_le_add (tupleGood_le_relativeBudget e f ω hreg H h hh b z x) le_rfl)

lemma budgetThreatEvent_subset_ae {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ) (b : ℕ → ℝ) (z s : ℝ) (π : Measure (Fin k → Lattice d)) [IsFiniteMeasure π] :
    budgetThreatEvent e f H (2*z) π s ≤ᵐ[environmentLaw ν]
      (({ω | (∫ x, noDropProduct (realPosition (step e)) x ω ∂π) < 2*s} ∪
      {ω | s < tupleBadMass (realPosition (step e)) (MedianTubeFailure (realPosition (step e)) f b H z) π ω}) : Set (Environment d)) := by
  filter_upwards [quenched_regularPath_ae ν _ htrans] with ω hω
  rintro ⟨h,hh,hbad⟩
  by_cases hq : (∫ x, noDropProduct (realPosition (step e)) x ω ∂π) < 2*s
  · exact Or.inl hq
  · right
    have hm := noDropMass_le_budget_bad e f ω hω H h hh b z π
    change s < _
    linarith

lemma single_budget_threat_bound {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ) (b : ℕ → ℝ) (z : ℝ) {s : ℝ} (hs : 0 < s)
    (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] :
    (environmentLaw ν).real (budgetThreatEvent e f H (2*z) π s) ≤
      (environmentLaw ν).real {ω | (∫ x, noDropProduct (realPosition (step e)) x ω ∂π) < 2*s} +
      (k:ℝ)*(annealedLaw ν).real (MedianTubeFailure (realPosition (step e)) f b H z ∩ NoDrop (realPosition (step e)) 0)/s := by
  let A := MedianTubeFailure (realPosition (step e)) f b H z
  have hA := measurableSet_medianTubeFailure (realPosition (step e)) f b H z
  have hm := ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (budgetThreatEvent_subset_ae ν e f htrans H b z s π))
  have hu := measureReal_union_le (μ := environmentLaw ν)
    {ω | (∫ x, noDropProduct (realPosition (step e)) x ω ∂π) < 2*s}
    {ω | s < tupleBadMass (realPosition (step e)) A π ω}
  apply hm.trans (hu.trans (add_le_add le_rfl ?_))
  have hb := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (environmentLaw ν) fun ω => tupleBadMass_nonneg (realPosition (step e)) A π ω)
    (integrable_sum_relativeBadMass ν (realPosition (step e)) A hA π).integral_prod_left s
  rw [tupleBadMass_mean ν (realPosition (step e)) A hA π] at hb
  apply (le_div_iff₀ hs).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (show {ω | s < tupleBadMass (realPosition (step e)) A π ω} ⊆ {ω | s ≤ tupleBadMass (realPosition (step e)) A π ω} from fun ω h => show s ≤ tupleBadMass (realPosition (step e)) A π ω from (show s < tupleBadMass (realPosition (step e)) A π ω from h).le)) hs.le).trans hb

lemma annealed_noDrop_event_le_conditioned {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    (annealedLaw ν).real (A ∩ NoDrop ℓ 0) ≤ (conditionedLaw ν ℓ).real A := by
  have he : annealedLaw ν (NoDrop ℓ 0)*conditionedLaw ν ℓ A = annealedLaw ν (A ∩ NoDrop ℓ 0) := by
    rw [conditionedLaw,Measure.smul_apply,Measure.restrict_apply hA,smul_eq_mul,
      ← mul_assoc,ENNReal.mul_inv_cancel hp (measure_ne_top _ _),one_mul]
  have he' := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_mul] at he'
  change ((annealedLaw ν) (A ∩ NoDrop ℓ 0)).toReal ≤ _
  rw [← he']
  exact mul_le_of_le_one_left ENNReal.toReal_nonneg (by exact measureReal_le_one)

lemma annealed_median_failure_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ) {z : ℝ} (hz : 0 < z) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν).real (NoDrop ℓ 0)
    (annealedLaw ν).real (MedianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H z ∩ NoDrop ℓ 0) ≤
      (10/p^2)*(H:ℝ)/fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) z := by
  dsimp only
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hp0 : 0 < (annealedLaw ν).real (NoDrop ℓ 0) := ENNReal.toReal_pos hp (measure_ne_top _ _)
  let A := MedianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H z
  have hA := measurableSet_medianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H z
  have ha := annealed_noDrop_event_le_conditioned ν ℓ hp A hA
  have hb := conditioned_median_tube_bound ν e f htrans H hz
  dsimp only at hb
  have hc : ((annealedLaw ν).real (NoDrop ℓ 0))^2/2*(annealedLaw ν).real (A ∩ NoDrop ℓ 0) ≤
      5*(H:ℝ)/fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) z :=
    (mul_le_mul_of_nonneg_left ha (by positivity)).trans hb
  have hi : (annealedLaw ν).real (A ∩ NoDrop ℓ 0) ≤
      (5*(H:ℝ)/fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) z) /
      (((annealedLaw ν).real (NoDrop ℓ 0))^2/2) := by
    apply (le_div_iff₀ (show 0 < ((annealedLaw ν).real (NoDrop ℓ 0))^2/2 by positivity)).mpr
    nlinarith only [hc]
  convert hi using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [A,ℓ])
  ring

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_FreshThreat
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem fresh_budget_threat_bound_oai {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ lam C D : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < C ∧ 0 < D ∧
      ∀ Bstar : ℝ, 0 < Bstar → ∀ k : ℕ, 1 ≤ k → ∃ G : ℕ,
      ∀ (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π],
        (∀ᵐ x ∂π, Pairwise fun i j => (G : ℤ) ≤ |x i f.1 - x j f.1|) →
        ∀ (H : ℕ) (z s : ℝ), 0 < z → Real.exp (-Bstar) ≤ s →
        (environmentLaw ν).real (budgetThreatEvent e f H (2*z) π s) ≤
          Real.exp (C*k)*s^lam + D*k*H /
            fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
              (commonIncrementProcess (realPosition (step e)) f 0) z / s := by
  obtain ⟨lam,C,hlam,hlam1,hC,hinv⟩ :=
    separated_initial_inverse_moment ν hue (realPosition (step e)) (signed_direction_unit e) htrans f.1
  let p := (annealedLaw ν).real (NoDrop (realPosition (step e)) 0)
  have hp : 0 < p := ENNReal.toReal_pos
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans)) (measure_ne_top _ _)
  refine ⟨lam,C,10/p^2,hlam,hlam1,hC,by positivity,?_⟩
  intro Bstar hB k hk
  obtain ⟨G,hG⟩ := hinv Bstar hB k hk
  refine ⟨G,?_⟩
  intro π hπ hsep H z s hz hs
  have hs0 : 0 < s := (Real.exp_pos _).trans_le hs
  let hp' := ne_of_gt (noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans)
  let b := fun j => (recordMedian ν (realPosition (step e)) hp' f j:ℝ)
  have hq : (environmentLaw ν).real
      {ω | (∫ x, noDropProduct (realPosition (step e)) x ω ∂π) < 2*s} ≤ Real.exp (C*k)*s^lam := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hG π hsep s hs)
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hs0.le _))] at h
    exact h
  have hf := annealed_median_failure_bound ν e f htrans H hz
  dsimp only at hf
  have hb := single_budget_threat_bound ν e f htrans H b z hs0 π
  apply hb.trans (add_le_add hq ?_)
  apply (div_le_div_iff_of_pos_right hs0).mpr
  calc
    _ ≤ (k:ℝ)*((10/p^2)*(H:ℝ)/fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) z) :=
      mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg k)
    _ = _ := by ring

end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.fresh_budget_threat_bound_oai := @OAI.DirectionalTransience.fresh_budget_threat_bound_oai
