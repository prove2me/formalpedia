-- Prove2me | solution 1 for OAI.DirectionalTransience.actual_profile_tail_decorrelation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:03:40.329263+00:00
-- url     : https://prove2.me/submissions/f276f859-b9e1-4abd-baa3-386de28674a1

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal004
import Definitions.Def_OAIQ242Bal007
import Theorems.Thm_OAI_DirectionalTransience_actual_outward_log_bound

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

lemma stayUntil_split {d : ℕ} (S : Set (Lattice d)) (n m : ℕ) :
    StayUntil S (n + m) = StayUntil S n ∩ FutureEvent (fun _ => StayUntil S m) n := by
  ext X
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), fun j hj => h (n + j) (by omega)⟩
  · rintro ⟨h, h'⟩ i hi
    by_cases hin : i ≤ n
    · exact h i hin
    · have he : n + (i - n) = i := by omega
      simpa only [he] using h' (i - n) (by omega)

lemma quenched_stayUntil_add {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S : Set (Lattice d)) (n m : ℕ) :
    quenchedKernel (ω, x) (StayUntil S (n + m)) =
      ∫⁻ X in StayUntil S n, quenchedKernel (ω, X n) (StayUntil S m)
        ∂quenchedKernel (ω, x) := by
  let A : Set ((i : Finset.Iic n) → Lattice d) := {f | ∀ i, f i ∈ S}
  have hA : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' A = StayUntil S n := by
    ext X
    constructor
    · intro h i hi
      exact h ⟨i, Finset.mem_Iic.mpr hi⟩
    · intro h i
      exact h i (Finset.mem_Iic.mp i.2)
  rw [stayUntil_split, ← hA]
  exact quenched_past_future ω x n A (fun _ => StayUntil S m)
    (fun _ => measurableSet_stayUntil S m)

lemma quenched_stayUntil_block_bound {d : ℕ} (ω : Environment d)
    (S : Set (Lattice d)) (N : ℕ) (c : ℝ≥0∞)
    (hc : ∀ y, quenchedKernel (ω, y) (StayUntil S N) ≤ c)
    (x : Lattice d) (k : ℕ) :
    quenchedKernel (ω, x) (StayUntil S (k * N)) ≤ c ^ k := by
  induction k with
  | zero => simpa using (prob_le_one (μ := quenchedKernel (ω, x)) (s := StayUntil S 0))
  | succ k ih =>
    rw [Nat.succ_mul, quenched_stayUntil_add]
    calc
      _ ≤ ∫⁻ _ in StayUntil S (k * N), c ∂quenchedKernel (ω, x) :=
        lintegral_mono fun X => hc (X (k * N))
      _ = c * quenchedKernel (ω, x) (StayUntil S (k * N)) := by simp
      _ ≤ c * c ^ k := mul_le_mul' le_rfl ih
      _ = c ^ (k + 1) := (pow_succ' c k).symm

lemma hitThrough_subset_hit {d : ℕ} (S T : Set (Lattice d)) (n : ℕ) :
    HitThrough S T n ⊆ Hit S T := by
  intro X h
  obtain ⟨k, _, hk⟩ := Set.mem_iUnion₂.mp h
  exact Set.mem_iUnion.mpr ⟨k, hk⟩

lemma hit_subset_hitThrough_union_stayUntil {d : ℕ} (S T : Set (Lattice d)) (n : ℕ) :
    Hit S T ⊆ HitThrough S T n ∪ StayUntil S n := by
  intro X h
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
  by_cases hkn : k ≤ n
  · exact Or.inl (Set.mem_iUnion₂.mpr ⟨k, hkn, hk⟩)
  · exact Or.inr (fun j hj => hk.2 j (by omega))

lemma quenched_hit_truncation {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (n : ℕ) :
    quenchedKernel (ω, x) (Hit S T) ≤
      quenchedKernel (ω, x) (HitThrough S T n) +
        quenchedKernel (ω, x) (StayUntil S n) :=
  (measure_mono (hit_subset_hitThrough_union_stayUntil S T n)).trans (measure_union_le _ _)

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

lemma quenched_hitThrough_locality {d : ℕ} (ω η : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (n : ℕ) (hωη : Set.EqOn ω η (LatticeBall x n)) :
    quenchedKernel (ω, x) (HitThrough S T n) =
      quenchedKernel (η, x) (HitThrough S T n) := by
  let C : Set ((i : Finset.Iic n) → Lattice d) :=
    {f | ∃ (k : ℕ) (hk : k ≤ n), f ⟨k, Finset.mem_Iic.mpr hk⟩ ∈ T ∧
      ∀ (j : ℕ) (hj : j < k), f ⟨j, Finset.mem_Iic.mpr (hj.le.trans hk)⟩ ∈ S}
  have hC : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C = HitThrough S T n := by
    ext X
    constructor
    · rintro ⟨k, hk, hT, hS⟩
      exact Set.mem_iUnion₂.mpr ⟨k, hk, hT, hS⟩
    · intro h
      obtain ⟨k, hk, hT, hS⟩ := Set.mem_iUnion₂.mp h
      exact ⟨k, hk, hT, hS⟩
  rw [← hC]
  exact quenched_prefix_locality ω η x n hωη C

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightSlab
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

lemma hit_concatenation {d : ℕ} {S₁ T₁ S₂ T₂ S : Set (Lattice d)}
    (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) :
    (⋃ n, HitAt S₁ T₁ n ∩ FutureEvent (fun _ => Hit S₂ T₂) n) ⊆ Hit S T₂ := by
  rintro X hX
  obtain ⟨n, hn, hfuture⟩ := Set.mem_iUnion.mp hX
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hfuture
  apply Set.mem_iUnion.mpr
  refine ⟨n + m, hm.1, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · exact h₁ (hn.2 j hjn)
  · have hn : n ≤ j := by omega
    have hsub : j - n < m := by omega
    have := h₂ (hm.2 (j - n) hsub)
    simpa only [Nat.add_sub_of_le hn] using this

lemma hitKernel_comp_le {d : ℕ} (ω : Environment d) (x : Lattice d)
    {S₁ T₁ S₂ T₂ S : Set (Lattice d)}
    (hST₁ : Disjoint S₁ T₁) (hST₂ : Disjoint S₂ T₂) (hST : Disjoint S T₂)
    (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) (U : Set (Lattice d)) :
    (∫⁻ y, hitKernel S₂ T₂ (ω, y) U ∂hitKernel S₁ T₁ (ω, x)) ≤
      hitKernel S T₂ (ω, x) U := by
  simp_rw [hitKernel_apply_eq_hit hST₂ U]
  rw [hitKernel_future ω x hST₁ (fun _ => Hit S₂ (T₂ ∩ U))
    (fun _ => measurableSet_hit _ _), hitKernel_apply_eq_hit hST U]
  exact measure_mono (hit_concatenation h₁ h₂)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FixedPairSuffix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_EndpointPrefix
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPairEndpoint
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma measurable_prefixEndpoint {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℕ) :
    Measurable (prefixEndpoint ℓ x H) := by
  exact measurable_const.add ((measurable_recordIndexPosition ℓ H).comp
    (Measurable.of_eval fun j => (measurable_of_countable (fun u : Lattice d => u-x)).comp (measurable_pi_apply j)))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_RawPairKernel
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma hit_prefixEndpoint_iff {d : ℕ} (e : Direction d) (x : Lattice d)
    {H : ℕ} (hH : 0 < H) (A : Set (Lattice d)) (X : Path d)
    (h0 : X 0=x) (hnn : ∀ n, ∃ g, X (n+1)=X n+step g) :
    X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H ∩ A) ↔
      X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∧
      prefixEndpoint (realPosition (step e)) x H X ∈ A := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp h
    have hh : X ∈ HitAt (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) n := ⟨hn.1.1,hn.2⟩
    refine ⟨Set.mem_iUnion.mpr ⟨n,hh⟩,?_⟩
    dsimp [prefixEndpoint]
    rw [coordinate_hitAt_record e x X h0 hnn hH hh]
    simpa only [add_sub_cancel] using hn.1.2
  · rintro ⟨h,hA⟩
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp h
    dsimp [prefixEndpoint] at hA
    rw [coordinate_hitAt_record e x X h0 hnn hH hn] at hA
    exact Set.mem_iUnion.mpr ⟨n,⟨hn.1,by simpa only [add_sub_cancel] using hA⟩,hn.2⟩

lemma hitKernel_eq_map_prefixEndpoint {d : ℕ} (e : Direction d) (x : Lattice d)
    {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    hitKernel (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) (ω,x) =
      ((quenchedKernel (ω,x)).restrict (Hit (Strip (realPosition (step e)) x H)
        (Upper (realPosition (step e)) x H))).map (prefixEndpoint (realPosition (step e)) x H) := by
  apply Measure.ext
  intro A hA
  rw [hitKernel_apply_eq_hit (disjoint_strip_upper _ _ _),Measure.map_apply
    (measurable_prefixEndpoint _ _ _) hA,Measure.restrict_apply ((measurable_prefixEndpoint _ _ _) hA)]
  apply measure_congr
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  have := hit_prefixEndpoint_iff e x hH A X h0 hnn
  apply propext
  exact this.trans and_comm

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPairLocality
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma variablePairHitKernel_apply {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) :
    variablePairHitKernel ℓ H (ω,x) = rawPairEndpointLaw ℓ H ω x := by
  simp only [variablePairHitKernel,Kernel.prod_apply,Kernel.comap_apply]
  rfl

lemma rawPairEndpointLaw_total_le_one {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) :
    rawPairEndpointLaw ℓ H ω x Set.univ ≤ 1 := by
  rw [rawPairEndpointLaw,←Set.univ_prod_univ,Measure.prod_prod]
  exact (mul_le_of_le_one_left (by positivity)
    (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _)).trans
      (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstHitUpward
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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

lemma single_step_dirac_le_hitKernel {d : ℕ} (ω : Environment d) (x : Lattice d)
    (e : Direction d) {S T : Set (Lattice d)} (hST : Disjoint S T)
    (hx : x ∈ S) (he : x+step e ∈ T) :
    ((ω x).1 e : ℝ≥0∞) • Measure.dirac (x+step e) ≤ hitKernel S T (ω,x) := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  rw [Measure.smul_apply, smul_eq_mul]
  by_cases hu : x+step e ∈ U
  · rw [Measure.dirac_apply_of_mem hu, mul_one,hitKernel_apply_eq_hit hST]
    have hsub : wordCylinder x [e] ⊆ Hit S (T ∩ U) := by
      intro X hX
      apply Set.mem_iUnion.mpr
      refine ⟨1,?_,?_⟩
      · have h1 := hX 1 (by simp)
        simp only [wordPath] at h1
        simpa only [h1] using (show x+step e ∈ T ∩ U from ⟨he,hu⟩)
      · intro j hj
        have hj0 : j=0 := by omega
        subst j
        have h0 := hX 0 (by simp)
        simpa only [wordPath_zero] using h0 ▸ hx
    have hm := measure_mono (μ := quenchedKernel (ω,x)) hsub
    simpa only [quenched_wordCylinder,wordWeight,mul_one,ENNReal.ofReal_coe_nnreal] using hm
  · rw [Measure.dirac_apply' _ hU,Set.indicator_of_notMem hu,mul_zero]
    exact bot_le

lemma elliptic_single_step_le_hitKernel {d : ℕ} (ω : Environment d) (x : Lattice d)
    (e : Direction d) {κ : ℝ≥0} (hκ : κ ≤ (ω x).1 e)
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (hx : x ∈ S) (he : x+step e ∈ T) :
    (κ : ℝ≥0∞) • Measure.dirac (x+step e) ≤ hitKernel S T (ω,x) := by
  intro U
  exact (mul_le_mul_left (ENNReal.coe_le_coe.mpr hκ) ((Measure.dirac (x+step e)) U)).trans
    ((single_step_dirac_le_hitKernel ω x e hST hx he) U)

lemma hitKernel_direct_step_retention {d : ℕ} (ω : Environment d) (x : Lattice d)
    (e : Direction d) {κ : ℝ≥0} (hκ : ∀ y, κ ≤ (ω y).1 e)
    {S₁ T₁ S₂ T₂ S : Set (Lattice d)}
    (hST₁ : Disjoint S₁ T₁) (hST₂ : Disjoint S₂ T₂) (hST : Disjoint S T₂)
    (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S)
    (hy : ∀ᵐ y ∂hitKernel S₁ T₁ (ω,x), y ∈ S₂ ∧ y+step e ∈ T₂) :
    (κ : ℝ≥0∞) • (hitKernel S₁ T₁ (ω,x)).map (fun y => y+step e) ≤
      hitKernel S T₂ (ω,x) := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  have hm : Measurable (fun y : Lattice d => y+step e) := measurable_of_countable _
  rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply hm hU]
  have heq : (κ : ℝ≥0∞)*hitKernel S₁ T₁ (ω,x) ((fun y => y+step e) ⁻¹' U) =
      ∫⁻ y, ((κ : ℝ≥0∞) • Measure.dirac (y+step e)) U ∂hitKernel S₁ T₁ (ω,x) := by
    simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ hU]
    rw [lintegral_const_mul _ (measurable_of_countable _)]
    congr 1
    rw [← lintegral_indicator_one (hm hU)]
    apply lintegral_congr
    intro y
    by_cases hy : y+step e ∈ U <;> simp [hy]
  rw [heq]
  apply le_trans _ (hitKernel_comp_le ω x hST₁ hST₂ hST h₁ h₂ U)
  apply lintegral_mono_ae
  filter_upwards [hy] with y hy
  exact (elliptic_single_step_le_hitKernel ω y e (hκ y) hST₂ hy.1 hy.2) U

lemma coordinate_hitKernel_upward_retention {d : ℕ} (e : Direction d) (x : Lattice d)
    (H : ℕ) (ω : Environment d) {κ : ℝ≥0} (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ : ℝ≥0∞) • (hitKernel (Strip (realPosition (step e)) x H)
        (Upper (realPosition (step e)) x H) (ω,x)).map (fun y => y+step e) ≤
      hitKernel (Strip (realPosition (step e)) x (H+1))
        (Upper (realPosition (step e)) x (H+1)) (ω,x) := by
  apply hitKernel_direct_step_retention ω x e hκ (disjoint_strip_upper _ _ _)
    (disjoint_strip_upper _ _ _) (disjoint_strip_upper _ _ _) ?_ (fun _ h => h) ?_
  · intro y hy
    exact ⟨hy.1,by have := hy.2; dsimp [Strip] at * <;> linarith⟩
  · filter_upwards [coordinate_hitKernel_supported e x H ω] with y hy
    have hh : dot (realPosition y) (realPosition (step e)) =
        dot (realPosition x) (realPosition (step e))+(H:ℝ) := by
      simp only [signedHeight_projection]
      exact_mod_cast hy
    constructor
    · constructor
      · rw [hh]
        exact le_add_of_nonneg_right (Nat.cast_nonneg H)
      · rw [hh]
        linarith
    · change _ ≤ dot (realPosition (y+step e)) (realPosition (step e))
      rw [dot_realPosition_add,signed_direction_unit,hh]
      linarith
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairUpwardRetention
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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

lemma rawPairEndpointLaw_upward {d : ℕ} (e : Direction d)
    (H : ℕ) (ω : Environment d) (x : Lattice d × Lattice d)
    {κ : ℝ≥0} (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ : ℝ≥0∞)^2 • (rawPairEndpointLaw (realPosition (step e)) H ω x).map (pairUp e) ≤
      rawPairEndpointLaw (realPosition (step e)) (H+1) ω x := by
  let ℓ := realPosition (step e)
  have hfinite (y : Lattice d) (h : ℕ) :
      IsFiniteMeasure (hitKernel (Strip ℓ y h) (Upper ℓ y h) (ω,y)) :=
    ⟨lt_of_le_of_lt (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _) ENNReal.one_lt_top⟩
  let := hfinite x.1 H
  let := hfinite x.2 H
  let := hfinite x.1 (H+1)
  let := hfinite x.2 (H+1)
  have hp := Measure.prod_mono (coordinate_hitKernel_upward_retention e x.1 H ω hκ)
    (coordinate_hitKernel_upward_retention e x.2 H ω hκ)
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,←pow_two,
    Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)] at hp
  unfold pairUp
  simpa only [rawPairEndpointLaw,Prod.map_def,Nat.cast_add,Nat.cast_one] using hp

lemma pairUp_preserves_gap {d : ℕ} (e f : Direction d) (x : Lattice d × Lattice d) :
    signedCoordinate f ((pairUp e x).2-(pairUp e x).1) = signedCoordinate f (x.2-x.1) := by
  dsimp [pairUp]
  congr 1
  abel

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_CanonicalLogExcess
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurable_canonicalLogExcess {Ω : Type*} [MeasurableSpace Ω]
    (A : ℝ) (p : ℕ → Ω → ℝ) (hp : ∀ n, Measurable (p n)) :
    Measurable (canonicalLogExcess A p) := by
  unfold canonicalLogExcess
  apply Measurable.ennreal_toReal
  apply Measurable.iSup
  intro n
  exact ((hp n).log.neg.sub_const _).ennreal_ofReal

lemma canonicalLogExcess_nonneg {Ω : Type*} (A : ℝ) (p : ℕ → Ω → ℝ) (ω : Ω) :
    0 ≤ canonicalLogExcess A p ω := ENNReal.toReal_nonneg

lemma canonicalLogExcess_bounds {Ω : Type*} {A D W : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hW : 0 ≤ W) (p : ℕ → Ω → ℝ) (ω : Ω)
    (hp : ∀ n, -Real.log (p n ω) ≤ A*Real.log ((n:ℝ)+2)+D*(W+1)) :
    canonicalLogExcess A p ω ≤ D*(W+1) ∧
    (∀ n, -Real.log (p n ω) ≤ 2*A*Real.log ((n:ℝ)+2)+canonicalLogExcess A p ω) := by
  let S := ⨆ n : ℕ, ENNReal.ofReal (-Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2))
  have hS : S ≤ ENNReal.ofReal (D*(W+1)) := by
    apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    have hn := hp n
    have hl : 0 ≤ Real.log ((n:ℝ)+2) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
    have hm : 0 ≤ A*Real.log ((n:ℝ)+2) := mul_nonneg hA hl
    linarith
  have hSt : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hS
  constructor
  · have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hS
    simpa only [canonicalLogExcess,S,ENNReal.toReal_ofReal (show 0 ≤ D*(W+1) by positivity)] using hh
  · intro n
    have hn : ENNReal.ofReal (-Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2)) ≤ S := le_iSup (fun k : ℕ => ENNReal.ofReal (-Real.log (p k ω)-2*A*Real.log ((k:ℝ)+2))) n
    have hr := (ENNReal.ofReal_le_iff_le_toReal hSt).mp hn
    change -Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2) ≤ canonicalLogExcess A p ω at hr
    linarith

lemma canonicalLogExcess_eq_finite {Ω : Type*} {A D W M : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hWM : W ≤ M) (p : ℕ → Ω → ℝ) (ω : Ω)
    (hp : ∀ n, -Real.log (p n ω) ≤ A*Real.log ((n:ℝ)+2)+D*(W+1))
    (N : ℕ) (hN : D*(M+1) ≤ A*Real.log ((N:ℝ)+2)) :
    canonicalLogExcess A p ω = finiteLogExcess A p N ω := by
  unfold canonicalLogExcess finiteLogExcess
  congr 1
  apply le_antisymm
  · apply iSup_le
    intro n
    by_cases hn : n ≤ N
    · exact le_iSup (fun k : Fin (N+1) => ENNReal.ofReal (-Real.log (p k ω)-2*A*Real.log ((k:ℝ)+2))) ⟨n,by omega⟩
    · have hlog : Real.log ((N:ℝ)+2) ≤ Real.log ((n:ℝ)+2) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (show N+2 ≤ n+2 by omega))
      have hAl := mul_le_mul_of_nonneg_left hlog hA
      have hDW := mul_le_mul_of_nonneg_left (add_le_add_right hWM 1) hD
      have hp' := hp n
      have hzero : -Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2) ≤ 0 := by linarith
      rw [ENNReal.ofReal_eq_zero.mpr hzero]
      exact zero_le
  · apply iSup_le
    intro n
    exact le_iSup (fun k : ℕ => ENNReal.ofReal (-Real.log (p k ω)-2*A*Real.log ((k:ℝ)+2))) n.val
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_OutwardCanonicalRows
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma outwardKernelMass_upper_rows {d : ℕ} (e f : Direction d) (H : ℕ) (hH : 0 < H)
    (a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    @Measurable _ _ (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}) _
      (outwardKernelMass e f H x) := by
  have h₁ : Strip (realPosition (step e)) x.1 H ⊆ {y | a ≤ dot (realPosition y) (realPosition (step e))} := by
    intro y hy
    change a ≤ dot (realPosition y) (realPosition (step e))
    simpa only [hx.1] using hy.1
  have h₂ : Strip (realPosition (step e)) x.2 H ⊆ {y | a ≤ dot (realPosition y) (realPosition (step e))} := by
    intro y hy
    change a ≤ dot (realPosition y) (realPosition (step e))
    simpa only [hx.2] using hy.1
  exact ((Measure.measurable_coe (Set.to_countable _).measurableSet).comp
    (rawPairEndpointLaw_rows (realPosition (step e)) x hH h₁ h₂)).ennreal_toReal

lemma measurable_outwardKernelMass {d : ℕ} (e f : Direction d) (H : ℕ)
    (x : Lattice d × Lattice d) : Measurable (outwardKernelMass e f H x) := by
  have h := ((variablePairHitKernel (realPosition (step e)) H).measurable_coe (Set.to_countable
    {y : Lattice d × Lattice d | signedCoordinate f (x.2-x.1) ≤ signedCoordinate f (y.2-y.1)}).measurableSet).comp
      (measurable_id.prodMk (measurable_const (a:=x)))
  change Measurable (fun ω => outwardKernelMass e f H x ω)
  simpa only [Function.comp_def,id_eq,variablePairHitKernel_apply,outwardKernelMass] using h.ennreal_toReal

lemma outwardCanonicalExcess_upper_rows {d : ℕ} (e f : Direction d) (A a : ℝ)
    (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    @Measurable _ _ (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}) _
      (outwardCanonicalExcess e f A x) := by
  let : MeasurableSpace (Environment d) := rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}
  apply measurable_canonicalLogExcess
  intro n
  exact outwardKernelMass_upper_rows e f (n+1) (Nat.succ_pos n) a x hx

lemma measurable_outwardCanonicalExcess {d : ℕ} (e f : Direction d) (A : ℝ)
    (x : Lattice d × Lattice d) : Measurable (outwardCanonicalExcess e f A x) :=
  measurable_canonicalLogExcess A _ (fun n => measurable_outwardKernelMass e f (n+1) x)
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CanonicalHeightCutoff
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma exists_log_height_cutoff {A D M : ℝ} (hA : 0 < A) :
    ∃ N : ℕ, D*(M+1) ≤ A*Real.log ((N:ℝ)+2) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (Real.exp (D*(M+1)/A))
  refine ⟨N,?_⟩
  have hh : Real.exp (D*(M+1)/A) ≤ (N:ℝ)+2 := by linarith
  have hlog := Real.log_le_log (Real.exp_pos _) hh
  rw [Real.log_exp] at hlog
  simpa only [mul_comm A] using (div_le_iff₀ hA).mp hlog

lemma canonical_height_cutoff_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A D B M : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (p : ℕ → Ω → ℝ) (W : Ω → ℝ)
    (hWi : Integrable (fun ω => Real.exp (W ω)) μ)
    (hWB : (∫ ω, Real.exp (W ω) ∂μ) ≤ B)
    (hp : ∀ᵐ ω ∂μ, ∀ n, -Real.log (p n ω) ≤ A*Real.log ((n:ℝ)+2)+D*(W ω+1))
    (N : ℕ) (hN : D*(M+1) ≤ A*Real.log ((N:ℝ)+2)) :
    μ.real {ω | canonicalLogExcess A p ω ≠ finiteLogExcess A p N ω} ≤ B/Real.exp M := by
  have hsub : ∀ᵐ ω ∂μ, (canonicalLogExcess A p ω ≠ finiteLogExcess A p N ω) →
      Real.exp M ≤ Real.exp (W ω) := by
    filter_upwards [hp] with ω hω hne
    apply Real.exp_le_exp.mpr
    by_contra hh
    exact hne (canonicalLogExcess_eq_finite hA hD (le_of_lt (lt_of_not_ge hh)) p ω hω N hN)
  have hle := measure_mono_ae hsub
  have hr : μ.real {ω | canonicalLogExcess A p ω ≠ finiteLogExcess A p N ω} ≤
      μ.real {ω | Real.exp M ≤ Real.exp (W ω)} := ENNReal.toReal_mono (measure_ne_top _ _) hle
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ω => (Real.exp_pos (W ω)).le)) hWi (Real.exp M)
  apply hr.trans
  apply (le_div_iff₀ (Real.exp_pos M)).mpr
  have hm' : μ.real {ω | Real.exp M ≤ Real.exp (W ω)} * Real.exp M ≤
      ∫ ω, Real.exp (W ω) ∂μ := by simpa only [mul_comm] using hm
  exact hm'.trans hWB

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_TailCuts
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter
open scoped Topology ENNReal
namespace TailCuts

lemma maximizing_cuts_escape {L U : ℤ → ℝ}
    (hL : StrictMono L) (hU : StrictAnti U)
    (hL0 : ∀ j, 0 < L j) (hU0 : ∀ j, 0 < U j)
    (hLm : Tendsto L atBot (𝓝 0)) (hUm : Tendsto U atTop (𝓝 0))
    (j : ℕ → ℤ) (hmax : ∀ (n : ℕ) (k : ℤ), score L U (n : ℤ) k ≤ score L U (n : ℤ) (j n)) :
    Tendsto j atTop atBot ∧ Tendsto (fun n => j n + (n : ℤ)) atTop atTop := by
  constructor
  · apply tendsto_atBot.2
    intro b
    have hshift : Tendsto (fun n : ℕ => b - 1 + (n : ℤ)) atTop atTop :=
      tendsto_atTop.2 fun z => by
        filter_upwards [(tendsto_natCast_atTop_atTop (R := ℤ)).eventually (eventually_ge_atTop (z - (b - 1)))] with n hn
        omega
    have ht : ∀ᶠ n : ℕ in atTop, U (b - 1 + (n : ℤ)) < L (b - 1) :=
      (hUm.comp hshift).eventually (gt_mem_nhds (hL0 _))
    filter_upwards [ht] with n hn
    by_contra hj
    have hb : b ≤ j n := le_of_lt (lt_of_not_ge hj)
    have hleft : U (j n + (n : ℤ)) < L (j n - 1) :=
      lt_of_le_of_lt (hU.antitone (by omega)) (lt_of_lt_of_le hn (hL.monotone (by omega)))
    have hright : U (j n + (n : ℤ)) < U (j n - 1 + (n : ℤ)) := hU (by omega)
    have hs : score L U (n : ℤ) (j n) < score L U (n : ℤ) (j n - 1) := by
      unfold score
      exact lt_of_le_of_lt (min_le_right _ _) (lt_min hleft hright)
    exact (not_lt_of_ge (hmax n (j n - 1))) hs
  · apply tendsto_atTop.2
    intro b
    have hshift : Tendsto (fun n : ℕ => b + 1 - (n : ℤ)) atTop atBot :=
      tendsto_atBot.2 fun z => by
        filter_upwards [(tendsto_natCast_atTop_atTop (R := ℤ)).eventually (eventually_ge_atTop (b + 1 - z))] with n hn
        omega
    have ht : ∀ᶠ n : ℕ in atTop, L (b + 1 - (n : ℤ)) < U (b + 1) :=
      (hLm.comp hshift).eventually (gt_mem_nhds (hU0 _))
    filter_upwards [ht] with n hn
    by_contra hj
    have hb : j n + (n : ℤ) ≤ b := le_of_lt (lt_of_not_ge hj)
    have hright : L (j n) < U (j n + 1 + (n : ℤ)) :=
      lt_of_le_of_lt (hL.monotone (by omega)) (lt_of_lt_of_le hn (hU.antitone (by omega)))
    have hleft : L (j n) < L (j n + 1) := hL (by omega)
    have hs : score L U (n : ℤ) (j n) < score L U (n : ℤ) (j n + 1) := by
      unfold score
      exact lt_of_le_of_lt (min_le_left _ _) (lt_min hleft hright)
    exact (not_lt_of_ge (hmax n (j n + 1))) hs

end TailCuts

namespace TailCuts

lemma exists_maximizing_cut {L U : ℤ → ℝ}
    (hL0 : ∀ j, 0 < L j) (hU0 : ∀ j, 0 < U j)
    (hLm : Tendsto L atBot (𝓝 0)) (hUm : Tendsto U atTop (𝓝 0)) (R : ℤ) :
    ∃ j : ℤ, ∀ k, score L U R k ≤ score L U R j := by
  have ht : 0 < score L U R 0 := lt_min (hL0 _) (hU0 _)
  obtain ⟨a, ha⟩ := eventually_atBot.mp (hLm.eventually (gt_mem_nhds ht))
  obtain ⟨b, hb⟩ := eventually_atTop.mp (hUm.eventually (gt_mem_nhds ht))
  let S := Finset.Icc (min a 0) (max (b - R) 0)
  have h0 : (0 : ℤ) ∈ S := Finset.mem_Icc.mpr ⟨min_le_right _ _, le_max_right _ _⟩
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image (score L U R) ⟨0, h0⟩
  refine ⟨j, fun k => ?_⟩
  by_cases hk : k ∈ S
  · exact hmax k hk
  · have hout : k < min a 0 ∨ max (b - R) 0 < k := by
      simpa only [S, Finset.mem_Icc, not_and_or, not_le] using hk
    apply le_trans _ (hmax 0 h0)
    rcases hout with hk | hk
    · exact (min_le_left _ _).trans (ha k (by omega)).le
    · exact (min_le_right _ _).trans (hb (k + R) (by omega)).le

lemma lower_pos (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : ∀ j, 0 < μ.real {j}) (j : ℤ) : 0 < lower μ j := by
  exact (hμ j).trans_le (measureReal_mono (by intro x hx; have hx' : x = j := hx; subst x; exact (show (j : ℤ) ≤ j from le_rfl)))

lemma upper_pos (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : ∀ j, 0 < μ.real {j}) (j : ℤ) : 0 < upper μ j := by
  exact (hμ j).trans_le (measureReal_mono (by intro x hx; have hx' : x = j := hx; subst x; exact (show (j : ℤ) ≤ j from le_rfl)))

lemma lower_strictMono (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : ∀ j, 0 < μ.real {j}) : StrictMono (lower μ) := by
  intro i j hij
  have hd : Disjoint (Set.Iic i) {j} := Set.disjoint_left.mpr (by
    intro x hx hxj
    simp only [Set.mem_singleton_iff] at hxj
    subst x
    exact (not_le_of_gt hij) hx)
  have hu := measureReal_union (μ := μ) hd (measurableSet_singleton j)
  have hs : Set.Iic i ∪ {j} ⊆ Set.Iic j := by
    intro x hx
    rcases hx with hx | hx
    · exact hx.trans hij.le
    · have hx' : x = j := hx
      subst x
      exact (show (j : ℤ) ≤ j from le_rfl)
  have hm := measureReal_mono (μ := μ) hs
  dsimp [lower]
  linarith [hμ j]

lemma upper_strictAnti (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : ∀ j, 0 < μ.real {j}) : StrictAnti (upper μ) := by
  intro i j hij
  have hd : Disjoint (Set.Ici j) {i} := Set.disjoint_left.mpr (by
    intro x hx hxi
    simp only [Set.mem_singleton_iff] at hxi
    subst x
    exact (not_le_of_gt hij) hx)
  have hu := measureReal_union (μ := μ) hd (measurableSet_singleton i)
  have hs : Set.Ici j ∪ {i} ⊆ Set.Ici i := by
    intro x hx
    rcases hx with hx | hx
    · exact hij.le.trans hx
    · have hx' : x = i := hx
      subst x
      exact (show (i : ℤ) ≤ i from le_rfl)
  have hm := measureReal_mono (μ := μ) hs
  dsimp [upper]
  linarith [hμ i]

lemma lower_tendsto (μ : Measure ℤ) [IsFiniteMeasure μ] :
    Tendsto (lower μ) atBot (𝓝 0) := by
  have ht := tendsto_measure_iInter_atBot (μ := μ)
    (s := fun j : ℤ => Set.Iic j) (fun j => measurableSet_Iic.nullMeasurableSet)
    (fun _ _ hij => Set.Iic_subset_Iic.mpr hij) ⟨0, measure_ne_top _ _⟩
  have he : (⋂ j : ℤ, Set.Iic j) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := Set.mem_iInter.mp hx (x - 1)
    simp only [Set.mem_Iic] at hx'
    omega
  rw [he, measure_empty] at ht
  change Tendsto (fun j => (μ (Set.Iic j)).toReal) atBot (𝓝 0)
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp ht

lemma upper_tendsto (μ : Measure ℤ) [IsFiniteMeasure μ] :
    Tendsto (upper μ) atTop (𝓝 0) := by
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (s := fun j : ℤ => Set.Ici j) (fun j => measurableSet_Ici.nullMeasurableSet)
    (fun _ _ hij => Set.Ici_subset_Ici.mpr hij) ⟨0, measure_ne_top _ _⟩
  have he : (⋂ j : ℤ, Set.Ici j) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := Set.mem_iInter.mp hx (x + 1)
    simp only [Set.mem_Ici] at hx'
    omega
  rw [he, measure_empty] at ht
  change Tendsto (fun j => (μ (Set.Ici j)).toReal) atTop (𝓝 0)
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp ht

theorem finite_profile_cuts_escape (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : ∀ j, 0 < μ.real {j}) :
    (∀ R : ℤ, ∃ j : ℤ, ∀ k, score (lower μ) (upper μ) R k ≤ score (lower μ) (upper μ) R j) ∧
    (∀ j : ℕ → ℤ,
      (∀ (n : ℕ) (k : ℤ), score (lower μ) (upper μ) (n : ℤ) k ≤
        score (lower μ) (upper μ) (n : ℤ) (j n)) →
      Tendsto j atTop atBot ∧ Tendsto (fun n => j n + (n : ℤ)) atTop atTop) := by
  exact ⟨exists_maximizing_cut (lower_pos μ hμ) (upper_pos μ hμ) (lower_tendsto μ) (upper_tendsto μ),
    fun j hj => maximizing_cuts_escape (lower_strictMono μ hμ) (upper_strictAnti μ hμ)
      (lower_pos μ hμ) (upper_pos μ hμ) (lower_tendsto μ) (upper_tendsto μ) j hj⟩

end TailCuts

namespace TailCuts

lemma measurable_maximizing_cut {D : Type*} [MeasurableSpace D]
    (L U : D → ℤ → ℝ) (R : ℤ)
    (hL : ∀ j, Measurable (fun d => L d j)) (hU : ∀ j, Measurable (fun d => U d j))
    (hex : ∀ d, ∃ j, ∀ k, score (L d) (U d) R k ≤ score (L d) (U d) R j) :
    ∃ j : D → ℤ, Measurable j ∧
      ∀ d k, score (L d) (U d) R k ≤ score (L d) (U d) R (j d) := by
  classical
  let p : D → ℕ → Prop := fun d n => ∀ k,
    score (L d) (U d) R k ≤ score (L d) (U d) R (Denumerable.ofNat ℤ n)
  have hp : ∀ d, ∃ n, p d n := by
    intro d
    obtain ⟨j, hj⟩ := hex d
    exact ⟨Encodable.encode j, by simpa only [p, Denumerable.ofNat_encode] using hj⟩
  have hm : ∀ n, MeasurableSet {d | p d n} := by
    intro n
    simp only [p, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_le ((hL k).min (hU (k+R)))
      ((hL _).min (hU _))
  refine ⟨fun d => Denumerable.ofNat ℤ (Nat.find (hp d)),
    (measurable_of_countable (Denumerable.ofNat ℤ)).comp (measurable_find hp hm), ?_⟩
  intro d
  exact Nat.find_spec (hp d)

end TailCuts

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_EntropyPlus
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailDecorrelation

lemma entropyPlus_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ entropyPlus u := by
  exact mul_nonneg hu (Real.log_nonneg (le_max_left _ _))

lemma measurable_entropyPlus : Measurable entropyPlus := by
  unfold entropyPlus
  exact measurable_id.mul (Real.measurable_log.comp (measurable_const.max measurable_id))

lemma entropy_young {u : ℝ} (hu : 0 ≤ u) (v : ℝ) :
    u * v ≤ entropyPlus u + Real.exp v := by
  by_cases h0 : u = 0
  · simp [h0, entropyPlus, Real.exp_nonneg]
  have hp : 0 < u := lt_of_le_of_ne hu (Ne.symm h0)
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (v - Real.log u)) hu
  have heq : u * Real.exp (v - Real.log u) = Real.exp v := by
    rw [Real.exp_sub, Real.exp_log hp]
    field_simp
  rw [heq] at he
  have hlog : Real.log u ≤ Real.log (max 1 u) :=
    Real.log_le_log hp (le_max_right _ _)
  have hm := mul_le_mul_of_nonneg_left hlog hu
  unfold entropyPlus
  nlinarith

section Integrability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma integrable_density_mul_of_entropy {f z : Ω → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : Measurable f) (hz : Measurable z)
    (hf0 : ∀ x, 0 ≤ f x) (hz0 : ∀ x, 0 ≤ z x)
    (hH : Integrable (fun x => entropyPlus (f x)) μ)
    (he : Integrable (fun x => Real.exp (c * z x)) μ) :
    Integrable (fun x => f x * z x) μ := by
  apply ((hH.add he).div_const c).mono' (hf.mul hz).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖f x * z x‖ ≤ (entropyPlus (f x) + Real.exp (c * z x)) / c
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x) (hz0 x))]
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using entropy_young (hf0 x) (c * z x)

lemma exp_on_density_tail_pointwise {u z c L B : ℝ}
    (hu : 0 ≤ u) (hc : 0 ≤ c) (hB : 0 < B) :
    (if B < u then Real.exp (c * z) else 0) ≤
      (Real.exp (c * L) / B) * u +
        Real.exp (-c * L) * Real.exp ((2 * c) * z) := by
  by_cases ht : B < u
  · rw [ite_eq_left ht]
    by_cases hz : z ≤ L
    · apply le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz hc))
      have hb : 1 ≤ u / B := (le_div_iff₀ hB).mpr (by linarith)
      have he := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (c * L))
      have hp : 0 ≤ Real.exp (-c * L) * Real.exp ((2 * c) * z) := by positivity
      have heq : Real.exp (c * L) * (u / B) = Real.exp (c * L) / B * u := by ring
      rw [mul_one, heq] at he
      exact he.trans (le_add_of_nonneg_right hp)
    · have hzl : L ≤ z := le_of_not_ge hz
      have hle : c * z ≤ -c * L + (2 * c) * z := by
        nlinarith [mul_nonneg hc (sub_nonneg.mpr hzl)]
      calc
        Real.exp (c * z) ≤ Real.exp (-c * L + (2 * c) * z) := Real.exp_le_exp.mpr hle
        _ = Real.exp (-c * L) * Real.exp ((2 * c) * z) := Real.exp_add _ _
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
  · rw [ite_eq_right ht]
    positivity

lemma density_tail_pointwise {u z c L B : ℝ}
    (hu : 0 ≤ u) (hz : 0 ≤ z) (hc : 0 < c) (hB : 0 < B) :
    c * (if B < u then u * z else 0) ≤
      (if B < u then entropyPlus u else 0) +
        (Real.exp (c * L) / B) * u +
          Real.exp (-c * L) * Real.exp ((2 * c) * z) := by
  rcases hz.eq_or_lt with rfl | _
  · have hEntropy := entropyPlus_nonneg hu
    simp only [mul_zero, ite_self]
    split_ifs <;> positivity
  · have he := exp_on_density_tail_pointwise (u := u) (z := z) (L := L) hu hc.le hB
    by_cases h : B < u
    · simp only [ite_eq_left h] at *
      have hy := entropy_young hu (c * z)
      nlinarith
    · simp only [ite_eq_right h, mul_zero, zero_add]
      positivity

lemma integrable_entropy_tail {f : Ω → ℝ} (hf : Measurable f)
    (hH : Integrable (fun x => entropyPlus (f x)) μ) (B : ℝ) :
    Integrable (fun x => if B < f x then entropyPlus (f x) else 0) μ := by
  apply hH.norm.mono'
    ((measurable_entropyPlus.comp hf).ite (measurableSet_lt measurable_const hf) measurable_const).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖if B < f x then entropyPlus (f x) else 0‖ ≤ ‖entropyPlus (f x)‖
  split_ifs <;> simp only [le_refl, norm_zero, norm_nonneg]

lemma entropy_tail_tendsto {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hH : Integrable (fun x => entropyPlus (f x)) μ) :
    Tendsto (fun n : ℕ => ∫ x, if (n : ℝ) < f x then entropyPlus (f x) else 0 ∂μ)
      atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x => if (n : ℝ) < f x then entropyPlus (f x) else 0) μ :=
    (integrable_entropy_tail hf hH n).aestronglyMeasurable
  have hb (n : ℕ) (x : Ω) :
      ‖(if (n : ℝ) < f x then entropyPlus (f x) else 0)‖ ≤ entropyPlus (f x) := by
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (entropyPlus_nonneg (hf0 x))]
    · simpa only [norm_zero] using entropyPlus_nonneg (hf0 x)
  have ht : ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => if (n : ℝ) < f x then entropyPlus (f x) else 0) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge (f x)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : f x ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
    simp only [not_lt.mpr hn', ite_false, if_false]
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun x => entropyPlus (f x)) hm hH
    (fun n => Eventually.of_forall (hb n)) ht

lemma density_tail_integral_le {f z : Ω → ℝ} {c B L : ℝ}
    (hc : 0 < c) (hB : 0 < B) (hf : Measurable f) (hz : Measurable z)
    (hf0 : ∀ x, 0 ≤ f x) (hz0 : ∀ x, 0 ≤ z x)
    (hfi : Integrable f μ) (hH : Integrable (fun x => entropyPlus (f x)) μ)
    (he : Integrable (fun x => Real.exp ((2 * c) * z x)) μ) :
    (∫ x, if B < f x then f x * z x else 0 ∂μ) ≤
      ((∫ x, if B < f x then entropyPlus (f x) else 0 ∂μ) +
        (Real.exp (c * L) / B) * (∫ x, f x ∂μ) +
          Real.exp (-c * L) * (∫ x, Real.exp ((2 * c) * z x) ∂μ)) / c := by
  have hei : Integrable (fun x => Real.exp (c * z x)) μ := by
    apply he.mono' (Real.measurable_exp.comp (measurable_const.mul hz)).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖Real.exp (c * z x)‖ ≤ Real.exp ((2 * c) * z x)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith [hz0 x])
  have hprod := integrable_density_mul_of_entropy hc hf hz hf0 hz0 hH hei
  have htail : Integrable (fun x => if B < f x then f x * z x else 0) μ := by
    apply hprod.norm.mono'
      ((hf.mul hz).ite (measurableSet_lt measurable_const hf) measurable_const).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖if B < f x then f x * z x else 0‖ ≤ ‖f x * z x‖
    split_ifs <;> simp only [le_refl, norm_zero, norm_nonneg]
  have hEt := integrable_entropy_tail hf hH B
  have hsum : Integrable (fun x => (if B < f x then entropyPlus (f x) else 0) +
      (Real.exp (c * L) / B) * f x) μ := hEt.add (hfi.const_mul _)
  have hi := integral_mono (htail.const_mul c)
    (hsum.add (he.const_mul (Real.exp (-c * L))))
    (fun x => density_tail_pointwise (L := L) (hf0 x) (hz0 x) hc hB)
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,
    integral_add hsum (he.const_mul _),
    integral_add hEt (hfi.const_mul _), integral_const_mul, integral_const_mul] at hi
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm] using hi

lemma remainder_cap_pointwise {z c K : ℝ} (hz : 0 ≤ z) (hc : 0 < c) :
    z - min K z ≤ (Real.exp (-c * K) / c) * Real.exp ((2 * c) * z) := by
  by_cases h : z ≤ K
  · rw [min_eq_right h, sub_self]
    positivity
  · have hK : K ≤ z := le_of_not_ge h
    rw [min_eq_left hK]
    have h0 : c * (z - K) ≤ Real.exp (c * (z - K)) := by
      linarith [Real.add_one_le_exp (c * (z - K))]
    have h1 : c * (z - K) ≤ -c * K + (2 * c) * z := by nlinarith
    have h2 := Real.exp_le_exp.mpr h1
    rw [Real.exp_add] at h2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using h0.trans h2

lemma exp_neg_nat_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-c * (n : ℝ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp only [Function.comp_apply, neg_mul]

lemma uniform_density_tail {f : Ω → ℝ} {Z : ℕ → Ω → ℝ} {c Q : ℝ}
    (hc : 0 < c) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f μ) (hH : Integrable (fun x => entropyPlus (f x)) μ)
    (hZ : ∀ r, Measurable (Z r)) (hZ0 : ∀ r x, 0 ≤ Z r x)
    (he : ∀ r, Integrable (fun x => Real.exp ((2 * c) * Z r x)) μ)
    (heQ : ∀ r, (∫ x, Real.exp ((2 * c) * Z r x) ∂μ) ≤ Q) :
    ∀ ε > 0, ∃ B > 1, ∀ r,
      (∫ x, if B < f x then f x * Z r x else 0 ∂μ) < ε := by
  let F := ∫ x, f x ∂μ
  have hF : 0 ≤ F := integral_nonneg hf0
  have ht : Tendsto (fun n : ℕ =>
      ((∫ x, if (n : ℝ) < f x then entropyPlus (f x) else 0 ∂μ) +
        Real.exp (-c * (n : ℝ)) * (F + Q)) / c) atTop (𝓝 0) := by
    simpa only [zero_mul, zero_add, zero_div] using
      ((entropy_tail_tendsto hf hf0 hH).add ((exp_neg_nat_tendsto hc).mul_const (F + Q))).div_const c
  intro ε hε
  obtain ⟨n, hn⟩ := (ht.eventually_lt_const hε).exists
  let L : ℝ := n
  let B : ℝ := Real.exp ((2 * c) * L) + L + 1
  have hL : 0 ≤ L := Nat.cast_nonneg n
  have hB : 1 < B := by dsimp [B] <;> linarith [Real.exp_pos ((2 * c) * L)]
  have hBn : (n : ℝ) ≤ B := by dsimp [B, L] <;> linarith [Real.exp_pos ((2 * c) * (n : ℝ))]
  have hcoeff : Real.exp (c * L) / B ≤ Real.exp (-c * L) := by
    apply (div_le_iff₀ (lt_trans zero_lt_one hB)).mpr
    have hscale : Real.exp (-c * L) * Real.exp ((2 * c) * L) = Real.exp (c * L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (c * L) = Real.exp (-c * L) * Real.exp ((2 * c) * L) := hscale.symm
      _ ≤ Real.exp (-c * L) * B := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        dsimp [B]
        linarith
  have hHtail : (∫ x, if B < f x then entropyPlus (f x) else 0 ∂μ) ≤
      ∫ x, if (n : ℝ) < f x then entropyPlus (f x) else 0 ∂μ := by
    apply integral_mono (integrable_entropy_tail hf hH B) (integrable_entropy_tail hf hH n)
    intro x
    change (if B < f x then entropyPlus (f x) else 0) ≤
      (if (n : ℝ) < f x then entropyPlus (f x) else 0)
    by_cases h : B < f x
    · rw [ite_eq_left h, ite_eq_left (lt_of_le_of_lt hBn h)]
    · rw [ite_eq_right h]
      split_ifs
      · exact entropyPlus_nonneg (hf0 x)
      · exact le_rfl
  refine ⟨B, hB, ?_⟩
  intro r
  apply lt_of_le_of_lt (density_tail_integral_le (c := c) (B := B) (L := L)
    hc (lt_trans zero_lt_one hB) hf (hZ r) hf0 (hZ0 r) hfi hH (he r))
  apply lt_of_le_of_lt _ hn
  apply div_le_div_of_nonneg_right _ hc.le
  have h1 := mul_le_mul_of_nonneg_right hcoeff hF
  have h2 := mul_le_mul_of_nonneg_left (heQ r) (Real.exp_nonneg (-c * L))
  dsimp [F, L] at *
  nlinarith

lemma cap_error_integrable {f z : Ω → ℝ} {c B K : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hf : Measurable f) (hz : Measurable z)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) (hz0 : ∀ x, 0 ≤ z x)
    (he : Integrable (fun x => Real.exp ((2 * c) * z x)) μ) :
    Integrable (fun x => f x * (z x - min K (z x))) μ := by
  apply (he.const_mul (B * (Real.exp (-c * K) / c))).mono'
    (hf.mul (hz.sub (measurable_const.min hz))).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖f x * (z x - min K (z x))‖ ≤ B * (Real.exp (-c * K) / c) * Real.exp ((2 * c) * z x)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x) (sub_nonneg.mpr (min_le_right _ _)))]
  have hbound := mul_le_mul (hfB x) (remainder_cap_pointwise (K := K) (hz0 x) hc)
    (sub_nonneg.mpr (min_le_right K (z x))) hB
  simpa only [mul_assoc] using hbound

lemma cap_error_integral_le {f z : Ω → ℝ} {c B K : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hf : Measurable f) (hz : Measurable z)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) (hz0 : ∀ x, 0 ≤ z x)
    (he : Integrable (fun x => Real.exp ((2 * c) * z x)) μ) :
    (∫ x, f x * (z x - min K (z x)) ∂μ) ≤
      (B * (Real.exp (-c * K) / c)) * (∫ x, Real.exp ((2 * c) * z x) ∂μ) := by
  rw [← integral_const_mul]
  apply integral_mono (cap_error_integrable hc hB hf hz hf0 hfB hz0 he) (he.const_mul _)
  intro x
  have hbound := mul_le_mul (hfB x) (remainder_cap_pointwise (K := K) (hz0 x) hc)
    (sub_nonneg.mpr (min_le_right K (z x))) hB
  simpa only [mul_assoc] using hbound

lemma uniform_remainder_cap {f : Ω → ℝ} {Z : ℕ → Ω → ℝ} {c B Q : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hZ : ∀ r, Measurable (Z r)) (hZ0 : ∀ r x, 0 ≤ Z r x)
    (he : ∀ r, Integrable (fun x => Real.exp ((2 * c) * Z r x)) μ)
    (heQ : ∀ r, (∫ x, Real.exp ((2 * c) * Z r x) ∂μ) ≤ Q) :
    ∀ ε > 0, ∃ K > 0, ∀ r,
      (∫ x, f x * (Z r x - min K (Z r x)) ∂μ) < ε := by
  have ht : Tendsto (fun n : ℕ => B * (Real.exp (-c * (n : ℝ)) / c) * Q)
      atTop (𝓝 0) := by
    simpa only [zero_div, mul_zero, zero_mul] using
      (((exp_neg_nat_tendsto hc).div_const c).const_mul B).mul_const Q
  intro ε hε
  obtain ⟨n, hn0, hn⟩ := ((eventually_gt_atTop 0).and (ht.eventually_lt_const hε)).exists
  refine ⟨n, by exact_mod_cast hn0, ?_⟩
  intro r
  apply lt_of_le_of_lt (cap_error_integral_le (K := n) hc hB hf (hZ r) hf0 hfB (hZ0 r) (he r))
  apply lt_of_le_of_lt _ hn
  exact mul_le_mul_of_nonneg_left (heQ r) (by positivity)

end Integrability

end TailDecorrelation

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_Rows
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TailDecorrelation

variable {I A D : Type*} [MeasurableSpace A] [MeasurableSpace D]

lemma rows_eq_iSup_two (S : Set I) :
    rows (A := A) S =
      ⨆ i ∈ S, (inferInstance : MeasurableSpace A).comap (fun ω : I → A => ω i) := by
  simp only [rows, iSup_subtype]

lemma independent_rows (ν : Measure A) [IsProbabilityMeasure ν]
    {S T : Set I} (hST : Disjoint S T) :
    Indep (rows S) (rows T) (Measure.infinitePi (fun _ : I => ν)) := by
  rw [rows_eq_iSup_two, rows_eq_iSup_two]
  exact indep_iSup_of_disjoint (fun i =>
    (show Measurable (fun ω : I → A => ω i) from measurable_pi_apply i).comap_le)
    (iIndepFun_infinitePi (P := fun _ : I => ν)
      (X := fun _ a => a) (fun _ => measurable_id)).iIndep hST

lemma independent_row_functions (ν : Measure A) [IsProbabilityMeasure ν]
    {S T : Set I} (hST : Disjoint S T)
    {f g : (I → A) → ℝ}
    (hf : @Measurable _ _ (rows S) _ f)
    (hg : @Measurable _ _ (rows T) _ g) :
    IndepFun f g (Measure.infinitePi (fun _ : I => ν)) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  exact (Indep_iff _ _ _).mp (independent_rows ν hST) _ _ (hf hs) (hg ht)

lemma row_function_integral_mul (ν : Measure A) [IsProbabilityMeasure ν]
    {S T : Set I} (hST : Disjoint S T)
    {f g : (I → A) → ℝ}
    (hf : @Measurable _ _ (rows S) _ f)
    (hg : @Measurable _ _ (rows T) _ g) :
    (∫ ω, f ω * g ω ∂Measure.infinitePi (fun _ : I => ν)) =
      (∫ ω, f ω ∂Measure.infinitePi (fun _ : I => ν)) *
        ∫ ω, g ω ∂Measure.infinitePi (fun _ : I => ν) := by
  exact (independent_row_functions ν hST hf hg).integral_mul_eq_mul_integral
    ((hf.mono (rows_le S) le_rfl).aestronglyMeasurable)
    ((hg.mono (rows_le T) le_rfl).aestronglyMeasurable)

lemma dataRows_section {S : Set I} {f : D × (I → A) → ℝ}
    (hf : @Measurable _ _ (dataRows S) _ f) (d : D) :
    @Measurable _ _ (rows S) _ (fun ω => f (d, ω)) := by
  apply hf.comp
  let : MeasurableSpace (I → A) := rows S
  exact measurable_const.prodMk measurable_id

variable [Encodable I]

lemma prefixRows_finite (n : ℕ) : (prefixRows (I := I) n).Finite := by
  exact (Set.finite_Iio n).preimage Encodable.encode_injective.injOn

lemma iSup_dataFiltration :
    (⨆ n, dataFiltration (D := D) (A := A) (I := I) n) = (inferInstance : MeasurableSpace (D × (I → A))) := by
  apply le_antisymm (iSup_le fun n => (dataFiltration (D := D) (A := A) (I := I)).le n)
  change (inferInstance : MeasurableSpace D).comap Prod.fst ⊔
    (inferInstance : MeasurableSpace (I → A)).comap Prod.snd ≤ _
  apply sup_le
  · exact le_iSup_of_le 0 le_sup_left
  · change (⨆ i : I, (inferInstance : MeasurableSpace A).comap (fun ω => ω i)).comap
      (Prod.snd : D × (I → A) → I → A) ≤ _
    rw [MeasurableSpace.comap_iSup]
    apply iSup_le
    intro i
    apply le_iSup_of_le (Encodable.encode i + 1)
    apply le_trans _ le_sup_right
    exact MeasurableSpace.comap_mono (le_iSup_of_le
      (⟨i, Nat.lt_succ_self _⟩ : prefixRows (Encodable.encode i + 1)) le_rfl)

section LikelihoodApproximation

variable {μ : Measure (D × (I → A))} [IsFiniteMeasure μ]

lemma likelihood_approximation {f : D × (I → A) → ℝ}
    (hf : Integrable f μ) (hm : StronglyMeasurable f) :
    Tendsto (fun n => eLpNorm
      (μ[f | dataFiltration (D := D) (A := A) (I := I) n] - f) 1 μ)
      atTop (𝓝 0) := by
  apply hf.tendsto_eLpNorm_condExp (ℱ := dataFiltration (D := D) (A := A) (I := I))
  rw [iSup_dataFiltration]
  exact hm

lemma bounded_likelihood_approximation {f : D × (I → A) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hf : StronglyMeasurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) :
    ∃ g : ℕ → D × (I → A) → ℝ,
      (∀ n, @Measurable _ _ (dataRows (prefixRows n)) _ (g n)) ∧
      (∀ n x, 0 ≤ g n x ∧ g n x ≤ B) ∧
      (∀ n, (∫ x, g n x ∂μ) = ∫ x, f x ∂μ) ∧
      Tendsto (fun n => ∫ x, |g n x - f x| ∂μ) atTop (𝓝 0) := by
  let F := dataFiltration (D := D) (A := A) (I := I)
  let u : ℕ → D × (I → A) → ℝ := fun n => μ[f | F n]
  let g : ℕ → D × (I → A) → ℝ := fun n x => max 0 (min B (u n x))
  have hu (n : ℕ) : @Measurable _ _ (dataRows (prefixRows n)) _ (u n) :=
    stronglyMeasurable_condExp.measurable
  have hg (n : ℕ) : @Measurable _ _ (dataRows (prefixRows n)) _ (g n) :=
    measurable_const.max (measurable_const.min (hu n))
  have hgf (n : ℕ) : g n =ᵐ[μ] u n := by
    have h0 : 0 ≤ᵐ[μ] u n := condExp_nonneg (Eventually.of_forall hf0)
    have h1 : ∀ᵐ x ∂μ, u n x ≤ B :=
      condExp_le_nonneg_const hB (Eventually.of_forall hfB)
    filter_upwards [h0, h1] with x hx0 hx1
    change 0 ≤ u n x at hx0
    simp only [g, min_eq_right hx1, max_eq_right hx0]
  have hfi : Integrable f μ := (integrable_const B).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hfB x)
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro n x
    exact ⟨le_max_left _ _, max_le hB (min_le_left _ _)⟩
  · intro n
    rw [integral_congr_ae (hgf n)]
    exact integral_condExp (F.le n)
  · have ht := ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp
      (likelihood_approximation (μ := μ) hfi hf)
    simp only [ENNReal.toReal_zero] at ht
    apply ht.congr
    intro n
    change (eLpNorm (u n - f) 1 μ).toReal = _
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← integral_norm_eq_lintegral_enorm (integrable_condExp.sub hfi).aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hgf n] with x hx
    simp only [Pi.sub_apply, Real.norm_eq_abs, hx]
    rfl

end LikelihoodApproximation

section BoundedEscape

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

lemma integrable_bounded_nonneg {f : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B) :
    Integrable f μ := by
  exact (integrable_const B).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hfB x)

lemma eventually_integral_le_of_pointwise_eventually
    {F : ℕ → Ω → ℝ} {G : Ω → ℝ} {K : ℝ}
    (hF : ∀ n, Measurable (F n)) (hG : Integrable G μ)
    (hF0 : ∀ n x, 0 ≤ F n x) (hFK : ∀ n x, F n x ≤ K)
    (hG0 : ∀ x, 0 ≤ G x)
    (hevent : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, F n x ≤ G x) :
    ∀ ε > 0, ∀ᶠ n in atTop, (∫ x, F n x ∂μ) ≤ (∫ x, G x ∂μ) + ε := by
  let E : ℕ → Ω → ℝ := fun n x => max 0 (F n x - G x)
  have hEmeas (n : ℕ) : AEStronglyMeasurable (E n) μ :=
    (aemeasurable_const.max ((hF n).aemeasurable.sub hG.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hEbound (n : ℕ) (x : Ω) : ‖E n x‖ ≤ K := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le (le_trans (hF0 n x) (hFK n x)) (by linarith [hFK n x, hG0 x])
  have hEi (n : ℕ) : Integrable (E n) μ :=
    (integrable_const K).mono' (hEmeas n) (Eventually.of_forall (hEbound n))
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => E n x) atTop (𝓝 0) := by
    filter_upwards [hevent] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hx] with n hn
    exact (max_eq_left (sub_nonpos.mpr hn)).symm
  have ht : Tendsto (fun n => ∫ x, E n x ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun _ => K) hEmeas (integrable_const K)
      (fun n => Eventually.of_forall (hEbound n)) hlim
  intro ε hε
  filter_upwards [ht.eventually_lt_const hε] with n hn
  calc
    (∫ x, F n x ∂μ) ≤ ∫ x, G x + E n x ∂μ := by
      apply integral_mono (integrable_bounded_nonneg (hF n) (hF0 n) (hFK n)) (hG.add (hEi n))
      intro x
      have := le_max_right 0 (F n x - G x)
      dsimp [E]
      linarith
    _ = (∫ x, G x ∂μ) + ∫ x, E n x ∂μ := integral_add hG (hEi n)
    _ ≤ _ := by linarith

end BoundedEscape

section BoundedIndependence

variable (δ : Measure D) (ν : Measure A) [IsProbabilityMeasure δ] [IsProbabilityMeasure ν]

omit [Encodable I] in
lemma bounded_escape_product
    {S : Set I} {g : D × (I → A) → ℝ} {B K C : ℝ}
    (hB : 0 ≤ B) (_ : 0 ≤ K) (hC : 0 ≤ C)
    (hg : @Measurable _ _ (dataRows S) _ g)
    (hg0 : ∀ x, 0 ≤ g x) (hgB : ∀ x, g x ≤ B)
    (W : ℕ → D × (I → A) → ℝ) (T : ℕ → D → Set I)
    (hW : ∀ n, Measurable (W n))
    (hW0 : ∀ n x, 0 ≤ W n x) (hWK : ∀ n x, W n x ≤ K)
    (hWr : ∀ n d, @Measurable _ _ (rows (T n d)) _ (fun ω => W n (d, ω)))
    (hWC : ∀ n d, (∫ ω, W n (d, ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ C)
    (hescape : ∀ᵐ d ∂δ, ∀ᶠ n in atTop, Disjoint S (T n d)) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (∫ x, g x * W n x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤
        C * (∫ x, g x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) + ε := by
  let P := Measure.infinitePi (fun _ : I => ν)
  have hgm : Measurable g := hg.mono (dataRows_le S) le_rfl
  have hgi : Integrable g (δ.prod P) := integrable_bounded_nonneg hgm hg0 hgB
  have hprod0 (n : ℕ) (x : D × (I → A)) : 0 ≤ g x * W n x :=
    mul_nonneg (hg0 x) (hW0 n x)
  have hprodK (n : ℕ) (x : D × (I → A)) : g x * W n x ≤ B * K :=
    mul_le_mul (hgB x) (hWK n x) (hW0 n x) hB
  have hprod (n : ℕ) : Integrable (fun x => g x * W n x) (δ.prod P) :=
    integrable_bounded_nonneg (hgm.mul (hW n)) (hprod0 n) (hprodK n)
  let F : ℕ → D → ℝ := fun n d => ∫ ω, g (d, ω) * W n (d, ω) ∂P
  let G : D → ℝ := fun d => C * ∫ ω, g (d, ω) ∂P
  have hFm (n : ℕ) : Measurable (F n) :=
    (hgm.mul (hW n)).stronglyMeasurable.integral_prod_right.measurable
  have hGi : Integrable G δ := hgi.integral_prod_left.const_mul C
  have hG0 (d : D) : 0 ≤ G d :=
    mul_nonneg hC (integral_nonneg fun ω => hg0 (d, ω))
  have hF0 (n : ℕ) (d : D) : 0 ≤ F n d := integral_nonneg fun ω => hprod0 n (d, ω)
  have hFK (n : ℕ) (d : D) : F n d ≤ B * K := by
    calc
      F n d ≤ ∫ _ : I → A, B * K ∂P := by
        exact integral_mono
          (integrable_bounded_nonneg (μ := P)
            ((hgm.mul (hW n)).comp (measurable_const.prodMk measurable_id))
            (fun ω => hprod0 n (d, ω)) (fun ω => hprodK n (d, ω)))
          (integrable_const _) (fun ω => hprodK n (d, ω))
      _ = B * K := by simp [P]
  have hevent : ∀ᵐ d ∂δ, ∀ᶠ n in atTop, F n d ≤ G d := by
    filter_upwards [hescape] with d hd
    filter_upwards [hd] with n hn
    change (∫ ω, g (d, ω) * W n (d, ω) ∂P) ≤ _
    rw [row_function_integral_mul ν hn (dataRows_section hg d) (hWr n d)]
    change (∫ ω, g (d, ω) ∂P) * (∫ ω, W n (d, ω) ∂P) ≤
      C * (∫ ω, g (d, ω) ∂P)
    exact (mul_le_mul_of_nonneg_left (hWC n d) (integral_nonneg fun ω => hg0 (d, ω))).trans_eq
      (mul_comm _ _)
  intro ε hε
  filter_upwards [eventually_integral_le_of_pointwise_eventually hFm hGi hF0 hFK hG0 hevent ε hε] with n hn
  rw [integral_prod _ (hprod n)]
  rw [show (∫ d, G d ∂δ) = C * ∫ x, g x ∂δ.prod P by
    dsimp [G]
    rw [integral_const_mul, ← integral_prod _ hgi]] at hn
  exact hn

lemma bounded_product_approximation_pointwise {f g z w B K : ℝ}
    (hg0 : 0 ≤ g) (hgB : g ≤ B) (hz0 : 0 ≤ z) (hzK : z ≤ K) :
    f * z ≤ g * w + K * |f - g| + B * |z - w| := by
  have h1 := mul_le_mul_of_nonneg_right (le_abs_self (f - g)) hz0
  have h2 := mul_le_mul_of_nonneg_left hzK (abs_nonneg (f - g))
  have h3 := mul_le_mul_of_nonneg_left (le_abs_self (z - w)) hg0
  have h4 := mul_le_mul_of_nonneg_right hgB (abs_nonneg (z - w))
  nlinarith

lemma bounded_decorrelation
    {f : D × (I → A) → ℝ} {Z : ℕ → D × (I → A) → ℝ} {B K C : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfB : ∀ x, f x ≤ B)
    (hZ : ∀ n, Measurable (Z n))
    (hZ0 : ∀ n x, 0 ≤ Z n x) (hZK : ∀ n x, Z n x ≤ K)
    (hZC : ∀ n d, (∫ ω, Z n (d, ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ C)
    (hloc : EscapingLocalApproximation δ ν Z K) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (∫ x, f x * Z n x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤
        C * (∫ x, f x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) + ε := by
  let P := Measure.infinitePi (fun _ : I => ν)
  let μ := δ.prod P
  have hfi : Integrable f μ := integrable_bounded_nonneg hf hf0 hfB
  have hfintB : (∫ x, f x ∂μ) ≤ B := by
    calc
      (∫ x, f x ∂μ) ≤ ∫ _ : D × (I → A), B ∂μ := integral_mono hfi (integrable_const B) hfB
      _ = B := by simp [μ, P]
  obtain ⟨g, hgr, hgb, hgint, hgconv⟩ :=
    bounded_likelihood_approximation (μ := μ) hB hf.stronglyMeasurable hf0 hfB
  intro ε hε
  let η := ε / (2 * (K + 2 * B + 1))
  have hη : 0 < η := by dsimp [η] <;> positivity
  obtain ⟨W, T, hWm, hWb, hWr, hWerr, hWesc⟩ := hloc η hη
  obtain ⟨j, hj⟩ := (hgconv.eventually_lt_const hη).exists
  let g₀ := g j
  have hg₀m : Measurable g₀ := (hgr j).mono (dataRows_le _) le_rfl
  have hg₀i : Integrable g₀ μ :=
    integrable_bounded_nonneg hg₀m (fun x => (hgb j x).1) (fun x => (hgb j x).2)
  have hW0 (n : ℕ) (x : D × (I → A)) : 0 ≤ W n x := (hWb n x).1
  have hWK (n : ℕ) (x : D × (I → A)) : W n x ≤ K := (hWb n x).2
  have hZi (n : ℕ) : Integrable (Z n) μ := integrable_bounded_nonneg (hZ n) (hZ0 n) (hZK n)
  have hWi (n : ℕ) : Integrable (W n) μ := integrable_bounded_nonneg (hWm n) (hW0 n) (hWK n)
  have hZsi (n : ℕ) (d : D) : Integrable (fun ω => Z n (d, ω)) P :=
    integrable_bounded_nonneg ((hZ n).comp (measurable_const.prodMk measurable_id))
      (fun ω => hZ0 n (d, ω)) (fun ω => hZK n (d, ω))
  have hWsi (n : ℕ) (d : D) : Integrable (fun ω => W n (d, ω)) P :=
    integrable_bounded_nonneg ((hWm n).comp (measurable_const.prodMk measurable_id))
      (fun ω => hW0 n (d, ω)) (fun ω => hWK n (d, ω))
  have hWmean (n : ℕ) (d : D) : (∫ ω, W n (d, ω) ∂P) ≤ C + η := by
    calc
      (∫ ω, W n (d, ω) ∂P) ≤ ∫ ω, Z n (d, ω) + |Z n (d, ω) - W n (d, ω)| ∂P := by
        apply integral_mono (hWsi n d) ((hZsi n d).add ((hZsi n d).sub (hWsi n d)).abs)
        intro ω
        have := neg_abs_le (Z n (d, ω) - W n (d, ω))
        change W n (d, ω) ≤ Z n (d, ω) + |Z n (d, ω) - W n (d, ω)|
        linarith
      _ = (∫ ω, Z n (d, ω) ∂P) + ∫ ω, |Z n (d, ω) - W n (d, ω)| ∂P :=
        integral_add (hZsi n d) ((hZsi n d).sub (hWsi n d)).abs
      _ ≤ C + η := add_le_add (hZC n d) (hWerr n d)
  have herri (n : ℕ) : Integrable (fun x => |Z n x - W n x|) μ :=
    ((hZi n).sub (hWi n)).abs
  have hWerrμ (n : ℕ) : (∫ x, |Z n x - W n x| ∂μ) ≤ η := by
    change (∫ x, |Z n x - W n x| ∂δ.prod P) ≤ η
    rw [integral_prod _ (herri n)]
    calc
      (∫ d, ∫ ω, |Z n (d, ω) - W n (d, ω)| ∂P ∂δ) ≤ ∫ _ : D, η ∂δ :=
        integral_mono ((hZi n).sub (hWi n)).abs.integral_prod_left (integrable_const η) (hWerr n)
      _ = η := by simp
  have hprod (n : ℕ) : Integrable (fun x => f x * Z n x) μ :=
    integrable_bounded_nonneg (hf.mul (hZ n)) (fun x => mul_nonneg (hf0 x) (hZ0 n x))
      (fun x => mul_le_mul (hfB x) (hZK n x) (hZ0 n x) hB)
  have hgprod (n : ℕ) : Integrable (fun x => g₀ x * W n x) μ :=
    integrable_bounded_nonneg (hg₀m.mul (hWm n)) (fun x => mul_nonneg (hgb j x).1 (hW0 n x))
      (fun x => mul_le_mul (hgb j x).2 (hWK n x) (hW0 n x) hB)
  have hgf : (∫ x, |f x - g₀ x| ∂μ) < η := by
    simpa only [abs_sub_comm] using hj
  have hevent := bounded_escape_product δ ν hB hK (add_nonneg hC hη.le)
    (hgr j) (fun x => (hgb j x).1) (fun x => (hgb j x).2)
    W T hWm hW0 hWK hWr hWmean (hWesc _ (prefixRows_finite j)) η hη
  filter_upwards [hevent] with n hn
  have hfgi : Integrable (fun x => |f x - g₀ x|) μ := (hfi.sub hg₀i).abs
  have hsum : Integrable (fun x => g₀ x * W n x + K * |f x - g₀ x|) μ :=
    (hgprod n).add (hfgi.const_mul K)
  have hi : (∫ x, f x * Z n x ∂μ) ≤
      (∫ x, g₀ x * W n x ∂μ) + K * (∫ x, |f x - g₀ x| ∂μ) +
        B * (∫ x, |Z n x - W n x| ∂μ) := by
    have ht := integral_mono (hprod n) (hsum.add ((herri n).const_mul B))
      (fun x => bounded_product_approximation_pointwise (hgb j x).1 (hgb j x).2 (hZ0 n x) (hZK n x))
    change (∫ x, f x * Z n x ∂μ) ≤
      ∫ x, (g₀ x * W n x + K * |f x - g₀ x|) + B * |Z n x - W n x| ∂μ at ht
    rwa [integral_add hsum ((herri n).const_mul B),
      integral_add (hgprod n) (hfgi.const_mul K),
      integral_const_mul, integral_const_mul] at ht
  have hn' : (∫ x, g₀ x * W n x ∂μ) ≤ (C + η) * (∫ x, f x ∂μ) + η := by
    change (∫ x, g j x * W n x ∂μ) ≤ (C + η) * (∫ x, g j x ∂μ) + η at hn
    rw [hgint j] at hn
    exact hn
  have heq : (K + 2 * B + 1) * η = ε / 2 := by
    dsimp [η]
    have hden : K + 2 * B + 1 ≠ 0 := by positivity
    field_simp
  have h1 := mul_le_mul_of_nonneg_left hgf.le hK
  have h2 := mul_le_mul_of_nonneg_left (hWerrμ n) hB
  have h3 := mul_le_mul_of_nonneg_left hfintB hη.le
  change (∫ x, f x * Z n x ∂μ) ≤ C * (∫ x, f x ∂μ) + ε
  nlinarith

end BoundedIndependence

end TailDecorrelation

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_EntropyDecorrelation
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailDecorrelation

section Unbounded

variable {D I A : Type*} [MeasurableSpace D] [MeasurableSpace A] [Encodable I]
variable (δ : Measure D) (ν : Measure A) [IsProbabilityMeasure δ] [IsProbabilityMeasure ν]

lemma entropy_decorrelation {f : D × (I → A) → ℝ} {Z : ℕ → D × (I → A) → ℝ}
    {c Q C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hf1 : (∫ x, f x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) = 1)
    (hH : Integrable (fun x => entropyPlus (f x))
      (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hZ : ∀ r, Measurable (Z r)) (hZ0 : ∀ r x, 0 ≤ Z r x)
    (he : ∀ r, Integrable (fun x => Real.exp ((2 * c) * Z r x))
      (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (heQ : ∀ r, (∫ x, Real.exp ((2 * c) * Z r x)
      ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤ Q)
    (hZsi : ∀ r d, Integrable (fun ω => Z r (d, ω)) (Measure.infinitePi (fun _ : I => ν)))
    (hZC : ∀ r d, (∫ ω, Z r (d, ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ C)
    (hloc : ∀ K > 0, EscapingLocalApproximation δ ν (fun r x => min K (Z r x)) K) :
    ∀ ε > 0, ∀ᶠ r in atTop,
      (∫ x, f x * Z r x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤ C + ε := by
  let P := Measure.infinitePi (fun _ : I => ν)
  let μ := δ.prod P
  have hprod (r : ℕ) : Integrable (fun x => f x * Z r x) μ := by
    apply integrable_density_mul_of_entropy (c := 2 * c) (by positivity) hf (hZ r) hf0 (hZ0 r) hH (he r)
  intro ε hε
  have ht : 0 < ε / 3 := by positivity
  obtain ⟨B, hB, htail⟩ := uniform_density_tail hc hf hf0 hfi hH hZ hZ0 he heQ (ε / 3) ht
  let b : D × (I → A) → ℝ := fun x => min B (f x)
  have hb : Measurable b := measurable_const.min hf
  have hb0 : ∀ x, 0 ≤ b x := fun x => le_min (by linarith) (hf0 x)
  have hbB : ∀ x, b x ≤ B := fun x => min_le_left _ _
  have hbf : ∀ x, b x ≤ f x := fun x => min_le_right _ _
  have hbi : Integrable b μ := integrable_bounded_nonneg hb hb0 hbB
  have hbm : (∫ x, b x ∂μ) ≤ 1 := by
    rw [← hf1]
    exact integral_mono hbi hfi hbf
  obtain ⟨K, hK, hcap⟩ := uniform_remainder_cap hc (by linarith : 0 ≤ B)
    hb hb0 hbB hZ hZ0 he heQ (ε / 3) ht
  let ZK : ℕ → D × (I → A) → ℝ := fun r x => min K (Z r x)
  have hZK (r : ℕ) : Measurable (ZK r) := measurable_const.min (hZ r)
  have hZK0 (r : ℕ) (x : D × (I → A)) : 0 ≤ ZK r x := le_min hK.le (hZ0 r x)
  have hZKB (r : ℕ) (x : D × (I → A)) : ZK r x ≤ K := min_le_left _ _
  have hZKC (r : ℕ) (d : D) : (∫ ω, ZK r (d, ω) ∂P) ≤ C := by
    apply le_trans _ (hZC r d)
    exact integral_mono
      (integrable_bounded_nonneg ((hZK r).comp (measurable_const.prodMk measurable_id))
        (fun ω => hZK0 r (d, ω)) (fun ω => hZKB r (d, ω)))
      (hZsi r d) (fun _ => min_le_right _ _)
  have hbd := bounded_decorrelation δ ν (by linarith : 0 ≤ B) hK.le hC hb hb0 hbB
    hZK hZK0 hZKB hZKC (hloc K hK) (ε / 3) ht
  filter_upwards [hbd] with r hr
  have hcapi : Integrable (fun x => b x * (Z r x - min K (Z r x))) μ :=
    cap_error_integrable (K := K) hc (by linarith) hb (hZ r) hb0 hbB (hZ0 r) (he r)
  have htaili : Integrable (fun x => if B < f x then f x * Z r x else 0) μ := by
    apply (hprod r).norm.mono'
      ((hf.mul (hZ r)).ite (measurableSet_lt measurable_const hf) measurable_const).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖if B < f x then f x * Z r x else 0‖ ≤ ‖f x * Z r x‖
    split_ifs <;> simp only [le_refl, norm_zero, norm_nonneg]
  have hbZi : Integrable (fun x => b x * ZK r x) μ :=
    integrable_bounded_nonneg (hb.mul (hZK r))
      (fun x => mul_nonneg (hb0 x) (hZK0 r x))
      (fun x => mul_le_mul (hbB x) (hZKB r x) (hZK0 r x) (by linarith))
  have hsum : Integrable (fun x => b x * ZK r x +
      (if B < f x then f x * Z r x else 0)) μ := hbZi.add htaili
  have hi := integral_mono (hprod r) (hsum.add hcapi) (fun x => show f x * Z r x ≤
      (b x * ZK r x + (if B < f x then f x * Z r x else 0)) +
        b x * (Z r x - min K (Z r x)) by
    by_cases hx : B < f x
    · rw [ite_eq_left hx]
      dsimp [ZK]
      nlinarith [mul_nonneg (hb0 x) (hZ0 r x)]
    · rw [ite_eq_right hx]
      have heq : b x = f x := min_eq_right (le_of_not_gt hx)
      rw [heq]
      dsimp [ZK]
      ring_nf
      exact le_rfl)
  change (∫ x, f x * Z r x ∂μ) ≤ ∫ x,
      (b x * ZK r x + (if B < f x then f x * Z r x else 0)) +
        b x * (Z r x - min K (Z r x)) ∂μ at hi
  rw [integral_add hsum hcapi, integral_add hbZi htaili] at hi
  have h1 : C * (∫ x, b x ∂μ) ≤ C := by nlinarith [hbm]
  have h2 := htail r
  have h3 := hcap r
  change (∫ x, b x * ZK r x ∂μ) ≤ C * (∫ x, b x ∂μ) + ε / 3 at hr
  change (∫ x, f x * Z r x ∂μ) ≤ C + ε
  nlinarith

end Unbounded

end TailDecorrelation

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OutwardCanonical
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

instance truncatedEndpointLaw_finite {d : ℕ} (e : Direction d) (H N : ℕ)
    (ω : Environment d) (x : Lattice d) : IsFiniteMeasure (truncatedEndpointLaw e H N ω x) := by
  unfold truncatedEndpointLaw
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_prefixEndpoint <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma truncatedEndpointLaw_le {d : ℕ} (e : Direction d) {H : ℕ} (hH : 0 < H)
    (N : ℕ) (ω : Environment d) (x : Lattice d) :
    truncatedEndpointLaw e H N ω x ≤
      hitKernel (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) (ω,x) := by
  rw [hitKernel_eq_map_prefixEndpoint e x hH]
  exact Measure.map_mono (Measure.restrict_mono (hitThrough_subset_hit _ _ _) le_rfl)
    (measurable_prefixEndpoint _ _ _)

lemma truncatedEndpointLaw_apply {d : ℕ} (e : Direction d) {H : ℕ} (hH : 0 < H)
    (N : ℕ) (ω : Environment d) (x : Lattice d) (A : Set (Lattice d)) :
    truncatedEndpointLaw e H N ω x A = quenchedKernel (ω,x)
      (HitThrough (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H ∩ A) N) := by
  rw [truncatedEndpointLaw,Measure.map_apply (measurable_prefixEndpoint _ _ _) (Set.to_countable _).measurableSet,
    Measure.restrict_apply ((measurable_prefixEndpoint _ _ _) (Set.to_countable _).measurableSet)]
  apply measure_congr
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  apply propext
  constructor
  · rintro ⟨hA,hhit⟩
    obtain ⟨n,hn,hdet⟩ := Set.mem_iUnion₂.mp hhit
    change prefixEndpoint (realPosition (step e)) x H X ∈ A at hA
    dsimp [prefixEndpoint] at hA
    rw [coordinate_hitAt_record e x X h0 hnn hH hdet] at hA
    exact Set.mem_iUnion₂.mpr ⟨n,hn,⟨hdet.1,by simpa only [add_sub_cancel] using hA⟩,hdet.2⟩
  · intro hhit
    obtain ⟨n,hn,hdet⟩ := Set.mem_iUnion₂.mp hhit
    have hh : X ∈ HitAt (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) n := ⟨hdet.1.1,hdet.2⟩
    refine ⟨?_,Set.mem_iUnion₂.mpr ⟨n,hn,hh⟩⟩
    change prefixEndpoint (realPosition (step e)) x H X ∈ A
    dsimp [prefixEndpoint]
    rw [coordinate_hitAt_record e x X h0 hnn hH hh]
    simpa only [add_sub_cancel] using hdet.1.2

lemma truncatedEndpointLaw_locality {d : ℕ} (e : Direction d) {H : ℕ} (hH : 0 < H)
    (N : ℕ) (ω η : Environment d) (x : Lattice d)
    (he : Set.EqOn ω η (LatticeBall x N)) :
    truncatedEndpointLaw e H N ω x = truncatedEndpointLaw e H N η x := by
  apply Measure.ext
  intro A hA
  rw [truncatedEndpointLaw_apply e hH,truncatedEndpointLaw_apply e hH]
  exact quenched_hitThrough_locality ω η x _ _ N he
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SignedStripTruncation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma wordCylinder_signed_up_disjoint_stay {d : ℕ} (e : Direction d)
    (x y : Lattice d) (H : ℕ) :
    Disjoint (wordCylinder y (List.replicate H e))
      (StayUntil (Strip (realPosition (step e)) x H) H) := by
  apply Set.disjoint_left.mpr
  intro X hw hS
  have hb := (hS 0 (Nat.zero_le H)).1
  have ht := (hS H le_rfl).2
  have hzero := hw 0 (by simp)
  have hend := hw H (by simp)
  rw [wordPath_replicate] at hend
  rw [hzero,wordPath_zero] at hb
  rw [hend,dot_realPosition_add,dot_realPosition_nsmul,dot_signed_direction e (step e),signedCoordinate_step_self,mul_one] at ht
  linarith

lemma quenched_signed_strip_block {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (e : Direction d) (x y : Lattice d) (H : ℕ) :
    quenchedKernel (ω,y) (StayUntil (Strip (realPosition (step e)) x H) H) ≤
      1-(κ:ℝ≥0∞)^H := by
  have hsub := (wordCylinder_signed_up_disjoint_stay e x y H).subset_compl_left
  calc
    _ ≤ quenchedKernel (ω,y) (wordCylinder y (List.replicate H e))ᶜ := measure_mono hsub
    _ = 1-ENNReal.ofReal (wordWeight ω y (List.replicate H e)) := by
      rw [measure_compl (measurableSet_wordCylinder _ _) (measure_ne_top _ _),measure_univ,quenched_wordCylinder]
    _ ≤ 1-(κ:ℝ≥0∞)^H := by
      apply tsub_le_tsub_left
      have hs := ENNReal.ofReal_le_ofReal (wordWeight_lower ω hκ y (List.replicate H e))
      simpa only [List.length_replicate,ENNReal.ofReal_pow κ.coe_nonneg,ENNReal.ofReal_coe_nnreal] using hs

lemma quenched_signed_strip_geometric {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (e : Direction d) (x y : Lattice d) (H k : ℕ) :
    quenchedKernel (ω,y) (StayUntil (Strip (realPosition (step e)) x H) (k*H)) ≤
      (1-(κ:ℝ≥0∞)^H)^k :=
  quenched_stayUntil_block_bound ω _ H _ (fun y => quenched_signed_strip_block ω hκ e x y H) y k

lemma truncatedEndpointLaw_mass_error {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (e : Direction d) (x : Lattice d)
    {H : ℕ} (hH : 0 < H) (k : ℕ) :
    hitKernel (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) (ω,x) Set.univ ≤
      truncatedEndpointLaw e H (k*H) ω x Set.univ+(1-(κ:ℝ≥0∞)^H)^k := by
  rw [truncatedEndpointLaw_apply e hH,Set.inter_univ,hitKernel_total (disjoint_strip_upper _ _ _)]
  exact (quenched_hit_truncation ω x _ _ _).trans
    (add_le_add le_rfl (quenched_signed_strip_geometric ω hκ e x x H k))
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProductTruncationError
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DirectionalTransience

lemma product_submeasure_error {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂]
    (h₁ : ν₁ ≤ μ₁) (h₂ : ν₂ ≤ μ₂) (ht₁ : μ₁ Set.univ ≤ 1) (ht₂ : μ₂ Set.univ ≤ 1)
    {ε₁ ε₂ : ℝ≥0∞}
    (he₁ : μ₁ Set.univ ≤ ν₁ Set.univ+ε₁) (he₂ : μ₂ Set.univ ≤ ν₂ Set.univ+ε₂)
    (S : Set (α × β)) :
    μ₁.prod μ₂ S ≤ ν₁.prod ν₂ S+ε₁+ε₂ := by
  let δ₁ := μ₁-ν₁
  let δ₂ := μ₂-ν₂
  have hd₁ : δ₁+ν₁=μ₁ := Measure.sub_add_cancel_of_le h₁
  have hd₂ : δ₂+ν₂=μ₂ := Measure.sub_add_cancel_of_le h₂
  have hδ₁ : δ₁ Set.univ ≤ ε₁ := by
    rw [show δ₁ = μ₁-ν₁ from rfl,Measure.sub_apply MeasurableSet.univ h₁]
    exact tsub_le_iff_right.mpr (by simpa only [add_comm] using he₁)
  have hδ₂ : δ₂ Set.univ ≤ ε₂ := by
    rw [show δ₂ = μ₂-ν₂ from rfl,Measure.sub_apply MeasurableSet.univ h₂]
    exact tsub_le_iff_right.mpr (by simpa only [add_comm] using he₂)
  have hν₁ : ν₁ Set.univ ≤ 1 := (h₁ Set.univ).trans ht₁
  have hp₁ : δ₁.prod μ₂ S ≤ ε₁ := by
    calc
      _ ≤ δ₁.prod μ₂ Set.univ := measure_mono (Set.subset_univ _)
      _ = δ₁ Set.univ*μ₂ Set.univ := by rw [←Set.univ_prod_univ,Measure.prod_prod]
      _ ≤ ε₁*1 := mul_le_mul' hδ₁ ht₂
      _ = ε₁ := mul_one _
  have hp₂ : ν₁.prod δ₂ S ≤ ε₂ := by
    calc
      _ ≤ ν₁.prod δ₂ Set.univ := measure_mono (Set.subset_univ _)
      _ = ν₁ Set.univ*δ₂ Set.univ := by rw [←Set.univ_prod_univ,Measure.prod_prod]
      _ ≤ 1*ε₂ := mul_le_mul' hν₁ hδ₂
      _ = ε₂ := one_mul _
  calc
    μ₁.prod μ₂ S = δ₁.prod μ₂ S+ν₁.prod μ₂ S := by rw [←hd₁,Measure.add_prod,Measure.add_apply]
    _ = δ₁.prod μ₂ S+(ν₁.prod δ₂ S+ν₁.prod ν₂ S) := by
      congr 1
      rw [←hd₂,Measure.prod_add,Measure.add_apply]
    _ ≤ ε₁+(ε₂+ν₁.prod ν₂ S) := add_le_add hp₁ (add_le_add hp₂ le_rfl)
    _ = ν₁.prod ν₂ S+ε₁+ε₂ := by ac_rfl
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma rawPairEndpointLaw_truncation {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (e : Direction d) (x : Lattice d × Lattice d)
    {H : ℕ} (hH : 0 < H) (k : ℕ) (S : Set (Lattice d × Lattice d)) :
    rawPairEndpointLaw (realPosition (step e)) H ω x S ≤
      (truncatedEndpointLaw e H (k*H) ω x.1).prod (truncatedEndpointLaw e H (k*H) ω x.2) S+
      (1-(κ:ℝ≥0∞)^H)^k+(1-(κ:ℝ≥0∞)^H)^k := by
  let (y : Lattice d) : IsFiniteMeasure (hitKernel (Strip (realPosition (step e)) y H) (Upper (realPosition (step e)) y H) (ω,y)) :=
    ⟨lt_of_le_of_lt (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _) ENNReal.one_lt_top⟩
  apply product_submeasure_error
  · exact truncatedEndpointLaw_le e hH _ _ _
  · exact truncatedEndpointLaw_le e hH _ _ _
  · exact hitKernel_total_le_one (disjoint_strip_upper _ _ _) _
  · exact hitKernel_total_le_one (disjoint_strip_upper _ _ _) _
  · exact truncatedEndpointLaw_mass_error ω hκ e x.1 hH k
  · exact truncatedEndpointLaw_mass_error ω hκ e x.2 hH k

lemma rawPairEndpointLaw_compare {d : ℕ} (ω η : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (e : Direction d) (x : Lattice d × Lattice d)
    {H : ℕ} (hH : 0 < H) (k : ℕ)
    (he : Set.EqOn ω η (LatticeBall x.1 (k*H) ∪ LatticeBall x.2 (k*H)))
    (S : Set (Lattice d × Lattice d)) :
    rawPairEndpointLaw (realPosition (step e)) H ω x S ≤
      rawPairEndpointLaw (realPosition (step e)) H η x S+
      (1-(κ:ℝ≥0∞)^H)^k+(1-(κ:ℝ≥0∞)^H)^k := by
  have ht := rawPairEndpointLaw_truncation ω hκ e x hH k S
  rw [truncatedEndpointLaw_locality e hH _ ω η x.1 (he.mono Set.subset_union_left),
    truncatedEndpointLaw_locality e hH _ ω η x.2 (he.mono Set.subset_union_right)] at ht
  exact ht.trans (add_le_add (add_le_add
    ((Measure.prod_mono (truncatedEndpointLaw_le e hH _ _ _) (truncatedEndpointLaw_le e hH _ _ _)) S) le_rfl) le_rfl)

lemma rawPairEndpointLaw_uniform_locality {d : ℕ} {κ : ℝ≥0} (hκ : 0 < κ)
    (e : Direction d) {H : ℕ} (hH : 0 < H) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (ω η : Environment d),
      (∀ y g, κ ≤ (ω y).1 g) → (∀ y g, κ ≤ (η y).1 g) →
      ∀ x : Lattice d × Lattice d,
      Set.EqOn ω η (LatticeBall x.1 N ∪ LatticeBall x.2 N) →
      ∀ S : Set (Lattice d × Lattice d),
      rawPairEndpointLaw (realPosition (step e)) H ω x S ≤
        rawPairEndpointLaw (realPosition (step e)) H η x S+ε ∧
      rawPairEndpointLaw (realPosition (step e)) H η x S ≤
        rawPairEndpointLaw (realPosition (step e)) H ω x S+ε := by
  have hc : 1-(κ:ℝ≥0∞)^H < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (pow_ne_zero _ (by exact_mod_cast hκ.ne'))
  have heps : 0 < ε/2 := ENNReal.div_pos_iff.mpr ⟨hε.ne',by norm_num⟩
  obtain ⟨k,hk⟩ := ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc).eventually_lt_const heps).exists
  have hs : (1-(κ:ℝ≥0∞)^H)^k+(1-(κ:ℝ≥0∞)^H)^k ≤ ε := by
    calc
      _ ≤ ε/2+ε/2 := add_le_add hk.le hk.le
      _ = ε := ENNReal.add_halves ε
  refine ⟨k*H,?_⟩
  intro ω η hω hη x he S
  constructor
  · exact (rawPairEndpointLaw_compare ω η hω e x hH k he S).trans
      (by simpa only [add_assoc] using add_le_add_right hs (rawPairEndpointLaw (realPosition (step e)) H η x S))
  · exact (rawPairEndpointLaw_compare η ω hη e x hH k he.symm S).trans
      (by simpa only [add_assoc] using add_le_add_right hs (rawPairEndpointLaw (realPosition (step e)) H ω x S))
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_OutwardKernelElementary
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.truncatedEndpointLaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma outwardKernelMass_lower {d : ℕ} (e f : Direction d) (H : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ:ℝ)^(2*H) ≤ outwardKernelMass e f H x ω := by
  let S := {y : Lattice d × Lattice d | signedCoordinate f (x.2-x.1) ≤ signedCoordinate f (y.2-y.1)}
  have hlow : ((κ:ℝ≥0∞)^2)^H ≤ rawPairEndpointLaw (realPosition (step e)) H ω x S := by
    induction H with
    | zero => simp [rawPairEndpointLaw_zero,S]
    | succ H ih =>
      have hh := rawPairEndpointLaw_upward e H ω x hκ S
      rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet] at hh
      have hpre : pairUp e ⁻¹' S=S := by
        ext y
        simp only [S,Set.mem_preimage,Set.mem_ofPred,pairUp_preserves_gap]
      rw [hpre] at hh
      apply le_trans _ hh
      rw [pow_succ']
      exact mul_le_mul_right ih _
  have hfinite : rawPairEndpointLaw (realPosition (step e)) H ω x S ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((measure_mono (Set.subset_univ _)).trans (rawPairEndpointLaw_total_le_one _ _ _ _))
  have hh := ENNReal.toReal_mono hfinite hlow
  simpa only [ENNReal.toReal_pow,ENNReal.coe_toReal,←pow_mul,outwardKernelMass,S] using hh

lemma rawPairEndpointLaw_upper_congr {d : ℕ} (e : Direction d) (H : ℕ)
    (a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a)
    (ω η : Environment d) (he : Set.EqOn ω η {y | a ≤ dot (realPosition y) (realPosition (step e))}) :
    rawPairEndpointLaw (realPosition (step e)) H ω x = rawPairEndpointLaw (realPosition (step e)) H η x := by
  have h₁ : Set.EqOn ω η (Strip (realPosition (step e)) x.1 H) := by
    intro y hy
    apply he
    change a ≤ dot (realPosition y) (realPosition (step e))
    simpa only [hx.1] using hy.1
  have h₂ : Set.EqOn ω η (Strip (realPosition (step e)) x.2 H) := by
    intro y hy
    apply he
    change a ≤ dot (realPosition y) (realPosition (step e))
    simpa only [hx.2] using hy.1
  unfold rawPairEndpointLaw
  rw [hitKernel_congr _ _ ω η h₁,hitKernel_congr _ _ ω η h₂]
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_UpperPairPatch
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma upperPairPatch_measurable {d : ℕ} (e : Direction d) (a : ℝ)
    (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a) (N : ℕ) :
    @Measurable _ _ (rowSigma (upperPairNeighborhood e a x N)) _ (upperPairPatch e a x N) := by
  have hx₁ : x.1 ∈ upperPairNeighborhood e a x N := by
    refine ⟨Or.inl ?_,?_⟩
    · simp [LatticeBall]
    · exact le_of_eq hx.1.symm
  refine @Measurable.of_eval _ _ _ (rowSigma (upperPairNeighborhood e a x N)) _ _ ?_
  intro y
  by_cases hy : y ∈ upperPairNeighborhood e a x N
  · simpa only [upperPairPatch,ite_eq_left hy] using measurable_row_on hy
  · simpa only [upperPairPatch,ite_eq_right hy] using measurable_row_on hx₁

lemma upperPairPatch_elliptic {d : ℕ} (e : Direction d) (a : ℝ)
    (x : Lattice d × Lattice d) (N : ℕ) (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y g, κ ≤ (ω y).1 g) :
    ∀ y g, κ ≤ ((upperPairPatch e a x N ω) y).1 g := by
  intro y g
  by_cases hy : y ∈ upperPairNeighborhood e a x N <;>
    simp only [upperPairPatch,hy,ite_true, if_true,ite_false, if_false] <;> apply hκ

lemma rawPairEndpointLaw_upper_patch_locality {d : ℕ} {κ : ℝ≥0} (hκ : 0 < κ)
    (e : Direction d) {H : ℕ} (hH : 0 < H) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∀ (ω : Environment d), (∀ y g, κ ≤ (ω y).1 g) →
      ∀ S : Set (Lattice d × Lattice d),
      rawPairEndpointLaw (realPosition (step e)) H ω x S ≤
        rawPairEndpointLaw (realPosition (step e)) H (upperPairPatch e a x N ω) x S+ε ∧
      rawPairEndpointLaw (realPosition (step e)) H (upperPairPatch e a x N ω) x S ≤
        rawPairEndpointLaw (realPosition (step e)) H ω x S+ε := by
  obtain ⟨N,hN⟩ := rawPairEndpointLaw_uniform_locality hκ e hH hε
  refine ⟨N,?_⟩
  intro a x hx ω hω S
  let η : Environment d := fun y => if a ≤ dot (realPosition y) (realPosition (step e)) then ω y else ω x.1
  have hη : ∀ y g, κ ≤ (η y).1 g := by
    intro y g
    dsimp [η]
    split_ifs <;> apply hω
  have he : Set.EqOn η (upperPairPatch e a x N ω) (LatticeBall x.1 N ∪ LatticeBall x.2 N) := by
    intro y hy
    by_cases ha : a ≤ dot (realPosition y) (realPosition (step e))
    · simp [η,upperPairPatch,upperPairNeighborhood,hy,ha]
    · simp [η,upperPairPatch,upperPairNeighborhood,ha]
  have hsame : rawPairEndpointLaw (realPosition (step e)) H ω x = rawPairEndpointLaw (realPosition (step e)) H η x := by
    apply rawPairEndpointLaw_upper_congr e H a x hx
    intro y hy
    change a ≤ dot (realPosition y) (realPosition (step e)) at hy
    simp only [η,ite_eq_left hy]
  rw [hsame]
  exact hN η (upperPairPatch e a x N ω) hη (upperPairPatch_elliptic e a x N ω hω) x he S
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_FiniteLogStability
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma finiteLogExcess_eq_ciSup {Ω : Type*} (A : ℝ) (p : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    finiteLogExcess A p N ω = ⨆ n : Fin (N+1), max (-Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2)) 0 := by
  unfold finiteLogExcess
  rw [ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal']

lemma finiteLogExcess_stability {Ω : Type*} (A : ℝ) (p q : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hpq : ∀ n ≤ N, |Real.log (p n ω)-Real.log (q n ω)| ≤ ε) :
    |finiteLogExcess A p N ω-finiteLogExcess A q N ω| ≤ ε := by
  have one_side (p q : ℕ → Ω → ℝ)
      (hpq : ∀ n ≤ N, |Real.log (p n ω)-Real.log (q n ω)| ≤ ε) :
      finiteLogExcess A p N ω ≤ finiteLogExcess A q N ω+ε := by
    rw [finiteLogExcess_eq_ciSup]
    apply ciSup_le
    intro n
    have hq : max (-Real.log (q n ω)-2*A*Real.log ((n:ℝ)+2)) 0 ≤ finiteLogExcess A q N ω := by
      rw [finiteLogExcess_eq_ciSup]
      exact le_ciSup (Set.finite_range (fun k : Fin (N+1) => max (-Real.log (q k ω)-2*A*Real.log ((k:ℝ)+2)) 0)).bddAbove n
    have hh := (abs_le.mp (hpq n (by omega))).1
    apply (max_le_max (by linarith : -Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2) ≤
      -Real.log (q n ω)-2*A*Real.log ((n:ℝ)+2)+ε) (show (0:ℝ) ≤ 0+ε by linarith)).trans
    simpa only [max_add_add_right] using add_le_add_left hq ε
  have h₁ := one_side p q hpq
  have h₂ := one_side q p (fun n hn => by simpa only [abs_sub_comm] using hpq n hn)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma log_uniform_on_positive_interval {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p q : ℝ, c ≤ p → p ≤ 1 → c ≤ q → q ≤ 1 → |p-q| < δ →
      |Real.log p-Real.log q| < ε := by
  have hcont : ContinuousOn Real.log (Set.Icc c 1) :=
    Real.continuousOn_log.mono (fun x hx => ne_of_gt (hc.trans_le hx.1))
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨δ,hδ,?_⟩
  intro p q hp hp1 hq hq1 hdif
  exact hd p ⟨hp,hp1⟩ q ⟨hq,hq1⟩ hdif
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma outwardKernelMass_le_one {d : ℕ} (e f : Direction d) (H : ℕ)
    (x : Lattice d × Lattice d) (ω : Environment d) : outwardKernelMass e f H x ω ≤ 1 := by
  have hh := ENNReal.toReal_mono ENNReal.one_ne_top
    ((measure_mono (Set.subset_univ {y : Lattice d × Lattice d | signedCoordinate f (x.2-x.1) ≤ signedCoordinate f (y.2-y.1)})).trans (rawPairEndpointLaw_total_le_one (realPosition (step e)) H ω x))
  simpa only [outwardKernelMass,ENNReal.toReal_one] using hh

lemma outwardLog_fixed_height_locality {d : ℕ} {κ : ℝ≥0} (hκ : 0 < κ)
    (e f : Direction d) {H : ℕ} (hH : 0 < H) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∀ (ω : Environment d), (∀ y g, κ ≤ (ω y).1 g) →
      |Real.log (outwardKernelMass e f H x ω)-
        Real.log (outwardKernelMass e f H x (upperPairPatch e a x N ω))| < ε := by
  have hκr : 0 < (κ:ℝ) := by exact_mod_cast hκ
  obtain ⟨δ,hδ,hlog⟩ := log_uniform_on_positive_interval (pow_pos hκr (2*H)) hε
  obtain ⟨N,hN⟩ := rawPairEndpointLaw_upper_patch_locality hκ e hH
    (ENNReal.ofReal_pos.mpr (show 0 < δ/2 by linarith))
  refine ⟨N,?_⟩
  intro a x hx ω hω
  let η := upperPairPatch e a x N ω
  have hη := upperPairPatch_elliptic e a x N ω hω
  apply hlog _ _ (outwardKernelMass_lower e f H ω x (fun y => hω y e))
    (outwardKernelMass_le_one e f H x ω)
    (outwardKernelMass_lower e f H η x (fun y => hη y e))
    (outwardKernelMass_le_one e f H x η)
  let S := {y : Lattice d × Lattice d | signedCoordinate f (x.2-x.1) ≤ signedCoordinate f (y.2-y.1)}
  have hfin (ζ : Environment d) : rawPairEndpointLaw (realPosition (step e)) H ζ x S ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((measure_mono (Set.subset_univ _)).trans (rawPairEndpointLaw_total_le_one _ _ _ _))
  have hh := hN a x hx ω hω S
  have h₁ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin η,ENNReal.ofReal_ne_top⟩) hh.1
  have h₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin ω,ENNReal.ofReal_ne_top⟩) hh.2
  rw [ENNReal.toReal_add (hfin η) ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal (by linarith : 0 ≤ δ/2)] at h₁
  rw [ENNReal.toReal_add (hfin ω) ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal (by linarith : 0 ≤ δ/2)] at h₂
  change outwardKernelMass e f H x ω ≤ outwardKernelMass e f H x η+δ/2 at h₁
  change outwardKernelMass e f H x η ≤ outwardKernelMass e f H x ω+δ/2 at h₂
  exact abs_lt.mpr ⟨by linarith,by linarith⟩
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_FiniteOutwardRowApproximation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma upperPairNeighborhood_mono {d : ℕ} (e : Direction d) (a : ℝ)
    (x : Lattice d × Lattice d) {N R : ℕ} (hNR : N ≤ R) :
    upperPairNeighborhood e a x N ⊆ upperPairNeighborhood e a x R := by
  intro y hy
  refine ⟨?_,hy.2⟩
  have hball (z : Lattice d) : LatticeBall z N ⊆ LatticeBall z R := by
    intro w hw i
    exact (hw i).trans (by exact_mod_cast hNR)
  exact hy.1.elim (fun h => Or.inl (hball _ h)) (fun h => Or.inr (hball _ h))

lemma finite_outward_upper_row_approximation {d : ℕ} {κ : ℝ≥0} (hκ : 0 < κ)
    (e f : Direction d) (A : ℝ) (N : ℕ) {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ R : ℕ, ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ F : Environment d → ℝ,
      @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ F ∧
      (∀ ω, 0 ≤ F ω ∧ F ω ≤ B) ∧
      (∀ ω, (∀ y g, κ ≤ (ω y).1 g) →
        |min (finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω) B-F ω| ≤ ε) := by
  have hloc (n : ℕ) := outwardLog_fixed_height_locality hκ e f (Nat.succ_pos n) hε
  choose r hr using hloc
  obtain ⟨R,hR⟩ := ((Finset.range (N+1)).image r).exists_le
  refine ⟨R,?_⟩
  intro a x hx
  let q : ℕ → Environment d → ℝ := fun n ω => outwardKernelMass e f (n+1) x (upperPairPatch e a x (r n) ω)
  let F : Environment d → ℝ := fun ω => min (finiteLogExcess A q N ω) B
  refine ⟨F,?_,?_,?_⟩
  · have hm : @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ (finiteLogExcess A q N) := by
      unfold finiteLogExcess
      apply Measurable.ennreal_toReal
      apply Measurable.iSup
      intro n
      have hnr : r n ≤ R := hR (r n) (Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr n.isLt,rfl⟩)
      have hp := (upperPairPatch_measurable e a x hx (r n)).mono
        (rowSigma_mono (upperPairNeighborhood_mono e a x hnr)) le_rfl
      have hq := (measurable_outwardKernelMass e f (n+1) x).comp hp
      exact (hq.log.neg.sub_const _).ennreal_ofReal
    exact hm.min measurable_const
  · intro ω
    exact ⟨le_min ENNReal.toReal_nonneg hB,min_le_right _ _⟩
  · intro ω hω
    have hd := finiteLogExcess_stability A (fun n => outwardKernelMass e f (n+1) x) q N ω hε.le
      (fun n hn => (hr n a x hx ω hω).le)
    have h₁ := (abs_le.mp hd).1
    have h₂ := (abs_le.mp hd).2
    apply abs_le.mpr
    constructor
    · have hh : min (finiteLogExcess A q N ω) B ≤ min (finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω) B+ε := by
        have ht := min_le_min (show finiteLogExcess A q N ω ≤ finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω+ε by linarith) (show B ≤ B+ε by linarith)
        simpa only [min_add_add_right] using ht
      exact by dsimp [F] <;> linarith
    · have hh : min (finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω) B ≤ min (finiteLogExcess A q N ω) B+ε := by
        have ht := min_le_min (show finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω ≤ finiteLogExcess A q N ω+ε by linarith) (show B ≤ B+ε by linarith)
        simpa only [min_add_add_right] using ht
      exact by dsimp [F] <;> linarith
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OutwardCapLocality
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma outward_canonical_cap_locality_of_log_bound {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e f : Direction d) {A D B : ℝ} (hA : 0 < A) (hD : 0 < D) (hB : 0 < B)
    (hdata : ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ W : Environment d → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
        Integrable (fun ω => Real.exp (W ω)) (environmentLaw ν) ∧
        (∫ ω, Real.exp (W ω) ∂environmentLaw ν) ≤ B ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ t : ℕ,
          0 < outwardKernelMass e f (t+1) x ω ∧
          -Real.log (outwardKernelMass e f (t+1) x ω) ≤
            A*Real.log ((t:ℝ)+2)+D*(W ω+1))) :
    ∀ C ε δ : ℝ, 0 < C → 0 < ε → 0 < δ → ∃ R : ℕ,
      ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ F : Environment d → ℝ,
      @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ F ∧
      (∀ ω, 0 ≤ F ω ∧ F ω ≤ C) ∧
      (environmentLaw ν).real {ω | ε < |min (outwardCanonicalExcess e f A x ω) C-F ω|} < δ := by
  obtain ⟨κ,hκ,hκae⟩ := environment_uniform_elliptic ν hue
  intro C ε δ hC hε hδ
  let M := Real.log (B/δ+1)
  have harg : 0 < B/δ+1 := by positivity
  have heM : Real.exp M = B/δ+1 := Real.exp_log harg
  have hprob : B/Real.exp M < δ := by
    apply (div_lt_iff₀ (Real.exp_pos M)).mpr
    rw [heM,mul_add,mul_one,mul_div_cancel₀ B hδ.ne']
    linarith
  obtain ⟨N,hN⟩ := exists_log_height_cutoff (D:=D) (M:=M) hA
  obtain ⟨R,hR⟩ := finite_outward_upper_row_approximation hκ e f A N hε hC.le
  refine ⟨R,?_⟩
  intro a x hx
  obtain ⟨F,hF,hFb,hFerr⟩ := hR a x hx
  refine ⟨F,hF,hFb,?_⟩
  obtain ⟨W,hW,hW0,hWi,hWB,hbound⟩ := hdata a x hx
  have hcut := canonical_height_cutoff_probability (environmentLaw ν) hA.le hD.le
    (fun n => outwardKernelMass e f (n+1) x) W hWi hWB
    (hbound.mono fun ω hω n => (hω n).2) N hN
  have hs : ∀ᵐ ω ∂environmentLaw ν,
      (ε < |min (outwardCanonicalExcess e f A x ω) C-F ω|) →
      canonicalLogExcess A (fun n => outwardKernelMass e f (n+1) x) ω ≠
        finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω := by
    filter_upwards [hκae] with ω hω herr heq
    have hh := hFerr ω hω
    change ε < |min (canonicalLogExcess A (fun n => outwardKernelMass e f (n+1) x) ω) C-F ω| at herr
    rw [heq] at herr
    exact (not_lt_of_ge hh) herr
  have hm := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs)
  exact (hm.trans hcut).trans_lt hprob

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_OutwardOrder
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma outward_canonical_bound_of_log_bound {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) {A D B : ℝ} (hA : 0 < A) (hD : 0 < D) (hB : 0 < B)
    (hdata : ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ W : Environment d → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
        Integrable (fun ω => Real.exp (W ω)) (environmentLaw ν) ∧
        (∫ ω, Real.exp (W ω) ∂environmentLaw ν) ≤ B ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ t : ℕ,
          0 < outwardKernelMass e f (t+1) x ω ∧
          -Real.log (outwardKernelMass e f (t+1) x ω) ≤
            A*Real.log ((t:ℝ)+2)+D*(W ω+1))) :
    ∃ c B' : ℝ, 0 < c ∧ 0 < B' ∧
      ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      let Z := outwardCanonicalExcess e f A x
      (∀ ω, 0 ≤ Z ω) ∧
      @Measurable _ _ (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}) _ Z ∧
      Integrable (fun ω => Real.exp (c*Z ω)) (environmentLaw ν) ∧
      (∫ ω, Real.exp (c*Z ω) ∂environmentLaw ν) ≤ B' ∧
      (∀ᵐ ω ∂environmentLaw ν, ∀ t : ℕ,
        0 < outwardKernelMass e f (t+1) x ω ∧
        -Real.log (outwardKernelMass e f (t+1) x ω) ≤ 2*A*Real.log ((t:ℝ)+2)+Z ω) := by
  refine ⟨D⁻¹,Real.exp 1*B,inv_pos.mpr hD,mul_pos (Real.exp_pos _) hB,?_⟩
  intro a x hx
  obtain ⟨W,hW,hW0,hWi,hWB,hbound⟩ := hdata a x hx
  let Z := outwardCanonicalExcess e f A x
  have hZm : Measurable Z := measurable_outwardCanonicalExcess e f A x
  have hZbound : ∀ᵐ ω ∂environmentLaw ν, Z ω ≤ D*(W ω+1) ∧
      ∀ n, -Real.log (outwardKernelMass e f (n+1) x ω) ≤ 2*A*Real.log ((n:ℝ)+2)+Z ω := by
    filter_upwards [hbound] with ω hω
    exact canonicalLogExcess_bounds hA.le hD.le (hW0 ω) _ ω (fun n => (hω n).2)
  have hdom : Integrable (fun ω => Real.exp 1*Real.exp (W ω)) (environmentLaw ν) := hWi.const_mul _
  have hexp : ∀ᵐ ω ∂environmentLaw ν, Real.exp (D⁻¹*Z ω) ≤ Real.exp 1*Real.exp (W ω) := by
    filter_upwards [hZbound] with ω hω
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hω.1 (inv_nonneg.mpr hD.le)
    rw [←mul_assoc,inv_mul_cancel₀ hD.ne',one_mul] at hh
    linarith
  have hZi : Integrable (fun ω => Real.exp (D⁻¹*Z ω)) (environmentLaw ν) :=
    hdom.mono_nonneg (hZm.const_mul _ |>.exp |>.aestronglyMeasurable)
      (Eventually.of_forall (fun ω => (Real.exp_pos _).le)) hexp
  refine ⟨fun ω => canonicalLogExcess_nonneg _ _ ω,outwardCanonicalExcess_upper_rows e f A a x hx,hZi,?_,?_⟩
  · calc
      _ ≤ ∫ ω, Real.exp 1*Real.exp (W ω) ∂environmentLaw ν := integral_mono_ae hZi hdom hexp
      _ = Real.exp 1*(∫ ω, Real.exp (W ω) ∂environmentLaw ν) := integral_const_mul _ _
      _ ≤ Real.exp 1*B := mul_le_mul_of_nonneg_left hWB (Real.exp_pos _).le
  · filter_upwards [hbound,hZbound] with ω hω hZω
    exact fun n => ⟨(hω n).1,hZω.2 n⟩

theorem actual_outward_order {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A c B : ℝ, 0 < A ∧ 0 < c ∧ 0 < B ∧
      (∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
        let Z := outwardCanonicalExcess e f A x
        (∀ ω, 0 ≤ Z ω) ∧
        @Measurable _ _ (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}) _ Z ∧
        Integrable (fun ω => Real.exp (c*Z ω)) (environmentLaw ν) ∧
        (∫ ω, Real.exp (c*Z ω) ∂environmentLaw ν) ≤ B ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ t : ℕ,
          0 < outwardKernelMass e f (t+1) x ω ∧
          -Real.log (outwardKernelMass e f (t+1) x ω) ≤ 2*A*Real.log ((t:ℝ)+2)+Z ω)) ∧
      (∀ C ε δ : ℝ, 0 < C → 0 < ε → 0 < δ → ∃ R : ℕ,
        ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
        ∃ F : Environment d → ℝ,
          @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ F ∧
          (∀ ω, 0 ≤ F ω ∧ F ω ≤ C) ∧
          (environmentLaw ν).real {ω | ε < |min (outwardCanonicalExcess e f A x ω) C-F ω|} < δ) := by
  obtain ⟨A,D,B,hA,hD,hB,hdata⟩ := actual_outward_log_bound ν hue e f hef htrans
  obtain ⟨c,B',hc,hB',hbound⟩ := outward_canonical_bound_of_log_bound ν e f hA hD hB hdata
  exact ⟨A,c,B',hA,hc,hB',hbound,
    outward_canonical_cap_locality_of_log_bound ν hue e f hA hD hB hdata⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TailSampling
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace TailSampling

variable {D X : Type*} [MeasurableSpace D] [MeasurableSpace X]

lemma cutKernel_apply (w : Kernel D X) (S : ℤ → Set X)
    (hS : ∀ j, MeasurableSet (S j)) (j : D → ℤ) (hj : Measurable j) (d : D) :
    cutKernel w S hS j hj d = (w d (S (j d)))⁻¹ • (w d).restrict (S (j d)) := rfl

lemma cutKernel_markov (w : Kernel D X) (S : ℤ → Set X)
    (hS : ∀ j, MeasurableSet (S j)) (j : D → ℤ) (hj : Measurable j)
    (hpos : ∀ d, w d (S (j d)) ≠ 0) (hfin : ∀ d, w d (S (j d)) ≠ ∞) :
    IsMarkovKernel (cutKernel w S hS j hj) := by
  constructor
  intro d
  constructor
  simp only [cutKernel_apply, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact ENNReal.inv_mul_cancel (hpos d) (hfin d)

lemma cutKernel_supported (w : Kernel D X) (S : ℤ → Set X)
    (hS : ∀ j, MeasurableSet (S j)) (j : D → ℤ) (hj : Measurable j) (d : D) :
    ∀ᵐ x ∂cutKernel w S hS j hj d, x ∈ S (j d) := by
  exact Measure.ae_smul_measure (ae_restrict_mem (hS (j d))) _

lemma coordinate_atom_pos (μ : Measure X) [IsFiniteMeasure μ]
    [MeasurableSingletonClass X] (ξ : X → ℤ) (hξ : Measurable ξ)
    (hsurj : Function.Surjective ξ) (hμ : ∀ x, 0 < μ.real {x}) (z : ℤ) :
    0 < (μ.map ξ).real {z} := by
  obtain ⟨x,hx⟩ := hsurj z
  rw [Measure.real, Measure.map_apply hξ (measurableSet_singleton z)]
  apply lt_of_lt_of_le (hμ x)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro y hy
  simp only [Set.mem_singleton_iff] at hy
  subst y
  exact hx

end TailSampling

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ProfileGrowth2
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.truncatedEndpointLaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma horizontal_coordinate_surjective {d : ℕ} (e : Direction d) (f : Fin d)
    (hef : e.1 ≠ f) : Function.Surjective (fun x : HorizontalLayer e => x.1 f) := by
  intro z
  refine ⟨⟨Pi.single f z, ?_⟩, ?_⟩
  · simp [Ne.symm hef]
  · simp

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TailProfile
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.truncatedEndpointLaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailSampling

variable {D X : Type*} [MeasurableSpace D] [MeasurableSpace X]
    [MeasurableSingletonClass X]

theorem measurable_profile_cuts (w : Kernel D X) [IsFiniteKernel w]
    (ξ : X → ℤ) (hξ : Measurable ξ) (hsurj : Function.Surjective ξ)
    (hfull : ∀ d x, 0 < (w d).real {x}) :
    ∃ j : ℕ → D → ℤ, (∀ r, Measurable (j r)) ∧
      (∀ d (r : ℕ) (k : ℤ), TailCuts.score (TailCuts.lower ((w d).map ξ))
        (TailCuts.upper ((w d).map ξ)) (r : ℤ) k ≤
        TailCuts.score (TailCuts.lower ((w d).map ξ))
        (TailCuts.upper ((w d).map ξ)) (r : ℤ) (j r d)) ∧
      (∀ d, Tendsto (fun r => j r d) atTop atBot ∧
        Tendsto (fun r => j r d + (r : ℤ)) atTop atTop) := by
  have hpos : ∀ d z, 0 < ((w d).map ξ).real {z} :=
    fun d => coordinate_atom_pos (w d) ξ hξ hsurj (hfull d)
  have hL : ∀ n, Measurable (fun d => TailCuts.lower ((w d).map ξ) n) := by
    intro n
    have hh := ((w.map ξ).measurable_coe (s := Set.Iic n) measurableSet_Iic).ennreal_toReal
    simpa only [TailCuts.lower, Measure.real, Kernel.map_apply _ hξ] using hh
  have hU : ∀ n, Measurable (fun d => TailCuts.upper ((w d).map ξ) n) := by
    intro n
    have hh := ((w.map ξ).measurable_coe (s := Set.Ici n) measurableSet_Ici).ennreal_toReal
    simpa only [TailCuts.upper, Measure.real, Kernel.map_apply _ hξ] using hh
  have hex : ∀ r : ℕ, ∃ j : D → ℤ, Measurable j ∧
      ∀ d k, TailCuts.score (TailCuts.lower ((w d).map ξ))
        (TailCuts.upper ((w d).map ξ)) (r : ℤ) k ≤
        TailCuts.score (TailCuts.lower ((w d).map ξ))
        (TailCuts.upper ((w d).map ξ)) (r : ℤ) (j d) := by
    intro r
    exact TailCuts.measurable_maximizing_cut _ _ (r : ℤ) hL hU
      (fun d => (TailCuts.finite_profile_cuts_escape ((w d).map ξ) (hpos d)).1 _)
  choose j hj hmax using hex
  refine ⟨j,hj,fun d r => hmax r d,fun d => ?_⟩
  exact (TailCuts.finite_profile_cuts_escape ((w d).map ξ) (hpos d)).2
    (fun r => j r d) (fun r k => hmax r d k)

lemma lowerKernel_markov (w : Kernel D X) [IsFiniteKernel w]
    (ξ : X → ℤ) (hξ : Measurable ξ) (hsurj : Function.Surjective ξ)
    (hfull : ∀ d x, 0 < (w d).real {x}) (j : D → ℤ) (hj : Measurable j) :
    IsMarkovKernel (lowerKernel w ξ hξ j hj) := by
  apply cutKernel_markov
  · intro d
    have ht := TailCuts.lower_pos ((w d).map ξ)
      (coordinate_atom_pos (w d) ξ hξ hsurj (hfull d)) (j d)
    rw [TailCuts.lower, Measure.real, Measure.map_apply hξ measurableSet_Iic] at ht
    exact (ENNReal.toReal_pos_iff.mp ht).1.ne'
  · exact fun d => measure_ne_top _ _

lemma upperKernel_markov (w : Kernel D X) [IsFiniteKernel w]
    (ξ : X → ℤ) (hξ : Measurable ξ) (hsurj : Function.Surjective ξ)
    (hfull : ∀ d x, 0 < (w d).real {x}) (j : D → ℤ) (hj : Measurable j) :
    IsMarkovKernel (upperKernel w ξ hξ j hj) := by
  apply cutKernel_markov
  · intro d
    have ht := TailCuts.upper_pos ((w d).map ξ)
      (coordinate_atom_pos (w d) ξ hξ hsurj (hfull d)) (j d)
    rw [TailCuts.upper, Measure.real, Measure.map_apply hξ measurableSet_Ici] at ht
    exact (ENNReal.toReal_pos_iff.mp ht).1.ne'
  · exact fun d => measure_ne_top _ _

omit [MeasurableSingletonClass X] in
lemma lowerKernel_supported [MeasurableSingletonClass X]
    (w : Kernel D X) (ξ : X → ℤ) (hξ : Measurable ξ)
    (j : D → ℤ) (hj : Measurable j) (d : D) :
    ∀ᵐ x ∂lowerKernel w ξ hξ j hj d, ξ x ≤ j d :=
  cutKernel_supported _ _ _ _ _ _

omit [MeasurableSingletonClass X] in
lemma upperKernel_supported [MeasurableSingletonClass X]
    (w : Kernel D X) (ξ : X → ℤ) (hξ : Measurable ξ)
    (j : D → ℤ) (hj : Measurable j) (d : D) :
    ∀ᵐ x ∂upperKernel w ξ hξ j hj d, j d ≤ ξ x :=
  cutKernel_supported _ _ _ _ _ _

end TailSampling

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma profilePairKernel_markov {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w]
    (hfull : ∀ z x, 0 < (w z).real {x}) (R : ℤ) (j : D → ℤ) (hj : Measurable j) :
    IsMarkovKernel (profilePairKernel e f w R j hj) := by
  have := TailSampling.lowerKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull j hj
  have := TailSampling.upperKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull (fun z => j z+R) (hj.add_const R)
  unfold profilePairKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_of_countable _)

lemma profilePairKernel_supported {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w]
    (hfull : ∀ z x, 0 < (w z).real {x}) (R : ℤ) (j : D → ℤ) (hj : Measurable j) (z : D) :
    ∀ᵐ p ∂profilePairKernel e f w R j hj z,
      p.1.1 f ≤ j z ∧ j z+R ≤ p.1.2 f := by
  have := TailSampling.lowerKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull j hj
  have := TailSampling.upperKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull (fun z => j z+R) (hj.add_const R)
  rw [profilePairKernel, Kernel.map_apply _ (measurable_of_countable _), Kernel.prod_apply]
  apply (ae_map_iff (measurable_of_countable _).aemeasurable
    ((Set.to_countable _).measurableSet)).mpr
  apply (Measure.ae_prod_iff_ae_ae ((Set.to_countable _).measurableSet)).mpr
  filter_upwards [TailSampling.lowerKernel_supported w (fun x => x.1 f)
    (measurable_of_countable _) j hj z] with x hx
  filter_upwards [TailSampling.upperKernel_supported w (fun x => x.1 f)
    (measurable_of_countable _) (fun z => j z+R) (hj.add_const R) z] with y hy
  exact ⟨hx,hy⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OutwardCapL1
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bounded_probability_error_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω → ℝ) (hm : Measurable h)
    {C ε : ℝ} (hε : 0 ≤ ε) (hb : ∀ ω, 0 ≤ h ω ∧ h ω ≤ C) :
    (∫ ω, h ω ∂μ) ≤ ε+C*μ.real {ω | ε < h ω} := by
  let E := {ω | ε < h ω}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hm
  have hg : Integrable (fun ω => ε+E.indicator (fun _ => C) ω) μ :=
    (integrable_const _).add ((integrable_const _).indicator hE)
  have hh : ∀ ω, h ω ≤ ε+E.indicator (fun _ => C) ω := by
    intro ω
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
      exact (hb ω).2.trans (by linarith)
    · rw [Set.indicator_of_notMem he,add_zero]
      exact le_of_not_gt he
  have hi : Integrable h μ := hg.mono_nonneg hm.aestronglyMeasurable
    (Eventually.of_forall fun ω => (hb ω).1) (Eventually.of_forall hh)
  have hle := integral_mono_ae hi hg (Eventually.of_forall hh)
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hE),
    integral_const,integral_indicator_const _ hE] at hle
  simpa only [probReal_univ,smul_eq_mul,one_mul,mul_one,mul_comm] using hle

lemma outward_cap_locality_L1 {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (e f : Direction d) (A : ℝ)
    (hloc : ∀ C ε δ : ℝ, 0 < C → 0 < ε → 0 < δ → ∃ R : ℕ,
      ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ F : Environment d → ℝ,
        @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ F ∧
        (∀ ω, 0 ≤ F ω ∧ F ω ≤ C) ∧
        (environmentLaw ν).real {ω | ε < |min (outwardCanonicalExcess e f A x ω) C-F ω|} < δ)
    {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ F : Environment d → ℝ,
        @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ F ∧
        (∀ ω, 0 ≤ F ω ∧ F ω ≤ C) ∧
        (∫ ω, |min (outwardCanonicalExcess e f A x ω) C-F ω| ∂environmentLaw ν) < ε := by
  obtain ⟨R,hR⟩ := hloc C (ε/2) (ε/(2*C)) hC (by positivity) (by positivity)
  refine ⟨R,?_⟩
  intro a x hx
  obtain ⟨F,hFm,hFb,hFerr⟩ := hR a x hx
  refine ⟨F,hFm,hFb,?_⟩
  have hFa : Measurable F := hFm.mono (rowSigma_le _) le_rfl
  have hh := bounded_probability_error_integral (environmentLaw ν)
    (fun ω => |min (outwardCanonicalExcess e f A x ω) C-F ω|)
    (((measurable_outwardCanonicalExcess e f A x).min measurable_const).sub hFa).abs
    (show 0 ≤ ε/2 by positivity) (C:=C) (fun ω => by
      refine ⟨abs_nonneg _,abs_le.mpr ⟨?_,?_⟩⟩
      · have hz : 0 ≤ min (outwardCanonicalExcess e f A x ω) C :=
          le_min (canonicalLogExcess_nonneg _ _ ω) hC.le
        linarith [(hFb ω).2]
      · linarith [min_le_right (outwardCanonicalExcess e f A x ω) C,(hFb ω).1])
  have hmul := mul_lt_mul_of_pos_left hFerr hC
  have heq : C*(ε/(2*C)) = ε/2 := by field_simp
  rw [heq] at hmul
  linarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma outward_order_countable_event {d : ℕ}
    (ν : Measure (Row d)) (e f : Direction d) (A : ℝ)
    (hbound : ∀ (a : ℝ) (x : Lattice d × Lattice d),
      x ∈ PairAtHeight (realPosition (step e)) a →
      ∀ᵐ ω ∂environmentLaw ν, ∀ t : ℕ,
        0 < outwardKernelMass e f (t+1) x ω ∧
        -Real.log (outwardKernelMass e f (t+1) x ω) ≤
          2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e f A x ω) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x : Lattice d × Lattice d,
      dot (realPosition x.1) (realPosition (step e)) =
        dot (realPosition x.2) (realPosition (step e)) →
      ∀ t : ℕ, 0 < outwardKernelMass e f (t+1) x ω ∧
        -Real.log (outwardKernelMass e f (t+1) x ω) ≤
          2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e f A x ω := by
  apply ae_all_iff.mpr
  intro x
  by_cases hx : dot (realPosition x.1) (realPosition (step e)) =
      dot (realPosition x.2) (realPosition (step e))
  · filter_upwards [hbound (dot (realPosition x.1) (realPosition (step e))) x ⟨rfl,hx.symm⟩] with ω hω
    exact fun _ => hω
  · exact Eventually.of_forall fun _ h => (hx h).elim

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_MeasurableCountableSample
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailDecorrelation

section SampledSites

variable {D I A J : Type*} [MeasurableSpace D] [MeasurableSpace A] [Encodable I]
variable [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
variable (δ : Measure D) (ν : Measure A) [IsProbabilityMeasure δ] [IsProbabilityMeasure ν]

omit [Encodable I] in
lemma measurable_countable_sample {Z : J → (I → A) → ℝ}
    (hZ : ∀ j, Measurable (Z j)) {j : D → J} (hj : Measurable j) :
    Measurable (fun x : D × (I → A) => Z (j x.1) x.2) := by
  have hm : Measurable (Function.uncurry Z) := measurable_from_prod_countable_right hZ
  exact hm.comp ((hj.comp measurable_fst).prodMk measurable_snd)

omit [Encodable I] in
lemma sampled_exponential_integrable {Z : J → (I → A) → ℝ} {s Q : ℝ}
    (hZ : ∀ j, Measurable (Z j))
    (he : ∀ j, Integrable (fun ω => Real.exp (s * Z j ω)) (Measure.infinitePi (fun _ : I => ν)))
    (heQ : ∀ j, (∫ ω, Real.exp (s * Z j ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ Q)
    {j : D → J} (hj : Measurable j) :
    Integrable (fun x : D × (I → A) => Real.exp (s * Z (j x.1) x.2))
      (δ.prod (Measure.infinitePi (fun _ : I => ν))) ∧
    (∫ x : D × (I → A), Real.exp (s * Z (j x.1) x.2)
      ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤ Q := by
  let P := Measure.infinitePi (fun _ : I => ν)
  let F : D × (I → A) → ℝ := fun x => Real.exp (s * Z (j x.1) x.2)
  have hF : Measurable F := Real.measurable_exp.comp
    (measurable_const.mul (measurable_countable_sample hZ hj))
  have hFm : Measurable (fun d => ∫ ω, F (d, ω) ∂P) := hF.stronglyMeasurable.integral_prod_right.measurable
  have hFi : Integrable (fun d => ∫ ω, F (d, ω) ∂P) δ :=
    integrable_bounded_nonneg hFm (fun d => integral_nonneg fun ω => (Real.exp_pos _).le)
      (fun d => heQ (j d))
  have hi : Integrable F (δ.prod P) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun d => he (j d)), ?_⟩
    simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hFi
  refine ⟨hi, ?_⟩
  change (∫ x, F x ∂δ.prod P) ≤ Q
  rw [integral_prod _ hi]
  calc
    (∫ d, ∫ ω, F (d, ω) ∂P ∂δ) ≤ (∫ _ : D, Q ∂δ) := integral_mono hFi (integrable_const Q) (fun d => heQ (j d))
    _ = Q := by simp

omit [Encodable I] [IsProbabilityMeasure δ] [IsProbabilityMeasure ν] in
lemma sampled_locality {Z : J → (I → A) → ℝ}
    (N : ℕ → J → Set I) (j : ℕ → D → J) (hj : ∀ r, Measurable (j r))
    (hloc : ∀ K η : ℝ, 0 < K → 0 < η → ∃ n : ℕ, ∃ F : J → (I → A) → ℝ,
      (∀ a, @Measurable _ _ (rows (N n a)) _ (F a)) ∧
      (∀ a ω, 0 ≤ F a ω ∧ F a ω ≤ K) ∧
      (∀ a, (∫ ω, |min K (Z a ω) - F a ω| ∂Measure.infinitePi (fun _ : I => ν)) ≤ η))
    (hescape : ∀ n (S : Set I), S.Finite → ∀ᵐ d ∂δ,
      ∀ᶠ r in atTop, Disjoint S (N n (j r d))) :
    ∀ K > 0, EscapingLocalApproximation δ ν
      (fun r x => min K (Z (j r x.1) x.2)) K := by
  intro K hK η hη
  obtain ⟨n, F, hFm, hFb, hFerr⟩ := hloc K η hK hη
  refine ⟨fun r x => F (j r x.1) x.2, fun r d => N n (j r d), ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    exact measurable_countable_sample (fun a => (hFm a).mono (rows_le _) le_rfl) (hj r)
  · exact fun r x => hFb _ _
  · exact fun r d => hFm _
  · exact fun r d => hFerr (j r d)
  · exact fun S hS => hescape n S hS

lemma sampled_entropy_decorrelation {f : D × (I → A) → ℝ} {Z : J → (I → A) → ℝ}
    {c Q C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hf1 : (∫ x, f x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) = 1)
    (hH : Integrable (fun x => entropyPlus (f x)) (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hZ : ∀ a, Measurable (Z a)) (hZ0 : ∀ a ω, 0 ≤ Z a ω)
    (he : ∀ a, Integrable (fun ω => Real.exp ((2 * c) * Z a ω)) (Measure.infinitePi (fun _ : I => ν)))
    (heQ : ∀ a, (∫ ω, Real.exp ((2 * c) * Z a ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ Q)
    (hZi : ∀ a, Integrable (Z a) (Measure.infinitePi (fun _ : I => ν)))
    (hZC : ∀ a, (∫ ω, Z a ω ∂Measure.infinitePi (fun _ : I => ν)) ≤ C)
    (N : ℕ → J → Set I) (j : ℕ → D → J) (hj : ∀ r, Measurable (j r))
    (hloc : ∀ K η : ℝ, 0 < K → 0 < η → ∃ n : ℕ, ∃ F : J → (I → A) → ℝ,
      (∀ a, @Measurable _ _ (rows (N n a)) _ (F a)) ∧
      (∀ a ω, 0 ≤ F a ω ∧ F a ω ≤ K) ∧
      (∀ a, (∫ ω, |min K (Z a ω) - F a ω| ∂Measure.infinitePi (fun _ : I => ν)) ≤ η))
    (hescape : ∀ n (S : Set I), S.Finite → ∀ᵐ d ∂δ,
      ∀ᶠ r in atTop, Disjoint S (N n (j r d))) :
    ∀ ε > 0, ∀ᶠ r in atTop,
      (∫ x : D × (I → A), f x * Z (j r x.1) x.2
        ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤ C + ε := by
  exact entropy_decorrelation δ ν hc hC hf hf0 hfi hf1 hH
    (fun r => measurable_countable_sample hZ (hj r)) (fun r x => hZ0 _ _)
    (fun r => (sampled_exponential_integrable δ ν hZ he heQ (hj r)).1)
    (fun r => (sampled_exponential_integrable δ ν hZ he heQ (hj r)).2)
    (fun r d => hZi (j r d)) (fun r d => hZC (j r d))
    (sampled_locality δ ν N j hj hloc hescape)

end SampledSites

lemma limsup_le_of_nonneg_eventual {a : ℕ → ℝ} {C : ℝ}
    (h0 : ∀ r, 0 ≤ a r) (h : ∀ ε > 0, ∀ᶠ r in atTop, a r ≤ C + ε) :
    Filter.limsup a atTop ≤ C := by
  apply (Filter.limsup_le_iff' (isCoboundedUnder_le_of_le atTop h0)
    (isBoundedUnder_of_eventually_le (h 1 zero_lt_one))).mpr
  intro y hy
  simpa only [add_sub_cancel] using h (y - C) (sub_pos.mpr hy)

end TailDecorrelation

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma analytic_rows_eq {d : ℕ} (S : Set (Lattice d)) :
    TailDecorrelation.rows (A := Row d) S = rowSigma S :=
  TailDecorrelation.rows_eq_iSup_two S

lemma integrable_and_mean_le_of_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {Z : Ω → ℝ} {c B : ℝ} (hc : 0 < c)
    (hZ : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hi : Integrable (fun ω => Real.exp (c * Z ω)) μ)
    (hB : (∫ ω, Real.exp (c * Z ω) ∂μ) ≤ B) :
    Integrable Z μ ∧ (∫ ω, Z ω ∂μ) ≤ B / c := by
  have hb : ∀ ω, Z ω ≤ Real.exp (c * Z ω) / c := by
    intro ω
    apply (le_div_iff₀ hc).mpr
    have h := Real.add_one_le_exp (c * Z ω)
    nlinarith
  have hz : Integrable Z μ := (hi.div_const c).mono' hZ.aestronglyMeasurable
    (Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 ω)]
      exact hb ω))
  refine ⟨hz, ?_⟩
  calc
    (∫ ω, Z ω ∂μ) ≤ (∫ ω, Real.exp (c * Z ω) / c ∂μ) := integral_mono hz (hi.div_const c) hb
    _ = (∫ ω, Real.exp (c * Z ω) ∂μ) / c := integral_div _ _
    _ ≤ B / c := div_le_div_of_nonneg_right hB hc.le

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_Kernel
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TailDecorrelation

section Randomization
variable {D I A J E : Type*} [MeasurableSpace D] [MeasurableSpace A]
variable [MeasurableSpace E] [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
variable (δ : Measure D) (σ : Measure E) (ν : Measure A)
variable [IsProbabilityMeasure δ] [IsProbabilityMeasure σ] [IsProbabilityMeasure ν]

lemma randomization_projection_preserving :
    MeasurePreserving (fun x : (D × E) × (I → A) => (x.1.1, x.2))
      ((δ.prod σ).prod (Measure.infinitePi (fun _ : I => ν)))
      (δ.prod (Measure.infinitePi (fun _ : I => ν))) := by
  exact measurePreserving_fst.prod (MeasurePreserving.id _)

lemma randomized_density {f : D × (I → A) → ℝ}
    (hf : Measurable f) (hfi : Integrable f (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hH : Integrable (fun x => entropyPlus (f x)) (δ.prod (Measure.infinitePi (fun _ : I => ν)))) :
    Integrable (fun x : (D × E) × (I → A) => f (x.1.1, x.2))
      ((δ.prod σ).prod (Measure.infinitePi (fun _ : I => ν))) ∧
    Integrable (fun x : (D × E) × (I → A) => entropyPlus (f (x.1.1, x.2)))
      ((δ.prod σ).prod (Measure.infinitePi (fun _ : I => ν))) ∧
    (∫ x : (D × E) × (I → A), f (x.1.1, x.2)
      ∂(δ.prod σ).prod (Measure.infinitePi (fun _ : I => ν))) =
      (∫ x, f x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) := by
  have hp := randomization_projection_preserving δ σ ν (I := I)
  refine ⟨(hp.integrable_comp hf.aestronglyMeasurable).mpr hfi,
    (hp.integrable_comp (measurable_entropyPlus.comp hf).aestronglyMeasurable).mpr hH, ?_⟩
  have hh : AEStronglyMeasurable f
      (((δ.prod σ).prod (Measure.infinitePi (fun _ : I => ν))).map
        (fun x : (D × E) × (I → A) => (x.1.1, x.2))) := by
    rw [hp.map_eq]
    exact hf.aestronglyMeasurable
  have he := integral_map hp.measurable.aemeasurable hh
  rw [hp.map_eq] at he
  exact he.symm

end Randomization
end TailDecorrelation

namespace TailDecorrelation

lemma measurableSet_eventually_nat {X : Type*} [MeasurableSpace X]
    {p : ℕ → X → Prop} (hp : ∀ n, MeasurableSet {x | p n x}) :
    MeasurableSet {x | ∀ᶠ n in atTop, p n x} := by
  simp only [eventually_atTop, Set.ofPred_exists, Set.ofPred_forall]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun m =>
    MeasurableSet.iInter fun _ => hp m

section KernelTransfer
variable {D E W J : Type*} [MeasurableSpace D] [MeasurableSpace E]
variable [MeasurableSpace W] [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
variable (δ : Measure D) (σ : Measure E) (P : Measure W)
variable [IsProbabilityMeasure δ] [IsProbabilityMeasure σ] [IsProbabilityMeasure P]

lemma integral_comp_preserving {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ρ : Measure Y} {T : X → Y} (hT : MeasurePreserving T μ ρ)
    {g : Y → ℝ} (hg : Measurable g) :
    (∫ x, g (T x) ∂μ) = ∫ y, g y ∂ρ := by
  have hm : AEStronglyMeasurable g (μ.map T) := by
    rw [hT.map_eq]
    exact hg.aestronglyMeasurable
  have he := integral_map hT.measurable.aemeasurable hm
  rw [hT.map_eq] at he
  exact he.symm

lemma swap_seed_preserving :
    MeasurePreserving (fun x : (D × W) × E => ((x.1.1,x.2),x.1.2))
      ((δ.prod P).prod σ) ((δ.prod σ).prod P) := by
  exact ((measurePreserving_prodAssoc δ σ P).symm MeasurableEquiv.prodAssoc).comp
    (((MeasurePreserving.id δ).prod Measure.measurePreserving_swap).comp
      (measurePreserving_prodAssoc δ P σ))

lemma sampled_kernel_integral (κ : Kernel D J) (s : D → E → J)
    (hs : Measurable (Function.uncurry s)) (hmap : ∀ d, σ.map (s d) = κ d)
    {f : D × W → ℝ} (hf : Measurable f) {Z : J → W → ℝ}
    (hZ : ∀ a, Measurable (Z a))
    (hi : Integrable (fun x : (D × E) × W => f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2)
      ((δ.prod σ).prod P)) :
    (∫ x : (D × E) × W, f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2 ∂(δ.prod σ).prod P) =
      (∫ x : D × W, f x * (∫ a, Z a x.2 ∂κ x.1) ∂δ.prod P) := by
  have hz : Measurable (Function.uncurry Z) := measurable_from_prod_countable_right hZ
  let G : (D × E) × W → ℝ := fun x => f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2
  have hG : Measurable G :=
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hz.comp ((hs.comp measurable_fst).prodMk measurable_snd))
  have hp := swap_seed_preserving δ σ P
  have hj : Integrable (fun x : (D × W) × E => f x.1 * Z (s x.1.1 x.2) x.1.2)
      ((δ.prod P).prod σ) := (hp.integrable_comp hG.aestronglyMeasurable).mpr hi
  rw [← integral_comp_preserving hp hG]
  change (∫ x : (D × W) × E, f x.1 * Z (s x.1.1 x.2) x.1.2 ∂(δ.prod P).prod σ) = _
  rw [integral_prod _ hj]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change (∫ u, f x * Z (s x.1 u) x.2 ∂σ) = f x * (∫ a, Z a x.2 ∂κ x.1)
  rw [integral_const_mul]
  congr 1
  have he := integral_map ((hs.comp measurable_prodMk_left).aemeasurable)
    (show AEStronglyMeasurable (fun a => Z a x.2) (σ.map (s x.1)) from
      Measurable.of_discrete.aestronglyMeasurable)
  change (∫ a, Z a x.2 ∂σ.map (s x.1)) = (∫ u, Z (s x.1 u) x.2 ∂σ) at he
  rw [hmap] at he
  exact he.symm

lemma sampled_kernel_integrable (κ : Kernel D J) (s : D → E → J)
    (hs : Measurable (Function.uncurry s)) (hmap : ∀ d, σ.map (s d) = κ d)
    {f : D × W → ℝ} (hf : Measurable f) {Z : J → W → ℝ}
    (hZ : ∀ a, Measurable (Z a))
    (hi : Integrable (fun x : (D × E) × W => f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2)
      ((δ.prod σ).prod P)) :
    Integrable (fun x : D × W => f x * (∫ a, Z a x.2 ∂κ x.1)) (δ.prod P) := by
  have hz : Measurable (Function.uncurry Z) := measurable_from_prod_countable_right hZ
  let G : (D × E) × W → ℝ := fun x => f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2
  have hG : Measurable G :=
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hz.comp ((hs.comp measurable_fst).prodMk measurable_snd))
  have hp := swap_seed_preserving δ σ P
  have hj : Integrable (fun x : (D × W) × E => f x.1 * Z (s x.1.1 x.2) x.1.2)
      ((δ.prod P).prod σ) := (hp.integrable_comp hG.aestronglyMeasurable).mpr hi
  apply hj.integral_prod_left.congr
  apply Eventually.of_forall
  intro x
  change (∫ u, f x * Z (s x.1 u) x.2 ∂σ) = f x * (∫ a, Z a x.2 ∂κ x.1)
  rw [integral_const_mul]
  congr 1
  have he := integral_map ((hs.comp measurable_prodMk_left).aemeasurable)
    (show AEStronglyMeasurable (fun a => Z a x.2) (σ.map (s x.1)) from
      Measurable.of_discrete.aestronglyMeasurable)
  change (∫ a, Z a x.2 ∂σ.map (s x.1)) = (∫ u, Z (s x.1 u) x.2 ∂σ) at he
  rw [hmap] at he
  exact he.symm

omit [IsProbabilityMeasure δ] in
lemma kernel_escape_sampled (κ : ℕ → Kernel D J) (s : ℕ → D → E → J)
    (hs : ∀ r, Measurable (Function.uncurry (s r)))
    (hmap : ∀ r d, σ.map (s r d) = κ r d)
    (good : ℕ → J → Prop)
    (hesc : ∀ᵐ d ∂δ, ∀ᶠ r in atTop, ∀ᵐ a ∂κ r d, good r a) :
    ∀ᵐ x ∂δ.prod σ, ∀ᶠ r in atTop, good r (s r x.1 x.2) := by
  have hm : ∀ r, MeasurableSet {x : D × E | good r (s r x.1 x.2)} := fun r =>
    (hs r) (Set.to_countable _).measurableSet
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eventually_nat hm)).mpr
  filter_upwards [hesc] with d hd
  obtain ⟨N,hN⟩ := eventually_atTop.mp hd
  have hforall : ∀ r : ℕ, ∀ᵐ u ∂σ, N ≤ r → good r (s r d u) := by
    intro r
    by_cases hr : N ≤ r
    · have hh := hN r hr
      rw [← hmap r d] at hh
      have htrans := (ae_map_iff (hs r |>.comp measurable_prodMk_left |>.aemeasurable)
        (Set.to_countable _).measurableSet).mp hh
      exact htrans.mono fun u hu _ => hu
    · exact Eventually.of_forall fun _ h => (hr h).elim
  filter_upwards [ae_all_iff.mpr hforall] with u hu
  exact eventually_atTop.mpr ⟨N,hu⟩

end KernelTransfer
end TailDecorrelation

namespace TailDecorrelation
section KernelCompletion
variable {D I A J : Type*} [MeasurableSpace D] [MeasurableSpace A] [Encodable I]
variable [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
variable [Nonempty J] [StandardBorelSpace J]
variable (δ : Measure D) (ν : Measure A) [IsProbabilityMeasure δ] [IsProbabilityMeasure ν]

omit [Encodable I] in
lemma kernel_density_integrable {f : D × (I → A) → ℝ} {Z : J → (I → A) → ℝ}
    {c Q : ℝ} (hc : 0 < c)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hH : Integrable (fun x => entropyPlus (f x)) (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hZ : ∀ a, Measurable (Z a)) (hZ0 : ∀ a ω, 0 ≤ Z a ω)
    (he : ∀ a, Integrable (fun ω => Real.exp (c * Z a ω)) (Measure.infinitePi (fun _ : I => ν)))
    (heQ : ∀ a, (∫ ω, Real.exp (c * Z a ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ Q)
    (κ : Kernel D J) [IsMarkovKernel κ] :
    Integrable (fun x : D × (I → A) => f x * (∫ a, Z a x.2 ∂κ x.1))
      (δ.prod (Measure.infinitePi (fun _ : I => ν))) := by
  obtain ⟨s,hs,hmap⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  let σ : Measure unitInterval := volume
  let g : (D × unitInterval) × (I → A) → ℝ := fun x => f (x.1.1,x.2)
  have hg : Measurable g := hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨_,hgH,_⟩ := randomized_density δ σ ν hf hfi hH
  have hi := integrable_density_mul_of_entropy hc hg
    (measurable_countable_sample hZ hs) (fun x => hf0 _) (fun x => hZ0 _ _) hgH
    (sampled_exponential_integrable (δ.prod σ) ν hZ he heQ hs).1
  exact sampled_kernel_integrable δ σ (Measure.infinitePi (fun _ : I => ν))
    κ s hs hmap hf hZ hi

lemma kernel_entropy_decorrelation {f : D × (I → A) → ℝ} {Z : J → (I → A) → ℝ}
    {c Q C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hf1 : (∫ x, f x ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) = 1)
    (hH : Integrable (fun x => entropyPlus (f x)) (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hZ : ∀ a, Measurable (Z a)) (hZ0 : ∀ a ω, 0 ≤ Z a ω)
    (he : ∀ a, Integrable (fun ω => Real.exp ((2 * c) * Z a ω)) (Measure.infinitePi (fun _ : I => ν)))
    (heQ : ∀ a, (∫ ω, Real.exp ((2 * c) * Z a ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ Q)
    (hZi : ∀ a, Integrable (Z a) (Measure.infinitePi (fun _ : I => ν)))
    (hZC : ∀ a, (∫ ω, Z a ω ∂Measure.infinitePi (fun _ : I => ν)) ≤ C)
    (N : ℕ → J → Set I) (κ : ℕ → Kernel D J) [∀ r, IsMarkovKernel (κ r)]
    (hloc : ∀ K η : ℝ, 0 < K → 0 < η → ∃ n : ℕ, ∃ F : J → (I → A) → ℝ,
      (∀ a, @Measurable _ _ (rows (N n a)) _ (F a)) ∧
      (∀ a ω, 0 ≤ F a ω ∧ F a ω ≤ K) ∧
      (∀ a, (∫ ω, |min K (Z a ω) - F a ω| ∂Measure.infinitePi (fun _ : I => ν)) ≤ η))
    (hescape : ∀ n (S : Set I), S.Finite → ∀ᵐ d ∂δ,
      ∀ᶠ r in atTop, ∀ᵐ a ∂κ r d, Disjoint S (N n a)) :
    ∀ ε > 0, ∀ᶠ r in atTop,
      (∫ x : D × (I → A), f x * (∫ a, Z a x.2 ∂κ r x.1)
        ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) ≤ C + ε := by
  classical
  let σ : Measure unitInterval := volume
  choose s hs hmap using fun r => Kernel.exists_measurable_map_eq_unitInterval (κ r)
  let g : (D × unitInterval) × (I → A) → ℝ := fun x => f (x.1.1,x.2)
  have hg : Measurable g := hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨hgi,hgH,hg1⟩ := randomized_density δ σ ν hf hfi hH
  have hesc : ∀ n (S : Set I), S.Finite → ∀ᵐ d ∂δ.prod σ,
      ∀ᶠ r in atTop, Disjoint S (N n (s r d.1 d.2)) := by
    intro n S hS
    exact kernel_escape_sampled δ σ κ s hs hmap (fun _ a => Disjoint S (N n a)) (hescape n S hS)
  have hbound := sampled_entropy_decorrelation (δ.prod σ) ν hc hC hg
    (fun x => hf0 _) hgi (hg1.trans hf1) hgH hZ hZ0 he heQ hZi hZC N
    (fun r => Function.uncurry (s r)) hs hloc hesc
  have heq : ∀ r, (∫ x : (D × unitInterval) × (I → A),
      g x * Z (s r x.1.1 x.1.2) x.2 ∂(δ.prod σ).prod (Measure.infinitePi (fun _ : I => ν))) =
      (∫ x : D × (I → A), f x * (∫ a, Z a x.2 ∂κ r x.1)
        ∂δ.prod (Measure.infinitePi (fun _ : I => ν))) := by
    intro r
    have hi := integrable_density_mul_of_entropy (by linarith : 0 < 2*c) hg
      (measurable_countable_sample hZ (hs r)) (fun x => hf0 _) (fun x => hZ0 _ _) hgH
      (sampled_exponential_integrable (δ.prod σ) ν hZ he heQ (hs r)).1
    exact sampled_kernel_integral δ σ (Measure.infinitePi (fun _ : I => ν))
      (κ r) (s r) (hs r) (hmap r) hf hZ hi
  intro ε hε
  filter_upwards [hbound ε hε] with r hr
  rw [← heq r]
  exact hr

end KernelCompletion
end TailDecorrelation

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_KernelSections
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailDecorrelation

lemma sampled_kernel_sections {D E J W : Type*}
    [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace J] [MeasurableSpace W]
    [Countable J] [MeasurableSingletonClass J]
    (δ : Measure D) (σ : Measure E) (P : Measure W)
    [IsProbabilityMeasure δ] [IsProbabilityMeasure σ] [IsProbabilityMeasure P]
    (κ : Kernel D J) (s : D → E → J)
    (hs : Measurable (Function.uncurry s)) (hmap : ∀ d, σ.map (s d) = κ d)
    {f : D × W → ℝ} (hf : Measurable f) {Z : J → W → ℝ}
    (hZ : ∀ a, Measurable (Z a))
    (hi : Integrable (fun x : (D × E) × W => f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2)
      ((δ.prod σ).prod P)) :
    ∀ᵐ x ∂δ.prod P, f x ≠ 0 → Integrable (fun a => Z a x.2) (κ x.1) := by
  have hz : Measurable (Function.uncurry Z) := measurable_from_prod_countable_right hZ
  let G : (D × E) × W → ℝ := fun x => f (x.1.1,x.2) * Z (s x.1.1 x.1.2) x.2
  have hG : Measurable G :=
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hz.comp ((hs.comp measurable_fst).prodMk measurable_snd))
  have hp := swap_seed_preserving δ σ P
  have hj : Integrable (fun x : (D × W) × E => f x.1 * Z (s x.1.1 x.2) x.1.2)
      ((δ.prod P).prod σ) := (hp.integrable_comp hG.aestronglyMeasurable).mpr hi
  filter_upwards [hj.prod_right_ae] with x hx
  intro hfx
  have hzx : Integrable (fun u => Z (s x.1 u) x.2) σ := by
    have hh := hx.const_mul (f x)⁻¹
    simpa only [←mul_assoc, inv_mul_cancel₀ hfx, one_mul] using hh
  rw [←hmap]
  exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (hs.comp measurable_prodMk_left).aemeasurable).mpr hzx

lemma kernel_density_sections {D I A J : Type*} [MeasurableSpace D] [MeasurableSpace A] [Encodable I]
    [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
    [Nonempty J] [StandardBorelSpace J]
    (δ : Measure D) (ν : Measure A) [IsProbabilityMeasure δ] [IsProbabilityMeasure ν]
    {f : D × (I → A) → ℝ} {Z : J → (I → A) → ℝ}
    {c Q : ℝ} (hc : 0 < c)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hH : Integrable (fun x => entropyPlus (f x)) (δ.prod (Measure.infinitePi (fun _ : I => ν))))
    (hZ : ∀ a, Measurable (Z a)) (hZ0 : ∀ a ω, 0 ≤ Z a ω)
    (he : ∀ a, Integrable (fun ω => Real.exp (c * Z a ω)) (Measure.infinitePi (fun _ : I => ν)))
    (heQ : ∀ a, (∫ ω, Real.exp (c * Z a ω) ∂Measure.infinitePi (fun _ : I => ν)) ≤ Q)
    (κ : Kernel D J) [IsMarkovKernel κ] :
    ∀ᵐ x ∂δ.prod (Measure.infinitePi (fun _ : I => ν)),
      f x ≠ 0 → Integrable (fun a => Z a x.2) (κ x.1) := by
  obtain ⟨s,hs,hmap⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  let σ : Measure unitInterval := volume
  let g : (D × unitInterval) × (I → A) → ℝ := fun x => f (x.1.1,x.2)
  have hg : Measurable g := hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨_,hgH,_⟩ := randomized_density δ σ ν hf hfi hH
  have hi := integrable_density_mul_of_entropy hc hg
    (measurable_countable_sample hZ hs) (fun x => hf0 _) (fun x => hZ0 _ _) hgH
    (sampled_exponential_integrable (δ.prod σ) ν hZ he heQ hs).1
  exact sampled_kernel_sections δ σ (Measure.infinitePi (fun _ : I => ν))
    κ s hs hmap hf hZ hi

end TailDecorrelation

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma cut_neighborhoods_escape {d : ℕ} (e : Direction d) (a : ℝ)
    (k : Fin d) (L U : ℕ → ℤ)
    (hL : Tendsto L atTop atBot) (hU : Tendsto U atTop atTop)
    (N : ℕ) (S : Set (Lattice d)) (hS : S.Finite) :
    ∀ᶠ r in atTop, ∀ p : Lattice d × Lattice d,
      p.1 k ≤ L r → U r ≤ p.2 k → Disjoint S (upperPairNeighborhood e a p N) := by
  have hz : ∀ z ∈ S, ∀ᶠ r in atTop, ∀ p : Lattice d × Lattice d,
      p.1 k ≤ L r → U r ≤ p.2 k → z ∉ LatticeBall p.1 N ∪ LatticeBall p.2 N := by
    intro z _
    filter_upwards [(tendsto_atBot.mp hL) (z k - (N : ℤ) - 1),
      (tendsto_atTop.mp hU) (z k + (N : ℤ) + 1)] with r hrx hry
    intro p hp hq hz
    rcases hz with hz | hz
    · have hh := (abs_le.mp (hz k)).2
      omega
    · have hh := (abs_le.mp (hz k)).1
      omega
  filter_upwards [hS.eventually_all.mpr hz] with r hr
  intro p hp hq
  exact Set.disjoint_left.mpr fun z hz hz' => hr z hz p hp hq hz'.1

theorem actual_kernel_tail_decorrelation {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 0 < A ∧
      (∀ᵐ ω ∂environmentLaw ν, ∀ x : Lattice d × Lattice d,
        dot (realPosition x.1) (realPosition (step e)) =
          dot (realPosition x.2) (realPosition (step e)) →
        ∀ t : ℕ, 0 < outwardKernelMass e f (t+1) x ω ∧
          -Real.log (outwardKernelMass e f (t+1) x ω) ≤
            2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e f A x ω) ∧
      let J := {p : Lattice d × Lattice d // p ∈ PairAtHeight (realPosition (step e)) 0}
      let Z : J → Environment d → ℝ := fun p => outwardCanonicalExcess e f A p.1
      BddAbove (Set.range (fun p => ∫ ω, Z p ω ∂environmentLaw ν)) ∧
      ∀ (D : Type) [MeasurableSpace D] (δ : Measure D) [IsProbabilityMeasure δ]
        (g : D × Environment d → ℝ),
        Measurable g → (∀ x, 0 ≤ g x) → Integrable g (δ.prod (environmentLaw ν)) →
        (∫ x, g x ∂δ.prod (environmentLaw ν)) = 1 →
        Integrable (fun x => TailDecorrelation.entropyPlus (g x)) (δ.prod (environmentLaw ν)) →
        ∀ (κ : ℕ → Kernel D J) [∀ r, IsMarkovKernel (κ r)] (L U : ℕ → D → ℤ),
          (∀ᵐ z ∂δ, Tendsto (fun r => L r z) atTop atBot ∧ Tendsto (fun r => U r z) atTop atTop) →
          (∀ r, ∀ᵐ z ∂δ, ∀ᵐ p ∂κ r z, p.1.1 f.1 ≤ L r z ∧ U r z ≤ p.1.2 f.1) →
          (∀ r, ∀ᵐ z ∂δ.prod (environmentLaw ν), g z ≠ 0 →
            Integrable (fun p => Z p z.2) (κ r z.1)) ∧
          (∀ r, Integrable (fun z => g z * (∫ p, Z p z.2 ∂κ r z.1)) (δ.prod (environmentLaw ν))) ∧
          (∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop,
            (∫ z, g z * (∫ p, Z p z.2 ∂κ r z.1) ∂δ.prod (environmentLaw ν)) ≤
              (⨆ p, ∫ ω, Z p ω ∂environmentLaw ν) + ε) ∧
          Filter.limsup (fun r => ∫ z, g z * (∫ p, Z p z.2 ∂κ r z.1)
            ∂δ.prod (environmentLaw ν)) atTop ≤ ⨆ p, ∫ ω, Z p ω ∂environmentLaw ν := by
  classical
  obtain ⟨A,c,B,hA,hc,hB,hbound,hloc⟩ := actual_outward_order ν hue e f hef htrans
  let J := {p : Lattice d × Lattice d // p ∈ PairAtHeight (realPosition (step e)) 0}
  let Z : J → Environment d → ℝ := fun p => outwardCanonicalExcess e f A p.1
  have hZm : ∀ p : J, Measurable (Z p) := fun p =>
    ((hbound 0 p.1 p.2).2.1).mono (rowSigma_le _) le_rfl
  have hZ0 : ∀ p : J, ∀ ω, 0 ≤ Z p ω := fun p => (hbound 0 p.1 p.2).1
  have he : ∀ p : J, Integrable (fun ω => Real.exp (c * Z p ω)) (environmentLaw ν) :=
    fun p => (hbound 0 p.1 p.2).2.2.1
  have heB : ∀ p : J, (∫ ω, Real.exp (c * Z p ω) ∂environmentLaw ν) ≤ B :=
    fun p => (hbound 0 p.1 p.2).2.2.2.1
  have hZi : ∀ p : J, Integrable (Z p) (environmentLaw ν) := fun p =>
    (integrable_and_mean_le_of_exp (environmentLaw ν) hc (hZm p) (hZ0 p) (he p) (heB p)).1
  have hZB : ∀ p : J, (∫ ω, Z p ω ∂environmentLaw ν) ≤ B / c := fun p =>
    (integrable_and_mean_le_of_exp (environmentLaw ν) hc (hZm p) (hZ0 p) (he p) (heB p)).2
  have hba : BddAbove (Set.range (fun p : J => ∫ ω, Z p ω ∂environmentLaw ν)) :=
    ⟨B/c, by rintro _ ⟨p,rfl⟩; exact hZB p⟩
  let p0 : J := ⟨(0,0), by simp [PairAtHeight, dot, realPosition]⟩
  let : Nonempty J := ⟨p0⟩
  have hC : 0 ≤ ⨆ p : J, ∫ ω, Z p ω ∂environmentLaw ν :=
    (integral_nonneg fun ω => hZ0 p0 ω).trans (le_ciSup hba p0)
  refine ⟨A,hA,outward_order_countable_event ν e f A (fun a x hx => (hbound a x hx).2.2.2.2),hba,?_⟩
  intro D mD δ hδ g hgm hg0 hgi hg1 hgH κ hκ L U hcuts htail
  have hcap : ∀ K η : ℝ, 0 < K → 0 < η → ∃ N : ℕ,
      ∃ F : J → Environment d → ℝ,
      (∀ p, @Measurable _ _ (TailDecorrelation.rows (upperPairNeighborhood e 0 p.1 N)) _ (F p)) ∧
      (∀ p ω, 0 ≤ F p ω ∧ F p ω ≤ K) ∧
      (∀ p, (∫ ω, |min K (Z p ω) - F p ω| ∂environmentLaw ν) ≤ η) := by
    intro K η hK hη
    obtain ⟨N,hN⟩ := outward_cap_locality_L1 ν e f A hloc hK hη
    have hh : ∀ p : J, ∃ F : Environment d → ℝ,
        @Measurable _ _ (rowSigma (upperPairNeighborhood e 0 p.1 N)) _ F ∧
        (∀ ω, 0 ≤ F ω ∧ F ω ≤ K) ∧
        (∫ ω, |min (Z p ω) K - F ω| ∂environmentLaw ν) < η :=
      fun p => hN 0 p.1 p.2
    choose F hFm hFb hFe using hh
    refine ⟨N,F,?_,hFb,?_⟩
    · intro p
      rw [analytic_rows_eq]
      exact hFm p
    · intro p
      simpa only [min_comm] using (hFe p).le
  have hesc : ∀ N (S : Set (Lattice d)), S.Finite → ∀ᵐ z ∂δ,
      ∀ᶠ r in atTop, ∀ᵐ p ∂κ r z, Disjoint S (upperPairNeighborhood e 0 p.1 N) := by
    intro N S hS
    filter_upwards [hcuts, ae_all_iff.mpr htail] with z hz ht
    filter_upwards [cut_neighborhoods_escape e 0 f.1 (fun r => L r z) (fun r => U r z)
      hz.1 hz.2 N S hS] with r hr
    filter_upwards [ht r] with p hp
    exact hr p.1 hp.1 hp.2
  have he' : ∀ p : J, Integrable (fun ω => Real.exp ((2*(c/2)) * Z p ω)) (environmentLaw ν) := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using he
  have heB' : ∀ p : J, (∫ ω, Real.exp ((2*(c/2)) * Z p ω) ∂environmentLaw ν) ≤ B := by
    simpa only [show 2*(c/2) = c by ring] using heB
  refine ⟨fun r => TailDecorrelation.kernel_density_sections δ ν hc hgm hg0 hgi hgH
    hZm hZ0 he heB (κ r), ?_⟩
  refine ⟨fun r => TailDecorrelation.kernel_density_integrable δ ν hc hgm hg0 hgi hgH
    hZm hZ0 he heB (κ r), ?_⟩
  have hE := TailDecorrelation.kernel_entropy_decorrelation δ ν (by linarith : 0 < c/2) hC
      hgm hg0 hgi hg1 hgH hZm hZ0 he' heB' hZi (fun p => le_ciSup hba p)
      (fun N p => upperPairNeighborhood e 0 p.1 N) κ hcap hesc
  exact ⟨hE, TailDecorrelation.limsup_le_of_nonneg_eventual
    (fun r => integral_nonneg fun z => mul_nonneg (hg0 z) (integral_nonneg fun p => hZ0 _ _)) hE⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_DensityTransfer
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

theorem actual_profile_tail_decorrelation_oai {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 0 < A ∧
      (∀ᵐ ω ∂environmentLaw ν, ∀ x : Lattice d × Lattice d,
        dot (realPosition x.1) (realPosition (step e)) =
          dot (realPosition x.2) (realPosition (step e)) →
        ∀ t : ℕ, 0 < outwardKernelMass e (f,true) (t+1) x ω ∧
          -Real.log (outwardKernelMass e (f,true) (t+1) x ω) ≤
            2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e (f,true) A x ω) ∧
      ∃ M : ℝ, 0 ≤ M ∧
      ∀ (D : Type) [MeasurableSpace D] (δ : Measure D) [IsProbabilityMeasure δ]
        (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w],
        (∀ z x, 0 < (w z).real {x}) →
        ∀ (g : D × Environment d → ℝ),
          Measurable g → (∀ z, 0 ≤ g z) → Integrable g (δ.prod (environmentLaw ν)) →
          (∫ z, g z ∂δ.prod (environmentLaw ν)) = 1 →
          Integrable (fun z => TailDecorrelation.entropyPlus (g z)) (δ.prod (environmentLaw ν)) →
          ∃ (j : ℕ → D → ℤ) (hj : ∀ r, Measurable (j r)),
            (∀ z (r : ℕ) (k : ℤ),
              TailCuts.score (TailCuts.lower ((w z).map (fun x => x.1 f)))
                (TailCuts.upper ((w z).map (fun x => x.1 f))) (r:ℤ) k ≤
              TailCuts.score (TailCuts.lower ((w z).map (fun x => x.1 f)))
                (TailCuts.upper ((w z).map (fun x => x.1 f))) (r:ℤ) (j r z)) ∧
            let Z : ZeroHeightPair e → Environment d → ℝ :=
              fun p => outwardCanonicalExcess e (f,true) A p.1
            let κ := fun r : ℕ => profilePairKernel e f w (r:ℤ) (j r) (hj r)
            (∀ r, ∀ᵐ z ∂δ.prod (environmentLaw ν), g z ≠ 0 →
              Integrable (fun p => Z p z.2) (κ r z.1)) ∧
            (∀ r, Integrable (fun z => g z * (∫ p, Z p z.2 ∂κ r z.1))
              (δ.prod (environmentLaw ν))) ∧
            (∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop,
              (∫ z, g z * (∫ p, Z p z.2 ∂κ r z.1) ∂δ.prod (environmentLaw ν)) ≤ M + ε) ∧
            Filter.limsup (fun r => ∫ z, g z * (∫ p, Z p z.2 ∂κ r z.1)
              ∂δ.prod (environmentLaw ν)) atTop ≤ M := by
  classical
  obtain ⟨A,hA,hpoint,hba,hdec⟩ := actual_kernel_tail_decorrelation ν hue e (f,true) hef htrans
  let Z : ZeroHeightPair e → Environment d → ℝ :=
    fun p => outwardCanonicalExcess e (f,true) A p.1
  let M : ℝ := ⨆ p : ZeroHeightPair e, ∫ ω, Z p ω ∂environmentLaw ν
  let p0 : ZeroHeightPair e := ⟨(0,0), by simp [PairAtHeight, dot, realPosition]⟩
  have hM : 0 ≤ M :=
    (integral_nonneg fun ω => canonicalLogExcess_nonneg _ _ ω).trans (le_ciSup hba p0)
  refine ⟨A,hA,hpoint,M,hM,?_⟩
  intro D mD δ hδ w hw hfull g hgm hg0 hgi hg1 hgH
  obtain ⟨j,hj,hmax,hesc⟩ := TailSampling.measurable_profile_cuts w (fun x => x.1 f)
    (measurable_of_countable _) (horizontal_coordinate_surjective e f hef) hfull
  let κ := fun r : ℕ => profilePairKernel e f w (r:ℤ) (j r) (hj r)
  let : ∀ r, IsMarkovKernel (κ r) :=
    fun r => profilePairKernel_markov e f hef w hfull (r:ℤ) (j r) (hj r)
  refine ⟨j,hj,hmax,?_⟩
  apply hdec D δ g hgm hg0 hgi hg1 hgH κ j (fun r z => j r z+(r:ℤ))
  · exact Eventually.of_forall hesc
  · intro r
    exact Eventually.of_forall fun z =>
      profilePairKernel_supported e f hef w hfull (r:ℤ) (j r) (hj r) z

end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.actual_profile_tail_decorrelation_oai := @OAI.DirectionalTransience.actual_profile_tail_decorrelation_oai
