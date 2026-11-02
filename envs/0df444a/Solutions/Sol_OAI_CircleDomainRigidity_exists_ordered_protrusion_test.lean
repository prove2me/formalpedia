-- Prove2me | solution 1 for OAI.CircleDomainRigidity.exists_ordered_protrusion_test
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:05:49.549923+00:00
-- url     : https://prove2.me/submissions/b9c53574-94a0-4c3b-b5e7-82ecab6a46cd

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010
import Theorems.Thm_OAI_CircleDomainRigidity_RecursiveCodeLaw_exists_selectable_protrusion_mean
import Theorems.Thm_OAI_CircleDomainRigidity_prescribed_countable_law_of_no_small_level_barrier

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryBumping
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Boundary bumping for compact continua

This is the compact-space argument used in the small-disk and generic-level
lemmas of the uniformization manuscript. It does not assume local
connectedness of the continuum.
-/

open Set Topology

namespace CircleDomainRigidity

/-- Every component of a proper closed subset of a compact connected space
meets its boundary. -/
theorem component_meets_frontier
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [PreconnectedSpace X] {F : Set X} (hF : IsClosed F) (hproper : F ≠ univ)
    {x : X} (hx : x ∈ F) :
    (connectedComponentIn F x ∩ frontier F).Nonempty := by
  classical
  by_contra hnonempty
  have hdisj : Disjoint (frontier F) (connectedComponentIn F x) :=
    (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hnonempty)).symm
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let xf : F := ⟨x, hx⟩
  let K : Set F := (Subtype.val : F → X) ⁻¹' frontier F
  have hK : IsClosed K := isClosed_frontier.preimage continuous_subtype_val
  have hd : Disjoint K (connectedComponent xf) := by
    apply Set.disjoint_left.mpr
    intro z hzK hzC
    apply Set.disjoint_left.mp hdisj hzK
    rw [connectedComponentIn_eq_image hx]
    exact ⟨z, hzC, rfl⟩
  rw [connectedComponent_eq_iInter_isClopen xf] at hd
  obtain ⟨s, hs⟩ := hK.isCompact.elim_finite_subfamily_closed
    (fun U : {U : Set F // IsClopen U ∧ xf ∈ U} => U.val)
    (fun U => U.property.1.isClosed) (Set.disjoint_iff_inter_eq_empty.mp hd)
  let U : Set F := ⋂ V ∈ s, (V : Set F)
  have hU : IsClopen U := isClopen_biInter_finset fun V _ => V.property.1
  have hxU : xf ∈ U := mem_iInter₂.mpr fun V _ => V.property.2
  let W : Set X := (Subtype.val : F → X) '' U
  have hWclosed : IsClosed W := hF.isClosedMap_subtype_val U hU.isClosed
  have hWF : W ⊆ F := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hWint : W ⊆ interior F := by
    rintro _ ⟨z, hz, rfl⟩
    by_contra hzi
    have hzK : z ∈ K := ⟨subset_closure z.property, hzi⟩
    exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hs) hzK hz
  obtain ⟨O, hO, hWO⟩ :=
    Topology.IsInducing.subtypeVal.image_eq_isOpen_inter_range hU.isOpen
  change W = O ∩ range (Subtype.val : F → X) at hWO
  have hWeq : W = O ∩ interior F := by
    apply Subset.antisymm
    · intro z hz
      exact ⟨(hWO ▸ hz).1, hWint hz⟩
    · intro z hz
      rw [hWO]
      exact ⟨hz.1, ⟨⟨z, interior_subset hz.2⟩, rfl⟩⟩
  have hWopen : IsOpen W := hWeq ▸ hO.inter isOpen_interior
  have hWuniv : W = univ := (show IsClopen W from ⟨hWclosed, hWopen⟩).eq_univ
    ⟨x, xf, hxU, rfl⟩
  apply hproper
  apply Set.eq_univ_of_univ_subset
  rw [← hWuniv]
  exact hWF

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathLawMixtures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel mixtures of actual path laws. Hit probabilities obey the mixture identity;
their finite nonnegative weighted bounds pass to arbitrary probability mixtures.
The dual finite bounds imply square summability and countable positive support. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]

theorem probabilityMixture_apply (P : ProbabilityMeasure Z)
    (law : Z → ProbabilityMeasure Ω) (hlaw : Measurable law)
    {E : Set Ω} (hE : MeasurableSet E) :
    (probabilityMixture P law hlaw : Measure Ω) E =
      ∫⁻ z, (law z : Measure Ω) E ∂(P : Measure Z) :=
  Measure.bind_apply hE (measurable_subtype_coe.comp hlaw).aemeasurable

section Paths

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
theorem pathHitReal_nonneg (μ : ProbabilityMeasure C(PathTime, X)) (x : X) :
    0 ≤ pathHitReal μ x := ENNReal.toReal_nonneg

theorem measurable_pathHitProbability (x : X) :
    Measurable (fun μ : ProbabilityMeasure C(PathTime, X) => pathHitProbability μ x) :=
  (Measure.measurable_coe (isClosed_paths_hitting x).measurableSet).comp
    measurable_subtype_coe

theorem integrable_pathHitReal (P : ProbabilityMeasure Z)
    {law : Z → ProbabilityMeasure C(PathTime, X)} (hlaw : Measurable law) (x : X) :
    Integrable (fun z => pathHitReal (law z) x) (P : Measure Z) := by
  apply Integrable.of_bound
    (((measurable_pathHitProbability x).comp hlaw).ennreal_toReal.aestronglyMeasurable) 1
  exact Eventually.of_forall fun z => by
    change ‖pathHitReal (law z) x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (pathHitReal_nonneg _ _)]
    exact pathHitReal_le_one _ _

theorem pathHitProbability_mixture (P : ProbabilityMeasure Z)
    (law : Z → ProbabilityMeasure C(PathTime, X)) (hlaw : Measurable law) (x : X) :
    pathHitProbability (probabilityMixture P law hlaw) x =
      ∫⁻ z, pathHitProbability (law z) x ∂(P : Measure Z) :=
  probabilityMixture_apply P law hlaw (isClosed_paths_hitting x).measurableSet

theorem pathHitReal_mixture (P : ProbabilityMeasure Z)
    (law : Z → ProbabilityMeasure C(PathTime, X)) (hlaw : Measurable law) (x : X) :
    pathHitReal (probabilityMixture P law hlaw) x =
      ∫ z, pathHitReal (law z) x ∂(P : Measure Z) := by
  rw [pathHitReal, pathHitProbability_mixture]
  exact (integral_toReal ((measurable_pathHitProbability x).comp hlaw).aemeasurable
    (Eventually.of_forall fun z => lt_of_le_of_lt
      (pathHitProbability_le_one (law z) x) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).symm

end Paths

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ConfigurationNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Testing all sizes and reciprocal separation scales is sufficient to control
the full square norm of the point-hit probabilities. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_reciprocal_separation {X I : Type*} [MetricSpace X] [Finite I]
    (x : I → X) (hx : Injective x) :
    ∃ m : ℕ, ∀ i j, i ≠ j → 1 / ((m : ℝ) + 1) ≤ dist (x i) (x j) := by
  obtain ⟨c, hc, hsep⟩ := (Set.finite_range x).relatively_discrete
  obtain ⟨a, ha, hac⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hc
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt ha0
  refine ⟨m, fun i j hij => hm.le.trans ?_⟩
  have hd := hac.le.trans (hsep (x i) (mem_range_self i) (x j) (mem_range_self j)
    (fun h => hij (hx h)))
  rw [edist_dist] at hd
  have hdreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  simpa only [ENNReal.coe_toReal, ENNReal.toReal_ofReal dist_nonneg] using hdreal

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VisitCounts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite visit witnesses have Borel incidence. The resulting extended count
records visits at distinct parameter times, including both endpoints. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem isClosed_separatedTimeSet (n : ℕ) (r : ℝ) : IsClosed (separatedTimeSet n r) := by
  simp only [separatedTimeSet, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_iInter fun _ => isClosed_le continuous_const (by fun_prop)

instance instCompactSpaceElemForallFinRealPathTimeSeparatedTimes (n : ℕ) (r : ℝ) : CompactSpace (SeparatedTimes n r) :=
  isCompact_iff_compactSpace.mp (isClosed_separatedTimeSet n r).isCompact

theorem isClosed_separatedVisitSet {X : Type*} [MetricSpace X] (n : ℕ) (r : ℝ) :
    IsClosed (separatedVisitSet (X := X) n r) := by
  let H : Set ((C(PathTime, X) × X) × SeparatedTimes n r) :=
    {q | ∀ i, q.1.1 (q.2.val i) = q.1.2}
  have hH : IsClosed H := by
    simp only [H, ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_eq
    · exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
    · exact continuous_snd.comp continuous_fst
  have heq : Prod.fst '' H = separatedVisitSet (X := X) n r := by
    ext q
    constructor
    · rintro ⟨⟨p, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(q, t), ht, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace H hH

theorem visitAtLeastSet_eq_iUnion {X : Type*} [MetricSpace X] (n : ℕ) :
    visitAtLeastSet (X := X) n =
      ⋃ m : ℕ, separatedVisitSet n (1 / ((m : ℝ) + 1)) := by
  ext q
  constructor
  · rintro ⟨t, ht, heq⟩
    obtain ⟨m, hm⟩ := exists_reciprocal_separation t ht
    exact mem_iUnion.mpr ⟨m, ⟨⟨t, hm⟩, heq⟩⟩
  · intro h
    obtain ⟨m, t, ht⟩ := mem_iUnion.mp h
    refine ⟨t.val, ?_, ht⟩
    intro i j hij
    by_contra hne
    have hd := t.property i j hne
    rw [hij, dist_self] at hd
    have hp : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_visitAtLeastSet (n : ℕ) :
    MeasurableSet (visitAtLeastSet (X := X) n) := by
  rw [visitAtLeastSet_eq_iUnion]
  exact MeasurableSet.iUnion fun m => (isClosed_separatedVisitSet n (1 / ((m : ℝ) + 1))).measurableSet

theorem measurable_visitCount : Measurable (fun q : C(PathTime, X) × X => visitCount q.1 q.2) := by
  classical
  unfold visitCount
  apply Measurable.iSup
  intro n
  exact measurable_const.piecewise (measurableSet_visitAtLeastSet (X := X) n) measurable_const

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem visitCount_ge_nat {γ : C(PathTime, X)} {x : X} {n : ℕ}
    (h : (γ, x) ∈ visitAtLeastSet n) : (n : ℝ≥0∞) ≤ visitCount γ x := by
  classical
  calc
    (n : ℝ≥0∞) = (if (γ, x) ∈ visitAtLeastSet n then (n : ℝ≥0∞) else 0) :=
      (ite_eq_left h).symm
    _ ≤ visitCount γ x := le_iSup (fun k : ℕ =>
      if (γ, x) ∈ visitAtLeastSet k then (k : ℝ≥0∞) else 0) n


omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem one_le_visitCount_of_hit {γ : C(PathTime, X)} {x : X}
    (h : ∃ t, γ t = x) : 1 ≤ visitCount γ x := by
  obtain ⟨t, ht⟩ := h
  have h1 := visitCount_ge_nat (γ := γ) (x := x) (n := 1)
    ⟨fun _ => t, fun _ _ _ => Subsingleton.elim _ _, fun _ => ht⟩
  simpa only [Nat.cast_one] using h1

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem pathHitProbability_le_meanVisitCount (μ : ProbabilityMeasure C(PathTime, X)) (x : X) :
    pathHitProbability μ x ≤ meanVisitCount μ x := by
  let H : Set C(PathTime, X) := {γ | ∃ t, γ t = x}
  calc
    pathHitProbability μ x = ∫⁻ γ, H.indicator (fun _ => (1 : ℝ≥0∞)) γ
        ∂(μ : Measure C(PathTime, X)) := by
      rw [lintegral_indicator (isClosed_paths_hitting x).measurableSet]
      simp only [lintegral_one, Measure.restrict_apply_univ]
      rfl
    _ ≤ meanVisitCount μ x := by
      apply lintegral_mono
      intro γ
      by_cases h : γ ∈ H
      · simpa only [Set.indicator_of_mem h] using one_le_visitCount_of_hit h
      · simp only [Set.indicator_of_notMem h]
        exact bot_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedTimeCounts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable multiplicity in a closed time relation. This allows visits to
be restricted to a tagged path's residual times and to a closed test interval. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section

namespace CircleDomainRigidity

variable {Z : Type*}

theorem timeCount_eq_iSup (R : Set (Z × PathTime)) (z : Z) :
    timeCount R z = ⨆ n : ℕ, if z ∈ timeWitnessSet R n then (n : ℝ≥0∞) else 0 := by
  apply le_antisymm
  · rw [timeCount, ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    let E := F.filter (fun t => (z, t) ∈ R)
    let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
    have ht : z ∈ timeWitnessSet R (Fintype.card E) := by
      refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
      intro i
      exact (Finset.mem_filter.mp (e i).property).2
    have hb : (Fintype.card E : ℝ≥0∞) ≤
        ⨆ n : ℕ, if z ∈ timeWitnessSet R n then (n : ℝ≥0∞) else 0 := by
      exact (ite_eq_left ht).symm.le.trans (le_iSup
        (fun n : ℕ => if z ∈ timeWitnessSet R n then (n : ℝ≥0∞) else 0) _)
    simpa only [Finset.sum_boole, Fintype.card_coe] using hb
  · apply iSup_le
    intro n
    split
    · rename_i hn
      obtain ⟨t, ht, hR⟩ := hn
      calc
        (n : ℝ≥0∞) = ∑' i : Fin n, if (z, t i) ∈ R then (1 : ℝ≥0∞) else 0 := by
          simp only [hR, ite_true, if_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
        _ ≤ timeCount R z := ENNReal.tsum_comp_le_tsum_of_injective ht
          (fun t : PathTime => if (z, t) ∈ R then 1 else 0)
    · exact bot_le

theorem timeWitnessSet_eq_iUnion (R : Set (Z × PathTime)) (n : ℕ) :
    timeWitnessSet R n = ⋃ m : ℕ, separatedTimeWitnessSet R n (1 / ((m : ℝ) + 1)) := by
  ext z
  constructor
  · rintro ⟨t, ht, hR⟩
    obtain ⟨m, hm⟩ := exists_reciprocal_separation t ht
    exact mem_iUnion.mpr ⟨m, ⟨⟨t, hm⟩, hR⟩⟩
  · intro h
    obtain ⟨m, t, hR⟩ := mem_iUnion.mp h
    refine ⟨t.val, ?_, hR⟩
    intro i j hij
    by_contra hne
    have hd := t.property i j hne
    rw [hij, dist_self] at hd
    have hp : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith

variable [TopologicalSpace Z]

theorem isClosed_separatedTimeWitnessSet {R : Set (Z × PathTime)} (hR : IsClosed R)
    (n : ℕ) (r : ℝ) : IsClosed (separatedTimeWitnessSet R n r) := by
  let H : Set (Z × SeparatedTimes n r) := {q | ∀ i, (q.1, q.2.val i) ∈ R}
  have hH : IsClosed H := by
    change IsClosed {q : Z × SeparatedTimes n r | ∀ i, (q.1, q.2.val i) ∈ R}
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => hR.preimage (continuous_fst.prodMk
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
  have hproj : Prod.fst '' H = separatedTimeWitnessSet R n r := by
    ext z
    constructor
    · rintro ⟨⟨z, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(z, t), ht, rfl⟩
  rw [← hproj]
  exact isClosedMap_fst_of_compactSpace H hH

variable [MeasurableSpace Z] [BorelSpace Z]

theorem measurable_timeCount {R : Set (Z × PathTime)} (hR : IsClosed R) :
    Measurable (timeCount R) := by
  change Measurable (fun z => timeCount R z)
  simp_rw [timeCount_eq_iSup]
  apply Measurable.iSup
  intro n
  apply measurable_const.piecewise _ measurable_const
  rw [timeWitnessSet_eq_iUnion]
  exact MeasurableSet.iUnion fun m =>
    (isClosed_separatedTimeWitnessSet hR n (1 / ((m : ℝ) + 1))).measurableSet

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathTags
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ambient tagged-path code space and its compact residual-time sections.
An active slot contains a nonempty finite label tuple, its circle levels,
and the two ends of its open time interval. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuous_tagLeft : Continuous tagLeft :=
  continuous_const.sumElim (continuous_sigma fun _ => continuous_snd.snd.fst)

theorem continuous_tagRight : Continuous tagRight :=
  continuous_const.sumElim (continuous_sigma fun _ => continuous_snd.snd.snd)

theorem isClosed_residualTimeGraph {X : Type*} [TopologicalSpace X]
    {B : Set X} (hB : IsClosed B) : IsClosed (residualTimeGraph B) := by
  apply IsClosed.inter
  · exact hB.preimage (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd))
  · change IsClosed {q : TaggedPath X × PathTime | ∀ k,
      q.2 ≤ tagLeft (q.1.2 k) ∨ tagRight (q.1.2 k) ≤ q.2}
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro k
    exact (isClosed_le (continuous_subtype_val.comp continuous_snd)
      (continuous_subtype_val.comp (continuous_tagLeft.comp
        ((continuous_apply k).comp continuous_fst.snd)))).union
      (isClosed_le (continuous_subtype_val.comp (continuous_tagRight.comp
        ((continuous_apply k).comp continuous_fst.snd)))
        (continuous_subtype_val.comp continuous_snd))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MomentLawBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The countable nonnegative integral tests used for candidate path laws form
a Borel family and are preserved by arbitrary Borel probability mixtures. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]

theorem lintegral_probabilityMixture (P : ProbabilityMeasure Z)
    (law : Z → ProbabilityMeasure Ω) (hlaw : Measurable law)
    {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(probabilityMixture P law hlaw : Measure Ω) =
      ∫⁻ z, ∫⁻ x, f x ∂(law z : Measure Ω) ∂(P : Measure Z) := by
  exact Measure.lintegral_bind (measurable_subtype_coe.comp hlaw).aemeasurable hf.aemeasurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ResidualVisits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual residual visit multiplicities and tolls on closed test intervals. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem isClosed_residualVisitRelation {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) : IsClosed (residualVisitRelation B I) :=
  ((isClosed_residualTimeGraph hB).preimage
    (continuous_fst.fst.prodMk continuous_snd)).inter
      ((hI.preimage continuous_snd).inter (isClosed_eq
        (continuous_eval.comp (continuous_fst.fst.fst.prodMk continuous_snd)) continuous_fst.snd))

theorem residualToll_eq_visits (B : Set X) (I : Set PathTime)
    (m : X → ℝ≥0∞) (Γ : TaggedPath X) :
    residualToll B I m Γ = ∑' x, m x * residualVisitCount B I Γ x := by
  rw [residualToll, ← ENNReal.tsum_fiberwise
    (fun t => if t ∈ residualTimes B Γ ∧ t ∈ I then m (Γ.1 t) else 0) Γ.1]
  apply tsum_congr
  intro x
  rw [residualVisitCount, timeCount, ← ENNReal.tsum_mul_left,
    tsum_subtype (Γ.1 ⁻¹' {x})
      (fun t : PathTime => if t ∈ residualTimes B Γ ∧ t ∈ I then m (Γ.1 t) else 0)]
  apply tsum_congr
  intro t
  by_cases he : Γ.1 t = x <;>
    by_cases ht : t ∈ residualTimes B Γ ∧ t ∈ I <;>
      simp [Set.indicator, residualVisitRelation, he, ht]

theorem residualToll_eq_support (B : Set X) (I : Set PathTime)
    (m : X → ℝ≥0∞) (Γ : TaggedPath X) :
    residualToll B I m Γ = ∑' x : Function.support m, m x * residualVisitCount B I Γ x := by
  rw [residualToll_eq_visits]
  symm
  apply tsum_subtype_eq_of_support_subset
    (f := fun x : X => m x * residualVisitCount B I Γ x)
  intro x hx
  contrapose! hx
  simp only [Function.mem_support] at hx ⊢
  simp [hx]

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_residualVisitCount {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) :
    Measurable (fun q : TaggedPath X × X => residualVisitCount B I q.1 q.2) :=
  measurable_timeCount (isClosed_residualVisitRelation hB hI)

theorem measurable_residualToll {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) {m : X → ℝ≥0∞}
    (hm : (Function.support m).Countable) : Measurable (residualToll B I m) := by
  let : Countable (Function.support m) := hm.to_subtype
  change Measurable (fun Γ => residualToll B I m Γ)
  simp_rw [residualToll_eq_support]
  exact Measurable.tsum fun x => measurable_const.mul
    ((measurable_residualVisitCount hB hI).comp (measurable_id.prodMk measurable_const))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ResidualIncidence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel residual incidences after finite point deletions. Compact time
projection proves these directly, including the prior-path and level tests. -/

open Set Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]

theorem isClosed_separatedResidualIncidence {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) {R : Set (Y × X)} (hR : IsClosed R)
    (P : Set X) (r : ℝ) : IsClosed (separatedResidualIncidence B I R P r) := by
  let H : Set ((TaggedPath X × Y) × PathTime) :=
    {q | q.2 ∈ residualTimes B q.1.1 ∧ q.2 ∈ I ∧ (q.1.2, q.1.1.1 q.2) ∈ R ∧
      ∀ p ∈ P, r ≤ dist (q.1.1.1 q.2) p}
  have he : Continuous (fun q : (TaggedPath X × Y) × PathTime => q.1.1.1 q.2) :=
    continuous_eval.comp (continuous_fst.fst.fst.prodMk continuous_snd)
  have hH : IsClosed H := by
    refine ((isClosed_residualTimeGraph hB).preimage
      (continuous_fst.fst.prodMk continuous_snd)).inter ?_
    refine (hI.preimage continuous_snd).inter ?_
    refine (hR.preimage (continuous_fst.snd.prodMk he)).inter ?_
    change IsClosed {q : (TaggedPath X × Y) × PathTime |
      ∀ p ∈ P, r ≤ dist (q.1.1.1 q.2) p}
    simp only [ofPred_forall]
    exact isClosed_iInter fun p => isClosed_iInter fun _ =>
      isClosed_le continuous_const (he.dist continuous_const)
  have hproj : Prod.fst '' H = separatedResidualIncidence B I R P r := by
    ext q
    constructor
    · rintro ⟨⟨q, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(q, t), ht, rfl⟩
  rw [← hproj]
  exact isClosedMap_fst_of_compactSpace H hH

omit [TopologicalSpace Y] in
theorem residualIncidence_eq_iUnion (B : Set X) (I : Set PathTime)
    (R : Set (Y × X)) {P : Set X} (hP : IsClosed P) :
    residualIncidence B I R P =
      ⋃ n : ℕ, separatedResidualIncidence B I R P (1 / ((n : ℝ) + 1)) := by
  ext q
  constructor
  · rintro ⟨t, ht, hI, hR, hnot⟩
    obtain ⟨ε, hε, hball⟩ := isOpen_iff.mp hP.isOpen_compl (q.1.1 t) hnot
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine mem_iUnion.mpr ⟨n, t, ht, hI, hR, fun p hp => hn.le.trans ?_⟩
    by_contra h
    have hd : dist p (q.1.1 t) < ε := by simpa only [dist_comm] using not_le.mp h
    exact hball hd hp
  · intro h
    obtain ⟨n, t, ht, hI, hR, hsep⟩ := mem_iUnion.mp h
    refine ⟨t, ht, hI, hR, ?_⟩
    intro hp
    have h := hsep _ hp
    rw [dist_self] at h
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

variable [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_residualIncidence {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) {R : Set (Y × X)} (hR : IsClosed R)
    {P : Set X} (hP : P.Finite) : MeasurableSet (residualIncidence B I R P) := by
  rw [residualIncidence_eq_iUnion B I R hP.isClosed]
  exact MeasurableSet.iUnion fun n =>
    (isClosed_separatedResidualIncidence hB hI hR P (1 / ((n : ℝ) + 1))).measurableSet

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ResidualImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact residual images and their Borel incidence masses. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem isClosed_residualImageGraph {B : Set X} (hB : IsClosed B) :
    IsClosed (residualImageGraph B) := by
  let H : Set ((TaggedPath X × X) × PathTime) :=
    {q | (q.1.1, q.2) ∈ residualTimeGraph B ∧ q.1.1.1 q.2 = q.1.2}
  have hH : IsClosed H :=
    ((isClosed_residualTimeGraph hB).preimage
      (continuous_fst.fst.prodMk continuous_snd)).inter
        (isClosed_eq (continuous_eval.comp
          (continuous_fst.fst.fst.prodMk continuous_snd)) continuous_fst.snd)
  have heq : Prod.fst '' H = residualImageGraph B := by
    ext q
    constructor
    · rintro ⟨⟨p, t⟩, ⟨ht, heq⟩, rfl⟩
      exact ⟨t, ht, heq⟩
    · rintro ⟨t, ht, heq⟩
      exact ⟨(q, t), ⟨ht, heq⟩, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace H hH

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_residualImageMass {B : Set X} (hB : IsClosed B)
    (ν : Measure X) [SFinite ν] :
    Measurable (fun Γ : TaggedPath X => ν (residualImage B Γ)) :=
  measurable_measure_prodMk_left (isClosed_residualImageGraph hB).measurableSet

theorem measurableSet_residualImageMass_zero {B : Set X} (hB : IsClosed B)
    (ν : Measure X) [SFinite ν] :
    MeasurableSet {Γ : TaggedPath X | ν (residualImage B Γ) = 0} :=
  (measurable_residualImageMass hB ν) (measurableSet_singleton 0)

variable {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem measurable_residualIncidenceMass {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) {R : Set (Y × X)} (hR : IsClosed R)
    {P : Set X} (hP : P.Finite) (ν : Measure Y) [SFinite ν] :
    Measurable (fun Γ : TaggedPath X =>
      ν {y | (Γ, y) ∈ residualIncidence B I R P}) :=
  measurable_measure_prodMk_left (measurableSet_residualIncidence hB hI hR hP)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ResidualConstraints
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCountableElemFirstUncountableIio _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational-interval residual constraints in the allowed path definition
are Borel. The incidence side uses the actual prior law or level measure;
the toll side retains parameter multiplicity after each finite deletion. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

theorem countable_support_deletedWeight {X : Type*} (P : Set X) {m : X → ℝ≥0∞}
    (hm : (Function.support m).Countable) :
    (Function.support (deletedWeight P m)).Countable := by
  apply hm.mono
  intro x hx
  simp only [Function.mem_support, deletedWeight] at hx ⊢
  by_contra h
  simp only [h, ite_self] at hx
  exact hx rfl

variable {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_residualIncidenceBound {B : Set X} (hB : IsClosed B)
    {I : Set PathTime} (hI : IsClosed I) {R : Set (Y × X)} (hR : IsClosed R)
    {P : Set X} (hP : P.Finite) (ν : Measure Y) [SFinite ν]
    {m : X → ℝ≥0∞} (hm : (Function.support m).Countable) :
    MeasurableSet {Γ | ResidualIncidenceBound B I R P ν m Γ} :=
  measurableSet_le (measurable_residualIncidenceMass hB hI hR hP ν)
    (measurable_residualToll hB hI (countable_support_deletedWeight P hm))

theorem measurableSet_residualConstraintFamily {B : Set X} (hB : IsClosed B)
    {R : ℕ → Set (Y × X)} (hR : ∀ i, IsClosed (R i))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Y) [∀ i, SFinite (ν i)]
    {m : ℕ → X → ℝ≥0∞} (hm : ∀ i, (Function.support (m i)).Countable) :
    MeasurableSet {Γ | ResidualConstraintFamily B R P ν m Γ} := by
  simp only [ResidualConstraintFamily, ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_residualIncidenceBound hB isClosed_Icc (hR i) (P i n).finite_toSet
        (ν i) (hm i)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TagContainment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed level-containment tests for the actual finite unions in tag slots. -/

open Set
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

theorem isClosed_labeledLevelGraph {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i)) : IsClosed (labeledLevelGraph H) := by
  have heq : (labeledLevelGraph H)ᶜ = ⋃ i : ℕ, {i} ×ˢ (H i)ᶜ := by
    ext q
    simp [labeledLevelGraph]
  rw [← isOpen_compl_iff, heq]
  exact isOpen_iUnion fun i => (isOpen_discrete _).prod (hH i).isOpen_compl

theorem isClosed_activeTagLevelGraph {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i)) : IsClosed (activeTagLevelGraph H) := by
  let A : Set (Σ n : ℕ, TagParameters n × X) :=
    {q | ∃ i : Fin (q.1 + 1), (q.2.1.2.1 i, q.2.2) ∈ H (q.2.1.1 i)}
  have hA : IsClosed A := by
    apply isClosed_sigma_iff.mpr
    intro n
    change IsClosed {q : TagParameters n × X |
      ∃ i : Fin (n + 1), (q.1.2.1 i, q.2) ∈ H (q.1.1 i)}
    simp only [ofPred_exists]
    apply isClosed_iUnion_of_finite
    intro i
    exact (isClosed_labeledLevelGraph hH).preimage
      (show Continuous (fun q : TagParameters n × X =>
        (q.1.1 i, (q.1.2.1 i, q.2))) from by fun_prop)
  exact hA.preimage (Homeomorph.sigmaProdDistrib (Y := X)).continuous

theorem isClosed_tagLevelGraph {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i)) : IsClosed (tagLevelGraph H) := by
  let A : Set ((Unit × X) ⊕ (TagData × X)) :=
    {q | match q with
      | Sum.inl _ => True
      | Sum.inr t => t ∈ activeTagLevelGraph H}
  have hA : IsClosed A :=
    isClosed_sum_iff.mpr ⟨isClosed_univ, isClosed_activeTagLevelGraph hH⟩
  have heq : tagLevelGraph H =
      (Homeomorph.sumProdDistrib (X := Unit) (Y := TagData) (Z := X)) ⁻¹' A := by
    ext ⟨s, x⟩
    cases s <;> rfl
  rw [heq]
  exact hA.preimage (Homeomorph.sumProdDistrib (X := Unit) (Y := TagData) (Z := X)).continuous

theorem isClosed_tagContainment {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i)) : IsClosed (tagContainment H) := by
  have heq : tagContainment H = ⋂ t : PathTime,
      {q | (t : ℝ) ≤ tagLeft q.2 ∨ (tagRight q.2 : ℝ) ≤ t ∨
        (q.2, q.1 t) ∈ tagLevelGraph H} := by
    ext q
    simp only [tagContainment, mem_ofPred_eq, mem_iInter]
    change (∀ t : PathTime, (tagLeft q.2 : ℝ) < t → (t : ℝ) < tagRight q.2 →
      (q.2, q.1 t) ∈ tagLevelGraph H) ↔ _
    simp only [← not_lt, ← imp_iff_not_or, ← imp_iff_not_or]
  rw [heq]
  apply isClosed_iInter
  intro t
  exact (isClosed_le continuous_const
    (continuous_subtype_val.comp (continuous_tagLeft.comp continuous_snd))).union
    ((isClosed_le (continuous_subtype_val.comp
      (continuous_tagRight.comp continuous_snd)) continuous_const).union
      ((isClosed_tagLevelGraph hH).preimage
        (continuous_snd.prodMk ((continuous_eval_const t).comp continuous_fst))))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TagValidity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel tests for nonconstant active tags and excluded level tuples. -/

open Set MeasureTheory Topology
open scoped Topology Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem isOpen_nonconstantTagSegment : IsOpen (nonconstantTagSegment (X := X)) := by
  simp only [nonconstantTagSegment, ofPred_exists]
  apply isOpen_iUnion
  intro s
  apply isOpen_iUnion
  intro t
  have hl : Continuous (fun q : C(PathTime, X) × TagSlot => (tagLeft q.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_tagLeft.comp continuous_snd)
  have hr : Continuous (fun q : C(PathTime, X) × TagSlot => (tagRight q.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_tagRight.comp continuous_snd)
  exact (isOpen_lt hl continuous_const).inter
    ((isOpen_lt continuous_const hr).inter
      ((isOpen_lt hl continuous_const).inter
        ((isOpen_lt continuous_const hr).inter
          (isClosed_eq ((continuous_eval_const s).comp continuous_fst)
            ((continuous_eval_const t).comp continuous_fst)).isOpen_compl)))

theorem isOpen_validTagShape : IsOpen (validTagShape (X := X)) :=
  (isOpen_range_inl.preimage continuous_snd).union isOpen_nonconstantTagSegment

theorem isClosedEmbedding_insertTagTuple (n : ℕ) (l : Fin (n + 1) → ℕ) :
    IsClosedEmbedding (insertTagTuple n l) := by
  have hp : IsClosedEmbedding
      (Prod.mk l : ((Fin (n + 1) → UnitAddCircle) × PathTime × PathTime) → TagParameters n) := by
    refine ⟨isEmbedding_prodMkRight l, ?_⟩
    have heq : Set.range
        (Prod.mk l : ((Fin (n + 1) → UnitAddCircle) × PathTime × PathTime) → TagParameters n) =
        {p | p.1 = l} := by
      ext p
      constructor
      · rintro ⟨_, rfl⟩
        rfl
      · intro h
        exact ⟨p.2, Prod.ext h.symm rfl⟩
    rw [heq]
    exact isClosed_eq continuous_fst continuous_const
  exact IsClosedEmbedding.inr.comp (IsClosedEmbedding.sigmaMk.comp hp)

theorem measurableSet_tagTupleExcluded
    {N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (hN : ∀ n l, MeasurableSet (N n l)) : MeasurableSet (tagTupleExcluded N) := by
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro l
  exact (isClosedEmbedding_insertTagTuple n l).measurableEmbedding.measurableSet_image.mpr
    ((hN n l).prod MeasurableSet.univ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathEndpoints
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel endpoint and first-arrival restrictions for the base path codes. -/

open Set Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem isClosed_earlyHitSet (b : X) (n : ℕ) : IsClosed (earlyHitSet b n) := by
  let H : Set (C(PathTime, X) × PathTime) :=
    {q | (q.2 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) ∧ q.1 q.2 = b}
  have hH : IsClosed H :=
    (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).inter
      (isClosed_eq continuous_eval continuous_const)
  have heq : Prod.fst '' H = earlyHitSet b n := by
    ext γ
    constructor
    · rintro ⟨⟨γ, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(γ, t), ht, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace H hH

theorem firstArrival_iff (b : X) (γ : C(PathTime, X)) :
    FirstArrival b γ ↔ γ ⊤ = b ∧ ∀ n : ℕ, γ ∉ earlyHitSet b n := by
  constructor
  · rintro ⟨he, hfirst⟩
    refine ⟨he, fun n hn => ?_⟩
    obtain ⟨t, ht, htb⟩ := hn
    apply hfirst t _ htb
    change (t : ℝ) < 1
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · rintro ⟨he, hnone⟩
    refine ⟨he, fun t ht htb => ?_⟩
    have ht' : (t : ℝ) < 1 := ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr ht')
    exact hnone n ⟨t, by linarith, htb⟩

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_firstArrival (b : X) : MeasurableSet {γ | FirstArrival b γ} := by
  simp only [firstArrival_iff, ofPred_and, ofPred_forall]
  apply MeasurableSet.inter
  · exact (isClosed_eq (continuous_eval_const ⊤) continuous_const).measurableSet
  · exact MeasurableSet.iInter fun n => (isClosed_earlyHitSet b n).measurableSet.compl

variable [MeasurableSpace X] [BorelSpace X]

theorem measurableSet_endpointCodes {E : Set X} (hE : MeasurableSet E) (b : X) :
    MeasurableSet {Γ : TaggedPath X | Γ.1 ⊥ ∈ E ∧ FirstArrival b Γ.1} := by
  exact (((continuous_eval_const ⊥).measurable hE).preimage measurable_fst).inter
    ((measurableSet_firstArrival b).preimage measurable_fst)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TagCodeSpace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Standard Borel ambient codes and Borel simultaneous tag rules. -/

open Set MeasureTheory TopologicalSpace
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_tagRules {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i))
    {N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (hN : ∀ n l, MeasurableSet (N n l)) :
    MeasurableSet {Γ : TaggedPath X | TagRules H N Γ} := by
  simp only [TagRules, ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  have hc : Continuous (fun Γ : TaggedPath X => (Γ.1, Γ.2 k)) :=
    continuous_fst.prodMk ((continuous_apply k).comp continuous_snd)
  exact ((isOpen_validTagShape.measurableSet).preimage hc.measurable).inter
    (((isClosed_tagContainment hH).measurableSet.preimage hc.measurable).inter
      ((measurableSet_tagTupleExcluded hN).compl.preimage
        (((continuous_apply k).comp continuous_snd).measurable)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TagTupleMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted tag-tuple measures. Tuple components retain the label list;
slot weights depend only on the slot number and have finite total mass. -/

open Set MeasureTheory TopologicalSpace Topology
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem continuous_tagDataTuple : Continuous tagDataTuple := by
  apply continuous_sigma
  intro n
  exact continuous_sigmaMk.comp (continuous_fst.prodMk continuous_snd.fst)

theorem measurable_slotTupleMeasure : Measurable slotTupleMeasure := by
  classical
  let : MeasurableSpace TagData := borel TagData
  let : BorelSpace TagData := ⟨rfl⟩
  apply Measure.measurable_of_measurable_coe
  intro A hA
  let S : Set TagSlot := activeTagSlot '' (tagDataTuple ⁻¹' A)
  have hi : IsOpenEmbedding activeTagSlot := IsOpenEmbedding.inr
  have hme : MeasurableEmbedding activeTagSlot :=
    IsOpenEmbedding.measurableEmbedding (α := TagData) (β := TagSlot) hi
  have himg : MeasurableSet S := hme.measurableSet_image.mpr
    (continuous_tagDataTuple.measurable hA)
  have heq : (fun s => slotTupleMeasure s A) = S.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext s
    cases s with
    | inl u =>
      have hnot : (Sum.inl u : TagSlot) ∉ S := by
        rintro ⟨q, _, he⟩
        cases he
      change 0 = if (Sum.inl u : TagSlot) ∈ S then 1 else 0
      rw [ite_eq_right hnot]
    | inr q =>
      have hmem : (Sum.inr q : TagSlot) ∈ S ↔ tagDataTuple q ∈ A := by
        constructor
        · rintro ⟨p, hp, hpq⟩
          cases Sum.inr.inj hpq
          exact hp
        · intro hq
          exact ⟨q, hq, rfl⟩
      change (Measure.dirac (tagDataTuple q)) A = if (Sum.inr q : TagSlot) ∈ S then 1 else 0
      rw [Measure.dirac_apply' _ hA]
      change (if tagDataTuple q ∈ A then 1 else 0) = if (Sum.inr q : TagSlot) ∈ S then 1 else 0
      rw [hmem]
  rw [heq]
  exact measurable_const.indicator himg

theorem slotWeight_pos (k : ℕ) : 0 < slotWeight k := by
  unfold slotWeight
  exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))

theorem tsum_slotWeight : ∑' k, slotWeight k = 2 := ENNReal.tsum_geometric_two

theorem weightedTupleMeasure_apply (θ : ℕ → TagSlot) {s : Set LevelTuple}
    (hs : MeasurableSet s) :
    weightedTupleMeasure θ s = ∑' k, slotWeight k * slotTupleMeasure (θ k) s := by
  simp only [weightedTupleMeasure, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]

theorem measurable_weightedTupleMeasure : Measurable weightedTupleMeasure := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [weightedTupleMeasure_apply _ hs]
  apply Measurable.tsum
  intro k
  exact measurable_const.mul ((Measure.measurable_coe hs).comp
    (measurable_slotTupleMeasure.comp (measurable_pi_apply k)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathVariation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel length data for ordinary continuous metric paths. These are applied
to physical-domain subarcs when forming the path occupation kernel. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_rectifiablePaths :
    MeasurableSet {γ : C(PathTime, X) | BoundedVariationOn γ univ} := by
  change MeasurableSet {γ : C(PathTime, X) | eVariationOn γ univ ≠ ∞}
  exact (measurable_pathVariation univ) (measurableSet_singleton ∞).compl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical occupation of a rectifiable metric path, and its mean under a law.
The measure records arclength with multiplicity, including repeated traversals. -/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_pathOccupation : Measurable (pathOccupation (X := X)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he : Measurable (fun p : RectifiablePath X × PathTime => p.1.val p.2) :=
    (continuous_eval.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).measurable
  have hm := Kernel.measurable_kernel_prodMk_left_of_finite
    (κ := pathLengthKernel (X := X)) (he hs) (fun γ => inferInstance)
  change Measurable (fun γ : RectifiablePath X =>
    pathLengthMeasure γ (γ.val ⁻¹' s)) at hm
  simpa only [pathOccupation_apply _ hs] using hm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RectifiableOccupationCode
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Borel occupation code on the Borel subset of rectifiable paths.
The total extension is zero off that subset; length finiteness is always
checked separately before it is used as physical occupation. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_rectifiableOccupationCode :
    Measurable (rectifiableOccupationCode (X := X)) :=
  measurable_pathOccupation.dite measurable_const measurableSet_rectifiablePaths

instance instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology [CompleteSpace X] [SecondCountableTopology X] :
    StandardBorelSpace (RectifiablePath X) :=
  measurableSet_rectifiablePaths.standardBorel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalSubpaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual physical lifts of quotient paths on a compact time interval.
The quotient is inverted only where it is a homeomorphism. Constant extension
at the interval ends gives an ordinary continuous physical path. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem isOpen_pathsInsideOn {U : Set X} (hU : IsOpen U) (a b : PathTime) :
    IsOpen (pathsInsideOn U a b) :=
  ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc hU

theorem continuous_physicalSubpath {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) : Continuous (physicalSubpath e hab) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_subtype_val.comp (e.symm.continuous.comp
    ((continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      ((timeClip a b).continuous.comp continuous_snd))).subtype_mk _))

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurable_totalPhysicalSubpath {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    (hU : IsOpen U) {a b : PathTime} (hab : a ≤ b) (y₀ : Y) :
    Measurable (totalPhysicalSubpath e hab y₀) := by
  classical
  exact (continuous_physicalSubpath e hab).measurable.dite
    measurable_const (isOpen_pathsInsideOn hU a b).measurableSet

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_IncreasingMeasureLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise increasing limits of the finite-stage occupation measures. -/

open Set MeasureTheory Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y : Type*} [MeasurableSpace Y]

theorem measurable_increasingMeasureLimit {Z : Type*} [MeasurableSpace Z]
    (μ : Z → ℕ → Measure Y) (hμ : ∀ z, Monotone (μ z))
    (hmeas : ∀ n, Measurable (fun z => μ z n)) :
    Measurable (fun z => increasingMeasureLimit (μ z) (hμ z)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [increasingMeasureLimit_apply _ _ hs]
  exact Measurable.iSup fun n => (Measure.measurable_coe hs).comp (hmeas n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalDyadicLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel dyadic physical length and finite-stage occupation data.
Every length here uses the physical metric after inverting the quotient. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurable_physicalDyadicLength (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (n : ℕ) (i : Fin (2 ^ n)) : Measurable (physicalDyadicLength e y₀ n i) :=
  (measurable_pathVariation univ).comp
    (measurable_totalPhysicalSubpath e hU (dyadicLeft_le_right n i) y₀)

theorem measurable_physicalDomainLength (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (physicalDomainLength e y₀) := by
  apply Measurable.iSup
  intro n
  exact Finset.measurable_sum _ fun i _ => measurable_physicalDyadicLength e hU y₀ n i

theorem measurableSet_finitePhysicalDomainLength (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    MeasurableSet {γ : C(PathTime, X) | physicalDomainLength e y₀ γ < ∞} :=
  measurableSet_lt (measurable_physicalDomainLength e hU y₀) measurable_const

variable [MeasurableSpace Y] [BorelSpace Y]

theorem measurable_physicalStageOccupation (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (n : ℕ) :
    Measurable (physicalStageOccupation e y₀ n) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.measurable_sum
  intro i _
  exact (Measure.measurable_coe hs).comp (measurable_rectifiableOccupationCode.comp
    (measurable_totalPhysicalSubpath e hU (dyadicLeft_le_right n i) y₀))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DyadicPhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Borel limit of the increasing dyadic physical occupation measures.
Its mass is the dyadic domain-length functional, and it is supported in the
physical domain. `PhysicalLengthCharacterization` identifies the associated
time measure with compact-interval arclength and componentwise exhaustion. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurable_dyadicPhysicalOccupation (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (dyadicPhysicalOccupation e y₀) := by
  apply measurable_increasingMeasureLimit
  intro n
  exact (measurable_physicalStageOccupation e hU y₀ n).comp measurable_subtype_coe

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathGates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many closed collar gates give Borel restrictions on path codes. -/

open Set Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem isClosed_separatedGateViolation {C : Set X} (hC : IsClosed C)
    (K : Set X) (r : ℝ) : IsClosed (separatedGateViolation C K r) := by
  let S : Set (C(PathTime, X) × PathTime) :=
    {q | q.1 q.2 ∈ C ∧ ∀ p ∈ K, r ≤ dist (q.1 q.2) p}
  have hS : IsClosed S := by
    refine (hC.preimage continuous_eval).inter ?_
    change IsClosed {q : C(PathTime, X) × PathTime |
      ∀ p ∈ K, r ≤ dist (q.1 q.2) p}
    simp only [ofPred_forall]
    exact isClosed_iInter fun p => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_eval.dist continuous_const)
  have heq : Prod.fst '' S = separatedGateViolation C K r := by
    ext γ
    constructor
    · rintro ⟨⟨γ, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(γ, t), ht, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace S hS

theorem gateRule_iff {C K : Set X} (hK : IsClosed K) (γ : C(PathTime, X)) :
    GateRule C K γ ↔ ∀ n : ℕ, γ ∉ separatedGateViolation C K (1 / ((n : ℝ) + 1)) := by
  constructor
  · intro h n ⟨t, ht, hsep⟩
    have hz := hsep (γ t) (h t ht)
    rw [dist_self] at hz
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro h t ht
    by_contra hn
    obtain ⟨ε, hε, hball⟩ := isOpen_iff.mp hK.isOpen_compl (γ t) hn
    obtain ⟨n, hne⟩ := exists_nat_one_div_lt hε
    apply h n
    refine ⟨t, ht, fun p hp => hne.le.trans ?_⟩
    by_contra hdist
    have hd : dist p (γ t) < ε := by simpa only [dist_comm] using not_le.mp hdist
    exact hball hd hp

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_gateRule {C K : Set X} (hC : IsClosed C) (hK : IsClosed K) :
    MeasurableSet {γ | GateRule C K γ} := by
  simp only [gateRule_iff hK, ofPred_forall]
  exact MeasurableSet.iInter fun n =>
    (isClosed_separatedGateViolation hC K (1 / ((n : ℝ) + 1))).measurableSet.compl

theorem measurableSet_gateRules {C K : ℕ → Set X}
    (hC : ∀ n, IsClosed (C n)) (hK : ∀ n, IsClosed (K n)) :
    MeasurableSet {γ | GateRules C K γ} := by
  simp only [GateRules, ofPred_forall]
  exact MeasurableSet.iInter fun n => measurableSet_gateRule (hC n) (hK n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BasePathCodes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base-code space from the positive-law construction. The defining
relations are the actual path-hit and level incidences, with physical length,
finite deletions, optional tags, endpoint conditions and collar gates. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable (X Y : Type*) [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

variable {X Y}

variable [SecondCountableTopology X] [BorelSpace X]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurableSet_allowedTaggedPath (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i))
    [∀ i, SFinite (d.priorLaws i)]
    (hprior : ∀ i, (support (priorHitMass (d.priorLaws i))).Countable)
    (hlevel : ∀ i, (support (d.levelWeights i)).Countable)
    (dustMeasure : Measure X) [SFinite dustMeasure]
    {N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (hN : ∀ n l, MeasurableSet (N n l)) :
    MeasurableSet {Γ | AllowedTaggedPath d dustMeasure N Γ} := by
  unfold AllowedTaggedPath
  exact ((measurableSet_finitePhysicalDomainLength d.domainEquiv hU d.basePoint).preimage
    measurable_fst).inter ((measurableSet_tagRules hH hN).inter
    ((measurableSet_residualConstraintFamily hB (fun _ => isClosed_pathHitSet)
      d.priorDeletions d.priorLaws hprior).inter
      ((measurableSet_residualConstraintFamily hB hH (fun _ => d.flagDeletions)
        (fun _ => volume) hlevel).inter (measurableSet_residualImageMass_zero hB dustMeasure))))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DelayedTupleMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Delaying tags scales their weighted tuple measure, allowing every finite
tuple cost of a fixed allowed path to become arbitrarily small. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem slotWeight_add (N k : ℕ) : slotWeight (N + k) = slotWeight N * slotWeight k :=
  pow_add _ _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PreterminalVisits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Visit multiplicities with the terminal parameter omitted. The extended
subtraction formula is justified by an exact all-time sum decomposition. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_terminalVisitCount :
    Measurable (fun q : C(PathTime, X) × X => terminalVisitCount q.1 q.2) := by
  unfold terminalVisitCount
  exact measurable_const.ite
    ((isClosed_eq ((continuous_eval_const ⊤).comp continuous_fst) continuous_snd).measurableSet)
    measurable_const

theorem measurable_preterminalVisitCount :
    Measurable (fun q : C(PathTime, X) × X => preterminalVisitCount q.1 q.2) :=
  measurable_visitCount.sub measurable_terminalVisitCount


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_AtomicVisitMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The countable atomic part of a path's coding measure, using actual
preterminal visit multiplicity and prescribed positive point weights. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X D : Type*} [MetricSpace X] [MeasurableSpace D]

theorem atomicVisitMeasure_apply (p : D → X) (c : D → ℝ≥0∞) (γ : C(PathTime, X))
    {A : Set D} (hA : MeasurableSet A) :
    atomicVisitMeasure p c γ A =
      ∑' s, (c s * preterminalVisitCount γ (p s)) * A.indicator 1 s := by
  simp only [atomicVisitMeasure, Measure.sum_apply _ hA, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hA]

variable [Countable D] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_atomicVisitMeasure (p : D → X) (c : D → ℝ≥0∞) :
    Measurable (atomicVisitMeasure p c) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp_rw [atomicVisitMeasure_apply p c _ hA]
  apply Measurable.tsum
  intro s
  exact (measurable_const.mul (measurable_preterminalVisitCount.comp
    (measurable_id.prodMk measurable_const))).mul_const _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathCostMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual three-part coding measure: physical occupation, countable
preterminal visits, and weighted tuples. Finiteness is a Borel code condition. -/

open Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

omit [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_costPhysical : Measurable (costPhysical (Y := Y) (D := D)) := by
  have hc : Continuous (costPhysical (Y := Y) (D := D)) := continuous_inl
  exact Continuous.measurable (α := Y) (γ := PathCostSpace Y D) hc

omit [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_costAtomic : Measurable (costAtomic (Y := Y) (D := D)) := by
  have hc : Continuous (costAtomic (Y := Y) (D := D)) := continuous_inr.comp continuous_inl
  exact Continuous.measurable (α := D) (γ := PathCostSpace Y D) hc

omit [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_costTuple : Measurable (costTuple (Y := Y) (D := D)) := by
  have hc : Continuous (costTuple (Y := Y) (D := D)) := continuous_inr.comp continuous_inr
  exact Continuous.measurable (α := LevelTuple) (γ := PathCostSpace Y D) hc

variable [SecondCountableTopology X] [Countable D]

omit [BorelSpace X] [SecondCountableTopology X] in
theorem measurable_baseCodeOccupation (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) :
    Measurable (baseCodeOccupation d) :=
  (measurable_dyadicPhysicalOccupation d.domainEquiv hU d.basePoint).comp
    ((measurable_fst.comp measurable_subtype_coe).subtype_mk)

theorem measurable_pathCostMeasure (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) : Measurable (pathCostMeasure d p c) := by
  exact (((Measure.measurable_map _ measurable_costPhysical).comp
    (measurable_baseCodeOccupation d hU)).add
    ((Measure.measurable_map _ measurable_costAtomic).comp
      ((measurable_atomicVisitMeasure p c).comp (measurable_fst.comp measurable_subtype_coe)))).add
    ((Measure.measurable_map _ measurable_costTuple).comp
      (measurable_weightedTupleMeasure.comp (measurable_snd.comp measurable_subtype_coe)))

theorem measurableSet_finiteCostCode (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) :
    MeasurableSet {Γ : BasePathCode d | pathCostMeasure d p c Γ univ < ∞} :=
  measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp
    (measurable_pathCostMeasure d hU p c)) measurable_const

theorem standardBorel_finiteCostCode (d : PathCodeData X Y) [StandardBorelSpace (BasePathCode d)]
    (hU : IsOpen d.quotientDomain) (p : D → X) (c : D → ℝ≥0∞) :
    StandardBorelSpace (FiniteCostCode d p c) :=
  (measurableSet_finiteCostCode d hU p c).standardBorel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TupleReference
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tuple reference measure is a positive weighted sum of Lebesgue
measures on the finite tuple tori, indexed by label type rather than slot. -/

open Set MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuous_tupleFiber (i : TupleType) : Continuous (tupleFiber i) :=
  continuous_sigmaMk.comp (continuous_const.prodMk continuous_id)

theorem measurable_tupleFiber (i : TupleType) : Measurable (tupleFiber i) :=
  Continuous.measurable (α := Fin (i.1 + 1) → UnitAddCircle) (γ := LevelTuple)
    (continuous_tupleFiber i)

theorem tupleReference_apply (ω : TupleType → ℝ≥0∞)
    {A : Set LevelTuple} (hA : MeasurableSet A) :
    tupleReference ω A = ∑' i, ω i * volume (tupleFiber i ⁻¹' A) := by
  simp only [tupleReference, Measure.sum_apply _ hA, Measure.smul_apply,
    smul_eq_mul, Measure.map_apply (measurable_tupleFiber _) hA]

theorem tupleReference_univ (ω : TupleType → ℝ≥0∞) :
    tupleReference ω univ = ∑' i, ω i := by
  rw [tupleReference_apply ω MeasurableSet.univ]
  apply tsum_congr
  intro i
  have hv : (volume : Measure (Fin (i.1 + 1) → UnitAddCircle)) univ = 1 := by
    change (Measure.pi (fun _ : Fin (i.1 + 1) => (volume : Measure UnitAddCircle))) univ = 1
    rw [Measure.pi_univ]
    simp [AddCircle.measure_univ]
  simp only [preimage_univ, hv, mul_one]

theorem finite_tupleReference {ω : TupleType → ℝ≥0∞} (hω : (∑' i, ω i) < ∞) :
    IsFiniteMeasure (tupleReference ω) := ⟨by rwa [tupleReference_univ]⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual mean occupation, atomic and tuple measures of a law on base
codes. Their sum is exactly the barycenter of the coding measures. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

omit [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)] [SecondCountableTopology X] in
theorem measurable_baseCodeTuple (d : PathCodeData X Y) :
    Measurable (fun Γ : BasePathCode d => weightedTupleMeasure Γ.val.2) :=
  measurable_weightedTupleMeasure.comp (measurable_snd.comp measurable_subtype_coe)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClopenNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolating a component by a clopen neighborhood

This is the compact-space step before the smooth contour construction:
a neighborhood containing a whole component contains a clopen
neighborhood of that component's base point. Applied in a closed
obstacle set, it isolates a singleton dust component.
-/

open Set

namespace CircleDomainRigidity

theorem exists_clopen_between_component_and_open
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x : X) {O : Set X} (hO : IsOpen O) (hC : connectedComponent x ⊆ O) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ O := by
  classical
  have hd : Disjoint Oᶜ (connectedComponent x) :=
    Set.disjoint_left.mpr (fun y hy hyC => hy (hC hyC))
  rw [connectedComponent_eq_iInter_isClopen x] at hd
  obtain ⟨s, hs⟩ := hO.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun V : {V : Set X // IsClopen V ∧ x ∈ V} => V.val)
    (fun V => V.property.1.isClosed) (Set.disjoint_iff_inter_eq_empty.mp hd)
  refine ⟨⋂ V ∈ s, (V : Set X), isClopen_biInter_finset (fun V _ => V.property.1),
    mem_iInter₂.mpr (fun V _ => V.property.2), ?_⟩
  intro y hy
  by_contra hyO
  exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hs) hyO hy

/-- In particular, singleton components in a compact closed obstacle
have arbitrarily small relatively clopen neighborhoods. -/
theorem exists_clopen_neighborhood_of_singleton_component
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x : X) (hC : connectedComponent x = {x}) {O : Set X}
    (hO : IsOpen O) (hx : x ∈ O) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ O :=
  exists_clopen_between_component_and_open x hO (by simpa only [hC, singleton_subset_iff] using hx)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ComponentLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localizing nondegenerate components

Boundary bumping turns a nondegenerate continuum through a point into
one in any prescribed neighborhood. This is the localization used in
the lower-grid obstacle argument. Totally disconnected dust cannot
destroy a singleton component of a compact closed obstacle.
-/

open Set Topology

namespace CircleDomainRigidity

theorem exists_nontrivial_subcontinuum_in_open
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {C U : Set X} (hcompact : IsCompact C) (hconn : IsConnected C)
    (hnt : C.Nontrivial) {x : X} (hx : x ∈ C) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ D : Set X, IsCompact D ∧ IsConnected D ∧ D.Nontrivial ∧ x ∈ D ∧ D ⊆ C ∩ U := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  let : PreconnectedSpace C := Subtype.preconnectedSpace hconn.isPreconnected
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  let xc : C := ⟨x, hx⟩
  let yc : C := ⟨y, hy⟩
  let O : Set C := (Subtype.val ⁻¹' U) ∩ {yc}ᶜ
  have hO : IsOpen O := (hU.preimage continuous_subtype_val).inter
    isClosed_singleton.isOpen_compl
  have hxO : xc ∈ O := ⟨hxU, fun heq => hyx (congrArg Subtype.val heq).symm⟩
  obtain ⟨N, hNnhds, hNclosed, hNO⟩ := exists_mem_nhds_isClosed_subset (hO.mem_nhds hxO)
  have hxN : xc ∈ N := mem_of_mem_nhds hNnhds
  have hNproper : N ≠ univ := by
    intro heq
    have hyN : yc ∈ N := by rw [heq]; trivial
    exact (hNO hyN).2 rfl
  obtain ⟨z, hz, hzfront⟩ := component_meets_frontier hNclosed hNproper hxN
  let K := connectedComponentIn N xc
  have hKclosed : IsClosed K := by
    change IsClosed (connectedComponentIn N xc)
    rw [connectedComponentIn_eq_image hxN]
    exact hNclosed.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hKconn : IsConnected K := isConnected_connectedComponentIn_iff.mpr hxN
  let D : Set X := Subtype.val '' K
  have hxD : x ∈ D := ⟨xc, mem_connectedComponentIn hxN, rfl⟩
  have hzD : z.val ∈ D := ⟨z, hz, rfl⟩
  have hzx : z.val ≠ x := by
    intro heq
    have hzc : z = xc := Subtype.ext heq
    have hxfront : xc ∈ frontier N := hzc ▸ hzfront
    exact hxfront.2 (mem_interior_iff_mem_nhds.mpr hNnhds)
  refine ⟨D, hKclosed.isCompact.image continuous_subtype_val,
    hKconn.image _ continuous_subtype_val.continuousOn,
    ⟨x, hxD, z.val, hzD, hzx.symm⟩, hxD, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.property, (hNO (connectedComponentIn_subset N xc hw)).1⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallPhysicalDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small physical disks at singleton quotient components

A singleton component of a closed quotient obstacle has a compact relatively
clopen neighborhood inside any prescribed open neighborhood. Pulling it back
and applying the proved smooth contour construction gives actual physical
Jordan disks. The boundaries avoid the entire quotient obstacle, and hence
lie in the physical domain whenever that obstacle contains the collapsed
complementary components.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- The compact relatively clopen obstacle piece used before smoothing. -/
theorem exists_compact_piece_of_singleton_component
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ A : Set X, IsCompact A ∧ x ∈ A ∧ A ⊆ F ∧ A ⊆ V ∧ IsClosed (F \ A) := by
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let xf : F := ⟨x, hx⟩
  have hcomp : connectedComponent xf = {xf} := by
    apply Set.Subset.antisymm
    · intro y hy
      have hy' : y.val ∈ connectedComponentIn F x := by
        rw [connectedComponentIn_eq_image hx]
        exact ⟨y, hy, rfl⟩
      rw [hcomponent] at hy'
      exact mem_singleton_iff.mpr (Subtype.ext (mem_singleton_iff.mp hy'))
    · exact singleton_subset_iff.mpr mem_connectedComponent
  obtain ⟨B, hB, hxB, hBV⟩ := exists_clopen_neighborhood_of_singleton_component xf hcomp
    (hV.preimage continuous_subtype_val) hxV
  let A : Set X := Subtype.val '' B
  have hdiff : F \ A = Subtype.val '' Bᶜ := by
    ext y
    constructor
    · rintro ⟨hyF, hyA⟩
      exact ⟨⟨y, hyF⟩, fun h => hyA ⟨⟨y, hyF⟩, h, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Subtype.ext hzy
      exact hy (hzy' ▸ hz)
  refine ⟨A, hB.isClosed.isCompact.image continuous_subtype_val,
    ⟨xf, hxB, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.property
  · rintro _ ⟨y, hy, rfl⟩
    exact hBV hy
  · rw [hdiff]
    exact hF.isClosedMap_subtype_val _ hB.isOpen.isClosed_compl

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SinglePhysicalDisk
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A single smooth physical disk about a quotient singleton

Connectedness of the fiber upgrades the finite disjoint cover to a single
disk. The general open-family lemma does not need finiteness.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_member_containing_connected_set
    {X I : Type*} [TopologicalSpace X] {S : Set X} (hS : IsConnected S)
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hd : Pairwise (Disjoint on U)) (hcover : S ⊆ ⋃ i, U i) :
    ∃ i, S ⊆ U i := by
  classical
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  let V : Set X := ⋃ j ∈ ({i}ᶜ : Set I), U j
  have hV : IsOpen V := isOpen_biUnion (fun j _ => hU j)
  have hUV : Disjoint (U i) V := by
    apply Set.disjoint_left.mpr
    intro z hz hzV
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzV
    exact Set.disjoint_left.mp (hd (fun h => hj (mem_singleton_iff.mpr h.symm))) hz hzj
  have hSC : S ⊆ U i ∪ V := by
    intro z hz
    obtain ⟨j, hzj⟩ := mem_iUnion.mp (hcover hz)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hzj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j, by simpa using hji, hzj⟩)
  rcases hS.isPreconnected.subset_or_subset (hU i) hV hUV hSC with h | h
  · exact ⟨i, h⟩
  · exact (Set.disjoint_left.mp hUV hxi (h hx)).elim

theorem isConnected_finite_fiber
    {X : Type*} (π : Sphere → X) (hfibers : ∀ x, IsConnected (π ⁻¹' {x}))
    {x : X} (hne : π OnePoint.infty ≠ x) :
    IsConnected {z : ℂ | π (z : Sphere) = x} := by
  have heq : ((↑) : ℂ → Sphere) '' {z : ℂ | π (z : Sphere) = x} = π ⁻¹' {x} := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp [hne]
    | coe z => simp [OnePoint.coe_injective.mem_set_image]
  have hconn : IsConnected (((↑) : ℂ → Sphere) '' {z : ℂ | π (z : Sphere) = x}) :=
    heq.symm ▸ hfibers x
  refine ⟨?_, OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
    hconn.isPreconnected⟩
  obtain ⟨p, hp⟩ := hconn.nonempty
  obtain ⟨z, hz, _⟩ := hp
  exact ⟨z, hz⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SaturatedDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Saturation of physical Jordan interiors

A connected quotient fiber cannot cross a boundary consisting of singleton
fibers. Thus physical Jordan interiors whose boundaries lie in the original
domain are saturated, and project to open quotient neighborhoods. This is
the saturation assertion preceding the small-disks lemma in Section 1.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem preimage_image_open_of_singleton_boundary_fibers
    {X Y : Type*} [TopologicalSpace X]
    (π : X → Y) (hfibers : ∀ y, IsPreconnected (π ⁻¹' {y}))
    {U : Set X} (hU : IsOpen U)
    (hsing : ∀ p ∈ frontier U, ∀ q, π q = π p → q = p) :
    π ⁻¹' (π '' U) = U := by
  apply Set.Subset.antisymm
  · rintro q ⟨p, hp, hpq⟩
    let K : Set X := π ⁻¹' {π p}
    have hpK : p ∈ K := rfl
    have hmiss : Disjoint K (frontier U) := by
      apply Set.disjoint_left.mpr
      intro z hz hzfront
      have hpz : p = z := hsing z hzfront p hz.symm
      have hpfront : p ∈ frontier U := hpz.symm ▸ hzfront
      rw [hU.frontier_eq] at hpfront
      exact hpfront.2 hp
    have hsplit : K ⊆ U ∨ K ⊆ (closure U)ᶜ := by
      apply (hfibers (π p)).subset_or_subset hU isClosed_closure.isOpen_compl
      · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
      · intro z hz
        by_cases hzU : z ∈ U
        · exact Or.inl hzU
        · right
          intro hzcl
          apply Set.disjoint_left.mp hmiss hz
          rw [hU.frontier_eq]
          exact ⟨hzcl, hzU⟩
    rcases hsplit with hin | hout
    · exact hin hpq.symm
    · exact (hout hpK (subset_closure hp)).elim
  · exact subset_preimage_image π U

/-- Physical Jordan disks with boundary in the domain are saturated for
the actual component-collapse quotient. -/
theorem preimage_image_jordanInterior_of_component_collapse
    {Y : Type*} (G : Set Sphere) (π : Sphere → Y) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' jordanInterior H := by
  apply preimage_image_open_of_singleton_boundary_fibers π
    (fun y => (connected_fibers_of_component_collapse G π hsurj hr y).isPreconnected)
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H))
  intro p hp q hqp
  rw [frontier_sphere_image_jordanInterior] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  rcases (hr (z : Sphere) q).mp hqp.symm with heq | ⟨hznot, _⟩
  · exact heq.symm
  · exact (hznot (hboundary z hz)).elim

/-- The saturated physical disk projects to an open quotient neighborhood. -/
theorem isOpen_image_jordanInterior_of_component_collapse
    {Y : Type*} [TopologicalSpace Y]
    (G : Set Sphere) (π : Sphere → Y) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    IsOpen (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  apply (hclosed.isQuotientMap hπ hsurj).isOpen_preimage.mp
  rw [preimage_image_jordanInterior_of_component_collapse G π hsurj hr H hboundary]
  exact OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalAreaLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local planar square integrability from spherical area. Spherical area
is written in its finite stereographic chart, with density 4/(1+|z|²)². -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_1
theorem lintegral_sphericalArea (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻x, g x ∂sphericalArea =
      ∫⁻z : ℂ, ENNReal.ofReal (sphericalAreaDensity z) * g (z : Sphere) := by
  rw [sphericalArea, lintegral_map hg OnePoint.continuous_coe.measurable]
  exact lintegral_withDensity_eq_lintegral_mul _
    continuous_sphericalAreaDensity.measurable.ennreal_ofReal
    (hg.comp OnePoint.continuous_coe.measurable)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereChartLipschitz
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed physical sphere metric has locally Lipschitz finite charts.
This follows from the explicit smooth inverse stereographic formula in
Mathlib, including the linear coordinates chosen by the sphere homeomorphism. -/

open Set Function Metric
open scoped Topology NNReal

noncomputable section

namespace CircleDomainRigidity

theorem contDiff_roundSphere_finite_chart :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) := by
  classical
  have hlin (W : Submodule ℝ RoundAmbient) (e : ℂ ≃L[ℝ] W) :
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z => (e z : RoundAmbient)) :=
    W.subtypeL.contDiff.comp e.contDiff
  simp only [roundSphereEquiv, onePointEquivSphereOfFinrankEq, Homeomorph.trans_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (stereoInvFunAux _ ∘ _)
  apply contDiff_stereoInvFunAux.comp
  exact hlin _ _

attribute [local instance] sphereMetric

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PeriodizedLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Periodizing scalar coarea lengths

A scalar coarea estimate controls the integral of the physical length
of real level sets. Integer translates of `[0,1)` partition the real
line, so the sum of these lengths over all lifts of a mod-one level
has the same integral on `[0,1)`. Countable subadditivity then gives
finite physical length for almost every mod-one level.
-/

open Set MeasureTheory Metric Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- The actual mod-one fiber of any real coordinate is the countable
union of its integer-translated scalar fibers. -/
theorem unitAddCircle_level_eq_iUnion_integer_levels {Z : Type*} (f : Z → ℝ) (t : ℝ) :
    {x | (f x : UnitAddCircle) = (t : UnitAddCircle)} =
      ⋃ k : ℤ, {x | f x = t + (k : ℝ)} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, unitAddCircle_eq_iff_exists_int]

theorem unitAddCircle_level_inter_eq_iUnion_integer_levels
    {Z : Type*} (f : Z → ℝ) (D : Set Z) (t : ℝ) :
    D ∩ {x | (f x : UnitAddCircle) = (t : UnitAddCircle)} =
      ⋃ k : ℤ, D ∩ {x | f x = t + (k : ℝ)} := by
  rw [unitAddCircle_level_eq_iUnion_integer_levels, inter_iUnion]

private theorem iUnion_integer_Ico : (⋃ k : ℤ, Ico (k : ℝ) ((k : ℝ) + 1)) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨⌊x⌋, Int.floor_le x, Int.lt_floor_add_one x⟩

private theorem pairwise_disjoint_integer_Ico :
    Pairwise (Disjoint on fun k : ℤ => Ico (k : ℝ) ((k : ℝ) + 1)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨hxi, hxi'⟩ ⟨hxj, hxj'⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hstep : i + 1 ≤ j := by omega
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hstep
    linarith
  · have hstep : j + 1 ≤ i := by omega
    have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hstep
    linarith

/-- Tonelli and the integer translates of a unit interval give the exact
periodized coarea integral. -/
theorem lintegral_periodizedLevelLength (L : ℝ → ℝ≥0∞) (hL : Measurable L) :
    ∫⁻ t in Ico (0 : ℝ) 1, periodizedLevelLength L t = ∫⁻ t, L t := by
  unfold periodizedLevelLength
  have hm (k : ℤ) : AEMeasurable (fun t : ℝ => L (t + (k : ℝ)))
      (volume.restrict (Ico (0 : ℝ) 1)) :=
    (hL.comp (measurable_id.add_const (k : ℝ))).aemeasurable
  rw [lintegral_tsum hm]
  have hshift (k : ℤ) :
      ∫⁻ t in Ico (0 : ℝ) 1, L (t + (k : ℝ)) =
        ∫⁻ t in Ico (k : ℝ) ((k : ℝ) + 1), L t := by
    have h := (measurePreserving_add_right volume (k : ℝ)).setLIntegral_comp_emb
      (Homeomorph.addRight (k : ℝ)).isClosedEmbedding.measurableEmbedding L (Ico 0 1)
    simpa only [image_add_const_Ico, zero_add, add_comm (1 : ℝ) (k : ℝ)] using h
  simp_rw [hshift]
  rw [← lintegral_iUnion (fun _ : ℤ => measurableSet_Ico) pairwise_disjoint_integer_Ico,
    iUnion_integer_Ico, Measure.restrict_univ]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoareaInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar coarea and its finite-energy consequences

The planar scalar coarea identities specialize
Federer, *Geometric Measure Theory*, Springer (1969), §3.2.11 (coarea)
and §3.2.12 (weighted coarea),
DOI: 10.1007/978-3-642-62010-2. For a `C¹` real function on an open
subset of the Euclidean plane, the integral of the one-dimensional
Hausdorff measures of its fibers equals the integral of the norm of its
differential. The locally Lipschitz version follows from the stated
Lipschitz coarea theorem by a countable relatively compact covering.

`PlanarScalarCoarea` and `WeightedPlanarScalarCoarea` express these
specializations as propositions. They require neither finite energy nor
topological conclusions. The length function need only be Lebesgue
measurable; Borel measurability is unnecessary.

Finite area and finite squared differential imply finite integrated
length, and integer periodization
gives finite physical length for almost every circle-valued level.
-/

open Set MeasureTheory Metric
open scoped ENNReal

namespace CircleDomainRigidity

/-- The scalar fibers are measurable even though the function is only
assumed continuous on its open domain. -/
theorem measurableSet_scalar_level {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (t : ℝ) :
    MeasurableSet (D ∩ {z | f z = t}) := by
  classical
  have hm : Measurable (D.piecewise f (fun _ => 0)) :=
    hf.measurable_piecewise continuousOn_const hD.measurableSet
  have heq : D ∩ {z | f z = t} =
      D ∩ (D.piecewise f (fun _ => 0)) ⁻¹' {t} := by
    ext z
    by_cases hz : z ∈ D <;> simp [hz]
  rw [heq]
  exact hD.measurableSet.inter (hm (measurableSet_singleton t))

/-- Countable additivity on the disjoint integer lifts is the exact
weighted circle-fiber identity. -/
theorem weightedCircleLevelLength_eq_periodized {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (q : ℂ → ℝ≥0∞) (t : ℝ) :
    weightedCircleLevelLength D f q t =
      periodizedLevelLength (weightedScalarLevelLength D f q) t := by
  unfold weightedCircleLevelLength periodizedLevelLength weightedScalarLevelLength
  rw [unitAddCircle_level_inter_eq_iUnion_integer_levels]
  apply lintegral_iUnion (fun k : ℤ => measurableSet_scalar_level hD hf (t + (k : ℝ)))
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨_, hzi⟩ ⟨_, hzj⟩
  change f z = t + (i : ℝ) at hzi
  change f z = t + (j : ℝ) at hzj
  apply hij
  exact_mod_cast (show (i : ℝ) = (j : ℝ) by linarith)

theorem lintegral_periodizedLevelLength_of_aemeasurable
    (L : ℝ → ℝ≥0∞) (hL : AEMeasurable L volume) :
    (∫⁻ t in Ico (0 : ℝ) 1, periodizedLevelLength L t) = ∫⁻ t, L t := by
  have htranslate (k : ℤ) :
      ∀ᵐ t ∂volume, L (t + (k : ℝ)) = hL.mk L (t + (k : ℝ)) :=
    (measurePreserving_add_right volume (k : ℝ)).quasiMeasurePreserving.ae hL.ae_eq_mk
  have heq : periodizedLevelLength L =ᵐ[volume.restrict (Ico (0 : ℝ) 1)]
      periodizedLevelLength (hL.mk L) := by
    filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr htranslate)] with t ht
    exact tsum_congr ht
  rw [lintegral_congr_ae heq, lintegral_periodizedLevelLength _ hL.measurable_mk,
    ← lintegral_congr_ae hL.ae_eq_mk]

/-- The weighted circle-valued coarea formula follows from the real
one, including the measurability needed for further integration. -/
theorem weighted_circle_coarea {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (q : ℂ → ℝ≥0∞)
    (hcoarea : WeightedScalarCoareaIdentity D f q) :
    AEMeasurable (weightedCircleLevelLength D f q)
        (volume.restrict (Ico (0 : ℝ) 1)) ∧
      (∫⁻ t in Ico (0 : ℝ) 1, weightedCircleLevelLength D f q t) =
        ∫⁻ z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖ := by
  have heq : weightedCircleLevelLength D f q =
      periodizedLevelLength (weightedScalarLevelLength D f q) :=
    funext (weightedCircleLevelLength_eq_periodized hD hf q)
  rw [heq]
  constructor
  · apply AEMeasurable.restrict
    exact AEMeasurable.tsum (fun k : ℤ => hcoarea.1.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume (k : ℝ)).quasiMeasurePreserving)
  · rw [lintegral_periodizedLevelLength_of_aemeasurable _ hcoarea.1, hcoarea.2]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExtendedWeightedCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted level estimate allows extended nonnegative densities.
Finite squared energy suffices; no pointwise finiteness is imposed. -/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace CircleDomainRigidity

theorem ennreal_mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  by_cases ha : a = ∞
  · simp [ha]
  by_cases hb : b = ∞
  · simp [hb]
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  have h : (a : ℝ) * (b : ℝ) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ)), sq_nonneg (a : ℝ), sq_nonneg (b : ℝ)]
  exact_mod_cast h

theorem weighted_circle_coarea_extended_finite_energy
    (hcoarea : WeightedPlanarScalarCoarea) {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) (q : ℂ → ℝ≥0∞) (hq : Measurable q)
    (hq2 : (∫⁻z in D, q z ^ 2) < ∞)
    (hf2 : (∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) < ∞) :
    AEMeasurable (weightedCircleLevelLength D f q) (volume.restrict (Ico (0 : ℝ) 1)) ∧
      (∫⁻t in Ico (0 : ℝ) 1, weightedCircleLevelLength D f q t) =
        (∫⁻z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖) ∧
      ∀ᵐt ∂volume.restrict (Ico (0 : ℝ) 1), weightedCircleLevelLength D f q t < ∞ := by
  obtain ⟨hmeas, heq⟩ := weighted_circle_coarea hD hf.continuousOn q (hcoarea D hD f hf q hq)
  have hfinite : (∫⁻t in Ico (0 : ℝ) 1, weightedCircleLevelLength D f q t) < ∞ := by
    rw [heq]
    calc
      _ ≤ ∫⁻z in D, (q z ^ 2 + ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) := by
        apply lintegral_mono
        intro z
        simpa only [ENNReal.ofReal_pow (norm_nonneg _)] using
          ennreal_mul_le_sq_add_sq (q z) (ENNReal.ofReal ‖fderiv ℝ f z‖)
      _ = (∫⁻z in D, q z ^ 2) + ∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) :=
        lintegral_add_left (hq.pow_const 2) _
      _ < ∞ := ENNReal.add_lt_top.mpr ⟨hq2, hf2⟩
  exact ⟨hmeas, heq, ae_lt_top' hmeas hfinite.ne⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CircleNullImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null images of local circle-valued traces

Projection modulo one preserves real outer-null sets. A countable family
of null real branches therefore gives a null image in the circle with
its Haar measure of total mass one.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

theorem volume_addCircle_image_eq_zero {A : Set ℝ} (hA : volume A = 0) :
    volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' A) = 0 := by
  have hpiece (a : ℝ) :
      volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' (A ∩ Ioc a (a + 1))) = 0 := by
    let e := AddCircle.measurableEquivIoc (1 : ℝ) a
    let S : Set (Ioc a (a + 1)) := Subtype.val ⁻¹' A
    have he : MeasurePreserving e volume (volume.comap Subtype.val) :=
      AddCircle.measurePreserving_equivIoc (1 : ℝ)
    have hset : e ⁻¹' S = ((↑) : ℝ → AddCircle (1 : ℝ)) '' (A ∩ Ioc a (a + 1)) := by
      ext y
      constructor
      · intro hy
        refine ⟨(e y).val, ⟨hy, (e y).property⟩, ?_⟩
        exact AddCircle.coe_equivIoc
      · rintro ⟨x, hx, rfl⟩
        change (AddCircle.equivIoc (1 : ℝ) a (x : AddCircle (1 : ℝ))).val ∈ A
        rw [AddCircle.equivIoc_coe_eq hx.2]
        exact hx.1
    rw [← hset, he.measure_preimage_equiv S,
      (MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply]
    apply measure_mono_null _ hA
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hcover : ((↑) : ℝ → AddCircle (1 : ℝ)) '' A ⊆
      ⋃ k : ℤ, ((↑) : ℝ → AddCircle (1 : ℝ)) ''
        (A ∩ Ioc ((k : ℝ) - 1) ((k : ℝ) - 1 + 1)) := by
    rintro y ⟨x, hx, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨⌈x⌉, x, ⟨hx, ?_⟩, rfl⟩
    have hlo := Int.ceil_lt_add_one x
    have hhi := Int.le_ceil x
    constructor <;> linarith
  apply measure_mono_null hcover
  exact measure_iUnion_null (fun k => hpiece ((k : ℝ) - 1))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RawBarrierCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compatibility for the actual raw path-cost barrier. Finite level
payments and square-summable point incidences give the null component
traces; the only descriptive-set input is the cited finite-torus form of
Kechris's analytic-measurability theorem. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem freeComponentFailure_empty_labels
    {X T Λ : Type*} [TopologicalSpace X]
    (F : Set X) (Rnew : Set (X × T)) (R : Λ → Set (X × T)) (labels : Fin 0 → Λ) :
    freeComponentFailure F Rnew R labels = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro z ⟨⟨x, t, θ⟩, hx, _⟩
  have he : {y | (y, θ) ∈ finiteLevelUnionGraph R labels} = ∅ := by
    simp [finiteLevelUnionGraph]
  have hh := hx.2.2
  change (connectedComponentIn {y | (y, θ) ∈ finiteLevelUnionGraph R labels} x).Nontrivial at hh
  rw [he, connectedComponentIn_eq_empty (by simp)] at hh
  exact not_nontrivial_empty hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_BoundaryTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unique traces outside the countable band support

For a bounded real coordinate the interval band is the actual interval
between the lower and upper boundary limits. A zero band budget forces
these limits to agree and gives convergence from the physical domain.
Square summability of the budgets makes all exceptions countable.
-/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

theorem countable_band_support {X : Type*} {a : X → ℝ}
    (ha : Summable (fun x => a x ^ 2)) : {x | a x ≠ 0}.Countable := by
  simpa only [Function.support, ne_eq, sq_eq_zero_iff] using ha.countable_support

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PlanarDifferentialEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-transfer gradient energy controls the norm of the scalar
real differential in the complex coarea chart. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem norm_complex_real_linear_le (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ≤ |L 1| + |L Complex.I| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hsplit : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    ‖L z‖ = ‖z.re • L 1 + z.im • L Complex.I‖ := by
      conv_lhs => rw [hsplit, map_add, map_smul, map_smul]
    _ ≤ ‖z.re • L 1‖ + ‖z.im • L Complex.I‖ := norm_add_le _ _
    _ = |z.re| * |L 1| + |z.im| * |L Complex.I| := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖z‖ * |L 1| + ‖z‖ * |L Complex.I| :=
      add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (abs_nonneg _))
    _ = (|L 1| + |L Complex.I|) * ‖z‖ := by ring

theorem complex_chart_differential_energy_finite
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {f : (ℝ × ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f D)
    (henergy : MemLp (FiniteTransfer.planarGradient f) 2 (volume.restrict D)) :
    (∫⁻z in Complex.equivRealProdCLM ⁻¹' D,
      ENNReal.ofReal (‖fderiv ℝ (f ∘ Complex.equivRealProdCLM) z‖ ^ 2)) < ∞ := by
  let e := Complex.equivRealProdCLM
  let μ : Measure ℂ := volume.restrict (e ⁻¹' D)
  have hmp : MeasurePreserving e μ (volume.restrict D) :=
    Complex.volume_preserving_equiv_real_prod.restrict_preimage hD.measurableSet
  have hx := henergy.fst.comp_measurePreserving hmp
  have hy := henergy.snd.comp_measurePreserving hmp
  have hi : Integrable (fun z : ℂ =>
      2 * ((fderiv ℝ f (e z)) (1, 0) ^ 2 + (fderiv ℝ f (e z)) (0, 1) ^ 2)) μ := by
    simpa only [FiniteTransfer.planarGradient, Function.comp_apply, Pi.add_apply] using
      (hx.integrable_sq.add hy.integrable_sq).const_mul 2
  have hfinite : (∫⁻z, ENNReal.ofReal
      (2 * ((fderiv ℝ f (e z)) (1, 0) ^ 2 + (fderiv ℝ f (e z)) (0, 1) ^ 2)) ∂μ) < ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => by positivity)).2 hi |>.lt_top
  apply lt_of_le_of_lt (lintegral_mono_ae ?_) hfinite
  filter_upwards [ae_restrict_mem (hD.preimage e.continuous).measurableSet] with z hz
  apply ENNReal.ofReal_le_ofReal
  have hdiff : DifferentiableAt ℝ f (e z) :=
    (hf.differentiableOn (by norm_num) _ hz).differentiableAt (hD.mem_nhds hz)
  have heq : fderiv ℝ (f ∘ e) z = (fderiv ℝ f (e z)).comp e.toContinuousLinearMap := by
    rw [fderiv_comp z hdiff e.differentiableAt, e.fderiv]
  have hn := norm_complex_real_linear_le ((fderiv ℝ f (e z)).comp e.toContinuousLinearMap)
  have hnorm : ‖fderiv ℝ (f ∘ e) z‖ ≤
      |(fderiv ℝ f (e z)) (1, 0)| + |(fderiv ℝ f (e z)) (0, 1)| := by
    rw [heq]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    e, Complex.equivRealProdCLM_apply, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im] using hn
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [sq_abs ((fderiv ℝ f (e z)) (1, 0)), sq_abs ((fderiv ℝ f (e z)) (0, 1)),
    sq_nonneg (|(fderiv ℝ f (e z)) (1, 0)| - |(fderiv ℝ f (e z)) (0, 1)|)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedHausdorffImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Hausdorff-measure estimates for the finite sphere chart.
The estimates are proved from the library's Lipschitz Hausdorff bound. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

theorem lipschitzOn_hausdorff_restrict_le_map
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Measurable f) {K : ℝ≥0} {S : Set X}
    (hK : LipschitzOnWith K f S) :
    (μH[1] : Measure Y).restrict (f '' S) ≤
      (K : ℝ≥0∞) • ((μH[1] : Measure X).restrict S).map f := by
  apply Measure.le_iff.mpr
  intro T hT
  rw [Measure.restrict_apply hT, Measure.smul_apply, Measure.map_apply hf hT,
    Measure.restrict_apply (hf hT)]
  have heq : T ∩ f '' S = f '' (f ⁻¹' T ∩ S) := by
    ext y
    constructor
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxS⟩, rfl⟩
      exact ⟨hx, x, hxS, rfl⟩
  rw [heq]
  simpa only [ENNReal.rpow_one, smul_eq_mul] using
    (hK.mono inter_subset_right).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)

theorem lipschitzOn_lintegral_hausdorff_image_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Measurable f) {K : ℝ≥0} {S : Set X}
    (hK : LipschitzOnWith K f S) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y in f '' S, g y ∂(μH[1] : Measure Y)) ≤
      (K : ℝ≥0∞) * ∫⁻x in S, g (f x) ∂(μH[1] : Measure X) := by
  calc
    _ ≤ ∫⁻y, g y ∂((K : ℝ≥0∞) • ((μH[1] : Measure X).restrict S).map f) :=
      lintegral_mono' (lipschitzOn_hausdorff_restrict_le_map hf hK) le_rfl
    _ = _ := by rw [lintegral_smul_measure, lintegral_map hg hf, smul_eq_mul]

theorem lintegral_hausdorff_image_le_of_partition
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Measurable f) (A : ℕ → Set X)
    (hA : ∀n, MeasurableSet (A n)) (hdisj : Pairwise (Disjoint on A))
    (hcover : ⋃n, A n = univ) (K : ℕ → ℝ≥0)
    (hK : ∀n, LipschitzOnWith (K n) f (A n))
    (w : X → ℝ≥0∞)
    (hweight : ∀n x, x ∈ A n → (K n : ℝ≥0∞) ≤ w x)
    {S : Set X} (hS : MeasurableSet S) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y in f '' S, g y ∂(μH[1] : Measure Y)) ≤
      ∫⁻x in S, w x * g (f x) ∂(μH[1] : Measure X) := by
  have hsets : ⋃n, S ∩ A n = S := by rw [← inter_iUnion, hcover, inter_univ]
  calc
    _ = ∫⁻y in ⋃n, f '' (S ∩ A n), g y ∂(μH[1] : Measure Y) := by
      rw [← image_iUnion, hsets]
    _ ≤ ∑'n, ∫⁻y in f '' (S ∩ A n), g y ∂(μH[1] : Measure Y) :=
      lintegral_iUnion_le _ _
    _ ≤ ∑'n, ∫⁻x in S ∩ A n, w x * g (f x) ∂(μH[1] : Measure X) := by
      apply ENNReal.tsum_le_tsum
      intro n
      calc
        _ ≤ (K n : ℝ≥0∞) * ∫⁻x in S ∩ A n, g (f x) ∂(μH[1] : Measure X) :=
          lipschitzOn_lintegral_hausdorff_image_le hf ((hK n).mono inter_subset_right) g hg
        _ = ∫⁻x in S ∩ A n, (K n : ℝ≥0∞) * g (f x) ∂(μH[1] : Measure X) :=
          (lintegral_const_mul _ (hg.comp hf)).symm
        _ ≤ _ := setLIntegral_mono' (hS.inter (hA n)) fun x hx =>
          mul_le_mul' (hweight n x hx.2) le_rfl
    _ = _ := by
      rw [← lintegral_iUnion (fun n => hS.inter (hA n))
        (fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right), hsets]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_GlobalSphericalDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The decaying finite-chart density is globally square integrable.
No compact restriction is needed after inserting the spherical factor. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem spherical_weight_sq_le_areaDensity (z : ℂ) :
    (1 / (1 + ‖z‖ ^ 2)) ^ 2 ≤ sphericalAreaDensity z := by
  rw [div_pow, one_pow, sphericalAreaDensity]
  exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LinearChartWeight
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed linear coordinates in the sphere homeomorphism preserve
the inverse quadratic decay of stereographic derivatives. -/

noncomputable section

namespace CircleDomainRigidity

theorem linear_chart_inverse_quadratic_bound
    {v : RoundAmbient} (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    16 * ‖A.toContinuousLinearMap‖ / (‖A z‖ ^ 2 + 4) ≤
      (16 * ‖A.toContinuousLinearMap‖ * (1 + ‖A.symm.toContinuousLinearMap‖ ^ 2)) /
        (1 + ‖z‖ ^ 2) := by
  have hlin : ‖z‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A z‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      A.symm.toContinuousLinearMap.le_opNorm (A z)
  have hsq := pow_le_pow_left₀ (norm_nonneg z) hlin 2
  simp only [mul_pow] at hsq
  have hden : 1 + ‖z‖ ^ 2 ≤
      (1 + ‖A.symm.toContinuousLinearMap‖ ^ 2) * (‖A z‖ ^ 2 + 4) := by
    nlinarith [sq_nonneg ‖A.symm.toContinuousLinearMap‖, sq_nonneg ‖A z‖]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  calc
    _ ≤ (16 * ‖A.toContinuousLinearMap‖) *
        ((1 + ‖A.symm.toContinuousLinearMap‖ ^ 2) * (‖A z‖ ^ 2 + 4)) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_StereographicDerivativeBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decay of the derivative of the fixed inverse stereographic map.
This supplies the spherical weight missing from a compact-chart bound. -/

open Set Function
open scoped RealInnerProductSpace

noncomputable section

namespace CircleDomainRigidity

theorem stereoInvFunAux_eq_centered (v w : RoundAmbient) :
    stereoInvFunAux v w =
      v + (4 / (‖w‖ ^ 2 + 4)) • (w - (2 : ℝ) • v) := by
  have hn : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  have h1 : (‖w‖ ^ 2 + 4)⁻¹ * 4 = 4 / (‖w‖ ^ 2 + 4) := by ring
  have h2 : (‖w‖ ^ 2 + 4)⁻¹ * (‖w‖ ^ 2 - 4) =
      1 - (4 / (‖w‖ ^ 2 + 4)) * 2 := by
    field_simp
    ring
  simp only [stereoInvFunAux, smul_add, smul_smul, h1, h2]
  module

theorem stereographic_scalar_bound {r : ℝ} (hr : 0 ≤ r) :
    4 / (r ^ 2 + 4) + 8 * r * (r + 2) / (r ^ 2 + 4) ^ 2 ≤
      16 / (r ^ 2 + 4) := by
  have hD : 0 < r ^ 2 + 4 := by positivity
  have hpoly : 4 * (r ^ 2 + 4) + 8 * r * (r + 2) ≤ 16 * (r ^ 2 + 4) := by
    nlinarith [sq_nonneg (r - 2)]
  calc
    _ = (4 * (r ^ 2 + 4) + 8 * r * (r + 2)) / (r ^ 2 + 4) ^ 2 := by
      field_simp
    _ ≤ (16 * (r ^ 2 + 4)) / (r ^ 2 + 4) ^ 2 :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hD)).2 hpoly
    _ = _ := by field_simp

theorem stereoInvFunAux_fderiv_apply (v w h : RoundAmbient) :
    (fderiv ℝ (stereoInvFunAux v) w) h =
      (4 / (‖w‖ ^ 2 + 4)) • h -
        (8 * inner ℝ w h / (‖w‖ ^ 2 + 4) ^ 2) • (w - (2 : ℝ) • v) := by
  let D : ℝ := ‖w‖ ^ 2 + 4
  have hD : D ≠ 0 := by dsimp [D] <;> positivity
  have hQ := (hasStrictFDerivAt_norm_sq w).hasFDerivAt.add_const (4 : ℝ)
  have ha : HasFDerivAt (fun z : RoundAmbient => 4 / (‖z‖ ^ 2 + 4))
      ((-8 / D ^ 2) • innerSL ℝ w) w := by
    convert ((hasFDerivAt_inv hD).comp w hQ).const_mul (4 : ℝ) using 1
    all_goals try with_reducible_and_instances rfl
    · funext z
      simp only [Function.comp_apply, div_eq_mul_inv]
    · ext z
      simp only [ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply,
        smul_eq_mul]
      dsimp [D]
      ring
  have hF := (hasFDerivAt_const v w).add
    (ha.smul ((hasFDerivAt_id w).sub_const ((2 : ℝ) • v)))
  have heq : stereoInvFunAux v =
      fun z : RoundAmbient => v + (4 / (‖z‖ ^ 2 + 4)) • (z - (2 : ℝ) • v) :=
    funext (stereoInvFunAux_eq_centered v)
  have hd := hF.fderiv
  change fderiv ℝ (fun z : RoundAmbient =>
    v + (4 / (‖z‖ ^ 2 + 4)) • (z - (2 : ℝ) • v)) w = _ at hd
  rw [heq, hd]
  simp only [zero_add, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
  dsimp [D]
  module

theorem norm_stereoInvFunAux_fderiv_apply (v w h : RoundAmbient) (hv : ‖v‖ ≤ 1) :
    ‖(fderiv ℝ (stereoInvFunAux v) w) h‖ ≤
      (16 / (‖w‖ ^ 2 + 4)) * ‖h‖ := by
  have hD : 0 < ‖w‖ ^ 2 + 4 := by positivity
  have hc : |8 * inner ℝ w h / (‖w‖ ^ 2 + 4) ^ 2| ≤
      8 * ‖w‖ * ‖h‖ / (‖w‖ ^ 2 + 4) ^ 2 := by
    calc
      _ = 8 * |inner ℝ w h| / (‖w‖ ^ 2 + 4) ^ 2 := by
        rw [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hD)]
        norm_num
      _ ≤ 8 * (‖w‖ * ‖h‖) / (‖w‖ ^ 2 + 4) ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm w h) (by norm_num))
          (sq_nonneg _)
      _ = _ := by ring
  have hvect : ‖w - (2 : ℝ) • v‖ ≤ ‖w‖ + 2 := by
    calc
      _ ≤ ‖w‖ + ‖(2 : ℝ) • v‖ := norm_sub_le _ _
      _ = ‖w‖ + 2 * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]; norm_num
      _ ≤ _ := by linarith
  have hfirst : ‖(4 / (‖w‖ ^ 2 + 4)) • h‖ = (4 / (‖w‖ ^ 2 + 4)) * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hD)]
  have hsecond : ‖(8 * inner ℝ w h / (‖w‖ ^ 2 + 4) ^ 2) • (w - (2 : ℝ) • v)‖ ≤
      (8 * ‖w‖ * ‖h‖ / (‖w‖ ^ 2 + 4) ^ 2) * (‖w‖ + 2) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hc hvect (norm_nonneg _) (by positivity)
  rw [stereoInvFunAux_fderiv_apply]
  calc
    _ ≤ ‖(4 / (‖w‖ ^ 2 + 4)) • h‖ +
        ‖(8 * inner ℝ w h / (‖w‖ ^ 2 + 4) ^ 2) • (w - (2 : ℝ) • v)‖ := norm_sub_le _ _
    _ ≤ (4 / (‖w‖ ^ 2 + 4)) * ‖h‖ +
        (8 * ‖w‖ * ‖h‖ / (‖w‖ ^ 2 + 4) ^ 2) * (‖w‖ + 2) :=
      add_le_add hfirst.le hsecond
    _ = (4 / (‖w‖ ^ 2 + 4) + 8 * ‖w‖ * (‖w‖ + 2) / (‖w‖ ^ 2 + 4) ^ 2) * ‖h‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (stereographic_scalar_bound (norm_nonneg w)) (norm_nonneg h)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereChartDerivativeDecay
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global inverse-quadratic derivative bound for the chosen finite sphere chart. -/

open Set Function

noncomputable section

namespace CircleDomainRigidity

theorem norm_stereoInvFunAux_fderiv (v w : RoundAmbient) (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (stereoInvFunAux v) w‖ ≤ 16 / (‖w‖ ^ 2 + 4) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  exact norm_stereoInvFunAux_fderiv_apply v w h hv

theorem norm_linearSphereChartMap (v : RoundAmbient) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) :
    ‖linearSphereChartMap v A‖ ≤ ‖A.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (linearSphereChartMap v A)
    (norm_nonneg A.toContinuousLinearMap)
  intro h
  exact A.toContinuousLinearMap.le_opNorm h

theorem linear_stereo_fderiv (v : RoundAmbient) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    fderiv ℝ (fun z : ℂ => stereoInvFunAux v (A z : RoundAmbient)) z =
      (fderiv ℝ (stereoInvFunAux v) (A z : RoundAmbient)).comp (linearSphereChartMap v A) := by
  have hA : HasFDerivAt (fun z : ℂ => (A z : RoundAmbient)) (linearSphereChartMap v A) z :=
    (ℝ ∙ v)ᗮ.subtypeL.hasFDerivAt.comp z A.hasFDerivAt
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) (stereoInvFunAux v) := contDiff_stereoInvFunAux
  have hD : DifferentiableAt ℝ (stereoInvFunAux v) (A z : RoundAmbient) :=
    (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
  have hFD : HasFDerivAt (stereoInvFunAux v)
      (fderiv ℝ (stereoInvFunAux v) (A z : RoundAmbient)) (A z : RoundAmbient) :=
    hD.hasFDerivAt
  have heq := (hFD.comp z hA).fderiv
  exact heq

theorem linear_stereo_derivative_decay
    (v : RoundAmbient) (hv : ‖v‖ ≤ 1) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    ‖fderiv ℝ (fun z : ℂ => stereoInvFunAux v (A z : RoundAmbient)) z‖ ≤
      (16 * ‖A.toContinuousLinearMap‖ * (1 + ‖A.symm.toContinuousLinearMap‖ ^ 2)) /
        (1 + ‖z‖ ^ 2) := by
  rw [linear_stereo_fderiv]
  calc
    _ ≤ ‖fderiv ℝ (stereoInvFunAux v) (A z : RoundAmbient)‖ *
        ‖linearSphereChartMap v A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (16 / (‖A z‖ ^ 2 + 4)) * ‖A.toContinuousLinearMap‖ :=
      mul_le_mul (norm_stereoInvFunAux_fderiv v _ hv) (norm_linearSphereChartMap v A)
        (norm_nonneg _) (by positivity)
    _ = 16 * ‖A.toContinuousLinearMap‖ / (‖A z‖ ^ 2 + 4) := by ring
    _ ≤ _ := linear_chart_inverse_quadratic_bound A z

theorem finite_sphere_chart_derivative_decay :
    ∃C : ℝ, 0 ≤ C ∧ ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2) := by
  classical
  have hlin (v : RoundAmbient) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (hv : ‖v‖ ≤ 1) :
      ∃C : ℝ, 0 ≤ C ∧ ∀z : ℂ,
        ‖fderiv ℝ (fun z : ℂ => stereoInvFunAux v (A z : RoundAmbient)) z‖ ≤
          C / (1 + ‖z‖ ^ 2) :=
    ⟨_, by positivity, linear_stereo_derivative_decay v hv A⟩
  simp only [roundSphereEquiv, onePointEquivSphereOfFinrankEq, Homeomorph.trans_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  apply hlin
  simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereChartSmallSets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative finite-chart Lipschitz constants on small convex sets. -/

open Set Metric
open scoped NNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem quadratic_weight_compare {x y : ℂ} (hxy : dist x y ≤ 1) :
    1 + ‖x‖ ^ 2 ≤ 3 * (1 + ‖y‖ ^ 2) := by
  have hnorm : ‖x‖ ≤ ‖y‖ + 1 := by
    have hn := norm_sub_norm_le x y
    rw [← dist_eq_norm] at hn
    linarith
  have hs := pow_le_pow_left₀ (norm_nonneg x) hnorm 2
  nlinarith [sq_nonneg (‖y‖ - 1)]

theorem decay_weight_compare {x y : ℂ} (hxy : dist x y ≤ 1) {C : ℝ} (hC : 0 ≤ C) :
    C / (1 + ‖y‖ ^ 2) ≤ 3 * C / (1 + ‖x‖ ^ 2) := by
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hy : 0 < 1 + ‖y‖ ^ 2 := by positivity
  apply (div_le_div_iff₀ hy hx).2
  nlinarith [mul_le_mul_of_nonneg_left (quadratic_weight_compare hxy) hC]

theorem finite_sphere_chart_lipschitz_on_small_convex
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {K : Set ℂ} (hK : Convex ℝ K) (hne : K.Nonempty)
    (hdiam : ∀x ∈ K, ∀y ∈ K, dist x y ≤ 1) :
    ∃L : ℝ≥0, LipschitzOnWith L ((↑) : ℂ → Sphere) K ∧
      ∀z ∈ K, (L : ℝ) ≤ 9 * C / (1 + ‖z‖ ^ 2) := by
  obtain ⟨c, hc⟩ := hne
  let L : ℝ≥0 := ⟨3 * C / (1 + ‖c‖ ^ 2), by positivity⟩
  let F : ℂ → RoundAmbient := fun z => roundSphereEquiv (z : Sphere)
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F := contDiff_roundSphere_finite_chart
  have hLip : LipschitzOnWith L F K :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun _ _ => (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt)
      (fun z hz => by
        change ‖fderiv ℝ F z‖₊ ≤ L
        exact_mod_cast (hderiv z).trans (decay_weight_compare (hdiam c hc z hz) hC)) hK
  refine ⟨L, ?_, ?_⟩
  · intro z hz w hw
    exact hLip hz hw
  · intro z hz
    change 3 * C / (1 + ‖c‖ ^ 2) ≤ _
    have h := decay_weight_compare (hdiam z hz c hc) (show 0 ≤ 3 * C by positivity)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SphericalWeightedLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spherical metric contributes its decay factor to weighted level
length. No pointwise finiteness of the nonnegative density is required. -/

open Set Function Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r6edb4b_1 : BorelSpace Sphere := ⟨rfl⟩
theorem finite_sphere_chart_weighted_length_le
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {S : Set ℂ} (hS : MeasurableSet S) (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y in ((↑) : ℂ → Sphere) '' S, g y ∂(μH[1] : Measure Sphere)) ≤
      ∫⁻z in S, ENNReal.ofReal (9 * C / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
        ∂(μH[1] : Measure ℂ) := by
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq ℂ
  let V : ℕ → Set ℂ := fun n => closedBall (c n) (1 / 2)
  have hV (n : ℕ) : MeasurableSet (V n) := isClosed_closedBall.measurableSet
  have hcover : ⋃n, V n = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨n, hn⟩ := hc.exists_dist_lt z (by norm_num : (0 : ℝ) < 1 / 2)
    exact mem_iUnion.mpr ⟨n, hn.le⟩
  have hsmall (n : ℕ) : ∀x ∈ V n, ∀y ∈ V n, dist x y ≤ 1 := by
    intro x hx y hy
    have h1 : dist x (c n) ≤ 1 / 2 := hx
    have h2 : dist (c n) y ≤ 1 / 2 := by
      change dist y (c n) ≤ 1 / 2 at hy
      simpa only [dist_comm] using hy
    exact (dist_triangle x (c n) y).trans (by linarith)
  choose K hK hweight using fun n => finite_sphere_chart_lipschitz_on_small_convex
    hC hderiv (convex_closedBall (c n) (1 / 2))
      (nonempty_closedBall.mpr (by norm_num)) (hsmall n)
  apply lintegral_hausdorff_image_le_of_partition OnePoint.continuous_coe.measurable
    (disjointed V) (MeasurableSet.disjointed hV) (disjoint_disjointed V)
    (by rw [iUnion_disjointed, hcover]) K
    (fun n => (hK n).mono (disjointed_subset V n))
    (fun z => ENNReal.ofReal (9 * C / (1 + ‖z‖ ^ 2)))
    (fun n z hz => ?_) hS g hg
  have hw := ENNReal.ofReal_le_ofReal (hweight n z (disjointed_subset V n hz))
  simpa using hw

theorem spherical_weighted_density_sq_finite
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻z : ℂ, (ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2)) * g (z : Sphere)) ^ 2) < ∞ := by
  rw [lintegral_sphericalArea _ (hg.pow_const 2)] at he
  apply lt_of_le_of_lt (lintegral_mono fun z => ?_) he
  rw [mul_pow, ← ENNReal.ofReal_pow (by positivity : 0 ≤ 1 / (1 + ‖z‖ ^ 2))]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (spherical_weight_sq_le_areaDensity z)) le_rfl

theorem spherical_weighted_length_le_chart
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (A : Set Sphere) (hA : MeasurableSet (((↑) : ℂ → Sphere) ⁻¹' A))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y in A, g y ∂(μH[1] : Measure Sphere)) ≤
      ∫⁻z in ((↑) : ℂ → Sphere) ⁻¹' A,
        ENNReal.ofReal (9 * C / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
          ∂(μH[1] : Measure ℂ) := by
  let : NullSingletonClass (μH[1] : Measure Sphere) :=
    Measure.nullSingletonClass_hausdorff Sphere (by norm_num)
  have hcover : A ⊆ ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' A) ∪
      {OnePoint.infty} := by
    intro y hy
    cases y using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe z => exact Or.inl ⟨z, hy, rfl⟩
  calc
    _ ≤ ∫⁻y in ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' A) ∪
        {OnePoint.infty}, g y ∂(μH[1] : Measure Sphere) := lintegral_mono_set hcover
    _ ≤ (∫⁻y in ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' A),
        g y ∂(μH[1] : Measure Sphere)) +
        ∫⁻y in ({OnePoint.infty} : Set Sphere), g y ∂(μH[1] : Measure Sphere) :=
      lintegral_union_le _ _ _
    _ = ∫⁻y in ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' A),
        g y ∂(μH[1] : Measure Sphere) := by simp
    _ ≤ _ := finite_sphere_chart_weighted_length_le hC hderiv hA g hg

theorem scaled_spherical_weighted_density_sq_finite
    (C : ℝ) (hC : 0 ≤ C) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻z : ℂ, (ENNReal.ofReal (C / (1 + ‖z‖ ^ 2)) * g (z : Sphere)) ^ 2) < ∞ := by
  have heq (z : ℂ) : ENNReal.ofReal (C / (1 + ‖z‖ ^ 2)) =
      ENNReal.ofReal C * ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2)) := by
    rw [← ENNReal.ofReal_mul hC]
    congr 1
    ring
  simp_rw [heq, mul_assoc, mul_pow]
  rw [lintegral_const_mul' _ _ (by finiteness)]
  apply ENNReal.mul_lt_top (by finiteness)
  simpa only [mul_pow] using spherical_weighted_density_sq_finite g hg he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleAlmostEverywhere
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-everywhere assertions on the unit circle from their real
representatives. No measurability of the asserted property is required. -/

open Set MeasureTheory

namespace CircleDomainRigidity

theorem ae_circle_of_ae_unit_interval (P : UnitAddCircle → Prop)
    (hP : ∀ᵐ(r : ℝ) ∂volume.restrict (Ico (0 : ℝ) 1), P (r : UnitAddCircle)) :
    ∀ᵐ(t : UnitAddCircle) ∂volume, P t := by
  rw [restrict_Ico_eq_restrict_Ioc] at hP
  have hnull : volume ({r : ℝ | ¬P (r : UnitAddCircle)} ∩ Ioc 0 1) = 0 := by
    simpa only [ae_iff, Measure.restrict_apply' measurableSet_Ioc] using hP
  have hcircle := volume_addCircle_image_eq_zero hnull
  rw [ae_iff]
  apply measure_mono_null _ hcircle
  intro t ht
  let r := AddCircle.equivIoc (1 : ℝ) 0 t
  have hr : (r.val : UnitAddCircle) = t := AddCircle.coe_equivIoc
  refine ⟨r.val, ⟨?_, by simpa using r.property⟩, hr⟩
  change ¬P (r.val : UnitAddCircle)
  change ¬P t at ht
  rwa [hr]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalWeightedCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite spherical weighted length of almost every circle-valued level,
from exactly the published scalar planar coarea input. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r6edb4b_2 : BorelSpace Sphere := ⟨rfl⟩
theorem ae_finite_spherical_weighted_levels
    (hcoarea : WeightedPlanarScalarCoarea)
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (hf2 : (∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) < ∞)
    (A : UnitAddCircle → Set Sphere)
    (hA : ∀t : UnitAddCircle, ((↑) : ℂ → Sphere) ⁻¹' A t =
      D ∩ {z | (f z : UnitAddCircle) = t})
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐt ∂volume, (∫⁻y in A t, g y ∂(μH[1] : Measure Sphere)) < ∞ := by
  let q : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (9 * C / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
  have hq : Measurable q := by
    apply Measurable.mul
    · apply Measurable.ennreal_ofReal
      apply Continuous.measurable
      exact continuous_const.div (continuous_const.add (continuous_norm.pow 2))
        (fun z => ne_of_gt (by positivity))
    · exact hg.comp OnePoint.continuous_coe.measurable
  have hq2 : (∫⁻z in D, q z ^ 2) < ∞ :=
    (lintegral_mono_set (subset_univ D)).trans_lt (by
      simpa only [Measure.restrict_univ] using
        scaled_spherical_weighted_density_sq_finite (9 * C) (by positivity) g hg henergy)
  have hfinite := (weighted_circle_coarea_extended_finite_energy hcoarea hD hf q hq hq2 hf2).2.2
  apply ae_circle_of_ae_unit_interval
  filter_upwards [hfinite] with t ht
  have hS : MeasurableSet (((↑) : ℂ → Sphere) ⁻¹' A (t : UnitAddCircle)) := by
    rw [hA, unitAddCircle_level_inter_eq_iUnion_integer_levels]
    exact MeasurableSet.iUnion fun k => measurableSet_scalar_level hD hf.continuousOn _
  apply lt_of_le_of_lt (spherical_weighted_length_le_chart hC hderiv _ hS g hg)
  simpa only [hA, weightedCircleLevelLength, q] using ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCoordinateCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply weighted coarea to the actual smooth physical representative
of a quotient coordinate. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r6edb4b_3 : BorelSpace Sphere := ⟨rfl⟩
theorem physicalRealCoordinate_ae_finite_weighted_levels
    {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData X Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → X)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    (Q : PhysicalRealCoordinate d π)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐt ∂volume,
      (∫⁻y in d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈
        circleBandGraph d.quotientDomain Q.quotient},
        g y ∂(μH[1] : Measure Sphere)) < ∞ := by
  let e := Complex.equivRealProdCLM
  let D := ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hDc : D = e ⁻¹' FiniteTransfer.realChartDomain d.physicalDomain := by
    ext z
    change (z : Sphere) ∈ d.physicalDomain ↔
      (e.symm (e z) : Sphere) ∈ d.physicalDomain
    rw [e.symm_apply_apply]
  have hreal : IsOpen (FiniteTransfer.realChartDomain d.physicalDomain) :=
    hG.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)
  have hs : ContDiffOn ℝ 1 Q.physical (FiniteTransfer.realChartDomain d.physicalDomain) :=
    Q.physical_smooth.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hf : ContDiffOn ℝ 1 (Q.physical ∘ e) D := by
    rw [hDc]
    exact hs.comp e.contDiff.contDiffOn (fun _ hx => hx)
  have hf2 : (∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ (Q.physical ∘ e) z‖ ^ 2)) < ∞ := by
    rw [hDc]
    exact complex_chart_differential_energy_finite hreal hs Q.physical_energy
  obtain ⟨C, hC, hderiv⟩ := finite_sphere_chart_derivative_decay
  apply ae_finite_spherical_weighted_levels hcoarea hC hderiv hD hf hf2
    (fun t => d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈
      circleBandGraph d.quotientDomain Q.quotient}) _ g hg henergy
  intro t
  ext z
  have hzU (hz : (z : Sphere) ∈ d.physicalDomain) : π z ∈ d.quotientDomain := by
    rw [he ⟨z, hz⟩]
    exact (d.domainEquiv ⟨z, hz⟩).property
  constructor
  · rintro ⟨hz, ht⟩
    refine ⟨hz, ?_⟩
    change (Q.physical (e z) : UnitAddCircle) = t
    rw [Q.pullback z hz]
    exact (circleBandGraph_on_open hU Q.quotient_continuous (hzU hz)).mp ht
  · rintro ⟨hz, ht⟩
    refine ⟨hz, (circleBandGraph_on_open hU Q.quotient_continuous (hzU hz)).mpr ?_⟩
    change (Q.physical (e z) : UnitAddCircle) = t at ht
    rwa [Q.pullback z hz] at ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite weighted regular levels for collar construction, using
Federer's coarea theorem and Sard's theorem. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem ennreal_mul_le_add_squares (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc
      a * b ≤ b * b := mul_le_mul' h le_rfl
      _ ≤ a ^ 2 + b ^ 2 := by rw [← pow_two]; exact le_add_self
  · calc
      a * b ≤ a * a := mul_le_mul' le_rfl h
      _ ≤ a ^ 2 + b ^ 2 := by rw [← pow_two]; exact le_self_add

theorem weighted_scalar_coarea_integral_lt_top
    {D : Set ℂ} {f : ℂ → ℝ} {q : ℂ → ℝ≥0∞}
    (hcoarea : WeightedScalarCoareaIdentity D f q) (hq : Measurable q)
    (hq2 : (∫⁻ z in D, q z ^ 2) < ∞)
    (hf2 : (∫⁻ z in D, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) < ∞) :
    (∫⁻ t, weightedScalarLevelLength D f q t) < ∞ := by
  rw [hcoarea.2]
  have hb : (∫⁻ z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖) ≤
      (∫⁻ z in D, q z ^ 2) + ∫⁻ z in D, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2 := by
    calc
      _ ≤ ∫⁻ z in D, (q z ^ 2 + (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) :=
        lintegral_mono fun z => ennreal_mul_le_add_squares _ _
      _ = _ := lintegral_add_left (hq.pow_const 2) _
  exact hb.trans_lt (ENNReal.add_lt_top.mpr ⟨hq2, hf2⟩)

theorem exists_weighted_regular_level
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hcompact : HasCompactSupport f) (q : ℂ → ℝ≥0∞) (hq : Measurable q)
    (hq2 : (∫⁻ z in D, q z ^ 2) < ∞)
    (hf2 : (∫⁻ z in D, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) < ∞)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, IsPlanarRegularValue f t ∧ weightedScalarLevelLength D f q t < ∞ := by
  have hc := hcoarea D hD f (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn q hq
  have hfin := weighted_scalar_coarea_integral_lt_top hc hq hq2 hf2
  have hbad : volume {t | weightedScalarLevelLength D f q t = ∞} = 0 := by
    have ha := ae_lt_top' hc.1 hfin.ne
    rw [ae_iff] at ha
    simpa only [not_lt, top_le_iff] using ha
  have hcrit := hsard f hf hcompact
  have hnull : volume ((f '' {z | fderiv ℝ f z = 0}) ∪
      {t | weightedScalarLevelLength D f q t = ∞}) = 0 := measure_union_null hcrit hbad
  have hpositive : 0 < volume (Ioo a b \ ((f '' {z | fderiv ℝ f z = 0}) ∪
      {t | weightedScalarLevelLength D f q t = ∞})) := by
    rw [measure_sdiff_null hnull, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  obtain ⟨t, ht, hgood⟩ := nonempty_of_measure_ne_zero hpositive.ne'
  refine ⟨t, ht, ?_, ?_⟩
  · intro z hz hzero
    exact hgood (Or.inl ⟨z, hzero, hz⟩)
  · exact lt_top_iff_ne_top.mpr (fun ht => hgood (Or.inr ht))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteWeightedCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compact cutoffs have finite differential energy, so weighted
coarea and Sard choose finite-cost regular contours without an added
energy hypothesis on the cutoff. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem smooth_compact_differential_energy {f : ℂ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hcompact : HasCompactSupport f) :
    (∫⁻ z, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) < ∞ := by
  have hd : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := (↑(⊤ : ℕ∞))) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous
  have hcont : Continuous (fun z => ‖fderiv ℝ f z‖ ^ 2) := hd.norm.pow 2
  have hsupp : HasCompactSupport (fun z => ‖fderiv ℝ f z‖ ^ 2) := by
    apply hcompact.mono'
    intro z hz
    by_contra hzf
    have hd := fderiv_of_notMem_tsupport ℝ hzf
    apply hz
    change ‖fderiv ℝ f z‖ ^ 2 = 0
    rw [hd]
    simp
  have hint : Integrable (fun z => ‖fderiv ℝ f z‖ ^ 2) :=
    hcont.integrable_of_hasCompactSupport hsupp
  have hfin := (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun z => sq_nonneg ‖fderiv ℝ f z‖))).mp hint.hasFiniteIntegral
  simpa only [ENNReal.ofReal_pow (norm_nonneg _)] using hfin

theorem exists_finite_weighted_regular_superlevel
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    {A O : Set ℂ} (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O)
    (q : ℂ → ℝ≥0∞) (hq : Measurable q) (hq2 : (∫⁻ z, q z ^ 2) < ∞) :
    ∃ (f : ℂ → ℝ) (t : ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ (∀ z, f z ∈ Icc 0 1) ∧ t ∈ Ioo 0 1 ∧
      IsOpen {z | t < f z} ∧ A ⊆ {z | t < f z} ∧
      IsCompact (closure {z | t < f z}) ∧ closure {z | t < f z} ⊆ O ∧
      IsCompact {z | f z = t} ∧ IsPlanarRegularValue f t ∧
      frontier {z | t < f z} ⊆ {z | f z = t} ∧
      weightedScalarLevelLength univ f q t < ∞ := by
  obtain ⟨f, hf, hcompact, hsupp, hrange, hone⟩ := exists_smooth_planar_cutoff hA hO hAO
  obtain ⟨t, ht, hregular, hfinite⟩ := exists_weighted_regular_level hcoarea hsard isOpen_univ
    hf hcompact q hq (by simpa only [Measure.restrict_univ] using hq2)
    (by simpa only [Measure.restrict_univ] using smooth_compact_differential_energy hf hcompact)
    zero_lt_one
  have hclosure := closure_superlevel_subset_tsupport (f := f) ht.1
  refine ⟨f, t, hf, hcompact, hsupp, hrange, ht, isOpen_lt continuous_const hf.continuous,
    ?_, hcompact.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hsupp,
    isCompact_nonzero_level hf.continuous hcompact ht.1.ne', hregular, ?_, hfinite⟩
  · intro z hz
    change t < f z
    rw [hone.self_of_nhdsSet z hz]
    exact ht.2
  · intro z hz
    exact (frontier_lt_subset_eq continuous_const hf.continuous hz).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedSmoothContours
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth obstacle-isolating contours whose actual Hausdorff arclength
integral against the prescribed density is finite. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Manifold

noncomputable section

namespace CircleDomainRigidity

theorem exists_weighted_regular_isolating_obstacle
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V)
    (q : ℂ → ℝ≥0∞) (hq : Measurable q) (hq2 : (∫⁻ z, q z ^ 2) < ∞) :
    ∃ (f : ℂ → ℝ) (t : ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ t ∈ Ioo 0 1 ∧
      IsOpen {z | t < f z} ∧ A ⊆ {z | t < f z} ∧
      IsCompact (closure {z | t < f z}) ∧ closure {z | t < f z} ⊆ V ∧
      closure {z | t < f z} ∩ F = A ∧ IsCompact {z | f z = t} ∧
      IsPlanarRegularValue f t ∧ Disjoint {z | f z = t} F ∧
      weightedScalarLevelLength univ f q t < ∞ := by
  let O := V ∩ (F \ A)ᶜ
  have hO : IsOpen O := hV.inter hFA.isOpen_compl
  have hAO : A ⊆ O := fun z hz => ⟨hAV hz, fun hbad => hbad.2 hz⟩
  obtain ⟨f, t, hf, _, hsupp, _, ht, hopen, hAU, hcompact, hclO,
    hlevel, hregular, _, hfinite⟩ :=
    exists_finite_weighted_regular_superlevel hcoarea hsard hA hO hAO q hq hq2
  have hclF : closure {z | t < f z} ∩ F = A := by
    apply Subset.antisymm
    · intro z hz
      by_contra hzA
      exact (hclO hz.1).2 ⟨hz.2, hzA⟩
    · intro z hz
      exact ⟨subset_closure (hAU hz), hAF hz⟩
  have hdisj : Disjoint {z | f z = t} F := by
    apply disjoint_left.mpr
    intro z hz hzF
    have hzSupp : z ∈ tsupport f := subset_tsupport f (by
      change f z ≠ 0
      rw [hz]
      exact ht.1.ne')
    have hzA : z ∈ A := by
      by_contra hnot
      exact (hsupp hzSupp).2 ⟨hzF, hnot⟩
    have hh := hAU hzA
    change t < f z at hh
    rw [hz] at hh
    exact hh.false
  exact ⟨f, t, hf, ht, hopen, hAU, hcompact, fun z hz => (hclO hz).1,
    hclF, hlevel, hregular, hdisj, hfinite⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedJordanCovers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Jordan fillings of finite-weight regular levels. The selected
frontiers retain the original regular-level equation and weighted bound. -/

open Set Filter Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_finite_weighted_jordan_cover
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V)
    (hVconn : IsPreconnected Vᶜ) (hVunbounded : ¬ Bornology.IsBounded Vᶜ)
    (q : ℂ → ℝ≥0∞) (hq : Measurable q) (hq2 : (∫⁻z, q z ^ 2) < ∞) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ IsPlanarRegularValue f t ∧
      {z | f z = t} ⊆ V ∧ Disjoint {z | f z = t} F ∧
      (∫⁻z in {z | f z = t}, q z ∂(μH[1] : Measure ℂ)) < ∞ ∧
      s.Finite ∧ A ⊆ ⋃ i ∈ s, jordanInterior (H i) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆ V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) (↑(⊤ : ℕ∞)) (γ i) ∧
        Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        Disjoint (frontier (jordanInterior (H i))) F ∧
        frontier (jordanInterior (H i)) ⊆ {z | f z = t} := by
  classical
  obtain ⟨f, t, hf, ht, hU, hAU, hUc, hUV, _, hlevel, hregular, havoid, hcost⟩ :=
    exists_weighted_regular_isolating_obstacle hcoarea hsard hA hAF hFA hV hAV q hq hq2
  obtain ⟨hfinite, γ, hγ, hγdisj, hγcover⟩ :=
    compact_regular_level_circle_contours hf hregular hlevel
  let : Finite (ConnectedComponents {z // f z = t}) := hfinite
  choose H hH using fun i => hschoenflies (γ i) (hγ i).2.continuous (hγ i).2.injective
  have hfront (i) : frontier (jordanInterior (H i)) = range (γ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (γ i) (hH i)
  have hUd : frontier {z | t < f z} = {z | f z = t} :=
    frontier_superlevel_eq_regular_level hf.continuous hregular
  have hfrontlevel (i) : frontier (jordanInterior (H i)) ⊆ {z | f z = t} := by
    rw [hfront, ← hγcover]
    exact subset_iUnion (fun i => range (γ i)) i
  have hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    simpa only [hfront] using hγdisj hij
  obtain ⟨s, hs, hsd, hdom, _⟩ := exists_outer_jordanInteriors H hpair
  let : Finite s := hs.to_subtype
  have hsd' : Pairwise (Disjoint on fun i : s => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hsd i.property j.property (fun h => hij (Subtype.ext h))
  have hcover : frontier {z | t < f z} ⊆ ⋃ i : s, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hUd, ← hγcover] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hi' : z ∈ closure (jordanInterior (H i)) := by
      apply frontier_subset_closure
      simpa only [hfront] using hi
    obtain ⟨j, hj, hij⟩ := hdom i
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hij hi'⟩
  have hUcover : {z | t < f z} ⊆ ⋃ i : s, jordanInterior (H i) :=
    open_subset_finite_jordanInteriors_of_frontier_subset (fun i : s => H i) hsd'
      hU (hUc.isBounded.subset subset_closure) hcover
      (fun i => hUd.symm ▸ hfrontlevel i)
  have hlevelV : {z | f z = t} ⊆ V := fun z hz =>
    hUV (frontier_subset_closure (hUd.symm ▸ hz))
  have hfiniteCost : (∫⁻z in {z | f z = t}, q z ∂(μH[1] : Measure ℂ)) < ∞ := by
    simpa only [weightedScalarLevelLength, univ_inter] using hcost
  refine ⟨f, t, γ, H, s, hf, hregular, hlevelV, havoid, hfiniteCost, hs, ?_, hsd, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hUcover (hAU hz))
    exact mem_iUnion₂.mpr ⟨i, i.property, hi⟩
  · intro i _
    apply closed_jordanInterior_subset_of_unbounded_connected_compl (H i) hVconn hVunbounded
    intro z hz
    apply hUV
    apply frontier_subset_closure
    rw [hUd]
    exact hfrontlevel i hz
  · intro i _
    exact ⟨(hγ i).1, (hγ i).2, hfront i, havoid.mono_left (hfrontlevel i), hfrontlevel i⟩


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedPhysicalCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-cost smooth physical collars of an actual collapsed component.
The regular level containing the chosen boundary is retained explicitly. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_weighted_small_physical_disk
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hVconn : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ F)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ) (f : ℂ → ℝ) (t : ℝ),
      {z : ℂ | π (z : Sphere) = x} ⊆ jordanInterior H ∧
      closure (jordanInterior H) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V ∧
      ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) (↑(⊤ : ℕ∞)) γ ∧ Topology.IsEmbedding γ ∧
      frontier (jordanInterior H) = range γ ∧
      frontier (jordanInterior H) ⊆ {z | f z = t} ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ IsPlanarRegularValue f t ∧
      {z | f z = t} ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V ∧
      (∀ z, f z = t → (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F) ∧
      (∫⁻z in {z | f z = t}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
  classical
  obtain ⟨hphysical, hunbounded⟩ :=
    physical_exterior_connected_unbounded_of_component_collapse G π hπ hclosed hsurj hr
      hV hVconn hinfty
  obtain ⟨A, hAc, hxA, hAF, hAV, hFA⟩ :=
    exists_compact_piece_of_singleton_component hF hx hcomponent hV hxV
  let q : ℂ → X := fun z => π (z : Sphere)
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hAp : IsCompact (q ⁻¹' A) := by
    apply isCompact_finite_preimage (hAc.isClosed.preimage hπ)
    exact fun h => hinfty (subset_closure (hAV h))
  have hFp : IsClosed ((q ⁻¹' F) \ (q ⁻¹' A)) := by
    simpa only [preimage_sdiff] using hFA.preimage hq
  obtain ⟨f, t, γ, H, s, hf, hreg, hlevelV, havoid, hcost,
    _, hcov, hd, hinside, hcurves⟩ :=
    exists_finite_weighted_jordan_cover hcoarea hsard hschoenflies hAp
      (preimage_mono hAF) hFp (hV.preimage hq) (preimage_mono hAV)
      hphysical hunbounded g hg hg2
  have hfiber : IsConnected {z : ℂ | π (z : Sphere) = x} := by
    apply isConnected_finite_fiber π (connected_fibers_of_component_collapse G π hsurj hr)
    intro heq
    exact hinfty (subset_closure (heq.symm ▸ hxV))
  have hpair : Pairwise (Disjoint on fun i : s => jordanInterior (H i)) := by
    intro i j hij
    exact (hd i.property j.property (fun h => hij (Subtype.ext h))).mono
      subset_closure subset_closure
  have hcover : {z : ℂ | π (z : Sphere) = x} ⊆ ⋃ i : s, jordanInterior (H i) := by
    intro z hz
    have hzA : z ∈ q ⁻¹' A := by
      change π (z : Sphere) ∈ A
      rwa [hz]
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov hzA)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  obtain ⟨i, hi⟩ := exists_member_containing_connected_set hfiber
    (fun i : s => jordanInterior (H i)) (fun i => jordanInterior_isOpen (H i)) hpair hcover
  obtain ⟨hγ, hemb, hfront, _, hfrontlevel⟩ := hcurves i i.property
  refine ⟨H i, γ i, f, t, hi, hinside i i.property, hγ, hemb, hfront,
    hfrontlevel, hf, hreg, hlevelV, ?_, hcost⟩
  intro z hz
  have hnot : π (z : Sphere) ∉ F := fun h => disjoint_left.mp havoid hz h
  refine ⟨?_, hnot⟩
  by_contra h
  exact hnot (hbad _ h)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted collars in the physical plane and their actual open quotient
neighborhoods. Compact containment survives projection. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

namespace WeightedCollar

variable {G : Set Sphere} {π : Sphere → Sphere} {B : Set Sphere}
  {p : Sphere} {g : ℂ → ℝ≥0∞} (D : WeightedCollar G π B p g)

theorem isOpen_region (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    IsOpen D.region :=
  isOpen_image_jordanInterior_of_component_collapse G π hπ hclosed hsurj hr D.disk
    (fun z hz => (D.level_good z (D.frontier_level hz)).1)

theorem point_mem_region (hsurj : Surjective π) (hp : p ≠ π OnePoint.infty) :
    p ∈ D.region := by
  obtain ⟨x, hx⟩ := hsurj p
  cases x using OnePoint.rec with
  | infty => exact (hp hx.symm).elim
  | coe z => exact ⟨z, ⟨z, D.fiber_inside hx, rfl⟩, hx⟩

theorem closure_region_subset_image (hπ : Continuous π) :
    closure D.region ⊆ π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior D.disk)) := by
  apply closure_minimal (image_mono (image_mono subset_closure))
  exact (((isCompact_closure_jordanInterior D.disk).image OnePoint.continuous_coe).image hπ).isClosed

theorem closure_region_subset {V : Set Sphere} (hπ : Continuous π)
    (hV : closure (jordanInterior D.disk) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V) :
    closure D.region ⊆ V := by
  intro x hx
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := D.closure_region_subset_image hπ hx
  exact hV hz

theorem frontier_region_subset (hπ : Continuous π) (hregion : IsOpen D.region) :
    frontier D.region ⊆ π '' (((↑) : ℂ → Sphere) '' {z | D.function z = D.level}) := by
  intro x hx
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := D.closure_region_subset_image hπ (frontier_subset_closure hx)
  have hznot : z ∉ jordanInterior D.disk := by
    intro h
    rw [hregion.frontier_eq] at hx
    exact hx.2 ⟨z, ⟨z, h, rfl⟩, rfl⟩
  have hzfront : z ∈ frontier (jordanInterior D.disk) := by
    rw [(jordanInterior_isOpen D.disk).frontier_eq]
    exact ⟨hz, hznot⟩
  exact ⟨z, ⟨z, D.frontier_level hzfront, rfl⟩, rfl⟩

end WeightedCollar

theorem exists_weighted_collar_in_neighborhood
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    {O : Set Sphere} (hO : IsOpen O) (hpO : p ∈ O)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ D : WeightedCollar G π B p g,
      closure D.region ⊆ O ∧ {z | D.function z = D.level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' O := by
  obtain ⟨V, hV, hpV, hVO, hVc⟩ := exists_sphere_neighborhood_connected_compl
    (hO.inter isClosed_singleton.isOpen_compl) ⟨hpO, hp⟩
  have hcomponent : connectedComponentIn B p = {p} :=
    (hTD _ (connectedComponentIn_subset B p) isPreconnected_connectedComponentIn).eq_singleton_of_mem
      (mem_connectedComponentIn hpB)
  obtain ⟨H, γ, f, t, hfiber, hinside, hsmooth, hemb, hfront, hfrontlevel,
    hf, hreg, hlevelV, hgood, hcost⟩ :=
    exists_weighted_small_physical_disk hcoarea hsard hsch G π hπ hclosed hsurj hr
      hB hpB hcomponent hV hpV hVc (fun h => (hVO h).2 rfl) hbad g hg hg2
  let D : WeightedCollar G π B p g :=
    ⟨H, γ, f, t, hfiber, hsmooth, hemb, hfront, hfrontlevel, hf, hreg, hgood, hcost⟩
  refine ⟨D, ?_, ?_⟩
  · exact (D.closure_region_subset hπ hinside).trans (fun _ h => (hVO (subset_closure h)).1)
  · exact hlevelV.trans (fun _ h => (hVO (subset_closure h)).1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NestedWeightedCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strictly nested actual weighted collars, chosen inside any prescribed
sequence of quotient neighborhoods. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_nested_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    (O : ℕ → Set Sphere) (hO : ∀n, IsOpen (O n)) (hpO : ∀n, p ∈ O n)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ D : ℕ → WeightedCollar G π B p g,
      (∀n, closure (D n).region ⊆ O n) ∧
      (∀n, closure (D (n+1)).region ⊆ (D n).region) ∧
      (∀n, {z | (D n).function z = (D n).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' O n) ∧
      (∀n, {z | (D (n+1)).function z = (D (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D n).region) := by
  classical
  obtain ⟨D0, hD0, hL0⟩ := exists_weighted_collar_in_neighborhood hcoarea hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad hpB hp (hO 0) (hpO 0) g hg hg2
  have hstep : ∀ (n : ℕ) (D : WeightedCollar G π B p g),
      ∃ E : WeightedCollar G π B p g,
        closure E.region ⊆ D.region ∩ O (n+1) ∧
        {z | E.function z = E.level} ⊆
          (fun z : ℂ => π (z : Sphere)) ⁻¹' (D.region ∩ O (n+1)) := by
    intro n D
    exact exists_weighted_collar_in_neighborhood hcoarea hsard hsch
      G π hπ hclosed hsurj hr hB hTD hbad hpB hp
      ((D.isOpen_region hπ hclosed hsurj hr).inter (hO (n+1)))
      ⟨D.point_mem_region hsurj hp, hpO (n+1)⟩ g hg hg2
  choose step hstep using hstep
  let D : ℕ → WeightedCollar G π B p g := Nat.rec D0 step
  have hs (n : ℕ) : D (n+1) = step n (D n) := rfl
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact hD0
    | succ n => exact fun z hz => ((hstep n (D n)).1 hz).2
  · intro n z hz
    exact ((hstep n (D n)).1 hz).1
  · intro n
    cases n with
    | zero => exact hL0
    | succ n => exact fun z hz => ((hstep n (D n)).2 hz).2
  · intro n z hz
    exact ((hstep n (D n)).2 hz).1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ShrinkingWeightedCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chosen collar closures and all their joining levels shrink to the
actual quotient point. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem exists_shrinking_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    {W : Set Sphere} (hW : IsOpen W) (hpW : p ∈ W)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ D : ℕ → WeightedCollar G π B p g,
      closure (D 0).region ⊆ W ∧
      (∀n, closure (D (n+1)).region ⊆ (D n).region) ∧
      (∀n, {z | (D (n+1)).function z = (D (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D n).region) ∧
      (∀V ∈ 𝓝 p, ∃N : ℕ, ∀n ≥ N, closure (D n).region ⊆ V ∧
        {z | (D n).function z = (D n).level} ⊆
          (fun z : ℂ => π (z : Sphere)) ⁻¹' V) := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hrpos (n : ℕ) : 0 < r n := by dsimp [r] <;> positivity
  have hrzero : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let O : ℕ → Set Sphere := fun n => W ∩ ball p (r n)
  obtain ⟨D, hD, hnested, hlevel, hlevelNested⟩ := exists_nested_weighted_collars
    hcoarea hsard hsch G π hπ hclosed hsurj hr hB hTD hbad hpB hp O
    (fun _ => hW.inter isOpen_ball) (fun n => ⟨hpW, mem_ball_self (hrpos n)⟩) g hg hg2
  refine ⟨D, (hD 0).trans inter_subset_left, hnested, hlevelNested, ?_⟩
  intro V hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrzero.eventually (gt_mem_nhds hδ))
  refine ⟨N, ?_⟩
  intro n hn
  have hsub : O n ⊆ V := inter_subset_right.trans ((ball_subset_ball (hN n hn).le).trans hball)
  exact ⟨(hD n).trans hsub, (hlevel n).trans (preimage_mono hsub)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarArcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual weighted collars supply the local short joining arcs
required for splicing. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

namespace WeightedCollar

theorem frontier_region_subset_quotient
    (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} {p : Sphere} {g : ℂ → ℝ≥0∞}
    (D : WeightedCollar d.physicalDomain π B p g) (hD : IsOpen D.region) :
    frontier D.region ⊆ d.quotientDomain := by
  intro x hx
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := D.frontier_region_subset hπ hD hx
  rw [← he ⟨(z : Sphere), (D.level_good z hz).1⟩]
  exact (d.domainEquiv _).property

end WeightedCollar
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PositiveCountableWeights
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive weights of total mass at most one on the prescribed countable
point and tuple-type sets. Their squares have the same upper bound. -/

open Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem sum_slotWeight_succ : (∑' k, slotWeight (k + 1)) = 1 := by
  simp_rw [Nat.add_comm _ 1, slotWeight_add]
  rw [ENNReal.tsum_mul_left, tsum_slotWeight]
  simpa only [slotWeight, pow_one] using
    (ENNReal.inv_mul_cancel (a := 2) (by norm_num) (by norm_num))

theorem exists_positive_summable_weights (D : Type*) [Countable D] :
    ∃ c : D → ℝ≥0∞, (∀ s, 0 < c s) ∧ (∑' s, c s) ≤ 1 := by
  classical
  let := Encodable.ofCountable D
  refine ⟨fun s => slotWeight (Encodable.encode s + 1), fun s => slotWeight_pos _, ?_⟩
  exact (ENNReal.tsum_comp_le_tsum_of_injective Encodable.encode_injective
    (fun k => slotWeight (k + 1))).trans_eq sum_slotWeight_succ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BarrierTrialMetric
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Failure of a small actual compatible barrier gives a uniform lower
bound on every admissible coding metric. The excluded tuples and positive
perturbations are constructed from that metric. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem barrierConstructionConstant_ne_top (C : ℝ) : barrierConstructionConstant C ≠ ∞ := by
  apply ne_of_lt
  exact max_lt_iff.mpr ⟨ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top, by norm_num⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletionUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite uniformization of the actual terminal-disk complement

The complementary components are exactly the closed physical terminal
caps. In particular they are finite and nondegenerate. The published
finite circle theorem therefore applies after compact metric
uniformization; the resulting map is conformal on the retained core.
-/

open Set Function Filter
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isConnected_openCompletedRegion {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    IsConnected (openCompletedRegion H) := by
  let S : Set ℂ := (⋃ i, closure (jordanInterior (H i)))ᶜ
  have hS : IsPreconnected S := isPreconnected_exterior_finite_jordanInteriors H hdisj
  have hinf : (∞ : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' S) := by
    have hmem : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ∈ S := by
      rw [coclosedCompact_eq_cocompact]
      exact (isCompact_iUnion fun i => isCompact_closure_jordanInterior (H i)).compl_mem_cocompact
    exact mem_closure_of_tendsto OnePoint.tendsto_coe_infty
      (hmem.mono fun z hz => ⟨z, hz, rfl⟩)
  have hsub : ((↑) : ℂ → Sphere) '' S ⊆ openCompletedRegion H := by
    rintro _ ⟨z, hz, rfl⟩ hb
    obtain ⟨i, x, hx, heq⟩ := mem_iUnion.mp hb
    have hxz : x = z := OnePoint.coe_injective heq
    exact hz (mem_iUnion.mpr ⟨i, hxz ▸ hx⟩)
  have hupper : openCompletedRegion H ⊆ closure (((↑) : ℂ → Sphere) '' S) := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
      apply subset_closure
      refine ⟨z, ?_, rfl⟩
      intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hp (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)
  refine ⟨⟨∞, ?_⟩, (hS.image _ OnePoint.continuous_coe.continuousOn).subset_closure hsub hupper⟩
  intro hb
  obtain ⟨i, z, _, heq⟩ := mem_iUnion.mp hb
  exact OnePoint.coe_ne_infty z heq

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ImageCoreBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Images of compact retained cores

A conformal injection on an open neighborhood carries a compact core's
interior and boundary to the interior and boundary of its image. Regular
closed cores remain regular closed. These facts use local openness, not a
boundary extension of the conformal map.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem frontier_image_of_continuous_open
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hc : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S))
    (hG : IsOpen G) (hi : InjOn f G) (hK : IsCompact K) (hKG : K ⊆ G) :
    frontier (f '' K) = f '' frontier K := by
  have hfc : IsClosed (f '' K) := (hK.image_of_continuousOn (hc.mono hKG)).isClosed
  rw [frontier, hfc.closure_eq, interior_image_of_continuous_open hc ho hG hi hKG,
    frontier, hK.isClosed.closure_eq]
  exact ((hi.mono hKG).image_sdiff_subset interior_subset).symm

theorem closure_image_interior_of_continuous
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hf : ContinuousOn f G) (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K) :
    closure (f '' interior K) = f '' K := by
  have hc : ContinuousOn f K := hf.mono hKG
  apply Subset.antisymm
  · exact closure_minimal (image_mono interior_subset) (hK.image_of_continuousOn hc).isClosed
  · have hci : ContinuousOn f (closure (interior K)) := hregular.symm ▸ hc
    simpa only [hregular] using hci.image_closure

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanCoreRecognition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recognizing the exterior bounded by a finite Jordan family

A regular closed sphere set with connected interior containing infinity
and with finitely many disjoint Jordan boundary curves is exactly their
common closed exterior. The filled disks are disjoint. This supplies the
image-side identification of retained cores without assuming orientation
or a boundary extension theorem.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem unbounded_preconnected_subset_jordan_exterior
    {T : Set ℂ} (hT : IsPreconnected T) (hunbounded : ¬ Bornology.IsBounded T)
    (H : ℂ ≃ₜ ℂ) (havoid : Disjoint T (frontier (jordanInterior H))) :
    T ⊆ (closure (jordanInterior H))ᶜ := by
  have hsplit : T ⊆ jordanInterior H ∨ T ⊆ (closure (jordanInterior H))ᶜ := by
    apply hT.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
    · exact Set.disjoint_left.mpr fun _ hx hy => hy (subset_closure hx)
    · intro z hz
      by_cases hi : z ∈ jordanInterior H
      · exact Or.inl hi
      · right
        intro hc
        exact Set.disjoint_left.mp havoid hz (by
          rw [(jordanInterior_isOpen H).frontier_eq]
          exact ⟨hc, hi⟩)
  rcases hsplit with h | h
  · exact (hunbounded ((isCompact_closure_jordanInterior H).isBounded.subset
      (h.trans subset_closure))).elim
  · exact h

theorem sphere_jordan_core_recognition
    {I : Type*} [Finite I] {A : Set Sphere}
    (hregular : closure (interior A) = A)
    (hconn : IsPreconnected (interior A)) (hinf : OnePoint.infty ∈ interior A)
    (H : I → ℂ ≃ₜ ℂ)
    (hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))))
    (hfront : frontier A = ⋃ i, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) :
    Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      Aᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i) := by
  have hAclosed : IsClosed A := hregular ▸ isClosed_closure
  let T : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' interior A
  have hT := finite_part_connected_unbounded hconn (by
    simpa only [interior_interior] using hinf)
  have hfrontA (i : I) : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) ⊆ frontier A := by
    rw [hfront]
    exact subset_iUnion (fun j : I => ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H j))) i
  have hTout (i : I) : T ⊆ (closure (jordanInterior (H i)))ᶜ := by
    apply unbounded_preconnected_subset_jordan_exterior hT.1 hT.2 (H i)
    apply Set.disjoint_left.mpr
    intro z hz hzfront
    have hzf := hfrontA i (mem_image_of_mem _ hzfront)
    exact hzf.2 hz
  have hAout (i : I) : A ⊆ (((↑) : ℂ → Sphere) '' jordanInterior (H i))ᶜ := by
    rw [← hregular]
    apply closure_minimal ?_ (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H i))).isClosed_compl
    intro p hp hinside
    obtain ⟨z, hz, rfl⟩ := hinside
    exact hTout i hp (subset_closure hz)
  have hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) := by
    intro i j hij
    rcases disjoint_or_nested_jordanInteriors (H i) (H j) (hpair hij) with hd | hn | hn
    · exact hd
    · obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H i)).nonempty
      have hzA : (z : Sphere) ∈ A := by
        simpa only [hAclosed.closure_eq] using frontier_subset_closure
          (hfrontA i (mem_image_of_mem _ hz))
      exact (hAout j hzA (mem_image_of_mem _ (hn (frontier_subset_closure hz)))).elim
    · obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H j)).nonempty
      have hzA : (z : Sphere) ∈ A := by
        simpa only [hAclosed.closure_eq] using frontier_subset_closure
          (hfrontA j (mem_image_of_mem _ hz))
      exact (hAout i hzA (mem_image_of_mem _ (hn (frontier_subset_closure hz)))).elim
  let U : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' Aᶜ
  have hUo : IsOpen U := hAclosed.isOpen_compl.preimage OnePoint.continuous_coe
  have hUb : Bornology.IsBounded U := by
    have hc := ((OnePoint.isOpen_iff_of_mem hinf).mp isOpen_interior).2
    apply hc.isBounded.subset
    intro z hz hzint
    exact hz (interior_subset hzint)
  have hprefront : frontier U = ((↑) : ℂ → Sphere) ⁻¹' frontier A := by
    change frontier (((↑) : ℂ → Sphere) ⁻¹' Aᶜ) = _
    rw [← OnePoint.isOpenEmbedding_coe.isOpenMap.preimage_frontier_eq_frontier_preimage
      OnePoint.continuous_coe, frontier_compl]
  have hcover : frontier U ⊆ ⋃ i, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hprefront] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hfront ▸ hz)
    have hzi : z ∈ frontier (jordanInterior (H i)) := OnePoint.coe_injective.mem_set_image.mp hi
    exact mem_iUnion.mpr ⟨i, frontier_subset_closure hzi⟩
  have hselected (i : I) : frontier (jordanInterior (H i)) ⊆ frontier U := by
    intro z hz
    rw [hprefront]
    exact hfrontA i (mem_image_of_mem _ hz)
  have hUfill := open_subset_finite_jordanInteriors_of_frontier_subset H hd hUo hUb hcover hselected
  refine ⟨hd, Subset.antisymm ?_ ?_⟩
  · intro p hp
    cases p using OnePoint.rec with
    | infty => exact (hp (interior_subset hinf)).elim
    | coe z =>
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hUfill hp)
      exact mem_iUnion.mpr ⟨i, z, hi, rfl⟩
  · intro p hp hpA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hAout i hpA hi

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ImageCoreJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual Jordan disks bounded by an image core

Schoenflies is applied only to the images of the given boundary circles.
The image-core theorem then proves that their filled sides are pairwise
disjoint and exhaust the complement of the image core.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_jordan_image_core_of_continuous_open
    (hschoenflies : PlanarSchoenflies)
    {f : Sphere → Sphere} {G K : Set Sphere}
    (hG : IsOpen G) (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hK : IsCompact K) (hKG : K ⊆ G)
    (hregular : closure (interior K) = K)
    (hconn : IsPreconnected (interior K)) (hinf : OnePoint.infty ∈ interior K)
    (hfix : f OnePoint.infty = OnePoint.infty)
    {I : Type*} [Finite I] (γ : I → Circle → ℂ)
    (hγ : ∀ i, Continuous (γ i)) (hγinj : ∀ i, Injective (γ i))
    (hγpair : Pairwise (fun i j => Disjoint (range (γ i)) (range (γ j))))
    (hfront : frontier K = ⋃ i, ((↑) : ℂ → Sphere) '' range (γ i)) :
    ∃ H : I → ℂ ≃ₜ ℂ,
      (∀ i, frontier (jordanInterior (H i)) =
        range (fun t => finiteCoord (f ((γ i t : ℂ) : Sphere)))) ∧
      Pairwise (Disjoint on fun i => closure (jordanInterior (H i))) ∧
      (f '' K)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (H i) := by
  have hγK (i : I) (t : Circle) : ((γ i t : ℂ) : Sphere) ∈ K := by
    apply hK.isClosed.closure_eq ▸ frontier_subset_closure
    rw [hfront]
    exact mem_iUnion.mpr ⟨i, γ i t, ⟨t, rfl⟩, rfl⟩
  have hinfG : OnePoint.infty ∈ G := hKG (interior_subset hinf)
  have hfinite (i : I) (t : Circle) : f ((γ i t : ℂ) : Sphere) ≠ OnePoint.infty :=
    finite_image_of_fixes_infty hi hinfG hfix (hKG (hγK i t))
  let δ : I → Circle → ℂ := fun i t => finiteCoord (f ((γ i t : ℂ) : Sphere))
  have hcoords (i : I) (t : Circle) : (δ i t : Sphere) = f ((γ i t : ℂ) : Sphere) :=
    CannonMobius.coe_coordinate (hfinite i t)
  have hδ (i : I) : Continuous (δ i) := by
    apply OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff.mpr
    have he : ((↑) : ℂ → Sphere) ∘ δ i = f ∘ ((↑) : ℂ → Sphere) ∘ γ i :=
      funext (hcoords i)
    rw [he]
    exact hf.comp_continuous (OnePoint.continuous_coe.comp (hγ i))
      (fun t => hKG (hγK i t))
  have hδinj (i : I) : Injective (δ i) := by
    intro x y hxy
    apply hγinj i
    apply OnePoint.coe_injective
    apply hi (hKG (hγK i x)) (hKG (hγK i y))
    exact (hcoords i x).symm.trans ((congrArg ((↑) : ℂ → Sphere) hxy).trans (hcoords i y))
  choose H hH using fun i => hschoenflies (δ i) (hδ i) (hδinj i)
  have hHfront (i : I) : frontier (jordanInterior (H i)) = range (δ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (δ i) (hH i)
  have hHp : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    rw [hHfront i, hHfront j]
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    have he : ((γ i x : ℂ) : Sphere) = ((γ j y : ℂ) : Sphere) := by
      apply hi (hKG (hγK i x)) (hKG (hγK j y))
      exact (hcoords i x).symm.trans
        ((congrArg ((↑) : ℂ → Sphere) (hx.trans hy.symm)).trans (hcoords j y))
    exact Set.disjoint_left.mp (hγpair hij) ⟨x, rfl⟩ ⟨y, OnePoint.coe_injective he.symm⟩
  have himages (i : I) : f '' (((↑) : ℂ → Sphere) '' range (γ i)) =
      ((↑) : ℂ → Sphere) '' range (δ i) := by
    ext p
    constructor
    · rintro ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, rfl⟩
      exact ⟨δ i t, ⟨t, rfl⟩, hcoords i t⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨((γ i t : ℂ) : Sphere), ⟨γ i t, ⟨t, rfl⟩, rfl⟩, (hcoords i t).symm⟩
  have htargetfront : frontier (f '' K) =
      ⋃ i, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) := by
    rw [frontier_image_of_continuous_open hf ho hG hi hK hKG, hfront, image_iUnion]
    congr 1
    funext i
    rw [hHfront i]
    exact himages i
  have htargetint := interior_image_of_continuous_open hf ho hG hi hKG
  have htargetregular : closure (interior (f '' K)) = f '' K := by
    rw [htargetint]
    exact closure_image_interior_of_continuous hf hK hKG hregular
  have htargetconn : IsPreconnected (interior (f '' K)) := by
    rw [htargetint]
    exact hconn.image f (hf.mono (interior_subset.trans hKG))
  have htargetinf : OnePoint.infty ∈ interior (f '' K) := by
    rw [htargetint]
    exact ⟨OnePoint.infty, hinf, hfix⟩
  obtain ⟨hd, he⟩ := sphere_jordan_core_recognition htargetregular htargetconn htargetinf H hHp htargetfront
  exact ⟨H, hHfront, hd, he⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CompatibleLevelBarrier
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real barrier in the endpoint problem, with its actual physical
representative, countable enlarged flags, and finite-torus compatibility. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

namespace CompatibleLevelBarrier

variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {previous : PriorLevelFamily d.physicalDomain π} {flags EStar : Set Sphere}
  {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere} {W₁ : Set Sphere}

theorem finite_compatibility
    (B : CompatibleLevelBarrier d π previous flags EStar regions f W₁)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (d.dust \ B.exclusions)
        (circleBandGraph d.quotientDomain B.coordinate.quotient)
        (fun i => previous.graph i) labels) = 0 := by
  cases n with
  | zero => simp only [freeComponentFailure_empty_labels, measure_empty]
  | succ n => exact B.compatible n labels

end CompatibleLevelBarrier
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ConstrainedCostCodes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite coding-measure family with a prescribed null
residual-image constraint, as a standard Borel space of codes. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

omit [BorelSpace D] [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [Countable D] in
theorem measurableSet_constrainedCostCode (d : PathCodeData X Y) (p : D → X)
    (c : D → ℝ≥0∞) (ν : Measure X) [SFinite ν] (hB : IsClosed d.dust) :
    MeasurableSet {Γ : FiniteCostCode d p c | ν (residualImage d.dust Γ.val.val) = 0} :=
  (measurableSet_residualImageMass_zero hB ν).preimage
    (measurable_subtype_coe.comp measurable_subtype_coe)

omit [BorelSpace D] [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [Countable D] in
theorem standardBorel_constrainedCostCode (d : PathCodeData X Y) (p : D → X)
    (c : D → ℝ≥0∞) (ν : Measure X) [SFinite ν] (hB : IsClosed d.dust)
    [StandardBorelSpace (FiniteCostCode d p c)] :
    StandardBorelSpace (ConstrainedCostCode d p c ν) :=
  (measurableSet_constrainedCostCode d p c ν hB).standardBorel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CountablePositiveWeights
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite positive costs on countable mark sets, from geometric weights
of total mass at most one. -/

open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem exists_positive_finite_square_weights (S : Type*) [Countable S] :
    ∃ w : S → ℝ≥0∞, (∀ s, w s ≠ 0) ∧ (∀ s, w s ≠ ∞) ∧
      (∑' s, w s) < ∞ ∧ (∑' s, w s ^ 2) < ∞ := by
  obtain ⟨w, hw, hsum⟩ := exists_positive_summable_weights S
  have hw1 : ∀ s, w s ≤ 1 := fun s => (ENNReal.le_tsum s).trans hsum
  refine ⟨w, fun s => (hw s).ne', fun s => ne_of_lt ((hw1 s).trans_lt (by simp)),
    hsum.trans_lt (by simp), ?_⟩
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum ?_) (hsum.trans_lt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  intro s
  simpa only [pow_two, mul_one] using mul_le_mul' le_rfl (hw1 s)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteGapPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Variation payment across finitely many gaps

The domain intervals of a line crossing a finite circle domain contribute
their actual derivative variation. Each intervening hole contributes only
the difference of the two endpoint traces. This is the finite telescoping
step in the manuscript's parallel-line payment estimate.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

theorem abs_sub_le_sum_segments_and_jumps (n : ℕ) (left right : Fin (n + 1) → ℝ) :
    |right (Fin.last n) - left 0| ≤
      (∑ i, |right i - left i|) +
        ∑ i : Fin n, |left i.succ - right i.castSucc| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprior := ih (fun i => left i.castSucc) (fun i => right i.castSucc)
    have htriangle : |right (Fin.last (n + 1)) - left 0| ≤
        |right (Fin.last (n + 1)) - left (Fin.last (n + 1))| +
        |left (Fin.last (n + 1)) - right (Fin.last n).castSucc| +
        |right (Fin.last n).castSucc - left 0| := by
      have heq : right (Fin.last (n + 1)) - left 0 =
          (right (Fin.last (n + 1)) - left (Fin.last (n + 1))) +
          (left (Fin.last (n + 1)) - right (Fin.last n).castSucc) +
          (right (Fin.last n).castSucc - left 0) := by ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    calc
      _ ≤ |right (Fin.last (n + 1)) - left (Fin.last (n + 1))| +
          |left (Fin.last (n + 1)) - right (Fin.last n).castSucc| +
          ((∑ i : Fin (n + 1), |right i.castSucc - left i.castSucc|) +
            ∑ i : Fin n, |left i.succ.castSucc - right i.castSucc.castSucc|) :=
        htriangle.trans (add_le_add le_rfl (by simpa only [Fin.castSucc_zero] using hprior))
      _ = _ := by
        rw [Fin.sum_univ_castSucc (fun i : Fin (n + 2) => |right i - left i|),
          Fin.sum_univ_castSucc (fun i : Fin (n + 1) => |left i.succ - right i.castSucc|)]
        simp only [Fin.castSucc_succ, Fin.succ_last]
        ring

theorem variation_le_integral_abs_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) :
    |f b - f a| ≤ ∫ x in a..b, |deriv f x| := by
  rw [← hf.integral_deriv_eq_sub]
  simpa only [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_integral_norm (f := deriv f) hab)

theorem line_payment_across_finite_gaps
    (n : ℕ) (a b : Fin (n + 1) → ℝ) (f : Fin (n + 1) → ℝ → ℝ)
    (A : Fin n → ℝ) (hab : ∀ i, a i ≤ b i)
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) (a i) (b i))
    (hzero : f 0 (a 0) = 0) (hone : f (Fin.last n) (b (Fin.last n)) = 1)
    (hjumps : ∀ i : Fin n,
      |f i.succ (a i.succ) - f i.castSucc (b i.castSucc)| ≤ A i) :
    1 ≤ (∑ i, ∫ x in a i..b i, |deriv (f i) x|) + ∑ i, A i := by
  have hchain := abs_sub_le_sum_segments_and_jumps n
    (fun i => f i (a i)) (fun i => f i (b i))
  rw [hone, hzero] at hchain
  norm_num only [sub_zero, abs_one] at hchain
  exact hchain.trans (add_le_add
    (Finset.sum_le_sum (fun i _ => variation_le_integral_abs_deriv (hab i) (hf i)))
    (Finset.sum_le_sum (fun i _ => hjumps i)))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_OpenGapPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Payment from smooth functions on open gaps

Finite energy supplies the endpoint traces, even when the function has
no prescribed values on the removed intervals. Bounds on the endpoint
traces are used only for the jumps across those intervals.
-/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem line_payment_from_open_gaps
    (n : ℕ) (a b : Fin (n + 1) → ℝ) (f : ℝ → ℝ) (d ρ : ℝ → ℝ)
    (A : Fin n → ℝ) (hab : ∀ i, a i < b i)
    (hd : ∀ i x, x ∈ Ioo (a i) (b i) → HasDerivAt f (d x) x)
    (hi : ∀ i, IntervalIntegrable d volume (a i) (b i))
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hdom : ∀ i x, x ∈ Ioo (a i) (b i) → |d x| ≤ ρ x)
    (hdisj : Pairwise (Disjoint on fun i => Ioo (a i) (b i)))
    (hzero : Tendsto f (𝓝[Ioo (a 0) (b 0)] (a 0)) (𝓝 0))
    (hone : Tendsto f (𝓝[Ioo (a (Fin.last n)) (b (Fin.last n))]
      (b (Fin.last n))) (𝓝 1))
    (hjump : ∀ (i : Fin n) u v,
      Tendsto f (𝓝[Ioo (a i.castSucc) (b i.castSucc)] (b i.castSucc)) (𝓝 u) →
      Tendsto f (𝓝[Ioo (a i.succ) (b i.succ)] (a i.succ)) (𝓝 v) → |v - u| ≤ A i) :
    1 ≤ (∫ x, ρ x) + ∑ i, A i := by
  choose g hg heq hleft hright using fun i =>
    exists_absolutelyContinuous_extension_of_integrable_derivative (hab i) (hd i) (hi i)
  have hgderiv (i : Fin (n + 1)) (x : ℝ) (hx : x ∈ Ioo (a i) (b i)) :
      deriv (g i) x = d x := by
    have hevent : g i =ᶠ[𝓝 x] f := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
      exact heq i hz
    exact ((hd i x hx).congr_of_eventuallyEq hevent).deriv
  have hfirst : g 0 (a 0) = 0 := by
    have : NeBot (𝓝[Ioo (a 0) (b 0)] (a 0)) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by simpa [closure_Ioo (hab 0).ne] using (hab 0).le)
    exact tendsto_nhds_unique (hleft 0) hzero
  have hlast : g (Fin.last n) (b (Fin.last n)) = 1 := by
    have : NeBot (𝓝[Ioo (a (Fin.last n)) (b (Fin.last n))] (b (Fin.last n))) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hab (Fin.last n)).ne]
        exact right_mem_Icc.mpr (hab (Fin.last n)).le)
    exact tendsto_nhds_unique (hright (Fin.last n)) hone
  have hline := line_payment_across_finite_gaps n a b g A (fun i => (hab i).le)
    hg hfirst hlast (fun i => hjump i _ _ (hright i.castSucc) (hleft i.succ))
  have hbound (i : Fin (n + 1)) :
      (∫ x in a i..b i, |deriv (g i) x|) ≤ ∫ x in Ioo (a i) (b i), ρ x := by
    rw [intervalIntegral.integral_of_le (hab i).le, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_mono_on ?_ hρ.integrableOn measurableSet_Ioo ?_
    · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (hab i).le).mp
        (hg i).intervalIntegrable_deriv.abs
    · intro x hx
      rw [hgderiv i x hx]
      exact hdom i x hx
  have hsum : (∑ i, ∫ x in a i..b i, |deriv (g i) x|) ≤ ∫ x, ρ x := by
    calc
      _ ≤ ∑ i, ∫ x in Ioo (a i) (b i), ρ x := Finset.sum_le_sum (fun i _ => hbound i)
      _ = ∫ x in ⋃ i, Ioo (a i) (b i), ρ x :=
        (integral_iUnion_fintype (fun _ => measurableSet_Ioo) hdisj
          (fun _ => hρ.integrableOn)).symm
      _ ≤ _ := setIntegral_le_integral hρ (Eventually.of_forall hpos)
  exact hline.trans (add_le_add hsum le_rfl)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteLineGaps
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual gaps of finitely many disjoint line intervals

Sorting the closed holes supplies the open intervals on which variation
is paid. Every gap is nonempty, the gaps are disjoint, and no point of a
gap belongs to a hole. Point holes are allowed.
-/

open Set Function

namespace CircleDomainRigidity

theorem gapsAfterHoles_disjoint {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 ≤ (H i).2)
    (hfirst : Monotone (fun i => (H i).1)) :
    Pairwise (Disjoint on fun i => Ioo
      (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2) := by
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)).symm
  obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last
    (show i ≠ Fin.last n by
      intro he
      subst i
      exact (not_lt_of_ge (Fin.le_last j)) hlt)
  obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero
    (show j ≠ 0 by intro he; simp [he] at hlt)
  have hkl : k ≤ l := by
    exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hlt)
  apply disjoint_left.mpr
  intro x hx hy
  dsimp only at hx hy
  rw [gapsAfterHoles_castSucc_snd] at hx
  rw [gapsAfterHoles_succ_fst] at hy
  exact (not_lt_of_ge (((hfirst hkl).trans (hvalid l)).trans hy.1.le)) hx.2

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_OrderedHolePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Line payment for an actual finite family of closed intervals

The removed intervals are ordered and disjoint. Smoothness is required
only on their complement. Endpoint cluster bounds pay for the jumps;
absolute continuity of the individual domain intervals is derived.
-/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem line_payment_of_ordered_holes
    {n : ℕ} {a b : ℝ} (hab : a < b) (H : Fin n → ℝ × ℝ)
    (hinside : ∀ i, a < (H i).1 ∧ (H i).1 ≤ (H i).2 ∧ (H i).2 < b)
    (hsep : ∀ i j, i < j → (H i).2 < (H j).1)
    {f d ρ : ℝ → ℝ} (A : Fin n → ℝ)
    (hd : ∀ x ∈ Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ, HasDerivAt f (d x) x)
    (hcd : ContinuousOn d (Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ))
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hdom : ∀ x ∈ Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ, |d x| ≤ ρ x)
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) (hzero : f a = 0) (hone : f b = 1)
    (hjump : ∀ i u v,
      MapClusterPt u (𝓝[Icc a b ∩ (⋃ j, Icc (H j).1 (H j).2)ᶜ] (H i).1) f →
      MapClusterPt v (𝓝[Icc a b ∩ (⋃ j, Icc (H j).1 (H j).2)ᶜ] (H i).2) f → |v - u| ≤ A i) :
    1 ≤ (∫ x, ρ x) + ∑ i, A i := by
  let gap := gapsAfterHoles a b H
  let D := Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ
  have hfirst : Monotone (fun i => (H i).1) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · rfl
    · exact (hinside i).2.1.trans (hsep i j hij).le
  have hlast : Monotone (fun i => (H i).2) := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · rfl
    · exact (hsep i j hij).le.trans (hinside j).2.1
  have hgap (i : Fin (n + 1)) : (gap i).1 < (gap i).2 :=
    gapsAfterHoles_strict hab H hinside hsep i
  have hgapAB (i : Fin (n + 1)) : Ioo (gap i).1 (gap i).2 ⊆ Icc a b := by
    have hleft : a ≤ (gap i).1 := by
      change a ≤ (gapsAfterHoles a b H i).1
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_rfl
      · exact (hinside j).1.le.trans (hinside j).2.1
    have hright : (gap i).2 ≤ b := by
      change (gapsAfterHoles a b H i).2 ≤ b
      refine Fin.lastCases (motive := fun j : Fin (n + 1) =>
        (gapsAfterHoles a b H j).2 ≤ b) ?_ (fun j => ?_) i
      · simp only [gapsAfterHoles_last_snd, le_refl]
      · simpa only [gapsAfterHoles_castSucc_snd] using (hinside j).2.1.trans (hinside j).2.2.le
    exact fun _ hx => ⟨hleft.trans hx.1.le, hx.2.le.trans hright⟩
  have hgapD (i : Fin (n + 1)) : Ioo (gap i).1 (gap i).2 ⊆ D := by
    intro x hx
    refine ⟨hgapAB i hx, ?_⟩
    exact fun h => by
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      exact gapsAfterHoles_avoid a b H hfirst hlast i hx j hj
  have hgi (i : Fin (n + 1)) : IntervalIntegrable d volume (gap i).1 (gap i).2 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (hgap i).le).mpr
    apply hρ.integrableOn.mono' ((hcd.mono (hgapD i)).aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using hdom x (hgapD i hx)
  apply line_payment_from_open_gaps n (fun i => (gap i).1) (fun i => (gap i).2)
    f d ρ A hgap (fun i x hx => hd x (hgapD i hx)) hgi hρ hpos
    (fun i x hx => hdom x (hgapD i hx))
    (gapsAfterHoles_disjoint a b H (fun i => (hinside i).2.1) hfirst)
  · simpa only [gap, gapsAfterHoles_zero_fst, ← hzero] using
      ha.mono_left nhdsWithin_le_nhds
  · simpa only [gap, gapsAfterHoles_last_snd, ← hone] using
      hb.mono_left nhdsWithin_le_nhds
  · intro i u v hu hv
    have hnleft : NeBot (𝓝[Ioo (gap i.castSucc).1 (gap i.castSucc).2] (gap i.castSucc).2) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hgap i.castSucc).ne]
        exact right_mem_Icc.mpr (hgap i.castSucc).le)
    have hnright : NeBot (𝓝[Ioo (gap i.succ).1 (gap i.succ).2] (gap i.succ).1) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hgap i.succ).ne]
        exact left_mem_Icc.mpr (hgap i.succ).le)
    have hlu := hu.mapClusterPt.mono (nhdsWithin_mono _ (hgapD i.castSucc))
    have hlv := hv.mapClusterPt.mono (nhdsWithin_mono _ (hgapD i.succ))
    apply hjump i u v
    · simpa only [gap, gapsAfterHoles_castSucc_snd] using hlu
    · simpa only [gap, gapsAfterHoles_succ_fst] using hlv

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DisjointHolePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Payment through an unordered finite set of holes

A finite set of disjoint closed intervals is sorted inside Lean; the
variation estimate is then applied to its actual complementary gaps.
-/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem line_payment_of_disjoint_holes
    {a b : ℝ} (hab : a < b) (F : Finset (ℝ × ℝ))
    (hinside : ∀ z ∈ F, a < z.1 ∧ z.1 ≤ z.2 ∧ z.2 < b)
    (hdisj : (↑F : Set (ℝ × ℝ)).PairwiseDisjoint (fun z => Icc z.1 z.2))
    {f d ρ : ℝ → ℝ} (A : ℝ × ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b ∩ (⋃ z ∈ F, Icc z.1 z.2)ᶜ, HasDerivAt f (d x) x)
    (hcd : ContinuousOn d (Icc a b ∩ (⋃ z ∈ F, Icc z.1 z.2)ᶜ))
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hdom : ∀ x ∈ Icc a b ∩ (⋃ z ∈ F, Icc z.1 z.2)ᶜ, |d x| ≤ ρ x)
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) (hzero : f a = 0) (hone : f b = 1)
    (hjump : ∀ z ∈ F, ∀ u v,
      MapClusterPt u (𝓝[Icc a b ∩ (⋃ w ∈ F, Icc w.1 w.2)ᶜ] z.1) f →
      MapClusterPt v (𝓝[Icc a b ∩ (⋃ w ∈ F, Icc w.1 w.2)ᶜ] z.2) f → |v - u| ≤ A z) :
    1 ≤ (∫ x, ρ x) + ∑ z ∈ F, A z := by
  classical
  let H := F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl
  have hmem (i : Fin F.card) : H i ∈ F := F.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ) rfl i
  have honto (z : ℝ × ℝ) (hz : z ∈ F) : ∃ i : Fin F.card, H i = z := by
    let z' : (F : Finset (ℝ ×ₗ ℝ)) := ⟨z, hz⟩
    refine ⟨(F.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).symm z', ?_⟩
    exact congrArg Subtype.val ((F.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).apply_symm_apply z')
  have hcover : (⋃ i, Icc (H i).1 (H i).2) = ⋃ z ∈ F, Icc z.1 z.2 := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨H i, mem_iUnion.mpr ⟨hmem i, hi⟩⟩
    · intro hx
      obtain ⟨z, hz, hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨i, rfl⟩ := honto z hz
      exact mem_iUnion.mpr ⟨i, hx⟩
  have h := line_payment_of_ordered_holes hab H (fun i => hinside _ (hmem i))
    (sorted_holes_separated F (fun z hz => (hinside z hz).2.1) hdisj)
    (fun i => A (H i))
    (by simpa only [hcover] using hd) (by simpa only [hcover] using hcd) hρ hpos
    (by simpa only [hcover] using hdom) ha hb hzero hone
    (by
      intro i u v hu hv
      apply hjump (H i) (hmem i) u v
      · simpa only [hcover] using hu
      · simpa only [hcover] using hv)
  have hsum : (∑ i : Fin F.card, A (H i)) = ∑ z ∈ F, A z := by
    apply Finset.sum_bij (fun i _ => H i)
    · exact fun i _ => hmem i
    · exact fun i _ j _ hij => H.injective hij
    · intro z hz
      obtain ⟨i, hi⟩ := honto z hz
      exact ⟨i, Finset.mem_univ _, hi⟩
    · exact fun _ _ => rfl
  exact h.trans_eq (congrArg (fun t => (∫ x, ρ x) + t) hsum)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ParallelDiskTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact costs of round holes on parallel lines

The horizontal lines meeting a closed round disk form an interval of
length twice its radius. Integrating finitely many hole tolls therefore
gives exactly the radius-weighted sum. Disjointness and a common containing
disk bound this sum by the square norm of the oscillation tolls.
-/

open Set Function Metric MeasureTheory

namespace CircleDomainRigidity

theorem parallel_disk_tolls_le_square_norm
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall 0 L) :
    (∫ y : ℝ, ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y) ≤
      2 * L * Real.sqrt (∑ i, A i ^ 2) := by
  rw [integral_parallel_disk_tolls c r A hr]
  have hs : Real.sqrt (∑ i, r i ^ 2) ≤ L := by
    simpa only [Real.sqrt_sq hL] using Real.sqrt_le_sqrt
      (sum_radii_sq_le_of_disjoint_closed_disks c r hr hL hdisj hsub)
  calc
    _ = 2 * ∑ i, r i * A i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ 2 * (Real.sqrt (∑ i, r i ^ 2) * Real.sqrt (∑ i, A i ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ r A) (by norm_num)
    _ ≤ 2 * (L * Real.sqrt (∑ i, A i ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)) (by norm_num)
    _ = _ := by ring

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DiskLinePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Variation across the round holes met by one line

This derives the linewise payment directly from smoothness on the
complement of the actual disks and their cluster oscillations. No
endpoint extension or pre-existing line-payment hypothesis is assumed.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem line_payment_through_disks
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {y a b : ℝ} (hab : a < b)
    (ha : a ∈ diskLineDomain c r y) (hb : b ∈ diskLineDomain c r y)
    {f ρ : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (diskLineDomain c r y))
    (hzero : f a = 0) (hone : f b = 1)
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hmajor : ∀ x ∈ Icc a b ∩ diskLineDomain c r y, |deriv f x| ≤ ρ x)
    (hcluster : ∀ i p q u v,
      (⟨p, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      (⟨q, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[diskLineDomain c r y] p) f →
      MapClusterPt v (𝓝[diskLineDomain c r y] q) f → |v - u| ≤ A i) :
    1 ≤ (∫ x, ρ x) +
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
  classical
  let F := crossingChords c r y a b
  let E := Icc a b ∩ (⋃ z ∈ F, Icc z.1 z.2)ᶜ
  have hED : E ⊆ diskLineDomain c r y := by
    intro x hx
    exact (crossingChords_domain c r hr hx.1).mp hx.2
  have hD := isOpen_diskLineDomain c r y
  have hfa := hf.contDiffAt (hD.mem_nhds ha)
  have hfb := hf.contDiffAt (hD.mem_nhds hb)
  have hp := line_payment_of_disjoint_holes hab F
    (crossingChords_inside c r hr
      (fun i hi => ha (mem_iUnion.mpr ⟨i, hi⟩))
      (fun i hi => hb (mem_iUnion.mpr ⟨i, hi⟩)))
    (crossingChords_disjoint c r hr hdisj) (chordToll c r A y a b)
    (fun x hx => (hf.contDiffAt (hD.mem_nhds (hED hx))).differentiableAt (by norm_num) |>.hasDerivAt)
    ((hf.continuousOn_deriv_of_isOpen hD le_rfl).mono hED)
    hρ hpos (fun x hx => hmajor x ⟨hx.1, hED hx⟩)
    hfa.continuousAt hfb.continuousAt hzero hone (by
      intro z hz u v hu hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hy := crossingDisk_line_hit hi
      have hp := (mem_closedBall_iff_mem_horizontalChord (c i) (hr i) hy).mpr
        (left_mem_Icc.mpr (horizontalChord_valid _ _ _))
      have hq := (mem_closedBall_iff_mem_horizontalChord (c i) (hr i) hy).mpr
        (right_mem_Icc.mpr (horizontalChord_valid _ _ _))
      exact (hcluster i _ _ u v hp hq
        (hu.mono (nhdsWithin_mono _ hED))
        (hv.mono (nhdsWithin_mono _ hED))).trans (le_chordToll c r A y a b hA hi))
  exact hp.trans (add_le_add le_rfl (sum_chordToll_le_line_hits c r A y a b hA))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ParallelLineIntegration
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integration of the parallel-line payments

The linewise variation and hole costs are integrated without a measurable
choice of crossing segments. Cauchy–Schwarz is applied only to the density
in the chosen bounded region. This is the integration step of the
parallel-line lemma in Section 5 of the Koebe manuscript.
-/

open Set Function Metric MeasureTheory

namespace CircleDomainRigidity

theorem integral_horizontal_slices {ρ : ℂ → ℝ} (hρ : Integrable ρ) :
    Integrable (fun y : ℝ => ∫ x : ℝ, ρ ⟨x, y⟩) ∧
      (∫ y : ℝ, ∫ x : ℝ, ρ ⟨x, y⟩) = ∫ z : ℂ, ρ z := by
  have he := (Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd).integrable_comp hρ.aestronglyMeasurable
  have hp : Integrable (fun p : ℝ × ℝ => ρ ⟨p.1, p.2⟩) := he.mpr hρ
  refine ⟨hp.integral_prod_right, ?_⟩
  calc
    _ = ∫ p : ℝ × ℝ, ρ ⟨p.1, p.2⟩ := (integral_prod_symm _ hp).symm
    _ = _ := (Complex.volume_preserving_equiv_real_prod.symm
      Complex.measurableEquivRealProd).integral_comp' ρ

theorem integrated_parallel_line_payment
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ)
    {ρ : ℂ → ℝ} {J : Set ℝ} {L : ℝ}
    (hJfinite : volume J ≠ ⊤)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i) (hL : 0 ≤ L)
    (hρ : MemLp ρ 2 volume) (hpos : ∀ z, 0 ≤ ρ z)
    (hsupport : support ρ ⊆ closedBall 0 L)
    (hpay : ∀ᵐ y ∂volume.restrict J, 1 ≤ (∫ x : ℝ, ρ ⟨x, y⟩) +
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt (∫ z, ρ z ^ 2) +
      ∑ i, 2 * r i * A i := by
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr hJfinite
  have hiρ := integral_le_disk_L2 hL hρ hpos hsupport
  have hslices := integral_horizontal_slices hiρ.1
  let toll : ℝ → ℝ := fun y =>
    ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y
  have hitoll : Integrable toll := by
    apply integrable_finsetSum
    intro i _
    exact (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hsumpos : ∀ y, 0 ≤ (∫ x : ℝ, ρ ⟨x, y⟩) + toll y := by
    intro y
    exact add_nonneg (integral_nonneg (fun _ => hpos _))
      (Finset.sum_nonneg (fun i _ => indicator_nonneg (fun _ _ => hA i) y))
  calc
    (volume J).toReal = ∫ _y in J, (1 : ℝ) := by simp [measureReal_def]
    _ ≤ ∫ y in J, (∫ x : ℝ, ρ ⟨x, y⟩) + toll y :=
      integral_mono_ae (integrable_const _) (hslices.1.add hitoll).integrableOn hpay
    _ ≤ ∫ y : ℝ, (∫ x : ℝ, ρ ⟨x, y⟩) + toll y :=
      setIntegral_le_integral (hslices.1.add hitoll) (Filter.Eventually.of_forall hsumpos)
    _ = (∫ z, ρ z) + ∑ i, 2 * r i * A i := by
      rw [integral_add hslices.1 hitoll, hslices.2]
      exact congrArg _ (integral_parallel_disk_tolls c r A hr)
    _ ≤ _ := add_le_add hiρ.2 le_rfl

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanFillLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Upper containment for limits of Jordan fills

Uniform convergence of boundary parametrizations traps the approximating
closed fills in every neighborhood of the limiting closed fill. The proof
uses Jordan nesting and radial enlargement.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem eventually_jordan_fill_subset_open
    (H : ℂ ≃ₜ ℂ) (J : ℕ → ℂ ≃ₜ ℂ)
    (γ : Circle → ℂ) (γn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hfront : range γ = frontier (jordanInterior H))
    (hfrontn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (J n)))
    (hlim : TendstoUniformly γn γ atTop)
    {O : Set ℂ} (hO : IsOpen O) (hHO : closure (jordanInterior H) ⊆ O) :
    ∀ᶠ n in atTop, closure (jordanInterior (J n)) ⊆ O := by
  obtain ⟨r, hr, hrO, _⟩ := exists_disjoint_jordan_enlargements
    (fun _ : Unit => H) (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
    (fun _ => O) (fun _ => hO) (fun _ => hHO)
  let K := dilatedJordan H (r Unit.unit) (by linarith [hr Unit.unit])
  have hK : jordanInterior K = H '' ball (0 : ℂ) (r Unit.unit) :=
    jordanInterior_dilated H _
  have hγK : range γ ⊆ jordanInterior K := by
    rw [hfront, frontier_jordanInterior, hK]
    apply image_mono
    intro z hz
    simpa only [mem_ball, mem_sphere, dist_zero_right] using
      (show ‖z‖ < r Unit.unit by
        have hz' : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
        linarith [hr Unit.unit])
  obtain ⟨δ, hδ, hδK⟩ := (isCompact_range hγ).exists_thickening_subset_open
    (jordanInterior_isOpen K) hγK
  have hclose := Metric.tendstoUniformly_iff.mp hlim δ hδ
  filter_upwards [hclose, hfrontn] with n hn hnfront
  apply (closed_jordanInterior_subset_of_frontier_subset (J n) K ?_).trans
    (show jordanInterior K ⊆ O by
      rw [hK]
      exact (image_mono ball_subset_closedBall).trans (hrO Unit.unit))
  rw [← hnfront]
  rintro _ ⟨t, rfl⟩
  apply hδK
  apply mem_thickening_iff.mpr
  exact ⟨γ t, mem_range_self t, by simpa only [dist_comm] using hn t⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedJordanCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Closed cores bounded by a finite disjoint Jordan family

The closed common exterior is regular closed, its interior is the already
constructed connected open completed region, and its boundary is exactly
the union of the specified Jordan curves.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem interior_finite_disjoint_closed
    {I : Type*} [Finite I] (C : I → Set Sphere)
    (hC : ∀ i, IsClosed (C i)) (hd : Pairwise (Disjoint on C)) :
    interior (⋃ i, C i) = ⋃ i, interior (C i) := by
  classical
  apply Subset.antisymm
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hp)
    let B : Set Sphere := ⋃ j : {j : I // j ≠ i}, C j
    have hB : IsClosed B := isClosed_iUnion_of_finite fun j => hC j
    have hpB : p ∉ B := by
      intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      exact Set.disjoint_left.mp (hd j.property.symm) hi hj
    have hsub : interior (⋃ j, C j) ∩ Bᶜ ⊆ C i := by
      rintro q ⟨hq, hqB⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (interior_subset hq)
      by_cases hji : j = i
      · exact hji ▸ hj
      · exact (hqB (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)).elim
    exact mem_iUnion.mpr ⟨i, interior_maximal hsub (isOpen_interior.inter hB.isOpen_compl) ⟨hp, hpB⟩⟩
  · exact iUnion_subset fun i => interior_mono (subset_iUnion C i)

theorem closure_interior_closedJordanCore
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    closure (interior (closedJordanCore H)) = closedJordanCore H := by
  rw [interior_closedJordanCore, openCompletedRegion, closure_compl,
    interior_finite_disjoint_closed (fun i => closedTerminalCap (H i))
      (fun i => (isCompact_closedTerminalCap (H i)).isClosed) (disjoint_closedTerminalCaps H hd)]
  simp only [interior_closedTerminalCap, closedJordanCore]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothJordanExhaustion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A strict exhaustion by finite smooth Jordan cores

Every prescribed compact subset is retained in the interior of a finite
Jordan core. Recursive application retains the preceding core and the next
compact exhaustion set. The construction uses Sard, one-manifold
classification, and Schoenflies.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

namespace SmoothJordanCore

variable {G : Set Sphere} (C : SmoothJordanCore G)

theorem regular : closure (interior C.carrier) = C.carrier :=
  closure_interior_closedJordanCore C.disk C.disjoint

theorem connected_interior : IsConnected (interior C.carrier) := by
  rw [carrier, interior_closedJordanCore]
  exact isConnected_openCompletedRegion C.disk C.disjoint

theorem infty_interior : OnePoint.infty ∈ interior C.carrier := by
  rw [carrier, interior_closedJordanCore]
  intro h
  obtain ⟨i, z, _, hz⟩ := mem_iUnion.mp h
  exact OnePoint.coe_ne_infty z hz

end SmoothJordanCore

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanIntersectionConnectivity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connectivity on the inside of a retained Jordan boundary

A radial clamp onto a slightly smaller disk fixes any prescribed pair of
interior points and maps the whole domain into its intersection with the
disk. The inner circle stays in the domain by compactness of the retained
boundary. This proves the connectedness needed to track source and image
sides under refinement.
-/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuous_radialClamp {r : ℝ} (hr : 0 < r) : Continuous (radialClamp r) := by
  apply (continuous_const.div (continuous_const.max continuous_norm) ?_).smul continuous_id
  intro z
  exact ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _))

theorem radialClamp_eq_self {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    radialClamp r z = z := by
  simp only [radialClamp, max_eq_left hz, div_self hr.ne', one_smul]

theorem norm_radialClamp_of_le {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : r ≤ ‖z‖) :
    ‖radialClamp r z‖ = r := by
  have hn : ‖z‖ ≠ 0 := ne_of_gt (hr.trans_le hz)
  rw [radialClamp, max_eq_right hz, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr.le (norm_nonneg z)), div_mul_cancel₀ _ hn]

theorem inner_circle_subset_of_retained_boundary
    {W : Set ℂ} (hW : IsOpen W) (hboundary : sphere (0 : ℂ) 1 ⊆ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < 1 → 1 - r < δ → sphere (0 : ℂ) r ⊆ W := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_sphere (0 : ℂ) 1).exists_cthickening_subset_open hW hboundary
  refine ⟨δ, hδ, ?_⟩
  intro r hr hr1 hnear z hz
  have hzn : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
  let w : ℂ := r⁻¹ • z
  have hwn : ‖w‖ = 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hzn,
      inv_mul_cancel₀ hr.ne']
  have hzw : z = r • w := by simp only [w, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  apply hsub
  apply mem_cthickening_of_dist_le z w δ (sphere (0 : ℂ) 1)
    (mem_sphere_zero_iff_norm.mpr hwn)
  calc
    dist z w = ‖(r - 1) • w‖ := by rw [hzw, dist_eq_norm, sub_smul, one_smul]
    _ = 1 - r := by rw [norm_smul, Real.norm_eq_abs, hwn, mul_one, abs_of_neg (sub_neg.mpr hr1)]; ring
    _ ≤ δ := hnear.le

theorem isPreconnected_inter_unitDisk
    {W : Set ℂ} (hW : IsOpen W) (hconn : IsPreconnected W)
    (hboundary : sphere (0 : ℂ) 1 ⊆ W) :
    IsPreconnected (W ∩ ball 0 1) := by
  obtain ⟨δ, hδ, hcircle⟩ := inner_circle_subset_of_retained_boundary hW hboundary
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  have hxn : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx.2
  have hyn : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy.2
  have hmax : max (max ‖x‖ ‖y‖) (1 - δ) < 1 :=
    max_lt (max_lt hxn hyn) (by linarith)
  obtain ⟨r, hrlo, hrhi⟩ := exists_between hmax
  have hxr : ‖x‖ < r := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hrlo)
  have hyr : ‖y‖ < r := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hrlo)
  have hr : 0 < r := (norm_nonneg x).trans_lt hxr
  have hnear : 1 - r < δ := by linarith [le_max_right (max ‖x‖ ‖y‖) (1 - δ)]
  have hmap : radialClamp r '' W ⊆ W ∩ ball 0 1 := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hzr : ‖z‖ ≤ r
    · rw [radialClamp_eq_self hr hzr]
      exact ⟨hz, by simpa only [mem_ball, dist_zero_right] using hzr.trans_lt hrhi⟩
    · have he := norm_radialClamp_of_le hr (le_of_lt (lt_of_not_ge hzr))
      exact ⟨hcircle r hr hrhi hnear (mem_sphere_zero_iff_norm.mpr he), by
        simpa only [mem_ball, dist_zero_right, he] using hrhi⟩
  refine ⟨radialClamp r '' W, hmap, ?_, ?_, hconn.image _ (continuous_radialClamp hr).continuousOn⟩
  · exact ⟨x, hx.1, radialClamp_eq_self hr hxr.le⟩
  · exact ⟨y, hy.1, radialClamp_eq_self hr hyr.le⟩

theorem isPreconnected_inter_jordanInterior
    {W : Set ℂ} (hW : IsOpen W) (hconn : IsPreconnected W)
    (H : ℂ ≃ₜ ℂ) (hboundary : frontier (jordanInterior H) ⊆ W) :
    IsPreconnected (W ∩ jordanInterior H) := by
  have hpre : IsPreconnected (H ⁻¹' W) := H.isPreconnected_preimage.mpr hconn
  have hbd : sphere (0 : ℂ) 1 ⊆ H ⁻¹' W := by
    intro z hz
    apply hboundary
    rw [frontier_jordanInterior]
    exact mem_image_of_mem _ hz
  have hi := isPreconnected_inter_unitDisk (hW.preimage H.continuous) hpre hbd
  have he : H '' ((H ⁻¹' W) ∩ ball 0 1) = W ∩ jordanInterior H := by
    rw [image_preimage_inter]
    rfl
  exact he ▸ hi.image H H.continuous.continuousOn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanSideCorrespondence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correspondence of the source and image sides of a core boundary

Connectivity of the source on a disk's inside, together with local openness
at its retained boundary, determines which target Jordan disk it maps into.
This tracks the labels of boundary curves without extending the conformal
map across any omitted component.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem isPreconnected_sphere_jordan_intersection
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (hinf : OnePoint.infty ∈ G) (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    IsPreconnected (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  let W : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' G
  have hW : IsPreconnected W := (finite_part_connected_unbounded hconn
    (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hinf))).1
  have hi := isPreconnected_inter_jordanInterior (hG.preimage OnePoint.continuous_coe) hW H
    (fun z hz => hboundary (mem_image_of_mem _ hz))
  have he : ((↑) : ℂ → Sphere) '' (W ∩ jordanInterior H) =
      G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H) := image_preimage_inter _ _ _
  exact he ▸ hi.image _ OnePoint.continuous_coe.continuousOn

theorem open_image_jordan_side_subset
    {I : Type*} [Finite I] (H J : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hKG : closedJordanCore H ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hboundary : ∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)))
    (himage : (f '' closedJordanCore H)ᶜ =
      ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i)) (i : I) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (J i) := by
  classical
  let S : Set Sphere := G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))
  let O : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior (J i)
  have hOo : IsOpen O := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (J i))
  have hKclosed : IsClosed (closedJordanCore H) :=
    (isOpen_iUnion fun j => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H j))).isClosed_compl
  have hsrcboundary (j : I) : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H j)) ⊆ G := by
    intro q hq
    apply hKG
    have hfq : q ∈ frontier (closedJordanCore H) := by
      rw [frontier_closedJordanCore H hd]
      exact mem_iUnion.mpr ⟨j, hq⟩
    simpa only [hKclosed.closure_eq] using frontier_subset_closure hfq
  have hS : IsPreconnected S :=
    isPreconnected_sphere_jordan_intersection hG hconn.isPreconnected hinf (H i) (hsrcboundary i)
  have hfrontO : frontier O = ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)) :=
    frontier_sphere_image_jordanInterior (J i)
  have havoid : Disjoint (f '' S) (frontier O) := by
    apply Set.disjoint_left.mpr
    rintro q ⟨x, hx, rfl⟩ hq
    rw [hfrontO, ← hboundary i] at hq
    obtain ⟨y, hy, he⟩ := hq
    have hyx : y = x := hi (hsrcboundary i hy) hx.1 he
    rw [hyx] at hy
    obtain ⟨z, hz, hez⟩ := hy
    obtain ⟨w, hw, hew⟩ := hx.2
    have hwz : w = z := OnePoint.coe_injective (hew.trans hez.symm)
    exact hz.2 ((jordanInterior_isOpen (H i)).interior_eq.symm ▸ (hwz ▸ hw))
  obtain ⟨z, hz⟩ := (isConnected_frontier_jordanInterior (H i)).nonempty
  let x : Sphere := (z : Sphere)
  have hxfront : x ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i)) := ⟨z, hz, rfl⟩
  let B : Set Sphere := ⋃ j : {j : I // j ≠ i}, closedTerminalCap (H j)
  have hBclosed : IsClosed B := isClosed_iUnion_of_finite fun j =>
    (isCompact_closedTerminalCap (H j)).isClosed
  have hxB : x ∉ B := by
    intro h
    obtain ⟨j, w, hw, he⟩ := mem_iUnion.mp h
    have hwz : w = z := OnePoint.coe_injective he
    exact Set.disjoint_left.mp (hd j.property.symm) (frontier_subset_closure hz) (hwz ▸ hw)
  let N : Set Sphere := G ∩ Bᶜ
  have hN : IsOpen N := hG.inter hBclosed.isOpen_compl
  have hxN : x ∈ N := ⟨hsrcboundary i hxfront, hxB⟩
  have hfN : IsOpen (f '' N) := ho _ hN inter_subset_left
  have hfxfront : f x ∈ frontier O := by
    rw [hfrontO, ← hboundary i]
    exact mem_image_of_mem _ hxfront
  obtain ⟨y, hyN, hyO⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hfxfront)
    (f '' N) (hfN.mem_nhds (mem_image_of_mem _ hxN))
  obtain ⟨w, hwN, rfl⟩ := hyN
  have hwK : w ∉ closedJordanCore H := by
    intro hw
    have htarget : f w ∈ (f '' closedJordanCore H)ᶜ := by
      rw [himage]
      exact mem_iUnion.mpr ⟨i, hyO⟩
    exact htarget (mem_image_of_mem _ hw)
  have hwS : w ∈ S := by
    refine ⟨hwN.1, ?_⟩
    have hwU : w ∈ ⋃ j, ((↑) : ℂ → Sphere) '' jordanInterior (H j) := not_not.mp hwK
    obtain ⟨j, v, hv, he⟩ := mem_iUnion.mp hwU
    by_cases hji : j = i
    · exact hji ▸ ⟨v, hv, he⟩
    · exact (hwN.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, v, subset_closure hv, he⟩)).elim
  have hmeet : (f '' S ∩ O).Nonempty := ⟨f w, mem_image_of_mem _ hwS, hyO⟩
  have hcover : f '' S ⊆ O ∪ (closure O)ᶜ := by
    intro q hq
    by_cases hqo : q ∈ O
    · exact Or.inl hqo
    · right
      intro hqc
      exact Set.disjoint_left.mp havoid hq ⟨hqc, by
        simpa only [hOo.interior_eq] using hqo⟩
  exact (hS.image f (hf.mono inter_subset_left)).subset_left_of_subset_union
    hOo isClosed_closure.isOpen_compl
    (Set.disjoint_left.mpr fun _ h₁ h₂ => h₂ (subset_closure h₁)) hcover hmeet


theorem open_image_jordan_side_eq
    {I : Type*} [Finite I] (H J : I → ℂ ≃ₜ ℂ)
    (hd : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    (hJd : Pairwise (Disjoint on fun i => closure (jordanInterior (J i))))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hKG : closedJordanCore H ⊆ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hboundary : ∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (H i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)))
    (himage : (f '' closedJordanCore H)ᶜ =
      ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i)) (i : I) :
    f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (H i))) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
  have hsides := open_image_jordan_side_subset H J hd hG hconn hinf hKG hf ho hi hboundary himage
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_image_of_mem _ hx.1, hsides i (mem_image_of_mem _ hx)⟩
  · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    have hnotK : x ∉ closedJordanCore H := by
      intro hxK
      have hnot : f x ∈ (f '' closedJordanCore H)ᶜ := by
        rw [himage]
        exact mem_iUnion.mpr ⟨i, hy⟩
      exact hnot (mem_image_of_mem _ hxK)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (not_not.mp hnotK)
    have hj' := hsides j (mem_image_of_mem f ⟨hx, hj⟩)
    have hji : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (disjoint_closedTerminalCaps J hJd hne)
        (by obtain ⟨z, hz, he⟩ := hj'; exact ⟨z, subset_closure hz, he⟩)
        (by obtain ⟨z, hz, he⟩ := hy; exact ⟨z, subset_closure hz, he⟩)
    exact ⟨x, ⟨hx, hji ▸ hj⟩, rfl⟩


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedImageCores
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matched source and target Jordan cores

The actual mapped boundary parametrizations identify each target disk's
label. Both inclusions of the corresponding source/target side equality
are proved, so refinement can carry those labels to end components.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_matched_image_core_of_continuous_open
    (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : ContinuousOn f G)
    (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S)) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) (C : SmoothJordanCore G) :
    ∃ J : Fin C.count → ℂ ≃ₜ ℂ,
      Pairwise (Disjoint on fun i => closure (jordanInterior (J i))) ∧
      (f '' C.carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i) ∧
      (∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i))) ∧
      ∀ i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (C.disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
  have hsrcfront : frontier C.carrier = ⋃ i, ((↑) : ℂ → Sphere) '' range (C.curve i) := by
    rw [SmoothJordanCore.carrier, frontier_closedJordanCore C.disk C.disjoint]
    simp only [C.boundary]
  have hcurvesG (i : Fin C.count) (t : Circle) : ((C.curve i t : ℂ) : Sphere) ∈ G := by
    apply C.subset
    have hfront : ((C.curve i t : ℂ) : Sphere) ∈ frontier C.carrier := by
      rw [hsrcfront]
      exact mem_iUnion.mpr ⟨i, C.curve i t, ⟨t, rfl⟩, rfl⟩
    simpa only [C.isCompact.isClosed.closure_eq] using frontier_subset_closure hfront
  obtain ⟨J, hJfront, hJd, hJe⟩ := exists_jordan_image_core_of_continuous_open hschoenflies hG hf ho hi
    C.isCompact C.subset C.regular C.connected_interior.isPreconnected C.infty_interior hfix
    C.curve (fun i => (C.embedding i).continuous) (fun i => (C.embedding i).injective)
    (by
      intro i j hij
      apply (C.disjoint hij).mono
      · rw [← C.boundary i]
        exact frontier_subset_closure
      · rw [← C.boundary j]
        exact frontier_subset_closure) hsrcfront
  have hboundary (i : Fin C.count) :
      f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i)) := by
    rw [C.boundary i, hJfront i, image_image, ← range_comp, ← range_comp]
    congr 1
    funext t
    exact (CannonMobius.coe_coordinate
      (finite_image_of_fixes_infty hi hinf hfix (hcurvesG i t))).symm
  refine ⟨J, hJd, hJe, hboundary, ?_⟩
  exact open_image_jordan_side_eq C.disk J C.disjoint hJd hG hconn hinf C.subset
    hf ho hi hboundary hJe


theorem exists_matched_image_core
    (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : IsConformalOn f G) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty) (C : SmoothJordanCore G) :
    ∃ J : Fin C.count → ℂ ≃ₜ ℂ,
      Pairwise (Disjoint on fun i => closure (jordanInterior (J i))) ∧
      (f '' C.carrier)ᶜ = ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J i) ∧
      (∀ i, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i))) ∧
      ∀ i, f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (C.disk i))) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J i)) :=
  exists_matched_image_core_of_continuous_open hschoenflies hG hconn hinf
    (fun p hp => (hf p hp).1.continuousWithinAt)
    (fun _ hS hSG => hf.isOpen_image hG hS hSG) hi hfix C


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteMarkedTrapping
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Marked-disk trapping for the actual finite terminal assignment

The assignment is constructed from a finite model. Once a fixed source
core is retained, a terminal inside one of its holes has its target disk
inside the corresponding image contour. Uniform convergence on that
contour passes this containment to the limiting closed disk.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem range_finite_image_boundary
    {f : Sphere → Sphere} {γ : Circle → ℂ} {H L : ℂ ≃ₜ ℂ}
    (hγ : frontier (jordanInterior H) = range γ)
    (hb : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior L))
    (hfinite : ∀ t, f ((γ t : ℂ) : Sphere) ≠ OnePoint.infty) :
    range (fun t => finiteCoord (f ((γ t : ℂ) : Sphere))) = frontier (jordanInterior L) := by
  apply OnePoint.coe_injective.image_injective
  rw [← hb, hγ, image_image, ← range_comp, ← range_comp]
  congr 1
  funext t
  exact coe_finiteCoord (hfinite t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereClusterBridge
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-chart cluster bounds from the assigned sphere ends

The line-payment lemma uses planar cluster points. They are the same
finite cluster values controlled by the inverse terminal-boundary
argument, so no boundary extension of the finite uniformization is needed.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem TerminalComponentAssignment.planar_cluster_gap_le
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (w : Sphere → ℝ)
    (hw : ∀ q ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)), ContinuousAt w q)
    (hbounded : Bornology.IsBounded
      (w '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)))))
    {p q : ℂ} {u v : ℝ}
    (hp : (p : Sphere) ∈ connectedComponentIn Vᶜ (a.point i))
    (hq : (q : Sphere) ∈ connectedComponentIn Vᶜ (a.point i))
    (hu : MapClusterPt u (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] p)
      ((w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
    (hv : MapClusterPt v (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] q)
      ((w ∘ fi) ∘ ((↑) : ℂ → Sphere))) :
    |v - u| ≤ Metric.diam
      (w '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)))) := by
  have hsub := a.cluster_values_subset_boundary hf i w hw
  have hu' := hsub (planar_mapClusterPt_mem_componentClusterValues hp hu)
  have hv' := hsub (planar_mapClusterPt_mem_componentClusterValues hq hv)
  simpa only [Real.dist_eq] using Metric.dist_le_diam_of_mem hbounded hv' hu'

theorem TerminalComponentAssignment.real_planar_cluster_gap_le
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (i : I) (w : (ℝ × ℝ) → ℝ)
    {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hAO : frontier (realJordanInterior (T i)) ⊆ O) (hw : ContinuousOn w O)
    {p q : ℂ} {u v : ℝ}
    (hp : (p : Sphere) ∈ connectedComponentIn Vᶜ (a.point i))
    (hq : (q : Sphere) ∈ connectedComponentIn Vᶜ (a.point i))
    (hu : MapClusterPt u (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] p)
      ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
    (hv : MapClusterPt v (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] q)
      ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))) :
    |v - u| ≤ Metric.diam (w '' frontier (realJordanInterior (T i))) := by
  have hfront := frontier_realJordanInterior (T i)
  have himage : sphereRealFunction w '' (((↑) : ℂ → Sphere) ''
      frontier (jordanInterior (T i))) = w '' frontier (realJordanInterior (T i)) := by
    rw [hfront, image_image, image_image]
    rfl
  have hbounded : Bornology.IsBounded (w '' frontier (realJordanInterior (T i))) :=
    ((realJordanInterior_geometry (T i)).2.1.image_of_continuousOn (hw.mono hAO)).isBounded
  rw [← himage]
  apply a.planar_cluster_gap_le hf i (sphereRealFunction w) _ (himage.symm ▸ hbounded) hp hq hu hv
  rintro q ⟨z, hz, rfl⟩
  apply continuousAt_sphereRealFunction
  apply hw.continuousAt (hO.mem_nhds (hAO ?_))
  rw [hfront]
  exact mem_image_of_mem _ hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_TransportedRealLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy transport on retained source subsets and away from a prescribed core set. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem transported_real_energy_on_source_set
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hUinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (w : (ℝ × ℝ) → ℝ) (hw : ContDiffOn ℝ ∞ w (realChartDomain U))
    {g : (ℝ × ℝ) → PlanarMetric}
    (hf : ∀ p ∈ U, IsMetricConformalAt g f p)
    (hg : ∀ x ∈ realChartDomain U, (g x).PosDef)
    (hi : IntegrableOn (gradientEnergy w g) (realChartDomain U))
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsU : s ⊆ realChartDomain U) :
    IntegrableOn (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)))
      (Complex.equivRealProdCLM ⁻¹' (sphereRealMap f '' s)) ∧
    (∫ z in Complex.equivRealProdCLM ⁻¹' (sphereRealMap f '' s),
      euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) z) =
      ∫ x in s, gradientEnergy w g x := by
  have hO := isOpen_realChartDomain hU
  obtain ⟨hW, hv, _⟩ := transported_real_coordinate heq hV hUinf hfix hO (Subset.refl _) w hw
  have himage : MeasurableSet (sphereRealMap f '' s) :=
    hs.image_of_continuousOn_injOn
      (fun x hx => (heq.real_smooth hUinf hfix (hsU hx)).continuousAt.continuousWithinAt)
      ((heq.real_bijOn hUinf hfix).injOn.mono hsU)
  have htarget := (integrable_transported_real_coordinate_iff heq hV hUinf hfix
    hO (Subset.refl _) w hw hs hsU hf (fun x hx => hg x (hsU hx))).mpr (hi.mono_set hsU)
  obtain ⟨hc, he⟩ := real_gradient_energy_in_complex_coordinates hW himage (image_mono hsU)
    (hv.of_le (by norm_num)) htarget
  rw [← transported_sphereRealFunction_eq] at hc he
  exact ⟨hc, he.trans (integral_transported_real_coordinate heq hV hUinf hfix
    hO (Subset.refl _) w hw hs hsU hf (fun x hx => hg x (hsU hx)))⟩

namespace FiniteTransfer.RealTransferStage

variable {S : Type*} {n : ℕ} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {u : Fin n → (ℝ × ℝ) → ℝ} {a b : Fin n → S → ℝ}
  {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε : ℝ}
  (M : RealTransferStage G π σ u a b Flag O K₀ ε)

/-- The finite target energy away from a retained source set is charged to
original source energy away from that same set, plus the transfer error. -/
theorem transported_energy_away_lt (l : Fin n)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEc : E ⊆ M.core)
    {W : Set ℂ} (hW : W ⊆ Complex.equivRealProdCLM ⁻¹'
      (sphereRealMap M.forward '' (realChartDomain (openCompletedRegion M.terminals.H) \ E))) :
    IntegrableOn (euclideanGradientEnergy
      ((sphereRealFunction (M.functions l) ∘ M.inverse) ∘ ((↑) : ℂ → Sphere))) W ∧
    (∫ z in W, euclideanGradientEnergy
      ((sphereRealFunction (M.functions l) ∘ M.inverse) ∘ ((↑) : ℂ → Sphere)) z) <
      (∫ x in realChartDomain G \ E,
        gradientEnergy (u l) (fun z => sphericalMetricFactor z • 1) x) + ε := by
  let _ : Fintype M.indices := M.finite_indices.fintype
  let A := realChartDomain (openCompletedRegion M.terminals.H)
  have hA : IsOpen A := isOpen_realChartDomain (isOpen_openCompletedRegion M.terminals.H)
  obtain ⟨hi, he⟩ := transported_real_energy_on_source_set M.equivalence
    (isOpen_openCompletedRegion M.terminals.H) M.circle_domain.1 M.source_infty M.principal.1
    (M.functions l) (M.functions_smooth_source l) M.metric_conformal
    (fun x _ => M.metric_pos x) (M.functions_integrable_source l)
    (hA.measurableSet.diff hE) sdiff_subset
  refine ⟨hi.mono_set hW, lt_of_le_of_lt ?_ (M.source_energy l E hE hEc)⟩
  apply le_trans (setIntegral_mono_set hi
    (ae_of_all _ (fun z => euclideanGradientEnergy_nonneg _ z))
    (Eventually.of_forall fun _ hz => hW hz))
  rw [he]
  exact setIntegral_mono_set ((M.integrable l).mono_set sdiff_subset)
    (ae_of_all _ (fun x => gradientEnergy_nonneg _ M.metric_pos x))
    (Eventually.of_forall fun _ hx =>
      ⟨openCompletedRegion_subset_completedRegion M.terminals.H hx.1, hx.2⟩)

end FiniteTransfer.RealTransferStage

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetainedJordanConvergence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Anchors for the Jordan curves of actual finite models

A point of the physical domain on the inside of a retained contour gives
an interior anchor in every sufficiently late model. The proved side
correspondence identifies that side, and local uniform convergence gives
the anchor and boundary convergence needed for the crossing argument.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_domain_point_inside_jordan
    {G : Set Sphere} (hG : IsOpen G) (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    ∃ q : ℂ, (q : Sphere) ∈ G ∧ q ∈ jordanInterior H := by
  obtain ⟨p, hp⟩ := (isConnected_frontier_jordanInterior H).nonempty
  have hpG : p ∈ ((↑) : ℂ → Sphere) ⁻¹' G := hboundary ⟨p, hp, rfl⟩
  exact mem_closure_iff_nhds.mp (frontier_subset_closure hp)
    (((↑) : ℂ → Sphere) ⁻¹' G) ((hG.preimage OnePoint.continuous_coe).mem_nhds hpG)

theorem exists_anchored_retained_jordan_models
    (hsch : PlanarSchoenflies)
    {I : ℕ → Type*} [∀ n, Finite (I n)] (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hTd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (T n i))))
    (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hV : ∀ n, IsOpen (V n)) (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {G : Set Sphere} (hG : IsOpen G) (A : SmoothJordanCore G) (j : Fin A.count)
    (hret : ∀ᶠ n in atTop, A.carrier ⊆ openCompletedRegion (T n))
    (hpoint : ∀ q ∈ G, ∀ᶠ n in atTop, q ∈ openCompletedRegion (T n))
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f n (z : Sphere)))
      F atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (H : ℂ ≃ₜ ℂ)
    (hH : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk j))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior H))
    (hside : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk j))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) :
    ∃ (J : ℕ → ℂ ≃ₜ ℂ) (q : ℂ),
      (q : Sphere) ∈ G ∧ q ∈ jordanInterior (A.disk j) ∧ F q ∈ jordanInterior H ∧
      Continuous (F ∘ A.curve j) ∧
      range (F ∘ A.curve j) = frontier (jordanInterior H) ∧
      TendstoUniformly (fun n s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere)))
        (F ∘ A.curve j) atTop ∧
      Tendsto (fun n => finiteCoord (f n (q : Sphere))) atTop (𝓝 (F q)) ∧
      (∀ᶠ n in atTop, finiteCoord (f n (q : Sphere)) ∈ jordanInterior (J n)) ∧
      (∀ᶠ n in atTop,
        f n '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk j))) =
          ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n))) ∧
      (∀ᶠ n in atTop, range (fun s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere))) =
        frontier (jordanInterior (J n))) := by
  classical
  have hinf (n : ℕ) : OnePoint.infty ∈ openCompletedRegion (T n) := by
    intro h
    obtain ⟨i, z, _, hz⟩ := mem_iUnion.mp h
    exact OnePoint.coe_ne_infty z hz
  have hex (n : ℕ) : ∃ J : Fin A.count → ℂ ≃ₜ ℂ,
      A.carrier ⊆ openCompletedRegion (T n) →
      (∀ i, f n '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i))) ∧
      ∀ i, f n '' (openCompletedRegion (T n) ∩
          (((↑) : ℂ → Sphere) '' jordanInterior (A.disk i))) =
        (f n '' openCompletedRegion (T n)) ∩
          (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
    by_cases hn : A.carrier ⊆ openCompletedRegion (T n)
    · obtain ⟨J, _, _, hb, hs⟩ := exists_matched_image_core_of_continuous_open hsch
        (isOpen_openCompletedRegion (T n)) (isConnected_openCompletedRegion (T n) (hTd n))
        (hinf n) (fun p hp => ((heq n).smooth p hp).1.continuousWithinAt)
        (fun S hS hSQ => (heq n).isOpen_image (hV n) hS hSQ)
        (heq n).bijOn.injOn (hfix n) (A.inDomain hn)
      exact ⟨J, fun _ => ⟨hb, hs⟩⟩
    · exact ⟨fun _ => H, fun h => (hn h).elim⟩
  choose J hJ using hex
  obtain ⟨q, hqG, hqA⟩ := exists_domain_point_inside_jordan hG (A.disk j)
    (A.boundary_subset_domain j)
  have hqH : F q ∈ jordanInterior H := by
    have hq : extendAtInfinity F (q : Sphere) ∈
        (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior H) := by
      rw [← hside]
      exact mem_image_of_mem _ ⟨hqG, q, hqA, rfl⟩
    simpa only [extendAtInfinity_coe, OnePoint.coe_injective.mem_set_image] using hq.2
  have hcurveG (s : Circle) : ((A.curve j s : ℂ) : Sphere) ∈ G := by
    apply A.boundary_subset_domain j
    exact ⟨A.curve j s, (A.boundary j) ▸ mem_range_self s, rfl⟩
  have hγ : Continuous (A.curve j) := (A.embedding j).continuous
  have hγF : Continuous (F ∘ A.curve j) := hF.comp_continuous hγ hcurveG
  have hfront : range (F ∘ A.curve j) = frontier (jordanInterior H) := by
    simpa only [extendAtInfinity_coe, finiteCoord_coe, Function.comp_def] using
      range_finite_image_boundary (A.boundary j) hH
        (fun s => by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
  have hγlim : TendstoUniformly
      (fun n s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere))) (F ∘ A.curve j) atTop := by
    apply tendstoUniformlyOn_univ.mp
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_univ).mp
    exact hlim.comp (A.curve j) (fun s _ => hcurveG s) hγ.continuousOn
  refine ⟨fun n => J n j, q, hqG, hqA, hqH, hγF, hfront, hγlim,
    hlim.tendsto_at hqG, ?_, ?_, ?_⟩
  · filter_upwards [hret, hpoint (q : Sphere) hqG] with n hn hqn
    have ht : f n (q : Sphere) ∈ ((↑) : ℂ → Sphere) '' jordanInterior (J n j) := by
      have hh := mem_image_of_mem (f n) (show (q : Sphere) ∈
        openCompletedRegion (T n) ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk j)) from
          ⟨hqn, q, hqA, rfl⟩)
      rw [(hJ n hn).2 j] at hh
      exact hh.2
    obtain ⟨r, hr, her⟩ := ht
    simpa only [← her, finiteCoord_coe] using hr
  · filter_upwards [hret] with n hn
    exact (hJ n hn).1 j
  · filter_upwards [hret] with n hn
    apply range_finite_image_boundary (A.boundary j) ((hJ n hn).1 j)
    intro s
    exact (heq n).finite_forward (hinf n) (hfix n)
      ((A.inDomain hn).boundary_subset_domain j
        ⟨A.curve j s, (A.boundary j) ▸ mem_range_self s, rfl⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RetainedTestCrossings
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Crossing segments for an actual retained test

The source test has value one on an inner retained contour and zero on
an outer one. Their actual finite-model images produce the common
crossings used in line payment, with anchors derived from source points.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem values_on_image_jordan_boundary
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V)
    {H K : ℂ ≃ₜ ℂ}
    (hsource : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ U)
    (himage : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior K))
    (w : Sphere → ℝ) {c : ℝ} (hvalue : ∀ z ∈ frontier (jordanInterior H), w z = c) :
    frontier (jordanInterior K) ⊆ ((↑) : ℂ → Sphere) ⁻¹' V ∧
      ∀ z ∈ frontier (jordanInterior K), w (fi z) = c := by
  have hpre (z : ℂ) (hz : z ∈ frontier (jordanInterior K)) :
      ∃ p ∈ (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)), f p = z := by
    have hh : (z : Sphere) ∈ f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) := by
      rw [himage]
      exact ⟨z, hz, rfl⟩
    exact hh
  constructor
  · intro z hz
    obtain ⟨p, hp, he⟩ := hpre z hz
    change (z : Sphere) ∈ V
    rw [← he]
    exact heq.mapsTo (hsource hp)
  · intro z hz
    obtain ⟨p, hp, he⟩ := hpre z hz
    have hpinv := heq.left_inv p (hsource hp)
    rw [he] at hpinv
    rw [hpinv]
    obtain ⟨q, hq, rfl⟩ := hp
    exact hvalue q hq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RealMarkedModels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assign the actual countable real-model terminals to their original source ends. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem CountableRealCoordinates.sourceMark_outside
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ) (s : S) : d.sourceMark s ∈ Gᶜ :=
  (Classical.choose_spec (d.labels_dust s)).1

theorem CountableRealCoordinates.sourceMark_image
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ) (s : S) : π (d.sourceMark s) = σ s :=
  (Classical.choose_spec (d.labels_dust s)).2

theorem CountableRealCoordinates.sourceMark_component
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (s : S) : connectedComponentIn Gᶜ (d.sourceMark s) = π ⁻¹' {σ s} := by
  ext x
  constructor
  · intro hx
    have he := (hr (d.sourceMark s) x).mpr (Or.inr ⟨d.sourceMark_outside s, hx⟩)
    exact he.symm.trans (d.sourceMark_image s)
  · intro hx
    have he : π (d.sourceMark s) = π x := (d.sourceMark_image s).trans hx.symm
    rcases (hr (d.sourceMark s) x).mp he with h | h
    · exact h ▸ mem_connectedComponentIn (d.sourceMark_outside s)
    · exact h.2

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RetainedRegionAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact source sets stay outside fixed separated target regions in the actual models. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

/-- d13f23b's public `Set.subset_image_sdiff` (private in our Mathlib 0df444a). -/
theorem _root_.Set.subset_image_sdiff {α β : Type*} (f : α → β) (s t : Set α) :
    f '' s \ f '' t ⊆ f '' (s \ t) := by
  rw [Set.sdiff_subset_iff, ← Set.image_union, Set.union_sdiff_self]
  exact Set.image_mono Set.subset_union_right

noncomputable section

namespace CircleDomainRigidity

theorem eventually_image_compact_avoids_closed
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {K W : Set ℂ}
    (hK : IsCompact K) (hF : ContinuousOn F K) (hW : IsClosed W)
    (hd : Disjoint (F '' K) W) (hlim : TendstoUniformlyOn f F atTop K) :
    ∀ᶠ n in atTop, Disjoint (f n '' K) W := by
  have hsub : F '' K ⊆ Wᶜ := fun _ hx hw => Set.disjoint_left.mp hd hx hw
  obtain ⟨δ, hδ, hsmall⟩ := (hK.image_of_continuousOn hF).exists_thickening_subset_open
    hW.isOpen_compl hsub
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with n hn
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ hz
  apply hsmall ?_ hz
  exact mem_thickening_iff.mpr ⟨F x, mem_image_of_mem _ hx, by simpa only [dist_comm] using hn x hx⟩

namespace FiniteTransfer.AssignedRealModelLimit

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (A : AssignedRealModelLimit M)

theorem eventually_avoids_closed
    {K W : Set ℂ} (hK : IsCompact K) (hKG : K ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hW : IsClosed W) (hd : Disjoint (A.function '' K) W) :
    ∀ᶠ n in atTop, Disjoint
      ((fun z : ℂ => finiteCoord ((M.stages (A.subsequence n)).forward z)) '' K) W := by
  have hF : ContinuousOn A.function K := by
    intro z hz
    have h := continuousAt_finite_part_of_conformalAt (A.conformal.1 _ (hKG hz))
      (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using h.continuousWithinAt
  exact eventually_image_compact_avoids_closed hK hF hW hd
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (A.converges.mono hKG))

theorem eventually_region_over_source_complement
    {K W : Set ℂ} (hK : IsCompact K) (hKG : K ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hW : IsClosed W) (hd : Disjoint (A.function '' K) W) :
    ∀ᶠ n in atTop,
      ((((↑) : ℂ → Sphere) ⁻¹' (M.stages (A.subsequence n)).domain) ∩ W) ⊆
        Complex.equivRealProdCLM ⁻¹'
          (sphereRealMap (M.stages (A.subsequence n)).forward ''
            (realChartDomain (openCompletedRegion (M.stages (A.subsequence n)).terminals.H) \
              (Complex.equivRealProdCLM '' K))) := by
  filter_upwards [A.eventually_avoids_closed hK hKG hW hd] with n hn
  intro z hz
  have hzreal : Complex.equivRealProdCLM z ∈ realChartDomain (M.stages (A.subsequence n)).domain := by
    simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz.1
  have hbij := (M.stages (A.subsequence n)).equivalence.real_bijOn
    (M.stages (A.subsequence n)).source_infty (M.stages (A.subsequence n)).principal.1
  have himage := hbij.surjOn hzreal
  apply subset_image_sdiff _ _ _ ⟨himage, ?_⟩
  rintro ⟨x, ⟨w, hw, rfl⟩, he⟩
  have hweq : finiteCoord ((M.stages (A.subsequence n)).forward w) = z := by
    apply Complex.equivRealProdCLM.injective
    simpa only [sphereRealMap, ContinuousLinearEquiv.symm_apply_apply] using he
  exact Set.disjoint_left.mp hn ⟨w, hw, hweq⟩ hz.2

end FiniteTransfer.AssignedRealModelLimit

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FlexibleCirclePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.axisSwap_horizontalLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Line payment is independent of which endpoint carries the value zero. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem line_payment_through_disks_one_zero
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {y a b : ℝ} (hab : a < b)
    (ha : a ∈ diskLineDomain c r y) (hb : b ∈ diskLineDomain c r y)
    {f ρ : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (diskLineDomain c r y))
    (hone : f a = 1) (hzero : f b = 0)
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hmajor : ∀ x ∈ Icc a b ∩ diskLineDomain c r y, |deriv f x| ≤ ρ x)
    (hcluster : ∀ i p q u v,
      (⟨p, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      (⟨q, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[diskLineDomain c r y] p) f →
      MapClusterPt v (𝓝[diskLineDomain c r y] q) f → |v - u| ≤ A i) :
    1 ≤ (∫ x, ρ x) +
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
  apply line_payment_through_disks c r A hr hA hdisj hab ha hb (f := fun x => 1 - f x)
    (contDiffOn_const.sub hf) (by simp [hone]) (by simp [hzero]) hρ hpos
  · intro x hx
    simpa only [deriv_const_sub, abs_neg] using hmajor x hx
  · intro i p q u v hp hq hu hv
    have hc : Continuous (fun t : ℝ => 1 - t) := continuous_const.sub continuous_id
    have hu' : MapClusterPt (1 - u) (𝓝[diskLineDomain c r y] p) f := by
      simpa only [Function.comp_def, sub_sub_cancel] using hu.continuousAt_comp hc.continuousAt
    have hv' : MapClusterPt (1 - v) (𝓝[diskLineDomain c r y] q) f := by
      simpa only [Function.comp_def, sub_sub_cancel] using hv.continuousAt_comp hc.continuousAt
    have h := hcluster i p q (1 - u) (1 - v) hp hq hu' hv'
    rw [show (1 - v) - (1 - u) = u - v by ring, abs_sub_comm] at h
    exact h

theorem parallel_line_payment_in_region_either_order
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v (⋃ i, closedBall (c i) (r i))ᶜ)
    {W : Set ℂ} (hW : MeasurableSet W) (hWB : W ⊆ closedBall 0 L)
    (henergy : IntegrableOn (euclideanGradientEnergy v) W)
    (hcluster : ∀ i p q u w, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p) v →
      MapClusterPt w (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q) v → |w - u| ≤ A i)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ a b : ℝ, a < b ∧ a ∈ diskLineDomain c r y ∧
      b ∈ diskLineDomain c r y ∧ horizontalLine y a ∈ closedBall 0 L ∧
      horizontalLine y b ∈ closedBall 0 L ∧ ((v (horizontalLine y a) = 0 ∧ v (horizontalLine y b) = 1) ∨
        (v (horizontalLine y a) = 1 ∧ v (horizontalLine y b) = 0)) ∧
      ∀ x ∈ Icc a b ∩ diskLineDomain c r y, horizontalLine y x ∈ W) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in W, euclideanGradientEnergy v z) +
      ∑ i, 2 * r i * A i := by
  let U := (⋃ i, closedBall (c i) (r i))ᶜ
  let E := W
  let ρ := E.indicator (euclideanGradientNorm v)
  have hU : IsOpen U := (isClosed_iUnion_of_finite (fun i => isClosed_closedBall)).isOpen_compl
  have hE : MeasurableSet E := hW
  have hρ : MemLp ρ 2 volume := memLp_indicator_euclideanGradientNorm hE henergy
  have hρpos : ∀ z, 0 ≤ ρ z := fun _ => indicator_nonneg
    (fun z _ => Real.sqrt_nonneg (euclideanGradientEnergy v z)) _
  have hρsupport : support ρ ⊆ closedBall 0 L := by
    intro z hz
    by_contra h
    exact hz (indicator_of_notMem (fun he : z ∈ E => h (hWB he)) _)
  have hρint := (integral_le_disk_L2 hL hρ hρpos hρsupport).1
  have hp : Integrable (fun p : ℝ × ℝ => ρ ⟨p.1, p.2⟩) :=
    ((Complex.volume_preserving_equiv_real_prod.symm
      Complex.measurableEquivRealProd).integrable_comp hρint.aestronglyMeasurable).mpr hρint
  have hJsub : J ⊆ Icc (-L) L := by
    intro y hy
    obtain ⟨a, _, _, _, _, ha, _⟩ := hcross y hy
    simpa only [Complex.zero_im, zero_sub, zero_add] using
      (horizontal_line_meets_closedBall (0 : ℂ)).mp ⟨a, ha⟩
  have hJfinite : volume J ≠ ⊤ := ne_of_lt ((measure_mono hJsub).trans_lt measure_Icc_lt_top)
  have hpay : ∀ᵐ y ∂volume.restrict J, 1 ≤ (∫ x : ℝ, ρ ⟨x, y⟩) +
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
    filter_upwards [ae_restrict_of_ae hp.prod_left_ae, ae_restrict_mem hJ] with y hiy hy
    obtain ⟨a, b, hab, haD, hbD, haB, hbB, hvalues, hsegment⟩ := hcross y hy
    have hf : ContDiffOn ℝ 1 (v ∘ horizontalLine y) (diskLineDomain c r y) :=
      hv.comp (contDiff_horizontalLine y).contDiffOn (fun _ hx => hx)
    have hmajor : ∀ x ∈ Icc a b ∩ diskLineDomain c r y,
        |deriv (v ∘ horizontalLine y) x| ≤ ρ (horizontalLine y x) := by
      intro x hx
      have hxE : horizontalLine y x ∈ E := hsegment x hx
      change |deriv (v ∘ horizontalLine y) x| ≤ E.indicator (euclideanGradientNorm v) (horizontalLine y x)
      rw [indicator_of_mem hxE]
      exact horizontal_derivative_le_gradient ((hv.contDiffAt (hU.mem_nhds hx.2)).differentiableAt (by norm_num))
    have hcl : ∀ i p q u w,
        (⟨p, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
        (⟨q, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
        MapClusterPt u (𝓝[diskLineDomain c r y] p) (v ∘ horizontalLine y) →
        MapClusterPt w (𝓝[diskLineDomain c r y] q) (v ∘ horizontalLine y) → |w - u| ≤ A i := by
      intro i p q u w hp hq hu hw
      exact hcluster i _ _ u w hp hq (horizontal_cluster_is_planar hu)
        (horizontal_cluster_is_planar hw)
    rcases hvalues with ⟨hzero, hone⟩ | ⟨hone, hzero⟩
    · exact line_payment_through_disks c r A hr hA hdisj hab haD hbD hf hzero hone hiy
        (fun x => hρpos _) hmajor hcl
    · exact line_payment_through_disks_one_zero c r A hr hA hdisj hab haD hbD hf hone hzero hiy
        (fun x => hρpos _) hmajor hcl
  have h := integrated_parallel_line_payment c r A hJfinite hr hA hL hρ hρpos hρsupport hpay
  have hsq : (fun z => ρ z ^ 2) = E.indicator (euclideanGradientEnergy v) := by
    funext z
    by_cases hz : z ∈ E
    · simp only [ρ, indicator_of_mem hz, euclideanGradientNorm_sq]
    · simp only [ρ, indicator_of_notMem hz, zero_pow (by norm_num : 2 ≠ 0)]
  rw [hsq, integral_indicator hE] at h
  exact h


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RotatedRealEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary planar rotation preserves the real gradient energy used in local crossing estimates. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

private theorem real_linear_complex_expansion (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = z.re * L 1 + z.im * L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    L z = L (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg L hz
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul]

theorem euclideanGradientEnergy_rotation (a : Circle) {v : ℂ → ℝ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (rotation a z)) :
    euclideanGradientEnergy (v ∘ rotation a) z = euclideanGradientEnergy v (rotation a z) := by
  have hd := (hv.hasFDerivAt.comp z (rotation a).hasFDerivAt).fderiv
  unfold euclideanGradientEnergy
  rw [hd]
  change (fderiv ℝ v (rotation a z) (rotation a 1)) ^ 2 +
    (fderiv ℝ v (rotation a z) (rotation a Complex.I)) ^ 2 = _
  rw [real_linear_complex_expansion _ (rotation a 1),
    real_linear_complex_expansion _ (rotation a Complex.I)]
  simp only [rotation_apply, mul_one, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, add_zero]
  have ha : (a : ℂ).re ^ 2 + (a : ℂ).im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, Circle.normSq_coe, pow_two] using
      (Complex.normSq_apply (a : ℂ)).symm.trans (Circle.normSq_coe a)
  linear_combination ((fderiv ℝ v ((a : ℂ) * z) 1) ^ 2 +
    (fderiv ℝ v ((a : ℂ) * z) Complex.I) ^ 2) * ha

theorem integral_energy_rotation_on (a : Circle)
    {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v U)
    {s : Set ℂ} (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hi : IntegrableOn (euclideanGradientEnergy v) s) :
    IntegrableOn (euclideanGradientEnergy (v ∘ rotation a)) (rotation a ⁻¹' s) ∧
      (∫ z in rotation a ⁻¹' s, euclideanGradientEnergy (v ∘ rotation a) z) =
        ∫ z in s, euclideanGradientEnergy v z := by
  have hm := (rotation a).measurePreserving.restrict_preimage_emb
    (rotation a).toMeasurableEquiv.measurableEmbedding s
  have hc : IntegrableOn (euclideanGradientEnergy v ∘ rotation a) (rotation a ⁻¹' s) :=
    (hm.integrable_comp hi.aestronglyMeasurable).mpr hi
  have he : euclideanGradientEnergy (v ∘ rotation a) =ᵐ[volume.restrict (rotation a ⁻¹' s)]
      euclideanGradientEnergy v ∘ rotation a := by
    filter_upwards [ae_restrict_mem (hs.preimage (rotation a).continuous.measurable)] with z hz
    exact euclideanGradientEnergy_rotation a
      ((hv.contDiffAt (hU.mem_nhds (hsU hz))).differentiableAt (by norm_num))
  refine ⟨hc.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  exact (rotation a).measurePreserving.setIntegral_preimage_emb
    (rotation a).toMeasurableEquiv.measurableEmbedding (euclideanGradientEnergy v) s

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RotatedLocalizedPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localized line payment in any fixed direction, with unchanged source energy and hole costs. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem rotated_line_payment_in_region
    (a : Circle) {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall 0 L)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v (⋃ i, closedBall (c i) (r i))ᶜ)
    {W : Set ℂ} (hW : MeasurableSet W) (hWU : W ⊆ (⋃ i, closedBall (c i) (r i))ᶜ)
    (hWB : W ⊆ closedBall 0 L) (henergy : IntegrableOn (euclideanGradientEnergy v) W)
    (hcluster : ∀ i p q u w, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p) v →
      MapClusterPt w (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q) v → |w - u| ≤ A i)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s ≠ t ∧
      rotatedLine a y s ∈ (⋃ i, closedBall (c i) (r i))ᶜ ∧
      rotatedLine a y t ∈ (⋃ i, closedBall (c i) (r i))ᶜ ∧
      rotatedLine a y s ∈ closedBall 0 L ∧ rotatedLine a y t ∈ closedBall 0 L ∧
      v (rotatedLine a y s) = 0 ∧ v (rotatedLine a y t) = 1 ∧
      ∀ x ∈ uIcc s t, rotatedLine a y x ∈ (⋃ i, closedBall (c i) (r i))ᶜ →
        rotatedLine a y x ∈ W) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in W, euclideanGradientEnergy v z) + 2 * L * Real.sqrt (∑ i, A i ^ 2) := by
  let R := rotation a
  let U := (⋃ i, closedBall (c i) (r i))ᶜ
  let V := (⋃ i, closedBall (R.symm (c i)) (r i))ᶜ
  have hU : IsOpen U := (isClosed_iUnion_of_finite fun _ => isClosed_closedBall).isOpen_compl
  have hVU : V = R ⁻¹' U := by
    simp only [V, U, preimage_compl, preimage_iUnion, R.preimage_closedBall]
  have hvV : ContDiffOn ℝ 1 (v ∘ R) V := by
    rw [hVU]
    exact hv.comp R.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hx => hx)
  obtain ⟨hiV, heV⟩ := integral_energy_rotation_on a hU hv hW hWU henergy
  have hball (z : ℂ) : z ∈ R ⁻¹' closedBall (0 : ℂ) L ↔ z ∈ closedBall 0 L := by
    simp only [R.preimage_closedBall, map_zero]
  have hdV : Pairwise (Disjoint on fun i => closedBall (R.symm (c i)) (r i)) := by
    intro i j hij
    simpa only [R.preimage_closedBall] using (hdisj hij).preimage R
  have hclV : ∀ i p q u w, p ∈ closedBall (R.symm (c i)) (r i) →
      q ∈ closedBall (R.symm (c i)) (r i) →
      MapClusterPt u (𝓝[V] p) (v ∘ R) → MapClusterPt w (𝓝[V] q) (v ∘ R) →
      |w - u| ≤ A i := by
    intro i p q u w hp hq hu hw
    apply hcluster i (R p) (R q) u w
    · change p ∈ R ⁻¹' closedBall (c i) (r i)
      rwa [R.preimage_closedBall]
    · change q ∈ R ⁻¹' closedBall (c i) (r i)
      rwa [R.preimage_closedBall]
    · apply MapClusterPt.of_comp _ hu
      rw [hVU]
      exact tendsto_nhdsWithin_iff.mpr
        ⟨R.continuous.continuousAt.mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩
    · apply MapClusterPt.of_comp _ hw
      rw [hVU]
      exact tendsto_nhdsWithin_iff.mpr
        ⟨R.continuous.continuousAt.mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩
  have hp : (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in R ⁻¹' W, euclideanGradientEnergy (v ∘ R) z) + ∑ i, 2 * r i * A i :=
    parallel_line_payment_in_region_either_order
      (fun i => R.symm (c i)) r A hr hA hL hdV hvV
      (hW.preimage R.continuous.measurable)
      (fun z hz => (hball z).mp (hWB hz)) hiV hclV hJ ?_
  · rw [heV] at hp
    have ht := parallel_disk_tolls_le_square_norm c r A hr hL hdisj hsub
    rw [integral_parallel_disk_tolls c r A hr] at ht
    exact hp.trans (add_le_add le_rfl ht)
  intro y hy
  obtain ⟨s, t, hst, hs, ht, hsB, htB, hs0, ht1, hseg⟩ := hcross y hy
  have hmem (x : ℝ) : horizontalLine y x ∈ V ↔ rotatedLine a y x ∈ U := by
    rw [hVU]
    rfl
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · refine ⟨s, t, hlt, (hmem s).mpr hs, (hmem t).mpr ht,
      (hball _).mp hsB, (hball _).mp htB, Or.inl ⟨hs0, ht1⟩, ?_⟩
    intro x hx
    exact hseg x (Icc_subset_uIcc hx.1) ((hmem x).mp hx.2)
  · refine ⟨t, s, hgt, (hmem t).mpr ht, (hmem s).mpr hs,
      (hball _).mp htB, (hball _).mp hsB, Or.inr ⟨ht1, hs0⟩, ?_⟩
    intro x hx
    exact hseg x (Icc_subset_uIcc' hx.1) ((hmem x).mp hx.2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RotatedRealPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary-direction localized payment for the actual assigned finite models and their limit. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity
open FiniteTransfer

theorem TerminalComponentAssignment.rotated_line_payment_in_region
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V) (rot : Circle)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ V)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    (w : (ℝ × ℝ) → ℝ) {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O) (hw : ContinuousOn w O)
    (hv : ContDiffOn ℝ 1 ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))
      (((↑) : ℂ → Sphere) ⁻¹' V))
    {W : Set ℂ} (hW : MeasurableSet W) (hWD : W ⊆ ((↑) : ℂ → Sphere) ⁻¹' V) (hWB : W ⊆ closedBall 0 L)
    (henergy : IntegrableOn
      (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))) W)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s ≠ t ∧
      (rotatedLine rot y s : Sphere) ∈ V ∧ (rotatedLine rot y t : Sphere) ∈ V ∧
      rotatedLine rot y s ∈ closedBall 0 L ∧ rotatedLine rot y t ∈ closedBall 0 L ∧
      sphereRealFunction w (fi (rotatedLine rot y s)) = 0 ∧
      sphereRealFunction w (fi (rotatedLine rot y t)) = 1 ∧
      ∀ x ∈ uIcc s t, (rotatedLine rot y x : Sphere) ∈ V → rotatedLine rot y x ∈ W) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in W,
        euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) z) +
      2 * L * Real.sqrt (∑ i, Metric.diam (w '' frontier (realJordanInterior (T i))) ^ 2) := by
  obtain ⟨c, r, hr, he, hd, hU⟩ := a.exists_disk_coordinates hV hinf
  let A : I → ℝ := fun i => Metric.diam (w '' frontier (realJordanInterior (T i)))
  have hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall (0 : ℂ) L :=
    fun i => terminal_disk_subset_bound (he i) hbound
  have hcl : ∀ i p q u v, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p)
        ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) →
      MapClusterPt v (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q)
        ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) → |v - u| ≤ A i := by
    intro i p q u v hp hq hu hv
    apply a.real_planar_cluster_gap_le hf i w hO (hTO i) hw
    · rw [he i]
      exact mem_image_of_mem _ hp
    · rw [he i]
      exact mem_image_of_mem _ hq
    · simpa only [hU] using hu
    · simpa only [hU] using hv
  have hv' : ContDiffOn ℝ 1 ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))
      (⋃ j, closedBall (c j) (r j))ᶜ := by simpa only [hU] using hv
  apply CircleDomainRigidity.rotated_line_payment_in_region rot c r A hr
    (fun _ => Metric.diam_nonneg) hL hd hsub hv' hW (by simpa only [hU] using hWD) hWB henergy hcl hJ
  intro y hy
  obtain ⟨s, t, hst, hsV, htV, hsB, htB, hs0, ht1, hsegment⟩ := hcross y hy
  refine ⟨s, t, hst, ?_, ?_, hsB, htB, hs0, ht1, ?_⟩
  · rw [← hU]
    exact hsV
  · rw [← hU]
    exact htV
  · intro x hx hxd
    apply hsegment x hx
    change rotatedLine rot y x ∈ ((↑) : ℂ → Sphere) ⁻¹' V
    rwa [hU]

end CircleDomainRigidity

namespace CircleDomainRigidity.FiniteTransfer.RealTransferStage


variable {S : Type*} {n : ℕ} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {u : Fin n → (ℝ × ℝ) → ℝ} {a b : Fin n → S → ℝ}
  {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε : ℝ}
  (M : RealTransferStage G π σ u a b Flag O K₀ ε)

theorem rotated_localized_line_payment
    (T : TerminalComponentAssignment M.terminals.H M.forward M.domain)
    (rot : Circle) (l : Fin n) {L : ℝ} (hL : 0 ≤ L)
    (hbound : M.domainᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEc : E ⊆ M.core)
    {W : Set ℂ} (hW : MeasurableSet W) (hWD : W ⊆ ((↑) : ℂ → Sphere) ⁻¹' M.domain) (hWB : W ⊆ closedBall 0 L)
    (hWsrc : W ⊆ Complex.equivRealProdCLM ⁻¹'
      (sphereRealMap M.forward '' (realChartDomain (openCompletedRegion M.terminals.H) \ E)))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s ≠ t ∧
      (rotatedLine rot y s : Sphere) ∈ M.domain ∧ (rotatedLine rot y t : Sphere) ∈ M.domain ∧
      rotatedLine rot y s ∈ closedBall 0 L ∧ rotatedLine rot y t ∈ closedBall 0 L ∧
      sphereRealFunction (M.functions l) (M.inverse (rotatedLine rot y s)) = 0 ∧
      sphereRealFunction (M.functions l) (M.inverse (rotatedLine rot y t)) = 1 ∧
      ∀ x ∈ uIcc s t, (rotatedLine rot y x : Sphere) ∈ M.domain → rotatedLine rot y x ∈ W) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      ((∫ x in realChartDomain G \ E,
        gradientEnergy (u l) (fun z => sphericalMetricFactor z • 1) x) + ε) +
      2 * L * (Real.sqrt (∑' s, (b l s - a l s) ^ 2) + ε) := by
  let _ : Fintype M.indices := M.finite_indices.fintype
  obtain ⟨hv, _, _⟩ := transported_real_energy M.equivalence
    (isOpen_openCompletedRegion M.terminals.H) M.circle_domain.1 M.source_infty M.principal.1
    (M.functions l) (M.functions_smooth_source l) M.metric_conformal
    (fun x _ => M.metric_pos x) (M.functions_integrable_source l)
  obtain ⟨hi, henergy⟩ := M.transported_energy_away_lt l hE hEc hWsrc
  have hp := T.rotated_line_payment_in_region rot M.equivalence M.circle_domain
    (M.equivalence.infty_mem_target M.source_infty M.principal.1) hL hbound
    (M.functions l) M.extension_open M.terminal_frontier_extension
    (M.functions_smooth l).continuousOn hv hW hWD hWB hi hJ hcross
  have hosc : Real.sqrt (∑ i : M.indices,
      diam (M.functions l '' frontier (realJordanInterior (M.terminals.H i))) ^ 2) ≤
      Real.sqrt (∑' s, (b l s - a l s) ^ 2) + ε := by
    simpa only [terminalOscillation, tsum_fintype] using (M.oscillation l).le
  exact hp.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt henergy.le)
      (mul_nonneg (Real.sqrt_nonneg _) hL))
    (mul_le_mul_of_nonneg_left hosc (mul_nonneg (by norm_num) hL)))

end CircleDomainRigidity.FiniteTransfer.RealTransferStage

namespace CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit


variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (A : AssignedRealModelLimit M)

theorem rotated_localized_line_payment
    (harea : ExteriorCoefficientAreaTheorem) (hε : Tendsto ε atTop (𝓝 0))
    (rot : Circle) (l : ℕ) {L : ℝ} (hL : 3 * M.radius ≤ L)
    {K : Set Sphere} (hK : IsCompact K) (hKG : K ⊆ G)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEK : E ⊆ realChartDomain K)
    (W : ℕ → Set ℂ) (hW : ∀ n, MeasurableSet (W n))
    (hWD : ∀ n, W n ⊆ ((↑) : ℂ → Sphere) ⁻¹' (M.stages (A.subsequence n)).domain)
    (hWB : ∀ n, W n ⊆ closedBall 0 L)
    (hWsrc : ∀ᶠ n in atTop, W n ⊆ Complex.equivRealProdCLM ⁻¹'
      (sphereRealMap (M.stages (A.subsequence n)).forward ''
        (realChartDomain (openCompletedRegion (M.stages (A.subsequence n)).terminals.H) \ E)))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J, ∃ s t : ℝ, s ≠ t ∧
      (rotatedLine rot y s : Sphere) ∈ (M.stages (A.subsequence n)).domain ∧
      (rotatedLine rot y t : Sphere) ∈ (M.stages (A.subsequence n)).domain ∧
      rotatedLine rot y s ∈ closedBall 0 L ∧ rotatedLine rot y t ∈ closedBall 0 L ∧
      sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
        ((M.stages (A.subsequence n)).inverse (rotatedLine rot y s)) = 0 ∧
      sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
        ((M.stages (A.subsequence n)).inverse (rotatedLine rot y t)) = 1 ∧
      ∀ x ∈ uIcc s t, (rotatedLine rot y x : Sphere) ∈ (M.stages (A.subsequence n)).domain →
        rotatedLine rot y x ∈ W n) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ x in realChartDomain G \ E,
        gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * L * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  let E₀ := ∫ x in realChartDomain G \ E,
    gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x
  let B := Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2)
  have hL0 : 0 ≤ L := (mul_nonneg (by norm_num) M.radius_pos.le).trans hL
  have hbound (n : ℕ) : (M.stages (A.subsequence n)).domainᶜ ⊆
      ((↑) : ℂ → Sphere) '' closedBall 0 L := by
    have h := (normalized_model_uniform_bound harea (M.stages (A.subsequence n)).equivalence
      (M.stages (A.subsequence n)).circle_domain.1 M.radius_pos
      ((M.exterior_core (A.subsequence n)).trans (M.core_model (A.subsequence n)))
      ((M.core_conformal (A.subsequence n)).mono
        ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans
          (M.exterior_core (A.subsequence n))))
      (M.stages (A.subsequence n)).principal).1
    exact fun p hp => image_mono (closedBall_subset_closedBall hL) (h p hp)
  have hpay : ∀ᶠ n in atTop, (volume J).toReal ≤
      Real.sqrt Real.pi * L * Real.sqrt (E₀ + ε (A.subsequence n)) +
      2 * L * (B + ε (A.subsequence n)) := by
    filter_upwards [A.strict.tendsto_atTop (M.eventually_core_contains hK hKG),
      A.strict.tendsto_atTop (prefixIndex_eq l), hWsrc, hcross] with n hn hl hsrc hcr
    have hec : E ⊆ (M.stages (A.subsequence n)).core := by
      intro x hx
      apply interior_subset ((M.stages (A.subsequence n)).core_contains ?_)
      exact preimage_mono hn (hEK hx)
    have hp := (M.stages (A.subsequence n)).rotated_localized_line_payment
      (A.assignment (A.subsequence n)) rot (prefixIndex l (A.subsequence n)) hL0 (hbound n)
      hE hec (hW n) (hWD n) (hWB n) hsrc hJ hcr
    change (prefixIndex l (A.subsequence n)).val = l at hl
    simpa only [E₀, B, hl] using hp
  have ht₀ : Tendsto (fun n => E₀ + ε (A.subsequence n)) atTop (𝓝 E₀) := by
    simpa only [add_zero, Function.comp_def] using tendsto_const_nhds.add (hε.comp A.strict.tendsto_atTop)
  have hs : Tendsto (fun n => Real.sqrt (E₀ + ε (A.subsequence n))) atTop (𝓝 (Real.sqrt E₀)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp ht₀
  have ht : Tendsto (fun n => Real.sqrt Real.pi * L * Real.sqrt (E₀ + ε (A.subsequence n)) +
      2 * L * (B + ε (A.subsequence n))) atTop
      (𝓝 (Real.sqrt Real.pi * L * Real.sqrt E₀ + 2 * L * B)) := by
    simpa only [add_zero, Function.comp_def] using (hs.const_mul (Real.sqrt Real.pi * L)).add
      ((tendsto_const_nhds.add (hε.comp A.strict.tendsto_atTop)).const_mul (2 * L))
  exact ge_of_tendsto ht hpay

theorem rotated_line_payment_away_from_compact
    (harea : ExteriorCoefficientAreaTheorem) (hε : Tendsto ε atTop (𝓝 0))
    (rot : Circle) (l : ℕ) {L : ℝ} (hL : 3 * M.radius ≤ L)
    {K W : Set ℂ} (hK : IsCompact K) (hKG : K ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hW : IsClosed W) (hWB : W ⊆ closedBall 0 L)
    (hd : Disjoint (A.function '' K) W)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J, ∃ s t : ℝ, s ≠ t ∧
      (rotatedLine rot y s : Sphere) ∈ (M.stages (A.subsequence n)).domain ∧
      (rotatedLine rot y t : Sphere) ∈ (M.stages (A.subsequence n)).domain ∧
      rotatedLine rot y s ∈ closedBall 0 L ∧ rotatedLine rot y t ∈ closedBall 0 L ∧
      sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
        ((M.stages (A.subsequence n)).inverse (rotatedLine rot y s)) = 0 ∧
      sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
        ((M.stages (A.subsequence n)).inverse (rotatedLine rot y t)) = 1 ∧
      ∀ x ∈ uIcc s t, (rotatedLine rot y x : Sphere) ∈ (M.stages (A.subsequence n)).domain →
        rotatedLine rot y x ∈ W) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' K),
        gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * L * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  let V (n : ℕ) : Set ℂ :=
    (((↑) : ℂ → Sphere) ⁻¹' (M.stages (A.subsequence n)).domain) ∩ W
  have hEK : Complex.equivRealProdCLM '' K ⊆ realChartDomain (((↑) : ℂ → Sphere) '' K) := by
    rintro x ⟨z, hz, rfl⟩
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ ((↑) : ℂ → Sphere) '' K
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact mem_image_of_mem _ hz
  apply A.rotated_localized_line_payment harea hε rot l hL (hK.image OnePoint.continuous_coe)
    (by rintro _ ⟨z, hz, rfl⟩; exact hKG hz)
    (hK.image Complex.equivRealProdCLM.continuous).measurableSet hEK V
    (fun n => (((M.stages (A.subsequence n)).circle_domain.1.preimage
      OnePoint.continuous_coe).measurableSet.inter hW.measurableSet))
    (fun _ => inter_subset_left)
    (fun _ => inter_subset_right.trans hWB)
    (A.eventually_region_over_source_complement hK hKG hW hd) hJ
  filter_upwards [hcross] with n hn
  intro y hy
  obtain ⟨s, t, hst, hsD, htD, hsB, htB, hs0, ht1, hsegment⟩ := hn y hy
  refine ⟨s, t, hst, hsD, htD, hsB, htB, hs0, ht1, ?_⟩
  intro x hx hxd
  exact ⟨hxd, hsegment x hx hxd⟩

end CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RealTargetEnds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full corresponding target ends and their collapse by actual source tests. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

namespace RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

theorem cap_antitone : Antitone (fun n => closedTerminalCap (L.contours n (E.address n))) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (E.nested n).trans (image_mono subset_closure)

theorem infinity_not_mem : OnePoint.infty ∉
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point := by
  intro h
  have hinf : OnePoint.infty ∈ G := M.core_source 0 (M.plane_core 0 (Or.inr rfl))
  apply connectedComponentIn_subset _ _ h
  exact ⟨OnePoint.infty, hinf, by simp⟩

theorem sphere_image_plane : ((↑) : ℂ → Sphere) '' E.plane =
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point := by
  apply image_preimage_eq_of_subset
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact (E.infinity_not_mem hp).elim
  | coe z => exact ⟨z, rfl⟩

theorem plane_compact : IsCompact E.plane := by
  apply isCompact_finite_preimage _ E.infinity_not_mem
  rw [E.target]
  exact isClosed_iInter fun n => (isCompact_closedTerminalCap _).isClosed

theorem plane_connected : IsConnected E.plane := by
  have hc : IsConnected (((↑) : ℂ → Sphere) '' E.plane) := by
    rw [E.sphere_image_plane]
    exact isConnected_connectedComponentIn_iff.mpr E.outside
  refine ⟨?_, OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
    hc.isPreconnected⟩
  obtain ⟨p, z, hz, _⟩ := hc.nonempty
  exact ⟨z, hz⟩

end RealTargetEnd

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RealEndCorrespondence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every target end has a source address, and that address identifies its marked disk. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (L : AssignedRealModelLimit M)

namespace RealTargetEnd

variable {L} {q : Sphere} (E : RealTargetEnd L q)

theorem marked_disk_subset
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {s : S} (hqs : π q = σ s) :
    ((↑) : ℂ → Sphere) '' Metric.closedBall (L.center s) (L.radius s) ⊆
      connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point := by
  obtain ⟨b, p, _, hs, ht, hdisk, _⟩ := L.marked s
  have hqm : q ∈ connectedComponentIn Gᶜ (d.sourceMark s) := by
    rw [d.sourceMark_component hr s]
    exact hqs
  have hqE : q ∈ ⋂ n, closedTerminalCap ((L.cores n).disk (E.address n)) :=
    E.source ▸ mem_connectedComponentIn hq
  have hqb : q ∈ ⋂ n, closedTerminalCap ((L.cores n).disk (b n)) := hs ▸ hqm
  have hb (n : ℕ) : b n = E.address n := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_closedTerminalCaps (L.cores n).disk
      (L.cores n).disjoint hne) (mem_iInter.mp hqb n) (mem_iInter.mp hqE n)
  have hbe : b = E.address := funext hb
  rw [hbe] at ht
  exact ht.trans E.target.symm ▸ hdisk

end RealTargetEnd

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionGeometry
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial geometric localization of a marked component protruding beyond its round disk. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

/-- A compact planar set extending beyond a round disk has a boundary point
beyond that disk. No boundary regularity is required. -/
theorem exists_frontier_point_outside_closedBall
    {K : Set ℂ} (hK : IsCompact K) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hnot : ¬ K ⊆ closedBall c r) :
    ∃ x ∈ frontier K, r < dist x c := by
  obtain ⟨y, hy, hyn⟩ := Set.not_subset.mp hnot
  have hyr : r < ‖y - c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hyn
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn ⟨y, hy⟩
    ((continuous_id.sub continuous_const).norm.continuousOn)
  have hxr : r < ‖x - c‖ := hyr.trans_le (hmax hy)
  have hd : 0 < ‖x - c‖ := hr.trans_lt hxr
  refine ⟨x, ⟨subset_closure hx, ?_⟩, ?_⟩
  · intro hi
    obtain ⟨δ, hδ, hδK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
    let t := δ / (2 * ‖x - c‖)
    have ht : 0 < t := div_pos hδ (mul_pos (by norm_num) hd)
    have htval : t * ‖x - c‖ = δ / 2 := by
      dsimp only [t]
      field_simp
    let z : ℂ := x + t • (x - c)
    have hzx : z - x = t • (x - c) := by dsimp only [z]; abel
    have hzc : z - c = (1 + t) • (x - c) := by dsimp only [z]; module
    have hzδ : z ∈ ball x δ := by
      rw [mem_ball, dist_eq_norm, hzx, norm_smul, Real.norm_eq_abs, abs_of_pos ht, htval]
      linarith
    have hh : ‖z - c‖ ≤ ‖x - c‖ := hmax (hδK hzδ)
    rw [hzc, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + t)] at hh
    nlinarith [mul_pos ht hd]
  · simpa only [dist_eq_norm] using hxr

/-- Every boundary point of a complementary component can be approached
from the planar domain. -/
theorem frontier_complement_component_subset_closure
    {U : Set ℂ} (hU : IsOpen U) {q : ℂ} (hq : q ∈ Uᶜ) :
    frontier (connectedComponentIn Uᶜ q) ⊆ closure U := by
  have hK : IsClosed (connectedComponentIn Uᶜ q) := by
    rw [connectedComponentIn_eq_image hq]
    exact hU.isClosed_compl.isClosedMap_subtype_val _ isClosed_connectedComponent
  intro x hx
  have hxK : x ∈ connectedComponentIn Uᶜ q := hK.closure_eq ▸ hx.1
  by_contra hxc
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (isClosed_closure.isOpen_compl.mem_nhds hxc)
  have hballU : ball x δ ⊆ Uᶜ := by
    intro z hz hzu
    exact hball hz (subset_closure hzu)
  have hballK := (convex_ball x δ).isPreconnected.subset_connectedComponentIn
    (mem_ball_self hδ) hballU
  rw [← connectedComponentIn_eq hxK] at hballK
  exact hx.2 (interior_maximal hballK isOpen_ball (mem_ball_self hδ))

/-- A genuine closed domain ball can be placed arbitrarily near a boundary
point of a complementary component. -/
theorem exists_domain_ball_near_component_frontier
    {U : Set ℂ} (hU : IsOpen U) {q : ℂ} (hq : q ∈ Uᶜ)
    {x : ℂ} (hx : x ∈ frontier (connectedComponentIn Uᶜ q))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (a : ℂ) (s : ℝ), 0 < s ∧ closedBall a s ⊆ U ∩ ball x ρ := by
  have hxc := frontier_complement_component_subset_closure hU hq hx
  obtain ⟨a, ha, hax⟩ := Metric.mem_closure_iff.mp hxc ρ hρ
  have haB : a ∈ ball x ρ := by simpa only [mem_ball, dist_comm] using hax
  exact ⟨a, Metric.nhds_basis_closedBall.mem_iff.mp
    ((hU.inter isOpen_ball).mem_nhds ⟨ha, haB⟩)⟩

/-- A protruding continuum has a small nontrivial subcontinuum separated
from its marked round disk, with a fixed pair of nested neighborhoods. -/
theorem exists_local_protrusion
    {K : Set ℂ} (hK : IsCompact K) (hconn : IsConnected K)
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hDK : closedBall c r ⊆ K)
    (hne : K ≠ closedBall c r) :
    ∃ (x : ℂ) (ρ : ℝ) (Q : Set ℂ),
      0 < ρ ∧ x ∈ frontier K ∧
      Disjoint (closedBall x (2 * ρ)) (closedBall c r) ∧
      IsCompact Q ∧ IsConnected Q ∧ Q.Nontrivial ∧ x ∈ Q ∧
      Q ⊆ K ∩ ball x ρ := by
  have hnot : ¬ K ⊆ closedBall c r := fun h => hne (Subset.antisymm h hDK)
  obtain ⟨x, hx, hdist⟩ := exists_frontier_point_outside_closedBall hK hr hnot
  have hxD : x ∉ closedBall c r := by simpa only [mem_closedBall, not_le] using hdist
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (isClosed_closedBall.isOpen_compl.mem_nhds hxD)
  let ρ := δ / 4
  have hρ : 0 < ρ := div_pos hδ (by norm_num)
  have hd : Disjoint (closedBall x (2 * ρ)) (closedBall c r) := by
    apply Set.disjoint_left.mpr
    intro z hz hzD
    apply hball ?_ hzD
    have hz' : dist z x ≤ 2 * ρ := hz
    change dist z x < δ
    dsimp only [ρ] at hz'
    linarith
  have hnt : K.Nontrivial := by
    refine ⟨x, hK.isClosed.closure_eq ▸ hx.1, c, hDK (mem_closedBall_self hr), ?_⟩
    intro h
    subst x
    simp only [dist_self] at hdist
    linarith
  obtain ⟨Q, hQc, hQconn, hQnt, hxQ, hQsub⟩ := exists_nontrivial_subcontinuum_in_open
    hK hconn hnt (hK.isClosed.closure_eq ▸ hx.1) isOpen_ball (mem_ball_self hρ)
  exact ⟨x, ρ, Q, hρ, hx, hd, hQc, hQconn, hQnt, hxQ, hQsub⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionProjection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nontrivial continuum has positive transverse overlap with any nearby anchor ball after
choosing a suitable direction. -/

open Set Function Filter Metric
open scoped Topology ComplexConjugate

noncomputable section

namespace CircleDomainRigidity

private theorem continuous_tiltedUnit : Continuous (fun t : ℝ => (tiltedUnit t : ℂ)) := by
  change Continuous (fun t : ℝ => (1 + (t : ℂ) * Complex.I) /
    ((‖1 + (t : ℂ) * Complex.I‖ : ℝ) : ℂ))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    exact_mod_cast norm_ne_zero_iff.mpr (one_add_im_ne_zero t)

private theorem tiltedUnit_zero : (tiltedUnit 0 : ℂ) = 1 := by
  simp [tiltedUnit, unitOfNonzero]

/-- Make the projection of a nonzero displacement nonzero while keeping another displacement's
projection as small as desired. -/
theorem exists_transverse_rotation {v : ℂ} (hv : v ≠ 0) (w : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : Circle, (rotation a v).im ≠ 0 ∧ |(rotation a w).im| < δ := by
  have hbase : ∃ b : Circle, ((b : ℂ) * w).im = 0 := by
    by_cases hw : w = 0
    · exact ⟨1, by simp [hw]⟩
    · refine ⟨unitOfNonzero (conj w) (by
        intro h
        apply hw
        simpa only [map_zero, Complex.conj_conj] using congrArg conj h), ?_⟩
      simp [unitOfNonzero, div_mul_eq_mul_div, Complex.div_im, Complex.mul_im]
      exact Or.inl (by ring)
  obtain ⟨b, hb⟩ := hbase
  let v' := (b : ℂ) * v
  let w' := (b : ℂ) * w
  have hv' : v' ≠ 0 := mul_ne_zero (Circle.coe_ne_zero b) hv
  have hw' : w'.im = 0 := hb
  have hcont : Continuous (fun t : ℝ => |((tiltedUnit t : ℂ) * w').im|) := by
    exact (Complex.continuous_im.comp (continuous_tiltedUnit.mul continuous_const)).abs
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |((tiltedUnit t : ℂ) * w').im| < δ := by
    apply (isOpen_lt hcont continuous_const).mem_nhds
    change |((tiltedUnit 0 : ℂ) * w').im| < δ
    simpa only [tiltedUnit_zero, one_mul, hw', abs_zero] using hδ
  by_cases him : v'.im = 0
  · have hre : v'.re ≠ 0 := by
      intro h
      apply hv'
      exact Complex.ext (by simpa using h) (by simpa using him)
    obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hsmall
    let t := ε / 2
    have ht : t ≠ 0 := ne_of_gt (half_pos hε)
    have htm : t ∈ ball (0 : ℝ) ε := by
      simp only [mem_ball, dist_zero_right, Real.norm_eq_abs, t,
        abs_of_pos (half_pos hε)]
      linarith
    refine ⟨tiltedUnit t * b, ?_, ?_⟩
    · change (((tiltedUnit t : ℂ) * (b : ℂ)) * v).im ≠ 0
      rw [mul_assoc]
      change ((tiltedUnit t : ℂ) * v').im ≠ 0
      simp only [tiltedUnit, unitOfNonzero, div_mul_eq_mul_div, Complex.div_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.normSq_ofReal,
        Complex.mul_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        zero_add, Complex.mul_re, Complex.I_re, Complex.I_im, mul_one, add_zero, him]
      simp only [zero_div, sub_zero]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero ht hre)
        (norm_ne_zero_iff.mpr (one_add_im_ne_zero t)))
        (mul_ne_zero (norm_ne_zero_iff.mpr (one_add_im_ne_zero t))
          (norm_ne_zero_iff.mpr (one_add_im_ne_zero t)))
    · simpa only [rotation_apply, Circle.coe_mul, mul_assoc, w'] using (show |((tiltedUnit t : ℂ) * w').im| < δ from he htm)
  · refine ⟨b, ?_, ?_⟩
    · exact him
    · simpa only [rotation_apply, hb, abs_zero] using hδ

/-- A nontrivial continuum through `x` has a nondegenerate interval of transverse parameters
strictly inside the projection of a prescribed anchor ball. -/
theorem exists_transverse_interval {Q : Set ℂ} (hQ : IsConnected Q) (hnt : Q.Nontrivial)
    {x : ℂ} (hx : x ∈ Q) (c : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (a : Circle) (s t : ℝ), s < t ∧
      Icc s t ⊆ (fun z => (rotation a z).im) '' Q ∩
        Ioo ((rotation a c).im - δ) ((rotation a c).im + δ) := by
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  obtain ⟨a, hgap, hclose⟩ := exists_transverse_rotation (sub_ne_zero.mpr hyx) (x - c) hδ
  let p : ℂ → ℝ := fun z => (rotation a z).im
  have hp : Continuous p := Complex.continuous_im.comp (rotation a).continuous
  have hpQ := hQ.isPreconnected.image p hp.continuousOn
  have hpx : p x ∈ p '' Q := mem_image_of_mem _ hx
  have hpy : p y ∈ p '' Q := mem_image_of_mem _ hy
  have hne : p y ≠ p x := by
    intro he
    apply hgap
    simpa only [map_sub, Complex.sub_im, sub_eq_zero] using he
  have hxc : p c - δ < p x ∧ p x < p c + δ := by
    change |(rotation a (x - c)).im| < δ at hclose
    rw [map_sub, Complex.sub_im, abs_lt] at hclose
    constructor <;> linarith [hclose.1, hclose.2]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨s, hs, hsx⟩ := exists_between (max_lt hlt hxc.1)
    refine ⟨a, s, p x, hsx, ?_⟩
    intro z hz
    refine ⟨hpQ.Icc_subset hpy hpx ⟨(le_max_left _ _).trans (hs.le.trans hz.1), hz.2⟩, ?_⟩
    exact ⟨lt_of_lt_of_le ((le_max_right _ _).trans_lt hs) hz.1,
      lt_of_le_of_lt hz.2 hxc.2⟩
  · obtain ⟨t, hxt, ht⟩ := exists_between (lt_min hgt hxc.2)
    refine ⟨a, p x, t, hxt, ?_⟩
    intro z hz
    refine ⟨hpQ.Icc_subset hpx hpy ⟨hz.1, hz.2.trans (ht.le.trans (min_le_left _ _))⟩, ?_⟩
    exact ⟨lt_of_lt_of_le hxc.1 hz.1,
      lt_of_le_of_lt hz.2 (ht.trans_le (min_le_right _ _))⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalCrossingGeometry
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local crossing segments from a buffered anchor ball to an inner target region. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuous_rotatedLine (a : Circle) (y : ℝ) : Continuous (rotatedLine a y) :=
  (rotation a).continuous.comp (continuous_horizontalLine y)

theorem convex_rotatedLine_preimage (a : Circle) (y : ℝ)
    {W : Set ℂ} (hW : Convex ℝ W) : Convex ℝ (rotatedLine a y ⁻¹' W) := by
  intro p hp q hq α β hα hβ hsum
  have he : horizontalLine y (α * p + β * q) =
      α • horizontalLine y p + β • horizontalLine y q := by
    apply Complex.ext
    · simp [horizontalLine]
    · simp only [horizontalLine, Complex.add_im, Complex.real_smul, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      calc
        y = (α + β) * y := by rw [hsum, one_mul]
        _ = α * y + β * y := by ring
  change rotation a (horizontalLine y (α * p + β * q)) ∈ W
  rw [he, map_add, map_smul, map_smul]
  exact hW hp hq hα hβ hsum

theorem middle_chord_dist (a : Circle) (y : ℝ) (c : ℂ) :
    dist (rotatedLine a y ((rotation a).symm c).re) c = |y - ((rotation a).symm c).im| := by
  let d := (rotation a).symm c
  have he : horizontalLine y d.re - d = ((y - d.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [horizontalLine]
  calc
    dist (rotatedLine a y d.re) c = dist (horizontalLine y d.re) d := by
      conv_lhs => rhs; rw [← (rotation a).apply_symm_apply c]
      exact (rotation a).dist_map _ _
    _ = |y - d.im| := by
      rw [dist_eq_norm, he, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs]

/-- A connected line segment joining the exterior of a closed region to its interior meets the
frontier at a parameter different from the exterior endpoint. -/
theorem exists_rotated_frontier_parameter (a : Circle) (y : ℝ)
    {U : Set ℂ} (hU : IsOpen U) {s t : ℝ}
    (hs : rotatedLine a y s ∉ closure U) (ht : rotatedLine a y t ∈ U) :
    ∃ b ∈ uIcc s t, b ≠ s ∧ rotatedLine a y b ∈ frontier U := by
  let C := rotatedLine a y '' uIcc s t
  have hC : IsPreconnected C :=
    isPreconnected_uIcc.image _ (continuous_rotatedLine a y).continuousOn
  have hsC : rotatedLine a y s ∈ C := mem_image_of_mem _ left_mem_uIcc
  have htC : rotatedLine a y t ∈ C := mem_image_of_mem _ right_mem_uIcc
  have hinter : (C ∩ frontier U).Nonempty := by
    by_contra h
    have havoid : ∀ z ∈ C, z ∉ frontier U := by
      intro z hz hzF
      exact h ⟨z, hz, hzF⟩
    have hcover : C ⊆ U ∪ (closure U)ᶜ := by
      intro z hz
      by_cases hzU : z ∈ U
      · exact Or.inl hzU
      · right
        intro hzcl
        exact havoid z hz ⟨hzcl, by simpa only [hU.interior_eq] using hzU⟩
    have hd : Disjoint U (closure U)ᶜ := disjoint_left.mpr
      (fun z hz hzc => hzc (subset_closure hz))
    rcases hC.subset_or_subset hU isClosed_closure.isOpen_compl hd hcover with h | h
    · exact hs (subset_closure (h hsC))
    · exact h htC (subset_closure ht)
  obtain ⟨z, ⟨b, hb, rfl⟩, hbf⟩ := hinter
  refine ⟨b, hb, ?_, hbf⟩
  intro he
  subst b
  exact hs hbf.1

/-- The compact transverse overlap supplies local segments starting strictly in the anchor ball
and ending on the inner frontier. The entire paid segment stays in the chosen convex region. -/
theorem localized_frontier_crossings (a : Circle)
    {U Q W : Set ℂ} (hU : IsOpen U) (hQU : Q ⊆ U) (hQW : Q ⊆ W)
    (hW : Convex ℝ W) {c : ℂ} {δ : ℝ}
    (hball : ball c δ ⊆ (closure U)ᶜ ∩ W) {J : Set ℝ}
    (hJ : J ⊆ (fun z => ((rotation a).symm z).im) '' Q ∩
      Ioo (((rotation a).symm c).im - δ) (((rotation a).symm c).im + δ)) :
    ∀ y ∈ J, ∃ s t : ℝ, s ≠ t ∧
      rotatedLine a y s ∈ ball c δ ∧ rotatedLine a y t ∈ frontier U ∧
      ∀ x ∈ uIcc s t, rotatedLine a y x ∈ W := by
  intro y hy
  obtain ⟨⟨q, hq, hqy⟩, hyl, hyr⟩ := hJ hy
  let s := ((rotation a).symm c).re
  let t := ((rotation a).symm q).re
  have hsball : rotatedLine a y s ∈ ball c δ := by
    rw [mem_ball, middle_chord_dist]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hqt : rotatedLine a y t = q := by
    change rotation a (horizontalLine y ((rotation a).symm q).re) = q
    rw [show horizontalLine y ((rotation a).symm q).re = (rotation a).symm q by
      apply Complex.ext
      · rfl
      · exact hqy.symm]
    exact (rotation a).apply_symm_apply q
  obtain ⟨b, hb, hbs, hbf⟩ := exists_rotated_frontier_parameter a y hU
    (hball hsball).1 (hqt ▸ hQU hq)
  have hsegment : uIcc s t ⊆ rotatedLine a y ⁻¹' W :=
    (convex_rotatedLine_preimage a y hW).ordConnected.uIcc_subset
      (hball hsball).2 (by change rotatedLine a y t ∈ W; simpa only [hqt] using hQW hq)
  exact ⟨s, b, hbs.symm, hsball, hbf, (uIcc_subset_uIcc_left hb).trans hsegment⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealAnchorRetention
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source anchor's fixed zero plateau is retained on a compact target anchor in the actual
finite models. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (A : AssignedRealModelLimit M)

/-- A compact portion of the limiting anchor image has the original test value zero in all
sufficiently late finite models, and lies in their actual target domains. -/
theorem eventually_zero_on_anchor_image
    (hsch : PlanarSchoenflies) (hG : IsOpen G) (H : ℂ ≃ₜ ℂ)
    (hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (l : ℕ) (hzero : ∀ z ∈ closure (jordanInterior H), d.physical l (Complex.equivRealProdCLM z) = 0)
    {K : Set ℂ} (hK : IsCompact K) (hKA : K ⊆ A.function '' jordanInterior H) :
    ∀ᶠ n in atTop, ∀ z ∈ K,
      (z : Sphere) ∈ (M.stages (A.subsequence n)).domain ∧
      sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
        ((M.stages (A.subsequence n)).inverse z) = 0 := by
  have hsourceK := (isCompact_closure_jordanInterior H).image OnePoint.continuous_coe
  have hsourceG : ((↑) : ℂ → Sphere) '' closure (jordanInterior H) ⊆ G := by
    rintro _ ⟨z, hz, rfl⟩
    exact hHG hz
  filter_upwards [A.eventually_compact_subset_anchor_image hsch hG H hHG hK hKA,
    A.strict.tendsto_atTop (M.eventually_model_contains hsourceK hsourceG),
    A.strict.tendsto_atTop (M.eventually_test_eq hsourceK hsourceG l)] with n hn hM htest
  intro z hz
  obtain ⟨x, hx, he⟩ := hn hz
  have hxsource := hM (mem_image_of_mem ((↑) : ℂ → Sphere) (subset_closure hx))
  have hxfinite := (M.stages (A.subsequence n)).equivalence.finite_forward
    (M.stages (A.subsequence n)).source_infty (M.stages (A.subsequence n)).principal.1 hxsource
  change finiteCoord ((M.stages (A.subsequence n)).forward x) = z at he
  have he' : (M.stages (A.subsequence n)).forward x = (z : Sphere) := by
    rw [← coe_finiteCoord hxfinite, he]
  refine ⟨he' ▸ (M.stages (A.subsequence n)).equivalence.mapsTo hxsource, ?_⟩
  rw [← he', (M.stages (A.subsequence n)).equivalence.left_inv x hxsource]
  change (M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n))
    (Complex.equivRealProdCLM x) = 0
  exact (htest x (mem_image_of_mem ((↑) : ℂ → Sphere) (subset_closure hx))).trans
    (hzero x (subset_closure hx))

end CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FixedCoreBarrierPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local real-barrier payment for a fixed source core, independent of the core exhaustion
chosen to construct the model limit. This permits using the same test in nearby model limits. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε}
  (A : AssignedRealModelLimit M)

theorem fixed_core_barrier_payment
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (B : SmoothJordanCore G) (j : Fin B.count) (l : ℕ)
    (J₀ : ℂ ≃ₜ ℂ)
    (hboundary₀ : extendAtInfinity A.function ''
      (((↑) : ℂ → Sphere) '' frontier (jordanInterior (B.disk j))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J₀))
    (hside₀ : extendAtInfinity A.function ''
      (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j))) =
      (extendAtInfinity A.function '' G) ∩
        (((↑) : ℂ → Sphere) '' jordanInterior J₀))
    (hone : ∀ z ∈ frontier (jordanInterior (B.disk j)),
      d.physical l (Complex.equivRealProdCLM z) = 1)
    (H : ℂ ≃ₜ ℂ) (hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hzero : ∀ z ∈ closure (jordanInterior H), d.physical l (Complex.equivRealProdCLM z) = 0)
    (c : ℂ) (δ : ℝ) (hanchor : closedBall c δ ⊆ A.function '' jordanInterior H)
    (hd : Disjoint (closedBall c δ) (closure (jordanInterior J₀)))
    {Q : Set ℂ} (hQ : IsCompact Q) (hQinner : Q ⊆ jordanInterior J₀)
    {W : Set ℂ} (hW : IsClosed W) (hWconvex : Convex ℝ W)
    (hQW : Q ⊆ W) (hBW : closedBall c δ ⊆ W)
    {P : Set ℂ} (hP : IsCompact P) (hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hPW : Disjoint (A.function '' P) W)
    (rot : Circle) {J : Set ℝ} (hJ : MeasurableSet J)
    (hprojection : J ⊆ (fun z => ((rotation rot).symm z).im) '' Q ∩
      Ioo (((rotation rot).symm c).im - δ) (((rotation rot).symm c).im + δ))
    {R : ℝ} (hR : 3 * M.radius ≤ R) (hWR : W ⊆ closedBall 0 R) :
    (volume J).toReal ≤ Real.sqrt Real.pi * R * Real.sqrt
      (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
        gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * R * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  let _ : ∀ n, Fintype (M.stages (A.subsequence n)).indices :=
    fun n => (M.stages (A.subsequence n)).finite_indices.fintype
  have hF : ContinuousOn A.function (((↑) : ℂ → Sphere) ⁻¹' G) := by
    intro z hz
    have h := continuousAt_finite_part_of_conformalAt (A.conformal.1 _ hz)
      (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using h.continuousWithinAt
  have hret := A.strict.tendsto_atTop
    (M.eventually_model_contains B.isCompact B.subset)
  obtain ⟨Jn, p, _, _, hp, hγ, hfront, hγlim, hplim, hpa, hboundary, hBfront⟩ :=
    exists_anchored_retained_jordan_models hsch
      (fun n => (M.stages (A.subsequence n)).terminals.H)
      (fun n => (M.stages (A.subsequence n)).terminals.disjoint_closures)
      (fun n => (M.stages (A.subsequence n)).forward)
      (fun n => (M.stages (A.subsequence n)).inverse)
      (fun n => (M.stages (A.subsequence n)).domain)
      (fun n => (M.stages (A.subsequence n)).equivalence)
      (fun n => (M.stages (A.subsequence n)).circle_domain.1)
      (fun n => (M.stages (A.subsequence n)).principal.1)
      hG B j hret
      (fun z hz => A.strict.tendsto_atTop
        ((M.eventually_model_contains isCompact_singleton (singleton_subset_iff.mpr hz)).mono
          (fun _ hn => hn (mem_singleton z))))
      A.function hF A.converges J₀ hboundary₀ hside₀
  have hQin := eventually_compact_subset_jordanInterior_of_anchor
    J₀ Jn _ _ hγ hfront hBfront hγlim hp hplim hpa
    hQ hQinner
  have hBin := eventually_jordan_fill_subset_open J₀ Jn _ _
    hγ hfront hBfront hγlim isClosed_closedBall.isOpen_compl
    (fun z hz hzb => Set.disjoint_left.mp hd hzb hz)
  have hzeron := A.eventually_zero_on_anchor_image hsch hG H hHG l hzero (isCompact_closedBall c δ) hanchor
  have honen : ∀ᶠ n in atTop,
      frontier (jordanInterior (Jn n)) ⊆ ((↑) : ℂ → Sphere) ⁻¹' (M.stages (A.subsequence n)).domain ∧
      ∀ z ∈ frontier (jordanInterior (Jn n)),
        sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
          ((M.stages (A.subsequence n)).inverse z) = 1 := by
    filter_upwards [hret, hboundary, A.strict.tendsto_atTop
      (M.eventually_test_eq B.isCompact B.subset l)] with n hn hb hv
    apply values_on_image_jordan_boundary (M.stages (A.subsequence n)).equivalence
      ((B.inDomain hn).boundary_subset_domain j) hb
    intro z hz
    change (M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n))
      (Complex.equivRealProdCLM z) = 1
    exact (hv z ((B.inDomain (Subset.refl _)).boundary_subset_domain j ⟨z, hz, rfl⟩)).trans (hone z hz)
  apply A.rotated_line_payment_away_from_compact harea hε rot l hR hP hPG hW hWR hPW hJ
  filter_upwards [hQin, hBin, hzeron, honen] with n hnQ hnB hnZ hnOne
  have hc := localized_frontier_crossings rot (jordanInterior_isOpen (Jn n)) hnQ hQW hWconvex
    (fun z hz => ⟨fun hzcl => hnB hzcl (ball_subset_closedBall hz),
      hBW (ball_subset_closedBall hz)⟩) hprojection
  intro y hy
  obtain ⟨s, t, hst, hs, ht, hsegment⟩ := hc y hy
  have hsZ := hnZ _ (ball_subset_closedBall hs)
  exact ⟨s, t, hst, hsZ.1, hnOne.1 ht,
    hWR (hsegment _ left_mem_uIcc), hWR (hsegment _ right_mem_uIcc),
    hsZ.2, hnOne.2 _ ht, fun x hx _ => hsegment x hx⟩

end CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LevelBarrierLocalizedNorm
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed compatible real barrier controls the localized norm used by the open
map exclusion. Enlarging the omitted penalty set only decreases its Dirichlet payment. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace CompatibleLevelBarrier
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {previous : PriorLevelFamily d.physicalDomain π} {flags EStar : Set Sphere}
  {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere} {W : Set Sphere}
  (R : CompatibleLevelBarrier d π previous flags EStar regions f W)

 theorem localized_norm_le_controlledSize
    {P : Set ℂ}
    (hP : (fun x : ℝ × ℝ => π (Complex.equivRealProdCLM.symm x : Sphere)) ⁻¹' R.penalty ⊆
      Complex.equivRealProdCLM '' P) :
    Real.sqrt (∫ x in realChartDomain d.physicalDomain \ (Complex.equivRealProdCLM '' P),
      gradientEnergy R.coordinate.physical (fun z => sphericalMetricFactor z • 1) x) +
      (countingSquareNorm R.weight).toReal ≤ R.controlledSize.toReal := by
  let E := (fun x : ℝ × ℝ => π (Complex.equivRealProdCLM.symm x : Sphere)) ⁻¹' R.penalty
  have hsub : realChartDomain d.physicalDomain \ (Complex.equivRealProdCLM '' P) ⊆
      realChartDomain d.physicalDomain \ E := by
    intro x hx
    exact ⟨hx.1, fun he => hx.2 (hP he)⟩
  have henergy := integrable_gradientEnergy_spherical_of_memLp
    (R.coordinate.physical_energy.mono_measure
      (Measure.restrict_mono_set volume (show realChartDomain d.physicalDomain \ E ⊆
        realChartDomain d.physicalDomain from sdiff_subset)))
  have hi := setIntegral_mono_set henergy
    (Eventually.of_forall fun x => by rw [gradientEnergy_spherical]; positivity)
    (Eventually.of_forall fun x hx => hsub hx)
  change _ ≤ (ENNReal.ofReal _ + countingSquareNorm R.weight).toReal
  have hw : countingSquareNorm R.weight ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) R.weight_finite.ne
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hw,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  exact add_le_add (Real.sqrt_le_sqrt hi) le_rfl

end CompatibleLevelBarrier
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealSourceBarriers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local plateaus of the original quotient tests collapse their corresponding full ends. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

theorem exists_positive_level_in_neighborhood
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {U : Set Sphere} (hU : IsOpen U) (hqU : π q ∈ U) :
    ∃ n, 0 < n ∧ closedTerminalCap ((L.cores n).disk (E.address n)) ⊆ π ⁻¹' U := by
  have hsub : (⋂ n, closedTerminalCap ((L.cores n).disk (E.address n))) ⊆ π ⁻¹' U := by
    rw [← E.source]
    intro x hx
    have he := (hr q x).mpr (Or.inr ⟨hq, hx⟩)
    change π x ∈ U
    rw [← he]
    exact hqU
  obtain ⟨n, hn⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap _).isClosed) E.source_cap_antitone
    (hU.preimage hπ) hsub
  exact ⟨n + 1, Nat.succ_pos _, (E.source_cap_antitone (Nat.le_succ n)).trans hn⟩

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealEndProtrusion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Protrusion localization for the actual marked components of the real-model limit. -/

open Set Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

/-- Removing infinity preserves these complementary components, which all
lie in the finite plane. -/
theorem plane_eq_component {x : ℂ} (hx : x ∈ E.plane) :
    E.plane = connectedComponentIn
      (((↑) : ℂ → Sphere) ⁻¹' (extendAtInfinity L.function '' G)ᶜ) x := by
  let D : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' (extendAtInfinity L.function '' G)ᶜ
  have hED : E.plane ⊆ D := fun _ hz =>
    connectedComponentIn_subset (extendAtInfinity L.function '' G)ᶜ E.point hz
  apply Subset.antisymm
  · exact E.plane_connected.isPreconnected.subset_connectedComponentIn hx hED
  · have himage : IsPreconnected (((↑) : ℂ → Sphere) '' connectedComponentIn D x) :=
      isPreconnected_connectedComponentIn.image _ OnePoint.continuous_coe.continuousOn
    have hsub : ((↑) : ℂ → Sphere) '' connectedComponentIn D x ⊆
        connectedComponentIn (extendAtInfinity L.function '' G)ᶜ (x : Sphere) :=
      himage.subset_connectedComponentIn
        (mem_image_of_mem _ (mem_connectedComponentIn (hED hx)))
        (by
          rintro _ ⟨z, hz, rfl⟩
          exact connectedComponentIn_subset D x hz)
    rw [← connectedComponentIn_eq hx] at hsub
    exact fun z hz => hsub (mem_image_of_mem _ hz)

/-- If an assigned marked disk does not fill its component, there is a
nontrivial local continuum outside the disk and a nearby genuine target
ball serving as the anchor for the barrier/stream alternatives. -/
theorem exists_protrusion_and_anchor
    (hG : IsOpen G)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {s : S} (hqs : π q = σ s)
    (hne : E.plane ≠ closedBall (L.center s) (L.radius s)) :
    ∃ (x : ℂ) (ρ : ℝ) (Q : Set ℂ) (a : ℂ) (δ : ℝ),
      0 < ρ ∧ x ∈ frontier E.plane ∧
      Disjoint (closedBall x (2 * ρ)) (closedBall (L.center s) (L.radius s)) ∧
      IsCompact Q ∧ IsConnected Q ∧ Q.Nontrivial ∧ x ∈ Q ∧
      Q ⊆ E.plane ∩ ball x ρ ∧ 0 < δ ∧
      closedBall a δ ⊆ (((↑) : ℂ → Sphere) ⁻¹' (extendAtInfinity L.function '' G)) ∩ ball x ρ := by
  have hD : closedBall (L.center s) (L.radius s) ⊆ E.plane := by
    intro z hz
    exact E.marked_disk_subset hr hq hqs (mem_image_of_mem _ hz)
  obtain ⟨x, ρ, Q, hρ, hx, hd, hQc, hQconn, hQnt, hxQ, hQsub⟩ :=
    exists_local_protrusion E.plane_compact E.plane_connected (L.bounds s).2.1 hD hne
  have hxE : x ∈ E.plane := E.plane_compact.isClosed.closure_eq ▸ hx.1
  have hU : IsOpen (((↑) : ℂ → Sphere) ⁻¹' (extendAtInfinity L.function '' G)) :=
    (L.conformal.1.isOpen_image hG hG (Subset.refl G)).preimage OnePoint.continuous_coe
  have hxfront : x ∈ frontier (connectedComponentIn
      ((((↑) : ℂ → Sphere) ⁻¹' (extendAtInfinity L.function '' G))ᶜ) x) := by
    simpa only [← preimage_compl, ← E.plane_eq_component hxE] using hx
  obtain ⟨a, δ, hδ, hanchor⟩ := exists_domain_ball_near_component_frontier hU
    (connectedComponentIn_subset (extendAtInfinity L.function '' G)ᶜ E.point hxE) hxfront hρ
  exact ⟨x, ρ, Q, a, δ, hρ, hx, hd, hQc, hQconn, hQnt, hxQ, hQsub, hδ, hanchor⟩

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_SourceAnchor
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A target-domain point has a compact source Jordan anchor whose image contains a target ball
inside any prescribed open neighborhood. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_source_jordan_anchor {f : ℂ → ℂ} {G W : Set ℂ}
    (hG : IsOpen G) (ho : ∀ S, IsOpen S → S ⊆ G → IsOpen (f '' S))
    (hW : IsOpen W) {a : ℂ} (ha : a ∈ f '' G) (haW : a ∈ W) :
    ∃ (H : ℂ ≃ₜ ℂ) (δ : ℝ), 0 < δ ∧
      closure (jordanInterior H) ⊆ G ∧ closedBall a δ ⊆ f '' jordanInterior H ∩ W := by
  obtain ⟨p, hp, rfl⟩ := ha
  obtain ⟨r, hr, hrG⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hG.mem_nhds hp)
  let H := roundJordanAt p r hr
  have hHG : closure (jordanInterior H) ⊆ G := by
    dsimp only [H]
    rw [roundJordanAt_closure]
    exact hrG
  have hpH : p ∈ jordanInterior H := by
    dsimp only [H]
    rw [roundJordanAt_interior]
    simpa only [mem_ball, dist_self] using hr
  have hopen : IsOpen (f '' jordanInterior H ∩ W) :=
    (ho _ (jordanInterior_isOpen H) (subset_closure.trans hHG)).inter hW
  obtain ⟨δ, hδ, hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hopen.mem_nhds ⟨mem_image_of_mem _ hpH, haW⟩)
  exact ⟨H, δ, hδ, hHG, hδsub⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionTestGeometry
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed source anchors, bounded target regions and positive transverse widths constructed
from a genuine protrusion of an assigned marked component. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

namespace LocalEndTestGeometry

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)

theorem model_bound : 3 * M.radius ≤ T.boundRadius := le_max_left _ _

theorem region_bound : closedBall T.center T.radius ⊆ closedBall 0 T.boundRadius := by
  intro z hz
  rw [mem_closedBall]
  calc
    dist z 0 ≤ dist z T.center + dist T.center 0 := dist_triangle _ _ _
    _ ≤ T.radius + ‖T.center‖ := by
      rw [dist_zero_right]
      linarith [mem_closedBall.mp hz]
    _ ≤ T.boundRadius := le_max_right _ _

end LocalEndTestGeometry

namespace RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd A q)

theorem exists_local_test_geometry (hG : IsOpen G)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {s : S} (hqs : π q = σ s)
    (hne : E.plane ≠ closedBall (A.center s) (A.radius s)) :
    ∃ T : LocalEndTestGeometry E,
      Disjoint (closedBall T.center (2 * T.radius)) (closedBall (A.center s) (A.radius s)) := by
  obtain ⟨x, ρ, Q, a, δ, hρ, _, hsep, hQc, hQconn, hQnt, hxQ, hQsub, hδ, hball⟩ :=
    E.exists_protrusion_and_anchor hG hr hq hqs hne
  have ha := hball (mem_closedBall_self hδ.le)
  have haimage : a ∈ A.function '' (((↑) : ℂ → Sphere) ⁻¹' G) := by
    obtain ⟨p, hp, he⟩ := ha.1
    cases p using OnePoint.rec with
    | infty => simp only [extendAtInfinity_infty] at he; exact (OnePoint.coe_ne_infty a he.symm).elim
    | coe z => exact ⟨z, hp, OnePoint.coe_injective he⟩
  obtain ⟨H, η, hη, hHG, hηsub⟩ := exists_source_jordan_anchor
    (hG.preimage OnePoint.continuous_coe) (A.plane_open_embedding hG).2.1
    isOpen_ball haimage ha.2
  obtain ⟨rot, lo, hi, hlt, hproj⟩ := exists_transverse_interval hQconn hQnt hxQ a hη
  refine ⟨{
    center := x
    radius := ρ
    radius_pos := hρ
    continuum := Q
    compact := hQc
    in_component := fun z hz => (hQsub hz).1
    in_region := fun z hz => ball_subset_closedBall (hQsub hz).2
    sourceAnchor := H
    source_inside := hHG
    anchorCenter := a
    anchorRadius := η
    anchorRadius_pos := hη
    anchor_image := fun z hz => (hηsub hz).1
    anchor_region := fun z hz => ball_subset_closedBall (hηsub hz).2
    direction := rot⁻¹
    lower := lo
    upper := hi
    width_pos := hlt
    projection := by simpa only [rotation_symm, inv_inv] using hproj
  }, hsep⟩

end RealTargetEnd
end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanControlNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative neighborhood for simultaneous inner and outer containment of a Jordan
fill. The interior anchor removes any choice of parametrization or orientation. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_jordan_control_radius
    (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ) (hγ : Continuous γ)
    (hfront : range γ = frontier (jordanInterior H))
    {z : ℂ} (hz : z ∈ jordanInterior H)
    {K O : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ jordanInterior H)
    (hO : IsOpen O) (hHO : closure (jordanInterior H) ⊆ O) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (γ' : Circle → ℂ) (z' : ℂ) (J : ℂ ≃ₜ ℂ),
      (∀ t, dist (γ' t) (γ t) < δ) → dist z' z < δ →
      range γ' = frontier (jordanInterior J) → z' ∈ jordanInterior J →
      K ⊆ jordanInterior J ∧ closure (jordanInterior J) ⊆ O := by
  by_contra! h
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ] <;> positivity
  have htδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose γn zn Jn hclose hzclose hfrontn hzn hfail using fun n => h (δ n) (hδ n)
  have hlim : TendstoUniformly γn γ atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [htδ.eventually (gt_mem_nhds hε)] with n hn t
    simpa only [dist_comm] using (hclose n t).trans hn
  have hzlim : Tendsto zn atTop (𝓝 z) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [htδ.eventually (gt_mem_nhds hε)] with n hn
    exact (hzclose n).trans hn
  have hinner := eventually_compact_subset_jordanInterior_of_anchor H Jn γ γn hγ hfront
    (Eventually.of_forall hfrontn) hlim hz hzlim (Eventually.of_forall hzn) hK hKH
  have houter := eventually_jordan_fill_subset_open H Jn γ γn hγ hfront
    (Eventually.of_forall hfrontn) hlim hO hHO
  obtain ⟨n, hn, hn'⟩ := (hinner.and houter).exists
  exact hfail n hn hn'

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SourceMapNeighborhood
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open conditions on finitely many source traces retain compact target anchors,
Jordan sides, and separation from the compact set excluded from the energy integral. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_open_jordan_map_control
    {X : Type*} [TopologicalSpace X] (f₀ : C(X, ℂ))
    (γ : C(Circle, X)) (a : X) (H : ℂ ≃ₜ ℂ)
    (hfront : range (f₀.comp γ) = frontier (jordanInterior H))
    (ha : f₀ a ∈ jordanInterior H)
    {K O : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ jordanInterior H)
    (hO : IsOpen O) (hHO : closure (jordanInterior H) ⊆ O) :
    ∃ V : Set C(X, ℂ), IsOpen V ∧ f₀ ∈ V ∧
      ∀ f ∈ V, ∀ J : ℂ ≃ₜ ℂ,
        range (f.comp γ) = frontier (jordanInterior J) →
        f a ∈ jordanInterior J →
        K ⊆ jordanInterior J ∧ closure (jordanInterior J) ⊆ O := by
  obtain ⟨δ, hδ, hcontrol⟩ := exists_jordan_control_radius H (f₀.comp γ)
    (f₀.comp γ).continuous hfront ha hK hKH hO hHO
  let V : Set C(X, ℂ) :=
    {f | dist (f.comp γ) (f₀.comp γ) < δ} ∩ {f | dist (f a) (f₀ a) < δ}
  have hV : IsOpen V :=
    (isOpen_lt ((ContinuousMap.continuous_precomp γ).dist continuous_const)
      continuous_const).inter
      (isOpen_lt ((continuous_eval_const a).dist continuous_const)
        continuous_const)
  refine ⟨V, hV, ⟨by simpa using hδ, by simpa using hδ⟩, ?_⟩
  intro f hf J hJ haJ
  exact hcontrol (f.comp γ) (f a) J
    (fun t => (ContinuousMap.dist_apply_le_dist t).trans_lt hf.1) hf.2 hJ haJ

 theorem exists_open_source_anchor_control
    (hsch : PlanarSchoenflies) {G : Set Sphere} (hG : IsOpen G)
    (F₀ : ℂ → ℂ) (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G))
    (ho₀ : ∀ U, IsOpen U → U ⊆ ((↑) : ℂ → Sphere) ⁻¹' G → IsOpen (F₀ '' U))
    (hi₀ : InjOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G))
    (H : ℂ ≃ₜ ℂ) (hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    {K : Set ℂ} (hK : IsCompact K) (hKF : K ⊆ F₀ '' jordanInterior H) :
    ∃ V : Set C(FiniteSource G, ℂ), IsOpen V ∧ finiteSourceMap F₀ hF₀ ∈ V ∧
      ∀ (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G)),
        finiteSourceMap F hF ∈ V →
        (∀ U, IsOpen U → U ⊆ ((↑) : ℂ → Sphere) ⁻¹' G → IsOpen (F '' U)) →
        InjOn F (((↑) : ℂ → Sphere) ⁻¹' G) → K ⊆ F '' jordanInterior H := by
  obtain ⟨J₀, hJ₀, _, hJ₀front⟩ := exists_jordan_image_disk hsch
    (hG.preimage OnePoint.continuous_coe) hF₀ ho₀ hi₀ H hHG
  let γ := sourceJordanCircle H (frontier_subset_closure.trans hHG)
  have h0H : H 0 ∈ jordanInterior H := ⟨0, by simp, rfl⟩
  let a : FiniteSource G := ⟨H 0, hHG (subset_closure h0H)⟩
  have hfront : range ((finiteSourceMap F₀ hF₀).comp γ) =
      frontier (jordanInterior J₀) := by
    change range (F₀ ∘ (fun t : Circle => H (t : ℂ))) = _
    rw [range_comp, jordan_circle_range, hJ₀front]
  have ha : (finiteSourceMap F₀ hF₀) a ∈ jordanInterior J₀ :=
    hJ₀ ▸ mem_image_of_mem F₀ h0H
  obtain ⟨V, hV, hfV, hcontrol⟩ := exists_open_jordan_map_control
    (finiteSourceMap F₀ hF₀) γ a J₀ hfront ha hK (hJ₀ ▸ hKF)
    isOpen_univ (subset_univ _)
  refine ⟨V, hV, hfV, ?_⟩
  intro F hF hFV ho hi
  obtain ⟨J, hJ, _, hJfront⟩ := exists_jordan_image_disk hsch
    (hG.preimage OnePoint.continuous_coe) hF ho hi H hHG
  have hfront' : range ((finiteSourceMap F hF).comp γ) = frontier (jordanInterior J) := by
    change range (F ∘ (fun t : Circle => H (t : ℂ))) = _
    rw [range_comp, jordan_circle_range, hJfront]
  have ha' : (finiteSourceMap F hF) a ∈ jordanInterior J :=
    hJ ▸ mem_image_of_mem F h0H
  exact hJ.symm ▸ (hcontrol _ hFV J hfront' ha').1

 theorem isOpen_source_image_disjoint {G : Set Sphere}
    {P W : Set ℂ} (hP : IsCompact P) (hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hW : IsClosed W) :
    IsOpen {f : C(FiniteSource G, ℂ) | Disjoint (f '' {x | x.val ∈ P}) W} := by
  have hPC : IsCompact {x : FiniteSource G | x.val ∈ P} := by
    apply Subtype.isCompact_iff.mpr
    have he : Subtype.val '' {x : FiniteSource G | x.val ∈ P} = P := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hz; exact ⟨⟨z, hPG hz⟩, hz, rfl⟩
    rw [he]
    exact hP
  convert ContinuousMap.isOpen_setOfPred_mapsTo hPC hW.isOpen_compl using 1
  all_goals try with_reducible_and_instances rfl
  ext f
  simp only [Set.mem_ofPred_eq, Set.disjoint_left, Set.MapsTo, Set.mem_compl_iff,
    Set.forall_mem_image]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FixedRealExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed source real barrier gives an open exclusion of conformal maps. The neighborhood
retains only compact source traces; later model limits may use different core exhaustions. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_open_fixed_core_real_exclusion
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (B : SmoothJordanCore G) (j : Fin B.count)
    (F₀ : ℂ → ℂ) (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G))
    (ho₀ : ∀ U, IsOpen U → U ⊆ ((↑) : ℂ → Sphere) ⁻¹' G → IsOpen (F₀ '' U))
    (hi₀ : InjOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G))
    (J₀ : ℂ ≃ₜ ℂ)
    (hboundary₀ : extendAtInfinity F₀ ''
      (((↑) : ℂ → Sphere) '' frontier (jordanInterior (B.disk j))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J₀))
    (hside₀ : extendAtInfinity F₀ ''
      (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j))) =
      (extendAtInfinity F₀ '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior J₀))
    (H : ℂ ≃ₜ ℂ) (hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (c : ℂ) (δ : ℝ) (hanchor : closedBall c δ ⊆ F₀ '' jordanInterior H)
    (hd : Disjoint (closedBall c δ) (closure (jordanInterior J₀)))
    {Q : Set ℂ} (hQ : IsCompact Q) (hQinner : Q ⊆ jordanInterior J₀)
    {W : Set ℂ} (hW : IsClosed W) (hWconvex : Convex ℝ W)
    (hQW : Q ⊆ W) (hBW : closedBall c δ ⊆ W)
    {P : Set ℂ} (hP : IsCompact P) (hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hPW : Disjoint (F₀ '' P) W)
    (rot : Circle) {J : Set ℝ} (hJ : MeasurableSet J)
    (hprojection : J ⊆ (fun z => ((rotation rot).symm z).im) '' Q ∩
      Ioo (((rotation rot).symm c).im - δ) (((rotation rot).symm c).im + δ))
    (R : ℝ) (hWR : W ⊆ closedBall 0 R) :
    ∃ V : Set C(FiniteSource G, ℂ), IsOpen V ∧ finiteSourceMap F₀ hF₀ ∈ V ∧
      ∀ {S : Type*} {π : Sphere → Sphere} {σ : S → Sphere}
        {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
        (M : RealModelExhaustion d O ε) (A : AssignedRealModelLimit M) (l : ℕ),
        Tendsto ε atTop (𝓝 0) → 3 * M.radius ≤ R →
        (∀ z ∈ frontier (jordanInterior (B.disk j)),
          d.physical l (Complex.equivRealProdCLM z) = 1) →
        (∀ z ∈ closure (jordanInterior H), d.physical l (Complex.equivRealProdCLM z) = 0) →
        Real.sqrt Real.pi * R * Real.sqrt
          (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
            gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
          2 * R * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) < (volume J).toReal →
        finiteSourceMap A.function (A.plane_open_embedding hG).1 ∉ V := by
  let γ : C(Circle, FiniteSource G) :=
    ⟨fun t => ⟨B.curve j t, B.boundary_subset_domain j
      ⟨B.curve j t, (B.boundary j) ▸ mem_range_self t, rfl⟩⟩,
      (B.embedding j).continuous.subtype_mk _⟩
  obtain ⟨q, hqG, hqB⟩ := exists_domain_point_inside_jordan hG (B.disk j)
    (B.boundary_subset_domain j)
  let a : FiniteSource G := ⟨q, hqG⟩
  have ha : (finiteSourceMap F₀ hF₀) a ∈ jordanInterior J₀ := by
    change F₀ q ∈ jordanInterior J₀
    have hh := mem_image_of_mem (extendAtInfinity F₀)
      (show (q : Sphere) ∈ G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j)) from
        ⟨hqG, q, hqB, rfl⟩)
    rw [hside₀] at hh
    simpa only [finiteSourceMap, ContinuousMap.coe_mk, a, extendAtInfinity_coe, OnePoint.coe_injective.mem_set_image] using hh.2
  have hfront : range ((finiteSourceMap F₀ hF₀).comp γ) = frontier (jordanInterior J₀) := by
    change range (fun t => F₀ (B.curve j t)) = _
    simpa only [finiteSourceMap, γ, ContinuousMap.comp_apply, ContinuousMap.coe_mk, extendAtInfinity_coe, finiteCoord_coe, Function.comp_def] using
      range_finite_image_boundary (B.boundary j) hboundary₀
        (fun t => by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
  obtain ⟨V₁, hV₁, hmem₁, hcontrol⟩ := exists_open_jordan_map_control
    (finiteSourceMap F₀ hF₀) γ a J₀ hfront ha hQ hQinner
    isClosed_closedBall.isOpen_compl
    (fun z hz hzb => Set.disjoint_left.mp hd hzb hz)
  obtain ⟨V₂, hV₂, hmem₂, hanchorControl⟩ := exists_open_source_anchor_control
    hsch hG F₀ hF₀ ho₀ hi₀ H hHG (isCompact_closedBall c δ) hanchor
  let V₃ : Set C(FiniteSource G, ℂ) := {f | Disjoint (f '' {x | x.val ∈ P}) W}
  have hV₃ : IsOpen V₃ := isOpen_source_image_disjoint hP hPG hW
  have hmem₃ : finiteSourceMap F₀ hF₀ ∈ V₃ := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ hz
    exact Set.disjoint_left.mp hPW (mem_image_of_mem F₀ hx) hz
  refine ⟨V₁ ∩ V₂ ∩ V₃, (hV₁.inter hV₂).inter hV₃, ⟨⟨hmem₁, hmem₂⟩, hmem₃⟩, ?_⟩
  intro S π σ d O ε M A l hε hR hone hzero hsmall hmem
  have hA := A.plane_open_embedding hG
  obtain ⟨J', _, _, hb', hs'⟩ := exists_matched_image_core hsch hG hconn
    (B.subset (interior_subset B.infty_interior)) A.conformal.1 A.conformal.bijOn.injOn
    (by simp) B
  have ha' : (finiteSourceMap A.function hA.1) a ∈ jordanInterior (J' j) := by
    change A.function q ∈ jordanInterior (J' j)
    have hh := mem_image_of_mem (extendAtInfinity A.function)
      (show (q : Sphere) ∈ G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j)) from
        ⟨hqG, q, hqB, rfl⟩)
    rw [hs' j] at hh
    simpa only [finiteSourceMap, ContinuousMap.coe_mk, a, extendAtInfinity_coe, OnePoint.coe_injective.mem_set_image] using hh.2
  have hfront' : range ((finiteSourceMap A.function hA.1).comp γ) =
      frontier (jordanInterior (J' j)) := by
    change range (fun t => A.function (B.curve j t)) = _
    simpa only [finiteSourceMap, γ, ContinuousMap.comp_apply, ContinuousMap.coe_mk, extendAtInfinity_coe, finiteCoord_coe, Function.comp_def] using
      range_finite_image_boundary (B.boundary j) (hb' j)
        (fun t => by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
  have hgeometry := hcontrol _ hmem.1.1 (J' j) hfront' ha'
  have hanchor' := hanchorControl A.function hA.1 hmem.1.2 hA.2.1 hA.2.2
  have hPW' : Disjoint (A.function '' P) W := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ hz
    exact Set.disjoint_left.mp hmem.2
      (show A.function x ∈ (finiteSourceMap A.function hA.1) '' {y | y.val ∈ P} from
        ⟨⟨x, hPG hx⟩, hx, rfl⟩) hz
  have hbound := A.fixed_core_barrier_payment hsch harea hG hε B j l (J' j)
    (hb' j) (hs' j) hone H hHG hzero c δ hanchor'
    (Set.disjoint_left.mpr fun z hz hzc => hgeometry.2 hzc hz)
    hQ hgeometry.1 hW hWconvex hQW hBW hP hPG hPW' rot hJ hprojection hR hWR
  exact (not_lt_of_ge hbound) hsmall

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalFixedRealExclusion
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small real barriers at an actual protruding end exclude a whole open neighborhood.
The retained contour is selected from the original end before testing any later model. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

namespace RealTargetEnd
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd A q)

 theorem exists_core_in_neighborhood_avoiding_anchor
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {U : Set Sphere} (hU : IsOpen U) (hqU : π q ∈ U)
    {K : Set ℂ} (hK : IsCompact K)
    (hKA : ((↑) : ℂ → Sphere) '' K ⊆ extendAtInfinity A.function '' G) :
    ∃ k : ℕ, closedTerminalCap ((A.cores k).disk (E.address k)) ⊆ π ⁻¹' U ∧
      Disjoint K (closure (jordanInterior (A.contours k (E.address k)))) := by
  obtain ⟨n, _, hsource⟩ := E.exists_positive_level_in_neighborhood hπ hr hq hU hqU
  have htarget : (⋂ n, closedTerminalCap (A.contours n (E.address n))) ⊆
      (((↑) : ℂ → Sphere) '' K)ᶜ := by
    rw [← E.target]
    intro p hp hpK
    exact connectedComponentIn_subset _ _ hp (hKA hpK)
  obtain ⟨m, htargetm⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap _).isClosed) E.cap_antitone
    (hK.image OnePoint.continuous_coe).isClosed.isOpen_compl htarget
  let k := max n m
  refine ⟨k, (E.source_cap_antitone (le_max_left n m)).trans hsource, ?_⟩
  apply Set.disjoint_left.mpr
  intro z hzK hzcap
  exact (E.cap_antitone (le_max_right n m)).trans htargetm
    ⟨z, hzcap, rfl⟩ (mem_image_of_mem _ hzK)

end RealTargetEnd

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SlackRealExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A strictly larger comparison radius gives an open radius interval in
the countable selection space while retaining the same real barrier test. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)

 theorem model_lt_selectionRadius : 3 * M.radius < T.selectionRadius := by
  have h := T.model_bound
  dsimp [selectionRadius]
  linarith

 theorem selectionThreshold_pos : 0 < T.selectionThreshold := by
  apply div_pos (sub_pos.mpr T.width_pos)
  apply mul_pos (by positivity)
  exact (mul_pos (by norm_num) M.radius_pos).trans T.model_lt_selectionRadius

 theorem exists_open_real_barrier_exclusion_at_radius
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hconn : IsConnected G) (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {U : Set Sphere} (hU : IsOpen U) (hqU : π q ∈ U)
    (u : (ℝ × ℝ) → ℝ)
    (hone : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U →
      u (Complex.equivRealProdCLM z) = 1)
    (hzero : ∀ z ∈ closure (jordanInterior T.sourceAnchor),
      u (Complex.equivRealProdCLM z) = 0)
    {P : Set ℂ} (hP : IsCompact P) (hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hPW : Disjoint (A.function '' P) (closedBall T.center T.radius))
    (R : ℝ) (hTR : T.boundRadius ≤ R)
    {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.sqrt (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
      gradientEnergy u (fun z => sphericalMetricFactor z • 1) x) + β < (T.upper - T.lower) / ((Real.sqrt Real.pi + 2) * R)) :
    ∃ V : Set C(FiniteSource G, ℂ), IsOpen V ∧
      finiteSourceMap A.function (A.plane_open_embedding hG).1 ∈ V ∧
      ∀ {S' : Type*} {π' : Sphere → Sphere} {σ' : S' → Sphere}
        {d' : CountableRealCoordinates G π' σ'} {O' : ℕ → S' → Set Sphere} {ε' : ℕ → ℝ}
        (M' : RealModelExhaustion d' O' ε') (A' : AssignedRealModelLimit M') (l : ℕ),
        Tendsto ε' atTop (𝓝 0) → 3 * M'.radius ≤ R →
        d'.physical l = u → Real.sqrt (∑' s, (d'.upper l s - d'.lower l s) ^ 2) ≤ β →
        finiteSourceMap A'.function (A'.plane_open_embedding hG).1 ∉ V := by
  have hKA : ((↑) : ℂ → Sphere) '' closedBall T.anchorCenter T.anchorRadius ⊆
      extendAtInfinity A.function '' G := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨p, hp, he⟩ := T.anchor_image hz
    exact ⟨p, T.source_inside (subset_closure hp), by simp only [extendAtInfinity_coe, he]⟩
  obtain ⟨k, hcap, hdisj⟩ := E.exists_core_in_neighborhood_avoiding_anchor
    hπ hr hq hU hqU (isCompact_closedBall _ _) hKA
  have hone' : ∀ z ∈ frontier (jordanInterior ((A.cores k).disk (E.address k))),
      u (Complex.equivRealProdCLM z) = 1 := by
    intro z hz
    exact hone z ((A.cores k).boundary_subset_domain (E.address k) ⟨z, hz, rfl⟩)
      (hcap ⟨z, frontier_subset_closure hz, rfl⟩)
  have hA := A.plane_open_embedding hG
  obtain ⟨V, hV, hmem, hexclude⟩ := exists_open_fixed_core_real_exclusion hsch harea hG hconn
    (A.cores k) (E.address k) A.function hA.1 hA.2.1 hA.2.2
    (A.contours k (E.address k)) (A.boundary k (E.address k)) (A.side k (E.address k))
    T.sourceAnchor T.source_inside T.anchorCenter T.anchorRadius T.anchor_image hdisj
    T.compact (T.in_component.trans (E.plane_inside k)) isClosed_closedBall
    (convex_closedBall T.center T.radius) T.in_region T.anchor_region hP hPG hPW
    T.direction measurableSet_Icc T.projection R
      (T.region_bound.trans (closedBall_subset_closedBall hTR))
  refine ⟨V, hV, hmem, ?_⟩
  intro S' π' σ' d' O' ε' M' A' l hε' hR heq hband
  apply hexclude M' A' l hε' hR
    (by simpa only [heq] using hone') (by simpa only [heq] using hzero)
  rw [heq]
  have hRpos : 0 < R :=
    lt_of_lt_of_le (mul_pos (by norm_num) M.radius_pos) (T.model_bound.trans hTR)
  have hden : 0 < (Real.sqrt Real.pi + 2) * R := by positivity
  have hstrict : ((Real.sqrt Real.pi + 2) * R) *
      (Real.sqrt (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
        gradientEnergy u (fun z => sphericalMetricFactor z • 1) x) + β) < T.upper - T.lower := by
    have h := (lt_div_iff₀ hden).mp hsmall
    simpa only [mul_comm] using h
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr T.width_pos.le)]
  calc
    _ ≤ Real.sqrt Real.pi * R * Real.sqrt
          (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
            gradientEnergy u (fun z => sphericalMetricFactor z • 1) x) +
        2 * R * β := by gcongr
    _ ≤ ((Real.sqrt Real.pi + 2) * R) *
        (Real.sqrt (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
          gradientEnergy u (fun z => sphericalMetricFactor z • 1) x) + β) := by
      nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg Real.pi) hRpos.le) hβ,
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hRpos.le)
          (Real.sqrt_nonneg (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
            gradientEnergy u (fun z => sphericalMetricFactor z • 1) x))]
    _ < T.upper - T.lower := hstrict

end CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LevelBarrierSlackExclusion
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed barrier excludes a whole open interval of model
radii around the current one, as required by countable open selection. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace CompatibleLevelBarrier
 theorem exists_open_exclusion_with_slack
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hπG : ∀ z : ℂ, (z : Sphere) ∈ base.physicalDomain → π (z : Sphere) ∈ base.quotientDomain)
    (hpre : π ⁻¹' base.quotientDomain ⊆ base.physicalDomain)
    (hinf : π OnePoint.infty ∈ base.anchor)
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} {E : RealTargetEnd A q}
    (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
    {previous : PriorLevelFamily base.physicalDomain π} {flags EStar : Set Sphere}
    {regions : ℕ → Set Sphere} {f : base.quotientDomain → Sphere} {W : Set Sphere}
    (R : CompatibleLevelBarrier base π previous flags EStar regions f W)
    (hregions : ∀ n, IsOpen (regions n)) (hqregions : ∀ n, π q ∈ regions n)
    (hzero : ∀ z ∈ closure (jordanInterior T.sourceAnchor), π (z : Sphere) ∈ EStar)
    (hf : ∀ (z : ℂ) (hz : (z : Sphere) ∈ base.physicalDomain),
      f ⟨π (z : Sphere), hπG z hz⟩ = (A.function z : Sphere))
    (hW : ((↑) : ℂ → Sphere) '' closedBall T.center T.radius ⊆ W)
    (hsmall : R.controlledSize.toReal < T.selectionThreshold) :
    ∃ V : Set C(FiniteSource base.physicalDomain, ℂ), IsOpen V ∧
      finiteSourceMap A.function (A.plane_open_embedding hG).1 ∈ V ∧
      ∀ {S' : Type*} {π' : Sphere → Sphere} {σ' : S' → Sphere}
        {d' : CountableRealCoordinates base.physicalDomain π' σ'}
        {O' : ℕ → S' → Set Sphere} {ε' : ℕ → ℝ}
        (M' : RealModelExhaustion d' O' ε') (A' : AssignedRealModelLimit M') (l : ℕ),
        Tendsto ε' atTop (𝓝 0) → 3 * M'.radius ≤ T.selectionRadius →
        d'.physical l = R.coordinate.physical →
        Real.sqrt (∑' s, (d'.upper l s - d'.lower l s) ^ 2) ≤
          (countingSquareNorm R.weight).toReal →
        finiteSourceMap A'.function (A'.plane_open_embedding hG).1 ∉ V := by
  let P : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' closure R.penalty)
  have hP : IsCompact P := isCompact_finite_preimage
    (isClosed_closure.preimage hπ) (fun hz => Set.disjoint_left.mp R.penalty_disjoint hinf hz)
  have hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain := by
    intro z hz
    exact hpre (R.penalty_inside hz)
  have hPW : Disjoint (A.function '' P) (closedBall T.center T.radius) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ hz
    have hn := R.penalty_avoids ⟨π (x : Sphere), R.penalty_inside hx⟩ hx
    rw [hf x (hPG hx)] at hn
    exact hn (hW (mem_image_of_mem _ hz))
  have hPcontains :
      (fun x : ℝ × ℝ => π (Complex.equivRealProdCLM.symm x : Sphere)) ⁻¹' R.penalty ⊆
        Complex.equivRealProdCLM '' P := by
    intro x hx
    exact ⟨Complex.equivRealProdCLM.symm x, subset_closure hx,
      Complex.equivRealProdCLM.apply_symm_apply x⟩
  have hnorm := R.localized_norm_le_controlledSize hPcontains
  apply T.exists_open_real_barrier_exclusion_at_radius hsch harea hG hconn hπ hr hq
    (hregions R.level) (hqregions R.level) R.coordinate.physical
    (fun z hz hzu => (R.coordinate.pullback z hz).trans
      (R.one _ ⟨subset_closure hzu, hπG z hz⟩))
    (fun z hz => (R.coordinate.pullback z (T.source_inside hz)).trans
      (R.zero _ (hzero z hz))) hP hPG hPW T.selectionRadius (by
      dsimp [LocalEndTestGeometry.selectionRadius] <;> linarith) ENNReal.toReal_nonneg
    (hnorm.trans_lt hsmall)

end CompatibleLevelBarrier
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedHitLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Path hits tested on a compact subset of the ambient path space.  The
continuous map is the inclusion of the dust in the application; no path is
required to lie in that subset. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity.MarkedHit

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace C(PathTime, Y)]
  (ι : C(X, Y))

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] [BorelSpace C(PathTime, Y)]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] in
theorem integrable_pathHitReal {Z : Type*} [MeasurableSpace Z]
    (P : ProbabilityMeasure Z) {law : Z → ProbabilityMeasure C(PathTime, Y)}
    (hlaw : Measurable law) (x : X) :
    Integrable (fun z => pathHitReal ι (law z) x) (P : Measure Z) :=
  CircleDomainRigidity.integrable_pathHitReal P hlaw (ι x)

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] in
theorem pathHitReal_mixture {Z : Type*} [MeasurableSpace Z]
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure C(PathTime, Y))
    (hlaw : Measurable law) (x : X) :
    pathHitReal ι (probabilityMixture P law hlaw) x =
      ∫ z, pathHitReal ι (law z) x ∂(P : Measure Z) :=
  CircleDomainRigidity.pathHitReal_mixture P law hlaw (ι x)

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MarkedConfigurationNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureConfigurationMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureMeanConfigurationMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Testing all sizes and reciprocal separation scales is sufficient to control
the full square norm of the point-hit probabilities. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace C(PathTime, Y)]
  (ι : C(X, Y)) (μ : ProbabilityMeasure C(PathTime, Y)) {B : ℝ}

theorem HasHitNormBound.summable_sq (h : HasHitNormBound ι μ B) :
    Summable (fun x => pathHitReal ι μ x ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) h

theorem HasHitNormBound.countable_positive_support (h : HasHitNormBound ι μ B) :
    {x | 0 < pathHitProbability ι μ x}.Countable := by
  apply h.summable_sq.countable_support.mono
  intro x hx
  change pathHitReal ι μ x ^ 2 ≠ 0
  apply pow_ne_zero
  exact ne_of_gt (ENNReal.toReal_pos (ne_of_gt hx)
    (ne_of_lt (lt_of_le_of_lt (pathHitProbability_le_one ι μ x) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))))

theorem configuration_bound_of_injective
    (h : HasConfigurationBounds ι μ B) {n : ℕ} (x : Fin n → X) (hx : Injective x)
    (w : Fin n → Icc (0 : ℝ) 1) (hw : (∑ i, (w i : ℝ) ^ 2) ≤ 1) :
    ∑ i, (w i : ℝ) * pathHitReal ι μ (x i) ≤ B := by
  obtain ⟨m, hm⟩ := exists_reciprocal_separation x hx
  exact h n m ⟨(x, w), hw, hm⟩

theorem configuration_square_sum_le
    (h : HasConfigurationBounds ι μ B) (hB : 0 ≤ B)
    {n : ℕ} (x : Fin n → X) (hx : Injective x) :
    ∑ i, pathHitReal ι μ (x i) ^ 2 ≤ B ^ 2 := by
  let v : Fin n → ℝ := fun i => pathHitReal ι μ (x i)
  let s : ℝ := Real.sqrt (∑ i, v i ^ 2)
  have hv (i) : 0 ≤ v i := pathHitReal_nonneg ι _ _
  have hsum : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs : s ^ 2 = ∑ i, v i ^ 2 := Real.sq_sqrt hsum
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  by_cases hsz : s = 0
  · have hz : (∑ i, v i ^ 2) = 0 := by nlinarith
    change (∑ i, v i ^ 2) ≤ B ^ 2
    rw [hz]
    positivity
  have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsz)
  have hvi (i) : v i ≤ s := by
    have hi : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith
  let w : Fin n → Icc (0 : ℝ) 1 := fun i =>
    ⟨v i / s, div_nonneg (hv i) hs0, (div_le_one hsp).mpr (hvi i)⟩
  have hw : (∑ i, (w i : ℝ) ^ 2) ≤ 1 := by
    change (∑ i, (v i / s) ^ 2) ≤ 1
    simp_rw [div_pow]
    rw [← Finset.sum_div, ← hs, div_self (pow_ne_zero 2 hsz)]
  have hb := configuration_bound_of_injective ι μ h x hx w hw
  have heq : (∑ i, (w i : ℝ) * pathHitReal ι μ (x i)) = s := by
    change (∑ i, (v i / s) * v i) = s
    calc
      _ = (∑ i, v i ^ 2) / s := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = s := by rw [← hs]; field_simp
  rw [heq] at hb
  change (∑ i, v i ^ 2) ≤ B ^ 2
  nlinarith

theorem hasHitNormBound_of_configuration_bounds
    (h : HasConfigurationBounds ι μ B) (hB : 0 ≤ B) : HasHitNormBound ι μ B := by
  classical
  change ∀ F : Finset X, ∑ x ∈ F, pathHitReal ι μ x ^ 2 ≤ B ^ 2
  intro F
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  have he : Injective (fun i : Fin (Fintype.card F) => (e i).val) :=
    Subtype.val_injective.comp e.injective
  have hb := configuration_square_sum_le ι μ h hB (fun i => (e i).val) he
  rw [e.sum_comp (fun a : F => pathHitReal ι μ a.val ^ 2)] at hb
  rw [Finset.sum_coe_sort F (fun x : X => pathHitReal ι μ x ^ 2)] at hb
  exact hb

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBarrierTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real tests used by the countable selection. Compatibility is
with every finite sublist of previously selected tests, retaining repetitions. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace UngatedRealTest
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}

omit [MeasurableSpace C(PathTime, Sphere)] in
theorem freeComponentFailure_congr_selected
    {X T I J K : Type*} [TopologicalSpace X]
    (F : Set X) (N : Set (X × T)) (R : I → Set (X × T)) (S : J → Set (X × T))
    (a : K → I) (b : K → J) (h : ∀ k, R (a k) = S (b k)) :
    freeComponentFailure F N R a = freeComponentFailure F N S b := by
  have he : finiteLevelUnionGraph R a = finiteLevelUnionGraph S b := by
    unfold finiteLevelUnionGraph
    apply iUnion_congr
    intro k
    rw [h k]
  unfold freeComponentFailure
  rw [he]

end UngatedRealTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FreeLevelSections
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique level traces away from the countable flags provide the null
circle sections required by the whole-image atomless test. -/

open Set MeasureTheory Filter

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*}

theorem unitAddCircle_volume_singleton (t : UnitAddCircle) : volume ({t} : Set UnitAddCircle) = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
  simpa only [Set.image_singleton] using
    (volume_addCircle_image_eq_zero (show volume ({x} : Set ℝ) = 0 from measure_singleton x))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RestrictedCoordinateMarks
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable selected family uses only countably many nonzero bands.
Restricting to these marks preserves the actual graph, physical function
and masks; every discarded marked fiber is already a singleton. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateData.countable_band_support
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) :
    {s | C.upper s - C.lower s ≠ 0}.Countable :=
  CircleDomainRigidity.countable_band_support C.width_summable

 theorem exists_common_countable_coordinate_marks
    {I S : Type*} [Countable I] {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : I → MaskedCoordinateData G U π σ) (B : Set S) (hB : B.Countable) :
    ∃ A : Set S, A.Countable ∧ B ⊆ A ∧
      (∀ i, (C i).singular ∈ A) ∧
      ∀ i s, (C i).upper s - (C i).lower s ≠ 0 → s ∈ A := by
  let A := B ∪ range (fun i => (C i).singular) ∪ ⋃ i, {s | (C i).upper s - (C i).lower s ≠ 0}
  refine ⟨A, (hB.union (countable_range _)).union
    (countable_iUnion fun i => (C i).countable_band_support), ?_, ?_, ?_⟩
  · intro s hs
    exact Or.inl (Or.inl hs)
  · intro i
    exact Or.inl (Or.inr (mem_range_self i))
  · intro i s hs
    exact Or.inr (mem_iUnion.mpr ⟨i, hs⟩)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedLevelData
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual marked band widths supply the level weights for the next
endpoint-law construction. This uses the full dust as a temporary label
set; the common countable mark restriction is performed after selection. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel

namespace FiniteTransfer.MaskedCoordinateData
variable {G U B : Set Sphere} {π : Sphere → Sphere}
  (C : MaskedCoordinateData G U π (fun x : B => x.val))

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_21
theorem dustWeight_square_sum : (∑' x, C.dustWeight x ^ 2) < ∞ := by
  classical
  have he : (∑' x, C.dustWeight x ^ 2) =
      ∑' s : B, ENNReal.ofReal ((C.upper s - C.lower s) ^ 2) := by
    have hsupp : support (fun x => C.dustWeight x ^ 2) ⊆ B := by
      intro x hx
      by_contra hn
      exact hx (by simp only [dustWeight, dite_eq_right hn, zero_pow (by decide : 2 ≠ 0)])
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    apply tsum_congr
    intro s
    simp only [dustWeight, dite_eq_left s.property,
      ENNReal.ofReal_pow (C.width_nonneg s)]
  rw [he, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) C.width_summable]
  exact ENNReal.ofReal_lt_top

theorem incidence_le_dustWeight
    (hBU : Bᶜ ⊆ U)
    (hU : ∀ x ∈ U, {t : UnitAddCircle | (x, t) ∈ C.graph}.Subsingleton)
    (x : Sphere) : volume {t : UnitAddCircle | (x, t) ∈ C.graph} ≤ C.dustWeight x := by
  classical
  by_cases hx : x ∈ B
  · rw [dustWeight, dite_eq_left hx]
    exact (measure_mono (C.marked_fiber ⟨x, hx⟩)).trans
      ((volume_addCircle_image_Icc_le _ _).trans
        (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  · let : NullSingletonClass (volume : Measure UnitAddCircle) :=
      ⟨unitAddCircle_volume_singleton⟩
    rw [dustWeight, dite_eq_right hx, (hU x (hBU hx)).measure_zero volume]

theorem unique_of_dustWeight_eq_zero {x : Sphere} (hx : x ∈ B)
    (hw : C.dustWeight x = 0) : {t : UnitAddCircle | (x, t) ∈ C.graph}.Subsingleton := by
  have hle : C.upper ⟨x, hx⟩ - C.lower ⟨x, hx⟩ ≤ 0 := by
    apply ENNReal.ofReal_eq_zero.mp
    simpa only [dustWeight, dite_eq_left hx] using hw
  have he : C.lower ⟨x, hx⟩ = C.upper ⟨x, hx⟩ :=
    (sub_eq_zero.mp (le_antisymm hle (C.width_nonneg ⟨x, hx⟩))).symm
  have hb := C.marked_fiber ⟨x, hx⟩
  rw [he, Icc_self, image_singleton] at hb
  intro a ha b hb'
  exact (mem_singleton_iff.mp (hb ha)).trans (mem_singleton_iff.mp (hb hb')).symm

end FiniteTransfer.MaskedCoordinateData

variable [MeasurableSpace C(PathTime, Sphere)]

namespace maskedLevelData
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  (C : ℕ → MaskedCoordinateData d.physicalDomain d.quotientDomain π
    (fun x : d.dust => x.val))

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_21
theorem point_bound (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (hU : ∀ i x, x ∈ d.quotientDomain →
      {t : UnitAddCircle | (x, t) ∈ (C i).graph}.Subsingleton) (i : ℕ) (x : Sphere) :
    volume {t | (t, x) ∈ (maskedLevelData d π C).levels i} ≤
      (maskedLevelData d π C).levelWeights i x :=
  (C i).incidence_le_dustWeight hBU (hU i) x

theorem exists_countable_flags (B₀ : Set Sphere) (hB₀ : B₀.Countable)
    (hB₀B : B₀ ⊆ d.dust) :
    ∃ flags : Set Sphere, flags.Countable ∧ B₀ ⊆ flags ∧ flags ⊆ d.dust ∧
      (∀ i, ((C i).singular : Sphere) ∈ flags) ∧
      ∀ i, support ((maskedLevelData d π C).levelWeights i) ⊆ flags := by
  obtain ⟨A, hA, hBA, hs, hw⟩ := exists_common_countable_coordinate_marks C
    (Subtype.val ⁻¹' B₀) (hB₀.preimage Subtype.val_injective)
  refine ⟨Subtype.val '' A, hA.image _, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hB₀B hx⟩, hBA hx, rfl⟩
  · rintro x ⟨s, _, rfl⟩
    exact s.property
  · intro i
    exact ⟨(C i).singular, hs i, rfl⟩
  · intro i x hx
    change (C i).dustWeight x ≠ 0 at hx
    by_cases hxB : x ∈ d.dust
    · refine ⟨⟨x, hxB⟩, hw i ⟨x, hxB⟩ ?_, rfl⟩
      intro he
      exact hx (by simp only [MaskedCoordinateData.dustWeight, dite_eq_left hxB, he,
        ENNReal.ofReal_zero])
    · exact (hx (by simp only [MaskedCoordinateData.dustWeight, dite_eq_right hxB])).elim

end maskedLevelData

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SelectableMaskedCoordinate
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected coordinate retains the precise level and flag data needed
for a later endpoint-law construction. Weighted coarea is proved for the
actual physical mean before placing it in this interface. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace SelectableMaskedCoordinate
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}

theorem CompatibleWith.mono {c : SelectableMaskedCoordinate d π}
    {A B : Set (SelectableMaskedCoordinate d π)}
    (h : c.CompatibleWith B) (hAB : A ⊆ B) : c.CompatibleWith A :=
  ⟨fun a ha => h.1 a (hAB ha), fun n q hq => h.2 n q (fun i => hAB (hq i))⟩

theorem point_bound (c : ℕ → SelectableMaskedCoordinate d π)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (i : ℕ) (x : Sphere) :
    volume {t | (t, x) ∈ (pathData c).levels i} ≤ (pathData c).levelWeights i x :=
  maskedLevelData.point_bound _ hBU (fun i => (c i).domain_unique) i x

end SelectableMaskedCoordinate

namespace SelectableMaskedCoordinate

 local instance localInst_r6edb4b_4 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_of_real
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → Sphere)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (Q : PhysicalRealCoordinate d π)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π (fun x : d.dust => x.val))
    (hgraph : C.graph = circleBandGraph d.quotientDomain Q.quotient)
    (flags : Set Sphere) (hflags : flags.Countable) (hflagsB : flags ⊆ d.dust) :
    ∃ c : SelectableMaskedCoordinate d π, c.coordinate = C ∧ flags ⊆ c.flags := by
  obtain ⟨Z, hZ, hfZ, hZB, hsing, hweights⟩ :=
    maskedLevelData.exists_countable_flags (fun _ => C) flags hflags hflagsB
  refine ⟨{
    coordinate := C
    flags := Z
    flags_countable := hZ
    flags_dust := hZB
    weight_support := hweights 0
    singular_marked := hsing 0
    domain_unique := ?_
    weighted := ?_ }, rfl, hfZ⟩
  · intro x hx a ha b hb
    rw [hgraph] at ha hb
    exact ((circleBandGraph_on_open hU Q.quotient_continuous hx).mp ha).symm.trans
      ((circleBandGraph_on_open hU Q.quotient_continuous hx).mp hb)
  · intro g hg henergy
    rw [hgraph]
    exact physicalRealCoordinate_ae_finite_weighted_levels hcoarea d hU hG π
      (fun x => (he x).symm) Q g hg henergy

end SelectableMaskedCoordinate

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_OrderedMaskedSelection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected mixed family retains the complete seed before the new
coordinates. Empty selection steps use the seed zero coordinate. The
resulting order has type omega plus omega, not a rearranged natural order. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem freeComponentFailure_mono_free {X T I J : Type*} [TopologicalSpace X]
    {F K : Set X} (hFK : F ⊆ K) (N : Set (X × T)) (R : I → Set (X × T)) (labels : J → I) :
    freeComponentFailure F N R labels ⊆ freeComponentFailure K N R labels := by
  rintro _ ⟨⟨x, t, θ⟩, h, rfl⟩
  exact ⟨(x, t, θ), ⟨hFK h.1, h.2⟩, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SelectableLevelBarrier
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small real-barrier alternative supplies an actual selectable
coordinate compatible with every previously selected real or period
coordinate. Its flags and presentation are constructed from the barrier. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_selectable_level_barrier
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdense : Dense d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ) (p : d.dust)
    (previous : PriorLevelFamily d.physicalDomain π)
    (flags EStar : Set Sphere) (hinfty : π OnePoint.infty ∈ interior EStar)
    (regions : ℕ → Set Sphere) (f : d.quotientDomain → Sphere) (W : Set Sphere)
    (R : CompatibleLevelBarrier d π previous flags EStar regions f W)
    (A : Set (SelectableMaskedCoordinate d π))
    (label : SelectableMaskedCoordinate d π → ℕ)
    (hflags : ∀ a ∈ A, a.flags ⊆ flags)
    (hgraphs : ∀ a ∈ A, a.coordinate.graph = previous.graph (label a)) :
    ∃ c : SelectableMaskedCoordinate d π, c.CompatibleWith A ∧
      c.coordinate.graph = circleBandGraph d.quotientDomain R.coordinate.quotient ∧
      ∃ P : RealCoordinatePresentation d π c.coordinate, P.coordinate = R.coordinate := by
  have hempty (j n : ℕ) (labels : Fin n → ℕ) (_ : ∀ i, labels i < j) :
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ d.dust)
          (circleBandGraph d.quotientDomain R.coordinate.quotient)
          (fun _ => circleBandGraph d.quotientDomain R.coordinate.quotient) labels) = 0 := by
    simp [freeComponentFailure]
  let F := realCoordinateFamily d hU hdense π he hB (fun _ => R.coordinate)
    d.dust (Subset.refl _) (fun _ => R.weight) (fun _ => R.weight_finite)
    (fun _ _ hx _ => hx) (fun _ => R.band_bound) hempty
  let C := F.maskedCoordinate hG p 0
  obtain ⟨c, hc, hmark⟩ := SelectableMaskedCoordinate.exists_of_real hcoarea d hU hG π he
    R.coordinate C rfl (R.exclusions ∩ d.dust)
    (R.exclusions_countable.mono inter_subset_left) inter_subset_right
  have hgraph : c.coordinate.graph = circleBandGraph d.quotientDomain R.coordinate.quotient := by
    rw [hc]
    rfl
  refine ⟨c, ⟨?_, ?_⟩, hgraph, ?_⟩
  · intro a ha x hx
    exact hmark ⟨R.prior_flags (hflags a ha hx), a.flags_dust hx⟩
  · intro n q hq
    rw [hgraph]
    have hz := R.finite_compatibility n (label ∘ q)
    rw [UngatedRealTest.freeComponentFailure_congr_selected (d.dust \ R.exclusions)
      (circleBandGraph d.quotientDomain R.coordinate.quotient) previous.graph
      (fun i : Fin n => (q i).coordinate.graph) (label ∘ q) id
      (fun i => (hgraphs (q i) (hq i)).symm)] at hz
    apply measure_mono_null (freeComponentFailure_mono_free ?_ _ _ id) hz
    intro x hx
    exact ⟨hx.1, fun hr => hx.2 (hmark ⟨hr, hx.1⟩)⟩
  · refine ⟨{
      coordinate := R.coordinate
      graph_eq := hgraph
      mask_eq_univ := by rw [hc]; rfl
      physical_eq := by intro x; rw [hc]; rfl
      band_width := by intro s; rw [hc]; rfl
      compactSupport := ((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' interior EStar)ᶜ
      isCompact_support := isCompact_finite_preimage
        (isOpen_interior.preimage hπ).isClosed_compl (fun h => h hinfty)
      zero_off := ?_
      zero_infty := fun _ => R.zero _ (interior_subset hinfty) }, rfl⟩
    intro z _ hz
    apply R.zero
    apply interior_subset
    by_contra hn
    exact hz hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealExclusionWitness
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real barrier test retains its actual presentation, band weight,
open map neighborhood, and the proved radius-dependent exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace RealExclusionWitness
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
    (fun x : base.dust => x.val)}
  (W : RealExclusionWitness base π C)

 theorem mem_sizedNeighborhood {F : C(FiniteSource base.physicalDomain, ℂ)}
    {c : ℂ} {r : ℝ≥0} {R : ℝ} (hF : F ∈ W.neighborhood) (hR : 3 * R < W.radius) :
    ((F, c, r), R) ∈ W.sizedNeighborhood :=
    ⟨⟨hF, mem_univ _⟩, by change R < W.radius / 3; linarith⟩
end RealExclusionWitness

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SelectableBarrierExclusion
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual small compatible barrier supplies both its selectable
coordinate and the open sized real exclusion carried into the final model. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem CompatibleLevelBarrier.exists_selectable_exclusion
    (hweighted : WeightedPlanarScalarCoarea)
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hB : base.dust = π '' base.physicalDomainᶜ)
    (hπG : ∀ z : ℂ, (z : Sphere) ∈ base.physicalDomain → π (z : Sphere) ∈ base.quotientDomain)
    (hpre : π ⁻¹' base.quotientDomain ⊆ base.physicalDomain)
    (hinf : π OnePoint.infty ∈ base.anchor)
    (p : base.dust)
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} {E : RealTargetEnd A q}
    (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
    {previous : PriorLevelFamily base.physicalDomain π} {flags EStar : Set Sphere}
    {regions : ℕ → Set Sphere} {f : base.quotientDomain → Sphere} {W₁ : Set Sphere}
    (R : CompatibleLevelBarrier base π previous flags EStar regions f W₁)
    (hregions : ∀ n, IsOpen (regions n)) (hqregions : ∀ n, π q ∈ regions n)
    (hzero : ∀ z ∈ closure (jordanInterior T.sourceAnchor), π (z : Sphere) ∈ EStar)
    (hf : ∀ (z : ℂ) (hz : (z : Sphere) ∈ base.physicalDomain),
      f ⟨π (z : Sphere), hπG z hz⟩ = (A.function z : Sphere))
    (hW : ((↑) : ℂ → Sphere) '' closedBall T.center T.radius ⊆ W₁)
    (hsmall : R.controlledSize.toReal < T.selectionThreshold)
    (hinfty : π OnePoint.infty ∈ interior EStar)
    (Candidates : Set (SelectableMaskedCoordinate base π))
    (label : SelectableMaskedCoordinate base π → ℕ)
    (hflags : ∀ c ∈ Candidates, c.flags ⊆ flags)
    (hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c)) :
    ∃ c : SelectableMaskedCoordinate base π, c.CompatibleWith Candidates ∧
      ∃ W : RealExclusionWitness base π c.coordinate,
        W.radius = T.selectionRadius ∧
        finiteSourceMap A.function (A.plane_open_embedding hG).1 ∈ W.neighborhood ∧
        ∀ a : ℂ, ∀ r : ℝ≥0,
          ((finiteSourceMap A.function (A.plane_open_embedding hG).1, a, r), M.radius) ∈
            W.sizedNeighborhood := by
  obtain ⟨c, hcomp, _, P, hP⟩ := exists_selectable_level_barrier hweighted base hU hG hdense
    π hπ he hB p previous flags EStar hinfty regions f W₁ R Candidates label hflags hgraphs
  obtain ⟨V, hV, hmem, hexclude⟩ := R.exists_open_exclusion_with_slack hsch harea hG hconn
    hπ hr hπG hpre hinf T hq hregions hqregions hzero hf hW hsmall
  let X : RealExclusionWitness base π c.coordinate := {
    presentation := P
    weight := R.weight
    weight_finite := R.weight_finite
    band_bound := by rw [hP]; exact R.band_bound
    radius := T.selectionRadius
    neighborhood := V
    isOpen_neighborhood := hV
    excludes := by
      intro S' π' σ' d' O' ε' M' A' l hG' hε hR hphysical hnorm
      apply hexclude M' A' l hε hR
      · rwa [← hP]
      · exact hnorm }
  refine ⟨c, hcomp, X, rfl, hmem, ?_⟩
  intro a r
  exact X.mem_sizedNeighborhood hmem T.model_lt_selectionRadius

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_BarrierCodeLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Failure of a small compatible barrier yields a probability law,
using ADMS duality, Bogachev lifting, and the resulting modulus bound. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
theorem exists_positive_barrier_duality_parameter (C : ℝ) {β : ℝ≥0∞} (hβ : 0 < β) :
    ∃r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞) < (β / (2 * barrierConstructionConstant C)) ^ 2 := by
  have hden : 2 * barrierConstructionConstant C ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (barrierConstructionConstant_ne_top C)
  have hpos : 0 < (β / (2 * barrierConstructionConstant C)) ^ 2 :=
    pos_iff_ne_zero.mpr (pow_ne_zero 2 (ENNReal.div_pos hβ.ne' hden).ne')
  obtain ⟨r, hr, hrb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
  exact ⟨r, ENNReal.coe_pos.mp hr, hrb⟩


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_BorelDensityBudget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel density budgets for measurable families of finite measures. The
finite mass cap lets us use the jointly measurable kernel Radon–Nikodym
 derivative in Mathlib. -/

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
  [MeasurableSpace.CountablyGenerated X]

theorem measurableSet_boundedDensityBudget
    (μ : Z → Measure X) (hμ : Measurable μ)
    (σ : Measure X) [IsFiniteMeasure σ]
    (mass energy : ℝ≥0∞) (hmass : mass < ∞) :
    MeasurableSet {z | BoundedDensityBudget σ (μ z) mass energy} := by
  classical
  let A : Set Z := {z | μ z univ ≤ mass}
  have hA : MeasurableSet A :=
    measurableSet_le ((Measure.measurable_coe MeasurableSet.univ).comp hμ) measurable_const
  let κ : Kernel Z X := ⟨A.piecewise μ (fun _ => 0), hμ.piecewise hA measurable_const⟩
  let : IsFiniteKernel κ := ⟨⟨mass, hmass, fun z => by
    change A.piecewise μ (fun _ => 0) z univ ≤ mass
    by_cases hz : z ∈ A
    · change μ z univ ≤ mass at hz
      simpa only [Set.piecewise_eq_of_mem A μ _ hz] using hz
    · simp [Set.piecewise_eq_of_notMem A μ _ hz]⟩⟩
  let η : Kernel Z X := Kernel.const Z σ
  have heq (z : Z) (hz : z ∈ A) : κ z = μ z := by
    change A.piecewise μ (fun _ => 0) z = μ z
    exact Set.piecewise_eq_of_mem A μ _ hz
  have hrn (z : Z) : κ.rnDeriv η z =ᵐ[σ] (κ z).rnDeriv σ :=
    Kernel.rnDeriv_eq_rnDeriv_measure
  have hmeas : Measurable (fun z => ∫⁻ x, κ.rnDeriv η z x ^ 2 ∂σ) :=
    (Kernel.measurable_rnDeriv κ η).pow_const 2 |>.lintegral_prod_right'
  have hset : MeasurableSet {z | κ z ≪ σ ∧
      (∫⁻ x, κ.rnDeriv η z x ^ 2 ∂σ) ≤ energy} :=
    (Kernel.measurableSet_absolutelyContinuous κ η).inter
      (measurableSet_le hmeas measurable_const)
  convert hA.inter hset using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  change BoundedDensityBudget σ (μ z) mass energy ↔
    z ∈ A ∧ κ z ≪ σ ∧ (∫⁻ x, κ.rnDeriv η z x ^ 2 ∂σ) ≤ energy
  constructor
  · rintro ⟨hz, g, hg, hμg, hge⟩
    have hk : κ z = σ.withDensity g := (heq z hz).trans hμg
    refine ⟨hz, hk ▸ withDensity_absolutelyContinuous _ _, ?_⟩
    have hrng : κ.rnDeriv η z =ᵐ[σ] g :=
      (hrn z).trans (by rw [hk]; exact Measure.rnDeriv_withDensity σ hg)
    apply le_trans (le_of_eq (lintegral_congr_ae ?_)) hge
    filter_upwards [hrng] with x hx
    exact congrArg (fun t : ℝ≥0∞ => t ^ 2) hx
  · rintro ⟨hz, hac, he⟩
    refine ⟨hz, κ.rnDeriv η z, Kernel.measurable_rnDeriv_right κ η z, ?_, he⟩
    rw [← heq z hz]
    exact ((withDensity_congr_ae (hrn z)).trans
      (Measure.withDensity_rnDeriv_eq (κ z) σ hac)).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FiniteChoiceLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The probability law of an explicitly weighted finite choice, viewed on the
natural numbers so that a single trajectory space works at all tree vertices. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem integral_finiteChoiceLaw (k : ℕ) (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : (∑ i, w i) = 1) (f : ℕ → ℝ) :
    ∫ a, f a ∂(finiteChoiceLaw k w hw hw1 : Measure ℕ) = ∑ i, w i * f i.val := by
  change ∫ a, f a ∂(∑ i : Fin k, ENNReal.ofReal (w i) • Measure.dirac i.val) = _
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw _),
      smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FusionTrajectory
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A probability measure on Baire addresses with a prescribed finite-history
transition law. The first coordinate is a dummy; later coordinates choose the
successive children. -/

open Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity
namespace FusionTrajectory

theorem history_restrict (n : ℕ) (x : ℕ → ℕ) :
    history n (frestrictLe n x) = PiNat.res (branch x) n := by
  apply PiNat.res_eq_res.mpr
  intro i hi
  simp only [frestrictLe_apply, branch]
  congr 1
  exact Nat.min_eq_left (by omega)

variable (step : List ℕ → ProbabilityMeasure ℕ)

theorem integral_next (n : ℕ) (g : List ℕ → ℕ → ℝ)
    (M : ℝ) (hM : ∀ l a, |g l a| ≤ M) :
    ∫ x, g (PiNat.res (branch x) n) (x (n + 1)) ∂measure step =
      ∫ h : History n, ∫ a, g (history n h) a ∂(step (history n h) : Measure ℕ)
        ∂(measure step).map (frestrictLe n) := by
  let f : History n × ℕ → ℝ := fun q => g (history n q.1) q.2
  have hfm : Measurable f := measurable_of_countable _
  have hf : Integrable f (((measure step).map (frestrictLe n)) ⊗ₘ transition step n) :=
    Integrable.of_bound hfm.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hM _ _)
  have heq := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => ℕ) (μ₀ := Measure.dirac (0 : ℕ)) (κ := transition step) (a := n)
  change _ = ∫ h : History n, ∫ a, f (h, a) ∂transition step n h
    ∂(measure step).map (frestrictLe n)
  rw [← Measure.integral_compProd hf]
  change _ = ∫ q, f q ∂(((measure step).map (frestrictLe n)) ⊗ₘ transition step n)
  rw [show ((measure step).map (frestrictLe n)) ⊗ₘ transition step n =
    (measure step).map (fun x => (frestrictLe n x, x (n + 1))) from heq]
  rw [integral_map (by fun_prop) hfm.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp only [f, history_restrict]

end FusionTrajectory
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ClosedFusionScheme
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested closed sets with uniformly shrinking children give a continuous
branch-limit map on Baire space. This is the topological part of law fusion. -/

open Set Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

namespace ClosedFusionScheme

variable {Z : Type*} [MetricSpace Z] (S : ClosedFusionScheme Z)

variable [CompleteSpace Z]

theorem limit_mem (x : ℕ → ℕ) (n : ℕ) : S.limit x ∈ S.carrier (PiNat.res x n) :=
  CantorScheme.map_mem _ n

end ClosedFusionScheme
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedFusionSmallSets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sigma-ideal of path-law candidates failing a prescribed countable/atomless
test. A finite atomless measure dominating any countable list of such tests is
constructed from the existing finite-measure representative of an s-finite measure. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y Z : Type*} [MetricSpace X]
  [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  (ι : C(X, Y))

omit [BorelSpace X] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [BorelSpace C(PathTime, Y)] in
/-- The extraction hypothesis makes the whole candidate space nonsmall. -/
theorem not_hitTestSmall_univ {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}
    (htest : ∀ D : Set X, D.Countable → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ∃ z, PassesHitTests ι C (law z) D ν) :
    ¬HitTestSmall ι law C univ := by
  rintro ⟨D, hD, ν, hν, hnull, hfail⟩
  obtain ⟨z, hz⟩ := htest D hD ν hν hnull
  exact hfail z (mem_univ z) hz

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteSupBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous finite weighted bound survives taking the independent
supremum in each coordinate. This will bound every tail of the fusion tree. -/

open Set

noncomputable section

namespace CircleDomainRigidity

theorem finite_weighted_sup_le {I Z : Type*} [Fintype I]
    (D : I → Set Z) (f : I → Z → ℝ) (w : I → ℝ)
    (hne : ∀ i, (D i).Nonempty)
    (hw : ∀ i, 0 ≤ w i) (hw1 : (∑ i, w i) = 1) {b : ℝ}
    (hbound : ∀ z : I → Z, (∀ i, z i ∈ D i) → ∑ i, w i * f i (z i) ≤ b) :
    ∑ i, w i * sSup (f i '' D i) ≤ b := by
  classical
  by_contra h
  let δ := ((∑ i, w i * sSup (f i '' D i)) - b) / 2
  have hδ : 0 < δ := by dsimp [δ] <;> linarith
  have hnear (i : I) : ∃ z ∈ D i, sSup (f i '' D i) - δ < f i z := by
    obtain ⟨v, ⟨z, hz, rfl⟩, hv⟩ := exists_lt_of_lt_csSup ((hne i).image (f i))
      (sub_lt_self _ hδ)
    exact ⟨z, hz, hv⟩
  choose z hzD hz using hnear
  have hs : (∑ i, w i * sSup (f i '' D i)) - δ ≤ b := calc
    (∑ i, w i * sSup (f i '' D i)) - δ =
        ∑ i, w i * (sSup (f i '' D i) - δ) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    _ ≤ ∑ i, w i * f i (z i) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hz i).le (hw i)
    _ ≤ b := hbound z hzD
  dsimp [δ] at hs
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedHitFusionCaps
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform upper bounds on a closed child control every continuation of a
fusion branch. The weighted sum of these bounds is the original split bound. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity.MarkedHit
namespace HitFusionSplit

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] {ι : C(X, Y)}
  [MetricSpace Z] [SecondCountableTopology Z]
  {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}
  {A : ClosedHitCandidate ι law C} {n : ℕ} {r ε η : ℝ}
  (S : HitFusionSplit ι law C A n r ε η)

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, Y)] [SecondCountableTopology Z] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem weighted_hitCap_le (p : HitConfiguration X n r) :
    ∑ i : Fin S.count, S.weight i * S.hitCap i.val p ≤ C + ε := by
  have h := finite_weighted_sup_le (fun i => (S.child i).carrier)
    (fun _ z => weightedConfigurationHits ι law z p) S.weight
    (fun i => (S.child i).nonempty) S.weight_nonneg S.weight_sum
    (fun z hz => (S.bound z hz p).le)
  simpa only [hitCap, index_val] using h

end HitFusionSplit
end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedHitFusionLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The law on the nested tree and its continuous limiting mixture. Every
scheduled configuration bound survives all subsequent refinements. -/

open Set Filter MeasureTheory ProbabilityTheory Preorder
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity.MarkedHit
namespace HitFusionData

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] {ι : C(X, Y)}
  [MetricSpace Z] [SecondCountableTopology Z]
  {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}
  (T : HitFusionData (ι := ι) (law := law) (C := C))

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, Y)] [SecondCountableTopology Z] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem childCap_bddAbove {n : ℕ} {r : ℝ} (l : List ℕ) (a : ℕ)
    (p : HitConfiguration X n r) :
    BddAbove ((fun z => weightedConfigurationHits ι law z p) '' (T.node (a :: l)).carrier) :=
  ⟨n, by rintro _ ⟨z, _, rfl⟩; exact weightedConfigurationHits_le_card ι law z p⟩

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, Y)] [SecondCountableTopology Z] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem le_childCap {n : ℕ} {r : ℝ} (l : List ℕ) (a : ℕ)
    (p : HitConfiguration X n r) {z : Z} (hz : z ∈ (T.node (a :: l)).carrier) :
    weightedConfigurationHits ι law z p ≤ T.childCap l a p :=
  le_csSup (T.childCap_bddAbove l a p) ⟨z, hz, rfl⟩

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, Y)] [SecondCountableTopology Z] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem childCap_nonneg {n : ℕ} {r : ℝ} (l : List ℕ) (a : ℕ)
    (p : HitConfiguration X n r) : 0 ≤ T.childCap l a p := by
  obtain ⟨z, hz⟩ := (T.node (a :: l)).nonempty
  exact (weightedConfigurationHits_nonneg ι law z p).trans (T.le_childCap l a p hz)

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, Y)] [SecondCountableTopology Z] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem childCap_le_card {n : ℕ} {r : ℝ} (l : List ℕ) (a : ℕ)
    (p : HitConfiguration X n r) : T.childCap l a p ≤ n := by
  apply csSup_le ((T.node (a :: l)).nonempty.image _)
  rintro _ ⟨z, _, rfl⟩
  exact weightedConfigurationHits_le_card ι law z p

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, Y)] [SecondCountableTopology Z] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem integral_childCap_le (l : List ℕ)
    (p : HitConfiguration X (T.sizes l.length) (T.separations l.length)) :
    ∫ a, T.childCap l a p ∂(T.step l : Measure ℕ) ≤ C + T.error := by
  rw [step, integral_finiteChoiceLaw]
  exact (T.splitAt l).weighted_hitCap_le p

variable [CompleteSpace Z]

omit [SecondCountableTopology X] [BorelSpace X]
    [BorelSpace C(PathTime, Y)] [SecondCountableTopology Z] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem endpoint_mem (x : ℕ → ℕ) (n : ℕ) :
    T.endpoint x ∈ (T.node (PiNat.res (FusionTrajectory.branch x) n)).carrier :=
  T.scheme.limit_mem _ _

omit [SecondCountableTopology Z] [SecondCountableTopology X] [BorelSpace X] in
theorem integral_endpoint_hits_le (hlaw : Continuous law) (d : ℕ)
    (p : HitConfiguration X (T.sizes d) (T.separations d)) :
    ∫ x, weightedConfigurationHits ι law (T.endpoint x) p
      ∂(T.addressLaw : Measure (ℕ → ℕ)) ≤ C + T.error := by
  let g : List ℕ → ℕ → ℝ := fun l a => T.childCap l a p
  have hg : ∀ l a, |g l a| ≤ T.sizes d := fun l a => by
    rw [abs_of_nonneg (T.childCap_nonneg l a p)]
    exact T.childCap_le_card l a p
  have hgm : Measurable (fun x : ℕ → ℕ =>
      g (PiNat.res (FusionTrajectory.branch x) d) (x (d + 1))) := by
    have hm : Measurable (fun q : FusionTrajectory.History d × ℕ =>
        g (FusionTrajectory.history d q.1) q.2) := measurable_of_countable _
    have hc : Measurable (fun x : ℕ → ℕ => (frestrictLe d x, x (d + 1))) :=
      (measurable_frestrictLe d).prodMk (measurable_pi_apply (d + 1))
    simpa only [Function.comp_def, FusionTrajectory.history_restrict] using hm.comp hc
  have hgi : Integrable
      (fun x => g (PiNat.res (FusionTrajectory.branch x) d) (x (d + 1)))
      (T.addressLaw : Measure (ℕ → ℕ)) := by
    refine Integrable.of_bound hgm.aestronglyMeasurable (T.sizes d) ?_
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hg _ _
  have hfi : Integrable (fun x => weightedConfigurationHits ι law (T.endpoint x) p)
      (T.addressLaw : Measure (ℕ → ℕ)) := by
    refine Integrable.of_bound ?_ (T.sizes d) ?_
    · exact ((weightedConfigurationHits_upperSemicontinuous ι hlaw _ _).comp
        (T.continuous_endpoint.prodMk continuous_const)).measurable.aestronglyMeasurable
    · exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (weightedConfigurationHits_nonneg ι law _ p)]
        exact weightedConfigurationHits_le_card ι law _ p
  calc
    ∫ x, weightedConfigurationHits ι law (T.endpoint x) p ∂(T.addressLaw : Measure (ℕ → ℕ)) ≤
        ∫ x, g (PiNat.res (FusionTrajectory.branch x) d) (x (d + 1))
          ∂(T.addressLaw : Measure (ℕ → ℕ)) := by
      apply integral_mono hfi hgi
      intro x
      exact T.le_childCap _ _ p (T.endpoint_mem x (d + 1))
    _ = ∫ h : FusionTrajectory.History d,
        ∫ a, g (FusionTrajectory.history d h) a
          ∂(T.step (FusionTrajectory.history d h) : Measure ℕ)
        ∂(FusionTrajectory.measure T.step).map (frestrictLe d) :=
      FusionTrajectory.integral_next T.step d g (T.sizes d) hg
    _ ≤ C + T.error := by
      have hnonneg (h : FusionTrajectory.History d) :
          0 ≤ ∫ a, g (FusionTrajectory.history d h) a
            ∂(T.step (FusionTrajectory.history d h) : Measure ℕ) :=
        integral_nonneg fun a => T.childCap_nonneg _ a p
      have hbound (l : List ℕ) (hl : l.length = d) :
          ∫ a, g l a ∂(T.step l : Measure ℕ) ≤ C + T.error := by
        subst d
        exact T.integral_childCap_le l p
      calc
        _ ≤ ∫ _ : FusionTrajectory.History d, C + T.error
            ∂(FusionTrajectory.measure T.step).map (frestrictLe d) :=
          integral_mono_of_nonneg (Eventually.of_forall hnonneg) (integrable_const _)
            (Eventually.of_forall fun h => hbound _ (by
              simp only [FusionTrajectory.history, PiNat.res_length]))
        _ = C + T.error := by
          have : IsProbabilityMeasure ((FusionTrajectory.measure T.step).map (frestrictLe d)) :=
            Measure.isProbabilityMeasure_map (measurable_frestrictLe d).aemeasurable
          simp

end HitFusionData
end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedHitFusion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fusion of a nonsmall closed family of path laws into a law with finite
point-hit square norm. All finite splitting and branch laws are constructed. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] (ι : C(X, Y))
  [MetricSpace Z] [SecondCountableTopology Z] [CompleteSpace Z]
  {law : Z → ProbabilityMeasure C(PathTime, Y)} {C : ℝ}

namespace HitFusionData

variable {ι}

variable (T : HitFusionData (ι := ι) (law := law) (C := C)) (hlaw : Continuous law)

omit [CompactSpace X] [SecondCountableTopology X] [BorelSpace X]
    [SecondCountableTopology Z] [SecondCountableTopology Y] [MeasurableSpace Y]
    [BorelSpace Y] in
theorem weighted_fusedLaw {n : ℕ} {r : ℝ} (p : HitConfiguration X n r) :
    weightedConfigurationHits ι (fun _ : Unit => T.fusedLaw hlaw) () p =
      ∫ x, weightedConfigurationHits ι law (T.endpoint x) p
        ∂(T.addressLaw : Measure (ℕ → ℕ)) := by
  unfold weightedConfigurationHits
  simp_rw [fusedLaw, pathHitReal_mixture ι]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact (integral_const_mul _ _).symm
  · intro i _
    exact (integrable_pathHitReal ι T.addressLaw
      (measurable_of_continuous_probability (hlaw.comp T.continuous_endpoint)) (p.val.1 i)).const_mul _

omit [CompactSpace X] [SecondCountableTopology Z] [SecondCountableTopology X]
    [BorelSpace X] in
theorem fusedLaw_configuration_bound (d : ℕ)
    (p : HitConfiguration X (T.sizes d) (T.separations d)) :
    weightedConfigurationHits ι (fun _ : Unit => T.fusedLaw hlaw) () p ≤ C + T.error := by
  rw [T.weighted_fusedLaw hlaw p]
  exact T.integral_endpoint_hits_le hlaw d p

end HitFusionData


theorem standardHitFusion_norm_bound (hlaw : Continuous law) (hC : 0 ≤ C)
    (root : ClosedHitCandidate ι law C) {ε : ℝ} (hε : 0 < ε) :
    HasHitNormBound ι ((standardHitFusion ι hlaw hC root ε hε).fusedLaw hlaw) (C + ε) := by
  apply hasHitNormBound_of_configuration_bounds ι _ ?_ (by positivity)
  intro n m
  have hb := (standardHitFusion ι hlaw hC root ε hε).fusedLaw_configuration_bound hlaw
    (Nat.pair n m)
  have hs : (standardHitFusion ι hlaw hC root ε hε).sizes (Nat.pair n m) = n := by
    change (Nat.unpair (Nat.pair n m)).1 = n
    rw [Nat.unpair_pair]
  have hr : (standardHitFusion ι hlaw hC root ε hε).separations (Nat.pair n m) =
      1 / ((m : ℝ) + 1) := by
    change 1 / (((Nat.unpair (Nat.pair n m)).2 : ℝ) + 1) = _
    rw [Nat.unpair_pair]
  rw [hs, hr] at hb
  exact hb

/-- The fused law is supported on original candidates, not merely limits of
arbitrary probability laws. Its positive point-hit support is countable. -/
theorem exists_hit_norm_mixture_of_nonsmall (hlaw : Continuous law) (hC : 0 ≤ C)
    {A : Set Z} (hAclosed : IsClosed A) (hA : ¬HitTestSmall ι law C A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : ProbabilityMeasure (ℕ → ℕ)) (e : C(ℕ → ℕ, Z)),
      (∀ x, e x ∈ A) ∧
      HasHitNormBound ι (probabilityMixture P (law ∘ e) (measurable_of_continuous_probability (hlaw.comp e.continuous)))
        (C + ε) := by
  let root : ClosedHitCandidate ι law C := ⟨A, hAclosed, hA⟩
  let T := standardHitFusion ι hlaw hC root ε hε
  refine ⟨T.addressLaw, ⟨T.endpoint, T.continuous_endpoint⟩, ?_, ?_⟩
  · intro x
    exact T.endpoint_mem x 0
  · exact standardHitFusion_norm_bound ι hlaw hC root hε

/-- The original countable and atomless tests supply the nonsmall root of the
constructed fusion tree. -/
theorem exists_hit_norm_mixture_of_countable_tests
    (hlaw : Continuous law) (hC : 0 ≤ C)
    (htest : ∀ D : Set X, D.Countable → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ∃ z, PassesHitTests ι C (law z) D ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : ProbabilityMeasure (ℕ → ℕ)) (e : C(ℕ → ℕ, Z)),
      HasHitNormBound ι (probabilityMixture P (law ∘ e)
        (measurable_of_continuous_probability (hlaw.comp e.continuous))) (C + ε) := by
  obtain ⟨P, e, _, hb⟩ := exists_hit_norm_mixture_of_nonsmall ι hlaw hC isClosed_univ
    (not_hitTestSmall_univ ι htest) hε
  exact ⟨P, e, hb⟩

end CircleDomainRigidity.MarkedHit

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ClosedSubsetHitFusion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fusion theorem applied to a closed dust subset. Its tests are ordinary
ambient measures supported on the dust, exactly as in the modulus extraction. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Z : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MetricSpace Z] [SecondCountableTopology Z] [CompleteSpace Z]

theorem exists_hit_norm_mixture_on_closed_subset
    (B : Set X) (hB : IsClosed B)
    (law : Z → ProbabilityMeasure C(PathTime, X)) (hlaw : Continuous law)
    {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ D : Set X, D.Countable → D ⊆ B → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ν Bᶜ = 0 →
        ∃ z, PassesHitTests C (law z) D ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : ProbabilityMeasure (ℕ → ℕ)) (e : C(ℕ → ℕ, Z)),
      let μ := probabilityMixture P (law ∘ e)
        (measurable_of_continuous_probability (hlaw.comp e.continuous))
      (∀ F : Finset B, ∑ x ∈ F, pathHitReal μ x.val ^ 2 ≤ (C + ε) ^ 2) ∧
        {x : X | x ∈ B ∧ 0 < pathHitProbability μ x}.Countable := by
  classical
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let ι : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have htest' : ∀ D : Set B, D.Countable → ∀ ν : Measure B,
      IsFiniteMeasure ν → NullSingletonClass ν →
        ∃ z, MarkedHit.PassesHitTests ι C (law z) D ν := by
    intro D hD ν hν hnull
    let : IsFiniteMeasure ν := hν
    let : NullSingletonClass ν := hnull
    let ρ : Measure X := ν.map (Subtype.val : B → X)
    have hρ : IsFiniteMeasure ρ := inferInstance
    have hρnull : NullSingletonClass ρ := by
      constructor
      intro x
      rw [show ρ = ν.map (Subtype.val : B → X) from rfl,
        Measure.map_apply continuous_subtype_val.measurable (measurableSet_singleton x)]
      by_cases hx : x ∈ B
      · have he : (Subtype.val : B → X) ⁻¹' {x} = {⟨x, hx⟩} := by
          ext y
          simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff]
        rw [he]
        exact measure_singleton _
      · have he : (Subtype.val : B → X) ⁻¹' {x} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hx ((mem_singleton_iff.mp hy) ▸ y.property)
        rw [he, measure_empty]
    have hρB : ρ Bᶜ = 0 := by
      rw [show ρ = ν.map (Subtype.val : B → X) from rfl,
        Measure.map_apply continuous_subtype_val.measurable hB.measurableSet.compl]
      simp
    obtain ⟨z, hz⟩ := htest (Subtype.val '' D) (hD.image _) (by
      rintro x ⟨y, _, rfl⟩
      exact y.property) ρ hρ hρnull hρB
    refine ⟨z, ?_, ?_⟩
    · intro F hF
      have hb := hz.1 (F.image (Subtype.val : B → X)) (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact mem_image_of_mem _ (hF hy))
      simpa only [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h),
        MarkedHit.pathHitReal, MarkedHit.pathHitProbability, pathHitReal, ι,
        ContinuousMap.coe_mk] using hb
    · change ∫⁻ x, pathHitProbability (law z) (x : X) ∂ν = 0
      rw [← lintegral_map (measurable_pathHitProbability_point (law z))
        continuous_subtype_val.measurable]
      exact hz.2
  obtain ⟨P, e, hb⟩ := MarkedHit.exists_hit_norm_mixture_of_countable_tests ι hlaw hC htest' hε
  refine ⟨P, e, hb, ?_⟩
  have hcount := hb.countable_positive_support
  have heq : Subtype.val '' {x : B | 0 < MarkedHit.pathHitProbability ι
      (probabilityMixture P (law ∘ e)
        (measurable_of_continuous_probability (hlaw.comp e.continuous))) x} =
      {x : X | x ∈ B ∧ 0 < pathHitProbability
        (probabilityMixture P (law ∘ e)
          (measurable_of_continuous_probability (hlaw.comp e.continuous))) x} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hh⟩
      exact ⟨⟨x, hx⟩, hh, rfl⟩
  rw [← heq]
  exact hcount.image _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ProbabilityMixtureMap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable pushforwards commute with the actual Borel probability mixture. -/

open MeasureTheory

noncomputable section
namespace CircleDomainRigidity

variable {Ω T Z : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSpace Z]

theorem probabilityMixture_map
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure Ω) (hlaw : Measurable law)
    (f : Ω → T) (hf : Measurable f) :
    (probabilityMixture P law hlaw).map (f := f) hf.aemeasurable =
      probabilityMixture P (fun z => (law z).map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
        ((measurable_probability_pushforward f hf).comp hlaw) := by
  apply Subtype.ext
  ext E hE
  change ((P : Measure Z).bind (fun z => (law z : Measure Ω))).map f E =
    ((P : Measure Z).bind (fun z => ((law z).map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure T))) E
  have hm : Measurable (fun z => (law z : Measure Ω)) :=
    measurable_subtype_coe.comp hlaw
  have hn : Measurable (fun z => ((law z).map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure T)) :=
    measurable_subtype_coe.comp ((measurable_probability_pushforward f hf).comp hlaw)
  rw [Measure.map_apply hf hE, Measure.bind_apply (hf hE) hm.aemeasurable,
    Measure.bind_apply hE hn.aemeasurable]
  apply lintegral_congr
  intro z
  exact (Measure.map_apply hf hE).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_BorelFamilyHitFusion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply compact-dust fusion to a Borel, mixture-closed family of code laws.
The compatible Polish refinement is constructed from the published
probability-space topology inputs and Mathlib's refinement theorem. -/

open Set Function MeasureTheory TopologicalSpace
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace Ω]

theorem exists_law_in_borel_family_with_hit_bound
    (hstandard : StandardBorelProbabilityLaws Ω)
    (hpath : PolishProbabilityLaws C(PathTime, X))
    (A : Set (ProbabilityMeasure Ω)) (hA : MeasurableSet A)
    (f : Ω → C(PathTime, X)) (hf : Measurable f)
    (hmix : ∀ (P : ProbabilityMeasure (ℕ → ℕ))
      (law : (ℕ → ℕ) → ProbabilityMeasure Ω) (hlaw : Measurable law),
      (∀ z, law z ∈ A) → probabilityMixture P law hlaw ∈ A)
    (B : Set X) (hB : IsClosed B) {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ D : Set X, D.Countable → D ⊆ B → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ν Bᶜ = 0 →
        ∃ μ ∈ A, PassesHitTests C (μ.map (f := f) hf.aemeasurable) D ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ μ ∈ A,
      (∀ F : Finset B, ∑ x ∈ F, pathHitReal (μ.map (f := f) hf.aemeasurable) x.val ^ 2 ≤ (C + ε) ^ 2) ∧
      {x : X | x ∈ B ∧ 0 < pathHitProbability (μ.map (f := f) hf.aemeasurable) x}.Countable := by
  let : StandardBorelSpace (ProbabilityMeasure Ω) := hstandard
  let : PolishSpace (ProbabilityMeasure C(PathTime, X)) := hpath.1
  let : BorelSpace (ProbabilityMeasure C(PathTime, X)) := hpath.2
  let : StandardBorelSpace A := hA.standardBorel
  let := upgradeStandardBorel A
  let law : A → ProbabilityMeasure C(PathTime, X) := fun μ => μ.val.map (f := f) hf.aemeasurable
  have hm : Measurable law := (measurable_probability_pushforward f hf).comp
    measurable_subtype_coe
  obtain ⟨t, hle, hc, ht⟩ := hm.exists_continuous
  have hbe : @BorelSpace A t inferInstance := by
    constructor
    rw [eq_borel_upgradeStandardBorel A, borel_eq_borel_of_le ht _ hle]
    first | exact Measure.isProbabilityMeasure_map (by first | exact hf.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : TopologicalSpace A := t
  let : PolishSpace A := ht
  let : BorelSpace A := hbe
  let := upgradeIsCompletelyMetrizable A
  have htest' : ∀ D : Set X, D.Countable → D ⊆ B → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ν Bᶜ = 0 →
        ∃ μ : A, PassesHitTests C (law μ) D ν := by
    intro D hD hDB ν hν hn hs
    obtain ⟨μ, hμ, hh⟩ := htest D hD hDB ν hν hn hs
    exact ⟨⟨μ, hμ⟩, hh⟩
  obtain ⟨P, e, hF, hcount⟩ :=
    exists_hit_norm_mixture_on_closed_subset B hB law hc hC htest' hε
  let codeLaw : (ℕ → ℕ) → ProbabilityMeasure Ω := fun z => (e z).val
  have hcode : Measurable codeLaw := measurable_subtype_coe.comp e.continuous.measurable
  let μ : ProbabilityMeasure Ω := probabilityMixture P codeLaw hcode
  have hmap : μ.map (f := f) hf.aemeasurable = probabilityMixture P (law ∘ e)
      (measurable_of_continuous_probability (hc.comp e.continuous)) := by
    exact probabilityMixture_map P codeLaw hcode f hf
  refine ⟨μ, hmix P codeLaw hcode (fun z => (e z).property), ?_, ?_⟩
  · simpa only [hmap] using hF
  · simpa only [hmap] using hcount

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawMixtures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mean occupation, tuple measure, and untagged path law of a code mixture
are the corresponding mixtures of the original means and path laws. -/

open MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] [MeasurableSpace Z]

theorem measurable_meanCodeTuple (d : PathCodeData X Y) :
    Measurable (meanCodeTuple d) :=
  (Measure.measurable_bind' (measurable_baseCodeTuple d)).comp measurable_subtype_coe

theorem meanCodeTuple_probabilityMixture (d : PathCodeData X Y)
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure (BasePathCode d))
    (hlaw : Measurable law) :
    meanCodeTuple d (probabilityMixture P law hlaw) =
      (P : Measure Z).bind (fun z => meanCodeTuple d (law z)) := by
  exact Measure.bind_bind (measurable_subtype_coe.comp hlaw).aemeasurable
    (measurable_baseCodeTuple d).aemeasurable

variable [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurable_meanCodeOccupation (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) : Measurable (meanCodeOccupation d) :=
  (Measure.measurable_bind' (measurable_baseCodeOccupation d hU)).comp measurable_subtype_coe

theorem meanCodeOccupation_probabilityMixture (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain)
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure (BasePathCode d))
    (hlaw : Measurable law) :
    meanCodeOccupation d (probabilityMixture P law hlaw) =
      (P : Measure Z).bind (fun z => meanCodeOccupation d (law z)) := by
  exact Measure.bind_bind (measurable_subtype_coe.comp hlaw).aemeasurable
    (measurable_baseCodeOccupation d hU).aemeasurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ProbabilitySquareBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Squared density and finite visit bounds survive probability mixtures.
These estimates allow the fused law to retain the original quantitative bounds. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]

theorem sq_lintegral_le_lintegral_sq_of_probability {f : Z → ℝ≥0∞}
    (hf : AEMeasurable f P) : (∫⁻ z, f z ∂P) ^ 2 ≤ ∫⁻ z, f z ^ 2 ∂P := by
  have hconj : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj hf
    (g := fun _ => 1) measurable_const.aemeasurable
  have hb : (∫⁻ z, f z ∂P) ≤ (∫⁻ z, f z ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
    simpa [Pi.mul_apply, ENNReal.rpow_two] using h
  apply (pow_le_pow_left' hb 2).trans_eq
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

theorem finite_square_moment_mixture_bound {I : Type*} (F : Finset I)
    (f : I → Z → ℝ≥0∞) (hf : ∀ i ∈ F, Measurable (f i))
    (E : ℝ≥0∞) (hE : ∀ᵐ z ∂P, ∑ i ∈ F, f i z ^ 2 ≤ E) :
    (∑ i ∈ F, (∫⁻ z, f i z ∂P) ^ 2) ≤ E := by
  calc
    _ ≤ ∑ i ∈ F, ∫⁻ z, f i z ^ 2 ∂P :=
      Finset.sum_le_sum fun i hi => sq_lintegral_le_lintegral_sq_of_probability P (hf i hi).aemeasurable
    _ = ∫⁻ z, ∑ i ∈ F, f i z ^ 2 ∂P :=
      (lintegral_finsetSum F (fun i hi => (hf i hi).pow_const 2)).symm
    _ ≤ ∫⁻ _z, E ∂P := lintegral_mono_ae hE
    _ = E := by simp

theorem density_square_integral_mixture_bound {X : Type*} [MeasurableSpace X]
    (σ : Measure X) [SFinite σ] (g : Z × X → ℝ≥0∞) (hg : Measurable g)
    (E : ℝ≥0∞) (hE : ∀ᵐ z ∂P, ∫⁻ x, g (z, x) ^ 2 ∂σ ≤ E) :
    (∫⁻ x, (∫⁻ z, g (z, x) ∂P) ^ 2 ∂σ) ≤ E := by
  calc
    _ ≤ ∫⁻ x, ∫⁻ z, g (z, x) ^ 2 ∂P ∂σ := by
      apply lintegral_mono
      intro x
      exact sq_lintegral_le_lintegral_sq_of_probability P
        (hg.comp measurable_prodMk_right).aemeasurable
    _ = ∫⁻ z, ∫⁻ x, g (z, x) ^ 2 ∂σ ∂P :=
      lintegral_lintegral_swap ((hg.comp measurable_swap).pow_const 2).aemeasurable
    _ ≤ ∫⁻ _z, E ∂P := lintegral_mono_ae hE
    _ = E := by simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableSquareLawBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably prescribed visit bounds define a Borel family of laws and are
preserved under probability mixtures. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Ω S Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]

theorem measurableSet_countableSquareLawBounds [Countable S]
    (v : S → Ω → ℝ≥0∞) (hv : ∀ s, Measurable (v s)) (budget : ℝ≥0∞) :
    MeasurableSet {μ : ProbabilityMeasure Ω | CountableSquareLawBounds v budget μ} := by
  simp only [CountableSquareLawBounds, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro F
  apply measurableSet_le _ measurable_const
  exact Finset.measurable_sum F fun s _ =>
    (((Measure.measurable_lintegral (hv s)).comp measurable_subtype_coe).pow_const 2)

theorem CountableSquareLawBounds.mixture
    (v : S → Ω → ℝ≥0∞) (hv : ∀ s, Measurable (v s)) (budget : ℝ≥0∞)
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure Ω) (hlaw : Measurable law)
    (hbound : ∀ᵐ z ∂(P : Measure Z), CountableSquareLawBounds v budget (law z)) :
    CountableSquareLawBounds v budget (probabilityMixture P law hlaw) := by
  intro F
  simp_rw [lintegral_probabilityMixture P law hlaw (hv _)]
  apply finite_square_moment_mixture_bound (P : Measure Z) F
    (fun s z => ∫⁻ w, v s w ∂(law z : Measure Ω))
    (fun s _ => (Measure.measurable_lintegral (hv s)).comp
      (measurable_subtype_coe.comp hlaw)) budget
  exact hbound.mono fun z hz => hz F

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DensityBudgetMixture
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint measurable densities and preservation of their budgets under
probability mixtures. This is applied separately to occupation and tuple kernels. -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
  [MeasurableSpace.CountablyGenerated X]

theorem jointly_measurable_densities_of_bounded_budget
    (μ : Z → Measure X) (hμ : Measurable μ) (σ : Measure X) [IsFiniteMeasure σ]
    (mass energy : ℝ≥0∞) (hmass : mass < ∞)
    (hbudget : ∀ z, BoundedDensityBudget σ (μ z) mass energy) :
    ∃ g : Z × X → ℝ≥0∞, Measurable g ∧ ∀ z,
      μ z = σ.withDensity (fun x => g (z, x)) ∧ (∫⁻ x, g (z, x) ^ 2 ∂σ) ≤ energy := by
  let κ : Kernel Z X := ⟨μ, hμ⟩
  let : IsFiniteKernel κ := ⟨⟨mass, hmass, fun z => (hbudget z).1⟩⟩
  let η : Kernel Z X := Kernel.const Z σ
  let g : Z × X → ℝ≥0∞ := fun p => κ.rnDeriv η p.1 p.2
  refine ⟨g, Kernel.measurable_rnDeriv κ η, ?_⟩
  intro z
  obtain ⟨f, hf, hμf, hfe⟩ := (hbudget z).2
  have hrn : (fun x => g (z, x)) =ᵐ[σ] (μ z).rnDeriv σ :=
    Kernel.rnDeriv_eq_rnDeriv_measure
  have hgf : (fun x => g (z, x)) =ᵐ[σ] f :=
    hrn.trans (by rw [hμf]; exact Measure.rnDeriv_withDensity σ hf)
  refine ⟨hμf.trans (withDensity_congr_ae hgf).symm, ?_⟩
  apply le_trans (le_of_eq (lintegral_congr_ae ?_)) hfe
  filter_upwards [hgf] with x hx
  exact congrArg (fun t : ℝ≥0∞ => t ^ 2) hx

theorem boundedDensityBudget_bind
    (μ : Z → Measure X) (hμ : Measurable μ) (σ : Measure X) [IsFiniteMeasure σ]
    (mass energy : ℝ≥0∞) (hmass : mass < ∞)
    (hbudget : ∀ z, BoundedDensityBudget σ (μ z) mass energy)
    (P : Measure Z) [IsProbabilityMeasure P] :
    BoundedDensityBudget σ (P.bind μ) mass energy := by
  obtain ⟨g, hg, hμg⟩ := jointly_measurable_densities_of_bounded_budget μ hμ σ
    mass energy hmass hbudget
  have hmass' : (P.bind μ) univ ≤ mass := by
    rw [Measure.bind_apply MeasurableSet.univ hμ.aemeasurable]
    calc
      _ ≤ ∫⁻ _z, mass ∂P := lintegral_mono fun z => (hbudget z).1
      _ = mass := by simp
  refine ⟨hmass', (fun x => ∫⁻ z, g (z, x) ∂P),
    (hg.comp measurable_swap).lintegral_prod_right', ?_, ?_⟩
  · ext s hs
    rw [Measure.bind_apply hs hμ.aemeasurable, withDensity_apply _ hs]
    simp_rw [(hμg _).1, withDensity_apply _ hs]
    exact lintegral_lintegral_swap hg.aemeasurable
  · exact density_square_integral_mixture_bound P σ g hg energy
      (Eventually.of_forall fun z => (hμg z).2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawCandidates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative family of code laws used in dust fusion is Borel and
closed under arbitrary Borel probability mixtures. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S Z : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]


omit [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_codeVisitWeight (d : PathCodeData X Y) (a : S → X) (s : S) :
    Measurable (codeVisitWeight d a s) :=
  measurable_visitCount.comp ((measurable_codePath d).prodMk measurable_const)

theorem measurableSet_codeLawCandidate [Countable S]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (a : S → X)
    (μ : Measure Y) [IsFiniteMeasure μ] (τ : Measure LevelTuple) [IsFiniteMeasure τ]
    (massOcc massTuple energy visitBudget : ℝ≥0∞)
    (hOcc : massOcc < ∞) (hTuple : massTuple < ∞) :
    MeasurableSet {P | CodeLawCandidate d a μ τ massOcc massTuple energy visitBudget P} := by
  exact (measurableSet_boundedDensityBudget (meanCodeOccupation d)
    (measurable_meanCodeOccupation d hU) μ massOcc energy hOcc).inter
    ((measurableSet_countableSquareLawBounds (codeVisitWeight d a)
      (measurable_codeVisitWeight d a) visitBudget).inter
    (measurableSet_boundedDensityBudget (meanCodeTuple d) (measurable_meanCodeTuple d)
      τ massTuple energy hTuple))

theorem CodeLawCandidate.mixture [MeasurableSpace Z]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (a : S → X)
    (μ : Measure Y) [IsFiniteMeasure μ] (τ : Measure LevelTuple) [IsFiniteMeasure τ]
    (massOcc massTuple energy visitBudget : ℝ≥0∞)
    (hOcc : massOcc < ∞) (hTuple : massTuple < ∞)
    (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure (BasePathCode d))
    (hlaw : Measurable law)
    (h : ∀ z, CodeLawCandidate d a μ τ massOcc massTuple energy visitBudget (law z)) :
    CodeLawCandidate d a μ τ massOcc massTuple energy visitBudget
      (probabilityMixture P law hlaw) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [meanCodeOccupation_probabilityMixture d hU P law hlaw]
    exact boundedDensityBudget_bind (fun z => meanCodeOccupation d (law z))
      ((measurable_meanCodeOccupation d hU).comp hlaw) μ massOcc energy hOcc
      (fun z => (h z).1) (P : Measure Z)
  · exact CountableSquareLawBounds.mixture (codeVisitWeight d a)
      (measurable_codeVisitWeight d a) visitBudget P law hlaw
      (Eventually.of_forall fun z => (h z).2.1)
  · rw [meanCodeTuple_probabilityMixture d P law hlaw]
    exact boundedDensityBudget_bind (fun z => meanCodeTuple d (law z))
      ((measurable_meanCodeTuple d).comp hlaw) τ massTuple energy hTuple
      (fun z => (h z).2.2) (P : Measure Z)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DensityMassBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite reference measure turns the square-density estimate into the
uniform mass cap needed for the Borel family of candidate laws. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

theorem mass_le_densityMassBound (σ : Measure X) {g : X → ℝ≥0∞}
    (hg : Measurable g) {energy : ℝ≥0∞} (henergy : (∫⁻ x, g x ^ 2 ∂σ) ≤ energy) :
    (σ.withDensity g) univ ≤ densityMassBound σ energy := by
  have hconj : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq σ hconj hg.aemeasurable
    (g := fun _ => 1) measurable_const.aemeasurable
  have hb : (∫⁻ x, g x ∂σ) ≤
      (∫⁻ x, g x ^ 2 ∂σ) ^ (1 / 2 : ℝ) * (σ univ) ^ (1 / 2 : ℝ) := by
    simpa [Pi.mul_apply, ENNReal.rpow_two] using h
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact hb.trans (mul_le_mul' (ENNReal.rpow_le_rpow henergy (by norm_num)) le_rfl)

theorem boundedDensityBudget_of_square_bound (σ : Measure X) (μ : Measure X)
    {g : X → ℝ≥0∞} (hg : Measurable g) (hμ : μ = σ.withDensity g)
    {energy : ℝ≥0∞} (henergy : (∫⁻ x, g x ^ 2 ∂σ) ≤ energy) :
    BoundedDensityBudget σ μ (densityMassBound σ energy) energy := by
  refine ⟨?_, g, hg, hμ, henergy⟩
  rw [hμ]
  exact mass_le_densityMassBound σ hg henergy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawCandidateBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative outputs of countable modulus extraction are members of
one fixed candidate family, independent of the prescribed countable set. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

omit [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem meanVisitCount_codePathLaw_eq_integral (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (a : S → X) (s : S) :
    meanVisitCount (codePathLaw d P) (a s) =
      ∫⁻ Γ, codeVisitWeight d a s Γ ∂(P : Measure (BasePathCode d)) := by
  have hv : Measurable (fun γ : C(PathTime, X) => visitCount γ (a s)) :=
    measurable_visitCount.comp (measurable_id.prodMk measurable_const)
  unfold meanVisitCount codePathLaw
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map hv (measurable_codePath d)]
  rfl

omit [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem countableSquareLawBounds_of_visit_norm (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (a : S → X) {C : ℝ≥0∞}
    (h : countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤ C) :
    CountableSquareLawBounds (codeVisitWeight d a) (C ^ 2) P := by
  intro F
  simp_rw [← meanVisitCount_codePathLaw_eq_integral]
  have he : countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ^ 2 =
      ∑' s, meanVisitCount (codePathLaw d P) (a s) ^ 2 := by
    rw [countingSquareNorm, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  exact (ENNReal.sum_le_tsum F).trans (he ▸ pow_le_pow_left' h 2)

omit [SecondCountableTopology Y] [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)] in
theorem codeLawCandidate_of_extracted_bounds (d : PathCodeData X Y)
    (a : S → X) (μ : Measure Y) (τ : Measure LevelTuple)
    (P : ProbabilityMeasure (BasePathCode d))
    {g : Y → ℝ≥0∞} {q : LevelTuple → ℝ≥0∞} (hg : Measurable g) (hq : Measurable q)
    (hocc : meanCodeOccupation d P = μ.withDensity g)
    (htuple : meanCodeTuple d P = τ.withDensity q)
    {E C : ℝ≥0∞} (hgE : (∫⁻ y, g y ^ 2 ∂μ) ≤ E)
    (hqE : (∫⁻ t, q t ^ 2 ∂τ) ≤ E)
    (hv : countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤ C) :
    CodeLawCandidate d a μ τ (densityMassBound μ E) (densityMassBound τ E) E (C ^ 2) P :=
  ⟨boundedDensityBudget_of_square_bound μ _ hg hocc hgE,
    countableSquareLawBounds_of_visit_norm d P a hv,
    boundedDensityBudget_of_square_bound τ _ hq htuple hqE⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableLawRestriction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction of the full mean-visit bound to any injectively indexed
subfamily of the prescribed marks. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem countingSquareNorm_comp_injective {A B : Type*} (v : B → ℝ≥0∞)
    (e : A → B) (he : Injective e) : countingSquareNorm (v ∘ e) ≤ countingSquareNorm v := by
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact ENNReal.tsum_comp_le_tsum_of_injective he (fun b => v b ^ 2)

theorem countingSquareNorm_restrict_range {X A B : Type*} (v : X → ℝ≥0∞)
    (a : A → X) (b : B → X) (ha : Injective a) (hab : range a ⊆ range b) :
    countingSquareNorm (v ∘ a) ≤ countingSquareNorm (v ∘ b) := by
  classical
  choose e he using fun s => hab (mem_range_self s)
  have hinj : Injective e := by
    intro s t h
    apply ha
    rw [← he s, ← he t, h]
  simpa only [Function.comp_def, he] using
    countingSquareNorm_comp_injective (v ∘ b) e hinj

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PositiveCodeLawFusion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fusion within the actual occupation/visit/tuple candidate family. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] [Countable S]

theorem exists_codeLawCandidate_with_hit_bound
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hstandard : StandardBorelProbabilityLaws (BasePathCode d))
    (hpath : PolishProbabilityLaws C(PathTime, X))
    (a : S → X) (μ : Measure Y) [IsFiniteMeasure μ]
    (τ : Measure LevelTuple) [IsFiniteMeasure τ]
    (M N E V : ℝ≥0∞) (hM : M < ∞) (hN : N < ∞)
    {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ D : Set X, D.Countable → D ⊆ d.dust → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ν d.dustᶜ = 0 →
        ∃ P, CodeLawCandidate d a μ τ M N E V P ∧
          PassesHitTests C (codePathLaw d P) D ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P, CodeLawCandidate d a μ τ M N E V P ∧
      (∀ F : Finset d.dust,
        ∑ x ∈ F, pathHitReal (codePathLaw d P) x.val ^ 2 ≤ (C + ε) ^ 2) ∧
      {x : X | x ∈ d.dust ∧ 0 < pathHitProbability (codePathLaw d P) x}.Countable := by
  exact exists_law_in_borel_family_with_hit_bound hstandard hpath
    {P | CodeLawCandidate d a μ τ M N E V P}
    (measurableSet_codeLawCandidate d hU a μ τ M N E V hM hN)
    (codePath d) (measurable_codePath d)
    (fun P law hlaw h => CodeLawCandidate.mixture d hU a μ τ M N E V hM hN
      P law hlaw h) d.dust hB hC htest hε

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableHitTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The visit estimate from modulus extraction supplies the finite point-hit
tests used by fusion, with the same numerical constant. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X A : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem finite_hit_square_sum_le_of_counting_norm
    (μ : ProbabilityMeasure C(PathTime, X)) (a : A → X)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : countingSquareNorm (fun s => meanVisitCount μ (a s)) ≤ ENNReal.ofReal C)
    (F : Finset X) (hF : (↑F : Set X) ⊆ range a) :
    ∑ x ∈ F, pathHitReal μ x ^ 2 ≤ C ^ 2 := by
  classical
  have hs : (∑' s, meanVisitCount μ (a s) ^ 2) ≤ (ENNReal.ofReal C) ^ 2 := by
    have he : countingSquareNorm (fun s => meanVisitCount μ (a s)) ^ 2 =
        ∑' s, meanVisitCount μ (a s) ^ 2 := by
      rw [countingSquareNorm, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
      norm_num
    rw [← he]
    exact pow_le_pow_left' hb 2
  let lift : F → A := fun x => Classical.choose (hF x.property)
  have hlift (x : F) : a (lift x) = x.val := Classical.choose_spec (hF x.property)
  have hinj : Injective lift := by
    intro x y h
    apply Subtype.ext
    rw [← hlift x, ← hlift y, h]
  have hsum : (∑ x : F, pathHitProbability μ x.val ^ 2) ≤ (ENNReal.ofReal C) ^ 2 := by
    calc
      _ ≤ ∑ x : F, meanVisitCount μ (a (lift x)) ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        rw [hlift]
        exact pow_le_pow_left' (pathHitProbability_le_meanVisitCount μ x.val) 2
      _ ≤ ∑' s, meanVisitCount μ (a s) ^ 2 :=
        calc
          _ = ∑ x ∈ Finset.univ.image lift, meanVisitCount μ (a x) ^ 2 := by
            rw [Finset.sum_image]
            exact fun _ _ _ _ h => hinj h
          _ ≤ _ := ENNReal.sum_le_tsum _
      _ ≤ _ := hs
  have hof : ENNReal.ofReal (∑ x ∈ F, pathHitReal μ x ^ 2) =
      ∑ x : F, pathHitProbability μ x.val ^ 2 := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    rw [← Finset.sum_coe_sort F]
    apply Finset.sum_congr rfl
    intro x _
    rw [ENNReal.ofReal_pow (pathHitReal_nonneg μ x.val), pathHitReal,
      ENNReal.ofReal_toReal (ne_of_lt ((pathHitProbability_le_one μ x.val).trans_lt (by simp)))]
  rw [← hof] at hsum
  have hsumreal := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hsum
  simpa only [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hC] using hsumreal

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableSetPresentation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable set can be indexed injectively by a closed subset of the
natural numbers, so the mark index has its usual discrete Polish structure. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

theorem countableSetPresentation {X : Type*} (D : Set X) (hD : D.Countable) :
    ∃ (I : Set ℕ) (p : I → X), IsClosed I ∧ Injective p ∧ range p = D := by
  let : Countable D := hD.to_subtype
  obtain ⟨f, hf⟩ := exists_injective_nat D
  let e : D ≃ range f := Equiv.ofInjective f hf
  let p : range f → X := fun i => (e.symm i).val
  refine ⟨range f, p, isClosed_discrete _, Subtype.val_injective.comp e.symm.injective, ?_⟩
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (e.symm i).property
  · intro hx
    exact ⟨e ⟨x, hx⟩, by simp [p]⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableExtractionFusion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable extraction supplies all tests in the fixed Borel candidate
family, so dust fusion retains the occupation and tuple density bounds. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] [Countable S]

theorem positive_code_law_of_countable_extraction
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hstandard : StandardBorelProbabilityLaws (BasePathCode d))
    (hpath : PolishProbabilityLaws C(PathTime, X))
    (a : S → X) (ha : Injective a) (haB : range a ⊆ d.dust)
    (μ : Measure Y) [IsFiniteMeasure μ] (τ : Measure LevelTuple) [IsFiniteMeasure τ]
    (E : ℝ≥0∞) (hE : E < ∞) {C : ℝ} (hC : 0 ≤ C)
    (hextract : ∀ (I : Set ℕ), IsClosed I → ∀ b : I → X, Injective b →
      range b ⊆ d.dust → ∀ ν : Measure X,
      IsFiniteMeasure ν → NullSingletonClass ν → ν d.dustᶜ = 0 →
        ∃ (P : ProbabilityMeasure (BasePathCode d)) (g : Y → ℝ≥0∞)
          (q : LevelTuple → ℝ≥0∞),
          Measurable g ∧ Measurable q ∧ meanCodeOccupation d P = μ.withDensity g ∧
          (∫⁻ y, g y ^ 2 ∂μ) ≤ E ∧
          countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (b s)) ≤
            ENNReal.ofReal C ∧
          meanCodeTuple d P = τ.withDensity q ∧ (∫⁻ t, q t ^ 2 ∂τ) ≤ E ∧
          (∫⁻ x, pathHitProbability (codePathLaw d P) x ∂ν) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P, CodeLawCandidate d a μ τ (densityMassBound μ E) (densityMassBound τ E)
        E ((ENNReal.ofReal C) ^ 2) P ∧
      (∀ F : Finset d.dust,
        ∑ x ∈ F, pathHitReal (codePathLaw d P) x.val ^ 2 ≤ (C + ε) ^ 2) ∧
      {x : X | x ∈ d.dust ∧ 0 < pathHitProbability (codePathLaw d P) x}.Countable := by
  apply exists_codeLawCandidate_with_hit_bound d hU hB hstandard hpath a μ τ
    (densityMassBound μ E) (densityMassBound τ E) E ((ENNReal.ofReal C) ^ 2)
    (densityMassBound_lt_top μ hE) (densityMassBound_lt_top τ hE) hC _ hε
  intro D hD hDB ν hν hn hνB
  obtain ⟨I, b, hI, hb, hbD⟩ :=
    countableSetPresentation (D ∪ range a) (hD.union (countable_range a))
  have hbB : range b ⊆ d.dust := by
    rw [hbD]
    exact union_subset hDB haB
  obtain ⟨P, g, q, hg, hq, hocc, hgE, hv, htuple, hqE, hhit⟩ :=
    hextract I hI b hb hbB ν hν hn hνB
  have hab : range a ⊆ range b := by rw [hbD]; exact subset_union_right
  have hva : countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤
      ENNReal.ofReal C :=
    (countingSquareNorm_restrict_range (meanVisitCount (codePathLaw d P)) a b ha hab).trans hv
  refine ⟨P, codeLawCandidate_of_extracted_bounds d a μ τ P hg hq hocc htuple hgE hqE hva,
    ?_, hhit⟩
  intro F hF
  exact finite_hit_square_sum_le_of_counting_norm (codePathLaw d P) b hC hv F
    (hF.trans (by rw [hbD]; exact subset_union_left))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PriorPositiveBarrierLaw
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCountableElemFirstUncountableIio _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full positive code law from failure of a small compatible barrier.
The countable extraction is invoked for every fusion test; the final law
keeps the quantitative occupation, fixed-mark visit, and tuple bounds. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r6edb4b_5 : BorelSpace Sphere := ⟨rfl⟩
theorem positive_code_law_of_no_small_level_barrier
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hEStar_anchor : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π d.dust p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint d.anchor (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : PriorLevelFamily d.physicalDomain π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      previous.graph i)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (flags : Set Sphere) (hflags : flags.Countable)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (htarget : d.target = p)
    (hcontours : d.gateContours = fun j => frontier (D j).region)
    (hgates : d.gateSets = fun _ => Subtype.val '' (f ⁻¹' closure W₂))
    {S : Type*} [Countable S] (a : S → Sphere) (ha : Injective a)
    (haB : range a ⊆ d.dust)
    [StandardBorelSpace (BasePathCode d)]
    (hstandard : StandardBorelProbabilityLaws (BasePathCode d))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (β : ℝ≥0∞)
    (hno : ∀ R : CompatibleLevelBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
      β ≤ R.controlledSize)
    (hdual : ∀ (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode d b c ν)],
      MeasureImageDuality (ConstrainedCostCode d b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode d b c ν)],
      MeasurePlanLifting (ConstrainedCostCode d b c ν) (PathCostSpace Sphere I))
    (r : ℝ≥0) (hrpos : 0 < r)
    (hrbound : (r : ℝ≥0∞) < (β / (2 * barrierConstructionConstant C)) ^ 2)
    (hunique : ∀ x ∈ d.dust \ flags, ∀ i t u,
      (t, x) ∈ d.levels i → (u, x) ∈ d.levels i → t = u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P, CodeLawCandidate d a sphericalArea (tupleReference ω)
        (densityMassBound sphericalArea (r : ℝ≥0∞)⁻¹)
        (densityMassBound (tupleReference ω) (r : ℝ≥0∞)⁻¹)
        (r : ℝ≥0∞)⁻¹ (((r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1) ^ 2) P ∧
      (∀ F : Finset d.dust,
        ∑ x ∈ F, pathHitReal (codePathLaw d P) x.val ^ 2 ≤
          (((r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1).toReal + ε) ^ 2) ∧
      {x : Sphere | x ∈ d.dust ∧
        0 < pathHitProbability (codePathLaw d P) x}.Countable := by
  let : IsFiniteMeasure (tupleReference ω) := finite_tupleReference hωsum
  have hr0 : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast hrpos.ne'
  have hE : (r : ℝ≥0∞)⁻¹ < ∞ := ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hr0)
  let K : ℝ≥0∞ := (r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1
  have hKt : K ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE.ne, by simp⟩
  have hKr : ENNReal.ofReal K.toReal = K := ENNReal.ofReal_toReal hKt
  suffices hs : ∃ P, CodeLawCandidate d a sphericalArea (tupleReference ω)
      (densityMassBound sphericalArea (r : ℝ≥0∞)⁻¹)
      (densityMassBound (tupleReference ω) (r : ℝ≥0∞)⁻¹)
      (r : ℝ≥0∞)⁻¹ ((ENNReal.ofReal K.toReal) ^ 2) P ∧
      (∀ F : Finset d.dust,
        ∑ x ∈ F, pathHitReal (codePathLaw d P) x.val ^ 2 ≤ (K.toReal + ε) ^ 2) ∧
      {x : Sphere | x ∈ d.dust ∧
        0 < pathHitProbability (codePathLaw d P) x}.Countable by
    simpa only [hKr] using hs
  apply positive_code_law_of_countable_extraction d hU hB hstandard hpath a ha haB
    sphericalArea (tupleReference ω) (r : ℝ≥0∞)⁻¹ hE ENNReal.toReal_nonneg _ hε
  intro I hI b hb hbB ν hν hn hνB
  let : PolishSpace I := hI.polishSpace
  let : IsFiniteMeasure ν := hν
  let : NullSingletonClass ν := hn
  obtain ⟨c, hc0, hct, _, hc⟩ := exists_positive_finite_square_weights I
  let : StandardBorelSpace (FiniteCostCode d b c) := standardBorel_finiteCostCode d hU b c
  let : StandardBorelSpace (ConstrainedCostCode d b c ν) :=
    standardBorel_constrainedCostCode d b c ν hB
  obtain ⟨P, g, q, hg, hq, hocc, hgE, hv, htuple, hqE, _, hhit, _⟩ :=
    prescribed_countable_law_of_no_small_level_barrier hcoarea hLusin hsard hsch
      d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad ν hinf
      EStar hEStar_anchor hEU hEStar hEStarE hinfE p hpDust hp D hnest hshrink hED
      f hf W₁ W₂ hW₁ hW₂ hW₁₂ hfiber harcs previous hlevels hweights hpoint flags hflags
      C hC hderiv htarget hcontours hgates b hb hbB c hc ω hω β hno hωsum
      (hdual I b c ν) (hlift I b c ν) r hrpos hrbound hc0 hct hνB hunique
  refine ⟨P, g, q, hg, hq, hocc, hgE, ?_, htuple, hqE, hhit⟩
  rw [hKr]
  exact hv

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableDeletions
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite increasing deletions exhausting a prescribed countable mark set. -/

open Set Function Filter

noncomputable section
namespace CircleDomainRigidity

theorem exists_finite_deletions {X : Type*} (S : Set X) (hS : S.Countable) :
    ∃ F : ℕ → Finset X, Monotone F ∧ (∀ n, (F n : Set X) ⊆ S) ∧
      ∀ x ∈ S, ∀ᶠ n in atTop, x ∈ F n := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => ∅, fun _ _ _ => le_rfl, by simp, by simp⟩
  obtain ⟨f, rfl⟩ := hS.exists_eq_range hne
  refine ⟨fun n => (Finset.range n).image f, ?_, ?_, ?_⟩
  · intro m n hmn
    exact Finset.image_mono f (Finset.range_mono hmn)
  · intro n x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact mem_range_self i
  · rintro x ⟨i, rfl⟩
    exact eventually_atTop.2 ⟨i + 1, fun n hn =>
      Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self i) hn), rfl⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DustPriorContacts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prior constraints only charge residual times in the dust. Consequently
their finite-toll argument only needs visit bounds at dust marks; a possible
atom at the image of infinity does not impose an extra path constraint. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem support_dustPriorHitMass {X : Type*} [MetricSpace X]
    [MeasurableSpace C(PathTime, X)] (B : Set X) (μ : Measure C(PathTime, X)) :
    support (dustPriorHitMass B μ) = B ∩ support (priorHitMass μ) := by
  ext x
  by_cases hx : x ∈ B <;> simp [dustPriorHitMass, hx]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PriorLawPresentation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The countable data attached to a recursion stage: every earlier law is
retained, its hit support has finite deletions, and every required dust mark
is among the marks prescribed to the next positive-law construction. -/

open Set Function Filter MeasureTheory

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem nonempty_priorLawPresentation (B S : Set X) (μ : ℕ → Measure C(PathTime, X))
    (hS : S.Countable) (hSB : S ⊆ B)
    (hμ : ∀ i, (support (priorHitMass (μ i))).Countable) :
    Nonempty (PriorLawPresentation B S μ) := by
  classical
  let M := S ∪ ⋃ i, support (dustPriorHitMass B (μ i))
  have hM : M.Countable := hS.union (countable_iUnion fun i => by
    rw [support_dustPriorHitMass]
    exact (hμ i).mono inter_subset_right)
  have hMB : M ⊆ B := by
    rintro x (hx | hx)
    · exact hSB hx
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ((support_dustPriorHitMass B (μ i)) ▸ hi).1
  choose F hFm hFs hFc using fun i => exists_finite_deletions _ (hμ i)
  obtain ⟨L, hLm, hLs, hLc⟩ := exists_finite_deletions S hS
  exact ⟨{
    marks := M
    marks_countable := hM
    marks_dust := hMB
    extra_marks := subset_union_left
    prior_marks := fun i x hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
    priorDeletions := F
    prior_monotone := hFm
    prior_subset := hFs
    prior_cover := hFc
    flagDeletions := L
    flag_monotone := hLm
    flag_subset := hLs
    flag_cover := hLc }⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RelativelyClosedGates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collar gates need be closed only on their closed contour. The preimage
of a closed target set under a map on the open domain has exactly this
property, even when its ambient closure reaches the boundary. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]

 theorem isClosed_contour_gate {U C : Set X} (hC : IsClosed C) (hCU : C ⊆ U)
    {f : U → Y} (hf : Continuous f) {W : Set Y} (hW : IsClosed W) :
    IsClosed (C ∩ (Subtype.val '' (f ⁻¹' W))) := by
  let g : C → Y := fun x => f ⟨x.val, hCU x.property⟩
  have hg : Continuous g := hf.comp (continuous_subtype_val.subtype_mk _)
  have hs : IsClosed (Subtype.val '' (g ⁻¹' W)) :=
    hC.isClosedMap_subtype_val _ (hW.preimage hg)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  constructor
  · rintro ⟨hx, y, hy, hyx⟩
    subst x
    exact ⟨⟨y.val, hx⟩, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, ⟨x.val, hCU x.property⟩, hx, rfl⟩

 theorem gateRule_inter_contour {C K : Set X} (γ : C(PathTime, X)) :
    GateRule C (C ∩ K) γ ↔ GateRule C K γ :=
  ⟨fun h t ht => (h t ht).2, fun h t ht => ⟨ht, h t ht⟩⟩

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

 theorem measurableSet_gateRules_of_inter_closed {C K : ℕ → Set X}
    (hC : ∀ n, IsClosed (C n)) (hCK : ∀ n, IsClosed (C n ∩ K n)) :
    MeasurableSet {γ | GateRules C K γ} := by
  have heq : {γ | GateRules C K γ} = {γ | GateRules C (fun n => C n ∩ K n) γ} := by
    ext γ
    exact forall_congr' fun n => (gateRule_inter_contour γ).symm
  rw [heq]
  exact measurableSet_gateRules hC hCK

variable [MeasurableSpace X]

variable [BorelSpace X] [SecondCountableTopology X] [CompleteSpace X]

 theorem standardBorel_basePathCode_of_inter_closed (d : PathCodeData X X)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) [∀ i, SFinite (d.priorLaws i)]
    (hprior : ∀ i, (support (priorHitMass (d.priorLaws i))).Countable)
    (hlevel : ∀ i, (support (d.levelWeights i)).Countable)
    (hE : MeasurableSet d.anchor)
    (hC : ∀ i, IsClosed (d.gateContours i))
    (hCK : ∀ i, IsClosed (d.gateContours i ∩ d.gateSets i)) :
    StandardBorelSpace (BasePathCode d) := by
  have hm : MeasurableSet {Γ | EndpointCode d 0 (fun _ _ => ∅) Γ} :=
    (measurableSet_allowedTaggedPath d hU hB hH hprior hlevel 0
      (fun _ _ => MeasurableSet.empty)).inter
      ((measurableSet_endpointCodes hE d.target).inter
        ((measurableSet_gateRules_of_inter_closed hC hCK).preimage measurable_fst))
  exact hm.standardBorel

attribute [local instance] sphereMetric sphereBorel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_GatedRecursiveLaw
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Failure of a small compatible real barrier constructs the recursive law
with the prescribed collar gates and actual prior-law presentation. The
code space is Borel because the gates are closed on their contours. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r6edb4b_6 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_gated_recursive_law_of_no_small_barrier
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀ x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (p : Sphere) (hp : p ∈ d.dust)
    {g : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π d.dust p g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 p, ∃ k : ℕ, ∀ n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint d.anchor (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : PriorLevelFamily d.physicalDomain π)
    (hlevels : ∀ i, d.levels i = Prod.swap ⁻¹' previous.graph i)
    (hweights : ∀ i, (∑' x, d.levelWeights i x ^ 2) < ∞)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (flags : Set Sphere) (hflags : flags.Countable) (hflagsB : flags ⊆ d.dust)
    (hmarked : ∀ i, support (d.levelWeights i) ⊆ flags)
    (hunique : ∀ x ∈ d.dust \ flags, ∀ i t u,
      (t, x) ∈ d.levels i → (u, x) ∈ d.levels i → t = u)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (β : ℝ≥0∞) (hβ : 0 < β)
    (hno : ∀ R : CompatibleLevelBarrier d π previous flags EStar
      (fun n => (D n).region) f W₁, β ≤ R.controlledSize)
    (μ : ℕ → Measure C(PathTime, Sphere))
    (hfinite : ∀ n, IsFiniteMeasure (μ n))
    (hμ : ∀ n, (support (priorHitMass (μ n))).Countable) :
    ∃ L : RecursiveCodeLaw d π flags ω,
      L.data.target = p ∧ L.data.priorLaws = μ ∧
      L.data.gateContours = (fun n => frontier (D n).region) ∧
      L.data.gateSets = (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) := by
  let P := Classical.choice (nonempty_priorLawPresentation d.dust flags μ hflags hflagsB hμ)
  let G := RecursiveCodeGeometry.of_presentation d π he p hp P
    (fun n => frontier (D n).region) (fun _ => Subtype.val '' (f ⁻¹' closure W₂))
  let e := G.data
  let prev : PriorLevelFamily e.physicalDomain π := previous
  let : ∀ n, IsFiniteMeasure (e.priorLaws n) := hfinite
  let : Countable P.marks := P.marks_countable.to_subtype
  have hH (i : ℕ) : IsClosed (e.levels i) := by
    rw [show e.levels i = d.levels i from rfl, hlevels]
    exact (previous.closed i).preimage continuous_swap
  have hcontours : ∀ n, IsClosed (e.gateContours n) := fun _ => isClosed_frontier
  have hgates : ∀ n, IsClosed (e.gateContours n ∩ e.gateSets n) := by
    intro n
    apply isClosed_contour_gate isClosed_frontier ?_ hf isClosed_closure
    exact (D n).frontier_region_subset_quotient d π hπ he
      ((D n).isOpen_region hπ hclosed hsurj hr)
  let : StandardBorelSpace (BasePathCode e) := standardBorel_basePathCode_of_inter_closed
    e hU hB hH hμ (fun i => hflags.mono (hmarked i)) hE.measurableSet hcontours hgates
  have hno' (R : CompatibleLevelBarrier e π prev flags EStar (fun n => (D n).region) f W₁) :
      β ≤ R.controlledSize := by
    have h := hno (R.rebase rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl))
    exact h
  obtain ⟨r, hrpos, hrbound⟩ := exists_positive_barrier_duality_parameter C hβ
  obtain ⟨Q, hQ, htest, hcount⟩ := positive_code_law_of_no_small_level_barrier
    hcoarea hLusin hsard hsch e hU hG hdisj π hπ hclosed hsurj hr he
    hB hTD hBU hdense hinfty hbad hinf EStar hE hEU hEStar hEStarE hinfE
    p hp (fun h => hinfty (h ▸ hp)) D hnest hshrink hED f hf W₁ W₂ hW₁ hW₂ hW₁₂
    hfiber harcs prev hlevels (fun i => (hweights i).ne) hpoint flags hflags C hC hderiv
    rfl rfl rfl (fun x : P.marks => x.val) Subtype.val_injective
    (by rintro _ ⟨x, rfl⟩; exact P.marks_dust x.property)
    (hstandard e) hpath ω hω hωsum β hno' (hdual e) (hlift e)
    r hrpos hrbound hunique (by norm_num : (0 : ℝ) < 1)
  exact ⟨RecursiveCodeLaw.of_positive_candidate G ω r hrpos 1 Q hQ htest hcount,
    rfl, rfl, rfl, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AnchoredMeanCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nested collars for a finite marked point can simultaneously
avoid the closed source anchor and the quotient point at infinity. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric

 theorem exists_anchored_shrinking_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G U B E : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hB : IsClosed B) (hTD : IsTotallyDisconnected B) (hdisj : Disjoint U B)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B) (hE : IsClosed E) (hEU : E ⊆ U)
    (hinfty : π OnePoint.infty ∉ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ OnePoint.infty) :
    ∃ D : ℕ → WeightedCollar G π B p (fun _ => 0),
      (∀ n, closure (D (n+1)).region ⊆ (D n).region) ∧
      (∀ W ∈ 𝓝 p, ∃ k : ℕ, ∀ n ≥ k, closure (D n).region ⊆ W) ∧
      Disjoint E (closure (D 0).region) ∧ OnePoint.infty ∉ closure (D 0).region := by
  have hpE : p ∉ E := fun hx => disjoint_left.mp hdisj (hEU hx) hpB
  have hpi : p ≠ π OnePoint.infty := fun h => hinfty (h ▸ hpB)
  obtain ⟨D, hD, hnest, _, hshrink⟩ := exists_shrinking_weighted_collars
    hcoarea hsard hsch G π hπ hclosed hsurj hr hB hTD hbad hpB hpi
    (hE.isOpen_compl.inter isClosed_singleton.isOpen_compl) ⟨hpE, hp⟩
    (fun _ => 0) measurable_const (by simp)
  refine ⟨D, hnest, (fun W hW => by
    obtain ⟨k, hk⟩ := hshrink W hW
    exact ⟨k, fun n hn => (hk n hn).1⟩), disjoint_left.mpr ?_, ?_⟩
  · intro x hxE hxD
    exact (hD hxD).1 hxE
  · intro hx
    exact (hD hx).2 rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionAnchors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact nested endpoint anchors retain the actual protrusion test anchor
and the normalized point at infinity, while remaining inside the quotient domain. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem FiniteTransfer.LocalEndTestGeometry.exists_endpoint_anchors
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
    {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)
    (hU : IsOpen U) (hπ : Continuous π) (e : G ≃ₜ U)
    (he : ∀ x : G, (e x).val = π x.val) :
    ∃ EStar Anchor : Set Sphere, IsCompact EStar ∧ IsClosed Anchor ∧
      EStar ⊆ interior Anchor ∧ Anchor ⊆ U ∧
      π OnePoint.infty ∈ interior EStar ∧
      (∀ z ∈ closure (jordanInterior T.sourceAnchor), π (z : Sphere) ∈ EStar) := by
  have hinfty : OnePoint.infty ∈ G := M.core_source 0 (M.plane_core 0 (Or.inr rfl))
  let K : Set Sphere := {π OnePoint.infty} ∪
    π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior T.sourceAnchor))
  have hK : IsCompact K := isCompact_singleton.union
    (((isCompact_closure_jordanInterior T.sourceAnchor).image OnePoint.continuous_coe).image hπ)
  have hKU : K ⊆ U := by
    rintro x (hx | ⟨_, ⟨z, hz, rfl⟩, rfl⟩)
    · rw [mem_singleton_iff] at hx
      rw [hx, ← he ⟨_, hinfty⟩]
      exact (e ⟨_, hinfty⟩).property
    · rw [← he ⟨_, T.source_inside hz⟩]
      exact (e ⟨_, T.source_inside hz⟩).property
  obtain ⟨EStar, hcompact, _, hKE, hEU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨Anchor, _, hclosed, hEA, hAU⟩ := exists_compact_closed_between hcompact hU hEU
  refine ⟨EStar, Anchor, hcompact, hclosed, hEA, hAU, hKE (Or.inl rfl), ?_⟩
  intro z hz
  exact interior_subset (hKE (Or.inr ⟨_, ⟨z, hz, rfl⟩, rfl⟩))

 theorem FiniteTransfer.LocalEndTestGeometry.exists_endpoint_anchors_retaining
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
    {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)
    (hU : IsOpen U) (hπ : Continuous π) (e : G ≃ₜ U)
    (he : ∀ x : G, (e x).val = π x.val)
    (E₀ : Set Sphere) (hE₀ : IsCompact E₀) (hE₀U : E₀ ⊆ U) :
    ∃ EStar Anchor : Set Sphere, IsCompact EStar ∧ IsClosed Anchor ∧
      EStar ⊆ interior Anchor ∧ Anchor ⊆ U ∧
      E₀ ⊆ interior EStar ∧ π OnePoint.infty ∈ interior EStar ∧
      (∀ z ∈ closure (jordanInterior T.sourceAnchor), π (z : Sphere) ∈ EStar) := by
  obtain ⟨E₁, A₁, hE₁, _, hE₁A₁, hA₁U, hinfty1, hsource⟩ :=
    T.exists_endpoint_anchors hU hπ e he
  have hE₁U : E₁ ⊆ U := fun x hx => hA₁U (interior_subset (hE₁A₁ hx))
  obtain ⟨EStar, hcompact, _, hKE, hEU⟩ :=
    exists_compact_closed_between (hE₀.union hE₁) hU (union_subset hE₀U hE₁U)
  obtain ⟨Anchor, _, hclosed, hEA, hAU⟩ := exists_compact_closed_between hcompact hU hEU
  refine ⟨EStar, Anchor, hcompact, hclosed, hEA, hAU,
    (fun _ hx => hKE (Or.inl hx)), hKE (Or.inr (interior_subset hinfty1)), ?_⟩
  intro z hz
  exact interior_subset (hKE (Or.inr (hsource z hz)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_GatedQuotientMap
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized map on the quotient domain. Its finite physical
formula is required only over the bounded target gate, which misses infinity. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem quotientNormalizedMap_continuous {G U : Set Sphere} (e : G ≃ₜ U) (F : ℂ → ℂ)
    (hF : IsConformalOn (extendAtInfinity F) G) : Continuous (quotientNormalizedMap e F) := by
  have hc : Continuous (fun x : G => extendAtInfinity F x.val) :=
    continuousOn_iff_continuous_domRestrict.mp (fun x hx => (hF x hx).1.continuousWithinAt)
  exact hc.comp e.symm.continuous

 theorem quotientNormalizedMap_physical {G U : Set Sphere} (e : G ≃ₜ U)
    (π : Sphere → Sphere) (he : ∀ x : G, (e x).val = π x.val) (F : ℂ → ℂ)
    (z : ℂ) (hz : (z : Sphere) ∈ G) :
    quotientNormalizedMap e F ⟨π (z : Sphere), (he ⟨_, hz⟩) ▸ (e ⟨_, hz⟩).property⟩ =
      (F z : Sphere) := by
  have h : (⟨π (z : Sphere), (he ⟨_, hz⟩) ▸ (e ⟨_, hz⟩).property⟩ : U) = e ⟨_, hz⟩ :=
    Subtype.ext (he ⟨(z : Sphere), hz⟩).symm
  simp only [quotientNormalizedMap, h, e.symm_apply_apply, extendAtInfinity_coe]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionGateGeometry
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual protrusion balls give the two target gates and a uniform
positive distance from the marked disk. The normalized source map stays
outside that disk throughout its physical domain. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

namespace LocalEndTestGeometry
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)

 theorem closed_closedGate : IsClosed T.closedGate :=
  OnePoint.isClosed_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall _ _⟩

 theorem open_openGate : IsOpen T.openGate := OnePoint.isOpen_image_coe.mpr isOpen_ball

 theorem closedGate_subset_openGate : T.closedGate ⊆ T.openGate :=
  image_mono (closedBall_subset_ball (by linarith [T.radius_pos]))

end LocalEndTestGeometry

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetargetedCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport a constructed weighted collar along an equality of target
points without changing its physical disk or quotient region. -/
open Set
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity.WeightedCollar
variable {G B : Set Sphere} {π : Sphere → Sphere} {p q : Sphere} {g : ℂ → ℝ≥0∞}

 theorem region_retarget (D : WeightedCollar G π B p g) (h : q = p) :
    (D.retarget h).region = D.region := by
  subst q
  rfl

end CircleDomainRigidity.WeightedCollar

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionAlternatives
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a marked-component protrusion, either a small compatible real
barrier exists, or positive-law duality constructs a compatible mean
coordinate with an open sized exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_31
theorem exists_protrusion_barrier_or_selectable_mean
    {I : Type*} [LinearOrder I] (rank : ℕ → I) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ base.quotientDomainᶜ)
    (C : ℕ → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val))
    (presentation : ∀ i, SelectedLevelPresentation hsch base π (C i))
    (hlevel : ∀ i, base.levels i = Prod.swap ⁻¹' (C i).graph)
    (hweights : ∀ i, base.levelWeights i = (C i).dustWeight)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ Flags)
    (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
    (hP : RankedLevelNullCompatibility rank base.levels (base.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ D : Set Sphere, IsCompact D → LocallyConnectedSpace D →
      HasSimpleArcsInConnectedOpens D)
    (previous : PriorLevelFamily base.physicalDomain π)
    (hprevious : ∀ i, previous.graph i = (C i).graph)
    (hweighted : WeightedPlanarScalarCoarea) (hcollar : SmoothRegularJordanCollars)
    (hselect : BorelPathRelationSelection)
    (Candidates : Set (SelectableMaskedCoordinate base π))
    (label : SelectableMaskedCoordinate base π → ℕ)
    (hflags : ∀ c ∈ Candidates, c.flags ⊆ Flags)
    (hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c))
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
    (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
    (s : S) (hqs : π q = σ s) (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hseparated : Disjoint (Metric.closedBall T.center (2 * T.radius))
      (Metric.closedBall (A.center s) (A.radius s)))
    {g : ℂ → ℝ≥0∞}
    (D : ℕ → WeightedCollar base.physicalDomain π base.dust (σ s) g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 (σ s), ∃ k : ℕ, ∀ n ≥ k, closure (D n).region ⊆ V)
    (hanchor : Disjoint base.anchor (closure (D 0).region))
    (hfinite : OnePoint.infty ∉ closure (D 0).region)
    (EStar : Set Sphere) (hE : IsClosed base.anchor) (hEU : base.anchor ⊆ base.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior base.anchor)
    (hinfE : π OnePoint.infty ∈ interior base.anchor)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ base.levels i} ≤ base.levelWeights i x)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C₀ / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (B R : ℝ) (hB : B / 4 < M.radius) (hR : 5 * M.radius < R)
    (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ base.anchor) :
    (∃ P : CompatibleLevelBarrier base π previous Flags EStar
      (fun n => (D n).region) (quotientNormalizedMap base.domainEquiv A.function) T.closedGate,
      P.controlledSize < ENNReal.ofReal T.selectionThreshold) ∨
    ∃ c : SelectableMaskedCoordinate base π, c.CompatibleWith Candidates ∧
      Nonempty (MeanCoordinatePresentation hsch base π c.coordinate) ∧
      (c.coordinate.singular : Sphere) = σ s ∧
      ∃ W : MeanExclusionWitness c.coordinate A.function (A.plane_open_embedding hG).1
        (A.center s) ⟨A.radius s, (A.bounds s).2.1⟩ R,
        (∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ < B) ∧
        ((finiteSourceMap A.function (A.plane_open_embedding hG).1,
          A.center s, (⟨A.radius s, (A.bounds s).2.1⟩ : ℝ≥0)), M.radius) ∈
            W.sizedNeighborhood (B / 4) := by
  classical
  by_cases hsmall : ∃ P : CompatibleLevelBarrier base π previous Flags EStar
      (fun n => (D n).region) (quotientNormalizedMap base.domainEquiv A.function) T.closedGate,
      P.controlledSize < ENNReal.ofReal T.selectionThreshold
  · exact Or.inl hsmall
  apply Or.inr
  have hinfty : π OnePoint.infty ∉ base.dust := by
    rw [hdust, ← he ⟨_, hinf⟩]
    exact not_not.mpr (base.domainEquiv ⟨_, hinf⟩).property
  have hpB : σ s ∈ base.dust := by
    rw [← hqs, hdust]
    exact hbad q hq
  have hp : σ s ≠ π OnePoint.infty := fun h => hinfty (h ▸ hpB)
  have hlevels : ∀ i, base.levels i = Prod.swap ⁻¹' previous.graph i := by
    intro i
    rw [hlevel, hprevious]
  have hweightsFinite : ∀ i, (∑' x, base.levelWeights i x ^ 2) < ∞ := by
    intro i
    rw [hweights]
    exact (C i).dustWeight_square_sum
  have hunique' : ∀ x ∈ base.dust \ Flags, ∀ i t u,
      (t, x) ∈ base.levels i → (u, x) ∈ base.levels i → t = u := by
    simpa only [hdust] using hunique
  have hno : ∀ P : CompatibleLevelBarrier base π previous Flags EStar
      (fun n => (D n).region) (quotientNormalizedMap base.domainEquiv A.function) T.closedGate,
      ENNReal.ofReal T.selectionThreshold ≤ P.controlledSize := by
    intro P
    exact le_of_not_gt (fun h => hsmall ⟨P, h⟩)
  obtain ⟨L, htarget, _, hcontours, hgates⟩ := exists_gated_recursive_law_of_no_small_barrier
    hweighted hLusin hsard hsch base hU hG
    (by rw [hdust]; exact disjoint_compl_right) π hπ hclosed hsurj hr he
    (by rw [hdust]; exact hU.isClosed_compl) (by simpa only [hdust] using hTD)
    (by rw [hdust, compl_compl]) hdense hinfty
    (by simpa only [hdust] using hbad) hinf EStar hE hEU hEStar hEStarE hinfE
    (σ s) hpB D hnest hshrink hanchor (quotientNormalizedMap base.domainEquiv A.function)
    (quotientNormalizedMap_continuous base.domainEquiv A.function A.conformal.1)
    T.closedGate T.openGate T.closed_closedGate T.open_openGate T.closedGate_subset_openGate
    hfiber harcs previous hlevels hweightsFinite hpoint Flags hFlags
    (by simpa only [hdust] using hFlagsB) hmarked hunique' C₀ hC₀ hderiv
    hstandard hpath ω hω hωsum hdual hlift (ENNReal.ofReal T.selectionThreshold)
    (ENNReal.ofReal_pos.mpr T.selectionThreshold_pos) hno (fun _ => 0)
    (fun _ => inferInstance) (fun _ => by
      change (support (fun _ : Sphere => (0 : ℝ≥0∞))).Countable
      apply countable_empty.mono
      intro x hx
      exact (hx rfl).elim)
  let D' (n : ℕ) := (D n).retarget htarget
  have hregion (n : ℕ) : (D' n).region = (D n).region :=
    (D n).region_retarget htarget
  apply L.exists_selectable_protrusion_mean rank hrank hcoarea hsard hsch hsep
    base hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB
    C presentation hlevel hweights hmarked hsingular hP hunique ω
    hLusin hfiber harcs previous hprevious hweighted hcollar hselect Candidates label hflags hgraphs
    E T hq s hqs htarget (by simpa only [htarget] using hp) hseparated D'
    (by simpa only [hregion] using hnest)
    (by simpa only [hregion, htarget] using hshrink)
    (by simpa only [hregion] using hanchor)
    (by simpa only [hregion] using hfinite)
    (fun n => (congrFun hcontours n).trans (by rw [hregion]))
    (fun n => congrFun hgates n) B R hB hR hfar

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionTestAvailability
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local real/mean alternative gives an actual compatible open test
at every protruding marked component. All exclusion data are constructed. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_32
theorem exists_protrusion_exclusion_test
    {I : Type*} [LinearOrder I] (rank : ℕ → I) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ base.quotientDomainᶜ)
    (C : ℕ → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val))
    (presentation : ∀ i, SelectedLevelPresentation hsch base π (C i))
    (hlevel : ∀ i, base.levels i = Prod.swap ⁻¹' (C i).graph)
    (hweights : ∀ i, base.levelWeights i = (C i).dustWeight)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ Flags)
    (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
    (hP : RankedLevelNullCompatibility rank base.levels (base.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ D : Set Sphere, IsCompact D → LocallyConnectedSpace D →
      HasSimpleArcsInConnectedOpens D)
    (previous : PriorLevelFamily base.physicalDomain π)
    (hprevious : ∀ i, previous.graph i = (C i).graph)
    (hweighted : WeightedPlanarScalarCoarea) (hcollar : SmoothRegularJordanCollars)
    (hselect : BorelPathRelationSelection)
    (Candidates : Set (SelectableMaskedCoordinate base π))
    (label : SelectableMaskedCoordinate base π → ℕ)
    (hflags : ∀ c ∈ Candidates, c.flags ⊆ Flags)
    (hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c))
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
    (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
    (s : S) (hqs : π q = σ s) (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hseparated : Disjoint (Metric.closedBall T.center (2 * T.radius))
      (Metric.closedBall (A.center s) (A.radius s)))
    {g : ℂ → ℝ≥0∞}
    (D : ℕ → WeightedCollar base.physicalDomain π base.dust (σ s) g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 (σ s), ∃ k : ℕ, ∀ n ≥ k, closure (D n).region ⊆ V)
    (hanchor : Disjoint base.anchor (closure (D 0).region))
    (hfinite : OnePoint.infty ∉ closure (D 0).region)
    (EStar : Set Sphere) (hE : IsClosed base.anchor) (hEU : base.anchor ⊆ base.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior base.anchor)
    (hinfE : π OnePoint.infty ∈ interior base.anchor)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ base.levels i} ≤ base.levelWeights i x)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C₀ / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (B R : ℝ) (hB : B / 4 < M.radius) (hR : 5 * M.radius < R)
    (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ base.anchor)
    (harea : ExteriorCoefficientAreaTheorem)
    (hzero : ∀ z ∈ closure (jordanInterior T.sourceAnchor), π (z : Sphere) ∈ EStar)
    (hconn : IsConnected base.physicalDomain)
    (hinfEStar : π OnePoint.infty ∈ interior EStar)
    (B₀ : Set base.dust) (p : B₀) (hp : p.val.val = σ s) :
    ∃ T' : CoordinateExclusionTest hsch base π B₀ (B / 4),
      T'.mark = p ∧ T'.coordinate.CompatibleWith Candidates ∧
      (p, (finiteSourceMap A.function (A.plane_open_embedding hG).1,
        A.center s, (⟨A.radius s, (A.bounds s).2.1⟩ : ℝ≥0)), M.radius) ∈ T'.neighborhood := by
  classical
  have hπG : ∀ z : ℂ, (z : Sphere) ∈ base.physicalDomain →
      π (z : Sphere) ∈ base.quotientDomain := by
    intro z hz
    rw [← he ⟨_, hz⟩]
    exact (base.domainEquiv ⟨_, hz⟩).property
  have hpre : π ⁻¹' base.quotientDomain ⊆ base.physicalDomain := by
    intro z hz
    by_contra hn
    exact hbad z hn hz
  have hBImage : base.dust = π '' base.physicalDomainᶜ := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨z, rfl⟩ := hsurj x
      refine ⟨z, ?_, rfl⟩
      intro hz
      have hπz : π z ∈ base.quotientDomain := by
        rw [← he ⟨_, hz⟩]
        exact (base.domainEquiv ⟨_, hz⟩).property
      exact (show π z ∈ base.quotientDomainᶜ from hdust ▸ hx) hπz
    · rintro _ ⟨z, hz, rfl⟩
      exact hdust.symm ▸ hbad z hz
  obtain hreal | hmean := exists_protrusion_barrier_or_selectable_mean rank hrank
    hcoarea hsard hsch hsep base hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad
    Flags hFlags hFlagsB C presentation hlevel hweights hmarked hsingular hP hunique
    ω hω hωsum hLusin hfiber harcs previous hprevious hweighted hcollar hselect
    Candidates label hflags hgraphs E T hq s hqs hinf hseparated D hnest hshrink
    hanchor hfinite EStar hE hEU hEStar hEStarE hinfE hpoint C₀ hC₀ hderiv
    hstandard hpath hdual hlift B R hB hR hfar
  · obtain ⟨P, hsmall⟩ := hreal
    obtain ⟨c, hcomp, W, _, hmem, hmemSized⟩ := P.exists_selectable_exclusion
      hweighted hsch harea hG hconn hU hdense hπ hr he hBImage hπG hpre
      (interior_subset hinfE) p.val T hq
      (fun n => (D n).isOpen_region hπ hclosed hsurj hr)
      (fun n => by rw [hqs]; exact (D n).point_mem_region hsurj (by
        intro hi
        have hx : σ s ∈ base.dust := hp ▸ p.val.property
        have hπi : π OnePoint.infty ∈ base.quotientDomain := hEU (interior_subset hinfE)
        exact (show σ s ∈ base.quotientDomainᶜ from hdust ▸ hx) (hi ▸ hπi)))
      hzero (fun z hz => quotientNormalizedMap_physical base.domainEquiv π he A.function z hz)
      (Subset.refl _) (ENNReal.toReal_lt_of_lt_ofReal hsmall) hinfEStar
      Candidates label hflags hgraphs
    exact ⟨⟨p, c, Sum.inl W⟩, rfl, hcomp, rfl, hmemSized _ _⟩
  · obtain ⟨c, hcomp, ⟨P⟩, hsing, W, hbound, hmem⟩ := hmean
    let W' : MeanExclusionTest hsch base π c.coordinate p.val (B / 4) := {
      presentation := P
      function := A.function
      continuousOn := (A.plane_open_embedding hG).1
      center := A.center s
      radius := ⟨A.radius s, (A.bounds s).2.1⟩
      budgetRadius := R
      witness := W
      singular := Subtype.ext (hsing.trans hp.symm)
      source_bound := fun z hz => by have h := hbound z hz; linarith }
    exact ⟨⟨p, c, Sum.inr W'⟩, rfl, hcomp, rfl, hmem⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RankedSelectedLevels
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enumerating the selected labels does not change their inherited order.
This supplies exactly the ranked compatibility used by the tag-law proofs. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem ranked_compatibility_of_ordered_family
    {L : Type*} [LinearOrder L] (rank : ℕ → L)
    (D : L → Set (Sphere × UnitAddCircle)) (F : Set Sphere)
    (H : ℕ → Set (UnitAddCircle × Sphere))
    (hH : ∀ i, H i = Prod.swap ⁻¹' D (rank i))
    (hcompat : ∀ (j : L) (n : ℕ) (labels : Fin n → L), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure F (D j) D labels) = 0) :
    RankedLevelNullCompatibility rank H F := by
  have hrel : levelRelation H = fun i => D (rank i) := by
    funext i
    ext p
    rw [levelRelation, hH i]
    rfl
  intro j n labels hlt
  rw [hrel]
  have h := hcompat (rank j) n (rank ∘ labels) hlt
  rw [UngatedRealTest.freeComponentFailure_congr_selected F (D (rank j)) D
    (fun i => D (rank i)) (rank ∘ labels) labels (fun _ => rfl)] at h
  simpa only [MeasureTheory.volume_pi] using h

 theorem selected_pathData_ranked_compatibility
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {L : Type*} [LinearOrder L] (rank : ℕ → L)
    (D : L → SelectableMaskedCoordinate d π)
    (hcompat : ∀ (j : L) (n : ℕ) (labels : Fin n → L), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
          (fun k => (D k).coordinate.graph) labels) = 0) :
    RankedLevelNullCompatibility rank
      (SelectableMaskedCoordinate.pathData (D ∘ rank)).levels (d.dust \ ⋃ k, (D k).flags) :=
  ranked_compatibility_of_ordered_family rank (fun k => (D k).coordinate.graph) _ _
    (fun _ => rfl) hcompat

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ReanchoredSelection
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local endpoint anchor does not change a selected coordinate, its
presentation, flags, or compatibility. This permits the protrusion anchor
to be chosen after the preceding countable coordinate family. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace SelectableMaskedCoordinate
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}

 local instance localInst_r6edb4b_7 : BorelSpace Sphere := ⟨rfl⟩
theorem reanchor_reverse (c : SelectableMaskedCoordinate d π) (E : Set Sphere) :
    (c.reanchor E).reanchor d.anchor = c := by
  cases c
  rfl

 theorem CompatibleWith.reanchor {c : SelectableMaskedCoordinate d π}
    {A : Set (SelectableMaskedCoordinate d π)} (hc : c.CompatibleWith A) (E : Set Sphere) :
    (c.reanchor E).CompatibleWith ((fun a => a.reanchor E) '' A) := by
  constructor
  · rintro a ⟨b, hb, rfl⟩
    exact hc.1 b hb
  · intro n q hq
    choose a ha heq using hq
    have hgraphs : (fun i => (q i).coordinate.graph) =
        (fun i => (a i).coordinate.graph) := by
      funext i
      rw [← heq i]
      rfl
    change (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (d.dust \ c.flags) c.coordinate.graph
        (fun i => (q i).coordinate.graph) id) = 0
    rw [hgraphs]
    exact hc.2 n a ha

end SelectableMaskedCoordinate
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ReanchoredExclusions
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local endpoint anchor changes neither an exclusion neighborhood nor
its retained coordinate. Transport back to the original selection base. -/
open Set Function MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
    (fun x : base.dust => x.val)}

namespace CoordinateExclusionTest
variable {hsch : PlanarSchoenflies} {B₀ : Set base.dust} {B : ℝ}

 theorem neighborhood_reanchor (T : CoordinateExclusionTest hsch base π B₀ B) (E : Set Sphere) :
    (T.reanchor E).neighborhood = T.neighborhood := by
  rcases T with ⟨p, c, W⟩
  cases W <;> rfl

 theorem reanchor_compatible {E : Set Sphere}
    (T : CoordinateExclusionTest hsch {base with anchor := E} π B₀ B)
    {A : Set (SelectableMaskedCoordinate base π)}
    (hT : T.coordinate.CompatibleWith ((fun c => c.reanchor E) '' A)) :
    (T.reanchor base.anchor).coordinate.CompatibleWith A := by
  apply (hT.reanchor base.anchor).mono
  intro c hc
  exact ⟨c.reanchor E, ⟨c, hc, rfl⟩, c.reanchor_reverse E⟩

end CoordinateExclusionTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RelevelledSelection
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Installing the preceding selected level graphs in a path code leaves
coordinates, flags, physical weights, and compatibility unchanged. -/
open Set Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
namespace SelectableMaskedCoordinate
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}

 local instance localInst_r6edb4b_8 : BorelSpace Sphere := ⟨rfl⟩
theorem withLevels_reverse (c : SelectableMaskedCoordinate d π) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    (c.withLevels H w).withLevels d.levels d.levelWeights = c := by
  cases c
  rfl

 theorem CompatibleWith.withLevels {c : SelectableMaskedCoordinate d π}
    {A : Set (SelectableMaskedCoordinate d π)} (hc : c.CompatibleWith A) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    (c.withLevels H w).CompatibleWith ((fun a => a.withLevels H w) '' A) := by
  constructor
  · rintro a ⟨b, hb, rfl⟩
    exact hc.1 b hb
  · intro n q hq
    choose a ha heq using hq
    have hgraphs : (fun i => (q i).coordinate.graph) =
        (fun i => (a i).coordinate.graph) := by
      funext i
      rw [← heq i]
      rfl
    change (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (d.dust \ c.flags) c.coordinate.graph
        (fun i => (q i).coordinate.graph) id) = 0
    rw [hgraphs]
    exact hc.2 n a ha

end SelectableMaskedCoordinate
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RelevelledExclusions
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing the path code's level metadata changes neither a test's
physical coordinate nor its open exclusion. -/
open Set Function MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
    (fun x : base.dust => x.val)}

namespace CoordinateExclusionTest
variable {hsch : PlanarSchoenflies} {B₀ : Set base.dust} {B : ℝ}

 theorem neighborhood_withLevels (T : CoordinateExclusionTest hsch base π B₀ B) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    (T.withLevels H w).neighborhood = T.neighborhood := by
  rcases T with ⟨p, c, W⟩
  cases W <;> rfl

 theorem withLevels_compatible {H : ℕ → Set (UnitAddCircle × Sphere)} {w : ℕ → Sphere → ℝ≥0∞}
    (T : CoordinateExclusionTest hsch {base with levels := H, levelWeights := w} π B₀ B)
    {A : Set (SelectableMaskedCoordinate base π)}
    (hT : T.coordinate.CompatibleWith ((fun c => c.withLevels H w) '' A)) :
    (T.withLevels base.levels base.levelWeights).coordinate.CompatibleWith A := by
  apply (hT.withLevels base.levels base.levelWeights).mono
  intro c hc
  exact ⟨c.withLevels H w, ⟨c, hc, rfl⟩, c.withLevels_reverse H w⟩

end CoordinateExclusionTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_OrderedProtrusionAvailability
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local construction is available against the whole preceding
ordered family. Its auxiliary anchor and level code are removed from the
returned test, preserving the original physical data and open exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_33
theorem exists_ordered_protrusion_test_oai
    (hcoarea : PlanarLipschitzFiberCoarea) (hweighted : WeightedPlanarScalarCoarea)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (harea : ExteriorCoefficientAreaTheorem)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hU : IsOpen base.quotientDomain) (hdense : Dense base.quotientDomain)
    (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (hinf : OnePoint.infty ∈ base.physicalDomain)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ K : Set Sphere, IsCompact K → LocallyConnectedSpace K →
      HasSimpleArcsInConnectedOpens K)
    {I : Type*} [LinearOrder I] [Countable I] (rank : ℕ ≃ I)
    (D : I → SelectableMaskedCoordinate base π)
    (pres : ∀ i, SelectedLevelPresentation hsch base π (D i).coordinate)
    (hcompat : ∀ (j : I) (n : ℕ) (labels : Fin n → I), (∀ i, labels i < j) →
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (base.dust \ ⋃ k, (D k).flags) (D j).coordinate.graph
          (fun k => (D k).coordinate.graph) labels) = 0)
    (E₀ : Set Sphere) (hE₀ : IsCompact E₀) (hE₀U : E₀ ⊆ base.quotientDomain)
    (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ E₀)
    (B₀ : Set base.dust) (p : B₀) (hpfinite : p.val.val ≠ OnePoint.infty)
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
    (hq : q ∈ base.physicalDomainᶜ) (s : S) (hqs : π q = σ s) (hp : p.val.val = σ s)
    (hne : E.plane ≠ Metric.closedBall (A.center s) (A.radius s))
    (hB : B / 4 < M.radius)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C₀ / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (J : Set ℕ) [PolishSpace J] (b : J → Sphere) (c : J → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere J))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (J : Set ℕ) [PolishSpace J] (b : J → Sphere) (c : J → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere J)) :
    ∃ T : CoordinateExclusionTest hsch base π B₀ (B / 4),
      T.mark = p ∧ T.coordinate.CompatibleWith (range D) ∧
      (p, (finiteSourceMap A.function (A.plane_open_embedding hG).1,
        A.center s, (⟨A.radius s, (A.bounds s).2.1⟩ : ℝ≥0)), M.radius) ∈ T.neighborhood := by
  classical
  obtain ⟨T, hseparated⟩ := E.exists_local_test_geometry hG hr hq hqs hne
  obtain ⟨EStar, Anchor, hEstar, hAnchor, hEA, hAU, hE₀E, hinftyE, hzero⟩ :=
    T.exists_endpoint_anchors_retaining hU hπ base.domainEquiv he E₀ hE₀ hE₀U
  let code : PathCodeData Sphere Sphere :=
    { SelectableMaskedCoordinate.pathData (D ∘ rank) with anchor := Anchor }
  let H := code.levels
  let w := code.levelWeights
  let C (n : ℕ) := (D (rank n)).coordinate
  let previous : PriorLevelFamily code.physicalDomain π :=
    SelectableMaskedCoordinate.priorLevels (d := base) (D ∘ rank)
  let Flags : Set Sphere := ⋃ i, (D i).flags
  have hFlags : Flags.Countable := countable_iUnion (fun i => (D i).flags_countable)
  have hFlagsB : Flags ⊆ base.quotientDomainᶜ := by
    rintro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hdust ▸ (D i).flags_dust hi
  have hinfty : π OnePoint.infty ∉ base.dust := by
    rw [hdust, ← he ⟨_, hinf⟩]
    exact not_not.mpr (base.domainEquiv ⟨_, hinf⟩).property
  obtain ⟨collars, hnest, hshrink, hanchor, hfinite⟩ :=
    exists_anchored_shrinking_weighted_collars hweighted hsard hsch
      base.physicalDomain base.quotientDomain base.dust Anchor π hπ hclosed hsurj hr
      (by rw [hdust]; exact hU.isClosed_compl) (by simpa only [hdust] using hTD)
      (by rw [hdust]; exact disjoint_compl_right) (by simpa only [hdust] using hbad)
      hAnchor hAU hinfty (hp ▸ p.val.property) (hp ▸ hpfinite)
  let Candidates : Set (SelectableMaskedCoordinate code π) :=
    (fun c => c.withLevels H w) '' ((fun c => c.reanchor Anchor) '' range D)
  have hindex : ∀ c ∈ Candidates, ∃ n, c.coordinate.graph = previous.graph n := by
    rintro c ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
    refine ⟨rank.symm i, ?_⟩
    change (D i).coordinate.graph = (D (rank (rank.symm i))).coordinate.graph
    rw [rank.apply_symm_apply]
  let label (c : SelectableMaskedCoordinate code π) : ℕ :=
    if hc : c ∈ Candidates then Classical.choose (hindex c hc) else 0
  have hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c) := by
    intro c hc
    dsimp only [label]
    rw [dite_eq_left hc]
    exact Classical.choose_spec (hindex c hc)
  have hflags : ∀ c ∈ Candidates, c.flags ⊆ Flags := by
    rintro c ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩ x hx
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hmarked : ∀ n, support (code.levelWeights n) ⊆ Flags := by
    intro n x hx
    exact mem_iUnion.mpr ⟨rank n, (D (rank n)).weight_support hx⟩
  have hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ i a b,
      (a, x) ∈ code.levels i → (b, x) ∈ code.levels i → a = b := by
    intro x hx i a b ha hb
    apply (C i).unique_of_dustWeight_eq_zero (hdust.symm ▸ hx.1) _ ha hb
    by_contra hw
    exact hx.2 (hmarked i hw)
  have hP : RankedLevelNullCompatibility rank code.levels (base.quotientDomainᶜ \ Flags) := by
    simpa only [code, Flags, hdust] using selected_pathData_ranked_compatibility rank D hcompat
  obtain ⟨X, hXp, hXcomp, hXmem⟩ := exists_protrusion_exclusion_test rank rank.injective
    hcoarea hsard hsch hsep code hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad
    Flags hFlags hFlagsB C (fun n => (pres (rank n)).rebase (e := code) rfl rfl rfl)
    (fun _ => rfl) (fun _ => rfl) hmarked
    (fun n => mem_iUnion.mpr ⟨rank n, (D (rank n)).singular_marked⟩) hP hunique
    ω hω hωsum hLusin hfiber harcs previous (fun _ => rfl) hweighted hcollar hselect
    Candidates label hflags hgraphs E T hq s hqs hinf hseparated collars hnest hshrink
    hanchor hfinite EStar hAnchor hAU hEstar hEA
    (hEA (interior_subset hinftyE))
    (SelectableMaskedCoordinate.point_bound (D ∘ rank) (by rw [hdust, compl_compl]))
    C₀ hC₀ hderiv hstandard hpath hdual hlift B (10 * M.radius) hB
    (by linarith [M.radius_pos])
    (fun z hz => interior_subset (hEA (interior_subset (hE₀E (hfar z hz)))))
    harea hzero hconn hinftyE B₀ p hp
  let Y := X.withLevels base.levels base.levelWeights
  have hYcomp : Y.coordinate.CompatibleWith ((fun c => c.reanchor Anchor) '' range D) :=
    X.withLevels_compatible (base := {base with anchor := Anchor}) hXcomp
  let Z : CoordinateExclusionTest hsch base π B₀ (B / 4) := Y.reanchor base.anchor
  refine ⟨Z, hXp, Y.reanchor_compatible (base := base) hYcomp, ?_⟩
  have hZY : Z.neighborhood = Y.neighborhood := Y.neighborhood_reanchor base.anchor
  have hYX : Y.neighborhood = X.neighborhood :=
    X.neighborhood_withLevels base.levels base.levelWeights
  exact hZY.symm ▸ (hYX.symm ▸ hXmem)

end CircleDomainRigidity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CircleDomainRigidity.exists_ordered_protrusion_test_oai.{u_1, u_2} := @OAI.CircleDomainRigidity.exists_ordered_protrusion_test_oai.{u_1, u_2}
