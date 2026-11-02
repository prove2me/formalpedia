-- Prove2me | solution 1 for OAI.CircleDomainRigidity.countable_uncovered_test_endpoints_of_range
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:04:41.143955+00:00
-- url     : https://prove2.me/submissions/ee2a435e-9cdd-4cf2-a7c9-e93b145425f7

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010
import Theorems.Thm_OAI_CircleDomainRigidity_barrier_modulus_lower_bound

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
-- module Solutions.Q146_CD.CircleDomains_Selection_VisitCardinality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable finite-witness count agrees with the actual extended sum
of unit tolls over all visit times. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem visitCount_eq_tsum (γ : C(PathTime, X)) (x : X) :
    visitCount γ x = ∑' t : PathTime, if γ t = x then (1 : ℝ≥0∞) else 0 := by
  classical
  apply le_antisymm
  · unfold visitCount
    apply iSup_le
    intro n
    split
    · rename_i hn
      obtain ⟨t, ht, heq⟩ := hn
      calc
        (n : ℝ≥0∞) = ∑' i : Fin n, if γ (t i) = x then (1 : ℝ≥0∞) else 0 := by
          simp only [heq, ite_true, if_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
        _ ≤ ∑' t : PathTime, if γ t = x then (1 : ℝ≥0∞) else 0 :=
          ENNReal.tsum_comp_le_tsum_of_injective ht (fun t => if γ t = x then 1 else 0)
    · exact bot_le
  · rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    let E := F.filter (fun t => γ t = x)
    let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
    have ht : (γ, x) ∈ visitAtLeastSet (Fintype.card E) := by
      refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
      intro i
      exact (Finset.mem_filter.mp (e i).property).2
    have hb := visitCount_ge_nat ht
    simpa only [Finset.sum_boole, Fintype.card_coe] using hb

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
-- module Solutions.Q146_CD.CircleDomains_Topology_PathTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary tolls count every parameter visit. Counting-square-summable
weights have countable support, so their true tolls are Borel. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem boundaryToll_eq_visits (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryToll γ m = ∑' x, m x * visitCount γ x := by
  rw [boundaryToll, ← ENNReal.tsum_fiberwise (fun t => m (γ t)) γ]
  apply tsum_congr
  intro x
  rw [visitCount_eq_tsum, ← ENNReal.tsum_mul_left,
    tsum_subtype (γ ⁻¹' {x}) (fun t : PathTime => m (γ t))]
  apply tsum_congr
  intro t
  by_cases h : γ t = x
  · simp [h, Set.indicator]
  · simp [h, Set.indicator]

theorem boundaryToll_eq_support (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryToll γ m = ∑' x : Function.support m, m x * visitCount γ x := by
  rw [boundaryToll_eq_visits]
  symm
  apply tsum_subtype_eq_of_support_subset (f := fun x : X => m x * visitCount γ x)
  intro x hx
  contrapose! hx
  simp only [Function.mem_support] at hx ⊢
  simp [hx]

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_boundaryToll {m : X → ℝ≥0∞} (hm : (Function.support m).Countable) :
    Measurable (fun γ : C(PathTime, X) => boundaryToll γ m) := by
  let : Countable (Function.support m) := hm.to_subtype
  simp_rw [boundaryToll_eq_support]
  exact Measurable.tsum fun x => measurable_const.mul
    (measurable_visitCount.comp (measurable_id.prodMk measurable_const))

theorem lintegral_boundaryToll (μ : ProbabilityMeasure C(PathTime, X))
    {m : X → ℝ≥0∞} (hm : (Function.support m).Countable) :
    ∫⁻ γ, boundaryToll γ m ∂(μ : Measure _) =
      ∑' x : Function.support m, m x * meanVisitCount μ x := by
  let : Countable (Function.support m) := hm.to_subtype
  simp_rw [boundaryToll_eq_support]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro x
    exact lintegral_const_mul _
      (measurable_visitCount.comp (measurable_id.prodMk measurable_const))
  · intro x
    exact (measurable_const.mul
      (measurable_visitCount.comp (measurable_id.prodMk measurable_const))).aemeasurable

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

theorem weightedTupleMeasure_slot_le (θ : ℕ → TagSlot) (k : ℕ) :
    slotWeight k • slotTupleMeasure (θ k) ≤ weightedTupleMeasure θ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [weightedTupleMeasure_apply θ hs, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.le_tsum (f := fun j => slotWeight j * slotTupleMeasure (θ j) s) k

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

theorem lintegral_pathOccupation (γ : RectifiablePath X) {g : X → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, g x ∂pathOccupation γ = ∫⁻ t, g (γ.val t) ∂pathLengthMeasure γ :=
  lintegral_map hg γ.val.continuous.measurable

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
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
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

theorem physicalSubpath_projects {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    (π : Y → X) (hπ : ∀ y : G, π y = (e y).val)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b) (t : PathTime) :
    π (physicalSubpath e hab γ t) = γ.val (timeClip a b t) := by
  change π (e.symm ⟨γ.val (timeClip a b t), _⟩).val = _
  rw [hπ]
  simp

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

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem physicalStageOccupation_univ (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hγ : physicalDomainLength e y₀ γ < ∞) (n : ℕ) :
    physicalStageOccupation e y₀ n γ univ = physicalStageLength e y₀ n γ := by
  simp only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply,
    rectifiableOccupationCode_univ (physicalDyadicPath_rectifiable e y₀ hγ n _)]
  rfl

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
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
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

theorem dyadicPhysicalOccupation_apply (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    {s : Set Y} (hs : MeasurableSet s) :
    dyadicPhysicalOccupation e y₀ γ s = ⨆ n, physicalStageOccupation e y₀ n γ.val s :=
  increasingMeasureLimit_apply _ _ hs

theorem dyadicPhysicalOccupation_univ (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    dyadicPhysicalOccupation e y₀ γ univ = physicalDomainLength e y₀ γ.val := by
  rw [dyadicPhysicalOccupation_apply _ _ _ MeasurableSet.univ]
  simp only [physicalStageOccupation_univ e y₀ γ.property]
  rfl

instance instIsFiniteMeasureDyadicPhysicalOccupation (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    IsFiniteMeasure (dyadicPhysicalOccupation e y₀ γ) :=
  ⟨by rw [dyadicPhysicalOccupation_univ]; exact γ.property⟩

theorem physicalStageOccupation_compl (e : G ≃ₜ U) (hG : IsOpen G) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    physicalStageOccupation e y₀ n γ.val Gᶜ = 0 := by
  classical
  simp only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · have hrect := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi] at hrect ⊢
    rw [rectifiableOccupationCode_eq hrect, pathOccupation,
      Measure.map_apply (physicalSubpath e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩).continuous.measurable
        hG.measurableSet.compl]
    have heq : (physicalSubpath e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩) ⁻¹' Gᶜ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact ht (physicalSubpath_mem e _ _ t)
    rw [heq, measure_empty]
  · simp [physicalDyadicPath, totalPhysicalSubpath, hi, rectifiableOccupationCode_const]

theorem dyadicPhysicalOccupation_compl (e : G ≃ₜ U) (hG : IsOpen G) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) : dyadicPhysicalOccupation e y₀ γ Gᶜ = 0 := by
  rw [dyadicPhysicalOccupation_apply _ _ _ hG.measurableSet.compl]
  simp [physicalStageOccupation_compl e hG y₀ γ]

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
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalOccupationPushforward
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical occupation is the pushforward of domain-time arclength, with
parameter multiplicity retained. The value assigned at dust times is irrelevant. -/

open Set MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalValue_subpath (e : G ≃ₜ U) (y₀ : Y)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b)
    {t : PathTime} (ht : t ∈ Icc a b) :
    physicalValue e y₀ (γ.val t) = physicalSubpath e hab γ t := by
  simp only [physicalValue, dite_eq_left (γ.property ht), physicalSubpath,
    ContinuousMap.coe_mk, timeClip, min_eq_right ht.2, max_eq_right ht.1]

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

theorem measurable_physicalValue (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (physicalValue e y₀) :=
  (continuous_subtype_val.comp e.symm.continuous).measurable.dite
    measurable_const hU.measurableSet

omit [MeasurableSpace X] [BorelSpace X] in
theorem physicalDyadicLength_map (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) (i : Fin (2 ^ n)) :
    (rectifiableLengthCode (physicalDyadicPath e y₀ n i γ.val)).map
        (physicalValue e y₀ ∘ γ.val) =
      rectifiableOccupationCode (physicalDyadicPath e y₀ n i γ.val) := by
  by_cases hi : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · have hr := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi] at hr ⊢
    rw [rectifiableLengthCode_eq hr, rectifiableOccupationCode_eq hr, pathOccupation]
    apply Measure.map_congr
    have hae : ∀ᵐ t ∂pathLengthMeasure
        ⟨physicalSubpath e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩, hr⟩,
        t ∈ Icc (dyadicLeft n i) (dyadicRight n i) := by
      have heq := physicalSubpath_timeLength_portion e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩ hr
      rw [rectifiableLengthCode_eq hr] at heq
      rw [heq]
      exact ae_restrict_mem measurableSet_Icc
    filter_upwards [hae] with t ht
    exact physicalValue_subpath e y₀ (dyadicLeft_le_right n i) ⟨γ.val, hi⟩ ht
  · simp [physicalDyadicPath, totalPhysicalSubpath, hi,
      rectifiableLengthCode_const, rectifiableOccupationCode_const]

theorem physicalStageTimeLength_map (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    (physicalStageTimeLength e y₀ n γ.val).map (physicalValue e y₀ ∘ γ.val) =
      physicalStageOccupation e y₀ n γ.val := by
  have hm := (measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable
  ext s hs
  rw [Measure.map_apply hm hs]
  simp only [physicalStageTimeLength, physicalStageOccupation, Measure.coe_finsetSum,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← physicalDyadicLength_map e y₀ γ n i, Measure.map_apply hm hs]

theorem physicalTimeLength_map (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) :
    (physicalTimeLength e y₀ γ).map (physicalValue e y₀ ∘ γ.val) =
      dyadicPhysicalOccupation e y₀ γ := by
  have hm := (measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable
  ext s hs
  rw [Measure.map_apply hm hs, physicalTimeLength_apply _ _ _ (hm hs),
    dyadicPhysicalOccupation_apply _ _ _ hs]
  congr 1
  funext n
  rw [← physicalStageTimeLength_map e hU y₀ γ n, Measure.map_apply hm hs]

theorem physicalOccupation_integral (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ γ =
      ∫⁻ t, g (physicalValue e y₀ (γ.val t)) ∂physicalTimeLength e y₀ γ := by
  rw [← physicalTimeLength_map e hU y₀ γ]
  exact lintegral_map hg ((measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable)

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
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
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

theorem preterminalVisitCount_eq_tsum (γ : C(PathTime, X)) (x : X) :
    preterminalVisitCount γ x =
      ∑' t : PathTime, if t ≠ ⊤ ∧ γ t = x then (1 : ℝ≥0∞) else 0 := by
  rw [preterminalVisitCount, visitCount_eq_tsum, ENNReal.tsum_eq_add_tsum_ite ⊤]
  have hfinite : terminalVisitCount γ x ≠ ∞ := by
    unfold terminalVisitCount
    split <;> simp
  change terminalVisitCount γ x + _ - terminalVisitCount γ x = _
  rw [ENNReal.add_sub_cancel_left hfinite]
  apply tsum_congr
  intro t
  by_cases ht : t = ⊤ <;> simp [ht]

theorem visitCount_eq_preterminal_add_terminal (γ : C(PathTime, X)) (x : X) :
    visitCount γ x = preterminalVisitCount γ x + terminalVisitCount γ x := by
  rw [visitCount_eq_tsum, ENNReal.tsum_eq_add_tsum_ite ⊤,
    preterminalVisitCount_eq_tsum, add_comm]
  congr 1
  apply tsum_congr
  intro t
  by_cases ht : t = ⊤ <;> simp [ht]

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

instance instIsFiniteMeasureBaseCodeOccupation (d : PathCodeData X Y) (Γ : BasePathCode d) : IsFiniteMeasure (baseCodeOccupation d Γ) := by
  unfold baseCodeOccupation
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

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
-- module Solutions.Q146_CD.CircleDomains_Modulus_TupleIncidence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence of a tuple with a fixed dust point. A free point whose
individual level sections are null has a null incident-tuple set. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

theorem isClosed_tupleIncident {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i)) (x : X) : IsClosed (tupleIncident H x) := by
  change IsClosed {q : Σ n : ℕ, (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle) |
    ∃ j : Fin (q.1 + 1), (q.2.2 j, x) ∈ H (q.2.1 j)}
  apply isClosed_sigma_iff.mpr
  intro n
  change IsClosed {q : (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle) |
    ∃ j, (q.2 j, x) ∈ H (q.1 j)}
  simp only [ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro j
  exact (isClosed_labeledLevelGraph hH).preimage
    (show Continuous (fun q : (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle) =>
      (q.1 j, (q.2 j, x))) from
      ((continuous_apply j).comp continuous_fst).prodMk
        (((continuous_apply j).comp continuous_snd).prodMk continuous_const))

omit [TopologicalSpace X] in
theorem tupleIncident_fiber_null (H : ℕ → Set (UnitAddCircle × X)) (x : X)
    (hx : ∀ i, volume {t : UnitAddCircle | (t, x) ∈ H i} = 0) (i : TupleType) :
    volume (tupleFiber i ⁻¹' tupleIncident H x) = 0 := by
  have heq : tupleFiber i ⁻¹' tupleIncident H x =
      ⋃ j : Fin (i.1 + 1), {t : Fin (i.1 + 1) → UnitAddCircle | (t j, x) ∈ H (i.2 j)} := by
    ext t
    simp only [mem_iUnion]
    rfl
  rw [heq]
  apply measure_iUnion_null
  intro j
  exact Measure.pi_eval_preimage_null (fun _ : Fin (i.1 + 1) =>
    (volume : Measure UnitAddCircle)) (hx (i.2 j))

theorem tupleReference_incident_null {H : ℕ → Set (UnitAddCircle × X)}
    (hH : ∀ i, IsClosed (H i)) (ω : TupleType → ℝ≥0∞) (x : X)
    (hx : ∀ i, volume {t : UnitAddCircle | (t, x) ∈ H i} = 0) :
    tupleReference ω (tupleIncident H x) = 0 := by
  rw [tupleReference_apply ω (isClosed_tupleIncident hH x).measurableSet,
    ENNReal.tsum_eq_zero]
  intro i
  rw [tupleIncident_fiber_null H x hx i, mul_zero]

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

omit [TopologicalSpace D] [MeasurableSpace Y] [BorelSpace Y] [BorelSpace D]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_baseCodeAtomic (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞) :
    Measurable (fun Γ : BasePathCode d => atomicVisitMeasure p c Γ.val.1) :=
  (measurable_atomicVisitMeasure p c).comp (measurable_fst.comp measurable_subtype_coe)

omit [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)] [SecondCountableTopology X] in
theorem measurable_baseCodeTuple (d : PathCodeData X Y) :
    Measurable (fun Γ : BasePathCode d => weightedTupleMeasure Γ.val.2) :=
  measurable_weightedTupleMeasure.comp (measurable_snd.comp measurable_subtype_coe)

omit [BorelSpace X] [SecondCountableTopology X] in
theorem meanCodeOccupation_apply (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) {A : Set Y} (hA : MeasurableSet A) :
    meanCodeOccupation d P A = ∫⁻ Γ, baseCodeOccupation d Γ A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_baseCodeOccupation d hU).aemeasurable

omit [TopologicalSpace D] [MeasurableSpace Y] [BorelSpace Y] [BorelSpace D]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem meanCodeAtomic_apply (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) {A : Set D} (hA : MeasurableSet A) :
    meanCodeAtomic d p c P A = ∫⁻ Γ, atomicVisitMeasure p c Γ.val.1 A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_baseCodeAtomic d p c).aemeasurable

omit [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)] [SecondCountableTopology X] in
theorem meanCodeTuple_apply (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    {A : Set LevelTuple} (hA : MeasurableSet A) :
    meanCodeTuple d P A = ∫⁻ Γ, weightedTupleMeasure Γ.val.2 A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_baseCodeTuple d).aemeasurable

theorem meanCodeCost_apply (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (P : ProbabilityMeasure (BasePathCode d))
    {A : Set (PathCostSpace Y D)} (hA : MeasurableSet A) :
    meanCodeCost d p c P A = ∫⁻ Γ, pathCostMeasure d p c Γ A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_pathCostMeasure d hU p c).aemeasurable

theorem meanCodeCost_eq (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (P : ProbabilityMeasure (BasePathCode d)) :
    meanCodeCost d p c P =
      (meanCodeOccupation d P).map costPhysical +
      (meanCodeAtomic d p c P).map costAtomic + (meanCodeTuple d P).map costTuple := by
  ext A hA
  rw [meanCodeCost_apply d hU p c P hA, Measure.add_apply, Measure.add_apply,
    Measure.map_apply measurable_costPhysical hA, Measure.map_apply measurable_costAtomic hA,
    Measure.map_apply measurable_costTuple hA,
    meanCodeOccupation_apply d hU P (measurable_costPhysical hA),
    meanCodeAtomic_apply d p c P (measurable_costAtomic hA),
    meanCodeTuple_apply d P (measurable_costTuple hA)]
  simp_rw [pathCostMeasure, Measure.add_apply,
    Measure.map_apply measurable_costPhysical hA, Measure.map_apply measurable_costAtomic hA,
    Measure.map_apply measurable_costTuple hA]
  have hp : Measurable (fun Γ : BasePathCode d =>
      baseCodeOccupation d Γ (costPhysical ⁻¹' A)) :=
    (Measure.measurable_coe (measurable_costPhysical hA)).comp
    (measurable_baseCodeOccupation d hU)
  have ha : Measurable (fun Γ : BasePathCode d =>
      atomicVisitMeasure p c Γ.val.1 (costAtomic ⁻¹' A)) :=
    (Measure.measurable_coe (measurable_costAtomic hA)).comp
    (measurable_baseCodeAtomic d p c)
  have hpa : Measurable (fun Γ : BasePathCode d =>
      baseCodeOccupation d Γ (costPhysical ⁻¹' A) +
        atomicVisitMeasure p c Γ.val.1 (costAtomic ⁻¹' A)) := hp.add ha
  rw [lintegral_add_left hpa, lintegral_add_left hp]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SlotLawMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each fixed slot distribution is dominated by the mean weighted tuple
measure, and hence inherits its absolute continuity. Inactive slots have
zero mass, so these are subprobability measures. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem measurable_baseCodeSlot (d : PathCodeData X Y) (k : ℕ) :
    Measurable (baseCodeSlot d k) :=
  measurable_slotTupleMeasure.comp
    ((measurable_pi_apply k).comp (measurable_snd.comp measurable_subtype_coe))

theorem slotLaw_apply (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (k : ℕ) {A : Set LevelTuple} (hA : MeasurableSet A) :
    slotLaw d P k A = ∫⁻ Γ, slotTupleMeasure (Γ.val.2 k) A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_baseCodeSlot d k).aemeasurable

theorem weighted_slotLaw_le (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (k : ℕ) : slotWeight k • slotLaw d P k ≤ meanCodeTuple d P := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul, slotLaw_apply d P k hA, meanCodeTuple_apply d P hA]
  have hm : Measurable (fun Γ : BasePathCode d => slotTupleMeasure (Γ.val.2 k) A) :=
    (Measure.measurable_coe hA).comp (measurable_baseCodeSlot d k)
  rw [← lintegral_const_mul _ hm]
  apply lintegral_mono
  intro Γ
  have h := (Measure.le_iff.mp (weightedTupleMeasure_slot_le Γ.val.2 k)) A hA
  simpa only [Measure.smul_apply, smul_eq_mul] using h

theorem slotLaw_absolutelyContinuous (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (τ : Measure LevelTuple)
    (hτ : meanCodeTuple d P ≪ τ) (k : ℕ) : slotLaw d P k ≪ τ :=
  (Measure.absolutelyContinuous_smul (slotWeight_pos k).ne').trans
    ((weighted_slotLaw_le d P k).absolutelyContinuous.trans hτ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TaggedPointContacts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For a free point, absolute continuity of tuple laws removes every open
tag contact. A hit at that point must then be a residual contact. -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] in
theorem no_tag_contact_of_slot_zero (H : ℕ → Set (UnitAddCircle × X))
    (hH : ∀ i, IsClosed (H i)) (Γ : TaggedPath X) (x : X) (k : ℕ)
    (hcontain : (Γ.1, Γ.2 k) ∈ tagContainment H)
    (hzero : slotTupleMeasure (Γ.2 k) (tupleIncident H x) = 0)
    (t : PathTime) (ht : Γ.1 t = x) :
    ¬ (tagLeft (Γ.2 k) < t ∧ t < tagRight (Γ.2 k)) := by
  rintro ⟨hl, hr⟩
  have hc := hcontain t hl hr
  rw [ht] at hc
  cases hs : Γ.2 k with
  | inl u =>
    simp only [hs, tagLeft, Sum.elim_inl] at hl
    exact (not_lt_of_ge le_top) hl
  | inr q =>
    have hmem : tagDataTuple q ∈ tupleIncident H x := by
      change ∃ j, (q.2.2.1 j, x) ∈ H (q.2.1 j)
      simpa only [hs, tagLevelGraph, activeTagLevelGraph, mem_ofPred_eq] using hc
    rw [hs, slotTupleMeasure, Sum.elim_inr,
      Measure.dirac_apply' _ (isClosed_tupleIncident hH x).measurableSet,
      indicator_of_mem hmem, Pi.one_apply] at hzero
    exact one_ne_zero hzero

theorem path_hit_iff_residual_of_slot_zero (d : PathCodeData X Y)
    (hH : ∀ i, IsClosed (d.levels i)) (Γ : BasePathCode d) {x : X} (hx : x ∈ d.dust)
    (hz : ∀ k, slotTupleMeasure (Γ.val.2 k) (tupleIncident d.levels x) = 0) :
    x ∈ Set.range Γ.val.1 ↔ x ∈ residualImage d.dust Γ.val := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ⟨by simpa only [ht] using hx, fun k => ?_⟩, ht⟩
    by_cases hl : t ≤ tagLeft (Γ.val.2 k)
    · exact Or.inl hl
    · right
      by_contra hr
      exact no_tag_contact_of_slot_zero d.levels hH Γ.val x k
        (Γ.property.1.2.1 k).2.1 (hz k) t ht ⟨lt_of_not_ge hl, lt_of_not_ge hr⟩
  · rintro ⟨t, _, ht⟩
    exact ⟨t, ht⟩

theorem ae_slot_incidence_zero (d : PathCodeData X Y)
    (hH : ∀ i, IsClosed (d.levels i)) (P : ProbabilityMeasure (BasePathCode d))
    (ω : TupleType → ℝ≥0∞) (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (x : X) (hx : ∀ i, volume {t : UnitAddCircle | (t, x) ∈ d.levels i} = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      ∀ k, slotTupleMeasure (Γ.val.2 k) (tupleIncident d.levels x) = 0 := by
  apply ae_all_iff.mpr
  intro k
  have hA := (isClosed_tupleIncident hH x).measurableSet
  have hz := slotLaw_absolutelyContinuous d P (tupleReference ω) hτ k
    (tupleReference_incident_null hH ω x hx)
  rw [slotLaw_apply d P k hA] at hz
  exact (lintegral_eq_zero_iff ((Measure.measurable_coe hA).comp
    (measurable_baseCodeSlot d k))).mp hz

theorem ae_path_hit_iff_residual (d : PathCodeData X Y)
    (hH : ∀ i, IsClosed (d.levels i)) (P : ProbabilityMeasure (BasePathCode d))
    (ω : TupleType → ℝ≥0∞) (hτ : meanCodeTuple d P ≪ tupleReference ω)
    {x : X} (hx : x ∈ d.dust)
    (hfree : ∀ i, volume {t : UnitAddCircle | (t, x) ∈ d.levels i} = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      x ∈ Set.range Γ.val.1 ↔ x ∈ residualImage d.dust Γ.val :=
  (ae_slot_incidence_zero d hH P ω hτ x hfree).mono fun Γ hΓ =>
    path_hit_iff_residual_of_slot_zero d hH Γ hx hΓ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeHitMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini for complete path images. At free points, tuple absolute
continuity reduces a path hit to a residual hit; residual nullity then
annihilates the integrated whole-image hit probability. -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem isClosed_codeResidualGraph (d : PathCodeData X Y) (hB : IsClosed d.dust) :
    IsClosed (codeResidualGraph d) :=
  (isClosed_residualImageGraph hB).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

variable [BorelSpace X] [BorelSpace C(PathTime, X)] [SecondCountableTopology X]

theorem lintegral_codeResidualProbability (d : PathCodeData X Y) (hB : IsClosed d.dust)
    (P : ProbabilityMeasure (BasePathCode d)) (ν : Measure X) [SFinite ν] :
    ∫⁻ x, codeResidualProbability d P x ∂ν =
      ∫⁻ Γ : BasePathCode d, ν (residualImage d.dust Γ.val) ∂(P : Measure (BasePathCode d)) := by
  have hm := (isClosed_codeResidualGraph d hB).measurableSet
  exact (Measure.prod_apply_symm hm).symm.trans (Measure.prod_apply hm)

omit [BorelSpace X] [BorelSpace C(PathTime, X)] [SecondCountableTopology X] in
theorem codeHitProbability_eq_residual (d : PathCodeData X Y)
    (hH : ∀ i, IsClosed (d.levels i)) (P : ProbabilityMeasure (BasePathCode d))
    (ω : TupleType → ℝ≥0∞) (hτ : meanCodeTuple d P ≪ tupleReference ω)
    {x : X} (hx : x ∈ d.dust)
    (hfree : ∀ i, volume {t : UnitAddCircle | (t, x) ∈ d.levels i} = 0) :
    codeHitProbability d P x = codeResidualProbability d P x := by
  apply measure_congr
  filter_upwards [ae_path_hit_iff_residual d hH P ω hτ hx hfree] with Γ hΓ
  exact propext hΓ

theorem lintegral_codeHitProbability_zero (d : PathCodeData X Y) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) (P : ProbabilityMeasure (BasePathCode d))
    (ω : TupleType → ℝ≥0∞) (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (ν : Measure X) [SFinite ν]
    (hfree : ∀ᵐ x ∂ν, x ∈ d.dust ∧
      ∀ i, volume {t : UnitAddCircle | (t, x) ∈ d.levels i} = 0)
    (hres : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0) :
    ∫⁻ x, codeHitProbability d P x ∂ν = 0 := by
  calc
    _ = ∫⁻ x, codeResidualProbability d P x ∂ν :=
      lintegral_congr_ae (hfree.mono fun x hx =>
        codeHitProbability_eq_residual d hH P ω hτ hx.1 hx.2)
    _ = ∫⁻ Γ : BasePathCode d, ν (residualImage d.dust Γ.val)
        ∂(P : Measure (BasePathCode d)) := lintegral_codeResidualProbability d hB P ν
    _ = 0 := (lintegral_eq_zero_iff
      ((measurable_residualImageMass hB ν).comp measurable_subtype_coe)).mpr hres

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathCostReference
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite reference measure for modulus: physical area, squared
countable-point weights, and the weighted tuple tori. Its square integral
is exactly the sum of the three corresponding energies. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

omit [TopologicalSpace D] [BorelSpace D] in
theorem atomicReference_univ (c : D → ℝ≥0∞) :
    atomicReference c univ = ∑' s, (c s) ^ 2 := by
  simp only [atomicReference, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]

omit [TopologicalSpace D] [BorelSpace D] in
theorem lintegral_atomicReference (c : D → ℝ≥0∞) (f : D → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ s, f s ∂atomicReference c = ∑' s, (c s) ^ 2 * f s := by
  rw [atomicReference, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

theorem pathCostReference_univ (μ : Measure Y) (c : D → ℝ≥0∞) (τ : Measure LevelTuple) :
    pathCostReference μ c τ univ = μ univ + (∑' s, (c s) ^ 2) + τ univ := by
  simp only [pathCostReference, Measure.add_apply,
    Measure.map_apply measurable_costPhysical MeasurableSet.univ,
    Measure.map_apply measurable_costAtomic MeasurableSet.univ,
    Measure.map_apply measurable_costTuple MeasurableSet.univ,
    preimage_univ, atomicReference_univ]

theorem finite_pathCostReference (μ : Measure Y) [IsFiniteMeasure μ]
    (c : D → ℝ≥0∞) (hc : (∑' s, (c s) ^ 2) < ∞)
    (τ : Measure LevelTuple) [IsFiniteMeasure τ] : IsFiniteMeasure (pathCostReference μ c τ) := by
  constructor
  rw [pathCostReference_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨measure_lt_top μ univ, hc⟩,
    measure_lt_top τ univ⟩

theorem lintegral_pathCostReference (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z, h z ∂pathCostReference μ c τ =
      (∫⁻ y, h (costPhysical y) ∂μ) +
      (∑' s, (c s) ^ 2 * h (costAtomic s)) + ∫⁻ t, h (costTuple t) ∂τ := by
  rw [pathCostReference, lintegral_add_measure, lintegral_add_measure,
    lintegral_map hh measurable_costPhysical, lintegral_map hh measurable_costAtomic,
    lintegral_map hh measurable_costTuple]
  rw [lintegral_atomicReference c (fun s => h (costAtomic s)) (hh.comp measurable_costAtomic)]

theorem squareIntegral_pathCostReference (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z, h z ^ 2 ∂pathCostReference μ c τ =
      (∫⁻ y, h (costPhysical y) ^ 2 ∂μ) +
      (∑' s, (c s * h (costAtomic s)) ^ 2) + ∫⁻ t, h (costTuple t) ^ 2 ∂τ := by
  rw [lintegral_pathCostReference μ c τ _ (hh.pow_const 2)]
  simp only [mul_pow]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CostSummands
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three disjoint cost summands can be recovered from the total
measure. In particular a total barycenter density gives the physical
occupation density on the original domain. -/

open Set MeasureTheory Topology
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

omit [MeasurableSpace D] [BorelSpace D] in
theorem measurableEmbedding_costPhysical :
    MeasurableEmbedding (costPhysical (Y := Y) (D := D)) := by
  have hi : IsOpenEmbedding (costPhysical (Y := Y) (D := D)) := IsOpenEmbedding.inl
  exact IsOpenEmbedding.measurableEmbedding (α := Y) (β := PathCostSpace Y D) hi

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem measurableEmbedding_costAtomic :
    MeasurableEmbedding (costAtomic (Y := Y) (D := D)) := by
  have hi : IsOpenEmbedding (costAtomic (Y := Y) (D := D)) :=
    IsOpenEmbedding.inr.comp IsOpenEmbedding.inl
  exact IsOpenEmbedding.measurableEmbedding (α := D) (β := PathCostSpace Y D) hi

omit [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D] in
theorem measurableEmbedding_costTuple :
    MeasurableEmbedding (costTuple (Y := Y) (D := D)) := by
  have hi : IsOpenEmbedding (costTuple (Y := Y) (D := D)) :=
    IsOpenEmbedding.inr.comp IsOpenEmbedding.inr
  exact IsOpenEmbedding.measurableEmbedding (α := LevelTuple) (β := PathCostSpace Y D) hi

theorem sumCostMeasures_physical (μ : Measure Y) (a : Measure D) (τ : Measure LevelTuple)
    {A : Set Y} (hA : MeasurableSet A) :
    sumCostMeasures μ a τ (costPhysical '' A) = μ A := by
  have hI := (measurableEmbedding_costPhysical (Y := Y) (D := D)).measurableSet_image.mpr hA
  rw [sumCostMeasures, Measure.add_apply, Measure.add_apply,
    Measure.map_apply measurable_costPhysical hI, Measure.map_apply measurable_costAtomic hI,
    Measure.map_apply measurable_costTuple hI]
  have hself : costPhysical ⁻¹' (costPhysical (Y := Y) (D := D) '' A) = A :=
    Set.preimage_image_eq A (measurableEmbedding_costPhysical (Y := Y) (D := D)).injective
  have hatom : costAtomic ⁻¹' (costPhysical (Y := Y) (D := D) '' A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s
    rintro ⟨y, _, he⟩
    change Sum.inl y = Sum.inr (Sum.inl s) at he
    cases he
  have htuple : costTuple ⁻¹' (costPhysical (Y := Y) (D := D) '' A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t
    rintro ⟨y, _, he⟩
    change Sum.inl y = Sum.inr (Sum.inr t) at he
    cases he
  simp only [hself, hatom, htuple, measure_empty, add_zero]

theorem sumCostMeasures_atomic (μ : Measure Y) (a : Measure D) (τ : Measure LevelTuple)
    {A : Set D} (hA : MeasurableSet A) :
    sumCostMeasures μ a τ (costAtomic '' A) = a A := by
  have hI := (measurableEmbedding_costAtomic (Y := Y) (D := D)).measurableSet_image.mpr hA
  rw [sumCostMeasures, Measure.add_apply, Measure.add_apply,
    Measure.map_apply measurable_costPhysical hI, Measure.map_apply measurable_costAtomic hI,
    Measure.map_apply measurable_costTuple hI]
  have hself : costAtomic ⁻¹' (costAtomic (Y := Y) (D := D) '' A) = A :=
    Set.preimage_image_eq A (measurableEmbedding_costAtomic (Y := Y) (D := D)).injective
  have hphys : costPhysical ⁻¹' (costAtomic (Y := Y) (D := D) '' A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y
    rintro ⟨s, _, he⟩
    change Sum.inr (Sum.inl s) = Sum.inl y at he
    cases he
  have htuple : costTuple ⁻¹' (costAtomic (Y := Y) (D := D) '' A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t
    rintro ⟨s, _, he⟩
    change Sum.inr (Sum.inl s) = Sum.inr (Sum.inr t) at he
    cases Sum.inr.inj he
  simp only [hself, hphys, htuple, measure_empty, zero_add, add_zero]

theorem sumCostMeasures_tuple (μ : Measure Y) (a : Measure D) (τ : Measure LevelTuple)
    {A : Set LevelTuple} (hA : MeasurableSet A) :
    sumCostMeasures μ a τ (costTuple '' A) = τ A := by
  have hI := (measurableEmbedding_costTuple (Y := Y) (D := D)).measurableSet_image.mpr hA
  rw [sumCostMeasures, Measure.add_apply, Measure.add_apply,
    Measure.map_apply measurable_costPhysical hI, Measure.map_apply measurable_costAtomic hI,
    Measure.map_apply measurable_costTuple hI]
  have hself : costTuple ⁻¹' (costTuple (Y := Y) (D := D) '' A) = A :=
    Set.preimage_image_eq A (measurableEmbedding_costTuple (Y := Y) (D := D)).injective
  have hphys : costPhysical ⁻¹' (costTuple (Y := Y) (D := D) '' A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y
    rintro ⟨t, _, he⟩
    change Sum.inr (Sum.inr t) = Sum.inl y at he
    cases he
  have hatom : costAtomic ⁻¹' (costTuple (Y := Y) (D := D) '' A) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s
    rintro ⟨t, _, he⟩
    change Sum.inr (Sum.inr t) = Sum.inr (Sum.inl s) at he
    cases Sum.inr.inj he
  simp only [hself, hphys, hatom, measure_empty, zero_add]

theorem sumCostMeasures_absolutelyContinuous {μ μ' : Measure Y} {a a' : Measure D}
    {τ τ' : Measure LevelTuple}
    (h : sumCostMeasures μ a τ ≪ sumCostMeasures μ' a' τ') :
    μ ≪ μ' ∧ a ≪ a' ∧ τ ≪ τ' := by
  refine ⟨Measure.AbsolutelyContinuous.mk ?_, Measure.AbsolutelyContinuous.mk ?_,
    Measure.AbsolutelyContinuous.mk ?_⟩
  · intro A hA hz
    rw [← sumCostMeasures_physical μ a τ hA]
    exact h (by rw [sumCostMeasures_physical μ' a' τ' hA, hz])
  · intro A hA hz
    rw [← sumCostMeasures_atomic μ a τ hA]
    exact h (by rw [sumCostMeasures_atomic μ' a' τ' hA, hz])
  · intro A hA hz
    rw [← sumCostMeasures_tuple μ a τ hA]
    exact h (by rw [sumCostMeasures_tuple μ' a' τ' hA, hz])

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeanVisitDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density on a countable cost atom records the actual mean number
of preterminal visits. The squared density budget therefore bounds the
counting square norm independently of the auxiliary positive weights. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D] [MeasurableSingletonClass D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace C(PathTime, X)]
  [BorelSpace C(PathTime, X)] [SecondCountableTopology X] [TopologicalSpace D]
  [BorelSpace D] [Countable D] in
theorem atomicVisitMeasure_singleton (p : D → X) (c : D → ℝ≥0∞)
    (γ : C(PathTime, X)) (s : D) :
    atomicVisitMeasure p c γ {s} = c s * preterminalVisitCount γ (p s) := by
  classical
  rw [atomicVisitMeasure_apply p c γ (measurableSet_singleton s)]
  simp [Set.indicator]

omit [TopologicalSpace D] [BorelSpace D] [Countable D] in
theorem atomicReference_singleton (c : D → ℝ≥0∞) (s : D) :
    atomicReference c {s} = (c s) ^ 2 := by
  classical
  simp only [atomicReference, Measure.sum_apply _ (measurableSet_singleton s),
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton s)]
  simp [Set.indicator]

omit [TopologicalSpace D] [BorelSpace D] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem meanCodeAtomic_singleton (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) (s : D) :
    meanCodeAtomic d p c P {s} = c s * meanCodePreVisits d P (p s) := by
  rw [meanCodeAtomic_apply d p c P (measurableSet_singleton s)]
  simp_rw [atomicVisitMeasure_singleton]
  exact lintegral_const_mul _ (measurable_preterminalVisitCount.comp
    ((measurable_fst.comp measurable_subtype_coe).prodMk measurable_const))

theorem meanCodePreVisits_density (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (P : ProbabilityMeasure (BasePathCode d))
    (μ : Measure Y) (τ : Measure LevelTuple) (q : PathCostSpace Y D → ℝ≥0∞)
    (hq : Measurable q)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q)
    (s : D) (hc0 : c s ≠ 0) (hct : c s ≠ ∞) :
    meanCodePreVisits d P (p s) = c s * q (costAtomic s) := by
  have hA := measurableSet_singleton s
  have hI := (measurableEmbedding_costAtomic (Y := Y) (D := D)).measurableSet_image.mpr hA
  have he := congrArg (fun ν : Measure (PathCostSpace Y D) => ν (costAtomic '' {s})) hbar
  rw [meanCodeCost_eq d hU p c P] at he
  change sumCostMeasures (meanCodeOccupation d P) (meanCodeAtomic d p c P)
    (meanCodeTuple d P) (costAtomic '' {s}) = _ at he
  rw [sumCostMeasures_atomic _ _ _ hA, meanCodeAtomic_singleton,
    withDensity_apply q hI, Set.image_singleton, lintegral_singleton' hq] at he
  have href : pathCostReference μ c τ {costAtomic s} = (c s) ^ 2 := by
    rw [← Set.image_singleton]
    exact (sumCostMeasures_atomic μ (atomicReference c) τ hA).trans
      (atomicReference_singleton c s)
  rw [href] at he
  apply (ENNReal.mul_left_inj hc0 hct).mp
  calc
    meanCodePreVisits d P (p s) * c s = c s * meanCodePreVisits d P (p s) := mul_comm _ _
    _ = q (costAtomic s) * (c s) ^ 2 := he
    _ = (c s * q (costAtomic s)) * c s := by rw [pow_two]; ac_rfl

theorem meanCodePreVisits_square_budget (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (hc0 : ∀ s, c s ≠ 0) (hct : ∀ s, c s ≠ ∞)
    (P : ProbabilityMeasure (BasePathCode d)) (μ : Measure Y) (τ : Measure LevelTuple)
    (q : PathCostSpace Y D → ℝ≥0∞) (hq : Measurable q)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q) :
    (∑' s, meanCodePreVisits d P (p s) ^ 2) ≤
      ∫⁻ z, q z ^ 2 ∂pathCostReference μ c τ := by
  simp_rw [meanCodePreVisits_density d hU p c P μ τ q hq hbar _ (hc0 _) (hct _)]
  rw [squareIntegral_pathCostReference μ c τ q hq]
  exact le_trans le_add_self le_self_add

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodePathLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Forgetting the optional tags produces the actual path law. Its full
mean visit function differs from the preterminal function by exactly one
unit at the prescribed terminal point. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

variable [BorelSpace X] [BorelSpace C(PathTime, X)] [SecondCountableTopology X]

theorem meanVisitCount_codePathLaw (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (x : X) :
    meanVisitCount (codePathLaw d P) x =
      meanCodePreVisits d P x + if d.target = x then 1 else 0 := by
  classical
  have hv : Measurable (fun γ : C(PathTime, X) => visitCount γ x) :=
    measurable_visitCount.comp (measurable_id.prodMk measurable_const)
  unfold meanVisitCount codePathLaw
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map hv (measurable_codePath d)]
  have he : ∀ Γ : BasePathCode d, visitCount (codePath d Γ) x =
      preterminalVisitCount Γ.val.1 x + if d.target = x then 1 else 0 := by
    intro Γ
    rw [visitCount_eq_preterminal_add_terminal]
    change preterminalVisitCount Γ.val.1 x + terminalVisitCount Γ.val.1 x = _
    rw [terminalVisitCount, Γ.property.2.1.2.1]
  simp_rw [he]
  have hm : Measurable (fun Γ : BasePathCode d => preterminalVisitCount Γ.val.1 x) :=
    measurable_preterminalVisitCount.comp
      ((measurable_fst.comp measurable_subtype_coe).prodMk measurable_const)
  rw [lintegral_add_left hm]
  simp only [lintegral_const, measure_univ, mul_one, meanCodePreVisits]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableVisitNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring the terminal visit adds at most one to the counting square
norm. The estimate is independent of the auxiliary positive atomic weights. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

theorem countingSquareNorm_mono {D : Type*} {a b : D → ℝ≥0∞}
    (h : ∀ s, a s ≤ b s) : countingSquareNorm a ≤ countingSquareNorm b := by
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact ENNReal.tsum_le_tsum (fun s => pow_le_pow_left' (h s) 2)

theorem countingSquareNorm_add_le {D : Type*} [Countable D] (a b : D → ℝ≥0∞) :
    countingSquareNorm (a + b) ≤ countingSquareNorm a + countingSquareNorm b := by
  let : MeasurableSpace D := ⊤
  have h := ENNReal.lintegral_Lp_add_le (μ := Measure.count)
    (p := (2 : ℝ)) (measurable_of_countable a).aemeasurable
    (measurable_of_countable b).aemeasurable (by norm_num)
  simpa only [ENNReal.rpow_two, lintegral_count, countingSquareNorm] using h

theorem countingSquareNorm_terminal_le {D X : Type*} (p : D → X)
    (hp : Function.Injective p) (x : X) :
    countingSquareNorm (fun s => if x = p s then 1 else 0) ≤ 1 := by
  classical
  by_cases ht : ∃ t, p t = x
  · obtain ⟨t, ht⟩ := ht
    have he : (fun s => if x = p s then (1 : ℝ≥0∞) else 0) =
        fun s => if s = t then 1 else 0 := by
      funext s
      simp only [← ht, hp.eq_iff, eq_comm]
    simp [he, countingSquareNorm]
  · have he : (fun s => if x = p s then (1 : ℝ≥0∞) else 0) = fun _ => 0 := by
      funext s
      rw [ite_eq_right (fun h => ht ⟨s, h.symm⟩)]
    simp [he, countingSquareNorm]

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D] [MeasurableSingletonClass D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

omit [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D]
  [MeasurableSingletonClass D] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem meanVisitCount_codePathLaw_norm (d : PathCodeData X Y)
    (p : D → X) (hp : Function.Injective p) (P : ProbabilityMeasure (BasePathCode d)) :
    countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (p s)) ≤
      countingSquareNorm (fun s => meanCodePreVisits d P (p s)) + 1 := by
  simp_rw [meanVisitCount_codePathLaw]
  exact (countingSquareNorm_add_le _ _).trans
    (add_le_add le_rfl (countingSquareNorm_terminal_le p hp d.target))

theorem meanVisitCount_codePathLaw_budget (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (p : D → X) (hp : Function.Injective p)
    (c : D → ℝ≥0∞) (hc0 : ∀ s, c s ≠ 0) (hct : ∀ s, c s ≠ ∞)
    (P : ProbabilityMeasure (BasePathCode d)) (μ : Measure Y) (τ : Measure LevelTuple)
    (q : PathCostSpace Y D → ℝ≥0∞) (hq : Measurable q)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q) :
    countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (p s)) ≤
      (∫⁻ z, q z ^ 2 ∂pathCostReference μ c τ) ^ (1 / 2 : ℝ) + 1 := by
  apply (meanVisitCount_codePathLaw_norm d p hp P).trans
  apply add_le_add _ le_rfl
  exact ENNReal.rpow_le_rpow
    (meanCodePreVisits_square_budget d hU p c hc0 hct P μ τ q hq hbar) (by norm_num)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawAbsoluteContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A density for the total coding barycenter gives absolute continuity
on each cost summand, including every tuple slot and the whole-image
atomless tests. -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

theorem codeLaw_components_absolutelyContinuous (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) (μ : Measure Y) (τ : Measure LevelTuple)
    (q : PathCostSpace Y D → ℝ≥0∞)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q) :
    meanCodeOccupation d P ≪ μ ∧ meanCodeAtomic d p c P ≪ atomicReference c ∧
      meanCodeTuple d P ≪ τ := by
  have hac := withDensity_absolutelyContinuous (pathCostReference μ c τ) q
  rw [← hbar, meanCodeCost_eq d hU p c P] at hac
  exact sumCostMeasures_absolutelyContinuous hac

theorem codeLaw_slot_absolutelyContinuous (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) (μ : Measure Y) (τ : Measure LevelTuple)
    (q : PathCostSpace Y D → ℝ≥0∞)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q) (k : ℕ) :
    slotLaw d P k ≪ τ :=
  slotLaw_absolutelyContinuous d P τ
    (codeLaw_components_absolutelyContinuous d hU p c P μ τ q hbar).2.2 k

theorem codeLaw_whole_image_test (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) (μ : Measure Y) (ω : TupleType → ℝ≥0∞)
    (q : PathCostSpace Y D → ℝ≥0∞)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c (tupleReference ω)).withDensity q)
    (ν : Measure X) [SFinite ν]
    (hfree : ∀ᵐ x ∂ν, x ∈ d.dust ∧
      ∀ i, volume {t : UnitAddCircle | (t, x) ∈ d.levels i} = 0)
    (hres : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0) :
    ∫⁻ x, codeHitProbability d P x ∂ν = 0 :=
  lintegral_codeHitProbability_zero d hB hH P ω
    (codeLaw_components_absolutelyContinuous d hU p c P μ (tupleReference ω) q hbar).2.2
    ν hfree hres

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CodeBarycenterDensities
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three components of a coding barycenter have the restrictions
of its density. Their square energies are bounded by the total energy. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

private theorem withDensity_map_comp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) {f : A → B} (hf : Measurable f) {q : B → ℝ≥0∞} (hq : Measurable q) :
    (μ.map f).withDensity q = (μ.withDensity (q ∘ f)).map f := by
  ext E hE
  rw [withDensity_apply q hE, Measure.restrict_map hf hE,
    lintegral_map hq hf, Measure.map_apply hf hE,
    withDensity_apply (q ∘ f) (hf hE)]
  rfl

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

theorem withDensity_sumCostMeasures (μ : Measure Y) (a : Measure D) (τ : Measure LevelTuple)
    (q : PathCostSpace Y D → ℝ≥0∞) (hq : Measurable q) :
    (sumCostMeasures μ a τ).withDensity q =
      sumCostMeasures (μ.withDensity (q ∘ costPhysical))
        (a.withDensity (q ∘ costAtomic)) (τ.withDensity (q ∘ costTuple)) := by
  simp only [sumCostMeasures, withDensity_add_measure,
    withDensity_map_comp _ measurable_costPhysical hq,
    withDensity_map_comp _ measurable_costAtomic hq,
    withDensity_map_comp _ measurable_costTuple hq]

theorem sumCostMeasures_injective {μ μ' : Measure Y} {a a' : Measure D}
    {τ τ' : Measure LevelTuple} (h : sumCostMeasures μ a τ = sumCostMeasures μ' a' τ') :
    μ = μ' ∧ a = a' ∧ τ = τ' := by
  refine ⟨?_, ?_, ?_⟩
  · ext E hE
    have he := congrArg (fun ν : Measure (PathCostSpace Y D) => ν (costPhysical '' E)) h
    simpa only [sumCostMeasures_physical _ _ _ hE] using he
  · ext E hE
    have he := congrArg (fun ν : Measure (PathCostSpace Y D) => ν (costAtomic '' E)) h
    simpa only [sumCostMeasures_atomic _ _ _ hE] using he
  · ext E hE
    have he := congrArg (fun ν : Measure (PathCostSpace Y D) => ν (costTuple '' E)) h
    simpa only [sumCostMeasures_tuple _ _ _ hE] using he

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

theorem codeLaw_component_densities (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (P : ProbabilityMeasure (BasePathCode d))
    (μ : Measure Y) (τ : Measure LevelTuple) (q : PathCostSpace Y D → ℝ≥0∞)
    (hq : Measurable q)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q) :
    meanCodeOccupation d P = μ.withDensity (q ∘ costPhysical) ∧
      meanCodeAtomic d p c P = (atomicReference c).withDensity (q ∘ costAtomic) ∧
      meanCodeTuple d P = τ.withDensity (q ∘ costTuple) := by
  rw [meanCodeCost_eq d hU p c P] at hbar
  change sumCostMeasures (meanCodeOccupation d P) (meanCodeAtomic d p c P)
    (meanCodeTuple d P) = (sumCostMeasures μ (atomicReference c) τ).withDensity q at hbar
  rw [withDensity_sumCostMeasures μ (atomicReference c) τ q hq] at hbar
  exact sumCostMeasures_injective hbar

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace C(PathTime, X)]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)] [SecondCountableTopology X] [Countable D] in
theorem codeReference_component_energies (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) (q : PathCostSpace Y D → ℝ≥0∞) (hq : Measurable q) :
    (∫⁻ y, q (costPhysical y) ^ 2 ∂μ) ≤ ∫⁻ z, q z ^ 2 ∂pathCostReference μ c τ ∧
      (∫⁻ t, q (costTuple t) ^ 2 ∂τ) ≤ ∫⁻ z, q z ^ 2 ∂pathCostReference μ c τ := by
  rw [squareIntegral_pathCostReference μ c τ q hq]
  exact ⟨le_add_of_le_left le_self_add, le_add_self⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_BandMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Haar measure of a projected band

The projection of a real interval of length `b - a` is contained in
the circle ball with midpoint `(a + b) / 2` and radius `(b - a) / 2`.
This gives the manuscript's band-incidence bound, including long bands.
-/

open Set MeasureTheory Metric
open scoped Topology

namespace CircleDomainRigidity

/-- The band-incidence estimate in the coordinates used by the paper:
the budget bounds the difference of the actual upper and lower limits. -/
theorem volume_circleBandGraph_incidence_le_budget
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ y ∈ G, |f y| ≤ M)
    {x : X} (hx : x ∈ closure G) {a : ℝ}
    (hbudget : Filter.limsup f (𝓝[G] x) - Filter.liminf f (𝓝[G] x) ≤ a) :
    volume {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G f} ≤
      ENNReal.ofReal a := by
  rw [circleBandGraph_fiber_eq_image_realFiber,
    intervalFiberHull_clusterGraph_eq_boundary_band hM hx]
  exact (volume_addCircle_image_Icc_le _ _).trans
    (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans hbudget))

end CircleDomainRigidity

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

/-- To rule out a nondegenerate component, it suffices to rule out small
subcontinua through the point in one open neighborhood. -/
theorem component_eq_singleton_of_local_no_continuum
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F U : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hU : IsOpen U) (hxU : x ∈ U)
    (hno : ∀ D : Set X, IsCompact D → IsConnected D → x ∈ D →
      D ⊆ F ∩ U → ¬ D.Nontrivial) :
    connectedComponentIn F x = {x} := by
  have hclosed : IsClosed (connectedComponentIn F x) := by
    rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hconn := isConnected_connectedComponentIn_iff.mpr hx
  have hsub : (connectedComponentIn F x).Subsingleton := by
    by_contra hn
    have hnt : (connectedComponentIn F x).Nontrivial := Set.not_subsingleton_iff.mp hn
    obtain ⟨D, hDcompact, hDconn, hDnt, hxD, hDsub⟩ :=
      exists_nontrivial_subcontinuum_in_open hclosed.isCompact hconn hnt
        (mem_connectedComponentIn hx) hU hxU
    exact hno D hDcompact hDconn hxD
      (fun y hy => ⟨connectedComponentIn_subset F x (hDsub hy).1, (hDsub hy).2⟩) hDnt
  exact hsub.eq_singleton_of_mem (mem_connectedComponentIn hx)

/-- Near a point, a finite closed level union only uses the levels which
contain that point. A singleton component in this smaller union is
therefore a singleton component in the entire union. -/
theorem component_finite_union_eq_singleton
    {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (s : Finset ι) (H : ι → Set X) (hH : ∀ i ∈ s, IsClosed (H i))
    {x : X} (hx : x ∈ ⋃ i ∈ s, H i)
    (hpresent : connectedComponentIn (⋃ i ∈ s, ⋃ (_ : x ∈ H i), H i) x = {x}) :
    connectedComponentIn (⋃ i ∈ s, H i) x = {x} := by
  classical
  let F := ⋃ i ∈ s, H i
  let B := ⋃ i ∈ s.filter (fun i => x ∉ H i), H i
  have hF : IsClosed F := isClosed_biUnion_finset (fun i hi => hH i hi)
  have hB : IsClosed B := isClosed_biUnion_finset (fun i hi => hH i (Finset.mem_filter.mp hi).1)
  have hxB : x ∉ B := by
    simp only [B, mem_iUnion, exists_prop, Finset.mem_filter]
    rintro ⟨i, ⟨_, hxi⟩, hxi'⟩
    exact hxi hxi'
  apply component_eq_singleton_of_local_no_continuum hF hx hB.isOpen_compl hxB
  intro D hDcompact hDconn hxD hDsub hDnt
  have hsub : D ⊆ ⋃ i ∈ s, ⋃ (_ : x ∈ H i), H i := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hDsub hy).1
    have hxi : x ∈ H i := by
      by_contra hn
      exact (hDsub hy).2 (mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hn⟩, hyi⟩)
    exact mem_iUnion₂.mpr ⟨i, hi, mem_iUnion.mpr ⟨hxi, hyi⟩⟩
  have hsingle : D ⊆ {x} := by
    rw [← hpresent]
    exact hDconn.isPreconnected.subset_connectedComponentIn hxD hsub
  exact hDnt.not_subsingleton (fun _ ha _ hb => (mem_singleton_iff.mp (hsingle ha)).trans
    (mem_singleton_iff.mp (hsingle hb)).symm)

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
-- module Solutions.Q146_CD.CircleDomains_Probability_DomainPhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a path contained in the physical domain, the dyadic occupation
kernel is exactly ordinary arclength occupation, with multiplicity. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem physicalStageOccupation_project (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) (n : ℕ) :
    physicalStageOccupation e y₀ n (projectDomainPath e β.val hβ) = pathOccupation β := by
  have he (i : Fin (2 ^ n)) :
      rectifiableOccupationCode (physicalDyadicPath e y₀ n i (projectDomainPath e β.val hβ)) =
        pathPortionOccupation β (dyadicLeft n i) (dyadicRight n i) := by
    rw [physicalDyadicPath_project]
    change rectifiableOccupationCode (clippedPath β (dyadicLeft_le_right n i)).val = _
    rw [rectifiableOccupationCode_eq (clippedPath β (dyadicLeft_le_right n i)).property]
    exact pathOccupation_clipped β (dyadicLeft_le_right n i)
  ext E hE
  have hsum := congrArg (fun ν : Measure PathTime => ν (β.val ⁻¹' E))
    (sum_dyadic_restrict (pathLengthMeasure β) n)
  simp only [Measure.coe_finsetSum, Finset.sum_apply] at hsum
  simpa only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply, he,
    pathPortionOccupation, Measure.map_apply β.val.continuous.measurable hE,
    pathOccupation_apply β hE] using hsum

theorem dyadicPhysicalOccupation_project (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) :
    dyadicPhysicalOccupation e y₀ (finiteProjectedPhysicalPath e y₀ β hβ) = pathOccupation β := by
  ext E hE
  rw [dyadicPhysicalOccupation_apply e y₀ _ hE]
  change (⨆ n, physicalStageOccupation e y₀ n (projectDomainPath e β.val hβ) E) = _
  simp only [physicalStageOccupation_project, iSup_const]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CountableImageIncidence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for the countable image exposed by discarded constant
tags. The estimate charges parameter times, and hence retains multiplicity. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {T X Z : Type*}

theorem timeToll_eq_indicator (γ : T → X) (A : Set T) (m : X → ℝ≥0∞) :
    timeToll γ A m = ∑' t, if t ∈ A then m (γ t) else 0 := by
  exact tsum_subtype A (fun t => m (γ t))

theorem timeToll_mono (γ : T → X) (m : X → ℝ≥0∞) {A C : Set T}
    (h : A ⊆ C) : timeToll γ A m ≤ timeToll γ C m :=
  ENNReal.tsum_mono_subtype (fun t => m (γ t)) h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TimeIncidenceReparametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence and multiplicity-sensitive tolls under an injective change
of path parameter. These formulas also apply to a restricted interval. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {S T X Z : Type*}

theorem timeToll_image (γ : T → X) (f : S → T) (hf : Injective f)
    (A : Set S) (m : X → ℝ≥0∞) :
    timeToll γ (f '' A) m = timeToll (γ ∘ f) A m := by
  exact ((Equiv.Set.image f A hf).tsum_eq (fun t => m (γ t))).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AffineBoundaryTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact dust tolls of an affine path restriction. The preterminal cost
corresponds to a half-open old interval, so cut points are never charged twice. -/

open Set Function
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem boundaryToll_eq_timeToll (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryToll γ m = timeToll γ univ m := by
  rw [timeToll_eq_indicator]
  simp only [mem_univ, ite_true, if_true]
  rfl

theorem boundaryToll_affine (γ : C(PathTime, X)) (m : X → ℝ≥0∞)
    {a b : PathTime} (hab : a < b) :
    boundaryToll (affineRestrictedPath a b γ) m = timeToll γ (Icc a b) m := by
  rw [boundaryToll_eq_timeToll, ← range_affinePathTime hab, ← image_univ,
    timeToll_image γ _ (affinePathTime_strictMono hab).injective]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_AffinePhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted physical costs of restricted paths are the old costs on the
retained interval, with full multiplicity and no endpoint atoms. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalOccupation_affine (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) :
    dyadicPhysicalOccupation e y₀ (affineFinitePhysicalPath e hU y₀ γ hab) =
      ((physicalTimeLength e y₀ γ).restrict (Icc a b)).map (physicalValue e y₀ ∘ γ.val) := by
  have hf := (measurable_physicalValue e hU y₀).comp
    (affineRestrictedPath a b γ.val).continuous.measurable
  rw [← physicalTimeLength_map e hU y₀, physicalTimeLength_affine e hU y₀ γ hab]
  change (((physicalTimeLength e y₀ γ).restrict (Icc a b)).map (rescalePathTime a b)).map
    (physicalValue e y₀ ∘ affineRestrictedPath a b γ.val) = _
  rw [Measure.map_map hf (rescalePathTime a b).continuous.measurable]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change physicalValue e y₀ (γ.val (affinePathTime a b (rescalePathTime a b t))) =
    physicalValue e y₀ (γ.val t)
  rw [affine_rescalePathTime hab ht]

theorem physicalCost_affine (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ (affineFinitePhysicalPath e hU y₀ γ hab)) =
      ∫⁻ t in Icc a b, g (physicalValue e y₀ (γ.val t)) ∂physicalTimeLength e y₀ γ := by
  rw [physicalOccupation_affine e hU y₀ γ hab]
  exact lintegral_map hg ((measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstExitCuts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual first-exit cuts for the collar-splicing construction. Every
retained initial fragment lies in the corresponding closed collar disk. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

theorem firstExitTime_le (γ : C(PathTime, X)) (V : Set X) {t : PathTime}
    (ht : γ t ∉ V) : firstExitTime γ V ≤ t :=
  sInf_le ht

theorem mem_before_firstExit (γ : C(PathTime, X)) (V : Set X) {t : PathTime}
    (ht : t < firstExitTime γ V) : γ t ∈ V := by
  by_contra hn
  exact ht.not_ge (firstExitTime_le γ V hn)

theorem firstExit_notMem (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hend : γ ⊤ ∉ V) : γ (firstExitTime γ V) ∉ V := by
  exact (hV.isClosed_compl.preimage γ.continuous).isCompact.sInf_mem ⟨⊤, hend⟩

theorem firstExit_pos (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ V) : ⊥ < firstExitTime γ V := by
  apply bot_lt_iff_ne_bot.mpr
  intro he
  exact firstExit_notMem γ hV hend (he ▸ hstart)

theorem firstExit_frontier (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ V) : γ (firstExitTime γ V) ∈ frontier V := by
  have hpos := firstExit_pos γ hV hstart hend
  have hcl : firstExitTime γ V ∈ closure (Iio (firstExitTime γ V)) := by
    rw [closure_Iio' ⟨⊥, hpos⟩]
    exact (le_rfl : firstExitTime γ V ≤ firstExitTime γ V)
  have hmap : MapsTo γ (Iio (firstExitTime γ V)) V := fun _ ht => mem_before_firstExit γ V ht
  rw [frontier, hV.interior_eq]
  exact ⟨hmap.closure γ.continuous hcl, firstExit_notMem γ hV hend⟩

theorem firstExit_initial_segment (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ V) :
    MapsTo γ (Iic (firstExitTime γ V)) (closure V) := by
  intro t ht
  change t ≤ firstExitTime γ V at ht
  rcases ht.eq_or_lt with rfl | hlt
  · exact frontier_subset_closure (firstExit_frontier γ hV hstart hend)
  · exact subset_closure (mem_before_firstExit γ V hlt)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LastEntryCuts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Last-entry collar cuts and the strict separation of the retained
middle fragment from the two endpoint tails. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem reversedPath_zero (γ : C(PathTime, X)) : reversedPath γ ⊥ = γ ⊤ := by
  apply congrArg γ
  apply Subtype.ext
  change (1 : ℝ) - 0 = 1
  norm_num

theorem reversedPath_one (γ : C(PathTime, X)) : reversedPath γ ⊤ = γ ⊥ := by
  apply congrArg γ
  apply Subtype.ext
  change (1 : ℝ) - 1 = 0
  norm_num

theorem lastEntry_frontier (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∉ V) (hend : γ ⊤ ∈ V) : γ (lastEntryTime γ V) ∈ frontier V := by
  exact firstExit_frontier (reversedPath γ) hV
    ((reversedPath_zero γ).symm ▸ hend) ((reversedPath_one γ).symm ▸ hstart)

theorem lastEntry_final_segment (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∉ V) (hend : γ ⊤ ∈ V) :
    MapsTo γ (Ici (lastEntryTime γ V)) (closure V) := by
  intro t ht
  have hle : unitInterval.symm t ≤ firstExitTime (reversedPath γ) V :=
    unitInterval.symm_le_comm.mpr ht
  have hm := firstExit_initial_segment (reversedPath γ) hV
    ((reversedPath_zero γ).symm ▸ hend) ((reversedPath_one γ).symm ▸ hstart) hle
  change γ (unitInterval.symm (unitInterval.symm t)) ∈ closure V at hm
  simpa only [unitInterval.symm_symm] using hm

end CircleDomainRigidity

end

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
-- module Solutions.Q146_CD.CircleDomains_Modulus_CompatibleRealBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
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

namespace CompatibleRealBarrier

variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {previous : ℕ → PhysicalRealCoordinate d π} {flags EStar : Set Sphere}
  {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere} {W₁ : Set Sphere}

theorem finite_compatibility
    (B : CompatibleRealBarrier d π previous flags EStar regions f W₁)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (d.dust \ B.exclusions)
        (circleBandGraph d.quotientDomain B.coordinate.quotient)
        (fun i => circleBandGraph d.quotientDomain (previous i).quotient) labels) = 0 := by
  cases n with
  | zero => simp only [freeComponentFailure_empty_labels, measure_empty]
  | succ n => exact B.compatible n labels

end CompatibleRealBarrier
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstEntryRestriction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cut a path at its first arrival in a closed collar. The retained
prefix avoids the open collar and has no greater full cost. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem physicalTollCost_affine_le (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) {a b : PathTime} (hab : a < b)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞) :
    physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ hab) ≤
      physicalTollCost d g m γ := by
  unfold physicalTollCost
  rw [physicalCost_affine d.domainEquiv hU d.basePoint γ hab g hg]
  change _ + boundaryToll (affineRestrictedPath a b γ.val) m ≤ _
  rw [boundaryToll_affine γ.val m hab,
    physicalOccupation_integral d.domainEquiv hU d.basePoint γ g hg, boundaryToll_eq_timeToll]
  exact add_le_add (lintegral_mono' Measure.restrict_le_self le_rfl)
    (timeToll_mono γ.val m (subset_univ _))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FullDomainPhysicalLift
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An arbitrary finite physical path wholly in the quotient domain has
an actual rectifiable physical lift with exactly the original occupation. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  in
theorem fullDomainPhysicalLift_value (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) (t : PathTime) :
    (fullDomainPhysicalLift d hU γ hγ).val t = (d.domainEquiv.symm ⟨γ.val t, hγ t⟩).val := by
  simp [fullDomainPhysicalLift, physicalSubpath, timeClip]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  in
theorem fullDomainPhysicalLift_project (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) :
    finiteProjectedPhysicalPath d.domainEquiv d.basePoint
      (fullDomainPhysicalLift d hU γ hγ) (fullDomainPhysicalLift_mem d hU γ hγ) = γ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change (d.domainEquiv ⟨(fullDomainPhysicalLift d hU γ hγ).val t, _⟩).val = γ.val t
  simp only [fullDomainPhysicalLift_value]
  exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨γ.val t, hγ t⟩)

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem fullDomainPhysicalLift_projects
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain)
    (π : Y → X) (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (t : PathTime) : π ((fullDomainPhysicalLift d hU γ hγ).val t) = γ.val t := by
  simpa [fullDomainPhysicalLift, timeClip] using
    physicalSubpath_projects d.domainEquiv π (fun y => (he y).symm)
      (show (⊥ : PathTime) ≤ ⊤ from bot_le) ⟨γ.val, fun t _ => hγ t⟩ t

omit [MeasurableSpace X] [BorelSpace X] in
theorem dyadicPhysicalOccupation_fullDomainLift
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) :
    dyadicPhysicalOccupation d.domainEquiv d.basePoint γ =
      pathOccupation (fullDomainPhysicalLift d hU γ hγ) := by
  calc
    _ = dyadicPhysicalOccupation d.domainEquiv d.basePoint
        (finiteProjectedPhysicalPath d.domainEquiv d.basePoint
          (fullDomainPhysicalLift d hU γ hγ) (fullDomainPhysicalLift_mem d hU γ hγ)) :=
      congrArg (dyadicPhysicalOccupation d.domainEquiv d.basePoint)
        (fullDomainPhysicalLift_project d hU γ hγ).symm
    _ = _ := dyadicPhysicalOccupation_project _ _ _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_IndicatorPathPenalty
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A constant density on an open region pays the length of a rectifiable
passage that lies in that region apart from its last endpoint. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem indicator_occupation_of_interior_passage
    (γ : RectifiablePath Y) (O : Set Y) (hO : MeasurableSet O)
    (hinside : ∀t < (⊤ : PathTime), γ.val t ∈ O) (a : ℝ≥0∞) :
    (∫⁻y, O.indicator (fun _ => a) y ∂pathOccupation γ) = a * eVariationOn γ.val univ := by
  rw [lintegral_pathOccupation γ (measurable_const.indicator hO)]
  have hae : ∀ᵐ t ∂pathLengthMeasure γ, O.indicator (fun _ => a) (γ.val t) = a := by
    have hn := (measure_eq_zero_iff_ae_notMem).mp
      (measure_singleton (μ := pathLengthMeasure γ) (⊤ : PathTime))
    filter_upwards [hn] with t ht
    have hne : t ≠ ⊤ := by simpa only [mem_singleton_iff] using ht
    exact Set.indicator_of_mem (hinside t (lt_top_iff_ne_top.mpr hne)) (fun _ => a)
  rw [lintegral_congr_ae hae, lintegral_const, pathLengthMeasure_univ]

theorem indicator_occupation_pays_endpoint_distance
    (γ : RectifiablePath Y) (O : Set Y) (hO : MeasurableSet O)
    (hinside : ∀t < (⊤ : PathTime), γ.val t ∈ O)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδfin : δ ≠ ∞)
    (hsep : δ ≤ edist (γ.val ⊥) (γ.val ⊤)) :
    1 ≤ ∫⁻y, O.indicator (fun _ => δ⁻¹) y ∂pathOccupation γ := by
  rw [indicator_occupation_of_interior_passage γ O hO hinside]
  calc
    1 = δ⁻¹ * δ := (ENNReal.inv_mul_cancel hδ hδfin).symm
    _ ≤ δ⁻¹ * eVariationOn γ.val univ :=
      mul_le_mul' le_rfl (hsep.trans (eVariationOn.edist_le γ.val (mem_univ _) (mem_univ _)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalExitPenalty
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine bounded indicator density pays for a first-exit passage
through a relatively compact domain region. The estimate uses physical
arclength and remains valid for paths with arbitrary dust contacts elsewhere. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem first_exit_indicator_cost_lower_bound
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (O : Set X) (hO : IsOpen O) (hOU : closure O ⊆ d.quotientDomain)
    (A : Set Y) {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδfin : δ ≠ ∞)
    (hsep : ∀a ∈ A, ∀b ∉ π ⁻¹' O, δ ≤ edist a b)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hstart : γ.val ⊥ ∈ O) (hend : γ.val ⊤ ∉ O)
    (hA : (d.domainEquiv.symm ⟨γ.val ⊥, hOU (subset_closure hstart)⟩).val ∈ A)
    (m : X → ℝ≥0∞) :
    1 ≤ physicalTollCost d ((π ⁻¹' O).indicator (fun _ => δ⁻¹)) m γ := by
  let t := firstExitTime γ.val O
  have ht : (⊥ : PathTime) < t := firstExit_pos γ.val hO hstart hend
  let ρ := affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ ht
  have hρU (s : PathTime) : ρ.val s ∈ d.quotientDomain := by
    apply hOU
    apply firstExit_initial_segment γ.val hO hstart hend
    exact (affinePathTime_mem_Icc ht.le s).2
  let β := fullDomainPhysicalLift d hU ρ hρU
  have hproject (s : PathTime) : π (β.val s) = ρ.val s :=
    fullDomainPhysicalLift_projects d hU ρ hρU π he s
  have hβA : β.val ⊥ ∈ A := by
    simpa only [β, fullDomainPhysicalLift_value, ρ, affineFinitePhysicalPath,
      affineRestrictedPath, ContinuousMap.comp_apply, affinePathTime_zero] using hA
  have hβout : β.val ⊤ ∉ π ⁻¹' O := by
    change π (β.val ⊤) ∉ O
    rw [hproject]
    change γ.val (affinePathTime ⊥ t ⊤) ∉ O
    rw [affinePathTime_one]
    exact firstExit_notMem γ.val hO hend
  have hβin (s : PathTime) (hs : s < ⊤) : β.val s ∈ π ⁻¹' O := by
    change π (β.val s) ∈ O
    rw [hproject]
    apply mem_before_firstExit γ.val O
    have h := affinePathTime_strictMono ht hs
    rwa [affinePathTime_one] at h
  let h : Y → ℝ≥0∞ := (π ⁻¹' O).indicator (fun _ => δ⁻¹)
  have hh : Measurable h := measurable_const.indicator (hO.preimage hπ).measurableSet
  have hpay : 1 ≤ ∫⁻y, h y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ := by
    rw [dyadicPhysicalOccupation_fullDomainLift d hU ρ hρU]
    exact indicator_occupation_pays_endpoint_distance β _ (hO.preimage hπ).measurableSet
      hβin hδ hδfin (hsep _ hβA _ hβout)
  have hfull : 1 ≤ physicalTollCost d h m ρ := hpay.trans le_self_add
  exact hfull.trans (physicalTollCost_affine_le d hU γ ht h hh m)

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
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarArcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
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
-- module Solutions.Q146_CD.CircleDomains_Probability_PublishedMeasureDuality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measure-family duality and probability lifting.

* Ambrosio–Di Marino–Savaré, JEMS 17 (2015), 1817–1853,
  DOI 10.4171/JEMS/546, Theorem 5.1 (p. 1830), Corollary 5.2(b)
  (p. 1833): positive modulus of a Suslin image yields a probability
  plan on finite measures with an L² barycenter. `MeasureImageDuality`
  is the p = 2 consequence for a Borel image of a standard Borel space.
* Bogachev, *Measure Theory*, vol. II (2007), Theorem 6.9.1 gives a
  measure-dependent measurable selector. `MeasurePlanLifting` states
  its probability-lifting consequence, used in the proof of ADMS,
  Theorem 7.2, p. 1839.

The two propositions separate measure-space duality from probability
lifting; neither assumes a compact-support conclusion.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable (A Z : Type*) [MeasurableSpace A] [StandardBorelSpace A]
  [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]

theorem indexed_measure_duality (hdual : MeasureImageDuality A Z)
    (hlift : MeasurePlanLifting A Z) (K : A → FiniteMeasure Z) (hK : Measurable K)
    (σ : Measure Z) [IsFiniteMeasure σ] (c : ℝ≥0) (hc : 0 < c)
    (hmod : (c : ℝ≥0∞) < measureFamilyModulus A Z σ K) :
    ∃ (P : ProbabilityMeasure A) (q : Z → ℝ≥0∞), Measurable q ∧
      (∀ E, MeasurableSet E →
        (∫⁻ a, (K a : Measure Z) E ∂(P : Measure A)) = σ.withDensity q E) ∧
      (∫⁻ z, q z ^ 2 ∂σ) ≤ (c : ℝ≥0∞)⁻¹ := by
  obtain ⟨η, q, hq, hrange, hbar, henergy⟩ := hdual K hK σ inferInstance c hc hmod
  obtain ⟨P, hP⟩ := hlift K hK η hrange
  refine ⟨P, q, hq, ?_, henergy⟩
  intro E hE
  have hev : Measurable (fun v : FiniteMeasure Z => (v : Measure Z) E) :=
    (Measure.measurable_coe hE).comp measurable_subtype_coe
  have hb := hbar E hE
  rw [← hP, ProbabilityMeasure.toMeasure_map, lintegral_map hev hK] at hb
  exact hb

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

theorem measurable_finiteCodeMeasure (d : PathCodeData X Y) (p : D → X)
    (c : D → ℝ≥0∞) (hU : IsOpen d.quotientDomain) :
    Measurable (finiteCodeMeasure d p c) :=
  ((measurable_pathCostMeasure d hU p c).comp measurable_subtype_coe).subtype_mk

theorem measurable_constrainedCodeMeasure (d : PathCodeData X Y) (p : D → X)
    (c : D → ℝ≥0∞) (ν : Measure X) (hU : IsOpen d.quotientDomain) :
    Measurable (constrainedCodeMeasure d p c ν) :=
  (measurable_finiteCodeMeasure d p c hU).comp measurable_subtype_coe

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ConstrainedCodeLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Forgetting the constrained finite-code subtype produces an actual law
on base paths, retaining the residual nullity and finite-cost properties. -/

open Set MeasureTheory Filter
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
theorem constrainedCodeLaw_residual_null (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X) [SFinite ν]
    (hB : IsClosed d.dust) (P : ProbabilityMeasure (ConstrainedCostCode d p c ν)) :
    ∀ᵐ Γ ∂(constrainedCodeLaw d p c ν P : Measure (BasePathCode d)),
      ν (residualImage d.dust Γ.val) = 0 := by
  apply (ae_map_iff (measurable_constrainedCodeToBase d p c ν).aemeasurable
    ((measurableSet_residualImageMass_zero hB ν).preimage measurable_subtype_coe)).mpr
  exact Eventually.of_forall fun Γ => Γ.property

theorem constrainedCodeLaw_finite (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X)
    (P : ProbabilityMeasure (ConstrainedCostCode d p c ν)) :
    ∀ᵐ Γ ∂(constrainedCodeLaw d p c ν P : Measure (BasePathCode d)),
      pathCostMeasure d p c Γ univ < ∞ := by
  apply (ae_map_iff (measurable_constrainedCodeToBase d p c ν).aemeasurable
    (measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp
      (measurable_pathCostMeasure d hU p c)) measurable_const)).mpr
  exact Eventually.of_forall fun Γ => Γ.val.property

theorem mean_constrainedCodeLaw (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X)
    (P : ProbabilityMeasure (ConstrainedCostCode d p c ν)) {A : Set (PathCostSpace Y D)}
    (hA : MeasurableSet A) :
    meanCodeCost d p c (constrainedCodeLaw d p c ν P) A =
      ∫⁻ Γ, (constrainedCodeMeasure d p c ν Γ : Measure (PathCostSpace Y D)) A
        ∂(P : Measure (ConstrainedCostCode d p c ν)) := by
  rw [meanCodeCost_apply d hU p c _ hA]
  exact lintegral_map ((Measure.measurable_coe hA).comp
    (measurable_pathCostMeasure d hU p c)) (measurable_constrainedCodeToBase d p c ν)

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

theorem level_section_null_of_unique (H : ℕ → Set (UnitAddCircle × X)) (x : X)
    (hunique : ∀ i t u, (t, x) ∈ H i → (u, x) ∈ H i → t = u) (i : ℕ) :
    volume {t : UnitAddCircle | (t, x) ∈ H i} = 0 := by
  have hs : ({t : UnitAddCircle | (t, x) ∈ H i}).Subsingleton := by
    intro t ht u hu
    exact hunique i t u ht hu
  let : NullSingletonClass (volume : Measure UnitAddCircle) :=
    ⟨unitAddCircle_volume_singleton⟩
  exact hs.countable.measure_zero volume

variable [MeasurableSpace X]

theorem ae_free_level_sections (H : ℕ → Set (UnitAddCircle × X)) (B flags : Set X)
    (ν : Measure X) [NullSingletonClass ν] (hflags : flags.Countable) (hB : ν Bᶜ = 0)
    (hunique : ∀ x ∈ B \ flags, ∀ i t u, (t, x) ∈ H i → (u, x) ∈ H i → t = u) :
    ∀ᵐ x ∂ν, x ∈ B ∧ ∀ i, volume {t : UnitAddCircle | (t, x) ∈ H i} = 0 := by
  have hmem : ∀ᵐ x ∂ν, x ∈ B := by
    rw [ae_iff]
    change ν Bᶜ = 0
    exact hB
  have hnot : ∀ᵐ x ∂ν, x ∉ flags :=
    (measure_eq_zero_iff_ae_notMem).mp (hflags.measure_zero ν)
  filter_upwards [hmem, hnot] with x hx hxflags
  exact ⟨hx, level_section_null_of_unique H x (hunique x ⟨hx, hxflags⟩)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CodeModulusExtraction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measure-family duality and probability lifting produce a law on the
constrained codes from a positive modulus bound. -/

open Set MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

variable [PolishSpace Y] [PolishSpace D]

theorem positive_modulus_code_law (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X) [SFinite ν]
    [StandardBorelSpace (ConstrainedCostCode d p c ν)]
    (μ : Measure Y) [IsFiniteMeasure μ] (τ : Measure LevelTuple) [IsFiniteMeasure τ]
    (hc : (∑' s, c s ^ 2) < ∞)
    (hdual : MeasureImageDuality (ConstrainedCostCode d p c ν) (PathCostSpace Y D))
    (hlift : MeasurePlanLifting (ConstrainedCostCode d p c ν) (PathCostSpace Y D))
    (r : ℝ≥0) (hr : 0 < r)
    (hmod : (r : ℝ≥0∞) < measureFamilyModulus (ConstrainedCostCode d p c ν)
      (PathCostSpace Y D) (pathCostReference μ c τ) (constrainedCodeMeasure d p c ν)) :
    ∃ (P : ProbabilityMeasure (BasePathCode d)) (q : PathCostSpace Y D → ℝ≥0∞),
      Measurable q ∧
      meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q ∧
      (∫⁻ z, q z ^ 2 ∂pathCostReference μ c τ) ≤ (r : ℝ≥0∞)⁻¹ ∧
      (∀ᵐ Γ ∂(P : Measure (BasePathCode d)), pathCostMeasure d p c Γ univ < ∞) ∧
      (∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0) := by
  let : IsFiniteMeasure (pathCostReference μ c τ) := finite_pathCostReference μ c hc τ
  obtain ⟨P, q, hq, hbar, he⟩ := indexed_measure_duality _ _ hdual hlift
    (constrainedCodeMeasure d p c ν) (measurable_constrainedCodeMeasure d p c ν hU)
    (pathCostReference μ c τ) r hr hmod
  refine ⟨constrainedCodeLaw d p c ν P, q, hq, ?_, he,
    constrainedCodeLaw_finite d hU p c ν P, constrainedCodeLaw_residual_null d p c ν hB P⟩
  ext E hE
  rw [mean_constrainedCodeLaw d hU p c ν P hE]
  exact hbar E hE

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
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawCandidateConsequences
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unpack the fused candidate's quantitative estimates and slot laws. -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem countableSquareLawBounds_visit_norm (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (a : S → X) {C : ℝ≥0∞}
    (h : CountableSquareLawBounds (codeVisitWeight d a) (C ^ 2) P) :
    countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤ C := by
  have hs : (∑' s, meanVisitCount (codePathLaw d P) (a s) ^ 2) ≤ C ^ 2 := by
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    simpa only [meanVisitCount_codePathLaw_eq_integral] using h F
  calc
    _ ≤ (C ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hs (by norm_num)
    _ = C := by rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num

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

theorem exists_countable_enumeration_with_default {I A : Type*} [Countable I]
    (f : I → A) (a₀ : A) :
    ∃ g : ℕ → A, (∀ i, ∃ n, g n = f i) ∧ ∀ n, g n = a₀ ∨ ∃ i, g n = f i := by
  let := Encodable.ofCountable I
  let g (n : ℕ) : A := (Encodable.decode (α := I) n).elim a₀ f
  refine ⟨g, ?_, ?_⟩
  · intro i
    exact ⟨Encodable.encode i, by simp [g]⟩
  · intro n
    cases h : Encodable.decode (α := I) n with
    | none => exact Or.inl (by simp [g, h])
    | some i => exact Or.inr ⟨i, by simp [g, h]⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ResidualTailNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite deletion constraints exclude residual incidences off the support
of the toll whenever the actual full path toll is finite. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem tendsto_deleted_series_zero {A : Type*} [Countable A]
    (f : A → ℝ≥0∞) (hf : (∑' a, f a) ≠ ∞) (P : ℕ → Set A)
    (hP : ∀ a, ∀ᶠ n in atTop, a ∈ P n) :
    Tendsto (fun n => ∑' a, if a ∈ P n then 0 else f a) atTop (𝓝 0) := by
  let : MeasurableSpace A := ⊤
  have h := tendsto_lintegral_of_dominated_convergence (μ := Measure.count)
    (F := fun n a => if a ∈ P n then 0 else f a) (f := fun _ => 0) f
    (fun _ => measurable_of_countable _)
    (fun n => Eventually.of_forall fun a => by
      change (if a ∈ P n then 0 else f a) ≤ f a
      split_ifs <;> simp)
    (by simpa only [lintegral_count] using hf)
    (Eventually.of_forall fun a => tendsto_const_nhds.congr' ((hP a).mono fun n hn => by simp [hn]))
  simpa only [lintegral_count, tsum_zero] using h

variable {X : Type*} [MetricSpace X]

theorem residualVisitCount_le_visitCount (B : Set X) (I : Set PathTime)
    (Γ : TaggedPath X) (x : X) : residualVisitCount B I Γ x ≤ visitCount Γ.1 x := by
  rw [residualVisitCount, timeCount, visitCount_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro t
  by_cases h : (Γ.1 t = x)
  · simp only [h, ite_true, if_true]
    split_ifs <;> simp
  · have hn : ((Γ, x), t) ∉ residualVisitRelation B I := fun hh => h hh.2.2
    simp only [h, hn, ite_false, if_false, le_refl]

theorem residualToll_deleted_le (B : Set X) (I : Set PathTime)
    (m : X → ℝ≥0∞) (P : Set X) (Γ : TaggedPath X) :
    residualToll B I (deletedWeight P m) Γ ≤
      ∑' x : support m, if x.val ∈ P then 0 else m x.val * visitCount Γ.1 x.val := by
  rw [residualToll_eq_visits]
  have he : (∑' x, deletedWeight P m x * residualVisitCount B I Γ x) =
      ∑' x : support m, deletedWeight P m x.val * residualVisitCount B I Γ x.val := by
    symm
    apply tsum_subtype_eq_of_support_subset
      (f := fun x : X => deletedWeight P m x * residualVisitCount B I Γ x)
    intro x hx
    by_contra hn
    have hz : m x = 0 := notMem_support.mp hn
    simp [deletedWeight, hz] at hx
  rw [he]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x.val ∈ P
  · simp [deletedWeight, hx]
  · simpa only [deletedWeight, hx, ite_false, if_false] using
      mul_le_mul' (le_refl (m x.val)) (residualVisitCount_le_visitCount B I Γ x.val)

theorem residual_incidence_envelope_null {Z : Type*} [MeasurableSpace Z]
    (B : Set X) (I : Set PathTime) (R : Set (Z × X)) (ν : Measure Z)
    (m : X → ℝ≥0∞) (hm : (support m).Countable) (P : ℕ → Set X)
    (hcover : ∀ x ∈ support m, ∀ᶠ n in atTop, x ∈ P n)
    (Γ : TaggedPath X) (hfinite : boundaryToll Γ.1 m < ∞)
    (hbound : ∀ n, ResidualIncidenceBound B I R (P n) ν m Γ) :
    ν (⋂ n, {z | (Γ, z) ∈ residualIncidence B I R (P n)}) = 0 := by
  let : Countable (support m) := hm.to_subtype
  have ht := tendsto_deleted_series_zero
    (fun x : support m => m x.val * visitCount Γ.1 x.val)
    (by simpa only [← boundaryToll_eq_support] using hfinite.ne)
    (fun n => {x : support m | x.val ∈ P n})
    (fun x => hcover x.val x.property)
  apply le_antisymm _ bot_le
  apply ge_of_tendsto ht
  apply Eventually.of_forall
  intro n
  exact (measure_mono (iInter_subset _ n)).trans
    ((hbound n).trans (residualToll_deleted_le B I m (P n) Γ))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SquareVisitTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square bounds on weights and mean visits give finite actual weighted
tolls almost surely. This retains all visits, including both endpoints. -/

open Set Filter Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem tsum_mul_le_countingSquareNorm {A : Type*} [Countable A]
    (a b : A → ℝ≥0∞) :
    (∑' x, a x * b x) ≤ countingSquareNorm a * countingSquareNorm b := by
  let : MeasurableSpace A := ⊤
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := Measure.count)
    (p := (2 : ℝ)) (q := (2 : ℝ)) (by constructor <;> norm_num)
    (measurable_of_countable a).aemeasurable (measurable_of_countable b).aemeasurable
  simpa only [Pi.mul_apply, ENNReal.rpow_two, lintegral_count, countingSquareNorm] using h

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem lintegral_boundaryToll_le_square_norms (μ : ProbabilityMeasure C(PathTime, X))
    (m : X → ℝ≥0∞) (hm : (support m).Countable) :
    (∫⁻ γ, boundaryToll γ m ∂(μ : Measure _)) ≤
      countingSquareNorm (fun x : support m => m x.val) *
      countingSquareNorm (fun x : support m => meanVisitCount μ x.val) := by
  let : Countable (support m) := hm.to_subtype
  rw [lintegral_boundaryToll μ hm]
  exact tsum_mul_le_countingSquareNorm _ _

theorem ae_boundaryToll_finite (μ : ProbabilityMeasure C(PathTime, X))
    (m : X → ℝ≥0∞) (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞) :
    ∀ᵐ γ ∂(μ : Measure _), boundaryToll γ m < ∞ := by
  apply ae_lt_top (measurable_boundaryToll hm)
  exact ((lintegral_boundaryToll_le_square_norms μ m hm).trans_lt
    (ENNReal.mul_lt_top hweight hvisits)).ne

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CodeResidualAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The stored rational-interval constraints give null residual-incidence
envelopes under the actual square bounds on visits. -/

open Set Filter Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

private theorem rationalStart_eq : rationalStart.toTime = (⊥ : PathTime) := by
  apply Subtype.ext
  norm_num [rationalStart, RationalPathTime.toTime]

private theorem rationalEnd_eq : rationalEnd.toTime = (⊤ : PathTime) := by
  apply Subtype.ext
  norm_num [rationalEnd, RationalPathTime.toTime]

theorem baseCode_prior_bound (d : PathCodeData X Y) (Γ : BasePathCode d) (i n : ℕ) :
    ResidualIncidenceBound d.dust univ pathHitSet (d.priorDeletions i n)
      (d.priorLaws i) (priorHitMass (d.priorLaws i)) Γ.val := by
  have h := Γ.property.1.2.2.1 i n rationalStart rationalEnd
  simpa only [rationalStart_eq, rationalEnd_eq, Icc_bot_top] using h

theorem baseCode_level_bound (d : PathCodeData X Y) (Γ : BasePathCode d) (i n : ℕ) :
    ResidualIncidenceBound d.dust univ (d.levels i) (d.flagDeletions n)
      volume (d.levelWeights i) Γ.val := by
  have h := Γ.property.1.2.2.2.1 i n rationalStart rationalEnd
  simpa only [rationalStart_eq, rationalEnd_eq, Icc_bot_top] using h

variable [BorelSpace X] [SecondCountableTopology X] [BorelSpace C(PathTime, X)]

theorem ae_code_boundaryToll_finite (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (m : X → ℝ≥0∞)
    (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support m => meanVisitCount (codePathLaw d P) x.val) < ∞) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), boundaryToll Γ.val.1 m < ∞ := by
  have h := ae_boundaryToll_finite (codePathLaw d P) m hm hweight hvisits
  exact (ae_map_iff (measurable_codePath d).aemeasurable
    (measurableSet_lt (measurable_boundaryToll hm) measurable_const)).mp h

theorem ae_code_level_envelope_null (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (i : ℕ)
    (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ x ∈ support (d.levelWeights i),
      ∀ᶠ n in atTop, x ∈ d.flagDeletions n) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), volume
      (⋂ n, {t | (Γ.val, t) ∈ residualIncidence d.dust univ (d.levels i)
        (d.flagDeletions n)}) = 0 := by
  filter_upwards [ae_code_boundaryToll_finite d P _ hm hweight hvisits] with Γ hΓ
  exact residual_incidence_envelope_null d.dust univ (d.levels i) _ _ hm _ hcover
    Γ.val hΓ (baseCode_level_bound d Γ i)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ResidualProductAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel envelopes allow Tonelli to remove diffuse residual contacts
without assuming that an uncountable incidence projection is Borel. -/

open Set Filter Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [TopologicalSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z]

theorem ae_no_residual_incidence_of_null_envelopes
    (d : PathCodeData X Y) (hB : IsClosed d.dust)
    (R : Set (Z × X)) (hR : IsClosed R)
    (P : ProbabilityMeasure (BasePathCode d)) (ν : Measure Z) [SFinite ν]
    (F : ℕ → Finset X) (S : Set X) (hFS : ∀ n, (F n : Set X) ⊆ S)
    (hnull : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      ν (⋂ n, {z | (Γ.val, z) ∈ residualIncidence d.dust univ R (F n)}) = 0) :
    ∀ᵐ q ∂((P : Measure (BasePathCode d)).prod ν),
      ∀ t ∈ residualTimes d.dust q.1.val, (q.2, q.1.val.1 t) ∈ R → q.1.val.1 t ∈ S := by
  let E : Set (BasePathCode d × Z) :=
    ⋂ n, {q | (q.1.val, q.2) ∈ residualIncidence d.dust univ R (F n)}
  have hE : MeasurableSet E := by
    apply MeasurableSet.iInter
    intro n
    exact (measurableSet_residualIncidence hB isClosed_univ hR (F n).finite_toSet).preimage
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  have hzero : ((P : Measure (BasePathCode d)).prod ν) E = 0 := by
    rw [Measure.prod_apply hE]
    calc
      _ = ∫⁻ _Γ, (0 : ℝ≥0∞) ∂(P : Measure (BasePathCode d)) := by
        apply lintegral_congr_ae
        filter_upwards [hnull] with Γ hΓ
        simpa only [E, preimage_iInter, preimage_ofPred_eq, Prod.mk.injEq] using hΓ
      _ = 0 := by simp
  have hae : ∀ᵐ q ∂((P : Measure (BasePathCode d)).prod ν), q ∉ E := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using hzero
  filter_upwards [hae] with q hq
  intro t ht hR
  by_contra hS
  apply hq
  apply mem_iInter.mpr
  intro n
  exact ⟨t, ht, mem_univ t, hR, fun h => hS (hFS n h)⟩

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

theorem residualToll_dust_restriction {X : Type*} [MetricSpace X]
    (B I : Set X) (J : Set PathTime) (m : X → ℝ≥0∞) (Γ : TaggedPath X) :
    residualToll B J (deletedWeight I (fun x => if x ∈ B then m x else 0)) Γ =
      residualToll B J (deletedWeight I m) Γ := by
  apply tsum_congr
  intro t
  by_cases ht : t ∈ residualTimes B Γ ∧ t ∈ J
  · have hb : Γ.1 t ∈ B := ht.1.1
    simp only [ht, ite_true, if_true, deletedWeight, hb]
  · simp only [ht, ite_false, if_false]

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_code_dust_prior_envelope_null (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (i : ℕ)
    (hm : (support (dustPriorHitMass d.dust (d.priorLaws i))).Countable)
    (hweight : countingSquareNorm (fun x : support (dustPriorHitMass d.dust (d.priorLaws i)) =>
      dustPriorHitMass d.dust (d.priorLaws i) x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (dustPriorHitMass d.dust (d.priorLaws i)) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ x ∈ support (dustPriorHitMass d.dust (d.priorLaws i)),
      ∀ᶠ n in atTop, x ∈ d.priorDeletions i n) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), (d.priorLaws i)
      (⋂ n, {η | (Γ.val, η) ∈ residualIncidence d.dust univ pathHitSet
        (d.priorDeletions i n)}) = 0 := by
  filter_upwards [ae_code_boundaryToll_finite d P _ hm hweight hvisits] with Γ hΓ
  apply residual_incidence_envelope_null d.dust univ pathHitSet _ _ hm _ hcover Γ.val hΓ
  intro n
  change _ ≤ residualToll d.dust univ
    (deletedWeight (d.priorDeletions i n)
      (fun x => if x ∈ d.dust then priorHitMass (d.priorLaws i) x else 0)) Γ.val
  rw [residualToll_dust_restriction]
  exact baseCode_prior_bound d Γ i n

theorem ae_later_residual_contact_in_prior_support_of_dust_bounds
    (d e : PathCodeData X Y) (hB : IsClosed e.dust)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    (i : ℕ) (hprior : e.priorLaws i = (codePathLaw d P : Measure C(PathTime, X)))
    (hm : (support (dustPriorHitMass e.dust (e.priorLaws i))).Countable)
    (hweight : countingSquareNorm (fun x : support (dustPriorHitMass e.dust (e.priorLaws i)) =>
      dustPriorHitMass e.dust (e.priorLaws i) x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (dustPriorHitMass e.dust (e.priorLaws i)) =>
      meanVisitCount (codePathLaw e Q) x.val) < ∞)
    (hcover : ∀ x ∈ support (dustPriorHitMass e.dust (e.priorLaws i)),
      ∀ᶠ n in atTop, x ∈ e.priorDeletions i n)
    (hsub : ∀ n, (e.priorDeletions i n : Set X) ⊆ support (priorHitMass (e.priorLaws i))) :
    ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      ∀ t ∈ residualTimes e.dust p.2.val, p.2.val.1 t ∈ range p.1.val.1 →
        p.2.val.1 t ∈ support (priorHitMass (e.priorLaws i)) := by
  let : SFinite (e.priorLaws i) := by rw [hprior]; infer_instance
  have hb := ae_no_residual_incidence_of_null_envelopes e hB pathHitSet isClosed_pathHitSet
    Q (e.priorLaws i) (e.priorDeletions i) (support (priorHitMass (e.priorLaws i))) hsub
    (ae_code_dust_prior_envelope_null e Q i hm hweight hvisits hcover)
  have hb' : ∀ᵐ q ∂((Q : Measure (BasePathCode e)).prod
      (codePathLaw d P : Measure C(PathTime, X))),
      ∀ t ∈ residualTimes e.dust q.1.val, (q.2, q.1.val.1 t) ∈ pathHitSet →
        q.1.val.1 t ∈ support (priorHitMass (e.priorLaws i)) := by
    simpa only [hprior] using hb
  have hpath : MeasurePreserving (codePath d) (P : Measure (BasePathCode d))
      (codePathLaw d P : Measure C(PathTime, X)) := ⟨measurable_codePath d, rfl⟩
  exact (Measure.measurePreserving_swap.comp
    (hpath.prod (MeasurePreserving.id (Q : Measure (BasePathCode e))))).quasiMeasurePreserving.ae hb'

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FiniteHitSquareEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite dust hit tests imply the full square sum needed for shrinking
collars, with no enlargement of the constant. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace X] [BorelSpace C(PathTime, X)] in
theorem pathHit_square_tsum_le (μ : ProbabilityMeasure C(PathTime, X))
    (B : Set X) (C : ℝ)
    (hfinite : ∀ F : Finset B, ∑ x ∈ F, pathHitReal μ x.val ^ 2 ≤ C ^ 2) :
    (∑' x : B, pathHitProbability μ x.val ^ 2) ≤ ENNReal.ofReal (C ^ 2) := by
  apply ENNReal.summable.tsum_le_of_sum_le
  intro F
  have he : (∑ x ∈ F, pathHitProbability μ x.val ^ 2) =
      ENNReal.ofReal (∑ x ∈ F, pathHitReal μ x.val ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro x hx
    rw [ENNReal.ofReal_pow (pathHitReal_nonneg μ x.val), pathHitReal,
      ENNReal.ofReal_toReal (ne_of_lt ((pathHitProbability_le_one μ x.val).trans_lt (by simp)))]
  rw [he]
  exact ENNReal.ofReal_le_ofReal (hfinite F)

theorem codeHit_square_tsum_le (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (C : ℝ)
    (hfinite : ∀ F : Finset d.dust,
      ∑ x ∈ F, pathHitReal (codePathLaw d P) x.val ^ 2 ≤ C ^ 2) :
    (∑' x : d.dust, codeHitProbability d P x.val ^ 2) ≤ ENNReal.ofReal (C ^ 2) := by
  simpa only [pathHitProbability_codePathLaw] using
    pathHit_square_tsum_le (codePathLaw d P) d.dust C hfinite

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DustPriorBudgets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The candidate's prescribed-mark budget supplies exactly the dust
visit norms used by the prior-contact argument. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace Y] [BorelSpace Y] [BorelSpace X] [SecondCountableTopology X] in
theorem priorHitMass_codePathLaw (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (x : X) :
    priorHitMass (codePathLaw d P : Measure C(PathTime, X)) x = codeHitProbability d P x :=
  pathHitProbability_codePathLaw d P x

omit [MeasurableSpace Y] [BorelSpace Y] [BorelSpace X] [SecondCountableTopology X] in
theorem dust_prior_weight_norm_finite (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (B : Set X)
    (hhit : (∑' x : B, codeHitProbability d P x.val ^ 2) < ∞) :
    countingSquareNorm (fun x : support (dustPriorHitMass B (codePathLaw d P : Measure _)) =>
      dustPriorHitMass B (codePathLaw d P : Measure _) x.val) < ∞ := by
  let M := support (dustPriorHitMass B (codePathLaw d P : Measure C(PathTime, X)))
  have hMB (x : M) : x.val ∈ B := by
    have hx : x.val ∈ support (dustPriorHitMass B (codePathLaw d P : Measure _)) := x.property
    rw [support_dustPriorHitMass] at hx
    exact hx.1
  let f : M → B := fun x => ⟨x.val, hMB x⟩
  have hf : Injective f := fun _ _ h => Subtype.ext (congrArg (fun x : B => x.val) h)
  have he : (fun x : M => dustPriorHitMass B (codePathLaw d P : Measure _) x.val) =
      (fun x : B => codeHitProbability d P x.val) ∘ f := by
    funext x
    have hx : x.val ∈ B := hMB x
    simp only [dustPriorHitMass, hx, ite_true, if_true, priorHitMass_codePathLaw, comp_apply, f]
  rw [he]
  apply (countingSquareNorm_comp_injective _ f hf).trans_lt
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hhit.ne

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem candidate_visit_norm_on_marks (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (M T : Set X) (hTM : T ⊆ M)
    {C : ℝ≥0∞}
    (hb : CountableSquareLawBounds (codeVisitWeight d (fun x : M => x.val)) (C ^ 2) P) :
    countingSquareNorm (fun x : T => meanVisitCount (codePathLaw d P) x.val) ≤ C := by
  have hsub : range (fun x : T => x.val) ⊆ range (fun x : M => x.val) := by
    rintro x ⟨t, rfl⟩
    exact ⟨⟨t.val, hTM t.property⟩, rfl⟩
  exact (countingSquareNorm_restrict_range (meanVisitCount (codePathLaw d P))
    (fun x : T => x.val) (fun x : M => x.val) Subtype.val_injective hsub).trans
      (countableSquareLawBounds_visit_norm d P (fun x : M => x.val) hb)

theorem PriorLawPresentation.prior_visit_norm_finite
    {B S : Set X} {μ : ℕ → Measure C(PathTime, X)} (R : PriorLawPresentation B S μ)
    (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (σ : Measure Y) (τ : Measure LevelTuple) (M N E C : ℝ≥0∞) (hC : C < ∞)
    (hb : CodeLawCandidate d (fun x : R.marks => x.val) σ τ M N E (C ^ 2) P) (i : ℕ) :
    countingSquareNorm (fun x : support (dustPriorHitMass B (μ i)) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞ :=
  (candidate_visit_norm_on_marks d P R.marks _ (R.prior_marks i) hb.2.1).trans_lt hC

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MarkedHitLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureConfigurationMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureMeanConfigurationMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
-- module Solutions.Q146_CD.CircleDomains_Modulus_UngatedBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choosing both gate target sets to be the whole sphere forces the
perturbation region to be empty. Thus the controlled norm is the global
norm required for the ungated barrier selection. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace CompatibleRealBarrier
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {previous : ℕ → PhysicalRealCoordinate d π} {flags EStar : Set Sphere}
  {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere}

theorem penalty_eq_empty_of_univ
    (R : CompatibleRealBarrier d π previous flags EStar regions f univ) : R.penalty = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact R.penalty_avoids ⟨x, R.penalty_inside (subset_closure hx)⟩
    (subset_closure hx) (mem_univ _)

theorem controlledSize_of_univ
    (R : CompatibleRealBarrier d π previous flags EStar regions f univ) :
    R.controlledSize = ENNReal.ofReal (Real.sqrt (∫ x in FiniteTransfer.realChartDomain d.physicalDomain,
      FiniteTransfer.gradientEnergy R.coordinate.physical
        (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x)) +
      countingSquareNorm R.weight := by
  simp only [controlledSize, R.penalty_eq_empty_of_univ, preimage_empty, sdiff_empty]

end CompatibleRealBarrier
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBarrierTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
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

theorem size_of_barrier {previous : ℕ → PhysicalRealCoordinate d π} {flags : Set Sphere}
    {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere}
    (R : CompatibleRealBarrier d π previous flags EStar regions f univ)
    (hopen : IsOpen (regions R.level)) : (of_barrier R hopen).size = R.controlledSize :=
  R.controlledSize_of_univ.symm

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

theorem of_barrier_compatible
    {previous : ℕ → PhysicalRealCoordinate d π} {flags : Set Sphere}
    {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere}
    (R : CompatibleRealBarrier d π previous flags EStar regions f univ)
    (hopen : IsOpen (regions R.level)) (A : Set (UngatedRealTest d π EStar))
    (labels : UngatedRealTest d π EStar → ℕ)
    (hflags : ∀ c ∈ A, c.exclusions ∩ d.dust ⊆ flags)
    (hQ : ∀ c ∈ A, c.coordinate.quotient = (previous (labels c)).quotient) :
    (of_barrier R hopen).CompatibleWith A := by
  refine ⟨fun c hc => (hflags c hc).trans R.prior_flags, ?_⟩
  intro n q hq
  change (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
    (freeComponentFailure (d.dust \ R.exclusions)
      (circleBandGraph d.quotientDomain R.coordinate.quotient)
      (fun i : Fin n => circleBandGraph d.quotientDomain (q i).coordinate.quotient) id) = 0
  rw [freeComponentFailure_congr_selected (d.dust \ R.exclusions)
    (circleBandGraph d.quotientDomain R.coordinate.quotient)
    (fun i : Fin n => circleBandGraph d.quotientDomain (q i).coordinate.quotient)
    (fun i => circleBandGraph d.quotientDomain (previous i).quotient) id (labels ∘ q)
    (fun i => by simp only [id_eq, Function.comp_apply, hQ (q i) (hq i)])]
  exact R.finite_compatibility n (labels ∘ q)

end UngatedRealTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TorusProjection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection onto any distinct selection of finite circle coordinates
preserves normalized Haar measure. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem torus_projection_measurePreserving {I J : Type*} [Fintype I] [Fintype J]
    (e : J → I) (he : Injective e) :
    MeasurePreserving (fun θ : I → UnitAddCircle => θ ∘ e) volume volume := by
  let f : (I → UnitAddCircle) →+ (J → UnitAddCircle) :=
    { toFun := fun θ => θ ∘ e
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hsurj : Surjective f := by
    intro θ
    refine ⟨Function.extend e θ (fun _ => 0), ?_⟩
    funext j
    exact he.extend_apply θ (fun _ => 0) j
  apply AddMonoidHom.measurePreserving (f := f)
    (by exact continuous_pi fun j => continuous_apply (e j)) hsurj
  change (Measure.pi (fun _ : I => (volume : Measure UnitAddCircle))) univ =
    (Measure.pi (fun _ : J => (volume : Measure UnitAddCircle))) univ
  simp [Measure.pi_univ, AddCircle.measure_univ]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteTupleCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered compatibility null sets survive arbitrary finite selections
of a prior tuple, including tuples with repeated labels. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

variable {X : Type*} [TopologicalSpace X]

theorem ae_finite_tuple_ordered_compatibility
    (H : ℕ → Set (UnitAddCircle × X)) (F : Set X)
    (hP : OrderedLevelNullCompatibility H F) {n m : ℕ}
    (l : Fin n → ℕ) (r : Fin m → ℕ) :
    ∀ᵐ p ∂((volume : Measure (Fin n → UnitAddCircle)).prod
      (volume : Measure (Fin m → UnitAddCircle))),
      ∀ j : Fin m, ∀ A : Finset (Fin n), (∀ k ∈ A, l k < r j) →
        ∀ x ∈ F, (p.2 j, x) ∈ H (r j) →
          ¬ (connectedComponentIn (⋃ k ∈ A, {y | (p.1 k, y) ∈ H (l k)}) x).Nontrivial := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro A
  by_cases horder : ∀ k ∈ A, l k < r j
  · let e : Fin (Fintype.card A) → Fin n := fun k => ((Fintype.equivFin A).symm k).val
    have he : Injective e := Subtype.val_injective.comp (Fintype.equivFin A).symm.injective
    have hp := hP (r j) (Fintype.card A) (l ∘ e) (fun k =>
      horder (e k) ((Fintype.equivFin A).symm k).property)
    have hproj : MeasurePreserving
        (fun p : (Fin n → UnitAddCircle) × (Fin m → UnitAddCircle) => (p.2 j, p.1 ∘ e))
        (volume.prod volume) (volume.prod volume) := by
      exact Measure.measurePreserving_swap.comp
        ((torus_projection_measurePreserving e he).prod
          (measurePreserving_eval (fun _ : Fin m => (volume : Measure UnitAddCircle)) j))
    have hzero := hproj.quasiMeasurePreserving.preimage_null hp
    have hgood : ∀ᵐ p ∂((volume : Measure (Fin n → UnitAddCircle)).prod
        (volume : Measure (Fin m → UnitAddCircle))),
        (p.2 j, p.1 ∘ e) ∉ freeComponentFailure F (levelRelation H (r j))
          (levelRelation H) (l ∘ e) := by
      rw [ae_iff]
      simpa only [Set.preimage, not_not, ofPred_mem_eq] using hzero
    filter_upwards [hgood] with p hp
    intro _ x hx hj hnt
    apply hp
    have hset : {y | (y, p.1 ∘ e) ∈ finiteLevelUnionGraph (levelRelation H) (l ∘ e)} =
        ⋃ k ∈ A, {y | (p.1 k, y) ∈ H (l k)} := by
      ext y
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := mem_iUnion.mp hy
        exact mem_iUnion₂.mpr ⟨e k, ((Fintype.equivFin A).symm k).property, hk⟩
      · intro hy
        obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hy
        refine mem_iUnion.mpr ⟨(Fintype.equivFin A) ⟨k, hk⟩, ?_⟩
        change (p.1 (e ((Fintype.equivFin A) ⟨k, hk⟩)), y) ∈
          H (l (e ((Fintype.equivFin A) ⟨k, hk⟩)))
        simpa only [e, Equiv.symm_apply_apply, mem_ofPred_eq] using hyk
    refine ⟨(x, p.2 j, p.1 ∘ e), ⟨hx, hj, ?_⟩, rfl⟩
    change (connectedComponentIn {y | (y, p.1 ∘ e) ∈
      finiteLevelUnionGraph (levelRelation H) (l ∘ e)} x).Nontrivial
    rwa [hset]
  · exact Eventually.of_forall fun _ h => (horder h).elim

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealTestLevelData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected real tests supply the actual level graphs and their
square-summable incidence weights for the next positive-law application. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace realTestLevelData
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
  (c : ℕ → UngatedRealTest d π EStar)

theorem weight_finite (i : ℕ) : (∑' x, (realTestLevelData d c).levelWeights i x ^ 2) < ∞ := by
  apply lt_of_le_of_lt (b := ∑' x, (c i).weight x ^ 2) _ (c i).weight_finite
  apply ENNReal.tsum_le_tsum
  intro x
  change (d.dust.indicator (c i).weight x) ^ 2 ≤ (c i).weight x ^ 2
  by_cases hx : x ∈ d.dust
  · simp only [indicator_of_mem hx, le_refl]
  · simp only [indicator_of_notMem hx, zero_pow (by decide : 2 ≠ 0), zero_le]

theorem marked_weights (M : Set Sphere)
    (hM : ∀ i, (c i).exclusions ∩ d.dust ⊆ M) (i : ℕ) :
    support ((realTestLevelData d c).levelWeights i) ⊆ M := by
  intro x hx
  change d.dust.indicator (c i).weight x ≠ 0 at hx
  by_cases hxB : x ∈ d.dust
  · rw [indicator_of_mem hxB] at hx
    exact hM i ⟨(c i).weight_support hx, hxB⟩
  · exact (hx (indicator_of_notMem hxB _)).elim

theorem point_bound (hU : IsOpen d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (i : ℕ) (x : Sphere) :
    volume {t | (t, x) ∈ (realTestLevelData d c).levels i} ≤
      (realTestLevelData d c).levelWeights i x := by
  change volume {t | (x, t) ∈ circleBandGraph d.quotientDomain (c i).coordinate.quotient} ≤
    d.dust.indicator (c i).weight x
  have hunit (y : Sphere) (_ : y ∈ d.quotientDomain) : |(c i).coordinate.quotient y| ≤ 1 := by
    rw [abs_of_nonneg ((c i).coordinate.quotient_unit y).1]
    exact ((c i).coordinate.quotient_unit y).2
  by_cases hx : x ∈ d.dust
  · rw [indicator_of_mem hx]
    exact (volume_circleBandGraph_incidence_le_budget hunit
      (by rw [hdense.closure_eq]; trivial) le_rfl).trans ((c i).band_bound x hx)
  · rw [indicator_of_notMem hx]
    have he : {t | (x, t) ∈ circleBandGraph d.quotientDomain (c i).coordinate.quotient} =
        {((c i).coordinate.quotient x : UnitAddCircle)} := by
      ext t
      change (x, t) ∈ circleBandGraph d.quotientDomain (c i).coordinate.quotient ↔
        t = ((c i).coordinate.quotient x : UnitAddCircle)
      rw [circleBandGraph_on_open hU (c i).coordinate.quotient_continuous (hBU hx)]
      exact eq_comm
    rw [he, unitAddCircle_volume_singleton]

theorem unique_free_trace (hdense : Dense d.quotientDomain) (M : Set Sphere)
    (hM : ∀ i, (c i).exclusions ∩ d.dust ⊆ M)
    (x : Sphere) (hx : x ∈ d.dust \ M) (i : ℕ) (a b : UnitAddCircle)
    (ha : (a, x) ∈ (realTestLevelData d c).levels i)
    (hb : (b, x) ∈ (realTestLevelData d c).levels i) : a = b := by
  have hunit (y : Sphere) (_ : y ∈ d.quotientDomain) : |(c i).coordinate.quotient y| ≤ 1 := by
    rw [abs_of_nonneg ((c i).coordinate.quotient_unit y).1]
    exact ((c i).coordinate.quotient_unit y).2
  have hcl : x ∈ closure d.quotientDomain := by rw [hdense.closure_eq]; trivial
  have hw : (c i).weight x = 0 := by
    by_contra h
    exact hx.2 (hM i ⟨(c i).weight_support h, hx.1⟩)
  have hle : limsup (c i).coordinate.quotient (𝓝[d.quotientDomain] x) -
      liminf (c i).coordinate.quotient (𝓝[d.quotientDomain] x) ≤ 0 := by
    apply ENNReal.ofReal_eq_zero.mp
    exact le_antisymm (by simpa only [hw] using (c i).band_bound x hx.1) bot_le
  have heq : limsup (c i).coordinate.quotient (𝓝[d.quotientDomain] x) =
      liminf (c i).coordinate.quotient (𝓝[d.quotientDomain] x) :=
    sub_eq_zero.mp (le_antisymm hle (boundary_width_nonneg hunit hcl))
  have hf : {t | (x, t) ∈ circleBandGraph d.quotientDomain (c i).coordinate.quotient} =
      {((liminf (c i).coordinate.quotient (𝓝[d.quotientDomain] x) : ℝ) : UnitAddCircle)} := by
    rw [circleBandGraph_fiber_eq_image_realFiber,
      intervalFiberHull_clusterGraph_eq_boundary_band hunit hcl, heq, Icc_self,
      image_singleton]
  have ha' : a ∈ ({t | (x, t) ∈ circleBandGraph d.quotientDomain (c i).coordinate.quotient}) := ha
  have hb' : b ∈ ({t | (x, t) ∈ circleBandGraph d.quotientDomain (c i).coordinate.quotient}) := hb
  rw [hf] at ha' hb'
  exact ha'.trans hb'.symm

end realTestLevelData

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SelectedBarrierRange
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small barrier is compatible with any subfamily of its retained levels. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace GradedRealTest

theorem exists_compatible_of_small_barrier
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    (c : ℕ → UngatedRealTest d π EStar) (M : Set Sphere)
    (hM : ∀ i, (c i).exclusions ∩ d.dust ⊆ M)
    (S : Set (UngatedRealTest d π EStar))
    (hselected : ∀ a ∈ S, ∃ i, c i = a)
    {regions : ℕ → Set Sphere}
    (hopen : ∀ n, IsOpen (regions n))
    (R : CompatibleRealBarrier (realTestLevelData d c) π
      (realTestLevelData.previous c) M EStar regions
      (fun _ => ((0 : ℂ) : Sphere)) univ)
    (k : ℕ) (hsmall : R.controlledSize < ENNReal.ofReal (1 / ((k : ℝ) + 1))) :
    ∃ b : GradedRealTest d π EStar,
      b.toUngatedRealTest.CompatibleWith S ∧ b.grade = k ∧ b.region = regions R.level := by
  classical
  let labels (a : UngatedRealTest d π EStar) : ℕ :=
    if h : ∃ i, c i = a then Classical.choose h else 0
  have hlabels (a) (ha : a ∈ S) : c (labels a) = a := by
    have h := hselected a ha
    dsimp only [labels]
    rw [dite_eq_left h]
    exact Classical.choose_spec h
  let R' : CompatibleRealBarrier d π (fun i => (c i).coordinate) M EStar regions
      (fun _ => ((0 : ℂ) : Sphere)) univ :=
    R.rebase rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)
  let b : GradedRealTest d π EStar :=
    { toUngatedRealTest := UngatedRealTest.of_barrier R' (hopen R'.level)
      grade := k
      small := by
        rw [UngatedRealTest.size_of_barrier]
        exact hsmall }
  refine ⟨b, ?_, rfl, rfl⟩
  apply UngatedRealTest.of_barrier_compatible R' (hopen R'.level) _ labels
  · intro a ha
    rw [← hlabels a ha]
    exact hM (labels a)
  · intro a ha
    rw [hlabels a ha]

end GradedRealTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableLawExtraction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed-countable-set conclusion from positive modulus. The
occupation and tuple densities, full visit bound, and atomless whole-image
test are obtained for the same law on actual base codes. -/

open Set MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D] [MeasurableSingletonClass D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D] [PolishSpace Y] [PolishSpace D]

theorem prescribed_countable_law_of_positive_modulus (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i))
    (p : D → X) (hp : Function.Injective p) (c : D → ℝ≥0∞)
    (hc0 : ∀ s, c s ≠ 0) (hct : ∀ s, c s ≠ ∞) (hc : (∑' s, c s ^ 2) < ∞)
    (ν : Measure X) [IsFiniteMeasure ν] [NullSingletonClass ν]
    [StandardBorelSpace (ConstrainedCostCode d p c ν)]
    (flags : Set X) (hflags : flags.Countable) (hν : ν d.dustᶜ = 0)
    (hunique : ∀ x ∈ d.dust \ flags, ∀ i t u,
      (t, x) ∈ d.levels i → (u, x) ∈ d.levels i → t = u)
    (μ : Measure Y) [IsFiniteMeasure μ]
    (ω : TupleType → ℝ≥0∞) (hω : (∑' i, ω i) < ∞)
    (hdual : MeasureImageDuality (ConstrainedCostCode d p c ν) (PathCostSpace Y D))
    (hlift : MeasurePlanLifting (ConstrainedCostCode d p c ν) (PathCostSpace Y D))
    (r : ℝ≥0) (hr : 0 < r)
    (hmod : (r : ℝ≥0∞) < measureFamilyModulus (ConstrainedCostCode d p c ν)
      (PathCostSpace Y D) (pathCostReference μ c (tupleReference ω))
        (constrainedCodeMeasure d p c ν)) :
    ∃ (P : ProbabilityMeasure (BasePathCode d)) (g : Y → ℝ≥0∞) (q : LevelTuple → ℝ≥0∞),
      Measurable g ∧ Measurable q ∧
      meanCodeOccupation d P = μ.withDensity g ∧
      (∫⁻ y, g y ^ 2 ∂μ) ≤ (r : ℝ≥0∞)⁻¹ ∧
      countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (p s)) ≤
        (r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1 ∧
      meanCodeTuple d P = (tupleReference ω).withDensity q ∧
      (∫⁻ t, q t ^ 2 ∂tupleReference ω) ≤ (r : ℝ≥0∞)⁻¹ ∧
      (∀ k, slotLaw d P k ≪ tupleReference ω) ∧
      (∫⁻ x, pathHitProbability (codePathLaw d P) x ∂ν) = 0 ∧
      (∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0) := by
  let : IsFiniteMeasure (tupleReference ω) := finite_tupleReference hω
  obtain ⟨P, Q, hQ, hbar, henergy, _, hres⟩ := positive_modulus_code_law d hU hB
    p c ν μ (tupleReference ω) hc hdual hlift r hr hmod
  have hd := codeLaw_component_densities d hU p c P μ (tupleReference ω) Q hQ hbar
  have he := codeReference_component_energies μ c (tupleReference ω) Q hQ
  refine ⟨P, Q ∘ costPhysical, Q ∘ costTuple, hQ.comp measurable_costPhysical,
    hQ.comp measurable_costTuple, hd.1, he.1.trans henergy, ?_, hd.2.2,
    he.2.trans henergy, ?_, ?_, hres⟩
  · exact (meanVisitCount_codePathLaw_budget d hU p hp c hc0 hct P μ
      (tupleReference ω) Q hQ hbar).trans
      (add_le_add (ENNReal.rpow_le_rpow henergy (by norm_num)) le_rfl)
  · exact codeLaw_slot_absolutelyContinuous d hU p c P μ (tupleReference ω) Q hbar
  · simp_rw [pathHitProbability_codePathLaw]
    exact codeLaw_whole_image_test d hU hB hH p c P μ ω Q hbar ν
      (ae_free_level_sections d.levels d.dust flags ν hflags hν hunique) hres

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_BarrierCodeLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
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

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_1 : BorelSpace Sphere := ⟨rfl⟩
theorem prescribed_countable_law_of_no_small_barrier
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
    (ν : Measure Sphere) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
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
    (previous : ℕ → PhysicalRealCoordinate d π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      circleBandGraph d.quotientDomain (previous i).quotient)
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
    {A : Type*} [TopologicalSpace A] [Countable A] [MeasurableSpace A] [BorelSpace A]
    (a : A → Sphere) (ha : Injective a) (haB : range a ⊆ d.dust)
    (c : A → ℝ≥0∞) (hc : (∑'s, c s ^ 2) < ∞)
    (ω : TupleType → ℝ≥0∞) (hω : ∀i, ω i ≠ 0)
    [PolishSpace A] [StandardBorelSpace (ConstrainedCostCode d a c ν)]
    (β : ℝ≥0∞)
    (hno : ∀R : CompatibleRealBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
      β ≤ R.controlledSize)
    (hωsum : (∑'i, ω i) < ∞)
    (hdual : MeasureImageDuality (ConstrainedCostCode d a c ν) (PathCostSpace Sphere A))
    (hlift : MeasurePlanLifting (ConstrainedCostCode d a c ν) (PathCostSpace Sphere A))
    (r : ℝ≥0) (hrpos : 0 < r)
    (hrbound : (r : ℝ≥0∞) < (β / (2 * barrierConstructionConstant C)) ^ 2)
    (hc0 : ∀s, c s ≠ 0) (hct : ∀s, c s ≠ ∞)
    (hν : ν d.dustᶜ = 0)
    (hunique : ∀x ∈ d.dust \ flags, ∀i t u,
      (t, x) ∈ d.levels i → (u, x) ∈ d.levels i → t = u) :
    ∃(P : ProbabilityMeasure (BasePathCode d)) (g : Sphere → ℝ≥0∞) (q : LevelTuple → ℝ≥0∞),
      Measurable g ∧ Measurable q ∧
      meanCodeOccupation d P = sphericalArea.withDensity g ∧
      (∫⁻y, g y ^ 2 ∂sphericalArea) ≤ (r : ℝ≥0∞)⁻¹ ∧
      countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤
        (r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1 ∧
      meanCodeTuple d P = (tupleReference ω).withDensity q ∧
      (∫⁻t, q t ^ 2 ∂tupleReference ω) ≤ (r : ℝ≥0∞)⁻¹ ∧
      (∀k, slotLaw d P k ≪ tupleReference ω) ∧
      (∫⁻x, pathHitProbability (codePathLaw d P) x ∂ν) = 0 ∧
      (∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0) := by
  have hmod := hrbound.trans_le (barrier_modulus_lower_bound hcoarea hLusin hsard hsch
    d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad ν hinf
    EStar hE hEU hEStar hEStarE hinfE p hpDust hp D hnest hshrink hED f hf W₁ W₂
    hW₁ hW₂ hW₁₂ hfiber harcs previous hlevels hweights hpoint flags hflags C hC hderiv
    htarget hcontours hgates a ha haB c hc ω hω β hno)
  have hH (i : ℕ) : IsClosed (d.levels i) := by
    rw [hlevels]
    exact (isCompact_circleBandGraph (fun x _ => by
      rw [abs_of_nonneg ((previous i).quotient_unit x).1]
      exact ((previous i).quotient_unit x).2)).isClosed.preimage continuous_swap
  exact prescribed_countable_law_of_positive_modulus d hU hB hH a ha c hc0 hct hc ν
    flags hflags hν hunique sphericalArea ω hωsum hdual hlift r hrpos hmod


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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
-- module Solutions.Q146_CD.CircleDomains_Probability_BorelFamilyHitFusion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
-- module Solutions.Q146_CD.CircleDomains_Selection_AtomlessQuantiles
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated positive-mass intervals for an atomless real probability law.
These provide the four collar arcs in the crossing argument after choosing
a circle coordinate. -/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem atomless_cdf_leftLim (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (x : ℝ) : leftLim (cdf μ) x = cdf μ x := by
  have hz := (cdf μ).measure_singleton x
  rw [measure_cdf μ, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at hz
  exact le_antisymm ((cdf μ).mono.leftLim_le le_rfl) (sub_nonpos.mp hz)

theorem continuous_atomless_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (cdf μ).mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [atomless_cdf_leftLim μ x, (cdf μ).rightLim_eq x]

theorem exists_atomless_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ x : ℝ, cdf μ x = q := by
  have hi := isPreconnected_univ.intermediate_value_Ioo
    (f := cdf μ) (l₁ := atBot) (l₂ := atTop) (by simp) (by simp)
    (continuous_atomless_cdf μ).continuousOn (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ)
  obtain ⟨x, _, hx⟩ := hi ⟨hq0, hq1⟩
  exact ⟨x, hx⟩

theorem atomless_measure_Ioo_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (a b : ℝ) :
    μ (Ioo a b) = ENNReal.ofReal (cdf μ b - cdf μ a) := by
  simpa only [measure_cdf, atomless_cdf_leftLim] using (cdf μ).measure_Ioo (a := a) (b := b)

theorem exists_eight_ordered_quantiles (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    ∃ q : Fin 8 → ℝ, StrictMono q ∧ ∀ i, cdf μ (q i) = ((i.val : ℝ) + 1) / 9 := by
  choose q hq using fun i : Fin 8 => exists_atomless_quantile μ
    (q := ((i.val : ℝ) + 1) / 9) (by positivity) (by
      have hi : (i.val : ℝ) < 8 := by exact_mod_cast i.isLt
      apply (div_lt_one (by norm_num : (0 : ℝ) < 9)).mpr
      linarith)
  refine ⟨q, ?_, hq⟩
  intro i j hij
  by_contra hn
  have hle := (cdf μ).mono (le_of_not_gt hn)
  rw [hq i, hq j] at hle
  have hval : (i.val : ℝ) < j.val := by exact_mod_cast hij
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RationalQuantileIntervals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed countable family suffices for the four separated quantile arcs. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem exists_rational_interval_inside (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) {r : ℝ≥0∞} (hr : r < μ (Ioo a b)) :
    ∃ l u : ℚ, a < (l : ℝ) ∧ l < u ∧ (u : ℝ) < b ∧ r < μ (Ioo (l : ℝ) (u : ℝ)) := by
  obtain ⟨K, hKsub, hK, hrK⟩ := measurableSet_Ioo.exists_lt_isCompact (μ := μ) hr
  have hKne : K.Nonempty := nonempty_of_measure_ne_zero
    (ne_of_gt (lt_of_le_of_lt bot_le hrK))
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hKne continuous_id.continuousOn
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hKne continuous_id.continuousOn
  obtain ⟨l, hal, hlx⟩ := exists_rat_btwn (hKsub hx).1
  obtain ⟨u, hyu, hub⟩ := exists_rat_btwn (hKsub hy).2
  have hlu : l < u := by exact_mod_cast (hlx.trans_le (hmax hx)).trans hyu
  refine ⟨l, u, hal, hlu, hub, hrK.trans_le (measure_mono ?_)⟩
  intro z hz
  exact ⟨hlx.trans_le (hmin hz), (hmax hz).trans_lt hyu⟩

/-- If the law is supported between two cut points, the four intervals can be
chosen strictly inside those cut points. -/
theorem exists_four_ordered_rational_intervals_between (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (a b : ℝ)
    (ha : cdf μ a = 0) (hb : cdf μ b = 1) :
    ∃ l u : Fin 4 → ℚ,
      (∀ i, a < (l i : ℝ) ∧ l i < u i ∧ (u i : ℝ) < b ∧
        (1 / 10 : ℝ≥0∞) < μ (Ioo (l i : ℝ) (u i : ℝ))) ∧
      ∀ i j, i < j → u i < l j := by
  obtain ⟨q, hmono, hq⟩ := exists_eight_ordered_quantiles μ
  have hqa (i : Fin 8) : a < q i := by
    by_contra hn
    have h := (cdf μ).mono (le_of_not_gt hn)
    rw [ha, hq] at h
    have : (0 : ℝ) < ((i.val : ℝ) + 1) / 9 := by positivity
    linarith
  have hqb (i : Fin 8) : q i < b := by
    by_contra hn
    have h := (cdf μ).mono (le_of_not_gt hn)
    rw [hb, hq] at h
    have hi : (i.val : ℝ) < 8 := by exact_mod_cast i.isLt
    linarith
  let L (i : Fin 4) : Fin 8 := ⟨2 * i.val, by omega⟩
  let U (i : Fin 4) : Fin 8 := ⟨2 * i.val + 1, by omega⟩
  have hm (i : Fin 4) : (1 / 10 : ℝ≥0∞) < μ (Ioo (q (L i)) (q (U i))) := by
    rw [atomless_measure_Ioo_cdf, hq, hq]
    have he : (((U i).val : ℝ) + 1) / 9 - (((L i).val : ℝ) + 1) / 9 = 1 / 9 := by
      simp only [L, U, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      ring
    rw [he, ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  choose l u hl hlu hu hmass using fun i => exists_rational_interval_inside μ
    (q (L i)) (q (U i)) (hm i)
  refine ⟨l, u, fun i => ⟨(hqa _).trans (hl i), hlu i, (hu i).trans (hqb _), hmass i⟩, ?_⟩
  intro i j hij
  have hqij : q (U i) < q (L j) := hmono (by change 2 * i.val + 1 < 2 * j.val; omega)
  exact_mod_cast (hu i).trans (hqij.trans (hl j))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleQuantileArcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four positively separated arcs from a fixed countable circle family. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem measurableSet_rationalCircleArc (l u : ℚ) : MeasurableSet (rationalCircleArc l u) :=
  measurable_unitCircleCut measurableSet_Ioo

theorem nullSingletonClass_unitCircleCut_map (μ : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (μ : Measure UnitAddCircle)] :
    NullSingletonClass (μ.map (f := unitCircleCut) (by first | (apply Measurable.aemeasurable; apply measurable_unitCircleCut <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure ℝ) := by
  constructor
  intro x
  rw [ProbabilityMeasure.map_apply' μ measurable_unitCircleCut.aemeasurable (measurableSet_singleton x)]
  apply Set.Subsingleton.measure_zero
  intro a ha b hb
  apply unitCircleCut_injective
  exact ha.trans hb.symm

theorem unitCircleCut_cdf_endpoints (μ : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (μ : Measure UnitAddCircle)] :
    cdf (μ.map (f := unitCircleCut) (by first | (apply Measurable.aemeasurable; apply measurable_unitCircleCut <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure ℝ) 0 = 0 ∧
      cdf (μ.map (f := unitCircleCut) (by first | (apply Measurable.aemeasurable; apply measurable_unitCircleCut <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure ℝ) 1 = 1 := by
  have := nullSingletonClass_unitCircleCut_map μ
  have hzero : (μ.map (f := unitCircleCut) (by first | (apply Measurable.aemeasurable; apply measurable_unitCircleCut <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure ℝ) (Iic 0) = 0 := by
    rw [ProbabilityMeasure.map_apply' μ measurable_unitCircleCut.aemeasurable measurableSet_Iic]
    apply measure_mono_null (t := unitCircleCut ⁻¹' {0})
    · intro θ hθ
      exact le_antisymm hθ (unitCircleCut_mem θ).1
    · apply Set.Subsingleton.measure_zero
      intro a ha b hb
      exact unitCircleCut_injective (ha.trans hb.symm)
  have hone : (μ.map (f := unitCircleCut) (by first | (apply Measurable.aemeasurable; apply measurable_unitCircleCut <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure ℝ) (Iic 1) = 1 := by
    rw [ProbabilityMeasure.map_apply' μ measurable_unitCircleCut.aemeasurable measurableSet_Iic]
    have he : unitCircleCut ⁻¹' Iic (1 : ℝ) = univ := by
      ext θ
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (unitCircleCut_mem θ).2.le
    rw [he, measure_univ]
  constructor
  · rw [cdf_eq_real, measureReal_def, hzero, ENNReal.toReal_zero]
  · rw [cdf_eq_real, measureReal_def, hone, ENNReal.toReal_one]

/-- All four arcs can be taken from the countable rational endpoint family,
with cyclic order witnessed inside a single cut of the circle. -/
theorem exists_four_ordered_rational_circle_arcs (μ : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (μ : Measure UnitAddCircle)] :
    ∃ l u : Fin 4 → ℚ,
      (∀ i, 0 < l i ∧ l i < u i ∧ u i < 1 ∧
        (1 / 10 : ℝ≥0∞) < (μ : Measure UnitAddCircle) (rationalCircleArc (l i) (u i))) ∧
      ∀ i j, i < j → u i < l j := by
  have := nullSingletonClass_unitCircleCut_map μ
  obtain ⟨hz, ho⟩ := unitCircleCut_cdf_endpoints μ
  obtain ⟨l, u, hlu, hord⟩ := exists_four_ordered_rational_intervals_between
    (μ.map (f := unitCircleCut) measurable_unitCircleCut.aemeasurable : Measure ℝ) 0 1 hz ho
  refine ⟨l, u, ?_, hord⟩
  intro i
  obtain ⟨hl, hmid, hu, hmass⟩ := hlu i
  refine ⟨by exact_mod_cast hl, hmid, by exact_mod_cast hu, ?_⟩
  rw [ProbabilityMeasure.map_apply' μ measurable_unitCircleCut.aemeasurable measurableSet_Ioo] at hmass
  exact hmass

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CircleSupportedLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of atomless boundary laws along an actual circle parametrization. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

theorem circle_supported_map_nullSingletonClass (μ : ProbabilityMeasure X)
    [NullSingletonClass (μ : Measure X)] (c : UnitAddCircle → X)
    (hc : MeasurableEmbedding c) (hs : (μ : Measure X) (range c)ᶜ = 0) :
    NullSingletonClass (μ.map (f := hc.invFun) hc.measurable_invFun.aemeasurable : Measure UnitAddCircle) := by
  constructor
  intro θ
  rw [ProbabilityMeasure.map_apply' μ hc.measurable_invFun.aemeasurable (measurableSet_singleton θ)]
  apply measure_mono_null (t := {c θ} ∪ (range c)ᶜ)
  · intro x hx
    by_cases hr : x ∈ range c
    · left
      obtain ⟨t, rfl⟩ := hr
      have ht : t = θ := (hc.leftInverse_invFun t).symm.trans hx
      exact congrArg c ht
    · exact Or.inr hr
  · exact measure_union_null (measure_singleton (c θ)) hs

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_OccupationProduct
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independence commutes with taking the mean physical occupation measure.
This identifies the expected two-path kernel integral with its density integral. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem measurable_finite_measure_product
    {A B X Y : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : A → Measure X) (ν : B → Measure Y)
    [∀ a, IsFiniteMeasure (μ a)] [∀ b, IsFiniteMeasure (ν b)]
    (hμ : Measurable μ) (hν : Measurable ν) :
    Measurable (fun p : A × B => (μ p.1).prod (ν p.2)) := by
  let mf : A → FiniteMeasure X := fun a => ⟨μ a, inferInstance⟩
  let nf : B → FiniteMeasure Y := fun b => ⟨ν b, inferInstance⟩
  have hm : Measurable mf := hμ.subtype_mk
  have hn : Measurable nf := hν.subtype_mk
  exact FiniteMeasure.measurable_fun_prod.comp
    ((hm.comp measurable_fst).prodMk (hn.comp measurable_snd))

theorem product_bind_finite_measures
    {A B X Y : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure A) (Q : Measure B) [SFinite P] [SFinite Q]
    (μ : A → Measure X) (ν : B → Measure Y)
    [∀ a, IsFiniteMeasure (μ a)] [∀ b, IsFiniteMeasure (ν b)]
    [SigmaFinite (P.bind μ)] [SigmaFinite (Q.bind ν)]
    (hμ : Measurable μ) (hν : Measurable ν) :
    (P.bind μ).prod (Q.bind ν) =
      (P.prod Q).bind (fun p => (μ p.1).prod (ν p.2)) := by
  apply Measure.prod_eq
  intro s t hs ht
  rw [Measure.bind_apply (hs.prod ht)
    (measurable_finite_measure_product μ ν hμ hν).aemeasurable]
  simp_rw [Measure.prod_prod]
  rw [lintegral_prod_mul
    (show Measurable (fun a => μ a s) from (Measure.measurable_coe hs).comp hμ).aemeasurable
    (show Measurable (fun b => ν b t) from (Measure.measurable_coe ht).comp hν).aemeasurable,
    Measure.bind_apply hs hμ.aemeasurable, Measure.bind_apply ht hν.aemeasurable]

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)]

theorem mean_code_pair_occupation (d e : PathCodeData X Y)
    (hd : IsOpen d.quotientDomain) (he : IsOpen e.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    [SigmaFinite (meanCodeOccupation d P)] [SigmaFinite (meanCodeOccupation e Q)]
    (K : Y × Y → ℝ≥0∞) (hK : Measurable K) :
    (∫⁻ p, ∫⁻ z, K z ∂(baseCodeOccupation d p.1).prod (baseCodeOccupation e p.2)
      ∂(P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))) =
      ∫⁻ z, K z ∂(meanCodeOccupation d P).prod (meanCodeOccupation e Q) := by
  have hm := measurable_baseCodeOccupation d hd
  have hn := measurable_baseCodeOccupation e he
  let : SigmaFinite ((P : Measure (BasePathCode d)).bind (baseCodeOccupation d)) :=
    inferInstanceAs (SigmaFinite (meanCodeOccupation d P))
  let : SigmaFinite ((Q : Measure (BasePathCode e)).bind (baseCodeOccupation e)) :=
    inferInstanceAs (SigmaFinite (meanCodeOccupation e Q))
  rw [meanCodeOccupation, meanCodeOccupation,
    product_bind_finite_measures (P : Measure (BasePathCode d)) (Q : Measure (BasePathCode e))
      (baseCodeOccupation d) (baseCodeOccupation e) hm hn,
    Measure.lintegral_bind (measurable_finite_measure_product _ _ hm hn).aemeasurable
      hK.aemeasurable]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PairKernelEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-sided kernel estimate used for local domain meetings. The
reference measure and kernel will be the spherical area and the normalized
small-ball indicator; no boundedness of the occupation densities is needed. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

theorem pair_kernel_energy_bound (σ : Measure X) [SFinite σ]
    (K : X × X → ℝ≥0∞) (hK : Measurable K)
    (g h : X → ℝ≥0∞) (hg : Measurable g) (hh : Measurable h)
    {C E : ℝ≥0∞}
    (hrow : ∀ x, (∫⁻ y, K (x, y) ∂σ) ≤ C)
    (hcol : ∀ y, (∫⁻ x, K (x, y) ∂σ) ≤ C)
    (hgE : (∫⁻ x, g x ^ 2 ∂σ) ≤ E)
    (hhE : (∫⁻ x, h x ^ 2 ∂σ) ≤ E) :
    (∫⁻ p, K p * (g p.1 * h p.2) ∂σ.prod σ) ≤ C * E := by
  let ν := (σ.prod σ).withDensity K
  have hgg : Measurable (fun p : X × X => g p.1 ^ 2) :=
    (hg.comp measurable_fst).pow_const 2
  have hhh : Measurable (fun p : X × X => h p.2 ^ 2) :=
    (hh.comp measurable_snd).pow_const 2
  have hG : (∫⁻ p, g p.1 ^ 2 ∂ν) ≤ C * E := by
    rw [show ν = (σ.prod σ).withDensity K from rfl,
      lintegral_withDensity_eq_lintegral_mul _ hK hgg,
      lintegral_prod _ (hK.mul hgg).aemeasurable]
    calc
      _ = ∫⁻ x, (∫⁻ y, K (x, y) ∂σ) * g x ^ 2 ∂σ := by
        apply lintegral_congr
        intro x
        simpa only [Pi.mul_apply, Function.comp_def, id_eq] using
          (lintegral_mul_const (μ := σ) (g x ^ 2)
            (hK.comp (measurable_const.prodMk measurable_id)))
      _ ≤ ∫⁻ x, C * g x ^ 2 ∂σ :=
        lintegral_mono fun x => mul_le_mul' (hrow x) le_rfl
      _ = C * ∫⁻ x, g x ^ 2 ∂σ := lintegral_const_mul _ (hg.pow_const 2)
      _ ≤ C * E := mul_le_mul' le_rfl hgE
  have hH : (∫⁻ p, h p.2 ^ 2 ∂ν) ≤ C * E := by
    rw [show ν = (σ.prod σ).withDensity K from rfl,
      lintegral_withDensity_eq_lintegral_mul _ hK hhh,
      lintegral_prod_symm _ (hK.mul hhh).aemeasurable]
    calc
      _ = ∫⁻ y, (∫⁻ x, K (x, y) ∂σ) * h y ^ 2 ∂σ := by
        apply lintegral_congr
        intro y
        simpa only [Pi.mul_apply, Function.comp_def, id_eq] using
          (lintegral_mul_const (μ := σ) (h y ^ 2)
            (hK.comp (measurable_id.prodMk measurable_const)))
      _ ≤ ∫⁻ y, C * h y ^ 2 ∂σ :=
        lintegral_mono fun y => mul_le_mul' (hcol y) le_rfl
      _ = C * ∫⁻ y, h y ^ 2 ∂σ := lintegral_const_mul _ (hh.pow_const 2)
      _ ≤ C * E := mul_le_mul' le_rfl hhE
  have hconj : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hconj
    (hg.comp measurable_fst).aemeasurable (hh.comp measurable_snd).aemeasurable
  have hCS' : (∫⁻ p, g p.1 * h p.2 ∂ν) ≤
      (∫⁻ p, g p.1 ^ 2 ∂ν) ^ (1 / 2 : ℝ) *
      (∫⁻ p, h p.2 ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    simpa only [Pi.mul_apply, Function.comp_def, ENNReal.rpow_two] using hCS
  have hid : (∫⁻ p, g p.1 * h p.2 ∂ν) =
      ∫⁻ p, K p * (g p.1 * h p.2) ∂σ.prod σ :=
    lintegral_withDensity_eq_lintegral_mul _ hK
      (show Measurable (fun p : X × X => g p.1 * h p.2) from
        (hg.comp measurable_fst).mul (hh.comp measurable_snd))
  rw [← hid]
  apply hCS'.trans
  calc
    _ ≤ (C * E) ^ (1 / 2 : ℝ) * (C * E) ^ (1 / 2 : ℝ) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hG (by norm_num))
        (ENNReal.rpow_le_rpow hH (by norm_num))
    _ = C * E := by rw [← sq, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BallPairKernel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized proximity kernels for two local arclength occupations. -/

open Set Function Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

theorem measurable_ballPairKernel (A : Set X) (hA : MeasurableSet A) (a : ℝ≥0) :
    Measurable (ballPairKernel A a) := by
  apply measurable_const.indicator
  exact (hA.preimage measurable_fst).inter
    ((hA.preimage measurable_snd).inter (measurableSet_lt measurable_dist measurable_const))

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem ballPairKernel_symm (A : Set X) (a : ℝ≥0) (x y : X) :
    ballPairKernel A a (x, y) = ballPairKernel A a (y, x) := by
  classical
  simp only [ballPairKernel, Set.indicator, mem_ofPred_eq, dist_comm y x]
  congr 1
  exact propext and_left_comm

omit [SecondCountableTopology X] in
theorem ballPairKernel_row_bound (σ : Measure X) (A : Set X) (hA : MeasurableSet A)
    {a : ℝ≥0} (ha : a ≠ 0) {C : ℝ≥0∞}
    (hball : ∀ x ∈ A, σ (ball x (2 * a)) ≤ C * (a : ℝ≥0∞) ^ 2) (x : X) :
    (∫⁻ y, ballPairKernel A a (x, y) ∂σ) ≤ C := by
  classical
  by_cases hx : x ∈ A
  · have hid : (fun y => ballPairKernel A a (x, y)) =
        (A ∩ ball x (2 * a)).indicator (fun _ => (a : ℝ≥0∞)⁻¹ ^ 2) := by
      funext y
      simp only [ballPairKernel, Set.indicator_apply, mem_ofPred_eq,
        mem_inter_iff, mem_ball, hx, true_and, dist_comm]
    rw [hid, lintegral_indicator_const (hA.inter measurableSet_ball)]
    calc
      _ ≤ (a : ℝ≥0∞)⁻¹ ^ 2 * (C * (a : ℝ≥0∞) ^ 2) :=
        mul_le_mul' le_rfl ((measure_mono inter_subset_right).trans (hball x hx))
      _ = C := by
        have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
        rw [mul_left_comm, ← mul_pow, ENNReal.inv_mul_cancel ha0 ENNReal.coe_ne_top]
        simp
  · have hz : (fun y => ballPairKernel A a (x, y)) = 0 := by
      funext y
      simp [ballPairKernel, hx]
    rw [hz]
    change (∫⁻ _ : X, (0 : ℝ≥0∞) ∂σ) ≤ C
    simp

theorem localized_ball_pair_energy_bound (σ : Measure X) [SFinite σ]
    (A : Set X) (hA : MeasurableSet A) {a : ℝ≥0} (ha : a ≠ 0)
    (g h : X → ℝ≥0∞) (hg : Measurable g) (hh : Measurable h) {C E : ℝ≥0∞}
    (hball : ∀ x ∈ A, σ (ball x (2 * a)) ≤ C * (a : ℝ≥0∞) ^ 2)
    (hgE : (∫⁻ x in A, g x ^ 2 ∂σ) ≤ E)
    (hhE : (∫⁻ x in A, h x ^ 2 ∂σ) ≤ E) :
    (∫⁻ p, ballPairKernel A a p * (g p.1 * h p.2) ∂σ.prod σ) ≤ C * E := by
  have hind (f : X → ℝ≥0∞) :
      (fun x => (A.indicator f x) ^ 2) = A.indicator (fun x => f x ^ 2) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hb := pair_kernel_energy_bound σ (ballPairKernel A a)
    (measurable_ballPairKernel A hA a) (A.indicator g) (A.indicator h)
    (hg.indicator hA) (hh.indicator hA) (C := C) (E := E)
    (ballPairKernel_row_bound σ A hA ha hball)
    (fun y => by simpa only [ballPairKernel_symm A a] using
      ballPairKernel_row_bound σ A hA ha hball y)
    (by rw [hind, lintegral_indicator hA]; exact hgE)
    (by rw [hind, lintegral_indicator hA]; exact hhE)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr
  intro p
  by_cases hpa : p.1 ∈ A <;> by_cases hpb : p.2 ∈ A <;>
    simp [ballPairKernel, Set.indicator, hpa, hpb]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodePairOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proximity integral of independent physical path occupations is
controlled by their local square energies. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurable_codePairProximity (d e : PathCodeData X Y)
    (hd : IsOpen d.quotientDomain) (he : IsOpen e.quotientDomain)
    (A : Set Y) (hA : MeasurableSet A) (a : ℝ≥0) :
    Measurable (codePairProximity d e A a) :=
  (Measure.measurable_lintegral (measurable_ballPairKernel A hA a)).comp
    (measurable_finite_measure_product _ _ (measurable_baseCodeOccupation d hd)
      (measurable_baseCodeOccupation e he))

theorem mean_codePairProximity_le (d e : PathCodeData X Y)
    (hd : IsOpen d.quotientDomain) (he : IsOpen e.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    [SigmaFinite (meanCodeOccupation d P)] [SigmaFinite (meanCodeOccupation e Q)]
    (σ : Measure Y) [SFinite σ] (g h : Y → ℝ≥0∞)
    (hg : Measurable g) (hh : Measurable h)
    (hP : meanCodeOccupation d P = σ.withDensity g)
    (hQ : meanCodeOccupation e Q = σ.withDensity h)
    (A : Set Y) (hA : MeasurableSet A) {a : ℝ≥0} (ha : a ≠ 0) {C E : ℝ≥0∞}
    (hball : ∀ x ∈ A, σ (Metric.ball x (2 * a)) ≤ C * (a : ℝ≥0∞) ^ 2)
    (hgE : (∫⁻ x in A, g x ^ 2 ∂σ) ≤ E)
    (hhE : (∫⁻ x in A, h x ^ 2 ∂σ) ≤ E) :
    (∫⁻ p, codePairProximity d e A a p
      ∂(P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))) ≤ C * E := by
  change (∫⁻ p, ∫⁻ z, ballPairKernel A a z
    ∂(baseCodeOccupation d p.1).prod (baseCodeOccupation e p.2)
    ∂(P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))) ≤ C * E
  rw [mean_code_pair_occupation d e hd he P Q _ (measurable_ballPairKernel A hA a),
    hP, hQ, prod_withDensity hg hh,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : Y × Y => g z.1 * h z.2) from
        (hg.comp measurable_fst).mul (hh.comp measurable_snd))
      (measurable_ballPairKernel A hA a)]
  have hb := localized_ball_pair_energy_bound σ A hA ha g h hg hh hball hgE hhE
  simpa only [Pi.mul_apply, Function.comp_def, mul_comm] using hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ExitTimeMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel first-exit and last-entry locations for the collar crossing laws. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem firstExit_notMem_of_exists (γ : C(PathTime, X)) {V : Set X}
    (hV : IsOpen V) (hex : ∃ t, γ t ∉ V) : γ (firstExitTime γ V) ∉ V :=
  (hV.isClosed_compl.preimage γ.continuous).isCompact.sInf_mem hex

theorem lt_firstExit_iff_mapsTo (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    {t : PathTime} (ht : t < ⊤) :
    t < firstExitTime γ V ↔ MapsTo γ (Iic t) V := by
  constructor
  · intro h s hs
    exact mem_before_firstExit γ V (hs.trans_lt h)
  · intro h
    by_contra hn
    have hle : firstExitTime γ V ≤ t := le_of_not_gt hn
    by_cases hex : ∃ s, γ s ∉ V
    · exact firstExit_notMem_of_exists γ hV hex (h hle)
    · have he : {s | γ s ∉ V} = ∅ := not_nonempty_iff_eq_empty.mp hex
      have htop : firstExitTime γ V = ⊤ := by rw [firstExitTime, he, sInf_empty]
      exact ht.not_ge (htop ▸ hle)

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_firstExitTime (V : Set X) (hV : IsOpen V) :
    Measurable (fun γ : C(PathTime, X) => firstExitTime γ V) := by
  apply measurable_of_Ioi
  intro t
  by_cases ht : t = ⊤
  · subst t
    simp
  · have he : (fun γ : C(PathTime, X) => firstExitTime γ V) ⁻¹' Ioi t =
        {γ : C(PathTime, X) | MapsTo γ (Iic t) V} := by
      ext γ
      exact lt_firstExit_iff_mapsTo γ hV (lt_top_iff_ne_top.mpr ht)
    rw [he]
    exact (ContinuousMap.isOpen_setOfPred_mapsTo isClosed_Iic.isCompact hV).measurableSet

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem continuous_reversedPath : Continuous (reversedPath (X := X)) :=
  ContinuousMap.continuous_precomp ⟨unitInterval.symm, unitInterval.continuous_symm⟩

theorem measurable_lastEntryTime (V : Set X) (hV : IsOpen V) :
    Measurable (fun γ : C(PathTime, X) => lastEntryTime γ V) :=
  unitInterval.continuous_symm.measurable.comp
    ((measurable_firstExitTime V hV).comp continuous_reversedPath.measurable)

theorem measurable_lastEntryLocation (V : Set X) (hV : IsOpen V)
    [MeasurableSpace X] [BorelSpace X] :
    Measurable (fun γ : C(PathTime, X) => γ (lastEntryTime γ V)) :=
  continuous_eval.measurable.comp (measurable_id.prodMk (measurable_lastEntryTime V hV))

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem mem_after_lastEntry (γ : C(PathTime, X)) (V : Set X) {t : PathTime}
    (ht : lastEntryTime γ V < t) : γ t ∈ V := by
  have hlt : unitInterval.symm t < firstExitTime (reversedPath γ) V :=
    unitInterval.symm_lt_comm.mpr ht
  have hm := mem_before_firstExit (reversedPath γ) V hlt
  simpa only [reversedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    unitInterval.symm_symm] using hm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LastEntryContinua
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The last-entry tails are actual compact connected sets. Their only point
outside the open collar is their initial boundary point. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem isCompact_lastEntryTail (γ : C(PathTime, X)) (V : Set X) :
    IsCompact (lastEntryTail γ V) :=
  isClosed_Ici.isCompact.image γ.continuous

theorem isConnected_lastEntryTail (γ : C(PathTime, X)) (V : Set X) :
    IsConnected (lastEntryTail γ V) :=
  (isConnected_Ici (a := lastEntryTime γ V)).image γ γ.continuous.continuousOn

theorem lastEntry_mem_tail (γ : C(PathTime, X)) (V : Set X) :
    γ (lastEntryTime γ V) ∈ lastEntryTail γ V := ⟨_, mem_Ici.mpr le_rfl, rfl⟩

theorem endpoint_mem_tail (γ : C(PathTime, X)) (V : Set X) :
    γ ⊤ ∈ lastEntryTail γ V := ⟨_, mem_Ici.mpr le_top, rfl⟩

theorem lastEntryTail_subset_closure (γ : C(PathTime, X)) {V : Set X}
    (hV : IsOpen V) (hstart : γ ⊥ ∉ V) (hend : γ ⊤ ∈ V) :
    lastEntryTail γ V ⊆ closure V := by
  rintro x ⟨t, ht, rfl⟩
  exact lastEntry_final_segment γ hV hstart hend ht

theorem lastEntryTail_outside (γ : C(PathTime, X)) (V : Set X) {x : X}
    (hx : x ∈ lastEntryTail γ V) (hxV : x ∉ V) :
    x = γ (lastEntryTime γ V) := by
  obtain ⟨t, ht, rfl⟩ := hx
  have he : t = lastEntryTime γ V := by
    apply le_antisymm _ ht
    by_contra hn
    exact hxV (mem_after_lastEntry γ V (lt_of_not_ge hn))
  rw [he]

theorem isConnected_union_lastEntryTails (γ δ : C(PathTime, X)) (V : Set X)
    (hend : γ ⊤ = δ ⊤) :
    IsConnected (lastEntryTail γ V ∪ lastEntryTail δ V) := by
  apply IsConnected.union
  · exact ⟨γ ⊤, endpoint_mem_tail γ V, hend.symm ▸ endpoint_mem_tail δ V⟩
  · exact isConnected_lastEntryTail γ V
  · exact isConnected_lastEntryTail δ V

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AlternatingTailCrossing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Alternating last-entry path tails cross in the interior of the disk. -/

open Set Function Metric

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem alternating_lastEntry_tails_intersect (hcross : UnitDiskAlternatingContinua)
    (V : Set X) (hV : IsOpen V) (f : X → ℂ)
    (hf : ContinuousOn f (closure V)) (hfinj : InjOn f (closure V))
    (hfdisk : MapsTo f (closure V) (closedBall 0 1))
    (γ : Fin 4 → C(PathTime, X))
    (hstart : ∀ i, γ i ⊥ ∉ V) (hend : ∀ i, γ i ⊤ ∈ V)
    (h02 : γ 0 ⊤ = γ 2 ⊤) (h13 : γ 1 ⊤ = γ 3 ⊤)
    (θ : Fin 4 → UnitAddCircle) (hθ : StrictMono (unitCircleCut ∘ θ))
    (hentry : ∀ i, f (γ i (lastEntryTime (γ i) V)) = standardCirclePoint (θ i)) :
    ∃ x ∈ V, (x ∈ lastEntryTail (γ 0) V ∨ x ∈ lastEntryTail (γ 2) V) ∧
      (x ∈ lastEntryTail (γ 1) V ∨ x ∈ lastEntryTail (γ 3) V) := by
  let A := lastEntryTail (γ 0) V ∪ lastEntryTail (γ 2) V
  let B := lastEntryTail (γ 1) V ∪ lastEntryTail (γ 3) V
  have hsub (i : Fin 4) : lastEntryTail (γ i) V ⊆ closure V :=
    lastEntryTail_subset_closure (γ i) hV (hstart i) (hend i)
  have hA : A ⊆ closure V := union_subset (hsub 0) (hsub 2)
  have hB : B ⊆ closure V := union_subset (hsub 1) (hsub 3)
  have hAc : IsCompact A := (isCompact_lastEntryTail (γ 0) V).union
    (isCompact_lastEntryTail (γ 2) V)
  have hBc : IsCompact B := (isCompact_lastEntryTail (γ 1) V).union
    (isCompact_lastEntryTail (γ 3) V)
  have hAn : IsConnected A := isConnected_union_lastEntryTails (γ 0) (γ 2) V h02
  have hBn : IsConnected B := isConnected_union_lastEntryTails (γ 1) (γ 3) V h13
  have hmem (i : Fin 4) : standardCirclePoint (θ i) ∈ f '' lastEntryTail (γ i) V :=
    ⟨_, lastEntry_mem_tail (γ i) V, hentry i⟩
  obtain ⟨z, ⟨x, hx, hfx⟩, y, hy, hfy⟩ := hcross (f '' A) (f '' B)
    (hAc.image_of_continuousOn (hf.mono hA)) (hAn.image f (hf.mono hA))
    (hBc.image_of_continuousOn (hf.mono hB)) (hBn.image f (hf.mono hB))
    (by rintro _ ⟨x, hx, rfl⟩; exact hfdisk (hA hx))
    (by rintro _ ⟨y, hy, rfl⟩; exact hfdisk (hB hy)) θ hθ
    (image_mono subset_union_left (hmem 0)) (image_mono subset_union_right (hmem 2))
    (image_mono subset_union_left (hmem 1)) (image_mono subset_union_right (hmem 3))
  have hxy : x = y := hfinj (hA hx) (hB hy) (hfx.trans hfy.symm)
  subst y
  have hne (i j : Fin 4) (hij : i ≠ j) :
      γ i (lastEntryTime (γ i) V) ≠ γ j (lastEntryTime (γ j) V) := by
    intro he
    have hh := congrArg f he
    rw [hentry i, hentry j] at hh
    exact hij (hθ.injective (congrArg unitCircleCut (standardCirclePoint_injective hh)))
  have hout (i j : Fin 4) (hij : i ≠ j)
      (hxi : x ∈ lastEntryTail (γ i) V) (hxj : x ∈ lastEntryTail (γ j) V) : x ∈ V := by
    by_contra hv
    exact hne i j hij ((lastEntryTail_outside (γ i) V hxi hv).symm.trans
      (lastEntryTail_outside (γ j) V hxj hv))
  refine ⟨x, ?_, hx, hy⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hout 0 1 (by decide) hx hy
  · exact hout 0 3 (by decide) hx hy
  · exact hout 2 1 (by decide) hx hy
  · exact hout 2 3 (by decide) hx hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FourSampleBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four independent samples in the alternating collar argument.  Outer
measure suffices, so no extra measurability premise is imposed on meeting events. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem measurePreserving_pairSample (μ : Measure X) [IsProbabilityMeasure μ] (i : Fin 2) :
    MeasurePreserving (pairSample i) (μ.prod μ) μ := by
  fin_cases i
  · have he : pairSample (0 : Fin 2) = (Prod.fst : X × X → X) := by
      funext p
      simp [pairSample]
    change MeasurePreserving (pairSample (0 : Fin 2)) (μ.prod μ) μ
    rw [he]
    exact measurePreserving_fst
  · have he : pairSample (1 : Fin 2) = (Prod.snd : X × X → X) := by
      funext p
      simp [pairSample]
    change MeasurePreserving (pairSample (1 : Fin 2)) (μ.prod μ) μ
    rw [he]
    exact measurePreserving_snd

theorem measurePreserving_crossSample (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (i j : Fin 2) :
    MeasurePreserving (crossSample i j) ((μ.prod μ).prod (ν.prod ν)) (μ.prod ν) :=
  (measurePreserving_pairSample μ i).prod (measurePreserving_pairSample ν j)

theorem four_cross_pair_union_bound (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (R : Set (X × Y)) :
    ((μ.prod μ).prod (ν.prod ν)) {p | ∃ i j : Fin 2, crossSample i j p ∈ R} ≤
      4 * (μ.prod ν) R := by
  let M := (μ.prod μ).prod (ν.prod ν)
  have he : {p | ∃ i j : Fin 2, crossSample i j p ∈ R} =
      ⋃ i : Fin 2, ⋃ j : Fin 2, crossSample i j ⁻¹' R := by ext p; simp
  rw [he]
  calc
    M (⋃ i : Fin 2, ⋃ j : Fin 2, crossSample i j ⁻¹' R) ≤
        ∑' i : Fin 2, M (⋃ j : Fin 2, crossSample i j ⁻¹' R) := measure_iUnion_le _
    _ ≤ ∑' i : Fin 2, ∑' j : Fin 2, M (crossSample i j ⁻¹' R) :=
      ENNReal.tsum_le_tsum fun i => measure_iUnion_le _
    _ ≤ ∑' _i : Fin 2, ∑' _j : Fin 2, (μ.prod ν) R :=
      ENNReal.tsum_le_tsum fun i => ENNReal.tsum_le_tsum fun j =>
        (measurePreserving_crossSample μ ν i j).measure_preimage_le R
    _ = 4 * (μ.prod ν) R := by simp [tsum_fintype] <;> ring

theorem four_sample_rectangle_lower_bound (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A₀ A₁ : Set X) (B₀ B₁ : Set Y) (r : ℝ≥0∞)
    (hA₀ : r ≤ μ A₀) (hA₁ : r ≤ μ A₁) (hB₀ : r ≤ ν B₀) (hB₁ : r ≤ ν B₁) :
    r ^ 4 ≤ ((μ.prod μ).prod (ν.prod ν)) ((A₀ ×ˢ A₁) ×ˢ (B₀ ×ˢ B₁)) := by
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  calc
    r ^ 4 = (r * r) * (r * r) := by ring
    _ ≤ (μ A₀ * μ A₁) * (ν B₀ * ν B₁) :=
      mul_le_mul' (mul_le_mul' hA₀ hA₁) (mul_le_mul' hB₀ hB₁)

theorem four_sample_meeting_constraint (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A₀ A₁ : Set X) (B₀ B₁ : Set Y) (R : Set (X × Y)) (r b : ℝ≥0∞)
    (hA₀ : r ≤ μ A₀) (hA₁ : r ≤ μ A₁) (hB₀ : r ≤ ν B₀) (hB₁ : r ≤ ν B₁)
    (hcross : ∀ᵐ p ∂((μ.prod μ).prod (ν.prod ν)),
      p ∈ (A₀ ×ˢ A₁) ×ˢ (B₀ ×ˢ B₁) → ∃ i j : Fin 2, crossSample i j p ∈ R)
    (hR : (μ.prod ν) R ≤ b) : r ^ 4 ≤ 4 * b := by
  exact (four_sample_rectangle_lower_bound μ ν A₀ A₁ B₀ B₁ r hA₀ hA₁ hB₀ hB₁).trans
    ((measure_mono_ae hcross).trans ((four_cross_pair_union_bound μ ν R).trans
      (mul_le_mul' (le_refl 4) hR)))

/-- A single sufficiently small collar budget defeats the four-sample lower bound. -/
theorem exists_small_crossing_budget (C : ℝ≥0∞) (hC : C ≠ ∞) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧
      4 * (2 * δ + (1 + C) * δ ^ 2) < (1 / 10 : ℝ≥0∞) ^ 4 := by
  have hsum : (1 : ℝ≥0∞) + C ≠ ∞ := ENNReal.add_ne_top.mpr ⟨by norm_num, hC⟩
  have hc : Continuous (fun δ : ℝ≥0∞ => 4 * (2 * δ + (1 + C) * δ ^ 2)) :=
    (ENNReal.continuous_const_mul (by norm_num)).comp
      ((ENNReal.continuous_const_mul (by norm_num)).add
        ((ENNReal.continuous_const_mul hsum).comp (ENNReal.continuous_pow 2)))
  have ht : Filter.Tendsto (fun δ : ℝ≥0∞ => 4 * (2 * δ + (1 + C) * δ ^ 2))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have he := ht.eventually_lt_const (ENNReal.pow_pos (ENNReal.div_pos (by norm_num) ENNReal.ofNat_ne_top) 4 :
    (0 : ℝ≥0∞) < (1 / 10 : ℝ≥0∞) ^ 4)
  have hp : ∀ᶠ δ : ℝ≥0∞ in nhdsWithin 0 (Ioi 0), 0 < δ := self_mem_nhdsWithin
  exact (hp.and he).exists

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CollarAlternationProbability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four positive-mass collar arcs force a quantitative lower bound for
meetings of the two independent original path laws. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X A B : Type*} [MetricSpace X] [MeasurableSpace A] [MeasurableSpace B]

theorem collar_alternation_probability (hcross : UnitDiskAlternatingContinua)
    (V : Set X) (hV : IsOpen V) (f : X → ℂ)
    (hf : ContinuousOn f (closure V)) (hfinj : InjOn f (closure V))
    (hfdisk : MapsTo f (closure V) (Metric.closedBall 0 1))
    (χ : X → UnitAddCircle)
    (hχ : ∀ x ∈ frontier V, f x = standardCirclePoint (χ x))
    (P : ProbabilityMeasure A) (Q : ProbabilityMeasure B)
    (a : A → C(PathTime, X)) (b : B → C(PathTime, X))
    (p q : X) (hp : p ∈ V) (hq : q ∈ V)
    (ha : ∀ᵐ z ∂(P : Measure A), a z ⊥ ∉ V ∧ a z ⊤ = p)
    (hb : ∀ᵐ z ∂(Q : Measure B), b z ⊥ ∉ V ∧ b z ⊤ = q)
    (l u : Fin 4 → ℚ) (horder : ∀ i j, i < j → u i < l j)
    (ha0 : (1 / 10 : ℝ≥0∞) ≤ (P : Measure A)
      {z | χ (a z (lastEntryTime (a z) V)) ∈ rationalCircleArc (l 0) (u 0)})
    (ha2 : (1 / 10 : ℝ≥0∞) ≤ (P : Measure A)
      {z | χ (a z (lastEntryTime (a z) V)) ∈ rationalCircleArc (l 2) (u 2)})
    (hb1 : (1 / 10 : ℝ≥0∞) ≤ (Q : Measure B)
      {z | χ (b z (lastEntryTime (b z) V)) ∈ rationalCircleArc (l 1) (u 1)})
    (hb3 : (1 / 10 : ℝ≥0∞) ≤ (Q : Measure B)
      {z | χ (b z (lastEntryTime (b z) V)) ∈ rationalCircleArc (l 3) (u 3)}) :
    (1 / 10 : ℝ≥0∞) ^ 4 ≤ 4 * ((P : Measure A).prod (Q : Measure B))
      {z | ∃ x ∈ V, x ∈ range (a z.1) ∧ x ∈ range (b z.2)} := by
  let E (i : Fin 4) (γ : C(PathTime, X)) :=
    χ (γ (lastEntryTime γ V)) ∈ rationalCircleArc (l i) (u i)
  let R : Set (A × B) := {z | ∃ x ∈ V, x ∈ range (a z.1) ∧ x ∈ range (b z.2)}
  let M := ((P : Measure A).prod (P : Measure A)).prod ((Q : Measure B).prod (Q : Measure B))
  have hA (i : Fin 2) : ∀ᵐ z ∂M,
      a (pairSample i z.1) ⊥ ∉ V ∧ a (pairSample i z.1) ⊤ = p :=
    ((measurePreserving_pairSample (P : Measure A) i).comp
      measurePreserving_fst).quasiMeasurePreserving.ae ha
  have hB (i : Fin 2) : ∀ᵐ z ∂M,
      b (pairSample i z.2) ⊥ ∉ V ∧ b (pairSample i z.2) ⊤ = q :=
    ((measurePreserving_pairSample (Q : Measure B) i).comp
      measurePreserving_snd).quasiMeasurePreserving.ae hb
  apply four_sample_meeting_constraint (P : Measure A) (Q : Measure B)
    {z | E 0 (a z)} {z | E 2 (a z)} {z | E 1 (b z)} {z | E 3 (b z)} R
    (1 / 10) (((P : Measure A).prod (Q : Measure B)) R) ha0 ha2 hb1 hb3 _ le_rfl
  filter_upwards [hA 0, hA 1, hB 0, hB 1] with z hA0 hA1 hB0 hB1 hz
  simp only [pairSample, Fin.isValue, ite_true, if_true, one_ne_zero, ite_false, if_false] at hA0 hA1 hB0 hB1
  let γ : Fin 4 → C(PathTime, X) := ![a z.1.1, b z.2.1, a z.1.2, b z.2.2]
  have hγstart : ∀ i, γ i ⊥ ∉ V := by
    intro i
    fin_cases i
    · exact hA0.1
    · exact hB0.1
    · exact hA1.1
    · exact hB1.1
  have hγend : ∀ i, γ i ⊤ ∈ V := by
    intro i
    fin_cases i
    · exact hA0.2 ▸ hp
    · exact hB0.2 ▸ hq
    · exact hA1.2 ▸ hp
    · exact hB1.2 ▸ hq
  let θ : Fin 4 → UnitAddCircle := fun i => χ (γ i (lastEntryTime (γ i) V))
  have hθarc : ∀ i, θ i ∈ rationalCircleArc (l i) (u i) := by
    intro i
    fin_cases i
    · exact hz.1.1
    · exact hz.2.1
    · exact hz.1.2
    · exact hz.2.2
  have hθorder : StrictMono (unitCircleCut ∘ θ) := by
    intro i j hij
    have hi := (hθarc i).2
    have hj := (hθarc j).1
    have hmid : (u i : ℝ) < (l j : ℝ) := by exact_mod_cast horder i j hij
    exact hi.trans (hmid.trans hj)
  obtain ⟨x, hxV, hxA, hxB⟩ := alternating_lastEntry_tails_intersect hcross V hV f
    hf hfinj hfdisk γ hγstart hγend (hA0.2.trans hA1.2.symm)
    (hB0.2.trans hB1.2.symm) θ hθorder
    (fun i => hχ _ (lastEntry_frontier (γ i) hV (hγstart i) (hγend i)))
  have htail (γ : C(PathTime, X)) : lastEntryTail γ V ⊆ range γ := image_subset_range _ _
  rcases hxA with hxA | hxA <;> rcases hxB with hxB | hxB
  · exact ⟨0, 0, x, hxV, htail _ hxA, htail _ hxB⟩
  · exact ⟨0, 1, x, hxV, htail _ hxA, htail _ hxB⟩
  · exact ⟨1, 0, x, hxV, htail _ hxA, htail _ hxB⟩
  · exact ⟨1, 1, x, hxV, htail _ hxA, htail _ hxB⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LastEntryLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual last-entry location law is atomless when the paths avoid
each fixed point of the collar boundary. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem lastEntryLaw_singleton_le_hit (μ : ProbabilityMeasure C(PathTime, X))
    (V : Set X) (hV : IsOpen V) (x : X) :
    (lastEntryLaw μ V : Measure X) {x} ≤ pathHitProbability μ x := by
  rw [lastEntryLaw, dif_pos (measurable_lastEntryLocation V hV).aemeasurable, ProbabilityMeasure.map_apply' μ
    (measurable_lastEntryLocation V hV).aemeasurable (measurableSet_singleton x)]
  apply measure_mono
  intro γ hγ
  exact ⟨lastEntryTime γ V, hγ⟩

omit [SecondCountableTopology X] in
theorem lastEntryLaw_boundary_support (μ : ProbabilityMeasure C(PathTime, X))
    (V : Set X) (hV : IsOpen V)
    (hend : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), γ ⊥ ∉ V ∧ γ ⊤ ∈ V) :
    (lastEntryLaw μ V : Measure X) (frontier V)ᶜ = 0 := by
  rw [lastEntryLaw, dif_pos (measurable_lastEntryLocation V hV).aemeasurable, ProbabilityMeasure.map_apply' μ
    (measurable_lastEntryLocation V hV).aemeasurable isClosed_frontier.measurableSet.compl]
  apply measure_mono_null (t := {γ | ¬ (γ ⊥ ∉ V ∧ γ ⊤ ∈ V)})
  · intro γ hγ hends
    exact hγ (lastEntry_frontier γ hV hends.1 hends.2)
  · exact ae_iff.mp hend

theorem lastEntryLaw_nullSingletonClass (μ : ProbabilityMeasure C(PathTime, X))
    (V : Set X) (hV : IsOpen V)
    (hend : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), γ ⊥ ∉ V ∧ γ ⊤ ∈ V)
    (havoid : ∀ x ∈ frontier V, pathHitProbability μ x = 0) :
    NullSingletonClass (lastEntryLaw μ V : Measure X) := by
  constructor
  intro x
  by_cases hx : x ∈ frontier V
  · exact le_antisymm ((lastEntryLaw_singleton_le_hit μ V hV x).trans_eq (havoid x hx)) bot_le
  · exact measure_mono_null (singleton_subset_iff.mpr hx)
      (lastEntryLaw_boundary_support μ V hV hend)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LastEntryCircleLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact probabilities of the collar arc events used in alternation. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [SecondCountableTopology X] in
theorem lastEntryCircleLaw_apply (μ : ProbabilityMeasure C(PathTime, X))
    (V : Set X) (hV : IsOpen V) (χ : X → UnitAddCircle) (hχ : Measurable χ)
    (l u : ℚ) :
    (lastEntryCircleLaw μ V χ : Measure UnitAddCircle) (rationalCircleArc l u) =
      (μ : Measure C(PathTime, X))
        {γ | χ (γ (lastEntryTime γ V)) ∈ rationalCircleArc l u} := by
  rw [lastEntryCircleLaw, dif_pos hχ.aemeasurable, ProbabilityMeasure.map_apply' _ hχ.aemeasurable
    (measurableSet_rationalCircleArc l u)]
  rw [lastEntryLaw, dif_pos (measurable_lastEntryLocation V hV).aemeasurable, ProbabilityMeasure.map_apply' _
    (measurable_lastEntryLocation V hV).aemeasurable
    (hχ (measurableSet_rationalCircleArc l u))]
  rfl

omit [SecondCountableTopology X] in
theorem lastEntryCircleLaw_nullSingletonClass (μ : ProbabilityMeasure C(PathTime, X))
    (V : Set X) (c : UnitAddCircle → X) (hc : MeasurableEmbedding c)
    (hs : (lastEntryLaw μ V : Measure X) (range c)ᶜ = 0)
    [NullSingletonClass (lastEntryLaw μ V : Measure X)] :
    NullSingletonClass (lastEntryCircleLaw μ V hc.invFun : Measure UnitAddCircle) := by
  rw [lastEntryCircleLaw, dif_pos hc.measurable_invFun.aemeasurable]
  exact circle_supported_map_nullSingletonClass (lastEntryLaw μ V) c hc hs

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_UncountableChoice
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable collar and arc choices can be made uniform on an uncountable set. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem exists_uncountable_common_choice {I K : Type*} [Countable K]
    (S : Set I) (hS : ¬ S.Countable) (P : I → K → Prop)
    (hP : ∀ i ∈ S, ∃ k, P i k) :
    ∃ k, ¬ {i | i ∈ S ∧ P i k}.Countable := by
  by_contra h
  push Not at h
  apply hS
  apply (countable_iUnion h).mono
  intro i hi
  obtain ⟨k, hk⟩ := hP i hi
  exact mem_iUnion.mpr ⟨k, hi, hk⟩

theorem exists_lt_of_uncountable {I : Type*} [LinearOrder I]
    {S : Set I} (hS : ¬ S.Countable) : ∃ i ∈ S, ∃ j ∈ S, i < j := by
  by_contra h
  push Not at h
  apply hS
  apply Set.Subsingleton.countable
  intro i hi j hj
  exact le_antisymm (h j hj i hi) (h i hi j hj)

theorem exists_common_four_circle_arcs {I : Type*} (S : Set I) (hS : ¬ S.Countable)
    (μ : I → ProbabilityMeasure UnitAddCircle)
    (hμ : ∀ i ∈ S, NullSingletonClass (μ i : Measure UnitAddCircle)) :
    ∃ l u : Fin 4 → ℚ,
      (∀ k, 0 < l k ∧ l k < u k ∧ u k < 1) ∧
      (∀ k j, k < j → u k < l j) ∧
      ¬ {i | i ∈ S ∧ ∀ k, (1 / 10 : ℝ≥0∞) <
        (μ i : Measure UnitAddCircle) (rationalCircleArc (l k) (u k))}.Countable := by
  let P (i : I) (a : (Fin 4 → ℚ) × (Fin 4 → ℚ)) : Prop :=
    (∀ k, 0 < a.1 k ∧ a.1 k < a.2 k ∧ a.2 k < 1 ∧
      (1 / 10 : ℝ≥0∞) < (μ i : Measure UnitAddCircle) (rationalCircleArc (a.1 k) (a.2 k))) ∧
    ∀ k j, k < j → a.2 k < a.1 j
  have hex : ∀ i ∈ S, ∃ a, P i a := by
    intro i hi
    have := hμ i hi
    obtain ⟨l, u, hmass, hord⟩ := exists_four_ordered_rational_circle_arcs (μ i)
    exact ⟨(l, u), hmass, hord⟩
  obtain ⟨⟨l, u⟩, h⟩ := exists_uncountable_common_choice S hS P hex
  have hne : {i | i ∈ S ∧ P i (l, u)}.Nonempty := by
    by_contra hn
    exact h (Set.not_nonempty_iff_eq_empty.mp hn ▸ countable_empty)
  obtain ⟨i, hi, hp⟩ := hne
  refine ⟨l, u, fun k => ⟨(hp.1 k).1, (hp.1 k).2.1, (hp.1 k).2.2.1⟩, hp.2, ?_⟩
  intro hc
  apply h
  apply hc.mono
  intro i hi
  exact ⟨hi.1, fun k => (hi.2.1 k).2.2.2⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableCodedCollarLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-collar argument with the varying base-code spaces retained.
Earlier-law constraints change those spaces during the transfinite recursion. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [LinearOrder I] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem countable_of_uniformly_small_coded_collar_meetings
    (hcross : UnitDiskAlternatingContinua)
    (S : Set I) (V : Set X) (hV : IsOpen V) (f : X → ℂ)
    (hf : ContinuousOn f (closure V)) (hfinj : InjOn f (closure V))
    (hfdisk : MapsTo f (closure V) (Metric.closedBall 0 1))
    (χ : X → UnitAddCircle) (hχmeas : Measurable χ)
    (hχ : ∀ x ∈ frontier V, f x = standardCirclePoint (χ x))
    (Ω : I → Type*) [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, ProbabilityMeasure (Ω i)) (a : ∀ i, Ω i → C(PathTime, X))
    (ha : ∀ i, Measurable (a i)) (p : I → X) (hp : ∀ i ∈ S, p i ∈ V)
    (hends : ∀ i ∈ S, ∀ᵐ z ∂(μ i : Measure (Ω i)), a i z ⊥ ∉ V ∧ a i z ⊤ = p i)
    (hatom : ∀ i ∈ S,
      NullSingletonClass (lastEntryCircleLaw ((μ i).map (f := a i) (ha i).aemeasurable) V χ : Measure UnitAddCircle))
    (hsmall : ∀ i ∈ S, ∀ j ∈ S, i < j →
      4 * ((μ i : Measure (Ω i)).prod (μ j : Measure (Ω j)))
        {z | ∃ x ∈ V, x ∈ range (a i z.1) ∧ x ∈ range (a j z.2)} <
          (1 / 10 : ℝ≥0∞) ^ 4) : S.Countable := by
  by_contra hS
  obtain ⟨l, u, _, horder, hunc⟩ := exists_common_four_circle_arcs S hS
    (fun i => lastEntryCircleLaw ((μ i).map (f := a i) (ha i).aemeasurable) V χ) hatom
  obtain ⟨i, hi, j, hj, hij⟩ := exists_lt_of_uncountable hunc
  have hm (i : I) (hi : i ∈ S ∧ ∀ k, (1 / 10 : ℝ≥0∞) <
      (lastEntryCircleLaw ((μ i).map (f := a i) (ha i).aemeasurable) V χ : Measure UnitAddCircle)
        (rationalCircleArc (l k) (u k))) (k : Fin 4) :
      (1 / 10 : ℝ≥0∞) ≤ (μ i : Measure (Ω i))
        {z | χ (a i z (lastEntryTime (a i z) V)) ∈ rationalCircleArc (l k) (u k)} := by
    have h := (hi.2 k).le
    rw [lastEntryCircleLaw_apply _ V hV χ hχmeas] at h
    have hs : MeasurableSet {γ : C(PathTime, X) |
        χ (γ (lastEntryTime γ V)) ∈ rationalCircleArc (l k) (u k)} := by
      exact (hχmeas.comp (measurable_lastEntryLocation V hV))
        (measurableSet_rationalCircleArc _ _)
    rw [ProbabilityMeasure.map_apply' (μ i) (ha i).aemeasurable hs] at h
    exact h
  have hlow := collar_alternation_probability hcross V hV f hf hfinj hfdisk χ hχ
    (μ i) (μ j) (a i) (a j) (p i) (p j) (hp i hi.1) (hp j hj.1)
    (hends i hi.1) (hends j hj.1) l u horder (hm i hi 0) (hm i hi 2)
    (hm j hj 1) (hm j hj 3)
  exact (not_lt_of_ge hlow) (hsmall i hi.1 j hj.1 hij)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LocalizedSquareMass
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local square-density estimates for point avoidance. The energy of a
shrinking family tends to zero when its intersection is reference-null. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

theorem localized_square_mass_bound (σ : Measure X) {g : X → ℝ≥0∞}
    (hg : Measurable g) {A : Set X} (hA : MeasurableSet A) :
    ((σ.withDensity g) A) ^ 2 ≤ (∫⁻ x in A, g x ^ 2 ∂σ) * σ A := by
  have h := mass_le_densityMassBound (σ.restrict A) hg
    (le_refl (∫⁻ x, g x ^ 2 ∂σ.restrict A))
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  rw [withDensity_apply _ hA]
  apply (pow_le_pow_left' h 2).trans_eq
  rw [densityMassBound, mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

theorem tendsto_local_square_energy_zero (σ : Measure X) {g : X → ℝ≥0∞}
    (hgfin : (∫⁻ x, g x ^ 2 ∂σ) < ∞)
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n)) (hanti : Antitone A)
    (hnull : σ (⋂ n, A n) = 0) :
    Tendsto (fun n => ∫⁻ x in A n, g x ^ 2 ∂σ) atTop (𝓝 0) := by
  let ν := σ.withDensity (fun x => g x ^ 2)
  have hfin : ν univ < ∞ := by
    rw [show ν = σ.withDensity (fun x => g x ^ 2) from rfl,
      withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    exact hgfin
  have hν : IsFiniteMeasure ν := ⟨hfin⟩
  have hz : ν (⋂ n, A n) = 0 := withDensity_absolutelyContinuous σ _ hnull
  have ht := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (hA n).nullMeasurableSet) hanti ⟨0, measure_ne_top ν _⟩
  rw [hz] at ht
  simpa only [Function.comp_def, ν, withDensity_apply _ (hA _)] using ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ShrinkingOccupationEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mean occupation has no mass off the physical domain. Its square density
therefore has vanishing energy on collars shrinking to a dust fibre. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem square_density_null_of_density_null {Y : Type*} [MeasurableSpace Y]
    (σ : Measure Y) (g : Y → ℝ≥0∞) (hg : Measurable g)
    {A : Set Y} (hA : MeasurableSet A) (hz : (σ.withDensity g) A = 0) :
    (σ.withDensity (fun x => g x ^ 2)) A = 0 := by
  rw [withDensity_apply _ hA] at hz ⊢
  have he := (lintegral_eq_zero_iff hg).mp hz
  apply (lintegral_eq_zero_iff (hg.pow_const 2)).mpr
  filter_upwards [he] with x hx
  change g x ^ 2 = 0
  have hx' : g x = 0 := hx
  rw [hx', zero_pow (by decide : (2 : ℕ) ≠ 0)]

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem meanCodeOccupation_compl (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (P : ProbabilityMeasure (BasePathCode d)) :
    meanCodeOccupation d P d.physicalDomainᶜ = 0 := by
  rw [meanCodeOccupation_apply d hU P hG.measurableSet.compl]
  have hz (Γ : BasePathCode d) : baseCodeOccupation d Γ d.physicalDomainᶜ = 0 :=
    dyadicPhysicalOccupation_compl d.domainEquiv hG d.basePoint (baseCodePhysicalPath d Γ)
  simp only [hz, lintegral_zero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_OccupationNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square occupation density has arbitrarily small mass in quotient
neighborhoods of a dust point, because its entire fibre lies off the domain. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem exists_open_small_occupation_energy (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Continuous π)
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (P : ProbabilityMeasure (BasePathCode d)) (σ : Measure Y) (g : Y → ℝ≥0∞)
    (hg : Measurable g) (hocc : meanCodeOccupation d P = σ.withDensity g)
    (henergy : (∫⁻ y, g y ^ 2 ∂σ) < ∞) (p : X) (hp : p ∈ d.dust)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ O : Set X, IsOpen O ∧ p ∈ O ∧ (∫⁻ y in π ⁻¹' O, g y ^ 2 ∂σ) < ε := by
  let ν : Measure Y := σ.withDensity (fun y => g y ^ 2)
  let : IsFiniteMeasure ν := ⟨by
    simpa only [ν, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using henergy⟩
  have hnull : ν d.physicalDomainᶜ = 0 :=
    square_density_null_of_density_null σ g hg hG.measurableSet.compl
      (hocc ▸ meanCodeOccupation_compl d hU hG P)
  have hfiber : π ⁻¹' {p} ⊆ d.physicalDomainᶜ := by
    intro y hy hyG
    have hyp : π y = p := hy
    have hyU := (d.domainEquiv ⟨y, hyG⟩).property
    rw [he ⟨y, hyG⟩, hyp] at hyU
    exact disjoint_left.mp hdisj hyU hp
  have hz : ν.map π {p} = 0 := by
    rw [Measure.map_apply hπ.measurable (measurableSet_singleton p)]
    exact measure_mono_null hfiber hnull
  obtain ⟨O, hpO, hO, hm⟩ := ({p} : Set X).exists_isOpen_lt_of_lt (μ := ν.map π)
    ε (hz ▸ hε)
  refine ⟨O, hO, hpO (mem_singleton p), ?_⟩
  rwa [Measure.map_apply hπ.measurable hO.measurableSet,
    withDensity_apply _ (hπ.measurable hO.measurableSet)] at hm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LocalMassVanishing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic area bound and a linear occupation lower bound force a
point-hit probability to vanish. This is the local L² estimate. -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem local_mass_vanishing {X : Type*} [MeasurableSpace X]
    (σ : Measure X) {g : X → ℝ≥0∞} (hg : Measurable g)
    (hgfin : (∫⁻ x, g x ^ 2 ∂σ) < ∞)
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n)) (hanti : Antitone A)
    (hnull : σ (⋂ n, A n) = 0) (r : ℕ → ℝ≥0) (hr : ∀ n, 0 < r n)
    (K p : ℝ≥0∞) (hK : K ≠ ∞)
    (harea : ∀ n, σ (A n) ≤ K * (r n : ℝ≥0∞) ^ 2)
    (hmass : ∀ n, (r n : ℝ≥0∞) * p ≤ (σ.withDensity g) (A n)) : p = 0 := by
  have hb (n : ℕ) : p ^ 2 ≤ (∫⁻ x in A n, g x ^ 2 ∂σ) * K := by
    have hmul : p ^ 2 * (r n : ℝ≥0∞) ^ 2 ≤
        ((∫⁻ x in A n, g x ^ 2 ∂σ) * K) * (r n : ℝ≥0∞) ^ 2 := by
      calc
        _ = ((r n : ℝ≥0∞) * p) ^ 2 := by rw [mul_pow, mul_comm]
        _ ≤ ((σ.withDensity g) (A n)) ^ 2 := pow_le_pow_left' (hmass n) 2
        _ ≤ (∫⁻ x in A n, g x ^ 2 ∂σ) * σ (A n) := localized_square_mass_bound σ hg (hA n)
        _ ≤ (∫⁻ x in A n, g x ^ 2 ∂σ) * (K * (r n : ℝ≥0∞) ^ 2) :=
          mul_le_mul' le_rfl (harea n)
        _ = _ := (mul_assoc _ _ _).symm
    exact (ENNReal.mul_le_mul_iff_left
      (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr (hr n).ne'))
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)).mp hmul
  have ht := ENNReal.Tendsto.mul_const
    (tendsto_local_square_energy_zero σ hgfin A hA hanti hnull) (Or.inr hK)
  have hp : p ^ 2 ≤ 0 := by
    have ht' : Tendsto (fun n => (∫⁻ x in A n, g x ^ 2 ∂σ) * K) atTop (𝓝 0) := by
      simpa using ht
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ht' (Eventually.of_forall hb)
  simpa using (le_antisymm hp bot_le : p ^ 2 = 0)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PointHitOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A visit to a fixed interior point forces physical occupation of each
surrounding region before the path can end outside it. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
theorem point_hit_occupation_lower_bound
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Continuous π)
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (p : Y) (hp : p ∈ d.physicalDomain)
    (O : Set X) (hO : IsOpen O) (hOU : closure O ⊆ d.quotientDomain) (hpO : π p ∈ O)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδfin : δ ≠ ∞)
    (hsep : ∀ b ∉ π ⁻¹' O, δ ≤ edist p b)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hend : γ.val ⊤ ∉ O) (hhit : π p ∈ range γ.val) :
    δ ≤ dyadicPhysicalOccupation d.domainEquiv d.basePoint γ (π ⁻¹' O) := by
  obtain ⟨t, ht⟩ := hhit
  have htt : t < ⊤ := lt_top_iff_ne_top.mpr (by
    intro h
    subst t
    exact hend (ht ▸ hpO))
  let ρ := affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ htt
  have hstart : ρ.val ⊥ = π p := by
    change γ.val (affinePathTime t ⊤ ⊥) = π p
    rwa [affinePathTime_zero]
  have hend' : ρ.val ⊤ ∉ O := by
    change γ.val (affinePathTime t ⊤ ⊤) ∉ O
    rwa [affinePathTime_one]
  have hpre : (d.domainEquiv.symm
      ⟨ρ.val ⊥, hOU (subset_closure (hstart ▸ hpO))⟩).val = p := by
    have hs : (⟨ρ.val ⊥, hOU (subset_closure (hstart ▸ hpO))⟩ : d.quotientDomain) =
        d.domainEquiv ⟨p, hp⟩ := Subtype.ext (hstart.trans (he ⟨p, hp⟩).symm)
    rw [hs, d.domainEquiv.symm_apply_apply]
  let w : Y → ℝ≥0∞ := (π ⁻¹' O).indicator (fun _ => δ⁻¹)
  have hw : Measurable w := measurable_const.indicator (hO.preimage hπ).measurableSet
  have hpay := first_exit_indicator_cost_lower_bound d hU π hπ he O hO hOU {p} hδ hδfin
    (by intro a ha b hb; simpa only [mem_singleton_iff.mp ha] using hsep b hb)
    ρ (hstart ▸ hpO) hend' (by exact hpre) (fun _ => 0)
  have hfull : 1 ≤ physicalTollCost d w (fun _ => 0) γ :=
    hpay.trans (physicalTollCost_affine_le d hU γ htt w hw (fun _ => 0))
  have hmass : 1 ≤ δ⁻¹ *
      dyadicPhysicalOccupation d.domainEquiv d.basePoint γ (π ⁻¹' O) := by
    simpa only [physicalTollCost, boundaryToll, tsum_zero, add_zero, w,
      lintegral_indicator_const (hO.preimage hπ).measurableSet] using hfull
  calc
    δ = δ * 1 := (mul_one _).symm
    _ ≤ δ * (δ⁻¹ * dyadicPhysicalOccupation d.domainEquiv d.basePoint γ (π ⁻¹' O)) :=
      mul_le_mul' le_rfl hmass
    _ = _ := by rw [← mul_assoc, ENNReal.mul_inv_cancel hδ hδfin, one_mul]

variable [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem mean_occupation_ge_point_hit
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Continuous π)
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (p : Y) (hp : p ∈ d.physicalDomain)
    (O : Set X) (hO : IsOpen O) (hOU : closure O ⊆ d.quotientDomain) (hpO : π p ∈ O)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδfin : δ ≠ ∞)
    (hsep : ∀ b ∉ π ⁻¹' O, δ ≤ edist p b)
    (P : ProbabilityMeasure (BasePathCode d)) (hend : d.target ∉ O) :
    δ * pathHitProbability (codePathLaw d P) (π p) ≤ meanCodeOccupation d P (π ⁻¹' O) := by
  let H : Set (BasePathCode d) := {Γ | π p ∈ range (codePath d Γ)}
  have hH : MeasurableSet H :=
    (measurable_codePath d) (isClosed_paths_hitting (π p)).measurableSet
  have heq : pathHitProbability (codePathLaw d P) (π p) = (P : Measure _) H :=
    pathHitProbability_codePathLaw d P (π p)
  rw [heq, ← lintegral_indicator_const hH δ]
  rw [meanCodeOccupation, Measure.bind_apply (hO.preimage hπ).measurableSet
    (measurable_baseCodeOccupation d hU).aemeasurable]
  apply lintegral_mono
  intro Γ
  by_cases hΓ : Γ ∈ H
  · rw [indicator_of_mem hΓ]
    apply point_hit_occupation_lower_bound d hU π hπ he p hp O hO hOU hpO hδ hδfin hsep
      (baseCodePhysicalPath d Γ)
    · change Γ.val.1 ⊤ ∉ O
      rw [Γ.property.2.1.2.1]
      exact hend
    · exact hΓ
  · simp only [indicator_of_notMem hΓ]
    exact bot_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereChartInverseControl
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local inverse Lipschitz control for the actual fixed finite sphere chart.
The chosen linear coordinates need not be orthonormal. -/

open Set Function Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

theorem linear_stereo_inverse_control (v : RoundAmbient) (hv : ‖v‖ = 1)
    (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    ∃ (L : ℝ≥0) (W : Set RoundAmbient), W ∈ 𝓝 (stereoInvFunAux v (A z : RoundAmbient)) ∧
      ∀ w : ℂ, stereoInvFunAux v (A w : RoundAmbient) ∈ W →
        dist w z ≤ L * dist (stereoInvFunAux v (A w : RoundAmbient))
          (stereoInvFunAux v (A z : RoundAmbient)) := by
  let F : ℂ → RoundAmbient := fun w => stereoInvFunAux v (A w : RoundAmbient)
  let g : RoundAmbient → ℂ := fun x => A.symm (stereoToFun v x)
  have hleft (w : ℂ) : g (F w) = w := by
    change A.symm (stereoToFun v (stereoInvFun hv (A w))) = w
    rw [stereo_right_inv, A.symm_apply_apply]
  have hx : ‖F z‖ = 1 := mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv (A z).property)
  have hneq : innerSL ℝ v (F z) ≠ 1 := by
    intro h
    have he : v = F z := (inner_eq_one_iff_of_norm_eq_one hv hx).mp h
    exact stereoInvFun_ne_north_pole hv (A z) (Subtype.ext he.symm)
  have hopen : IsOpen {x : RoundAmbient | innerSL ℝ v x ≠ 1} :=
    (isClosed_eq (innerSL ℝ v).continuous continuous_const).isOpen_compl
  have hg : ContDiffAt ℝ 1 g (F z) :=
    A.symm.contDiff.contDiffAt.comp (F z)
      ((contDiffOn_stereoToFun (n := 1)).contDiffAt (hopen.mem_nhds hneq))
  obtain ⟨L, W, hW, hL⟩ := hg.exists_lipschitzOnWith
  refine ⟨L, W, hW, fun w hw => ?_⟩
  simpa only [hleft] using hL.dist_le_mul (F w) hw (F z) (mem_of_mem_nhds hW)

theorem finite_sphere_chart_inverse_control (z : ℂ) :
    ∃ (L : ℝ≥0) (W : Set RoundAmbient),
      W ∈ 𝓝 (roundSphereEquiv (z : Sphere) : RoundAmbient) ∧
      ∀ w : ℂ, (roundSphereEquiv (w : Sphere) : RoundAmbient) ∈ W →
        dist w z ≤ L * dist (roundSphereEquiv (w : Sphere) : RoundAmbient)
          (roundSphereEquiv (z : Sphere) : RoundAmbient) := by
  classical
  simp only [roundSphereEquiv, onePointEquivSphereOfFinrankEq, Homeomorph.trans_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  apply linear_stereo_inverse_control
  simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalBallArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic local area growth for the fixed physical sphere metric, at
finite points. This compares its actual chart with the area chart. -/

open Set Filter Function Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r01fbe5_2 : BorelSpace Sphere := ⟨rfl⟩
theorem sphericalArea_singleton (p : Sphere) : sphericalArea {p} = 0 := by
  rw [sphericalArea, Measure.map_apply OnePoint.continuous_coe.measurable
    (measurableSet_singleton p)]
  cases p using OnePoint.rec with
  | infty => simp
  | coe z =>
    have he : ((↑) : ℂ → Sphere) ⁻¹' {(z : Sphere)} = {z} := by
      ext w
      simp
    rw [he]
    exact withDensity_absolutelyContinuous volume _ (measure_singleton z)

theorem sphericalAreaDensity_le_four (z : ℂ) : sphericalAreaDensity z ≤ 4 := by
  rw [sphericalAreaDensity, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ ^ 2)]

theorem exists_small_spherical_ball_area_bound (z : ℂ) :
    ∃ (R : ℝ), 0 < R ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧
      ∀ r : ℝ≥0, (r : ℝ) < R →
        sphericalArea (ball (z : Sphere) r) ≤ K * (r : ℝ≥0∞) ^ 2 := by
  obtain ⟨L, W, hW, hL⟩ := finite_sphere_chart_inverse_control z
  have hc : Continuous (fun p : Sphere => (roundSphereEquiv p : RoundAmbient)) :=
    continuous_subtype_val.comp roundSphereEquiv.continuous
  obtain ⟨R, hR, hRW⟩ := Metric.mem_nhds_iff.mp (hc.continuousAt.preimage_mem_nhds hW)
  let K : ℝ≥0∞ := 4 * (↑(L + 1) : ℝ≥0∞) ^ 2 * NNReal.pi
  refine ⟨R, hR, K, by dsimp [K]; finiteness, ?_⟩
  intro r hr
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' ball (z : Sphere) r
  have hAB : A ⊆ closedBall z ((L + 1 : ℝ≥0) * r) := by
    intro w hw
    have hwR : (w : Sphere) ∈ ball (z : Sphere) R :=
      (ball_subset_ball hr.le) hw
    have hb := hL w (hRW hwR)
    have hd : dist (w : Sphere) (z : Sphere) < r := hw
    change dist w z ≤ (L + 1 : ℝ≥0) * r
    calc
      dist w z ≤ L * dist (w : Sphere) (z : Sphere) := hb
      _ ≤ L * r := mul_le_mul_of_nonneg_left hd.le L.coe_nonneg
      _ ≤ (L + 1 : ℝ≥0) * r :=
        mul_le_mul_of_nonneg_right (by simp) r.coe_nonneg
  rw [sphericalArea, Measure.map_apply OnePoint.continuous_coe.measurable measurableSet_ball,
    withDensity_apply _ (OnePoint.continuous_coe.measurable measurableSet_ball)]
  calc
    _ ≤ ∫⁻ _ in A, (4 : ℝ≥0∞) := by
      apply lintegral_mono
      intro w
      exact (ENNReal.ofReal_le_ofReal (sphericalAreaDensity_le_four w)).trans_eq (by norm_num)
    _ = 4 * volume A := by simp
    _ ≤ 4 * volume (closedBall z ((L + 1 : ℝ≥0) * r)) :=
      mul_le_mul' le_rfl (measure_mono hAB)
    _ = K * (r : ℝ≥0∞) ^ 2 := by
      rw [Complex.volume_closedBall]
      rw [show ENNReal.ofReal ((L + 1 : ℝ≥0) * r) =
        (↑(L + 1) : ℝ≥0∞) * ↑r from by
          rw [← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul], mul_pow]
      dsimp [K]
      ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientInteriorBalls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A physical ball compactly contained in the domain descends to an open
quotient neighborhood with exactly that ball as its full inverse image. -/

open Set Function Metric Topology
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem component_collapse_preimage_image_subset_domain
    (G : Set Sphere) (π : Sphere → Sphere)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (S : Set Sphere) (hS : S ⊆ G) : π ⁻¹' (π '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (hr y x).mp hxy with h | ⟨hg, _⟩
    · exact h ▸ hy
    · exact (hg (hS hy)).elim
  · exact fun hx => mem_image_of_mem π hx

variable [MeasurableSpace C(PathTime, Sphere)]

theorem quotient_interior_ball
    (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (p : Sphere) {r : ℝ} (hrpos : 0 < r)
    (hball : closedBall p r ⊆ d.physicalDomain) :
    IsOpen (π '' ball p r) ∧ closure (π '' ball p r) ⊆ d.quotientDomain ∧
      π ⁻¹' (π '' ball p r) = ball p r ∧ π p ∈ π '' ball p r := by
  have hsat := component_collapse_preimage_image_subset_domain d.physicalDomain π hr
    (ball p r) (ball_subset_closedBall.trans hball)
  have hopen : IsOpen (π '' ball p r) :=
    (hclosed.isQuotientMap hπ hsurj).isOpen_preimage.mp (by rw [hsat]; exact isOpen_ball)
  refine ⟨hopen, ?_, hsat, mem_image_of_mem π (mem_ball_self hrpos)⟩
  apply (closure_minimal (image_mono ball_subset_closedBall)
    (hclosed _ isClosed_closedBall)).trans
  rintro x ⟨y, hy, rfl⟩
  rw [← he ⟨y, hball hy⟩]
  exact (d.domainEquiv ⟨y, hball hy⟩).property

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FinitePointAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An L² occupation density makes every fixed finite physical-domain
point polar for a code law whose terminal point lies outside the domain. -/

open Set Filter Function Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_3 : BorelSpace Sphere := ⟨rfl⟩
theorem finite_domain_point_avoided
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hend : d.target ∉ d.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity g)
    (henergy : (∫⁻ x, g x ^ 2 ∂sphericalArea) < ∞)
    (z : ℂ) (hz : (z : Sphere) ∈ d.physicalDomain) :
    pathHitProbability (codePathLaw d P) (π (z : Sphere)) = 0 := by
  obtain ⟨RG, hRG, hballG⟩ := Metric.mem_nhds_iff.mp (hG.mem_nhds hz)
  obtain ⟨RA, hRA, K, hK, harea⟩ := exists_small_spherical_ball_area_bound z
  let q : ℝ := min RG RA / 2
  have hq : 0 < q := by dsimp [q] <;> positivity
  have hqG : q < RG := by dsimp [q] <;> linarith [min_le_left RG RA]
  have hqA : q < RA := by dsimp [q] <;> linarith [min_le_right RG RA]
  let r : ℕ → ℝ≥0 := fun n => ⟨q / ((n : ℝ) + 1), by positivity⟩
  have hrpos (n : ℕ) : 0 < r n := by change 0 < q / ((n : ℝ) + 1); positivity
  have hrq (n : ℕ) : (r n : ℝ) ≤ q := by
    change q / ((n : ℝ) + 1) ≤ q
    exact div_le_self hq.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hanti : Antitone (fun n => (r n : ℝ)) := by
    intro i j hij
    change q / ((j : ℝ) + 1) ≤ q / ((i : ℝ) + 1)
    apply div_le_div_of_nonneg_left hq.le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have ht : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => q / ((n : ℝ) + 1)) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul q
  let A : ℕ → Set Sphere := fun n => ball (z : Sphere) (r n)
  have hAnull : sphericalArea (⋂ n, A n) = 0 := by
    apply measure_mono_null _ (sphericalArea_singleton (z : Sphere))
    intro x hx
    have hd : dist x (z : Sphere) ≤ 0 := ge_of_tendsto ht (Eventually.of_forall fun n =>
      (show dist x (z : Sphere) < r n from mem_iInter.mp hx n).le)
    exact dist_le_zero.mp hd
  apply local_mass_vanishing sphericalArea hg henergy A (fun _ => measurableSet_ball)
    (fun i j hij => ball_subset_ball (hanti hij)) hAnull r hrpos K _ hK
  · intro n
    exact harea (r n) ((hrq n).trans_lt hqA)
  · intro n
    have hball : closedBall (z : Sphere) (r n) ⊆ d.physicalDomain := by
      apply Subset.trans _ hballG
      intro x hx
      exact (mem_closedBall.mp hx).trans_lt ((hrq n).trans_lt hqG)
    obtain ⟨hO, hOU, hpre, hpO⟩ := quotient_interior_ball d π hπ hclosed hsurj hr he
      (z : Sphere) (show 0 < (r n : ℝ) from hrpos n) hball
    have hb := mean_occupation_ge_point_hit d hU π hπ he (z : Sphere) hz
      (π '' ball (z : Sphere) (r n)) hO hOU hpO
      (ENNReal.coe_ne_zero.mpr (hrpos n).ne') ENNReal.coe_ne_top
      (δ := (r n : ℝ≥0∞)) (fun b hb => ?_) P
      (fun hh => hend (hOU (subset_closure hh)))
    · rw [hocc, hpre] at hb
      exact hb
    · rw [hpre] at hb
      have hd : (r n : ℝ) ≤ dist b (z : Sphere) := le_of_not_gt hb
      simpa only [edist_dist, dist_comm, ENNReal.ofReal_coe_nnreal] using
        ENNReal.ofReal_le_ofReal hd

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalLastEntryLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Last-entry distributions on physical collar boundaries have no atoms. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_4 : BorelSpace Sphere := ⟨rfl⟩
theorem physical_lastEntryLaw_nullSingletonClass
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hend : d.target ∉ d.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity g)
    (henergy : (∫⁻ x, g x ^ 2 ∂sphericalArea) < ∞)
    (V : Set Sphere) (hV : IsOpen V) (hfront : frontier V ⊆ d.quotientDomain)
    (hinf : π OnePoint.infty ∉ frontier V)
    (hstart : Disjoint d.anchor V) (htarget : d.target ∈ V) :
    NullSingletonClass (lastEntryLaw (codePathLaw d P) V : Measure Sphere) := by
  apply lastEntryLaw_nullSingletonClass (codePathLaw d P) V hV
  · change ∀ᵐ γ ∂((P : Measure (BasePathCode d)).map (codePath d)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V
    apply (ae_map_iff (measurable_codePath d).aemeasurable
      (((continuous_eval_const ⊥).measurable hV.measurableSet).compl.inter
        ((continuous_eval_const ⊤).measurable hV.measurableSet))).mpr
    exact Eventually.of_forall fun Γ =>
      ⟨fun hv => disjoint_left.mp hstart Γ.property.2.1.1 hv,
       by change Γ.val.1 ⊤ ∈ V; rw [Γ.property.2.1.2.1]; exact htarget⟩
  · intro x hx
    let p : d.physicalDomain := d.domainEquiv.symm ⟨x, hfront hx⟩
    have hp : π p.val = x := by
      rw [← he p]
      exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨x, hfront hx⟩)
    have hpfin : p.val ≠ OnePoint.infty := by
      intro h
      apply hinf
      simpa only [← hp, h] using hx
    cases heq : p.val using OnePoint.rec with
    | infty => exact (hpfin heq).elim
    | coe z =>
      have hz : (z : Sphere) ∈ d.physicalDomain := heq ▸ p.property
      have hzx : π (z : Sphere) = x := heq ▸ hp
      rw [← hzx]
      exact finite_domain_point_avoided d hU hG π hπ hclosed hsurj hr he hend P g hg
        hocc henergy z hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableMeetingBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Once diffuse meetings are excluded, independence bounds the remaining
meeting event by the sum of products of the point-hit probabilities. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]
  [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
theorem code_pair_meeting_bound
    (d e : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (Q : ProbabilityMeasure (BasePathCode e)) (B D : Set X) (hD : D.Countable)
    (hcontacts : ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      range p.1.val.1 ∩ range p.2.val.1 ∩ B ⊆ D) :
    ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {p | (range p.1.val.1 ∩ range p.2.val.1 ∩ B).Nonempty} ≤
        ∑' x : ↥(D ∩ B), codeHitProbability d P x.val * codeHitProbability e Q x.val := by
  let : Countable ↥(D ∩ B) := (hD.mono inter_subset_left).to_subtype
  let A (x : ↥(D ∩ B)) : Set (BasePathCode d × BasePathCode e) :=
    {Γ | x.val ∈ range Γ.val.1} ×ˢ {Δ | x.val ∈ range Δ.val.1}
  have hsub : {p | (range p.1.val.1 ∩ range p.2.val.1 ∩ B).Nonempty} ≤ᵐ[
      (P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))] ⋃ x, A x := by
    filter_upwards [hcontacts] with p hp hmeet
    obtain ⟨x, hx⟩ := hmeet
    exact mem_iUnion.mpr ⟨⟨x, hp hx, hx.2⟩, hx.1⟩
  apply (measure_mono_ae hsub).trans
  apply (measure_iUnion_le A).trans
  apply le_of_eq
  apply tsum_congr
  intro x
  exact Measure.prod_prod _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TwoTerminalHitBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two distinguished terminal hits and the remaining square tails control
the sum appearing in the independent dust-meeting bound. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

theorem two_terminal_hit_sum_bound {A : Type*} [Countable A]
    (a b : A → ℝ≥0∞) (p q : A) (ha : a p ≤ 1) (hb : b q ≤ 1) :
    (∑' x, a x * b x) ≤ b p + a q +
      countingSquareNorm (awayFromTwo p q a) * countingSquareNorm (awayFromTwo p q b) := by
  have hpoint (x : A) : a x * b x ≤
      (if x = p then b p else 0) + (if x = q then a q else 0) +
        awayFromTwo p q a x * awayFromTwo p q b x := by
    by_cases hxp : x = p
    · subst x
      have h : a p * b p ≤ b p := by simpa using mul_le_mul' ha (le_refl (b p))
      simpa only [awayFromTwo, true_or, ite_true, if_true, zero_mul, add_zero] using
        h.trans (le_add_right le_rfl)
    · by_cases hxq : x = q
      · subst x
        have h : a q * b q ≤ a q := by simpa using mul_le_mul' (le_refl (a q)) hb
        simpa [awayFromTwo, hxp] using h
      · simp [awayFromTwo, hxp, hxq]
  calc
    (∑' x, a x * b x) ≤ ∑' x, ((if x = p then b p else 0) + (if x = q then a q else 0) +
        awayFromTwo p q a x * awayFromTwo p q b x) := ENNReal.tsum_le_tsum hpoint
    _ = b p + a q + ∑' x, awayFromTwo p q a x * awayFromTwo p q b x := by
      rw [ENNReal.tsum_add, ENNReal.tsum_add]
      simp
    _ ≤ _ := add_le_add le_rfl (tsum_mul_le_countingSquareNorm _ _)

theorem two_terminal_hit_sum_le {A : Type*} [Countable A]
    (a b : A → ℝ≥0∞) (p q : A) (ha : a p ≤ 1) (hb : b q ≤ 1)
    {δ : ℝ≥0∞} (hab : b p ≤ δ) (hba : a q ≤ δ)
    (hatail : countingSquareNorm (awayFromTwo p q a) ≤ δ)
    (hbtail : countingSquareNorm (awayFromTwo p q b) ≤ δ) :
    (∑' x, a x * b x) ≤ 2 * δ + δ ^ 2 := by
  apply (two_terminal_hit_sum_bound a b p q ha hb).trans
  calc
    _ ≤ δ + δ + δ * δ := add_le_add (add_le_add hab hba) (mul_le_mul' hatail hbtail)
    _ = 2 * δ + δ ^ 2 := by rw [← two_mul, pow_two]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PuncturedHitProduct
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two terminal contributions are controlled by the opposite punctured
square norm. No separate small individual-hit hypothesis is needed. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

theorem countingSquareNorm_point_le {S : Type*} (m : S → ℝ≥0∞) (x : S) :
    m x ≤ countingSquareNorm m := by
  have h := countingSquareNorm_comp_injective m (fun _ : Unit => x)
    (fun _ _ _ => Subsingleton.elim _ _)
  simpa [countingSquareNorm, Function.comp_def, tsum_fintype,
    ← ENNReal.rpow_natCast_mul] using h

theorem punctured_hit_product_sum_le {S : Type*} [Countable S]
    (a b : S → ℝ≥0∞) (U : Set S) (p q : S) (hp : p ∈ U) (hq : q ∈ U)
    (hpq : p ≠ q) (ha : a p ≤ 1) (hb : b q ≤ 1) {δ : ℝ≥0∞}
    (hatail : countingSquareNorm (puncturedHit a U p) ≤ δ)
    (hbtail : countingSquareNorm (puncturedHit b U q) ≤ δ) :
    (∑' x, (if x ∈ U then a x else 0) * (if x ∈ U then b x else 0)) ≤
      2 * δ + δ ^ 2 := by
  apply two_terminal_hit_sum_le
    (fun x => if x ∈ U then a x else 0) (fun x => if x ∈ U then b x else 0) p q
  · simpa [hp] using ha
  · simpa [hq] using hb
  · have h := (countingSquareNorm_point_le (puncturedHit b U q) p).trans hbtail
    simpa [puncturedHit, hp, hpq] using h
  · have h := (countingSquareNorm_point_le (puncturedHit a U p) q).trans hatail
    simpa [puncturedHit, hq, hpq.symm] using h
  · apply (countingSquareNorm_mono (b := puncturedHit a U p) ?_).trans hatail
    intro x
    by_cases hx : x ∈ U <;> by_cases hxp : x = p <;> by_cases hxq : x = q <;>
      simp [awayFromTwo, puncturedHit, hx, hxp, hxq]
  · apply (countingSquareNorm_mono (b := puncturedHit b U q) ?_).trans hbtail
    intro x
    by_cases hx : x ∈ U <;> by_cases hxp : x = p <;> by_cases hxq : x = q <;>
      simp [awayFromTwo, puncturedHit, hx, hxp, hxq]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CodeDustMeetingBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative dust meeting estimate for the actual two code laws. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
theorem code_dust_meeting_bound
    (d e : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (Q : ProbabilityMeasure (BasePathCode e)) (U D : Set X) (hD : D.Countable)
    (hcontacts : ∀ᵐ z ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      range z.1.val.1 ∩ range z.2.val.1 ∩ d.dust ⊆ D)
    (p q : X) (hp : p ∈ D ∩ (U ∩ d.dust)) (hq : q ∈ D ∩ (U ∩ d.dust)) (hpq : p ≠ q)
    {δ : ℝ≥0∞}
    (hatail : countingSquareNorm (fun x : ↥(D ∩ (U ∩ d.dust)) =>
      if x.val ≠ p then codeHitProbability d P x.val else 0) ≤ δ)
    (hbtail : countingSquareNorm (fun x : ↥(D ∩ (U ∩ d.dust)) =>
      if x.val ≠ q then codeHitProbability e Q x.val else 0) ≤ δ) :
    ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {z | (range z.1.val.1 ∩ range z.2.val.1 ∩ (U ∩ d.dust)).Nonempty} ≤
        2 * δ + δ ^ 2 := by
  have hcount : (D ∩ (U ∩ d.dust)).Countable := hD.mono inter_subset_left
  let : Countable ↥(D ∩ (U ∩ d.dust)) := hcount.to_subtype
  apply (code_pair_meeting_bound d e P Q (U ∩ d.dust) D hD ?_).trans
  · let p' : ↥(D ∩ (U ∩ d.dust)) := ⟨p, hp⟩
    let q' : ↥(D ∩ (U ∩ d.dust)) := ⟨q, hq⟩
    have ha : codeHitProbability d P p ≤ 1 := prob_le_one
    have hb : codeHitProbability e Q q ≤ 1 := prob_le_one
    have hpa : countingSquareNorm (puncturedHit
        (fun x : ↥(D ∩ (U ∩ d.dust)) => codeHitProbability d P x.val) univ p') ≤ δ := by
      convert hatail using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext x
      simp [puncturedHit, p', Subtype.ext_iff]
    have hqb : countingSquareNorm (puncturedHit
        (fun x : ↥(D ∩ (U ∩ d.dust)) => codeHitProbability e Q x.val) univ q') ≤ δ := by
      convert hbtail using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext x
      simp [puncturedHit, q', Subtype.ext_iff]
    have h := punctured_hit_product_sum_le
      (fun x : ↥(D ∩ (U ∩ d.dust)) => codeHitProbability d P x.val)
      (fun x : ↥(D ∩ (U ∩ d.dust)) => codeHitProbability e Q x.val)
      univ p' q' (mem_univ _) (mem_univ _)
      (fun h => hpq (congrArg Subtype.val h)) ha hb
      hpa hqb
    simpa only [mem_univ, ite_true, if_true] using h
  · filter_upwards [hcontacts] with z hz
    rintro x ⟨hx, hxU, hxB⟩
    exact hz ⟨hx, hxB⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeetingFatou
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fatou's lemma controls an outer meeting event from eventual occupation
lower bounds. No measurability of the event itself is required. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace CircleDomainRigidity

theorem measure_event_le_of_eventual_unit_integrals
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω)
    (I : ℕ → Ω → ℝ≥0∞) (hI : ∀ n, Measurable (I n)) {B : ℝ≥0∞}
    (hlower : ∀ p ∈ E, ∀ᶠ n in atTop, 1 ≤ I n p)
    (hupper : ∀ᶠ n in atTop, (∫⁻ p, I n p ∂μ) ≤ B) : μ E ≤ B := by
  apply (meas_le_lintegral₀ (Measurable.liminf hI).aemeasurable
    (fun p hp => le_liminf_of_le (by isBoundedDefault) (hlower p hp))).trans
  apply (lintegral_liminf_le hI).trans
  exact le_trans liminf_le_limsup (limsup_le_of_le (by isBoundedDefault) hupper)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PointHitPairOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common interior visit forces a unit lower bound for every sufficiently
small proximity integral. The bound concerns the original physical occupations. -/

open Set Function Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem one_le_ball_pair_integral {Y : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ ν : Measure Y) [SFinite ν] (A : Set Y) (p : Y)
    {a : ℝ≥0} (ha : a ≠ 0) (hball : ball p a ⊆ A)
    (hμ : (a : ℝ≥0∞) ≤ μ (ball p a)) (hν : (a : ℝ≥0∞) ≤ ν (ball p a)) :
    1 ≤ ∫⁻ z, ballPairKernel A a z ∂μ.prod ν := by
  let B : Set Y := ball p a
  have hsub : B ×ˢ B ⊆ {z : Y × Y | z.1 ∈ A ∧ z.2 ∈ A ∧ dist z.1 z.2 < 2 * a} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    refine ⟨hball hx, hball hy, ?_⟩
    exact (dist_triangle x p y).trans_lt (by
      have hx' : dist x p < a := hx
      have hy' : dist p y < a := by
        rw [dist_comm]
        exact hy
      linarith)
  have hlow : (B ×ˢ B).indicator (fun _ => (a : ℝ≥0∞)⁻¹ ^ 2) ≤ ballPairKernel A a :=
    indicator_le_indicator_of_subset hsub (fun _ => bot_le)
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
  calc
    1 = (a : ℝ≥0∞)⁻¹ ^ 2 * ((a : ℝ≥0∞) * (a : ℝ≥0∞)) := by
      rw [← pow_two, ← mul_pow, ENNReal.inv_mul_cancel ha0 ENNReal.coe_ne_top, one_pow]
    _ ≤ (a : ℝ≥0∞)⁻¹ ^ 2 * (μ B * ν B) :=
      mul_le_mul' le_rfl (mul_le_mul' hμ hν)
    _ = ∫⁻ z, (B ×ˢ B).indicator (fun _ => (a : ℝ≥0∞)⁻¹ ^ 2) z ∂μ.prod ν := by
      rw [lintegral_indicator_const (measurableSet_ball.prod measurableSet_ball),
        Measure.prod_prod]
    _ ≤ _ := lintegral_mono hlow

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_5 : BorelSpace Sphere := ⟨rfl⟩
omit [BorelSpace C(PathTime, Sphere)] in
theorem code_hit_ball_occupation_ge
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hend : d.target ∉ d.quotientDomain)
    (p : Sphere) {a : ℝ≥0} (ha : 0 < a)
    (hball : closedBall p a ⊆ d.physicalDomain)
    (Γ : BasePathCode d) (hhit : π p ∈ range Γ.val.1) :
    (a : ℝ≥0∞) ≤ baseCodeOccupation d Γ (ball p a) := by
  have hp : p ∈ d.physicalDomain := hball (mem_closedBall_self a.coe_nonneg)
  obtain ⟨hO, hOU, hpre, hpO⟩ := quotient_interior_ball d π hπ hclosed hsurj hr he
    p (show 0 < (a : ℝ) from ha) hball
  have h := point_hit_occupation_lower_bound d hU π hπ he p hp
    (π '' ball p a) hO hOU hpO
    (ENNReal.coe_ne_zero.mpr ha.ne') ENNReal.coe_ne_top
    (δ := (a : ℝ≥0∞)) (fun b hb => ?_) (baseCodePhysicalPath d Γ)
    (by change Γ.val.1 ⊤ ∉ π '' ball p a
        rw [Γ.property.2.1.2.1]
        exact fun ht => hend (hOU (subset_closure ht))) hhit
  · simpa only [hpre, baseCodeOccupation] using h
  · rw [hpre] at hb
    have hd : (a : ℝ) ≤ dist b p := le_of_not_gt hb
    simpa only [edist_dist, dist_comm, ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal hd

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DomainMeetingBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior meetings of two independent laws are bounded by their local
occupation energies. The geometric small-ball constant is kept explicit. -/

open Set Function Filter Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_6 : BorelSpace Sphere := ⟨rfl⟩
theorem domain_meeting_bound_of_ball_area
    (d e : PathCodeData Sphere Sphere) (hd : IsOpen d.quotientDomain)
    (he : IsOpen e.quotientDomain) (hG : e.physicalDomain = d.physicalDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (hed : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hee : ∀ y : e.physicalDomain, (e.domainEquiv y).val = π y.val)
    (hdend : d.target ∉ d.quotientDomain) (heend : e.target ∉ e.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    [SigmaFinite (meanCodeOccupation d P)] [SigmaFinite (meanCodeOccupation e Q)]
    (σ : Measure Sphere) [SFinite σ] (g h : Sphere → ℝ≥0∞)
    (hg : Measurable g) (hh : Measurable h)
    (hP : meanCodeOccupation d P = σ.withDensity g)
    (hQ : meanCodeOccupation e Q = σ.withDensity h)
    (A : Set Sphere) (hA : IsOpen A) (hAG : A ⊆ d.physicalDomain)
    (a : ℕ → ℝ≥0) (ha : ∀ n, 0 < a n)
    (hat : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0)) {C E : ℝ≥0∞}
    (hball : ∀ᶠ n in atTop, ∀ x ∈ A,
      σ (ball x (2 * a n)) ≤ C * (a n : ℝ≥0∞) ^ 2)
    (hgE : (∫⁻ x in A, g x ^ 2 ∂σ) ≤ E)
    (hhE : (∫⁻ x in A, h x ^ 2 ∂σ) ≤ E) :
    ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {p | ∃ x ∈ A, π x ∈ range p.1.val.1 ∧ π x ∈ range p.2.val.1} ≤ C * E := by
  apply measure_event_le_of_eventual_unit_integrals _ _ (fun n => codePairProximity d e A (a n))
    (fun n => measurable_codePairProximity d e hd he A hA.measurableSet (a n))
  · rintro p ⟨x, hx, hxd, hxe⟩
    obtain ⟨R, hR, hRA⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds hx)
    filter_upwards [hat.eventually (gt_mem_nhds hR)] with n hn
    have hcl : closedBall x (a n) ⊆ A := fun y hy =>
      hRA ((mem_closedBall.mp hy).trans_lt hn)
    have hmd := code_hit_ball_occupation_ge d hd π hπ hclosed hsurj hr hed hdend x (ha n)
      (hcl.trans hAG) p.1 hxd
    have hre : ∀ x y, π x = π y ↔ x = y ∨
        (x ∈ e.physicalDomainᶜ ∧ y ∈ connectedComponentIn e.physicalDomainᶜ x) := by
      simpa only [hG] using hr
    have hme := code_hit_ball_occupation_ge e he π hπ hclosed hsurj hre hee heend x (ha n)
      (by simpa only [hG] using hcl.trans hAG) p.2 hxe
    exact one_le_ball_pair_integral _ _ A x (ha n).ne' (ball_subset_closedBall.trans hcl) hmd hme
  · filter_upwards [hball] with n hn
    exact mean_codePairProximity_le d e hd he P Q σ g h hg hh hP hQ A hA.measurableSet
      (ha n).ne' hn hgE hhE

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalizedMeetingUnion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Splitting a meeting into its physical-domain and dust parts. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
theorem localized_code_meeting_union_bound
    (d e : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (Q : ProbabilityMeasure (BasePathCode e)) (U B : Set X) (A : Set Y) (π : Y → X)
    (hcover : ∀ x ∈ U, x ∈ B ∨ ∃ y ∈ A, π y = x)
    {b c : ℝ≥0∞}
    (hB : ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {p | (range p.1.val.1 ∩ range p.2.val.1 ∩ (U ∩ B)).Nonempty} ≤ b)
    (hA : ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {p | ∃ y ∈ A, π y ∈ range p.1.val.1 ∧ π y ∈ range p.2.val.1} ≤ c) :
    ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {p | ∃ x ∈ U, x ∈ range p.1.val.1 ∧ x ∈ range p.2.val.1} ≤ b + c := by
  apply (measure_mono (t :=
    {p | (range p.1.val.1 ∩ range p.2.val.1 ∩ (U ∩ B)).Nonempty} ∪
    {p | ∃ y ∈ A, π y ∈ range p.1.val.1 ∧ π y ∈ range p.2.val.1}) ?_).trans
  · exact (measure_union_le _ _).trans (add_le_add hB hA)
  · rintro p ⟨x, hxU, hxp, hxq⟩
    rcases hcover x hxU with hxB | ⟨y, hy, hπy⟩
    · exact Or.inl ⟨x, ⟨hxp, hxq⟩, hxU, hxB⟩
    · exact Or.inr ⟨y, hy, hπy.symm ▸ hxp, hπy.symm ▸ hxq⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalCodeMeetingBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full localized meeting estimate for two original code laws: the dust
part and the physical occupation part use the same collar and budget. -/

open Set Function Filter Metric MeasureTheory
open scoped ENNReal NNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_7 : BorelSpace Sphere := ⟨rfl⟩
theorem local_code_meeting_bound
    (d e : PathCodeData Sphere Sphere) (hd : IsOpen d.quotientDomain)
    (he : IsOpen e.quotientDomain) (hG : IsOpen d.physicalDomain)
    (hGe : e.physicalDomain = d.physicalDomain) (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (hed : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hee : ∀ y : e.physicalDomain, (e.domainEquiv y).val = π y.val)
    (hdend : d.target ∉ d.quotientDomain) (heend : e.target ∉ e.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    [SigmaFinite (meanCodeOccupation d P)] [SigmaFinite (meanCodeOccupation e Q)]
    (σ : Measure Sphere) [SFinite σ] (g h : Sphere → ℝ≥0∞)
    (hg : Measurable g) (hh : Measurable h)
    (hP : meanCodeOccupation d P = σ.withDensity g)
    (hQ : meanCodeOccupation e Q = σ.withDensity h)
    (U D : Set Sphere) (hU : IsOpen U) (hD : D.Countable)
    (hcontacts : ∀ᵐ z ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      range z.1.val.1 ∩ range z.2.val.1 ∩ d.dust ⊆ D)
    (p q : Sphere) (hp : p ∈ D ∩ (U ∩ d.dust)) (hq : q ∈ D ∩ (U ∩ d.dust)) (hpq : p ≠ q)
    (a : ℕ → ℝ≥0) (ha : ∀ n, 0 < a n) (hat : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0))
    (C δ : ℝ≥0∞)
    (hball : ∀ᶠ n in atTop, ∀ x ∈ d.physicalDomain ∩ π ⁻¹' U,
      σ (ball x (2 * a n)) ≤ C * (a n : ℝ≥0∞) ^ 2)
    (hgE : (∫⁻ x in d.physicalDomain ∩ π ⁻¹' U, g x ^ 2 ∂σ) ≤ δ ^ 2)
    (hhE : (∫⁻ x in d.physicalDomain ∩ π ⁻¹' U, h x ^ 2 ∂σ) ≤ δ ^ 2)
    (hatail : countingSquareNorm (fun x : ↥(D ∩ (U ∩ d.dust)) =>
      if x.val ≠ p then codeHitProbability d P x.val else 0) ≤ δ)
    (hbtail : countingSquareNorm (fun x : ↥(D ∩ (U ∩ d.dust)) =>
      if x.val ≠ q then codeHitProbability e Q x.val else 0) ≤ δ) :
    ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {z | ∃ x ∈ U, x ∈ range z.1.val.1 ∧ x ∈ range z.2.val.1} ≤
        2 * δ + (1 + C) * δ ^ 2 := by
  have hcover : ∀ x ∈ U, x ∈ d.dust ∨ ∃ y ∈ d.physicalDomain ∩ π ⁻¹' U, π y = x := by
    intro x hx
    by_cases hxB : x ∈ d.dust
    · exact Or.inl hxB
    · right
      let y : d.physicalDomain := d.domainEquiv.symm ⟨x, hBU hxB⟩
      have hy : π y.val = x := by
        rw [← hed y]
        exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨x, hBU hxB⟩)
      refine ⟨y.val, ⟨y.property, ?_⟩, hy⟩
      change π y.val ∈ U
      rw [hy]
      exact hx
  have hdust := code_dust_meeting_bound d e P Q U D hD hcontacts p q hp hq hpq hatail hbtail
  have hdomain := domain_meeting_bound_of_ball_area d e hd he hGe π hπ hclosed hsurj hr
    hed hee hdend heend P Q σ g h hg hh hP hQ (d.physicalDomain ∩ π ⁻¹' U)
    (hG.inter (hU.preimage hπ)) inter_subset_left a ha hat hball hgE hhE
  apply (localized_code_meeting_union_bound d e P Q U d.dust
    (d.physicalDomain ∩ π ⁻¹' U) π hcover hdust hdomain).trans
  apply le_of_eq
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableLocalFamily
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable subfamily of the actual collar neighborhoods suffices at every
point and every scale. The selected sets retain their original witnesses. -/

open Set Function TopologicalSpace

noncomputable section
namespace CircleDomainRigidity

theorem exists_countable_local_family {X C : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] (S : Set X) (U : C → Set X)
    (hU : ∀ c, IsOpen (U c))
    (hlocal : ∀ x ∈ S, ∀ V : Set X, IsOpen V → x ∈ V →
      ∃ c, x ∈ U c ∧ U c ⊆ V) :
    ∃ D : Set C, D.Countable ∧ ∀ x ∈ S, ∀ V : Set X,
      IsOpen V → x ∈ V → ∃ c ∈ D, x ∈ U c ∧ U c ⊆ V := by
  classical
  obtain ⟨B, hB⟩ := exists_seq_basis X
  have hcover (n : ℕ) : ∃ D : Set C, D.Countable ∧
      (∀ c ∈ D, U c ⊆ B n) ∧ S ∩ B n ⊆ ⋃ c ∈ D, U c := by
    let T := {c : C | U c ⊆ B n}
    have hc : S ∩ B n ⊆ ⋃ c : T, U c.val := by
      rintro x ⟨hxS, hxB⟩
      obtain ⟨c, hxc, hc⟩ := hlocal x hxS (B n)
        (hB.isOpen (mem_range_self n)) hxB
      exact mem_iUnion.mpr ⟨⟨c, hc⟩, hxc⟩
    obtain ⟨D, hD, hcov⟩ := (HereditarilyLindelofSpace.isLindelof (S ∩ B n)).elim_countable_subcover
      (fun c : T => U c.val) (fun c => hU c.val) hc
    refine ⟨Subtype.val '' D, hD.image _, ?_, ?_⟩
    · rintro c ⟨d, hd, rfl⟩
      exact d.property
    · intro x hx
      obtain ⟨c, hcD, hxc⟩ := mem_iUnion₂.mp (hcov hx)
      exact mem_iUnion₂.mpr ⟨c.val, mem_image_of_mem _ hcD, hxc⟩
  choose D hD hDB hcov using hcover
  refine ⟨⋃ n, D n, countable_iUnion hD, ?_⟩
  intro x hxS V hV hxV
  obtain ⟨W, hWB, hxW, hWV⟩ := hB.exists_subset_of_mem_open hxV hV
  obtain ⟨n, rfl⟩ := hWB
  obtain ⟨c, hcD, hxc⟩ := mem_iUnion₂.mp (hcov n ⟨hxS, hxW⟩)
  exact ⟨c, mem_iUnion.mpr ⟨n, hcD⟩, hxc, (hDB n c hcD).trans hWV⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanDiskImages
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact Jordan disks contained in the domain of an open embedding have their actual Jordan
interiors as images. This identifies the anchor disks in finite models. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

/-- An open bounded region with the boundary of a Jordan disk is that disk. -/
theorem open_eq_jordanInterior_of_frontier
    (H : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (hne : U.Nonempty) (hf : frontier U = frontier (jordanInterior H)) :
    U = jordanInterior H := open_eq_jordan_of_frontier H hU hb hne hf

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SaturatedFrontier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A saturated open set with closed projected closure has its exact projected
frontier. This identifies the boundary of the quotient collars. -/

open Set Function

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem frontier_image_of_saturated_open (π : X → Y) (hπ : Continuous π)
    (U : Set X) (hU : IsOpen U) (ho : IsOpen (π '' U))
    (hc : IsClosed (π '' closure U)) (hsat : π ⁻¹' (π '' U) = U) :
    frontier (π '' U) = π '' frontier U := by
  have hcl : closure (π '' U) = π '' closure U := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono subset_closure) hc
    · exact image_closure_subset_closure_image hπ
  rw [ho.frontier_eq, hcl, hU.frontier_eq]
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, fun h => hy ⟨x, h, rfl⟩⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hxn⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    intro h
    exact hxn (hsat ▸ h)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientCollarJordan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual image of a physical collar under the component-collapse map
is a Jordan disk. Its filled side is identified by its exact frontier. -/

open Set Function Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_jordan_quotient_collar (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G)
    (hinf : OnePoint.infty ∉ closure (π '' (((↑) : ℂ → Sphere) '' jordanInterior H))) :
    ∃ K : ℂ ≃ₜ ℂ,
      π '' (((↑) : ℂ → Sphere) '' jordanInterior H) =
        ((↑) : ℂ → Sphere) '' jordanInterior K := by
  let W := ((↑) : ℂ → Sphere) '' jordanInterior H
  let V := π '' W
  have hW : IsOpen W := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)
  have hV : IsOpen V := isOpen_image_jordanInterior_of_component_collapse
    G π hπ hclosed hsurj hr H hboundary
  have hWc : IsCompact (closure W) := by
    rw [closure_sphere_image_jordanInterior]
    exact (isCompact_closure_jordanInterior H).image OnePoint.continuous_coe
  have hsat : π ⁻¹' V = W := preimage_image_jordanInterior_of_component_collapse
    G π hsurj hr H hboundary
  have hfront : frontier V = π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) := by
    rw [frontier_image_of_saturated_open π hπ W hW hV (hWc.image hπ).isClosed hsat,
      frontier_sphere_image_jordanInterior]
  let c : Circle → Sphere := fun t => π ((H (t : ℂ) : ℂ) : Sphere)
  have hc : Continuous c := hπ.comp (OnePoint.continuous_coe.comp
    (H.continuous.comp continuous_subtype_val))
  have hrange : range c = frontier V := by
    rw [hfront, frontier_jordanInterior]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, ⟨_, ⟨t, t.property, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have hcf (t : Circle) : c t ≠ OnePoint.infty := by
    intro he
    apply hinf
    rw [← he]
    exact frontier_subset_closure (hrange ▸ mem_range_self t)
  have hci : Injective c := by
    intro s t he
    have hsG : ((H (s : ℂ) : ℂ) : Sphere) ∈ G :=
      hboundary _ (by rw [frontier_jordanInterior]; exact ⟨s, s.property, rfl⟩)
    rcases (hr _ _).mp he with h | h
    · exact Subtype.ext (H.injective (OnePoint.coe_injective h))
    · exact (h.1 hsG).elim
  let δ : Circle → ℂ := finiteCoord ∘ c
  have hδ : Continuous δ :=
    (continuousOn_finiteCoord_of_avoids_infty hinf).comp_continuous hc
      (fun t => frontier_subset_closure (hrange ▸ mem_range_self t))
  have hδi : Injective δ := by
    intro s t h
    apply hci
    have h' := congrArg ((↑) : ℂ → Sphere) h
    change (finiteCoord (c s) : Sphere) = (finiteCoord (c t) : Sphere) at h'
    exact (CannonMobius.coe_coordinate (hcf s)).symm.trans
      (h'.trans (CannonMobius.coe_coordinate (hcf t)))
  obtain ⟨K, hK⟩ := hsch δ hδ hδi
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' V
  have hAf : frontier A = range δ := by
    rw [← OnePoint.isOpenEmbedding_coe.isOpenMap.preimage_frontier_eq_frontier_preimage
      OnePoint.continuous_coe V, ← hrange]
    ext z
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      change finiteCoord (c t) = z
      rw [ht, finiteCoord_coe]
    · rintro ⟨t, rfl⟩
      exact ⟨t, (CannonMobius.coe_coordinate (hcf t)).symm⟩
  have hAn : A.Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_jordanInterior H).nonempty
    have hx : π (z : Sphere) ∈ V := ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hxne : π (z : Sphere) ≠ OnePoint.infty := fun h => hinf (h ▸ subset_closure hx)
    exact ⟨finiteCoord (π (z : Sphere)), (CannonMobius.coe_coordinate hxne).symm ▸ hx⟩
  have hAK : A = jordanInterior K := open_eq_jordanInterior_of_frontier K
    (hV.preimage OnePoint.continuous_coe)
    ((isCompact_finite_preimage isClosed_closure hinf).isBounded.subset
      (preimage_mono subset_closure)) hAn
    (hAf.trans (frontier_jordanInterior_eq_circle_range K δ hK).symm)
  refine ⟨K, ?_⟩
  change V = ((↑) : ℂ → Sphere) '' jordanInterior K
  rw [← hAK]
  apply Subset.antisymm
  · intro x hx
    have hxne : x ≠ OnePoint.infty := fun h => hinf (h ▸ subset_closure hx)
    exact ⟨finiteCoord x, (CannonMobius.coe_coordinate hxne).symm ▸ hx,
      CannonMobius.coe_coordinate hxne⟩
  · exact image_preimage_subset _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CountableJordanCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single countable family of genuine Jordan collars is a neighborhood
basis at every finite dust point. Boundaries lie in the quotient domain. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem exists_countable_jordan_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G U B E : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hB : IsClosed B) (hTD : IsTotallyDisconnected B) (hBU : Bᶜ ⊆ U)
    (hdisj : Disjoint U B) (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hE : IsClosed E) (hEU : E ⊆ U) (hinf : π OnePoint.infty ∉ B) :
    ∃ C : Set (ℂ ≃ₜ ℂ), C.Countable ∧
      (∀ K ∈ C, frontier (quotientJordanDisk K) ⊆ U ∧
        π OnePoint.infty ∉ closure (quotientJordanDisk K) ∧
        Disjoint E (quotientJordanDisk K)) ∧
      ∀ p ∈ B \ {OnePoint.infty}, ∀ O : Set Sphere, IsOpen O → p ∈ O →
        ∃ K ∈ C, p ∈ quotientJordanDisk K ∧ quotientJordanDisk K ⊆ O := by
  classical
  let Valid (K : ℂ ≃ₜ ℂ) : Prop := frontier (quotientJordanDisk K) ⊆ U ∧
    π OnePoint.infty ∉ closure (quotientJordanDisk K) ∧ Disjoint E (quotientJordanDisk K)
  have hlocal (p : Sphere) (hp : p ∈ B \ {OnePoint.infty})
      (O : Set Sphere) (hO : IsOpen O) (hpO : p ∈ O) :
      ∃ K : {K : ℂ ≃ₜ ℂ // Valid K},
        p ∈ quotientJordanDisk K.val ∧ quotientJordanDisk K.val ⊆ O := by
    have hpE : p ∉ E := fun he => disjoint_left.mp hdisj (hEU he) hp.1
    have hpi : p ≠ π OnePoint.infty := fun he => hinf (he ▸ hp.1)
    let V := O ∩ Eᶜ ∩ {π OnePoint.infty}ᶜ ∩ {OnePoint.infty}ᶜ
    have hV : IsOpen V := ((hO.inter hE.isOpen_compl).inter
      isClosed_singleton.isOpen_compl).inter isClosed_singleton.isOpen_compl
    have hpV : p ∈ V := ⟨⟨⟨hpO, hpE⟩, hpi⟩, hp.2⟩
    obtain ⟨D, hDV, _⟩ := exists_weighted_collar_in_neighborhood hcoarea hsard hsch
      G π hπ hclosed hsurj hr hB hTD hbad hp.1 hpi hV hpV
      (fun _ => 0) measurable_const (by simp)
    have hDo : IsOpen D.region := D.isOpen_region hπ hclosed hsurj hr
    obtain ⟨K, hK⟩ := exists_jordan_quotient_collar hsch G π hπ hclosed hsurj hr
      D.disk (fun z hz => (D.level_good z (D.frontier_level hz)).1)
      (fun hi => (hDV hi).2 rfl)
    have heq : D.region = quotientJordanDisk K := hK
    have hvalid : Valid K := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← heq]
        intro x hx
        obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := D.frontier_region_subset hπ hDo hx
        exact hBU (D.level_good z hz).2
      · rw [← heq]
        exact fun hi => (hDV hi).1.2 rfl
      · apply disjoint_left.mpr
        intro x hxE hxK
        have hxD : x ∈ D.region := heq ▸ hxK
        exact (hDV (subset_closure hxD)).1.1.2 hxE
    refine ⟨⟨K, hvalid⟩, heq ▸ D.point_mem_region hsurj hpi, ?_⟩
    intro x hx
    exact (hDV (subset_closure (heq ▸ hx))).1.1.1
  obtain ⟨C, hC, hc⟩ := exists_countable_local_family (B \ {OnePoint.infty})
    (fun K : {K : ℂ ≃ₜ ℂ // Valid K} => quotientJordanDisk K.val)
    (fun K => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen K.val)) hlocal
  refine ⟨Subtype.val '' C, hC.image _, ?_, ?_⟩
  · rintro K ⟨k, hk, rfl⟩
    exact k.property
  · intro p hp O hO hpO
    obtain ⟨K, hKC, hpK, hKO⟩ := hc p hp O hO hpO
    exact ⟨K.val, mem_image_of_mem _ hKC, hpK, hKO⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereJordanCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complex disk and measurable circle coordinates for a spherical
Jordan collar. -/

open Set Function Metric MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem sphereJordanCoordinate_continuousOn (K : ℂ ≃ₜ ℂ) :
    ContinuousOn (sphereJordanCoordinate K)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) := by
  exact K.symm.continuous.comp_continuousOn
    (continuousOn_finiteCoord_of_avoids_infty (by
      rw [closure_sphere_image_jordanInterior]
      rintro ⟨z, _, hz⟩
      exact OnePoint.coe_ne_infty z hz))

theorem sphereJordanCoordinate_injOn (K : ℂ ≃ₜ ℂ) :
    InjOn (sphereJordanCoordinate K) (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) := by
  intro x hx y hy h
  rw [closure_sphere_image_jordanInterior] at hx hy
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  exact congrArg ((↑) : ℂ → Sphere) (K.symm.injective h)

theorem sphereJordanCoordinate_mapsTo (K : ℂ ≃ₜ ℂ) :
    MapsTo (sphereJordanCoordinate K)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) (closedBall 0 1) := by
  intro x hx
  rw [closure_sphere_image_jordanInterior, closure_jordanInterior] at hx
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hx
  simpa only [sphereJordanCoordinate, finiteCoord_coe, K.symm_apply_apply] using hz

theorem sphereJordanCoordinate_boundary_inverse (K : ℂ ≃ₜ ℂ) :
    ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K),
      sphereJordanCoordinate K x = standardCirclePoint
        ((measurableEmbedding_sphereJordanBoundary K).invFun x) := by
  intro x hx
  rw [← range_sphereJordanBoundary] at hx
  obtain ⟨θ, rfl⟩ := hx
  rw [(measurableEmbedding_sphereJordanBoundary K).leftInverse_invFun θ]
  simp only [sphereJordanCoordinate, sphereJordanBoundary, finiteCoord_coe, K.symm_apply_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanCollarCountability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coded-law countability argument on an actual spherical Jordan collar.
Its disk coordinates and boundary probability transport are constructed here. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_8 : BorelSpace Sphere := ⟨rfl⟩
theorem countable_of_small_jordan_collar_meetings {I : Type*} [LinearOrder I]
    (hcross : UnitDiskAlternatingContinua) (S : Set I) (K : ℂ ≃ₜ ℂ)
    (Ω : I → Type*) [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, ProbabilityMeasure (Ω i)) (a : ∀ i, Ω i → C(PathTime, Sphere))
    (ha : ∀ i, Measurable (a i)) (p : I → Sphere)
    (hp : ∀ i ∈ S, p i ∈ ((↑) : ℂ → Sphere) '' jordanInterior K)
    (hends : ∀ i ∈ S, ∀ᵐ z ∂(μ i : Measure (Ω i)),
      a i z ⊥ ∉ ((↑) : ℂ → Sphere) '' jordanInterior K ∧ a i z ⊤ = p i)
    (hatom : ∀ i ∈ S, NullSingletonClass
      (lastEntryLaw ((μ i).map (f := a i) (ha i).aemeasurable) (((↑) : ℂ → Sphere) '' jordanInterior K) : Measure Sphere))
    (hsmall : ∀ i ∈ S, ∀ j ∈ S, i < j →
      4 * ((μ i : Measure (Ω i)).prod (μ j : Measure (Ω j)))
        {z | ∃ x ∈ ((↑) : ℂ → Sphere) '' jordanInterior K,
          x ∈ range (a i z.1) ∧ x ∈ range (a j z.2)} < (1 / 10 : ℝ≥0∞) ^ 4) :
    S.Countable := by
  let V := ((↑) : ℂ → Sphere) '' jordanInterior K
  have hV : IsOpen V := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen K)
  let c := sphereJordanBoundary K
  let hc := measurableEmbedding_sphereJordanBoundary K
  apply countable_of_uniformly_small_coded_collar_meetings hcross S V hV
    (sphereJordanCoordinate K) (sphereJordanCoordinate_continuousOn K)
    (sphereJordanCoordinate_injOn K) (sphereJordanCoordinate_mapsTo K)
    hc.invFun hc.measurable_invFun (sphereJordanCoordinate_boundary_inverse K)
    Ω μ a ha p hp hends _ hsmall
  intro i hi
  have := hatom i hi
  apply lastEntryCircleLaw_nullSingletonClass ((μ i).map (f := a i) (ha i).aemeasurable) V c hc
  rw [range_sphereJordanBoundary]
  apply lastEntryLaw_boundary_support _ V hV
  change ∀ᵐ γ ∂((μ i : Measure (Ω i)).map (a i)), γ ⊥ ∉ V ∧ γ ⊤ ∈ V
  apply (ae_map_iff (ha i).aemeasurable
    (((continuous_eval_const ⊥).measurable hV.measurableSet).compl.inter
      ((continuous_eval_const ⊤).measurable hV.measurableSet))).mpr
  filter_upwards [hends i hi] with z hz
  refine ⟨hz.1, ?_⟩
  change (a i z) ⊤ ∈ V
  rw [hz.2]
  exact hp i hi

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PuncturedSquareNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite square mass admits a small punctured neighborhood of any point.
This controls the entire hit vector, including any later countable restriction. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem punctured_square_norm_subtype_le {X : Type*} (m : X → ℝ≥0∞)
    (D U B : Set X) (p : X) :
    countingSquareNorm (fun x : ↥(D ∩ (U ∩ B)) => if x.val ≠ p then m x.val else 0) ≤
      countingSquareNorm (fun x : B => if x.val ∈ U ∧ x.val ≠ p then m x.val else 0) := by
  let f : ↥(D ∩ (U ∩ B)) → B := fun x => ⟨x.val, x.property.2.2⟩
  have hf : Injective f := fun _ _ h =>
    Subtype.ext (congrArg (fun z : B => z.val) h)
  have he : (fun x : ↥(D ∩ (U ∩ B)) => if x.val ≠ p then m x.val else 0) =
      (fun x : B => if x.val ∈ U ∧ x.val ≠ p then m x.val else 0) ∘ f := by
    funext x
    simp only [Function.comp_def, f, x.property.2.1, true_and]
  rw [he]
  exact countingSquareNorm_comp_injective _ f hf

theorem exists_open_punctured_square_norm {X A : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (x : A → X) (m : A → ℝ≥0∞) (hm : (∑' a, m a ^ 2) < ∞)
    (p : X) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ O : Set X, IsOpen O ∧ p ∈ O ∧
      countingSquareNorm (fun a => if x a ∈ O ∧ x a ≠ p then m a else 0) < δ := by
  let w : A → ℝ≥0∞ := fun a => if x a ≠ p then m a ^ 2 else 0
  let ν : Measure X := Measure.sum fun a => w a • Measure.dirac (x a)
  have hfin : ν univ < ∞ := by
    dsimp only [ν]
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ,
      mem_univ, indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
    exact (ENNReal.tsum_le_tsum (fun a => by dsimp only [w]; split_ifs <;> simp)).trans_lt hm
  let : IsFiniteMeasure ν := ⟨hfin⟩
  have hzero : ν {p} = 0 := by
    dsimp only [ν]
    rw [Measure.sum_apply _ (measurableSet_singleton p)]
    have hz (a : A) : (w a • Measure.dirac (x a)) {p} = 0 := by
      by_cases h : x a = p <;> simp [w, h]
    simp only [hz, tsum_zero]
  obtain ⟨O, hpO, hO, hmass⟩ := ({p} : Set X).exists_isOpen_lt_of_lt (μ := ν)
    (δ ^ 2) (hzero ▸ ENNReal.pow_pos hδ 2)
  have he : ν O = ∑' a, (if x a ∈ O ∧ x a ≠ p then m a else 0) ^ 2 := by
    dsimp only [ν]
    rw [Measure.sum_apply _ hO.measurableSet]
    apply tsum_congr
    intro a
    by_cases ho : x a ∈ O <;> by_cases hp : x a = p <;> simp [w, ho, hp]
  refine ⟨O, hO, hpO (mem_singleton p), ?_⟩
  have hroot := ENNReal.rpow_lt_rpow hmass (by norm_num : (0 : ℝ) < 1 / 2)
  rw [he] at hroot
  have hpow : (δ ^ 2) ^ (1 / 2 : ℝ) = δ := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  simpa only [countingSquareNorm, Function.comp_def, hpow] using hroot

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableDiffuseCodeLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The crossing contradiction for a family of actual positive code laws.
Pairwise dust contacts are countable; square occupation and hit bounds make
all remaining meetings small on a common member of the countable collar basis. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_9 : BorelSpace Sphere := ⟨rfl⟩
theorem countable_diffuse_code_laws {I : Type*} [LinearOrder I]
    (hcross : UnitDiskAlternatingContinua)
    (G U B E : Set Sphere) (hG : IsOpen G) (hU : IsOpen U)
    (hdisj : Disjoint U B) (hBU : Bᶜ ⊆ U)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (d : I → PathCodeData Sphere Sphere)
    (hGd : ∀ i, (d i).physicalDomain = G) (hUd : ∀ i, (d i).quotientDomain = U)
    (hBd : ∀ i, (d i).dust = B) (hEd : ∀ i, (d i).anchor = E)
    (hed : ∀ i, ∀ y : (d i).physicalDomain, ((d i).domainEquiv y).val = π y.val)
    (htarget : ∀ i, (d i).target ∈ B \ {OnePoint.infty})
    (hinj : Injective (fun i => (d i).target))
    (P : ∀ i, ProbabilityMeasure (BasePathCode (d i)))
    [∀ i, SigmaFinite (meanCodeOccupation (d i) (P i))]
    (g : I → Sphere → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (hocc : ∀ i, meanCodeOccupation (d i) (P i) = sphericalArea.withDensity (g i))
    (henergy : ∀ i, (∫⁻ x, g i x ^ 2 ∂sphericalArea) < ∞)
    (hhit : ∀ i, (∑' x : B, codeHitProbability (d i) (P i) x.val ^ 2) < ∞)
    (hcontacts : ∀ i j, i < j → ∃ D : Set Sphere, D.Countable ∧
      ∀ᵐ z ∂((P i : Measure (BasePathCode (d i))).prod (P j : Measure (BasePathCode (d j)))),
        range z.1.val.1 ∩ range z.2.val.1 ∩ (d i).dust ⊆ D)
    (K : Set (ℂ ≃ₜ ℂ)) (hK : K.Countable)
    (hgood : ∀ k ∈ K, frontier (quotientJordanDisk k) ⊆ U ∧
      π OnePoint.infty ∉ closure (quotientJordanDisk k) ∧ Disjoint E (quotientJordanDisk k))
    (hbasis : ∀ p ∈ B \ {OnePoint.infty}, ∀ O : Set Sphere, IsOpen O → p ∈ O →
      ∃ k ∈ K, p ∈ quotientJordanDisk k ∧ quotientJordanDisk k ⊆ O)
    (a : ℕ → ℝ≥0) (ha : ∀ n, 0 < a n) (hat : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (A : Set Sphere) (hKA : ∀ k ∈ K, π ⁻¹' quotientJordanDisk k ⊆ A)
    (hball : ∀ᶠ n in atTop, ∀ x ∈ A,
      sphericalArea (Metric.ball x (2 * a n)) ≤ C * (a n : ℝ≥0∞) ^ 2) : Countable I := by
  obtain ⟨δ, hδ, hbudget⟩ := exists_small_crossing_budget C hC
  have hδ2 : 0 < δ ^ 2 := ENNReal.pow_pos hδ 2
  have hu (i : I) : IsOpen (d i).quotientDomain := by simpa only [hUd i] using hU
  have hphys (i : I) : IsOpen (d i).physicalDomain := by simpa only [hGd i] using hG
  have hdb (i : I) : Disjoint (d i).quotientDomain (d i).dust := by
    simpa only [hUd i, hBd i] using hdisj
  have hri (i : I) : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ (d i).physicalDomainᶜ ∧ y ∈ connectedComponentIn (d i).physicalDomainᶜ x) := by
    simpa only [hGd i] using hr
  have hpB (i : I) : (d i).target ∈ (d i).dust := by
    simpa only [hBd i] using (htarget i).1
  have hpend (i : I) : (d i).target ∉ (d i).quotientDomain :=
    fun hi => disjoint_left.mp (hdb i) hi (hpB i)
  let Good (k : ℂ ≃ₜ ℂ) (i : I) : Prop :=
    (d i).target ∈ quotientJordanDisk k ∧
    (∫⁻ x in π ⁻¹' quotientJordanDisk k, g i x ^ 2 ∂sphericalArea) ≤ δ ^ 2 ∧
    countingSquareNorm (fun x : B =>
      if x.val ∈ quotientJordanDisk k ∧ x.val ≠ (d i).target
        then codeHitProbability (d i) (P i) x.val else 0) ≤ δ
  have hcover (i : I) : ∃ k ∈ K, Good k i := by
    obtain ⟨O, hO, hpO, hOE⟩ := exists_open_small_occupation_energy (d i) (hu i) (hphys i)
      (hdb i) π hπ (hed i) (P i) sphericalArea (g i) (hg i) (hocc i) (henergy i)
      (d i).target (hpB i) hδ2
    obtain ⟨V, hV, hpV, hVH⟩ := exists_open_punctured_square_norm
      (fun x : B => x.val) (fun x : B => codeHitProbability (d i) (P i) x.val)
      (hhit i) (d i).target hδ
    obtain ⟨k, hk, hpk, hsub⟩ := hbasis (d i).target (htarget i) (O ∩ V)
      (hO.inter hV) ⟨hpO, hpV⟩
    refine ⟨k, hk, hpk, ?_, ?_⟩
    · exact (lintegral_mono_set (preimage_mono (hsub.trans inter_subset_left))).trans hOE.le
    · apply (countingSquareNorm_mono ?_).trans hVH.le
      intro x
      by_cases hx : x.val ∈ quotientJordanDisk k ∧ x.val ≠ (d i).target
      · have hxV : x.val ∈ V ∧ x.val ≠ (d i).target := ⟨(hsub hx.1).2, hx.2⟩
        simp only [hx, hxV, le_refl]
      · simp only [hx, ite_false, if_false, zero_le]
  have hcount (k : ℂ ≃ₜ ℂ) (hk : k ∈ K) : {i | Good k i}.Countable := by
    let V := quotientJordanDisk k
    have hV : IsOpen V := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen k)
    obtain ⟨hfront, hinf, hE⟩ := hgood k hk
    apply countable_of_small_jordan_collar_meetings hcross {i | Good k i} k
      (fun i => BasePathCode (d i)) P (fun i => codePath (d i))
      (fun i => measurable_codePath (d i)) (fun i => (d i).target)
    · exact fun i hi => hi.1
    · intro i hi
      exact Eventually.of_forall fun z => ⟨fun hx => disjoint_left.mp hE
        ((hEd i) ▸ z.property.2.1.1) hx, z.property.2.1.2.1⟩
    · intro i hi
      exact physical_lastEntryLaw_nullSingletonClass (d i) (hu i) (hphys i) π hπ hclosed
        hsurj (hri i) (hed i) (hpend i) (P i) (g i) (hg i) (hocc i) (henergy i)
        V hV (by simpa only [hUd i] using hfront) (fun h => hinf (frontier_subset_closure h))
        (by simpa only [hEd i] using hE) hi.1
    · intro i hi j hj hij
      obtain ⟨D₀, hD₀, hcontact⟩ := hcontacts i j hij
      let D := insert (d i).target (insert (d j).target D₀)
      have hD : D.Countable := (hD₀.insert _).insert _
      have hc : ∀ᵐ z ∂((P i : Measure (BasePathCode (d i))).prod
          (P j : Measure (BasePathCode (d j)))),
          range z.1.val.1 ∩ range z.2.val.1 ∩ (d i).dust ⊆ D :=
        hcontact.mono fun z hz => hz.trans (subset_insert _ _ |>.trans (subset_insert _ _))
      have hpi : (d i).target ∈ D ∩ (V ∩ (d i).dust) :=
        ⟨mem_insert _ _, hi.1, hpB i⟩
      have hpj : (d j).target ∈ D ∩ (V ∩ (d i).dust) := by
        refine ⟨mem_insert_of_mem _ (mem_insert _ _), hj.1, ?_⟩
        simpa only [hBd i] using (htarget j).1
      have ht (i : I) (hi : Good k i) :
          countingSquareNorm (fun x : ↥(D ∩ (V ∩ B)) =>
            if x.val ≠ (d i).target then codeHitProbability (d i) (P i) x.val else 0) ≤ δ :=
        (punctured_square_norm_subtype_le (codeHitProbability (d i) (P i)) D V B
          (d i).target).trans hi.2.2
      have hb : ∀ᶠ n in atTop, ∀ x ∈ (d i).physicalDomain ∩ π ⁻¹' V,
          sphericalArea (Metric.ball x (2 * a n)) ≤ C * (a n : ℝ≥0∞) ^ 2 := by
        filter_upwards [hball] with n hn
        intro x hx
        exact hn x (hKA k hk hx.2)
      have hbU : (d i).dustᶜ ⊆ (d i).quotientDomain := by
        simpa only [hBd i, hUd i] using hBU
      have heG : (d j).physicalDomain = (d i).physicalDomain := (hGd j).trans (hGd i).symm
      have heI : (∫⁻ x in (d i).physicalDomain ∩ π ⁻¹' V,
          g i x ^ 2 ∂sphericalArea) ≤ δ ^ 2 :=
        (lintegral_mono_set inter_subset_right).trans hi.2.1
      have heJ : (∫⁻ x in (d i).physicalDomain ∩ π ⁻¹' V,
          g j x ^ 2 ∂sphericalArea) ≤ δ ^ 2 :=
        (lintegral_mono_set inter_subset_right).trans hj.2.1
      have hti : countingSquareNorm (fun x : ↥(D ∩ (V ∩ (d i).dust)) =>
          if x.val ≠ (d i).target then codeHitProbability (d i) (P i) x.val else 0) ≤ δ := by
        rw [hBd i]
        exact ht i hi
      have htj : countingSquareNorm (fun x : ↥(D ∩ (V ∩ (d i).dust)) =>
          if x.val ≠ (d j).target then codeHitProbability (d j) (P j) x.val else 0) ≤ δ := by
        rw [hBd i]
        exact ht j hj
      have hbound := local_code_meeting_bound (d i) (d j) (hu i) (hu j) (hphys i) heG hbU
        π hπ hclosed hsurj (hri i) (hed i) (hed j) (hpend i) (hpend j) (P i) (P j)
        sphericalArea (g i) (g j) (hg i) (hg j) (hocc i) (hocc j) V D hV hD hc
        (d i).target (d j).target hpi hpj (fun h => (ne_of_lt hij) (hinj h))
        a ha hat C δ hb heI heJ
        hti htj
      exact (mul_le_mul' (le_refl 4) hbound).trans_lt hbudget
  have hall : (univ : Set I) ⊆ ⋃ k ∈ K, {i | Good k i} := by
    intro i _
    obtain ⟨k, hk, hi⟩ := hcover i
    exact mem_iUnion₂.mpr ⟨k, hk, hi⟩
  exact Set.countable_univ_iff.mp ((hK.biUnion hcount).mono hall)

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
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereChartInversePairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse chart control for pairs of nearby finite sphere points. -/

open Set Function Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

theorem linear_stereo_inverse_pairs (v : RoundAmbient) (hv : ‖v‖ = 1)
    (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    ∃ (L : ℝ≥0) (W : Set RoundAmbient),
      W ∈ 𝓝 (stereoInvFunAux v (A z : RoundAmbient)) ∧
      ∀ w u : ℂ, stereoInvFunAux v (A w : RoundAmbient) ∈ W →
        stereoInvFunAux v (A u : RoundAmbient) ∈ W →
        dist w u ≤ L * dist (stereoInvFunAux v (A w : RoundAmbient))
          (stereoInvFunAux v (A u : RoundAmbient)) := by
  let F : ℂ → RoundAmbient := fun w => stereoInvFunAux v (A w : RoundAmbient)
  let g : RoundAmbient → ℂ := fun x => A.symm (stereoToFun v x)
  have hleft (w : ℂ) : g (F w) = w := by
    change A.symm (stereoToFun v (stereoInvFun hv (A w))) = w
    rw [stereo_right_inv, A.symm_apply_apply]
  have hx : ‖F z‖ = 1 := mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv (A z).property)
  have hneq : innerSL ℝ v (F z) ≠ 1 := by
    intro h
    have he : v = F z := (inner_eq_one_iff_of_norm_eq_one hv hx).mp h
    exact stereoInvFun_ne_north_pole hv (A z) (Subtype.ext he.symm)
  have hopen : IsOpen {x : RoundAmbient | innerSL ℝ v x ≠ 1} :=
    (isClosed_eq (innerSL ℝ v).continuous continuous_const).isOpen_compl
  have hg : ContDiffAt ℝ 1 g (F z) :=
    A.symm.contDiff.contDiffAt.comp (F z)
      ((contDiffOn_stereoToFun (n := 1)).contDiffAt (hopen.mem_nhds hneq))
  obtain ⟨L, W, hW, hL⟩ := hg.exists_lipschitzOnWith
  refine ⟨L, W, hW, fun w u hw hu => ?_⟩
  simpa only [hleft] using hL.dist_le_mul (F w) hw (F u) hu

theorem finite_sphere_chart_inverse_pairs (z : ℂ) :
    ∃ (L : ℝ≥0) (W : Set RoundAmbient),
      W ∈ 𝓝 (roundSphereEquiv (z : Sphere) : RoundAmbient) ∧
      ∀ w u : ℂ, (roundSphereEquiv (w : Sphere) : RoundAmbient) ∈ W →
        (roundSphereEquiv (u : Sphere) : RoundAmbient) ∈ W →
        dist w u ≤ L * dist (roundSphereEquiv (w : Sphere) : RoundAmbient)
          (roundSphereEquiv (u : Sphere) : RoundAmbient) := by
  classical
  simp only [roundSphereEquiv, onePointEquivSphereOfFinrankEq, Homeomorph.trans_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  apply linear_stereo_inverse_pairs
  simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_UniformSphericalBallArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic area estimates with constants uniform near a finite centre. -/

open Set Filter Function Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r01fbe5_10 : BorelSpace Sphere := ⟨rfl⟩
theorem spherical_ball_area_bound_near (z : ℂ) :
    ∃ V : Set Sphere, IsOpen V ∧ (z : Sphere) ∈ V ∧
      ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧
        ∀ w : ℂ, (w : Sphere) ∈ V → ∀ r : ℝ≥0, (r : ℝ) < R →
          sphericalArea (ball (w : Sphere) r) ≤ K * (r : ℝ≥0∞) ^ 2 := by
  obtain ⟨L, W, hW, hL⟩ := finite_sphere_chart_inverse_pairs z
  have hc : Continuous (fun p : Sphere => (roundSphereEquiv p : RoundAmbient)) :=
    continuous_subtype_val.comp roundSphereEquiv.continuous
  obtain ⟨R, hR, hRW⟩ := Metric.mem_nhds_iff.mp (hc.continuousAt.preimage_mem_nhds hW)
  let K : ℝ≥0∞ := 4 * (↑(L + 1) : ℝ≥0∞) ^ 2 * NNReal.pi
  refine ⟨ball (z : Sphere) (R / 2), isOpen_ball, mem_ball_self (by positivity),
    R / 2, by positivity, K, by dsimp [K]; finiteness, ?_⟩
  intro w hw r hr
  have hwW : (roundSphereEquiv (w : Sphere) : RoundAmbient) ∈ W :=
    hRW (ball_subset_ball (by linarith : R / 2 ≤ R) hw)
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' ball (w : Sphere) r
  have hAB : A ⊆ closedBall w ((L + 1 : ℝ≥0) * r) := by
    intro u hu
    have huR : (u : Sphere) ∈ ball (z : Sphere) R := by
      exact (dist_triangle (u : Sphere) (w : Sphere) (z : Sphere)).trans_lt
        (by have h1 : dist (u : Sphere) (w : Sphere) < r := hu
            have h2 : dist (w : Sphere) (z : Sphere) < R / 2 := hw
            linarith)
    have hb := hL u w (hRW huR) hwW
    have hd : dist (u : Sphere) (w : Sphere) < r := hu
    change dist u w ≤ (L + 1 : ℝ≥0) * r
    calc
      dist u w ≤ L * dist (u : Sphere) (w : Sphere) := hb
      _ ≤ L * r := mul_le_mul_of_nonneg_left hd.le L.coe_nonneg
      _ ≤ (L + 1 : ℝ≥0) * r :=
        mul_le_mul_of_nonneg_right (by simp) r.coe_nonneg
  rw [sphericalArea, Measure.map_apply OnePoint.continuous_coe.measurable measurableSet_ball,
    withDensity_apply _ (OnePoint.continuous_coe.measurable measurableSet_ball)]
  calc
    _ ≤ ∫⁻ _ in A, (4 : ℝ≥0∞) := by
      apply lintegral_mono
      intro u
      exact (ENNReal.ofReal_le_ofReal (sphericalAreaDensity_le_four u)).trans_eq (by norm_num)
    _ = 4 * volume A := by simp
    _ ≤ 4 * volume (closedBall w ((L + 1 : ℝ≥0) * r)) :=
      mul_le_mul' le_rfl (measure_mono hAB)
    _ = K * (r : ℝ≥0∞) ^ 2 := by
      rw [Complex.volume_closedBall]
      rw [show ENNReal.ofReal ((L + 1 : ℝ≥0) * r) =
        (↑(L + 1) : ℝ≥0∞) * ↑r from by
          rw [← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul], mul_pow]
      dsimp [K]
      ring

theorem spherical_ball_area_bound_on_compact {T : Set ℂ} (hT : IsCompact T) :
    ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧
      ∀ z ∈ T, ∀ r : ℝ≥0, (r : ℝ) < R →
        sphericalArea (ball (z : Sphere) r) ≤ K * (r : ℝ≥0∞) ^ 2 := by
  classical
  choose V hVo hVm R hRp K hK hbound using spherical_ball_area_bound_near
  obtain ⟨s, hs⟩ := hT.elim_finite_subcover
    (fun z : ℂ => ((↑) : ℂ → Sphere) ⁻¹' V z)
    (fun z => (hVo z).preimage OnePoint.continuous_coe)
    (fun z _ => mem_iUnion.mpr ⟨z, hVm z⟩)
  have hmin : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ s, r ≤ R z := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert z s hz ih =>
      obtain ⟨r, hr, hrR⟩ := ih
      refine ⟨min r (R z), lt_min hr (hRp z), ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hrR w hw)
  obtain ⟨r, hr, hrR⟩ := hmin
  refine ⟨r, hr, ∑ z ∈ s, K z, ENNReal.sum_ne_top.mpr (fun z _ => hK z), ?_⟩
  intro z hz a ha
  obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hs hz)
  exact (hbound w z hzw a (ha.trans_le (hrR w hw))).trans
    (mul_le_mul' (Finset.single_le_sum (fun _ _ => zero_le) hw) le_rfl)

theorem spherical_ball_area_bound_away_infinity (A : Set Sphere)
    (hinf : OnePoint.infty ∉ closure A) :
    ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧
      ∀ p ∈ A, ∀ r : ℝ≥0, (r : ℝ) < R →
        sphericalArea (ball p r) ≤ K * (r : ℝ≥0∞) ^ 2 := by
  have hT : IsCompact (((↑) : ℂ → Sphere) ⁻¹' closure A) :=
    isCompact_finite_preimage isClosed_closure hinf
  obtain ⟨R, hR, K, hK, hb⟩ := spherical_ball_area_bound_on_compact hT
  refine ⟨R, hR, K, hK, ?_⟩
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact (hinf (subset_closure hp)).elim
  | coe z => exact hb z (subset_closure hp)

theorem spherical_ball_sequence_area_bound (A : Set Sphere)
    (hinf : OnePoint.infty ∉ closure A) (a : ℕ → ℝ≥0)
    (hat : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ᶠ n in atTop, ∀ p ∈ A,
      sphericalArea (ball p (2 * a n)) ≤ C * (a n : ℝ≥0∞) ^ 2 := by
  obtain ⟨R, hR, K, hK, hb⟩ := spherical_ball_area_bound_away_infinity A hinf
  refine ⟨4 * K, by finiteness, ?_⟩
  filter_upwards [hat.eventually (gt_mem_nhds (half_pos hR))] with n hn
  intro p hp
  have h2 : ((2 * a n : ℝ≥0) : ℝ) < R := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith
  calc
    sphericalArea (ball p (2 * a n)) ≤ K * ((2 * a n : ℝ≥0) : ℝ≥0∞) ^ 2 :=
      hb p hp (2 * a n) h2
    _ = (4 * K) * (a n : ℝ≥0∞) ^ 2 := by
      rw [ENNReal.coe_mul, ENNReal.coe_ofNat, mul_pow]
      ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableQuotientCodeLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual component quotient supplies the common collar basis and
uniform area constant in the countability theorem. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_11 : BorelSpace Sphere := ⟨rfl⟩
theorem countable_quotient_code_laws {I : Type*} [LinearOrder I]
    (hcross : UnitDiskAlternatingContinua)
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G U B E : Set Sphere) (hG : IsOpen G) (hU : IsOpen U)
    (hdisj : Disjoint U B) (hBU : Bᶜ ⊆ U) (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hE : IsClosed E) (hEU : E ⊆ U)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B) (hinf : π OnePoint.infty ∉ B)
    (d : I → PathCodeData Sphere Sphere)
    (hGd : ∀ i, (d i).physicalDomain = G) (hUd : ∀ i, (d i).quotientDomain = U)
    (hBd : ∀ i, (d i).dust = B) (hEd : ∀ i, (d i).anchor = E)
    (hed : ∀ i, ∀ y : (d i).physicalDomain, ((d i).domainEquiv y).val = π y.val)
    (htarget : ∀ i, (d i).target ∈ B \ {OnePoint.infty})
    (hinj : Injective (fun i => (d i).target))
    (P : ∀ i, ProbabilityMeasure (BasePathCode (d i)))
    [∀ i, SigmaFinite (meanCodeOccupation (d i) (P i))]
    (g : I → Sphere → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (hocc : ∀ i, meanCodeOccupation (d i) (P i) = sphericalArea.withDensity (g i))
    (henergy : ∀ i, (∫⁻ x, g i x ^ 2 ∂sphericalArea) < ∞)
    (hhit : ∀ i, (∑' x : B, codeHitProbability (d i) (P i) x.val ^ 2) < ∞)
    (hcontacts : ∀ i j, i < j → ∃ D : Set Sphere, D.Countable ∧
      ∀ᵐ z ∂((P i : Measure (BasePathCode (d i))).prod (P j : Measure (BasePathCode (d j)))),
        range z.1.val.1 ∩ range z.2.val.1 ∩ (d i).dust ⊆ D) : Countable I := by
  obtain ⟨K, hK, hgood, hbasis⟩ := exists_countable_jordan_collars hcoarea hsard hsch
    G U B E π hπ hclosed hsurj hr hB hTD hBU hdisj hbad hE hEU hinf
  obtain ⟨W, hW, hBW, hWi⟩ := normal_exists_closure_subset hB
    (isClosed_singleton (x := π OnePoint.infty)).isOpen_compl
    (fun x hx h => hinf (h ▸ hx))
  let K' := {k | k ∈ K ∧ quotientJordanDisk k ⊆ W}
  have hK' : K'.Countable := hK.mono (fun _ h => h.1)
  have hg' : ∀ k ∈ K', frontier (quotientJordanDisk k) ⊆ U ∧
      π OnePoint.infty ∉ closure (quotientJordanDisk k) ∧ Disjoint E (quotientJordanDisk k) :=
    fun k hk => hgood k hk.1
  have hb' : ∀ p ∈ B \ {OnePoint.infty}, ∀ O : Set Sphere, IsOpen O → p ∈ O →
      ∃ k ∈ K', p ∈ quotientJordanDisk k ∧ quotientJordanDisk k ⊆ O := by
    intro p hp O hO hpO
    obtain ⟨k, hk, hpk, hsub⟩ := hbasis p hp (O ∩ W) (hO.inter hW) ⟨hpO, hBW hp.1⟩
    exact ⟨k, ⟨hk, hsub.trans inter_subset_right⟩, hpk, hsub.trans inter_subset_left⟩
  let A := π ⁻¹' W
  have hsub : closure A ⊆ π ⁻¹' closure W :=
    closure_minimal (preimage_mono subset_closure) (isClosed_closure.preimage hπ)
  have hAi : OnePoint.infty ∉ closure A := fun h => hWi (hsub h) rfl
  let a : ℕ → ℝ≥0 := fun n => ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have ha (n : ℕ) : 0 < a n := by change 0 < 1 / ((n : ℝ) + 1); positivity
  have hat : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨C, hC, hball⟩ := spherical_ball_sequence_area_bound A hAi a hat
  exact countable_diffuse_code_laws hcross G U B E hG hU hdisj hBU π hπ hclosed hsurj hr
    d hGd hUd hBd hEd hed htarget hinj P g hg hocc henergy hhit hcontacts
    K' hK' hg' hb' a ha hat C hC A (fun _ hk => preimage_mono hk.2) hball

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FullHitSupport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Outside the dust, only the distinguished image of infinity can have
positive hit probability. Thus the full prior-law mark set is countable. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_12 : BorelSpace Sphere := ⟨rfl⟩
theorem codeHitProbability_zero_off_dust
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hend : d.target ∉ d.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity g)
    (henergy : (∫⁻ x, g x ^ 2 ∂sphericalArea) < ∞)
    (x : Sphere) (hx : x ∉ d.dust) (hxi : x ≠ π OnePoint.infty) :
    codeHitProbability d P x = 0 := by
  let y : d.physicalDomain := d.domainEquiv.symm ⟨x, hBU hx⟩
  have hy : π y.val = x := by
    rw [← he y]
    exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨x, hBU hx⟩)
  have hyi : y.val ≠ OnePoint.infty := fun h => hxi (hy.symm.trans (congrArg π h))
  cases heq : y.val using OnePoint.rec with
  | infty => exact (hyi heq).elim
  | coe z =>
    have hz : (z : Sphere) ∈ d.physicalDomain := heq ▸ y.property
    have hzx : π (z : Sphere) = x := heq ▸ hy
    rw [← pathHitProbability_codePathLaw, ← hzx]
    exact finite_domain_point_avoided d hU hG π hπ hclosed hsurj hr he hend P g hg hocc henergy z hz

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem countable_full_hit_support {X : Type*} (m : X → ℝ≥0∞) (B : Set X) (p : X)
    (hB : {x | x ∈ B ∧ 0 < m x}.Countable)
    (hz : ∀ x, x ∉ B → x ≠ p → m x = 0) : (support m).Countable := by
  apply (hB.insert p).mono
  intro x hx
  by_cases hxp : x = p
  · exact Or.inl hxp
  · right
    have hxB : x ∈ B := by
      by_contra hn
      exact hx (hz x hn hxp)
    exact ⟨hxB, pos_iff_ne_zero.mpr hx⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RecursiveCodeLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved outputs retained at one stage of the endpoint-law recursion.
The candidate includes actual densities and quantitative mark budgets. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace RecursiveCodeLaw

variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
  (L : RecursiveCodeLaw base π flags ω)

local instance localInst_r01fbe5_13 : BorelSpace Sphere := ⟨rfl⟩
theorem density_measurable : Measurable L.density := (Classical.choose_spec L.candidate.1.2).1

theorem occupation_eq : meanCodeOccupation L.data L.law = sphericalArea.withDensity L.density :=
  (Classical.choose_spec L.candidate.1.2).2.1

theorem density_energy_finite : (∫⁻ x, L.density x ^ 2 ∂sphericalArea) < ∞ :=
  (Classical.choose_spec L.candidate.1.2).2.2.trans_lt L.energy_finite

theorem finite_occupation : IsFiniteMeasure (meanCodeOccupation L.data L.law) :=
  ⟨L.candidate.1.1.trans_lt L.occupationMass_finite⟩

variable [BorelSpace C(PathTime, Sphere)]

theorem hit_square_finite : (∑' x : base.dust, codeHitProbability L.data L.law x.val ^ 2) < ∞ := by
  have h := (codeHit_square_tsum_le L.data L.law L.hitConstant L.finite_hit_tests).trans_lt
    ENNReal.ofReal_lt_top
  change (∑' x : L.data.dust, codeHitProbability L.data L.law x.val ^ 2) < ∞ at h
  rw [L.dust_eq] at h
  exact h

omit [BorelSpace C(PathTime, Sphere)] in
theorem tuple_absolutelyContinuous : meanCodeTuple L.data L.law ≪ tupleReference ω := by
  obtain ⟨q, _, hq, _⟩ := L.candidate.2.2.2
  rw [hq]
  exact withDensity_absolutelyContinuous _ _

theorem prior_visit_norm_finite (i : ℕ) :
    countingSquareNorm (fun x : support (dustPriorHitMass base.dust (L.data.priorLaws i)) =>
      meanVisitCount (codePathLaw L.data L.law) x.val) < ∞ :=
  L.presentation.prior_visit_norm_finite L.data L.law sphericalArea (tupleReference ω)
    L.occupationMass L.tupleMass L.energy L.visitConstant L.visitConstant_finite L.candidate i

theorem flag_visit_norm_finite (i : ℕ) (hflags : support (base.levelWeights i) ⊆ flags) :
    countingSquareNorm (fun x : support (base.levelWeights i) =>
      meanVisitCount (codePathLaw L.data L.law) x.val) < ∞ :=
  (candidate_visit_norm_on_marks L.data L.law L.presentation.marks _
    (hflags.trans L.presentation.extra_marks) L.candidate.2.1).trans_lt L.visitConstant_finite

theorem full_hit_support_countable
    (hU : IsOpen base.quotientDomain) (hG : IsOpen base.physicalDomain)
    (hBU : base.dustᶜ ⊆ base.quotientDomain)
    (hdisj : Disjoint base.quotientDomain base.dust)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x)) :
    (support (priorHitMass (codePathLaw L.data L.law : Measure C(PathTime, Sphere)))).Countable := by
  have hz (x : Sphere) (hx : x ∉ L.data.dust) (hi : x ≠ π OnePoint.infty) :
      codeHitProbability L.data L.law x = 0 := by
    apply codeHitProbability_zero_off_dust L.data (by simpa only [L.quotient_eq] using hU)
      (by simpa only [L.physical_eq] using hG)
      (by simpa only [L.dust_eq, L.quotient_eq] using hBU)
      π hπ hclosed hsurj (by simpa only [L.physical_eq] using hr) L.domain_agrees
      (fun ht => disjoint_left.mp hdisj (L.quotient_eq ▸ ht) L.target_dust)
      L.law L.density L.density_measurable L.occupation_eq L.density_energy_finite x hx hi
  have hc := countable_full_hit_support (codeHitProbability L.data L.law) L.data.dust
    (π OnePoint.infty) L.countable_dust_hits hz
  apply hc.mono
  intro x hx
  change priorHitMass (codePathLaw L.data L.law : Measure _) x ≠ 0 at hx
  change codeHitProbability L.data L.law x ≠ 0
  rwa [priorHitMass_codePathLaw] at hx

end RecursiveCodeLaw
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_NullLevelTuples
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null sets of scalar levels induce null sets of finite tagged tuples.
This also supplies a Borel description when the null sets are envelopes. -/

open Set Function MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem measurableEmbedding_tupleFiber (i : TupleType) : MeasurableEmbedding (tupleFiber i) := by
  apply (measurable_tupleFiber i).measurableEmbedding
  intro x y h
  have hp : (i.2, x) = (i.2, y) :=
    sigma_mk_injective (β := fun n : ℕ =>
      (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle)) h
  exact congrArg Prod.snd hp

theorem levelTuple_eq_iUnion_fibers (A : Set LevelTuple) :
    A = ⋃ i : TupleType, tupleFiber i '' (tupleFiber i ⁻¹' A) := by
  ext q
  constructor
  · intro hq
    rcases q with ⟨n, l, t⟩
    exact mem_iUnion.mpr ⟨⟨n, l⟩, t, hq, rfl⟩
  · intro h
    obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp h
    exact ht

theorem measurableSet_levelTuple_of_fibers (A : Set LevelTuple)
    (hA : ∀ i : TupleType, MeasurableSet (tupleFiber i ⁻¹' A)) : MeasurableSet A := by
  rw [levelTuple_eq_iUnion_fibers A]
  exact MeasurableSet.iUnion fun i => (measurableEmbedding_tupleFiber i).measurableSet_image.mpr (hA i)

theorem measurableSet_tuplesWithBadLevel (N : ℕ → Set UnitAddCircle)
    (hN : ∀ i, MeasurableSet (N i)) : MeasurableSet (tuplesWithBadLevel N) := by
  apply measurableSet_levelTuple_of_fibers
  intro i
  change MeasurableSet {t : Fin (i.1 + 1) → UnitAddCircle | ∃ j, t j ∈ N (i.2 j)}
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion fun j => (hN (i.2 j)).preimage (measurable_pi_apply j)

theorem tupleReference_badLevel_null (ω : TupleType → ℝ≥0∞)
    (N : ℕ → Set UnitAddCircle) (hN : ∀ i, MeasurableSet (N i))
    (hzero : ∀ i, volume (N i) = 0) : tupleReference ω (tuplesWithBadLevel N) = 0 := by
  rw [tupleReference_apply ω (measurableSet_tuplesWithBadLevel N hN), ENNReal.tsum_eq_zero]
  intro i
  have he : tupleFiber i ⁻¹' tuplesWithBadLevel N =
      ⋃ j : Fin (i.1 + 1), {t : Fin (i.1 + 1) → UnitAddCircle | t j ∈ N (i.2 j)} := by
    ext t
    simp only [mem_iUnion]
    rfl
  rw [he]
  have hz : volume (⋃ j : Fin (i.1 + 1),
      {t : Fin (i.1 + 1) → UnitAddCircle | t j ∈ N (i.2 j)}) = 0 := by
    apply measure_iUnion_null
    intro j
    exact Measure.pi_eval_preimage_null
      (fun _ : Fin (i.1 + 1) => (volume : Measure UnitAddCircle)) (hzero (i.2 j))
  rw [hz, mul_zero]

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem ae_slots_zero_on_null_tuples (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (τ : Measure LevelTuple)
    (hτ : meanCodeTuple d P ≪ τ) (A : Set LevelTuple) (hA : MeasurableSet A)
    (hz : τ A = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k, slotTupleMeasure (Γ.val.2 k) A = 0 := by
  apply ae_all_iff.mpr
  intro k
  have h := slotLaw_absolutelyContinuous d P τ hτ k hz
  rw [slotLaw_apply d P k hA] at h
  exact (lintegral_eq_zero_iff ((Measure.measurable_coe hA).comp
    (measurable_baseCodeSlot d k))).mp h

theorem no_tag_level_in_null_set (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (ω : TupleType → ℝ≥0∞)
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (N : ℕ → Set UnitAddCircle) (hN : ∀ i, MeasurableSet (N i))
    (hzero : ∀ i, volume (N i) = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      ∀ k q, Γ.val.2 k = Sum.inr q → ∀ j, q.2.2.1 j ∉ N (q.2.1 j) := by
  filter_upwards [ae_slots_zero_on_null_tuples d P (tupleReference ω) hτ
    (tuplesWithBadLevel N) (measurableSet_tuplesWithBadLevel N hN)
    (tupleReference_badLevel_null ω N hN hzero)] with Γ hΓ
  intro k q hq j hj
  have hmem : tagDataTuple q ∈ tuplesWithBadLevel N := ⟨j, hj⟩
  have h := hΓ k
  rw [hq, slotTupleMeasure, Sum.elim_inr,
    Measure.dirac_apply' _ (measurableSet_tuplesWithBadLevel N hN),
    indicator_of_mem hmem, Pi.one_apply] at h
  exact one_ne_zero h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ParametricNullTuples
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel scalar-level envelopes remain Borel after forming finite tuples
and active slots, also when they depend on an earlier sampled path. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurableSet_badTupleGraph (N : Ω → ℕ → Set UnitAddCircle)
    (hN : ∀ i, MeasurableSet {q : Ω × UnitAddCircle | q.2 ∈ N q.1 i}) :
    MeasurableSet (badTupleGraph N) := by
  let f (i : TupleType) : Ω × (Fin (i.1 + 1) → UnitAddCircle) → Ω × LevelTuple :=
    Prod.map id (tupleFiber i)
  have he : badTupleGraph N = ⋃ i : TupleType, f i '' (f i ⁻¹' badTupleGraph N) := by
    ext q
    constructor
    · intro hq
      rcases q with ⟨ω, n, l, t⟩
      exact mem_iUnion.mpr ⟨⟨n, l⟩, (ω, t), hq, rfl⟩
    · intro h
      obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp h
      exact hp
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  apply (MeasurableEmbedding.id.prodMap (measurableEmbedding_tupleFiber i)).measurableSet_image.mpr
  change MeasurableSet {q : Ω × (Fin (i.1 + 1) → UnitAddCircle) |
    ∃ j, q.2 j ∈ N q.1 (i.2 j)}
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion fun j => (hN (i.2 j)).preimage
    (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

theorem measurableSet_badSlotGraph (N : Ω → ℕ → Set UnitAddCircle)
    (hN : ∀ i, MeasurableSet {q : Ω × UnitAddCircle | q.2 ∈ N q.1 i}) :
    MeasurableSet (badSlotGraph N) := by
  let : MeasurableSpace TagData := borel TagData
  let : BorelSpace TagData := ⟨rfl⟩
  have he : badSlotGraph N = Prod.map id activeTagSlot ''
      (Prod.map id tagDataTuple ⁻¹' badTupleGraph N) := by
    ext p
    constructor
    · rintro ⟨q, hq, hmem⟩
      exact ⟨(p.1, q), hmem, Prod.ext rfl hq.symm⟩
    · rintro ⟨⟨ω, q⟩, hq, rfl⟩
      exact ⟨q, rfl, hq⟩
  rw [he]
  have hi : Topology.IsOpenEmbedding activeTagSlot :=
    Topology.IsOpenEmbedding.inr
  have hme : MeasurableEmbedding activeTagSlot :=
    Topology.IsOpenEmbedding.measurableEmbedding (α := TagData) (β := TagSlot) hi
  apply (MeasurableEmbedding.id.prodMap hme).measurableSet_image.mpr
  exact (measurableSet_badTupleGraph N hN).preimage
    (measurable_id.prodMap continuous_tagDataTuple.measurable)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ResidualTagAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent later tags avoid the scalar-level null envelopes of an
earlier residual image. The product event is built from Borel envelopes. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {Ω X Y : Type*} [MeasurableSpace Ω] [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem ae_product_no_bad_tag_level (P : ProbabilityMeasure Ω)
    (d : PathCodeData X Y) (Q : ProbabilityMeasure (BasePathCode d))
    (ω : TupleType → ℝ≥0∞) (hτ : meanCodeTuple d Q ≪ tupleReference ω)
    (N : Ω → ℕ → Set UnitAddCircle)
    (hN : ∀ i, MeasurableSet {q : Ω × UnitAddCircle | q.2 ∈ N q.1 i})
    (hzero : ∀ᵐ a ∂(P : Measure Ω), ∀ i, volume (N a i) = 0) :
    ∀ᵐ p ∂((P : Measure Ω).prod (Q : Measure (BasePathCode d))),
      ∀ k q, p.2.val.2 k = Sum.inr q → ∀ j, q.2.2.1 j ∉ N p.1 (q.2.1 j) := by
  have hall : ∀ k, ∀ᵐ p ∂((P : Measure Ω).prod (Q : Measure (BasePathCode d))),
      (p.1, p.2.val.2 k) ∉ badSlotGraph N := by
    intro k
    let E : Set (Ω × BasePathCode d) := {p | (p.1, p.2.val.2 k) ∈ badSlotGraph N}
    have hE : MeasurableSet E := (measurableSet_badSlotGraph N hN).preimage
      (measurable_fst.prodMk ((measurable_pi_apply k).comp
        (measurable_snd.comp (measurable_subtype_coe.comp measurable_snd))))
    have hz : ((P : Measure Ω).prod (Q : Measure (BasePathCode d))) E = 0 := by
      rw [Measure.prod_apply hE]
      calc
        _ = ∫⁻ _a, (0 : ℝ≥0∞) ∂(P : Measure Ω) := by
          apply lintegral_congr_ae
          filter_upwards [hzero] with a ha
          have hNa : ∀ i, MeasurableSet (N a i) := fun i =>
            (hN i).preimage (measurable_const.prodMk measurable_id)
          have hgood := no_tag_level_in_null_set d Q ω hτ (N a) hNa ha
          have hnot : ∀ᵐ Γ ∂(Q : Measure (BasePathCode d)), Γ ∉ Prod.mk a ⁻¹' E := by
            filter_upwards [hgood] with Γ hΓ
            rintro ⟨q, hq, j, hj⟩
            exact hΓ k q hq j hj
          simpa only [ae_iff, not_not, ofPred_mem_eq] using hnot
        _ = 0 := by simp
    have hnot : ∀ᵐ p ∂((P : Measure Ω).prod (Q : Measure (BasePathCode d))), p ∉ E := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using hz
    exact hnot
  filter_upwards [ae_all_iff.mpr hall] with p hp
  intro k q hq j hj
  exact hp k ⟨q, hq, j, hj⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ResidualTagContacts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Application to the actual earlier residual constraints: independent
later tags can meet an earlier residual image only at the prescribed flags. -/

open Set Filter Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_residual_tag_contact_in_flags
    (d e : PathCodeData X Y) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) (hle : e.levels = d.levels)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    (ω : TupleType → ℝ≥0∞) (hτ : meanCodeTuple e Q ≪ tupleReference ω)
    (hm : ∀ i, (support (d.levelWeights i)).Countable)
    (hweight : ∀ i, countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : ∀ i, countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ i x, x ∈ support (d.levelWeights i) →
      ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (S : Set X) (hFS : ∀ n, (d.flagDeletions n : Set X) ⊆ S) :
    ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      ∀ s ∈ residualTimes d.dust p.1.val, ∀ k t,
        tagLeft (p.2.val.2 k) < t → t < tagRight (p.2.val.2 k) →
        p.2.val.1 t = p.1.val.1 s → p.1.val.1 s ∈ S := by
  let N : BasePathCode d → ℕ → Set UnitAddCircle := fun Γ i =>
    ⋂ n, {t | (Γ.val, t) ∈ residualIncidence d.dust univ (d.levels i) (d.flagDeletions n)}
  have hN : ∀ i, MeasurableSet {p : BasePathCode d × UnitAddCircle | p.2 ∈ N p.1 i} := by
    intro i
    simp only [N, mem_iInter, ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    exact (measurableSet_residualIncidence hB isClosed_univ (hH i)
      (d.flagDeletions n).finite_toSet).preimage
        ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  have hz : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ i, volume (N Γ i) = 0 :=
    ae_all_iff.mpr fun i => ae_code_level_envelope_null d P i (hm i)
      (hweight i) (hvisits i) (hcover i)
  filter_upwards [ae_product_no_bad_tag_level P e Q ω hτ N hN hz] with p hp
  intro s hs k t hl hr heq
  by_contra hx
  have hc := (p.2.property.1.2.1 k).2.1 t hl hr
  cases hslot : p.2.val.2 k with
  | inl u =>
    simp only [hslot, tagLeft, Sum.elim_inl] at hl
    exact (not_lt_of_ge le_top) hl
  | inr q =>
    have hactive : ∃ j, (q.2.2.1 j, p.2.val.1 t) ∈ d.levels (q.2.1 j) := by
      rw [hslot] at hc
      simpa only [tagLevelGraph, activeTagLevelGraph, mem_ofPred_eq, hle] using hc
    obtain ⟨j, hj⟩ := hactive
    apply hp k q hslot j
    apply mem_iInter.mpr
    intro n
    exact ⟨s, hs, mem_univ s, heq ▸ hj, fun h => hx (hFS n h)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SlotPairNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent active tag tuples avoid every product-null tuple event.
Inactive slots carry no tuple mass. -/

open Set Filter Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem measurableSet_activeSlotPairs (E : Set (LevelTuple × LevelTuple))
    (hE : MeasurableSet E) : MeasurableSet (activeSlotPairs E) := by
  let : MeasurableSpace TagData := borel TagData
  let : BorelSpace TagData := ⟨rfl⟩
  have hi : Topology.IsOpenEmbedding activeTagSlot := Topology.IsOpenEmbedding.inr
  have hme : MeasurableEmbedding activeTagSlot :=
    Topology.IsOpenEmbedding.measurableEmbedding (α := TagData) (β := TagSlot) hi
  have he : activeSlotPairs E = Prod.map activeTagSlot activeTagSlot ''
      (Prod.map tagDataTuple tagDataTuple ⁻¹' E) := by
    ext p
    constructor
    · rintro ⟨q, r, hq, hr, hqr⟩
      exact ⟨(q, r), hqr, Prod.ext hq.symm hr.symm⟩
    · rintro ⟨⟨q, r⟩, hqr, rfl⟩
      exact ⟨q, r, rfl, rfl, hqr⟩
  rw [he]
  apply (hme.prodMap hme).measurableSet_image.mpr
  exact hE.preimage (continuous_tagDataTuple.measurable.prodMap continuous_tagDataTuple.measurable)

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem ae_active_slots_avoid (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (τ : Measure LevelTuple)
    (hτ : meanCodeTuple d P ≪ τ) (A : Set LevelTuple) (hA : MeasurableSet A)
    (hz : τ A = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k q,
      Γ.val.2 k = Sum.inr q → tagDataTuple q ∉ A := by
  filter_upwards [ae_slots_zero_on_null_tuples d P τ hτ A hA hz] with Γ hΓ
  intro k q hq hmem
  have h := hΓ k
  rw [hq, slotTupleMeasure, Sum.elim_inr, Measure.dirac_apply' _ hA,
    indicator_of_mem hmem, Pi.one_apply] at h
  exact one_ne_zero h

theorem ae_slot_pair_avoids_product_null
    (d e : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    (τ : Measure LevelTuple) [SFinite τ]
    (hP : meanCodeTuple d P ≪ τ) (hQ : meanCodeTuple e Q ≪ τ)
    (E : Set (LevelTuple × LevelTuple)) (hzero : (τ.prod τ) E = 0) :
    ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      ∀ k l q r, p.1.val.2 k = Sum.inr q → p.2.val.2 l = Sum.inr r →
        (tagDataTuple q, tagDataTuple r) ∉ E := by
  obtain ⟨E', hEE', hE', hz⟩ := exists_measurable_superset_of_null hzero
  let A : Set LevelTuple := {t | τ (Prod.mk t ⁻¹' E') ≠ 0}
  have hA : MeasurableSet A := ((measurable_measure_prodMk_left hE')
    (measurableSet_singleton 0)).compl
  have hzA : τ A = 0 := by
    have h := Measure.measure_ae_null_of_prod_null hz
    change ∀ᵐ t ∂τ, τ (Prod.mk t ⁻¹' E') = 0 at h
    exact ae_iff.mp h
  have hfirst := ae_active_slots_avoid d P τ hP A hA hzA
  have hpair (k l : ℕ) :
      ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
        (p.1.val.2 k, p.2.val.2 l) ∉ activeSlotPairs E' := by
    have hmeas : MeasurableSet {p : BasePathCode d × BasePathCode e |
        (p.1.val.2 k, p.2.val.2 l) ∉ activeSlotPairs E'} :=
      (measurableSet_activeSlotPairs E' hE').compl.preimage
        (((measurable_pi_apply k).comp (measurable_snd.comp
          (measurable_subtype_coe.comp measurable_fst))).prodMk
        ((measurable_pi_apply l).comp (measurable_snd.comp
          (measurable_subtype_coe.comp measurable_snd))))
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards [hfirst] with Γ hΓ
    cases hslot : Γ.val.2 k with
    | inl a =>
      apply Eventually.of_forall
      intro Δ h
      obtain ⟨q, r, hq, _, _⟩ := h
      change (Sum.inl a : TagSlot) = Sum.inr q at hq
      cases hq
    | inr q =>
      have hsec : τ (Prod.mk (tagDataTuple q) ⁻¹' E') = 0 := by
        exact not_ne_iff.mp (hΓ k q hslot)
      filter_upwards [ae_active_slots_avoid e Q τ hQ _
        (hE'.preimage (measurable_const.prodMk measurable_id)) hsec] with Δ hΔ
      rintro ⟨q', r, hq', hr, hqr⟩
      have hqq' : q = q' := Sum.inr.inj hq'
      subst q'
      exact hΔ l r hr hqr
  have hall := ae_all_iff.mpr fun k => ae_all_iff.mpr (hpair k)
  filter_upwards [hall] with p hp
  intro k l q r hq hr hmem
  exact hp k l ⟨q, r, hq, hr, hEE' hmem⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TupleProductNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null events on every pair of finite level-torus fibers are null for
the actual positive weighted tuple reference measure. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem tupleReference_product_null (ω : TupleType → ℝ≥0∞)
    (E : Set (LevelTuple × LevelTuple))
    (hE : ∀ i j : TupleType,
      ((volume : Measure (Fin (i.1 + 1) → UnitAddCircle)).prod
        (volume : Measure (Fin (j.1 + 1) → UnitAddCircle)))
        (Prod.map (tupleFiber i) (tupleFiber j) ⁻¹' E) = 0) :
    ((tupleReference ω).prod (tupleReference ω)) E = 0 := by
  rw [tupleReference, Measure.prod_sum, Measure.sum_apply_eq_zero]
  intro p
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    Measure.map_prod_map _ _ (measurable_tupleFiber _) (measurable_tupleFiber _),
    ((measurableEmbedding_tupleFiber _).prodMap
      (measurableEmbedding_tupleFiber _)).map_apply]
  rw [hE, mul_zero, mul_zero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TuplePairCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent tuples satisfy every ordered compatibility test and have
no equal levels carrying the same label across the two tuples. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

variable {X : Type*} [TopologicalSpace X]

theorem ae_torus_pair_distinct {n m : ℕ} :
    ∀ᵐ p ∂((volume : Measure (Fin n → UnitAddCircle)).prod
      (volume : Measure (Fin m → UnitAddCircle))), ∀ i j, p.1 i ≠ p.2 j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  have hd : ((volume : Measure UnitAddCircle).prod volume)
      {p : UnitAddCircle × UnitAddCircle | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply (isClosed_eq continuous_fst continuous_snd).measurableSet]
    have hz : (volume : Measure UnitAddCircle) {0} = 0 := by
      simpa only [image_singleton, AddCircle.coe_zero] using
        (volume_addCircle_image_eq_zero (A := {(0 : ℝ)}) (measure_singleton 0))
    simp [hz]
  have hp := (measurePreserving_eval (fun _ : Fin n => (volume : Measure UnitAddCircle)) i).prod
    (measurePreserving_eval (fun _ : Fin m => (volume : Measure UnitAddCircle)) j)
  have hgood : ∀ᵐ p ∂((volume : Measure UnitAddCircle).prod volume), p.1 ≠ p.2 := by
    rw [ae_iff]
    simpa only [not_not] using hd
  exact hp.quasiMeasurePreserving.ae hgood

theorem tupleReference_pair_incompatible_null
    (H : ℕ → Set (UnitAddCircle × X)) (F : Set X)
    (hP : OrderedLevelNullCompatibility H F) (ω : TupleType → ℝ≥0∞) :
    ((tupleReference ω).prod (tupleReference ω))
      {p | ¬ TuplePairCompatible H F p.1 p.2} = 0 := by
  apply tupleReference_product_null
  intro i j
  have hleft := ae_finite_tuple_ordered_compatibility H F hP i.2 j.2
  have hright := Measure.measurePreserving_swap.quasiMeasurePreserving.ae
    (ae_finite_tuple_ordered_compatibility H F hP j.2 i.2)
  have hall : ∀ᵐ p ∂((volume : Measure (Fin (i.1 + 1) → UnitAddCircle)).prod
      (volume : Measure (Fin (j.1 + 1) → UnitAddCircle))),
      TuplePairCompatible H F (tupleFiber i p.1) (tupleFiber j p.2) := by
    filter_upwards [ae_torus_pair_distinct, hleft, hright] with p hp hl hr
    exact ⟨fun a b _ => hp a b, hl, hr⟩
  exact ae_iff.mp hall

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TagComponents
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonconstant active tag lies in a nontrivial connected component
through each of its interior image points. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
theorem nontrivial_component_of_tag (γ : C(PathTime, X)) (s : TagSlot)
    (hshape : (γ, s) ∈ validTagShape) (A : Set X)
    (hcontain : ∀ t, tagLeft s < t → t < tagRight s → γ t ∈ A)
    (t : PathTime) (hl : tagLeft s < t) (hr : t < tagRight s) :
    (connectedComponentIn A (γ t)).Nontrivial := by
  have hnonconstant : (γ, s) ∈ nonconstantTagSegment := by
    rcases hshape with h | h
    · obtain ⟨u, hu⟩ := h
      change Sum.inl u = s at hu
      rw [← hu] at hl
      exact (not_lt_of_ge le_top hl).elim
    · exact h
  obtain ⟨a, b, ha, ha', hb, hb', hab⟩ := hnonconstant
  have hconn : IsPreconnected (γ '' Ioo (tagLeft s) (tagRight s)) :=
    isPreconnected_Ioo.image γ γ.continuous.continuousOn
  have hsub : γ '' Ioo (tagLeft s) (tagRight s) ⊆ A := by
    rintro x ⟨u, hu, rfl⟩
    exact hcontain u hu.1 hu.2
  have hcc := hconn.subset_connectedComponentIn (mem_image_of_mem γ ⟨hl, hr⟩) hsub
  exact ⟨γ a, hcc (mem_image_of_mem γ ⟨ha, ha'⟩),
    γ b, hcc (mem_image_of_mem γ ⟨hb, hb'⟩), hab⟩

omit [T2Space X] in
theorem active_tag_nontrivial_component
    (H : ℕ → Set (UnitAddCircle × X)) (γ : C(PathTime, X)) (q : TagData)
    (hshape : (γ, Sum.inr q) ∈ validTagShape)
    (hcontain : (γ, Sum.inr q) ∈ tagContainment H)
    (t : PathTime) (hl : tagLeft (Sum.inr q) < t) (hr : t < tagRight (Sum.inr q)) :
    (connectedComponentIn (⋃ j : Fin (q.1 + 1), {x | (q.2.2.1 j, x) ∈ H (q.2.1 j)})
      (γ t)).Nontrivial := by
  apply nontrivial_component_of_tag γ (Sum.inr q) hshape _ _ t hl hr
  intro u hu hu'
  exact mem_iUnion.mpr (hcontain u hu hu')

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TagPairTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The topological part of excluding free contacts of two tags. At the
largest level label present at a contact, the other tag gives a forbidden
nontrivial component in lower levels. -/

open Set Function
open scoped Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

theorem tag_impossible_below_compatible_level
    (H : ℕ → Set (UnitAddCircle × X)) (hH : ∀ i, IsClosed (H i))
    (γ : C(PathTime, X)) (q : TagData)
    (hshape : (γ, Sum.inr q) ∈ validTagShape)
    (hcontain : (γ, Sum.inr q) ∈ tagContainment H)
    (t : PathTime) (hl : tagLeft (Sum.inr q) < t) (hr : t < tagRight (Sum.inr q))
    (j : ℕ)
    (hbelow : ∀ k, (q.2.2.1 k, γ t) ∈ H (q.2.1 k) → q.2.1 k < j)
    (hcompat : ∀ A : Finset (Fin (q.1 + 1)), (∀ k ∈ A, q.2.1 k < j) →
      ¬ (connectedComponentIn (⋃ k ∈ A, {x | (q.2.2.1 k, x) ∈ H (q.2.1 k)})
        (γ t)).Nontrivial) : False := by
  let L : Fin (q.1 + 1) → Set X := fun k => {x | (q.2.2.1 k, x) ∈ H (q.2.1 k)}
  let A : Finset (Fin (q.1 + 1)) := Finset.univ.filter (fun k => γ t ∈ L k)
  have hx : γ t ∈ ⋃ k, L k := mem_iUnion.mpr (hcontain t hl hr)
  have hxA : γ t ∈ ⋃ k ∈ A, L k := by
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact mem_iUnion₂.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩, hk⟩
  have he : (⋃ k ∈ (Finset.univ : Finset (Fin (q.1 + 1))),
      ⋃ (_ : γ t ∈ L k), L k) = ⋃ k ∈ A, L k := by
    ext x
    simp only [mem_iUnion, exists_prop, Finset.mem_univ, true_and, A, Finset.mem_filter]
  have hsmall : connectedComponentIn (⋃ k ∈ A, L k) (γ t) = {γ t} :=
    (Set.not_nontrivial_iff.mp (hcompat A (fun k hk =>
      hbelow k (Finset.mem_filter.mp hk).2))).eq_singleton_of_mem (mem_connectedComponentIn hxA)
  have hsingle : connectedComponentIn (⋃ k, L k) (γ t) = {γ t} := by
    have h := component_finite_union_eq_singleton Finset.univ L
      (fun k _ => (hH _).preimage (continuous_const.prodMk continuous_id))
      (by simpa only [Finset.mem_univ, iUnion_true] using hx)
      (by rw [he]; exact hsmall)
    simpa only [Finset.mem_univ, iUnion_true] using h
  have hn := active_tag_nontrivial_component H γ q hshape hcontain t hl hr
  rw [hsingle] at hn
  exact Set.not_nontrivial_singleton hn

theorem incompatible_tag_pair_at_point
    (H : ℕ → Set (UnitAddCircle × X)) (hH : ∀ i, IsClosed (H i))
    (γ δ : C(PathTime, X)) (q r : TagData)
    (hqshape : (γ, Sum.inr q) ∈ validTagShape)
    (hrshape : (δ, Sum.inr r) ∈ validTagShape)
    (hqcontain : (γ, Sum.inr q) ∈ tagContainment H)
    (hrcontain : (δ, Sum.inr r) ∈ tagContainment H)
    (t u : PathTime) (htl : tagLeft (Sum.inr q) < t) (htr : t < tagRight (Sum.inr q))
    (hul : tagLeft (Sum.inr r) < u) (hur : u < tagRight (Sum.inr r))
    (heq : δ u = γ t)
    (hunique : ∀ i a b, (a, γ t) ∈ H i → (b, γ t) ∈ H i → a = b)
    (hcross : ∀ i j, q.2.1 i = r.2.1 j → q.2.2.1 i ≠ r.2.2.1 j)
    (hleft : ∀ j, (r.2.2.1 j, γ t) ∈ H (r.2.1 j) →
      ∀ A : Finset (Fin (q.1 + 1)), (∀ k ∈ A, q.2.1 k < r.2.1 j) →
        ¬ (connectedComponentIn (⋃ k ∈ A, {x | (q.2.2.1 k, x) ∈ H (q.2.1 k)})
          (γ t)).Nontrivial)
    (hright : ∀ i, (q.2.2.1 i, δ u) ∈ H (q.2.1 i) →
      ∀ A : Finset (Fin (r.1 + 1)), (∀ k ∈ A, r.2.1 k < q.2.1 i) →
        ¬ (connectedComponentIn (⋃ k ∈ A, {x | (r.2.2.1 k, x) ∈ H (r.2.1 k)})
          (δ u)).Nontrivial) : False := by
  let L := Finset.univ.filter (fun i : Fin (q.1 + 1) => (q.2.2.1 i, γ t) ∈ H (q.2.1 i))
  let R := Finset.univ.filter (fun j : Fin (r.1 + 1) => (r.2.2.1 j, γ t) ∈ H (r.2.1 j))
  have hL : L.Nonempty := by
    obtain ⟨i, hi⟩ := hqcontain t htl htr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hR : R.Nonempty := by
    have hr' : ∃ j, (r.2.2.1 j, γ t) ∈ H (r.2.1 j) := by
      simpa only [heq, tagLevelGraph, activeTagLevelGraph, mem_ofPred_eq] using hrcontain u hul hur
    obtain ⟨j, hj⟩ := hr'
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨i, hi, hmaxi⟩ := L.exists_max_image q.2.1 hL
  obtain ⟨j, hj, hmaxj⟩ := R.exists_max_image r.2.1 hR
  have hqi : (q.2.2.1 i, γ t) ∈ H (q.2.1 i) := (Finset.mem_filter.mp hi).2
  have hrj : (r.2.2.1 j, γ t) ∈ H (r.2.1 j) := (Finset.mem_filter.mp hj).2
  rcases lt_trichotomy (q.2.1 i) (r.2.1 j) with hlt | he | hgt
  · apply tag_impossible_below_compatible_level H hH γ q hqshape hqcontain t htl htr
      (r.2.1 j) _ (hleft j hrj)
    intro k hk
    exact (hmaxi k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)).trans_lt hlt
  · exact hcross i j he (hunique (q.2.1 i) _ _ hqi (he ▸ hrj))
  · apply tag_impossible_below_compatible_level H hH δ r hrshape hrcontain u hul hur
      (q.2.1 i) _ (hright i (heq ▸ hqi))
    intro k hk
    have hk' : (r.2.2.1 k, γ t) ∈ H (r.2.1 k) := heq ▸ hk
    exact (hmaxj k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩)).trans_lt hgt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TagPairAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered compatibility and tuple absolute continuity exclude every
free contact between two independent active tags. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem ae_no_tag_pair_contact
    (d e : PathCodeData X Y) (hle : e.levels = d.levels)
    (hH : ∀ i, IsClosed (d.levels i)) (F : Set X)
    (hP : OrderedLevelNullCompatibility d.levels F)
    (hunique : ∀ x ∈ F, ∀ i a b, (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτP : meanCodeTuple d P ≪ tupleReference ω)
    (hτQ : meanCodeTuple e Q ≪ tupleReference ω) :
    ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      ∀ k l t u, tagLeft (p.1.val.2 k) < t → t < tagRight (p.1.val.2 k) →
        tagLeft (p.2.val.2 l) < u → u < tagRight (p.2.val.2 l) →
        p.1.val.1 t ∈ F → p.2.val.1 u ≠ p.1.val.1 t := by
  have hnull := tupleReference_pair_incompatible_null d.levels F hP ω
  filter_upwards [ae_slot_pair_avoids_product_null d e P Q (tupleReference ω) hτP hτQ
    {p | ¬ TuplePairCompatible d.levels F p.1 p.2} hnull] with p hp
  intro k l t u htl htr hul hur hx heq
  cases hq : p.1.val.2 k with
  | inl a =>
    simp only [hq, tagLeft, Sum.elim_inl] at htl
    exact not_lt_of_ge le_top htl
  | inr q =>
    cases hr : p.2.val.2 l with
    | inl a =>
      simp only [hr, tagLeft, Sum.elim_inl] at hul
      exact not_lt_of_ge le_top hul
    | inr r =>
      have hc : TuplePairCompatible d.levels F (tagDataTuple q) (tagDataTuple r) :=
        not_not.mp (hp k l q r hq hr)
      have hrc : (p.2.val.1, (Sum.inr r : TagSlot)) ∈ tagContainment d.levels := by
        rw [← hle]
        exact hr ▸ (p.2.property.1.2.1 l).2.1
      apply incompatible_tag_pair_at_point d.levels hH p.1.val.1 p.2.val.1 q r
        (hq ▸ (p.1.property.1.2.1 k).1) (hr ▸ (p.2.property.1.2.1 l).1)
        (hq ▸ (p.1.property.1.2.1 k).2.1)
        hrc
        t u (hq ▸ htl) (hq ▸ htr) (hr ▸ hul) (hr ▸ hur) heq
        (hunique _ hx) hc.1
      · intro j hj A hA
        exact hc.2.1 j A hA _ hx hj
      · intro i hi A hA
        exact hc.2.2 i A hA _ (heq ▸ hx) hi

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DustBoundDiffuseIntersections
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diffuse dust intersections using only the visit bounds on dust marks.
No visit bound is required at the distinguished image of infinity. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

private theorem tag_interval_of_not_residual {X : Type*} [TopologicalSpace X]
    (B : Set X) (Γ : TaggedPath X) (t : PathTime) (ht : Γ.1 t ∈ B)
    (hres : t ∉ residualTimes B Γ) :
    ∃ k, tagLeft (Γ.2 k) < t ∧ t < tagRight (Γ.2 k) := by
  by_contra h
  apply hres
  refine ⟨ht, ?_⟩
  intro k
  by_cases hl : t ≤ tagLeft (Γ.2 k)
  · exact Or.inl hl
  · right
    by_contra hr
    exact h ⟨k, lt_of_not_ge hl, lt_of_not_ge hr⟩

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_diffuse_dust_intersections_of_dust_bounds
    (d e : PathCodeData X Y) (hB : IsClosed d.dust) (hde : e.dust = d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) (hle : e.levels = d.levels)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    (i : ℕ) (hprior : e.priorLaws i = (codePathLaw d P : Measure C(PathTime, X)))
    (hm : (support (dustPriorHitMass e.dust (e.priorLaws i))).Countable)
    (hweight : countingSquareNorm (fun x : support (dustPriorHitMass e.dust (e.priorLaws i)) =>
      dustPriorHitMass e.dust (e.priorLaws i) x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (dustPriorHitMass e.dust (e.priorLaws i)) =>
      meanVisitCount (codePathLaw e Q) x.val) < ∞)
    (hcover : ∀ x ∈ support (dustPriorHitMass e.dust (e.priorLaws i)),
      ∀ᶠ n in atTop, x ∈ e.priorDeletions i n)
    (hsub : ∀ n, (e.priorDeletions i n : Set X) ⊆ support (priorHitMass (e.priorLaws i)))
    (S : Set X) (hFS : ∀ n, (d.flagDeletions n : Set X) ⊆ S)
    (hmlevel : ∀ j, (support (d.levelWeights j)).Countable)
    (hwlevel : ∀ j, countingSquareNorm (fun x : support (d.levelWeights j) =>
      d.levelWeights j x.val) < ∞)
    (hvlevel : ∀ j, countingSquareNorm (fun x : support (d.levelWeights j) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hflagcover : ∀ j x, x ∈ support (d.levelWeights j) →
      ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hcompat : OrderedLevelNullCompatibility d.levels (d.dust \ S))
    (hunique : ∀ x ∈ d.dust \ S, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτP : meanCodeTuple d P ≪ tupleReference ω)
    (hτQ : meanCodeTuple e Q ≪ tupleReference ω) :
    ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      range p.1.val.1 ∩ range p.2.val.1 ∩ d.dust ⊆
        S ∪ support (priorHitMass (e.priorLaws i)) := by
  have hpriorAE := ae_later_residual_contact_in_prior_support_of_dust_bounds d e (hde ▸ hB)
    P Q i hprior hm hweight hvisits hcover hsub
  have hresAE := ae_residual_tag_contact_in_flags d e hB hH hle P Q ω hτQ
    hmlevel hwlevel hvlevel hflagcover S hFS
  have htagAE := ae_no_tag_pair_contact d e hle hH (d.dust \ S)
    hcompat hunique P Q ω hτP hτQ
  filter_upwards [hpriorAE, hresAE, htagAE] with p hp hr ht
  rintro x ⟨⟨⟨t, htx⟩, ⟨u, hux⟩⟩, hxB⟩
  by_cases hxS : x ∈ S
  · exact Or.inl hxS
  have hnewB : p.2.val.1 u ∈ e.dust := by rw [hux, hde]; exact hxB
  by_cases hnew : u ∈ residualTimes e.dust p.2.val
  · right
    rw [← hux]
    exact hp u hnew ⟨t, htx.trans hux.symm⟩
  obtain ⟨l, hul, hur⟩ := tag_interval_of_not_residual e.dust p.2.val u hnewB hnew
  have holdB : p.1.val.1 t ∈ d.dust := htx ▸ hxB
  by_cases hold : t ∈ residualTimes d.dust p.1.val
  · exact (hxS (htx ▸ hr t hold l u hul hur (hux.trans htx.symm))).elim
  obtain ⟨k, htl, htr⟩ := tag_interval_of_not_residual d.dust p.1.val t holdB hold
  exact (ht k l t u htl htr hul hur ⟨holdB, htx ▸ hxS⟩ (hux.trans htx.symm)).elim

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RecursiveLawContacts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every earlier law retained in a later stage has only countably many
dust contacts with it. All visit hypotheses are supplied by the candidates. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_14 : BorelSpace Sphere := ⟨rfl⟩
theorem RecursiveCodeLaw.countable_contacts
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {flags : Set Sphere} {ω : TupleType → ℝ≥0∞} [SFinite (tupleReference ω)]
    (L M : RecursiveCodeLaw base π flags ω)
    (hB : IsClosed base.dust) (hflags : flags.Countable)
    (hH : ∀ i, IsClosed (base.levels i))
    (hweights : ∀ i, (∑' x, base.levelWeights i x ^ 2) < ∞)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ flags)
    (hcompat : OrderedLevelNullCompatibility base.levels (base.dust \ flags))
    (hunique : ∀ x ∈ base.dust \ flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (i : ℕ) (hprior : M.data.priorLaws i = (codePathLaw L.data L.law : Measure C(PathTime, Sphere))) :
    ∃ D : Set Sphere, D.Countable ∧
      ∀ᵐ z ∂((L.law : Measure (BasePathCode L.data)).prod
        (M.law : Measure (BasePathCode M.data))),
        range z.1.val.1 ∩ range z.2.val.1 ∩ L.data.dust ⊆ D := by
  have hde : M.data.dust = L.data.dust := M.dust_eq.trans L.dust_eq.symm
  have heq : support (dustPriorHitMass M.data.dust (M.data.priorLaws i)) =
      {x | x ∈ L.data.dust ∧ 0 < codeHitProbability L.data L.law x} := by
    rw [hde, hprior, support_dustPriorHitMass]
    ext x
    simp only [mem_inter_iff, mem_support, priorHitMass_codePathLaw, mem_ofPred_eq,
      pos_iff_ne_zero]
  have hm : (support (dustPriorHitMass M.data.dust (M.data.priorLaws i))).Countable :=
    heq.symm ▸ L.countable_dust_hits
  have hw : countingSquareNorm (fun x : support
      (dustPriorHitMass M.data.dust (M.data.priorLaws i)) =>
        dustPriorHitMass M.data.dust (M.data.priorLaws i) x.val) < ∞ := by
    rw [M.dust_eq, hprior]
    exact dust_prior_weight_norm_finite L.data L.law base.dust L.hit_square_finite
  have hv : countingSquareNorm (fun x : support
      (dustPriorHitMass M.data.dust (M.data.priorLaws i)) =>
        meanVisitCount (codePathLaw M.data M.law) x.val) < ∞ := by
    rw [M.dust_eq]
    exact M.prior_visit_norm_finite i
  have hc : ∀ x ∈ support (dustPriorHitMass M.data.dust (M.data.priorLaws i)),
      ∀ᶠ n in atTop, x ∈ M.data.priorDeletions i n := by
    intro x hx
    rw [support_dustPriorHitMass] at hx
    simpa only [M.prior_deletions_eq] using M.presentation.prior_cover i x hx.2
  have hs : ∀ n, (M.data.priorDeletions i n : Set Sphere) ⊆
      support (priorHitMass (M.data.priorLaws i)) := by
    intro n
    simpa only [M.prior_deletions_eq] using M.presentation.prior_subset i n
  have hf : ∀ n, (L.data.flagDeletions n : Set Sphere) ⊆ flags := by
    intro n
    simpa only [L.flag_deletions_eq] using L.presentation.flag_subset n
  have hlcount (j : ℕ) : (support (L.data.levelWeights j)).Countable := by
    rw [L.weights_eq]
    exact hflags.mono (hmarked j)
  have hlweight (j : ℕ) : countingSquareNorm (fun x : support (L.data.levelWeights j) =>
      L.data.levelWeights j x.val) < ∞ := by
    rw [L.weights_eq]
    apply (countingSquareNorm_comp_injective (base.levelWeights j)
      (fun x : support (base.levelWeights j) => x.val) Subtype.val_injective).trans_lt
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hweights j).ne
  have hlvisit (j : ℕ) : countingSquareNorm (fun x : support (L.data.levelWeights j) =>
      meanVisitCount (codePathLaw L.data L.law) x.val) < ∞ := by
    rw [L.weights_eq]
    exact L.flag_visit_norm_finite j (hmarked j)
  have hlcover : ∀ j x, x ∈ support (L.data.levelWeights j) →
      ∀ᶠ n in atTop, x ∈ L.data.flagDeletions n := by
    intro j x hx
    rw [L.weights_eq] at hx
    simpa only [L.flag_deletions_eq] using L.presentation.flag_cover x (hmarked j hx)
  have hraw := ae_diffuse_dust_intersections_of_dust_bounds L.data M.data
    (by simpa only [L.dust_eq] using hB) hde
    (by simpa only [L.levels_eq] using hH) (M.levels_eq.trans L.levels_eq.symm)
    L.law M.law i hprior hm hw hv hc hs flags hf hlcount hlweight hlvisit hlcover
    (by simpa only [L.levels_eq, L.dust_eq] using hcompat)
    (by simpa only [L.levels_eq, L.dust_eq] using hunique)
    ω L.tuple_absolutelyContinuous M.tuple_absolutelyContinuous
  refine ⟨flags ∪ support (dustPriorHitMass M.data.dust (M.data.priorLaws i)),
    hflags.union hm, ?_⟩
  filter_upwards [hraw] with z hz
  intro x hx
  rcases hz hx with hxf | hxp
  · exact Or.inl hxf
  · right
    rw [support_dustPriorHitMass]
    exact ⟨hde.symm ▸ hx.2, hxp⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableRecursiveLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the crossing countability theorem to the recursively retained
laws. The earlier-law lookup is the only ordering information required. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_15 : BorelSpace Sphere := ⟨rfl⟩
theorem countable_recursive_code_laws {I : Type*} [LinearOrder I]
    (hcross : UnitDiskAlternatingContinua)
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdisj : Disjoint base.quotientDomain base.dust) (hBU : base.dustᶜ ⊆ base.quotientDomain)
    (hB : IsClosed base.dust) (hTD : IsTotallyDisconnected base.dust)
    (hE : IsClosed base.anchor) (hEU : base.anchor ⊆ base.quotientDomain)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hbad : ∀ x ∈ base.physicalDomainᶜ, π x ∈ base.dust)
    (hinf : π OnePoint.infty ∉ base.dust)
    (flags : Set Sphere) (hflags : flags.Countable)
    (hH : ∀ i, IsClosed (base.levels i))
    (hweights : ∀ i, (∑' x, base.levelWeights i x ^ 2) < ∞)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ flags)
    (hcompat : OrderedLevelNullCompatibility base.levels (base.dust \ flags))
    (hunique : ∀ x ∈ base.dust \ flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (L : I → RecursiveCodeLaw base π flags ω)
    (hfinite : ∀ i, (L i).data.target ≠ OnePoint.infty)
    (hinj : Injective (fun i => (L i).data.target))
    (hprior : ∀ i j, i < j → ∃ n,
      (L j).data.priorLaws n = (codePathLaw (L i).data (L i).law : Measure C(PathTime, Sphere))) : Countable I := by
  let : ∀ i, IsFiniteMeasure (meanCodeOccupation (L i).data (L i).law) :=
    fun i => (L i).finite_occupation
  apply countable_quotient_code_laws hcross hcoarea hsard hsch
    base.physicalDomain base.quotientDomain base.dust base.anchor hG hU hdisj hBU hB hTD hE hEU
    π hπ hclosed hsurj hr hbad hinf (fun i => (L i).data)
    (fun i => (L i).physical_eq) (fun i => (L i).quotient_eq)
    (fun i => (L i).dust_eq) (fun i => (L i).anchor_eq)
    (fun i => (L i).domain_agrees) (fun i => ⟨(L i).target_dust, hfinite i⟩) hinj
    (fun i => (L i).law) (fun i => (L i).density) (fun i => (L i).density_measurable)
    (fun i => (L i).occupation_eq) (fun i => (L i).density_energy_finite)
    (fun i => (L i).hit_square_finite)
  intro i j hij
  obtain ⟨n, hn⟩ := hprior i j hij
  exact (L i).countable_contacts (L j) hB hflags hH hweights hmarked hcompat hunique n hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PositiveBarrierLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCountableElemFirstUncountableIio _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
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

local instance localInst_r01fbe5_16 : BorelSpace Sphere := ⟨rfl⟩
theorem positive_code_law_of_no_small_barrier
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
    (previous : ℕ → PhysicalRealCoordinate d π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      circleBandGraph d.quotientDomain (previous i).quotient)
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
    (hno : ∀ R : CompatibleRealBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
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
    prescribed_countable_law_of_no_small_barrier hcoarea hLusin hsard hsch
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
-- module Solutions.Q146_CD.CircleDomains_Selection_CountablePriorRecursion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recursive selection with every strict predecessor retained. The later
law construction instantiates this with a well-order whose initial segments
are countable, so all earlier laws are among its prescribed constraints. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

theorem exists_prior_compatible_family {I A : Type*} [LinearOrder I] [WellFoundedLT I]
    (P : ∀ i : I, (Iio i → A) → A → Prop)
    (hP : ∀ (i : I) (g : Iio i → A), ∃ a, P i g a) :
    ∃ f : I → A, ∀ i, P i (fun j => f j.val) (f i) := by
  let F (i : I) (g : ∀ j : I, j < i → A) : A :=
    Classical.choose (hP i (fun j => g j.val j.property))
  let f : I → A := WellFounded.fix wellFounded_lt F
  refine ⟨f, ?_⟩
  intro i
  have he : f i = F i (fun j _ => f j) := WellFounded.fix_eq wellFounded_lt F i
  rw [he]
  exact Classical.choose_spec (hP i (fun j => f j.val))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstUncountableRecursion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first uncountable well-order has countable strict initial segments.
This is the precise index set for retaining every earlier path law. -/

open Set Function Cardinal Ordinal
open scoped Cardinal Ordinal

noncomputable section
namespace CircleDomainRigidity

theorem firstUncountable_not_countable : ¬Countable FirstUncountable := by
  rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_toType]
  simp

theorem exists_injective_firstUncountable {X : Type} (S : Set X)
    (hS : ¬S.Countable) : ∃ f : FirstUncountable → X,
      Injective f ∧ range f ⊆ S := by
  have hc : ℵ₁ ≤ Cardinal.mk S := by
    rw [Cardinal.aleph_one_le_iff, Cardinal.aleph0_lt_mk_iff]
    exact not_countable_iff.mp (Set.countable_coe_iff.not.mpr hS)
  have hcard : Cardinal.mk FirstUncountable ≤ Cardinal.mk S := by
    simpa only [FirstUncountable, Cardinal.mk_toType, Ordinal.card_omega] using hc
  obtain ⟨f⟩ := (Cardinal.le_def _ _).mp hcard
  exact ⟨fun i => (f i).val, Subtype.val_injective.comp f.injective,
    by rintro x ⟨i, rfl⟩; exact (f i).property⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RecursiveLawSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retaining every predecessor in a well-ordered construction.  The selection
hypothesis is discharged by the positive-law construction in the application. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [BorelSpace C(PathTime, Sphere)] in
theorem exists_recursive_code_laws {I : Type*} [LinearOrder I] [WellFoundedLT I]
    [∀ i : I, Countable (Iio i)]
    (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (flags : Set Sphere) (ω : TupleType → ℝ≥0∞) (p : I → Sphere)
    (hfull : ∀ L : RecursiveCodeLaw base π flags ω,
      (support (priorHitMass (codePathLaw L.data L.law : Measure C(PathTime, Sphere)))).Countable)
    (hselect : ∀ (i : I) (μ : ℕ → Measure C(PathTime, Sphere)),
      (∀ n, IsFiniteMeasure (μ n)) →
      (∀ n, (support (priorHitMass (μ n))).Countable) →
      ∃ L : RecursiveCodeLaw base π flags ω,
        L.data.target = p i ∧ L.data.priorLaws = μ) :
    ∃ L : I → RecursiveCodeLaw base π flags ω,
      (∀ i, (L i).data.target = p i) ∧
      ∀ i j, i < j → ∃ n,
        (L j).data.priorLaws n = (codePathLaw (L i).data (L i).law : Measure C(PathTime, Sphere)) := by
  let P (i : I) (g : Iio i → RecursiveCodeLaw base π flags ω)
      (L : RecursiveCodeLaw base π flags ω) : Prop :=
    L.data.target = p i ∧ ∀ j : Iio i, ∃ n,
      L.data.priorLaws n = (codePathLaw (g j).data (g j).law : Measure C(PathTime, Sphere))
  have hP (i : I) (g : Iio i → RecursiveCodeLaw base π flags ω) : ∃ L, P i g L := by
    obtain ⟨μ, hmem, hμ⟩ := exists_countable_enumeration_with_default
      (fun j => (codePathLaw (g j).data (g j).law : Measure C(PathTime, Sphere))) 0
    have hc (n : ℕ) : (support (priorHitMass (μ n))).Countable := by
      rcases hμ n with hn | ⟨j, hn⟩
      · rw [hn]
        have hz : support (priorHitMass (0 : Measure C(PathTime, Sphere))) = ∅ := by
          ext x
          simp [priorHitMass, mem_support]
        rw [hz]
        exact countable_empty
      · rw [hn]
        exact hfull (g j)
    have hf (n : ℕ) : IsFiniteMeasure (μ n) := by
      rcases hμ n with hn | ⟨j, hn⟩
      · rw [hn]
        first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
      · rw [hn]
        first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    obtain ⟨L, ht, hL⟩ := hselect i μ hf hc
    refine ⟨L, ht, ?_⟩
    intro j
    obtain ⟨n, hn⟩ := hmem j
    exact ⟨n, by rw [hL]; exact hn⟩
  obtain ⟨L, hL⟩ := exists_prior_compatible_family P hP
  exact ⟨L, fun i => (hL i).1, fun i j hij => (hL j).2 ⟨i, hij⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RecursiveEndpointCountability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first uncountable recursion and the actual crossing estimate exclude
uncountably many endpoints admitting the recursive positive-law selection. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem countable_endpoints_of_recursive_selection
    (hcross : UnitDiskAlternatingContinua)
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdisj : Disjoint base.quotientDomain base.dust) (hBU : base.dustᶜ ⊆ base.quotientDomain)
    (hB : IsClosed base.dust) (hTD : IsTotallyDisconnected base.dust)
    (hE : IsClosed base.anchor) (hEU : base.anchor ⊆ base.quotientDomain)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hbad : ∀ x ∈ base.physicalDomainᶜ, π x ∈ base.dust)
    (hinf : π OnePoint.infty ∉ base.dust)
    (flags : Set Sphere) (hflags : flags.Countable)
    (hH : ∀ i, IsClosed (base.levels i))
    (hweights : ∀ i, (∑' x, base.levelWeights i x ^ 2) < ∞)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ flags)
    (hcompat : OrderedLevelNullCompatibility base.levels (base.dust \ flags))
    (hunique : ∀ x ∈ base.dust \ flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (S : Set Sphere) (hS : S ⊆ base.dust \ {OnePoint.infty})
    (hselect : ∀ (p : Sphere), p ∈ S → ∀ (μ : ℕ → Measure C(PathTime, Sphere)),
      (∀ n, IsFiniteMeasure (μ n)) →
      (∀ n, (support (priorHitMass (μ n))).Countable) →
      ∃ L : RecursiveCodeLaw base π flags ω,
        L.data.target = p ∧ L.data.priorLaws = μ) : S.Countable := by
  by_contra hunc
  obtain ⟨p, hp, hpS⟩ := exists_injective_firstUncountable S hunc
  obtain ⟨L, htarget, hprior⟩ := exists_recursive_code_laws base π flags ω p
    (fun L => L.full_hit_support_countable hU hG hBU hdisj hπ hclosed hsurj hr)
    (fun i μ hf hμ => hselect (p i) (hpS (mem_range_self i)) μ hf hμ)
  have hc : Countable FirstUncountable := countable_recursive_code_laws
    hcross hcoarea hsard hsch base π hG hU hdisj hBU hB hTD hE hEU
    hπ hclosed hsurj hr hbad hinf flags hflags hH hweights hmarked hcompat hunique ω L
    (fun i => by rw [htarget i]; exact (hS (hpS (mem_range_self i))).2)
    (by intro i j hij; apply hp; simpa only [htarget] using hij) hprior
  exact firstUncountable_not_countable hc

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_UngatedCodes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A contour already contained in its allowed gate imposes no restriction.
This includes the ungated endpoint problems used in the transfinite recursion. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurableSet_endpointCode_of_vacuous_gates (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) [∀ i, SFinite (d.priorLaws i)]
    (hprior : ∀ i, (support (priorHitMass (d.priorLaws i))).Countable)
    (hlevel : ∀ i, (support (d.levelWeights i)).Countable)
    (hE : MeasurableSet d.anchor)
    (hgate : ∀ i, d.gateContours i ⊆ d.gateSets i)
    (dustMeasure : Measure X) [SFinite dustMeasure]
    {N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (hN : ∀ n l, MeasurableSet (N n l)) :
    MeasurableSet {Γ | EndpointCode d dustMeasure N Γ} := by
  have hg (γ : C(PathTime, X)) : GateRules d.gateContours d.gateSets γ :=
    fun i _ ht => hgate i ht
  have heq : {Γ | EndpointCode d dustMeasure N Γ} =
      {Γ | AllowedTaggedPath d dustMeasure N Γ} ∩
      {Γ : TaggedPath X | Γ.1 ⊥ ∈ d.anchor ∧ FirstArrival d.target Γ.1} := by
    ext Γ
    simp only [EndpointCode, mem_ofPred_eq, mem_inter_iff, hg, and_true]
  rw [heq]
  exact (measurableSet_allowedTaggedPath d hU hB hH hprior hlevel dustMeasure hN).inter
    (measurableSet_endpointCodes hE d.target)

theorem standardBorel_basePathCode_of_vacuous_gates [CompleteSpace X]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) [∀ i, SFinite (d.priorLaws i)]
    (hprior : ∀ i, (support (priorHitMass (d.priorLaws i))).Countable)
    (hlevel : ∀ i, (support (d.levelWeights i)).Countable)
    (hE : MeasurableSet d.anchor)
    (hgate : ∀ i, d.gateContours i ⊆ d.gateSets i) :
    StandardBorelSpace (BasePathCode d) :=
  (measurableSet_endpointCode_of_vacuous_gates d hU hB hH hprior hlevel hE hgate 0
    (fun _ _ => MeasurableSet.empty)).standardBorel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableUnavailableEndpoints
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countability of endpoints with no small compatible barrier. The
transfinite positive-law recursion retains all earlier laws and their dust
marks, and alternating disk crossings give the contradiction. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_17 : BorelSpace Sphere := ⟨rfl⟩
theorem countable_unavailable_endpoints
    (hcross : UnitDiskAlternatingContinua)
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
    (P : Set Sphere) (hPB : P ⊆ d.dust)
    {g₀ : ℂ → ℝ≥0∞}
    (D : ∀ p : P, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
    (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
    (hshrink : ∀ p : P, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
      ∀ n ≥ k, closure (D p n).region ⊆ V)
    (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : ℕ → PhysicalRealCoordinate d π)
    (hlevels : ∀ i, d.levels i = Prod.swap ⁻¹'
      circleBandGraph d.quotientDomain (previous i).quotient)
    (hweights : ∀ i, (∑' x, d.levelWeights i x ^ 2) < ∞)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (flags : Set Sphere) (hflags : flags.Countable) (hflagsB : flags ⊆ d.dust)
    (hmarked : ∀ i, support (d.levelWeights i) ⊆ flags)
    (hcompat : OrderedLevelNullCompatibility d.levels (d.dust \ flags))
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
    (hno : ∀ p : P, ∀ R : CompatibleRealBarrier d π previous flags EStar
      (fun j => (D p j).region) (fun _ => ((0 : ℂ) : Sphere)) univ,
      β ≤ R.controlledSize) : P.Countable := by
  obtain ⟨r, hrpos, hrbound⟩ := exists_positive_barrier_duality_parameter C hβ
  have hH (i : ℕ) : IsClosed (d.levels i) := by
    rw [hlevels i]
    apply (isCompact_circleBandGraph (M := 1) (fun x _ => ?_)).isClosed.preimage continuous_swap
    rw [abs_of_nonneg ((previous i).quotient_unit x).1]
    exact ((previous i).quotient_unit x).2
  let : IsFiniteMeasure (tupleReference ω) := finite_tupleReference hωsum
  have hsmall : (P \ {OnePoint.infty}).Countable := by
    apply countable_endpoints_of_recursive_selection hcross hcoarea hsard hsch
      d π hG hU hdisj hBU hB hTD hE hEU hπ hclosed hsurj hr hbad hinfty
      flags hflags hH hweights hmarked hcompat hunique ω (P \ {OnePoint.infty})
      (fun _ hx => ⟨hPB hx.1, hx.2⟩)
    intro p hp μ hfinite hμ
    let p' : P := ⟨p, hp.1⟩
    let R := Classical.choice (nonempty_priorLawPresentation d.dust flags μ hflags hflagsB hμ)
    let G := RecursiveCodeGeometry.of_presentation d π he p (hPB hp.1) R
      (fun j => frontier (D p' j).region) (fun _ => d.quotientDomain)
    let e := G.data
    let prev : ℕ → PhysicalRealCoordinate e π := fun i => (previous i).rebase rfl rfl
    let : ∀ n, IsFiniteMeasure (e.priorLaws n) := hfinite
    let : Countable R.marks := R.marks_countable.to_subtype
    have hgate : ∀ i, e.gateContours i ⊆ e.gateSets i := by
      intro i
      exact (D p' i).frontier_region_subset_quotient d π hπ he
        ((D p' i).isOpen_region hπ hclosed hsurj hr)
    let : StandardBorelSpace (BasePathCode e) := standardBorel_basePathCode_of_vacuous_gates
      e hU hB hH hμ (fun i => hflags.mono (hmarked i)) hE.measurableSet hgate
    have hno' (Q : CompatibleRealBarrier e π prev flags EStar
        (fun j => (D p' j).region) (fun _ => ((0 : ℂ) : Sphere)) univ) :
        β ≤ Q.controlledSize := by
      have hb := hno p' (Q.rebase rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl))
      change β ≤ Q.controlledSize at hb
      exact hb
    obtain ⟨Q, hQ, htest, hcount⟩ := positive_code_law_of_no_small_barrier
      hcoarea hLusin hsard hsch e hU hG hdisj π hπ hclosed hsurj hr he
      hB hTD hBU hdense hinfty hbad hinf EStar hE hEU hEStar hEStarE hinfE
      p (hPB hp.1) (fun h => hinfty (h ▸ hPB hp.1)) (D p') (hnest p') (hshrink p')
      (hED p') (fun _ => ((0 : ℂ) : Sphere)) continuous_const
      univ univ isClosed_univ isOpen_univ (Subset.rfl) hfiber harcs prev hlevels
      (fun i => (hweights i).ne) hpoint flags hflags C hC hderiv rfl rfl
      (by ext i x; simp [e, G, RecursiveCodeGeometry.of_presentation, endpointCodeData])
      (fun x : R.marks => x.val) Subtype.val_injective
      (by rintro _ ⟨x, rfl⟩; exact R.marks_dust x.property)
      (hstandard e) hpath ω hω hωsum β hno' (hdual e) (hlift e)
      r hrpos hrbound hunique (by norm_num : (0 : ℝ) < 1)
    exact ⟨RecursiveCodeLaw.of_positive_candidate G ω r hrpos 1 Q hQ htest hcount, rfl, rfl⟩
  apply ((hsmall.insert OnePoint.infty)).mono
  intro p hp
  by_cases hi : p = OnePoint.infty
  · exact Or.inl hi
  · exact Or.inr ⟨hp, hi⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableUncoveredSeededEnds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The greedy selection of tests misses only countably many ends at each
accuracy, by the positive-law recursion and alternating disk crossings. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r01fbe5_18 : BorelSpace Sphere := ⟨rfl⟩
theorem countable_uncovered_test_endpoints_of_range_oai
    (hcross : UnitDiskAlternatingContinua)
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
    (P : Set Sphere) (hPB : P ⊆ d.dust)
    {g₀ : ℂ → ℝ≥0∞}
    (D : ∀ p : P, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
    (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
    (hshrink : ∀ p : P, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
      ∀ n ≥ k, closure (D p n).region ⊆ V)
    (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (A : Set (GradedRealTest d π EStar)) (k : ℕ)
    (hmiss : ∀ p ∈ P, p ∈ uncoveredTestEnds A k)
    (c : ℕ → UngatedRealTest d π EStar) (M : Set Sphere)
    (hcover : ∀ b : GradedRealTest d π EStar, b.toUngatedRealTest.CompatibleWith (range c) →
      ∀ x ∈ b.toUngatedRealTest.openEnds,
        ∃ a ∈ A, a.grade = b.grade ∧ x ∈ a.toUngatedRealTest.openEnds)
    (hMc : M.Countable) (hMB : M ⊆ d.dust)
    (hM : ∀ i, (c i).exclusions ∩ d.dust ⊆ M)
    (hcompat : OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M))
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
    : P.Countable := by
  let e := realTestLevelData d c
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  apply countable_unavailable_endpoints hcross hcoarea hLusin hsard hsch
    e hU hG hdisj π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad hinf
    EStar hE hEU hEStar hEStarE hinfE P hPB D hnest hshrink hED hfiber harcs
    (realTestLevelData.previous c) (fun _ => rfl)
    (realTestLevelData.weight_finite c) (realTestLevelData.point_bound c hU hdense hBU)
    M hMc hMB (realTestLevelData.marked_weights c M hM) hcompat
    (realTestLevelData.unique_free_trace c hdense M hM) C hC hderiv
    hstandard hpath ω hω hωsum hdual hlift (ENNReal.ofReal (1 / ((k : ℝ) + 1)))
    (ENNReal.ofReal_pos.mpr hk)
  intro p R
  by_contra h
  have hsmall : R.controlledSize < ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
    lt_of_not_ge h
  obtain ⟨b, hb, hbk, hbreg⟩ := GradedRealTest.exists_compatible_of_small_barrier
    c M hM (range c) (fun _ h => h) (fun n => (D p n).isOpen_region hπ hclosed hsurj hr) R k hsmall
  have hpreg : p.val ∈ (D p R.level).region :=
    (D p R.level).point_mem_region hsurj (fun hp => hinfty (hp ▸ hPB p.property))
  have hpopen : (⟨p.val, hPB p.property⟩ : d.dust) ∈ b.toUngatedRealTest.openEnds := by
    change p.val ∈ b.region
    rwa [hbreg]
  obtain ⟨a, ha, hak, hpa⟩ := hcover b hb _ hpopen
  exact (hmiss p.val p.property).2 a ha (hak.trans hbk) hpa

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.countable_uncovered_test_endpoints_of_range_oai := @OAI.CircleDomainRigidity.countable_uncovered_test_endpoints_of_range_oai
