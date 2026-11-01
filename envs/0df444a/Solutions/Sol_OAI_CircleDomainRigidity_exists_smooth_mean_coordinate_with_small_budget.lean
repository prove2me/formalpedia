-- Prove2me | solution 1 for OAI.CircleDomainRigidity.exists_smooth_mean_coordinate_with_small_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:52:23.908918+00:00
-- url     : https://prove2.me/submissions/fb39cacd-9762-409b-a4e1-51024541be76

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010

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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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

instance instIsFiniteMeasureBaseCodeOccupation (d : PathCodeData X Y) (Γ : BasePathCode d) : IsFiniteMeasure (baseCodeOccupation d Γ) := by
  unfold baseCodeOccupation
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BandBudgetNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real square norms of band widths are bounded by their ENNReal budgets,
including when the marked set is only a subset of the full budget support. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem real_square_norm_le_counting {A B : Type*}
    (v : A → ℝ) (w : B → ℝ≥0∞) (e : A → B) (he : Injective e)
    (hv : ∀ a, 0 ≤ v a) (hb : ∀ a, ENNReal.ofReal (v a) ≤ w (e a))
    (hw : (∑' b, w b ^ 2) < ∞) :
    Real.sqrt (∑' a, v a ^ 2) ≤ (countingSquareNorm w).toReal := by
  have hE : (∑' a, ENNReal.ofReal (v a ^ 2)) ≤ ∑' b, w b ^ 2 := by
    calc
      _ = ∑' a, ENNReal.ofReal (v a) ^ 2 := by
        congr 1
        funext a
        exact ENNReal.ofReal_pow (hv a) 2
      _ ≤ ∑' a, w (e a) ^ 2 := ENNReal.tsum_le_tsum
        (fun a => pow_le_pow_left' (hb a) 2)
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective he (fun b => w b ^ 2)
  have hr := ENNReal.toReal_mono hw.ne hE
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)] at hr
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at hr
  rw [countingSquareNorm, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt hr

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleLifts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real lifts of circle coordinates near filling disks

The quotient `ℝ → ℝ/ℤ` is a covering map in Mathlib. Its lifting theorem
therefore gives actual continuous real branches on simply connected open
sets. Smoothness is expressed in the ordinary real quotient charts
`AddCircle.equivIco`; a continuous lift is locally one of these charts plus
an integer, so the lift is smooth. No external lifting axiom is used.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_continuous_circle_lift
    {X : Type*} [TopologicalSpace X] {U : Set X}
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    (f : X → UnitAddCircle) (hf : ContinuousOn f U)
    {x₀ : X} (hx₀ : x₀ ∈ U) (r₀ : ℝ) (hr₀ : (r₀ : UnitAddCircle) = f x₀) :
    ∃ u : X → ℝ, ContinuousOn u U ∧ u x₀ = r₀ ∧
      ∀ x ∈ U, (u x : UnitAddCircle) = f x := by
  classical
  let f' : C(U, UnitAddCircle) := ⟨fun x => f x, hf.domRestrict⟩
  obtain ⟨g, ⟨hg₀, hg⟩, _⟩ :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
      f' ⟨x₀, hx₀⟩ r₀ hr₀
  let u : X → ℝ := fun x => if hx : x ∈ U then g ⟨x, hx⟩ else 0
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert g.continuous using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    change u x = g x
    simp only [u, dite_eq_left x.property]
  · simpa only [u, dite_eq_left hx₀] using hg₀
  · intro x hx
    have h := congrFun hg (⟨x, hx⟩ : U)
    change (g ⟨x, hx⟩ : UnitAddCircle) = f x at h
    simpa only [u, dite_eq_left hx] using h

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleCovectors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth covector fields of periodic coordinates

The locally defined circle differential is an ordinary smooth covector
field on its open domain. This supplies the tensor used in the same
metric construction as for single-valued real coordinates.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem contDiffOn_circleFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hU : IsOpen U) (hf : SmoothCircleOn f U) :
    ContDiffOn ℝ ∞ (circleFDeriv f) U := by
  intro x hx
  let a := circleCut f x
  let V := U ∩ f ⁻¹' ({(a : UnitAddCircle)} : Set UnitAddCircle)ᶜ
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hxV : x ∈ V := ⟨hx, circleCut_ne f x⟩
  have hu : ContDiffOn ℝ ∞ (circleBranch f a) V := by
    intro y hy
    exact (hf y hy.1 a hy.2).contDiffWithinAt
  have heq := circleFDeriv_eventuallyEq_lift hV (hf.continuousOn.mono inter_subset_left)
    hu (fun y _ => coe_circleBranch f a y) hxV
  exact (((hu.fderiv_of_isOpen (m := ∞) hV (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hV.mem_nhds hxV)).congr_of_eventuallyEq
    heq).contDiffWithinAt

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localized energy for periodic differentials

Agreement of circle maps near the retained core implies agreement of
their intrinsic differentials. Original L² energy controls the entire
unbounded core; smoothness on a compact tail controls the remainder.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem fieldEnergy_spherical (v : (ℝ × ℝ) → ℝ × ℝ) (z : ℝ × ℝ) :
    fieldEnergy v (fun z => sphericalMetricFactor z • 1) z = (v z).1 ^ 2 + (v z).2 ^ 2 := by
  unfold fieldEnergy
  rw [covectorEnergy_eq_matrixEnergy,
    matrixEnergy_pos_smul _ Matrix.PosDef.one (sphericalMetricFactor_pos z),
    ← covectorEnergy_eq_matrixEnergy, covectorEnergy_identity]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleGradientSize
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full spherical energy of a circle coordinate is controlled by
its two real partial derivatives, with no choice of global real lift. -/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem circle_gradient_energy_eq_norms
    {μ : Measure (ℝ × ℝ)} {f : (ℝ × ℝ) → UnitAddCircle}
    (hf : MemLp (circleGradient f) 2 μ) :
    (∫ x, fieldEnergy (circleGradient f) (fun z => sphericalMetricFactor z • 1) x ∂μ) =
      (eLpNorm (fun x => circleFDeriv f x (1, 0)) 2 μ).toReal ^ 2 +
        (eLpNorm (fun x => circleFDeriv f x (0, 1)) 2 μ).toReal ^ 2 := by
  calc
    _ = ∫ x, (circleGradient f x).1 ^ 2 + (circleGradient f x).2 ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fieldEnergy_spherical (circleGradient f))
    _ = (∫ x, (circleGradient f x).1 ^ 2 ∂μ) +
        (∫ x, (circleGradient f x).2 ^ 2 ∂μ) :=
      integral_add hf.fst.integrable_sq hf.snd.integrable_sq
    _ = _ := by
      rw [integral_sq_eq_eLpNorm_toReal_sq hf.fst, integral_sq_eq_eLpNorm_toReal_sq hf.snd]
      rfl

 theorem circle_gradient_norm_le_partial_norms
    {μ : Measure (ℝ × ℝ)} {f : (ℝ × ℝ) → UnitAddCircle}
    (hf : MemLp (circleGradient f) 2 μ) :
    Real.sqrt (∫ x, fieldEnergy (circleGradient f)
      (fun z => sphericalMetricFactor z • 1) x ∂μ) ≤
      (eLpNorm (fun x => circleFDeriv f x (1, 0)) 2 μ).toReal +
        (eLpNorm (fun x => circleFDeriv f x (0, 1)) 2 μ).toReal := by
  rw [circle_gradient_energy_eq_norms hf, Real.sqrt_le_iff]
  constructor
  · positivity
  · have hx := ENNReal.toReal_nonneg
      (a := eLpNorm (fun x => circleFDeriv f x (1, 0)) 2 μ)
    have hy := ENNReal.toReal_nonneg
      (a := eLpNorm (fun x => circleFDeriv f x (0, 1)) 2 μ)
    nlinarith [mul_nonneg hx hy]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceBandLevel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a point with a genuine limiting real trace, the entire circle
band is the single projected trace value. -/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

theorem circleBandGraph_of_trace
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [CompactSpace X] [T2Space X] {G : Set X} {u : X → ℝ} {M : ℝ}
    (hM : ∀x ∈ G, |u x| ≤ M) {x : X} (hx : x ∈ closure G) {v : ℝ}
    (htrace : Tendsto u (𝓝[G] x) (𝓝 v)) {t : AddCircle (1 : ℝ)} :
    (x, t) ∈ circleBandGraph G u ↔ (v : AddCircle (1 : ℝ)) = t := by
  let : NeBot (𝓝[G] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hband : ∀r : ℝ, (x, r) ∈ intervalFiberHull (clusterGraph G u) ↔ r = v := by
    intro r
    have he := intervalFiberHull_clusterGraph_eq_boundary_band hM hx
    have hr := Set.ext_iff.mp he r
    simpa only [mem_ofPred_eq, htrace.liminf_eq, htrace.limsup_eq, Icc_self,
      mem_singleton_iff] using hr
  constructor
  · rintro ⟨⟨y, r⟩, hr, heq⟩
    obtain ⟨rfl, ht⟩ := Prod.mk.inj heq
    rwa [(hband r).mp hr] at ht
  · intro ht
    exact ⟨(x, v), (hband v).mpr rfl, Prod.ext rfl ht⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalBandTransitions
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer changes of local sheet preserve the actual interval-band
level graph. Eventual equality is enough: values outside the patch do
not enter its boundary band. -/

open Set Function Filter
open scoped Topology

namespace CircleDomainRigidity

theorem clusterGraph_add_const_of_eventuallyEq
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {D : Set X} {f g : X → ℝ} {x : X} {c : ℝ}
    (heq : g =ᶠ[𝓝[D] x] fun y => f y + c) (t : ℝ) :
    (x, t + c) ∈ clusterGraph D g ↔ (x, t) ∈ clusterGraph D f := by
  simp only [mem_clusterGraph_iff_mapClusterPt]
  constructor
  · intro ht
    have h := (ht.congrFun heq).continuousAt_comp
      (continuousAt_id.sub_const c)
    simpa only [Function.comp_def, id_eq, add_sub_cancel_right] using h
  · intro ht
    have h := ht.continuousAt_comp (continuousAt_id.add_const c)
    exact h.congrFun heq.symm

theorem intervalBand_add_const_of_eventuallyEq
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {D : Set X} {f g : X → ℝ} {x : X} {c : ℝ}
    (heq : g =ᶠ[𝓝[D] x] fun y => f y + c) (t : ℝ) :
    (x, t + c) ∈ intervalFiberHull (clusterGraph D g) ↔
      (x, t) ∈ intervalFiberHull (clusterGraph D f) := by
  constructor
  · intro ht
    obtain ⟨a, b, s, ha, hb, hs, ht⟩ := mem_intervalFiberHull_iff.mp ht
    have ha' : (x, (a - c) + c) ∈ clusterGraph D g := by simpa using ha
    have hb' : (x, (b - c) + c) ∈ clusterGraph D g := by simpa using hb
    exact mem_intervalFiberHull_iff.mpr ⟨a - c, b - c, s,
      (clusterGraph_add_const_of_eventuallyEq heq _).mp ha',
      (clusterGraph_add_const_of_eventuallyEq heq _).mp hb', hs, by nlinarith [ht]⟩
  · intro ht
    obtain ⟨a, b, s, ha, hb, hs, ht⟩ := mem_intervalFiberHull_iff.mp ht
    exact mem_intervalFiberHull_iff.mpr ⟨a + c, b + c, s,
      (clusterGraph_add_const_of_eventuallyEq heq _).mpr ha,
      (clusterGraph_add_const_of_eventuallyEq heq _).mpr hb, hs, by nlinarith [ht]⟩

theorem circleBand_fiber_eq_of_eventually_add_int
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {D : Set X} {f g : X → ℝ} {x : X} {k : ℤ}
    (heq : g =ᶠ[𝓝[D] x] fun y => f y + (k : ℝ)) :
    {θ : UnitAddCircle | (x, θ) ∈ circleBandGraph D g} =
      {θ | (x, θ) ∈ circleBandGraph D f} := by
  have hadd (a : ℝ) : ((a + (k : ℝ) : ℝ) : UnitAddCircle) = (a : UnitAddCircle) :=
    unitAddCircle_eq_iff_exists_int.mpr ⟨k, rfl⟩
  ext θ
  constructor
  · rintro ⟨⟨y, a⟩, ha, he⟩
    have hy : y = x := congrArg Prod.fst he
    subst y
    have ha' : (x, (a - (k : ℝ)) + (k : ℝ)) ∈ intervalFiberHull (clusterGraph D g) := by
      simpa using ha
    refine ⟨(x, a - (k : ℝ)), (intervalBand_add_const_of_eventuallyEq heq _).mp ha', ?_⟩
    change (x, ((a - (k : ℝ) : ℝ) : UnitAddCircle)) = (x, θ)
    have hc := hadd (a - (k : ℝ))
    have hs : ((a - (k : ℝ) : ℝ) : UnitAddCircle) = θ := by
      have hc' : (a : UnitAddCircle) = ((a - (k : ℝ) : ℝ) : UnitAddCircle) := by
        simpa only [sub_add_cancel] using hc
      exact hc'.symm.trans (congrArg Prod.snd he)
    exact congrArg (fun θ => (x, θ)) hs
  · rintro ⟨⟨y, a⟩, ha, he⟩
    have hy : y = x := congrArg Prod.fst he
    subst y
    refine ⟨(x, a + (k : ℝ)), (intervalBand_add_const_of_eventuallyEq heq _).mpr ha, ?_⟩
    change (x, ((a + (k : ℝ) : ℝ) : UnitAddCircle)) = (x, θ)
    exact Prod.ext rfl ((hadd a).trans (congrArg Prod.snd he))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PeriodBandGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The period-coordinate level graph of Definition 2.3, assembled from
local real branches on the punctured mask. The singular point belongs to
every level. Integer changes of sheet give the compatibility used below;
the closedness proof only needs the resulting equality of projected bands. -/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem periodBandGraph_on_patch {ι : Type*}
    (D M : Set Sphere) (b : Sphere) (V : ι → Set Sphere) (f : ι → Sphere → ℝ)
    (hmiss : ∀ i, b ∉ V i)
    (hcompat : ∀ i j x, x ∈ V i → x ∈ V j → ∀ θ,
      (x, θ) ∈ circleBandGraph D (f i) ↔ (x, θ) ∈ circleBandGraph D (f j))
    {i : ι} {x : Sphere} (hx : x ∈ V i) (θ : UnitAddCircle) :
    (x, θ) ∈ periodBandGraph D M b V f ↔ x ∈ M ∧ (x, θ) ∈ circleBandGraph D (f i) := by
  constructor
  · rintro ⟨hxM, rfl | ⟨j, hxj, hj⟩⟩
    · exact (hmiss i hx).elim
    · exact ⟨hxM, (hcompat j i x hxj hx θ).mp hj⟩
  · rintro ⟨hxM, hi⟩
    exact ⟨hxM, Or.inr ⟨i, hx, hi⟩⟩

theorem isClosed_periodBandGraph {ι : Type*}
    (D M : Set Sphere) (hM : IsClosed M) (b : Sphere)
    (V : ι → Set Sphere) (hV : ∀ i, IsOpen (V i)) (hmiss : ∀ i, b ∉ V i)
    (hcover : M \ {b} ⊆ ⋃ i, V i)
    (f : ι → Sphere → ℝ) (bound : ι → ℝ)
    (hbound : ∀ i x, x ∈ D → |f i x| ≤ bound i)
    (hcompat : ∀ i j x, x ∈ V i → x ∈ V j → ∀ θ,
      (x, θ) ∈ circleBandGraph D (f i) ↔ (x, θ) ∈ circleBandGraph D (f j)) :
    IsClosed (periodBandGraph D M b V f) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  by_cases hxM : p.1 ∈ M
  · have hxb : p.1 ≠ b := fun heq => hp ⟨hxM, Or.inl heq⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hxM, hxb⟩)
    have hc : IsClosed (Prod.fst ⁻¹' M ∩ circleBandGraph D (f i)) :=
      (hM.preimage continuous_fst).inter (isCompact_circleBandGraph (hbound i)).isClosed
    have hp' : p ∈ (Prod.fst ⁻¹' M ∩ circleBandGraph D (f i))ᶜ := by
      intro h
      exact hp ((periodBandGraph_on_patch D M b V f hmiss hcompat hi p.2).mpr h)
    apply mem_of_superset (((hV i).preimage continuous_fst).inter hc.isOpen_compl |>.mem_nhds ⟨hi, hp'⟩)
    intro q hq hqgraph
    exact hq.2 ((periodBandGraph_on_patch D M b V f hmiss hcompat hq.1 q.2).mp hqgraph)
  · apply mem_of_superset ((hM.isOpen_compl.preimage continuous_fst).mem_nhds hxM)
    intro q hq hqgraph
    exact hq hqgraph.1

theorem periodBandGraph_fiber_on_patch {ι : Type*}
    (D M : Set Sphere) (b : Sphere) (V : ι → Set Sphere) (f : ι → Sphere → ℝ)
    (hmiss : ∀ i, b ∉ V i)
    (hcompat : ∀ i j x, x ∈ V i → x ∈ V j → ∀ θ,
      (x, θ) ∈ circleBandGraph D (f i) ↔ (x, θ) ∈ circleBandGraph D (f j))
    {i : ι} {x : Sphere} (hxM : x ∈ M) (hx : x ∈ V i) :
    {θ | (x, θ) ∈ periodBandGraph D M b V f} =
      {θ | (x, θ) ∈ circleBandGraph D (f i)} := by
  ext θ
  change (x, θ) ∈ periodBandGraph D M b V f ↔ (x, θ) ∈ circleBandGraph D (f i)
  rw [periodBandGraph_on_patch D M b V f hmiss hcompat hx]
  exact and_iff_right hxM

theorem isClosed_periodBandGraph_of_integer_transitions {ι : Type*}
    [FirstCountableTopology Sphere]
    (D M : Set Sphere) (hM : IsClosed M) (b : Sphere)
    (V : ι → Set Sphere) (hV : ∀ i, IsOpen (V i)) (hmiss : ∀ i, b ∉ V i)
    (hcover : M \ {b} ⊆ ⋃ i, V i)
    (f : ι → Sphere → ℝ) (bound : ι → ℝ)
    (hbound : ∀ i x, x ∈ D → |f i x| ≤ bound i)
    (htrans : ∀ i j x, x ∈ V i → x ∈ V j →
      ∃ k : ℤ, f j =ᶠ[𝓝[D] x] fun y => f i y + (k : ℝ)) :
    IsClosed (periodBandGraph D M b V f) := by
  apply isClosed_periodBandGraph D M hM b V hV hmiss hcover f bound hbound
  intro i j x hxi hxj θ
  obtain ⟨k, hk⟩ := htrans i j x hxi hxj
  exact (Set.ext_iff.mp (circleBand_fiber_eq_of_eventually_add_int hk) θ).symm

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleIncrementContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous families of circle paths have continuous real increments.
This follows from the actual homotopy lift, so no choice of a discontinuous
starting-angle representative enters the continuity or compact bounds. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem compact_circle_increment_bounded
    (K : Set C(unitInterval, UnitAddCircle)) (hK : IsCompact K) :
    ∃ M : ℝ, ∀ γ ∈ K, |circlePathIncrement γ| ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image continuous_circlePathIncrement).isBounded.exists_norm_le
  exact ⟨M, fun γ hγ => by simpa only [Real.norm_eq_abs] using hM _ (mem_image_of_mem _ hγ)⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CirclePathPrefixes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds for all initial lifts in a compact family of circle paths. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem continuous_circlePathPrefix :
    Continuous (fun p : C(unitInterval, UnitAddCircle) × unitInterval =>
      circlePathPrefix p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
    (continuous_snd.mul (continuous_snd.comp continuous_fst)))

theorem circlePathIncrement_prefix (γ : C(unitInterval, UnitAddCircle)) (t : unitInterval) :
    circlePathIncrement (circlePathPrefix γ t) =
      realCirclePathLift γ t - realCirclePathLift γ 0 := by
  let u := (realCirclePathLift γ).comp
    (⟨fun s : unitInterval => s * t, continuous_id.mul continuous_const⟩ :
      C(unitInterval, unitInterval))
  rw [circlePathIncrement_eq_lift (circlePathPrefix γ t) u
    (fun s => realCirclePathLift_projects γ (s * t))]
  simp only [u, ContinuousMap.comp_apply, ContinuousMap.coe_mk, one_mul, zero_mul]

theorem compact_circle_path_lifts_bounded
    (K : Set C(unitInterval, UnitAddCircle)) (hK : IsCompact K) :
    ∃ M : ℝ, ∀ γ ∈ K, ∀ t : unitInterval, |realCirclePathLift γ t| ≤ M := by
  obtain ⟨M, hM⟩ := compact_circle_increment_bounded _
    ((hK.prod isCompact_univ).image continuous_circlePathPrefix)
  refine ⟨M + 1, fun γ hγ t => ?_⟩
  have hb : |realCirclePathLift γ t - realCirclePathLift γ 0| ≤ M := by
    rw [← circlePathIncrement_prefix]
    exact hM _ ⟨(γ, t), ⟨hγ, mem_univ _⟩, rfl⟩
  have hstart : realCirclePathLift γ 0 = circleRepresentative (γ 0) := by
    exact (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_zero _ _ _
  have hr := (AddCircle.equivIco (1 : ℝ) 0 (γ 0)).property
  have hs : |realCirclePathLift γ 0| ≤ 1 := by
    rw [hstart]
    change |((AddCircle.equivIco (1 : ℝ) 0 (γ 0)).val)| ≤ 1
    rw [abs_of_nonneg hr.1]
    simpa only [zero_add] using hr.2.le
  calc
    |realCirclePathLift γ t| =
        |(realCirclePathLift γ t - realCirclePathLift γ 0) + realCirclePathLift γ 0| := by
          congr 1; ring
    _ ≤ |realCirclePathLift γ t - realCirclePathLift γ 0| + |realCirclePathLift γ 0| := abs_add_le _ _
    _ ≤ M + 1 := add_le_add hb hs

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasurableArcIndex
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Borel version of the explicit index, including a value on the
coincidence set. Its deck identity holds everywhere, before averaging. -/

open Set Function Filter MeasureTheory
open scoped Topology Classical

/-! d13f23b's Borel structure on `C(X, Y)` (missing in our Mathlib), with `measurable_iff_eval`
proved here for a compact metric domain. -/

theorem _root_.ContinuousMap.measurable_iff_eval {X Y Z : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace Z] {g : Z → C(X, Y)} :
    Measurable g ↔ ∀ x, Measurable fun z => g z x := by
  refine ⟨fun h x => (continuous_eval_const x).measurable.comp h, fun h => ?_⟩
  obtain ⟨D, hDc, hDd⟩ := _root_.TopologicalSpace.exists_countable_dense X
  have hcl : ∀ (f : C(X, Y)) (s : ℝ), MeasurableSet {z | dist (g z) f ≤ s} := by
    intro f s
    rcases lt_or_ge s 0 with hs | hs
    · have : {z | dist (g z) f ≤ s} = ∅ :=
        Set.eq_empty_of_forall_notMem fun z hz => absurd (lt_of_le_of_lt dist_nonneg (lt_of_le_of_lt hz hs)) (lt_irrefl _)
      rw [this]; exact MeasurableSet.empty
    have heq : {z | dist (g z) f ≤ s} = ⋂ x ∈ D, {z | dist (g z x) (f x) ≤ s} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [ContinuousMap.dist_le hs]
      refine ⟨fun H x _ => H x, fun H x => ?_⟩
      have hc : IsClosed {x | dist (g z x) (f x) ≤ s} :=
        isClosed_le ((g z).continuous.dist f.continuous) continuous_const
      have : closure D ⊆ {x | dist (g z x) (f x) ≤ s} :=
        hc.closure_subset_iff.mpr (fun x hx => H x hx)
      exact this (hDd.closure_eq ▸ Set.mem_univ x)
    rw [heq]
    exact MeasurableSet.biInter hDc fun x _ =>
      measurableSet_le ((h x).dist measurable_const) measurable_const
  have hball : ∀ (f : C(X, Y)) (r : ℝ), MeasurableSet (g ⁻¹' Metric.ball f r) := by
    intro f r
    have : g ⁻¹' Metric.ball f r = ⋃ n : ℕ, {z | dist (g z) f ≤ r - 1 / (n + 1)} := by
      ext z
      simp only [Set.mem_preimage, Metric.mem_ball, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hz)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : (0 : ℝ) < 1 / (n + 1) := by positivity
        linarith
    rw [this]
    exact MeasurableSet.iUnion fun n => hcl f _
  refine measurable_of_isOpen fun U hU => ?_
  have hε : ∀ f : U, ∃ ε > 0, Metric.ball (f : C(X, Y)) ε ⊆ U := fun f =>
    Metric.isOpen_iff.mp hU f f.2
  choose ε hεpos hεU using hε
  obtain ⟨T, hTc, hT⟩ := _root_.TopologicalSpace.isOpen_iUnion_countable
    (fun f : U => Metric.ball (f : C(X, Y)) (ε f)) (fun _ => Metric.isOpen_ball)
  have hU' : U = ⋃ f ∈ T, Metric.ball (f : C(X, Y)) (ε f) := by
    rw [hT]
    ext h
    simp only [Set.mem_iUnion]
    refine ⟨fun hh => ⟨⟨h, hh⟩, Metric.mem_ball_self (hεpos _)⟩, fun ⟨f, hf⟩ => hεU f hf⟩
  rw [hU', Set.preimage_iUnion₂]
  exact MeasurableSet.biUnion hTc fun f _ => hball _ _


noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem measurable_circleRepresentative_dup1 : Measurable circleRepresentative := by
  exact measurable_unitCircleCut

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DiskStartLaw
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Atomlessness and the boundary measure for the actual disk arc law. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem normalizedArgument_injOn_unit_sphere :
    InjOn normalizedArgument {z : ℂ | ‖z‖ = 1} := by
  intro z hz w hw h
  apply Complex.ext_norm_arg (hz.trans hw.symm)
  apply Complex.arg_coe_angle_eq_iff.mp
  exact (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_CayleyBoundaryOrder
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real boundary of the half-plane is sent monotonically to the
positively oriented circle cut at the point at infinity. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem cayleyBoundary_ne_one (x : ℝ) : halfPlaneDisk x ≠ 1 :=
  halfPlaneDisk_ne_one (by simp)

theorem continuous_cayleyBoundaryAngle : Continuous cayleyBoundaryAngle := by
  have hM : Continuous (fun x : ℝ => halfPlaneDisk x) :=
    continuousOn_halfPlaneDisk.comp_continuous Complex.continuous_ofReal (by intro x; simp)
  apply continuous_iff_continuousAt.mpr
  intro x
  have hn : halfPlaneDisk (x : ℂ) ≠ 0 := by
    intro he
    have hh := cayleyBoundary_norm x
    rw [he, norm_zero] at hh
    exact zero_ne_one hh
  have hzero : normalizedArgument (halfPlaneDisk x) ≠ (0 : ℝ) := by
    intro he
    apply cayleyBoundary_ne_one x
    rw [← standardCirclePoint_normalizedArgument (cayleyBoundary_norm x), he,
      AddCircle.coe_zero, standardCirclePoint_zero]
  exact continuous_subtype_val.continuousAt.comp
    ((AddCircle.continuousAt_equivIco (1 : ℝ) 0 hzero).comp
      (f := fun y : ℝ => normalizedArgument (halfPlaneDisk y))
      ((continuousAt_normalizedArgument hn).comp (f := fun y : ℝ => halfPlaneDisk y) hM.continuousAt))

theorem cayleyBoundaryAngle_injective : Injective cayleyBoundaryAngle := by
  intro x y he
  have ha := normalizedArgument_injOn_unit_sphere (cayleyBoundary_norm x)
    (cayleyBoundary_norm y) (unitCircleCut_injective he)
  exact Complex.ofReal_injective (halfPlaneDisk_injOn (by simp) (by simp) ha)

theorem cayleyBoundaryAngle_zero : cayleyBoundaryAngle 0 = 1 / 2 := by
  have hM : halfPlaneDisk 0 = -1 := by simp [halfPlaneDisk]
  have hπ : Real.pi / (2 * Real.pi) = 1 / 2 := by field_simp
  unfold cayleyBoundaryAngle
  rw [Complex.ofReal_zero, hM, normalizedArgument_eq, Complex.arg_neg_one, hπ]
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
    (show (1 / 2 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) by constructor <;> norm_num))

theorem cayleyBoundaryAngle_one : cayleyBoundaryAngle 1 = 3 / 4 := by
  have hM : halfPlaneDisk 1 = -Complex.I := by
    unfold halfPlaneDisk
    apply (div_eq_iff (halfPlaneDisk_den_ne_zero (z := 1) (by simp))).mpr
    rw [mul_add]
    simp only [neg_mul, mul_one, Complex.I_mul_I, neg_neg]
    ring
  have hπ : -(Real.pi / 2) / (2 * Real.pi) = -(1 / 4) := by field_simp <;> ring
  have hc : ((-(1 / 4) : ℝ) : UnitAddCircle) = ((3 / 4 : ℝ) : UnitAddCircle) :=
    (addCircle_eq_iff_exists_int 1 _ _).mpr ⟨-1, by norm_num⟩
  unfold cayleyBoundaryAngle
  rw [Complex.ofReal_one, hM, normalizedArgument_eq, Complex.arg_neg_I, hπ, hc]
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
    (show (3 / 4 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) by constructor <;> norm_num))

theorem strictMono_cayleyBoundaryAngle : StrictMono cayleyBoundaryAngle := by
  rcases continuous_cayleyBoundaryAngle.strictMono_of_inj cayleyBoundaryAngle_injective with h | h
  · exact h
  · have hh := h (show (0 : ℝ) < 1 by norm_num)
    rw [cayleyBoundaryAngle_zero, cayleyBoundaryAngle_one] at hh
    norm_num at hh

theorem cayleyBoundary_mem_closingArc (a x : ℝ) :
    halfPlaneDisk x ∈ range (boundaryClosingArc (halfPlaneDisk a) (cayleyBoundary_norm a)) ↔ x ≤ a := by
  let A := cayleyBoundaryAngle a
  have hA : 0 < A := boundary_angle_pos (cayleyBoundary_norm a) (cayleyBoundary_ne_one a)
  constructor
  · rintro ⟨t, ht⟩
    have hc := congrArg normalizedArgument ht
    change normalizedArgument (standardCirclePoint ((A * (t : ℝ) : ℝ) : UnitAddCircle)) =
      normalizedArgument (halfPlaneDisk x) at hc
    rw [normalizedArgument_standardCirclePoint] at hc
    have hb := boundary_arc_parameter_mem (cayleyBoundary_norm a) (cayleyBoundary_ne_one a) t
    change A * (t : ℝ) ∈ Ico (0 : ℝ) 1 at hb
    have hqx : cayleyBoundaryAngle x = A * (t : ℝ) := by
      unfold cayleyBoundaryAngle unitCircleCut
      rw [← hc]
      exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
        (show A * (t : ℝ) ∈ Ico (0 : ℝ) (0 + 1) by simpa only [zero_add] using hb))
    apply strictMono_cayleyBoundaryAngle.le_iff_le.mp
    rw [hqx]
    exact mul_le_of_le_one_right hA.le t.property.2
  · intro hxa
    have hqx : cayleyBoundaryAngle x ≤ A := strictMono_cayleyBoundaryAngle.monotone hxa
    let t : PathTime := ⟨cayleyBoundaryAngle x / A,
      div_nonneg (unitCircleCut_mem _).1 hA.le, (div_le_one hA).mpr hqx⟩
    refine ⟨t, ?_⟩
    change standardCirclePoint ((A * (cayleyBoundaryAngle x / A) : ℝ) : UnitAddCircle) = _
    rw [mul_div_cancel₀ _ hA.ne']
    change standardCirclePoint ((unitCircleCut (normalizedArgument (halfPlaneDisk x)) : ℝ) : UnitAddCircle) = _
    rw [show ((unitCircleCut (normalizedArgument (halfPlaneDisk x)) : ℝ) : UnitAddCircle) =
      normalizedArgument (halfPlaneDisk x) from AddCircle.coe_equivIco]
    exact standardCirclePoint_normalizedArgument (cayleyBoundary_norm x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactArcWinding
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform winding bounds for initial portions of a compact simple-arc
family, in any continuous angular coordinate on the punctured plane. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer

theorem compact_initial_arc_lifts_bounded
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (b : ℂ)
    (hinj : ∀ γ ∈ K, Injective γ) (hend : ∀ γ ∈ K, γ ⊤ = b)
    (q : C({x : ℂ // x ≠ b}, UnitAddCircle)) (c : PathTime) (hc : c < ⊤) :
    ∃ M : ℝ, ∀ γ : K, ∀ t : unitInterval,
      |realCirclePathLift (initialArcAngles q γ.val (hinj _ γ.property)
        (hend _ γ.property) c hc) t| ≤ M := by
  let F : K → C(unitInterval, UnitAddCircle) := fun γ =>
    initialArcAngles q γ.val (hinj _ γ.property) (hend _ γ.property) c hc
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply q.continuous.comp
    apply Continuous.subtype_mk
    exact continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_snd.mul continuous_const))
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M, hM⟩ := compact_circle_path_lifts_bounded (range F) (isCompact_range hF)
  exact ⟨M, fun γ t => hM (F γ) (mem_range_self γ) t⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactDiskRayBounds
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded-depth part of a compact family of disk rays lies in a
common initial time interval, on which the angular lifts are uniformly bounded. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem compact_disk_rays_initial_angle_bound
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) {r : ℝ} (hr : 0 < r) :
    ∃ (c : PathTime) (hc : c < ⊤) (M : ℝ),
      0 < c ∧
      (∀ γ ∈ K, ∀ t, r ≤ ‖γ t‖ → t < c) ∧
      ∀ γ : K, ∀ t : unitInterval,
        |realCirclePathLift (initialArcAngles puncturedArgument γ.val
          (hKS γ.property).1 (hKS γ.property).2.2.1 c hc) t| ≤ M := by
  obtain ⟨c, hc0, hc1, htail⟩ := compact_disk_rays_uniform_tail K hK
    (fun γ hγ => (hKS hγ).2.2.1) hr
  have hc : c < ⊤ := hc1
  obtain ⟨M, hM⟩ := compact_initial_arc_lifts_bounded K hK 0
    (fun γ hγ => (hKS hγ).1) (fun γ hγ => (hKS hγ).2.2.1)
    puncturedArgument c hc
  refine ⟨c, hc, M, hc0, ?_, hM⟩
  intro γ hγ t ht
  by_contra! hct
  exact (not_lt_of_ge ht) (htail γ hγ t hct)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayLift
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous lift of each actual terminal arc to angular and logarithmic
coordinates. The angular origin is the representative of the arc start. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem diskRayAngle_mul_prefix (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (c : DiskRayTime) (u : unitInterval) :
    diskRayAngle γ hi he ⟨u * c.val, (unitInterval.mul_le_right.trans_lt c.property)⟩ =
      realCirclePathLift (initialArcAngles puncturedArgument γ hi he c.val c.property) u := by
  let A := initialArcAngles puncturedArgument γ hi he c.val c.property
  have hp : initialArcAngles puncturedArgument γ hi he (u * c.val)
      (unitInterval.mul_le_right.trans_lt c.property) = circlePathPrefix A u := by
    ext s
    change normalizedArgument (γ (s * (u * c.val))) = normalizedArgument (γ ((s * u) * c.val))
    rw [mul_assoc]
  rw [diskRayAngle_eq_increment, hp, circlePathIncrement_prefix]
  have h0 : realCirclePathLift A 0 = circleRepresentative (normalizedArgument (γ 0)) := by
    rw [realCirclePathLift, (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_zero]
    simp only [A, initialArcAngles, puncturedArgument, ContinuousMap.coe_mk, zero_mul]
  rw [h0]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayProper
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform properness and angular bounds on every bounded-depth strip
for the lifted compact disk-arc family. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem compact_disk_rays_angle_bound_on_strip
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (Y : ℝ) :
    ∃ M : ℝ, ∀ γ : K, ∀ t : DiskRayTime, diskRayDepth γ.val t ≤ Y →
      |diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 t| ≤ M := by
  obtain ⟨c, hc, M, hc0, htime, hM⟩ :=
    compact_disk_rays_initial_angle_bound K hK hKS (Real.exp_pos (-Y))
  refine ⟨M, fun γ t ht => ?_⟩
  have hp : 0 < ‖γ.val t.val‖ := norm_pos_iff.mpr
    (diskRay_nonzero γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 t)
  have hnorm : Real.exp (-Y) ≤ ‖γ.val t.val‖ := by
    apply (Real.le_log_iff_exp_le hp).mp
    change -Real.log ‖γ.val t.val‖ ≤ Y at ht
    linarith
  have htc := htime γ.val γ.property t.val hnorm
  have hcp : (0 : ℝ) < c := hc0
  let u : unitInterval := ⟨(t.val : ℝ) / (c : ℝ),
    div_nonneg t.val.property.1 hcp.le, (div_le_one hcp).mpr htc.le⟩
  have hut : u * c = t.val := by
    apply Subtype.ext
    exact div_mul_cancel₀ _ hcp.ne'
  have he : (⟨u * c, unitInterval.mul_le_right.trans_lt hc⟩ : DiskRayTime) = t :=
    Subtype.ext hut
  have ha := diskRayAngle_mul_prefix γ.val (hKS γ.property).1
    (hKS γ.property).2.2.1 (⟨c, hc⟩ : DiskRayTime) u
  have hat : diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 t =
      realCirclePathLift (initialArcAngles puncturedArgument γ.val
        (hKS γ.property).1 (hKS γ.property).2.2.1 c hc) u := by
    simpa only [he] using ha
  exact (congrArg abs hat).symm ▸ hM γ u

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayTranslates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Different integer translates of a lifted simple disk arc are disjoint. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem diskRayTime_eq_of_coordinates (γ : C(PathTime, ℂ))
    (hi : Injective γ) (he : γ ⊤ = 0) (s t : DiskRayTime)
    (hangle : (diskRayAngle γ hi he s : UnitAddCircle) = diskRayAngle γ hi he t)
    (hdepth : diskRayDepth γ s = diskRayDepth γ t) : s = t := by
  apply Subtype.ext
  apply hi
  apply Complex.ext_norm_arg
  · have hd : Real.log ‖γ s.val‖ = Real.log ‖γ t.val‖ := neg_injective hdepth
    have hexp := congrArg Real.exp hd
    simpa only [Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hi he s)),
      Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hi he t))] using hexp
  · apply Complex.arg_coe_angle_eq_iff.mp
    apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
    exact (diskRayAngle_projects γ hi he s).symm.trans
      (hangle.trans (diskRayAngle_projects γ hi he t))

theorem translatedDiskRay_eq_iff (γ : C(PathTime, ℂ))
    (hi : Injective γ) (he : γ ⊤ = 0) (k l : ℤ) (s t : DiskRayTime) :
    translatedDiskRay γ hi he k s = translatedDiskRay γ hi he l t ↔ k = l ∧ s = t := by
  constructor
  · intro h
    have ha : diskRayAngle γ hi he s + (k : ℝ) = diskRayAngle γ hi he t + (l : ℝ) :=
      congrArg Prod.fst h
    have hd : diskRayDepth γ s = diskRayDepth γ t := congrArg Prod.snd h
    have hk : ((k : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 (k : ℝ) 0).mpr ⟨k, by simp⟩
    have hl : ((l : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 (l : ℝ) 0).mpr ⟨l, by simp⟩
    have hs : s = t := diskRayTime_eq_of_coordinates γ hi he s t (by
      have hc := congrArg (fun x : ℝ => (x : UnitAddCircle)) ha
      simpa only [AddCircle.coe_add, hk, hl, add_zero] using hc) hd
    subst t
    exact ⟨Int.cast_injective (add_left_cancel ha), rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayJordan
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compactified lifted ray bounds a Jordan disk after closing
along the positive boundary arc. Its entire filling stays in the unit disk. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem jordan_fill_subset_closed_unitDisk (H : ℂ ≃ₜ ℂ)
    (hf : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 1) :
    closure (jordanInterior H) ⊆ Metric.closedBall (0 : ℂ) 1 := by
  apply closed_jordanInterior_subset_of_unbounded_connected_compl H
  · simpa only [jordanInterior, Homeomorph.refl_apply, image_id,
      closure_ball _ one_ne_zero]
      using (isConnected_exterior_jordanInterior (Homeomorph.refl ℂ)).isPreconnected
  · intro hb
    apply NormedSpace.unbounded_univ ℝ ℂ
    have h := (isCompact_closedBall (0 : ℂ) 1).isBounded.union hb
    simpa only [union_compl_self] using h
  · intro z hz
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hf z hz)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskBoundarySide
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from the crosscut, a boundary arc of a filling has a whole relative
neighborhood in the closed disk on the same side. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem closed_disk_neighborhood_in_filling
    (H : ℂ ≃ₜ ℂ) (hU : jordanInterior H ⊆ Metric.ball 0 1)
    {x : ℂ} (hx : x ∈ frontier (jordanInterior H))
    {ε : ℝ} (hε : 0 < ε)
    (hfront : Metric.ball x ε ∩ frontier (jordanInterior H) ⊆ Metric.sphere 0 1) :
    Metric.ball x ε ∩ Metric.closedBall 0 1 ⊆ closure (jordanInterior H) := by
  have hC : IsPreconnected (Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1) :=
    ((convex_ball x ε).inter (convex_ball (0 : ℂ) 1)).isPreconnected
  have hmiss : Disjoint (Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1)
      (frontier (jordanInterior H)) := by
    apply Set.disjoint_left.mpr
    intro z hz hf
    have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp (hfront ⟨hz.1, hf⟩)
    have hl : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz.2
    exact (ne_of_lt hl) hn
  have hsplit : Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 ⊆ jordanInterior H ∨
      Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 ⊆ (closure (jordanInterior H))ᶜ := by
    apply hC.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
    · exact disjoint_compl_right.mono_left subset_closure
    · intro z hz
      by_cases hi : z ∈ jordanInterior H
      · exact Or.inl hi
      · right
        intro hc
        apply Set.disjoint_left.mp hmiss hz
        rw [(jordanInterior_isOpen H).frontier_eq]
        exact ⟨hc, hi⟩
  have hinside : Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 ⊆ jordanInterior H := by
    rcases hsplit with hi | ho
    · exact hi
    · obtain ⟨z, hzB, hzU⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hx)
        (Metric.ball x ε) (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
      exact (ho ⟨hzB, hU hzU⟩ (subset_closure hzU)).elim
  intro z hz
  apply closure_mono hinside
  apply Metric.isOpen_ball.inter_closure
  simpa only [closure_ball _ one_ne_zero] using hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HalfPlaneRay
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactification of the integer translates of a lifted ray. The curve
escapes in height, so the added endpoint is the single boundary point 1. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem translatedHalfPlaneRay_meet_iff (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k l : ℤ) (s t : DiskRayTime) :
    (translatedHalfPlaneRay γ hγ k).curve s = (translatedHalfPlaneRay γ hγ l).curve t ↔
      k = l ∧ s = t := by
  have he : ((translatedHalfPlaneRay γ hγ k).curve s = (translatedHalfPlaneRay γ hγ l).curve t) ↔
      translatedDiskRay γ hγ.1 hγ.2.2.1 k s = translatedDiskRay γ hγ.1 hγ.2.2.1 l t := by
    constructor
    · intro h
      apply Prod.ext
      · simpa [translatedHalfPlaneRay, diskRayComplex, translatedDiskRay, diskRayLift] using congrArg Complex.re h
      · simpa [translatedHalfPlaneRay, diskRayComplex, translatedDiskRay, diskRayLift] using congrArg Complex.im h
    · intro h
      apply Complex.ext
      · simpa [translatedHalfPlaneRay, diskRayComplex, translatedDiskRay, diskRayLift] using congrArg Prod.fst h
      · simpa [translatedHalfPlaneRay, diskRayComplex, translatedDiskRay, diskRayLift] using congrArg Prod.snd h
  exact he.trans (translatedDiskRay_eq_iff γ hγ.1 hγ.2.2.1 k l s t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RayJordanSides
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Side functions for all integer translates of a lifted ray. Boundary
order is the ordinary order on the real boundary of the half-plane. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

namespace HalfPlaneRay

theorem crosscut_norm_le (R : HalfPlaneRay) (t : PathTime) : ‖R.crosscut t‖ ≤ 1 := by
  by_cases ht : t < ⊤
  · change ‖R.compactify t‖ ≤ 1
    rw [compactify, dite_eq_left ht]
    exact halfPlaneDisk_norm_le (R.nonneg _)
  · have he : t = ⊤ := top_le_iff.mp (not_lt.mp ht)
    subst t
    change ‖R.compactify ⊤‖ ≤ 1
    rw [R.compactify_top, norm_one]

theorem filling_subset (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) :
    closure (jordanInterior H) ⊆ Metric.closedBall 0 1 ∧
      jordanInterior H ⊆ Metric.ball 0 1 := by
  have hcl : closure (jordanInterior H) ⊆ Metric.closedBall 0 1 := by
    apply jordan_fill_subset_closed_unitDisk
    intro z hz
    rw [hH] at hz
    rcases hz with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact R.crosscut_norm_le t
    · exact (boundaryClosingArc_norm _ _ t).le
  refine ⟨hcl, ?_⟩
  have hi := interior_mono hcl
  rwa [interior_closure_jordanInterior, interior_closedBall _ one_ne_zero] at hi

theorem isLocallyConstant_side (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) :
    IsLocallyConstant (R.side H) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro z
  by_cases hz : z.val ∈ closure (jordanInterior H)
  · have hn : ∃ ε > 0, Metric.ball z.val ε ∩ Metric.closedBall 0 1 ⊆
        closure (jordanInterior H) := by
      by_cases hi : z.val ∈ jordanInterior H
      · obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.mp (jordanInterior_isOpen H) z.val hi
        exact ⟨ε, hε, fun _ h => subset_closure (hB h.1)⟩
      · have hf : z.val ∈ frontier (jordanInterior H) := by
          rw [(jordanInterior_isOpen H).frontier_eq]
          exact ⟨hz, hi⟩
        obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.mp
          (isCompact_range R.crosscut.continuous).isClosed.isOpen_compl z.val z.property.2
        refine ⟨ε, hε, closed_disk_neighborhood_in_filling H (R.filling_subset hH).2 hf hε ?_⟩
        rintro w ⟨hw, hwf⟩
        rw [hH] at hwf
        rcases hwf with hwc | ⟨t, rfl⟩
        · exact (hB hw hwc).elim
        · exact mem_sphere_zero_iff_norm.mpr (boundaryClosingArc_norm _ _ t)
    obtain ⟨ε, hε, hB⟩ := hn
    have hnear : ∀ᶠ w : R.CutDomain in 𝓝 z, w.val ∈ Metric.ball z.val ε :=
      continuous_subtype_val.continuousAt.eventually
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
    filter_upwards [hnear] with w hw
    simp only [side, ite_eq_left hz, ite_eq_left (hB ⟨hw, w.property.1⟩)]
  · have hnear : ∀ᶠ w : R.CutDomain in 𝓝 z, w.val ∈ (closure (jordanInterior H))ᶜ :=
      continuous_subtype_val.continuousAt.eventually (isClosed_closure.isOpen_compl.mem_nhds hz)
    filter_upwards [hnear] with w hw
    simp only [side, ite_eq_right hz, ite_eq_right hw]

theorem start_eq_real (R : HalfPlaneRay) :
    R.compactify 0 = halfPlaneDisk ((R.curve ⟨0, bot_lt_top⟩).re : ℂ) := by
  have ht : (0 : PathTime) < ⊤ := bot_lt_top
  rw [compactify, dite_eq_left ht]
  congr 1
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using R.start

theorem side_boundary (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H)
    (x : ℝ) (hmiss : halfPlaneDisk x ∉ range R.crosscut) :
    R.side H ⟨halfPlaneDisk x, Metric.mem_closedBall.mpr
      (by simpa only [dist_zero_right] using (cayleyBoundary_norm x).le), hmiss⟩ =
      if x ≤ (R.curve ⟨0, bot_lt_top⟩).re then false else true := by
  have hnot : halfPlaneDisk x ∉ jordanInterior H := by
    intro hi
    have hl : ‖halfPlaneDisk x‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using (R.filling_subset hH).2 hi
    rw [cayleyBoundary_norm] at hl
    exact lt_irrefl _ hl
  have hc : halfPlaneDisk x ∈ closure (jordanInterior H) ↔ x ≤ (R.curve ⟨0, bot_lt_top⟩).re := by
    have he : halfPlaneDisk x ∈ closure (jordanInterior H) ↔ halfPlaneDisk x ∈ frontier (jordanInterior H) := by
      rw [(jordanInterior_isOpen H).frontier_eq]
      simp only [Set.mem_sdiff, hnot, not_false_eq_true, and_true]
    rw [he, hH, mem_union, or_iff_right hmiss]
    have hb := cayleyBoundary_mem_closingArc (R.curve ⟨0, bot_lt_top⟩).re x
    have heq : (fun t : PathTime => boundaryClosingArc (R.compactify 0) R.crosscut_start_norm t) =
        (fun t : PathTime => boundaryClosingArc
          (halfPlaneDisk ((R.curve ⟨0, bot_lt_top⟩).re : ℂ))
          (cayleyBoundary_norm (R.curve ⟨0, bot_lt_top⟩).re) t) := by
      funext t
      change standardCirclePoint _ = standardCirclePoint _
      rw [R.start_eq_real]
    change halfPlaneDisk x ∈ range (fun t : PathTime =>
      boundaryClosingArc (R.compactify 0) R.crosscut_start_norm t) ↔ _
    rw [heq]
    exact hb
  simp only [side, hc]

end HalfPlaneRay
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RaySideConnectivity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both sides of each compactified lifted ray are connected. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.HalfPlaneRay

theorem subset_complement (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ)
    (hf : R.IsJordan H) :
    jordanInterior H ⊆ Metric.ball 0 1 \ range R.crosscut := by
  intro z hz
  refine ⟨(R.filling_subset hf).2 hz, ?_⟩
  intro hp
  have hfront : z ∈ frontier (jordanInterior H) := hf ▸ Or.inl hp
  have hi : z ∈ interior (jordanInterior H) := by
    simpa only [(jordanInterior_isOpen H).interior_eq] using hz
  exact Set.disjoint_left.mp disjoint_interior_frontier hi hfront

theorem component_in_or_out (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ)
    (hf : R.IsJordan H)
    {V : Set ℂ} (hV : IsPreconnected V)
    (hsub : V ⊆ Metric.ball 0 1 \ range R.crosscut) :
    V ⊆ jordanInterior H ∨ V ⊆ (closure (jordanInterior H))ᶜ := by
  apply hV.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
  · exact disjoint_compl_right.mono_left subset_closure
  · intro z hz
    by_cases hin : z ∈ jordanInterior H
    · exact Or.inl hin
    · right
      intro hcl
      have hfront : z ∈ frontier (jordanInterior H) := by
        rw [(jordanInterior_isOpen H).frontier_eq]
        exact ⟨hcl, hin⟩
      rw [hf] at hfront
      rcases hfront with hp | ⟨t, rfl⟩
      · exact (hsub hz).2 hp
      · have hn : ‖boundaryClosingArc _ R.crosscut_start_norm t‖ < 1 := by
          simpa only [Metric.mem_ball, dist_zero_right] using (hsub hz).1
        rw [boundaryClosingArc_norm] at hn
        exact lt_irrefl _ hn

theorem exterior_connected (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ)
    (hf : R.IsJordan H) :
    IsConnected (Metric.ball 0 1 \ closure (jordanInterior H)) := by
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hd, hcover, _, _⟩ :=
    hsep R.crosscut.toContinuousMap R.compactify_injective
      R.crosscut_start_norm (by
        change ‖R.compactify ⊤‖ = 1
        rw [R.compactify_top, norm_one])
      R.crosscut_interior
  have hJsub := subset_complement R H hf
  have hJUorV : jordanInterior H ⊆ U ∨ jordanInterior H ⊆ V := by
    apply (isConnected_jordanInterior H).isPreconnected.subset_or_subset hUo hVo hd
    exact fun z hz => hcover ▸ hJsub hz
  have hcase (A B : Set ℂ) (hAc : IsConnected A) (hBc : IsConnected B)
      (hAB : Disjoint A B) (hc : A ∪ B = Metric.ball 0 1 \ range R.crosscut)
      (hJA : jordanInterior H ⊆ A) :
      Metric.ball 0 1 \ closure (jordanInterior H) = B := by
    have hAsub : A ⊆ Metric.ball 0 1 \ range R.crosscut := hc ▸ subset_union_left
    have hBsub : B ⊆ Metric.ball 0 1 \ range R.crosscut := hc ▸ subset_union_right
    have hAJ : A ⊆ jordanInterior H := by
      rcases component_in_or_out R H hf hAc.isPreconnected hAsub with h | h
      · exact h
      · obtain ⟨z, hz⟩ := (isConnected_jordanInterior H).nonempty
        exact (h (hJA hz) (subset_closure hz)).elim
    have hBout : B ⊆ (closure (jordanInterior H))ᶜ := by
      rcases component_in_or_out R H hf hBc.isPreconnected hBsub with h | h
      · obtain ⟨z, hz⟩ := hBc.nonempty
        exact (Set.disjoint_left.mp hAB (hJA (h hz)) hz).elim
      · exact h
    apply Subset.antisymm
    · intro z hz
      have hn : z ∉ range R.crosscut := by
        intro hp
        exact hz.2 (frontier_subset_closure (hf ▸ Or.inl hp))
      have hu : z ∈ A ∪ B := hc ▸ ⟨hz.1, hn⟩
      rcases hu with hA | hB
      · exact (hz.2 (subset_closure (hAJ hA))).elim
      · exact hB
    · intro z hz
      exact ⟨(hBsub hz).1, hBout hz⟩
  rcases hJUorV with h | h
  · rw [hcase U V hUc hVc hd hcover h]
    exact hVc
  · rw [hcase V U hVc hUc hd.symm (union_comm U V ▸ hcover) h]
    exact hUc


theorem leftSide_connected (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ) (hf : R.IsJordan H) :
    IsConnected (closure (jordanInterior H) \ range R.crosscut) := by
  apply (isConnected_jordanInterior H).subset_closure
  · intro z hz
    exact ⟨subset_closure hz, (R.subset_complement H hf hz).2⟩
  · exact sdiff_subset

theorem rightSide_connected (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ) (hf : R.IsJordan H) :
    IsConnected (Metric.closedBall 0 1 \ closure (jordanInterior H)) := by
  apply (R.exterior_connected hsep H hf).subset_closure
  · exact sdiff_subset_sdiff_left Metric.ball_subset_closedBall
  · intro z hz
    have hh : z ∈ (closure (jordanInterior H))ᶜ ∩ closure (Metric.ball (0 : ℂ) 1) := by
      refine ⟨hz.2, ?_⟩
      simpa only [closure_ball _ one_ne_zero] using hz.1
    have hi := isClosed_closure.isOpen_compl.inter_closure hh
    change z ∈ closure (Metric.ball 0 1 ∩ (closure (jordanInterior H))ᶜ)
    simpa only [inter_comm] using hi

end CircleDomainRigidity.HalfPlaneRay

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VerticalRayAvoidance
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common angular strip bound makes all sufficiently far translates
miss each vertical segment to the real boundary. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem verticalCayleyPath_norm_le (x y : ℝ) (hy : 0 ≤ y) (t : PathTime) :
    ‖verticalCayleyPath x y hy t‖ ≤ 1 := halfPlaneDisk_norm_le (vertical_im_nonneg x y hy t)

theorem verticalCayleyPath_common_strip_bound
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (Y : ℝ) :
    ∃ M : ℝ, ∀ x y : ℝ, ∀ hy : 0 ≤ y, y ≤ Y → ∀ γ : K, ∀ k : ℤ,
      ¬ Disjoint (range (verticalCayleyPath x y hy))
        (range (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut) →
      |x - (k : ℝ)| ≤ M := by
  obtain ⟨M, hM⟩ := compact_disk_rays_angle_bound_on_strip K hK hKS Y
  refine ⟨M, ?_⟩
  intro x y hy hyY γ k hh
  obtain ⟨z, ⟨s, hs⟩, ⟨t, ht⟩⟩ := Set.not_disjoint_iff.mp hh
  have he : verticalCayleyPath x y hy s =
      (translatedHalfPlaneRay γ.val (hKS γ.property) k).compactify t := hs.trans ht.symm
  have hnonneg := vertical_im_nonneg x y hy s
  have htop : t < ⊤ := by
    by_contra hn
    have het : t = ⊤ := top_le_iff.mp (not_lt.mp hn)
    rw [het, HalfPlaneRay.compactify_top] at he
    exact halfPlaneDisk_ne_one hnonneg he
  rw [HalfPlaneRay.compactify, dite_eq_left htop] at he
  have hc := halfPlaneDisk_injOn hnonneg
    ((translatedHalfPlaneRay γ.val (hKS γ.property) k).nonneg ⟨t, htop⟩) he
  have hdep : diskRayDepth γ.val ⟨t, htop⟩ = (s : ℝ) * y := by
    have hi := congrArg Complex.im hc
    simpa only [verticalCayleyPath, ContinuousMap.coe_mk, translatedHalfPlaneRay,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add,
      Complex.intCast_im, diskRayComplex_im] using hi.symm
  have hdle : diskRayDepth γ.val ⟨t, htop⟩ ≤ y := by
    rw [hdep]
    exact mul_le_of_le_one_left hy s.property.2
  have hre : x = diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨t, htop⟩ + (k : ℝ) := by
    have hr := congrArg Complex.re hc
    simpa [verticalCayleyPath, translatedHalfPlaneRay, diskRayComplex] using hr
  have hb := hM γ ⟨t, htop⟩ (hdle.trans hyY)
  have hsub : x - (k : ℝ) =
      diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨t, htop⟩ := by linarith
  rwa [hsub]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FarRaySides
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform eventual values of the translated side functions on bounded
rectangles of the half-plane. This gives the finite range of possible indices. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

namespace HalfPlaneRay

theorem side_eq_boundary_of_vertical_avoidance (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ}
    (hH : R.IsJordan H) (x y : ℝ) (hy : 0 ≤ y)
    (hmiss : Disjoint (range (verticalCayleyPath x y hy)) (range R.crosscut)) :
    (if halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) ∈ closure (jordanInterior H)
      then false else true) = if x ≤ (R.curve ⟨0, bot_lt_top⟩).re then false else true := by
  have hm (t : PathTime) : verticalCayleyPath x y hy t ∉ range R.crosscut :=
    Set.disjoint_left.mp hmiss (mem_range_self t)
  let f : PathTime → R.CutDomain := fun t =>
    ⟨verticalCayleyPath x y hy t, Metric.mem_closedBall.mpr
      (by simpa only [dist_zero_right] using verticalCayleyPath_norm_le x y hy t), hm t⟩
  have hc : Continuous f := (verticalCayleyPath x y hy).continuous.subtype_mk _
  have he := ((R.isLocallyConstant_side hH).comp_continuous hc).apply_eq_of_preconnectedSpace
    (1 : PathTime) 0
  have h0 : halfPlaneDisk x ∉ range R.crosscut := by simpa only [verticalCayleyPath_zero] using hm 0
  have hb := R.side_boundary hH x h0
  have he' : (if halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) ∈ closure (jordanInterior H)
      then false else true) = (if halfPlaneDisk x ∈ closure (jordanInterior H) then false else true) := by
    simpa only [Function.comp_apply, side, f, verticalCayleyPath_zero, verticalCayleyPath_one] using he
  exact he'.trans hb

end HalfPlaneRay

theorem translated_sides_eventually_fixed
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    ∃ N : ℝ, 0 < N ∧ ∀ (γ : K) (x y : ℝ), |x| ≤ X → ∀ _hy : 0 ≤ y, y ≤ Y →
      ∀ (k : ℤ) (H : ℂ ≃ₜ ℂ), (translatedHalfPlaneRay γ.val (hKS γ.property) k).IsJordan H →
      (N < (k : ℝ) → halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) ∈ closure (jordanInterior H)) ∧
      ((k : ℝ) < -N → halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) ∉ closure (jordanInterior H)) := by
  obtain ⟨M, hM⟩ := verticalCayleyPath_common_strip_bound K hK hKS Y
  obtain ⟨A, hA⟩ := compact_disk_rays_angle_bound_on_strip K hK hKS Y
  let N := |M| + |A| + X + 2
  refine ⟨N, by dsimp [N] <;> positivity, ?_⟩
  intro γ x y hx hy hyY k H hH
  have hzero : diskRayDepth γ.val ⟨0, bot_lt_top⟩ = 0 := by
    simp only [diskRayDepth, (hKS γ.property).2.1, Real.log_one, neg_zero]
  have ha := hA γ ⟨0, bot_lt_top⟩ (by simpa only [hzero] using hY)
  have hlo : -|A| ≤ diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨0, bot_lt_top⟩ :=
    (abs_le.mp ha).1.trans' (neg_le_neg (le_abs_self A))
  have hhi : diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨0, bot_lt_top⟩ ≤ |A| :=
    (abs_le.mp ha).2.trans (le_abs_self A)
  have hstart : ((translatedHalfPlaneRay γ.val (hKS γ.property) k).curve ⟨0, bot_lt_top⟩).re =
      diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨0, bot_lt_top⟩ + (k : ℝ) := by
    simp [translatedHalfPlaneRay, diskRayComplex]
  have hside (hk : M < |x - (k : ℝ)|) := by
    have hmiss : Disjoint (range (verticalCayleyPath x y hy))
        (range (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut) := by
      by_contra hn
      exact (not_le_of_gt hk) (hM x y hy hyY γ k hn)
    exact HalfPlaneRay.side_eq_boundary_of_vertical_avoidance _ hH x y hy hmiss
  constructor
  · intro hk
    have hlarge : M < |x - (k : ℝ)| := by
      have hab := neg_le_abs (x - (k : ℝ))
      have hm := le_abs_self M
      have hx' := (abs_le.mp hx).2
      dsimp [N] at hk
      linarith [abs_nonneg A]
    have hs := hside hlarge
    have hle : x ≤ ((translatedHalfPlaneRay γ.val (hKS γ.property) k).curve ⟨0, bot_lt_top⟩).re := by
      rw [hstart]
      have hx' := (abs_le.mp hx).2
      dsimp [N] at hk
      linarith [abs_nonneg M]
    simp only [ite_eq_left hle] at hs
    by_contra hn
    simp only [ite_eq_right hn] at hs
    cases hs
  · intro hk
    have hlarge : M < |x - (k : ℝ)| := by
      have hab := le_abs_self (x - (k : ℝ))
      have hm := le_abs_self M
      have hx' := (abs_le.mp hx).1
      dsimp [N] at hk
      linarith [abs_nonneg A]
    have hs := hside hlarge
    have hlt : ((translatedHalfPlaneRay γ.val (hKS γ.property) k).curve ⟨0, bot_lt_top⟩).re < x := by
      rw [hstart]
      have hx' := (abs_le.mp hx).1
      dsimp [N] at hk
      linarith [abs_nonneg M]
    simp only [ite_eq_right (not_le_of_gt hlt)] at hs
    intro hin
    simp only [ite_eq_left hin] at hs
    cases hs

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GeometricRayIndex
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual greatest-translate index. Compact strip bounds prove that
the defining set is nonempty and bounded above, uniformly over the arc law. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem rayJordan_spec (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) :
    (translatedHalfPlaneRay γ hγ k).IsJordan (rayJordan hsch γ hγ k) :=
  Classical.choose_spec ((translatedHalfPlaneRay γ hγ k).exists_jordan hsch)

theorem compact_ray_indices_bounded (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    ∃ B : ℤ, 0 < B ∧ ∀ (γ : K) (x y : ℝ), |x| ≤ X → 0 ≤ y → y ≤ Y →
      (-B ∈ rayRightIndices hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I)) ∧
      B ∈ upperBounds (rayRightIndices hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I)) := by
  obtain ⟨N, hN, hfixed⟩ := translated_sides_eventually_fixed K hK hKS X Y hX hY
  obtain ⟨B, hB⟩ := exists_int_gt N
  have hBpos : 0 < B := by exact_mod_cast hN.trans hB
  refine ⟨B, hBpos, ?_⟩
  intro γ x y hx hy hyY
  have hneg : ((-B : ℤ) : ℝ) < -N := by rw [Int.cast_neg]; linarith
  constructor
  · exact (hfixed γ x y hx hy hyY (-B) (rayJordan hsch γ.val (hKS γ.property) (-B))
      (rayJordan_spec hsch γ.val (hKS γ.property) (-B))).2 hneg
  · intro k hk
    by_contra hnot
    have hBk : B < k := lt_of_not_ge hnot
    have hNk : N < (k : ℝ) := hB.trans (by exact_mod_cast hBk)
    exact hk ((hfixed γ x y hx hy hyY k (rayJordan hsch γ.val (hKS γ.property) k)
      (rayJordan_spec hsch γ.val (hKS γ.property) k)).1 hNk)

theorem rayRightIndices_nonempty_bddAbove (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) :
    (rayRightIndices hsch γ hγ z).Nonempty ∧ BddAbove (rayRightIndices hsch γ hγ z) := by
  obtain ⟨B, _, hb⟩ := compact_ray_indices_bounded hsch {γ} isCompact_singleton
    (by simpa only [singleton_subset_iff] using hγ) |z.re| z.im (abs_nonneg _) hz
  have h := hb ⟨γ, mem_singleton γ⟩ z.re z.im le_rfl hz le_rfl
  have he : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
  simpa only [he] using And.intro (show (rayRightIndices hsch γ hγ
    ((z.re : ℂ) + (z.im : ℂ) * Complex.I)).Nonempty from ⟨-B, h.1⟩)
    (show BddAbove (rayRightIndices hsch γ hγ ((z.re : ℂ) + (z.im : ℂ) * Complex.I)) from ⟨B, h.2⟩)

theorem geometricRayIndex_isGreatest (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) :
    IsGreatest (rayRightIndices hsch γ hγ z) (geometricRayIndex hsch γ hγ z) := by
  obtain ⟨hne, hbdd⟩ := rayRightIndices_nonempty_bddAbove hsch γ hγ z hz
  exact ⟨Int.csSup_mem hne hbdd, fun _ hk => le_csSup hbdd hk⟩

theorem compact_geometricRayIndex_bound (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    ∃ M : ℝ, ∀ (γ : K) (x y : ℝ), |x| ≤ X → 0 ≤ y → y ≤ Y →
      |(geometricRayIndex hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I) : ℝ)| ≤ M := by
  obtain ⟨B, _, hB⟩ := compact_ray_indices_bounded hsch K hK hKS X Y hX hY
  refine ⟨(B : ℝ), ?_⟩
  intro γ x y hx hy hyY
  obtain ⟨hlow, hupp⟩ := hB γ x y hx hy hyY
  have hnon : (rayRightIndices hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I)).Nonempty :=
    ⟨-B, hlow⟩
  have hbdd : BddAbove (rayRightIndices hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I)) :=
    ⟨B, hupp⟩
  have hsup := Int.csSup_mem hnon hbdd
  have hl := le_csSup hbdd hlow
  have hu := hupp hsup
  apply abs_le.mpr
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_GeometricIndexBoundary
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibration of the greatest-translate index on the real boundary.
The value is the floor of the horizontal coordinate minus the arc start. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem HalfPlaneRay.boundary_hit_iff (R : HalfPlaneRay) (x : ℝ) :
    halfPlaneDisk x ∈ range R.crosscut ↔ x = (R.curve ⟨0, bot_lt_top⟩).re := by
  constructor
  · rintro ⟨t, ht⟩
    have htlt : t < ⊤ := by
      by_contra hn
      have he : t = ⊤ := top_le_iff.mp (not_lt.mp hn)
      subst t
      change R.compactify ⊤ = halfPlaneDisk x at ht
      rw [R.compactify_top] at ht
      exact cayleyBoundary_ne_one x ht.symm
    change R.compactify t = halfPlaneDisk x at ht
    rw [HalfPlaneRay.compactify, dite_eq_left htlt] at ht
    have hc := halfPlaneDisk_injOn (R.nonneg ⟨t, htlt⟩) (by simp) ht
    have hzero : t = 0 := by
      by_contra hn
      have hp := R.positive ⟨t, htlt⟩ (lt_of_le_of_ne bot_le (Ne.symm hn))
      have hi := congrArg Complex.im hc
      simp only [Complex.ofReal_im] at hi
      exact (ne_of_gt hp) hi
    subst t
    exact (congrArg Complex.re hc).symm
  · intro hx
    refine ⟨0, ?_⟩
    change R.compactify 0 = halfPlaneDisk x
    rw [R.start_eq_real, hx]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TranslatedRayOrder
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The side of one translated ray relative to another is fixed by their
starting order on the real boundary. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem translated_curve_avoids_crosscut (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) {k l : ℤ} (hkl : k ≠ l) (t : DiskRayTime) :
    halfPlaneDisk ((translatedHalfPlaneRay γ hγ l).curve t) ∉
      range (translatedHalfPlaneRay γ hγ k).crosscut := by
  let R := translatedHalfPlaneRay γ hγ k
  let S := translatedHalfPlaneRay γ hγ l
  rintro ⟨s, hs⟩
  have hst : s < ⊤ := by
    by_contra hn
    have he : s = ⊤ := top_le_iff.mp (not_lt.mp hn)
    subst s
    change R.compactify ⊤ = halfPlaneDisk (S.curve t) at hs
    rw [R.compactify_top] at hs
    exact halfPlaneDisk_ne_one (S.nonneg t) hs.symm
  change R.compactify s = halfPlaneDisk (S.curve t) at hs
  rw [HalfPlaneRay.compactify, dite_eq_left hst] at hs
  have hc := halfPlaneDisk_injOn (R.nonneg ⟨s, hst⟩) (S.nonneg t) hs
  exact hkl ((translatedHalfPlaneRay_meet_iff γ hγ k l ⟨s, hst⟩ t).mp hc).1

theorem translated_ray_side_value (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) {k l : ℤ} (hkl : k ≠ l)
    (H : ℂ ≃ₜ ℂ) (hH : (translatedHalfPlaneRay γ hγ k).IsJordan H) (t : DiskRayTime) :
    (if halfPlaneDisk ((translatedHalfPlaneRay γ hγ l).curve t) ∈ closure (jordanInterior H)
      then false else true) = if l ≤ k then false else true := by
  let R := translatedHalfPlaneRay γ hγ k
  let S := translatedHalfPlaneRay γ hγ l
  let f : DiskRayTime → R.CutDomain := fun u => ⟨halfPlaneDisk (S.curve u),
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le (S.nonneg u)),
    translated_curve_avoids_crosscut γ hγ hkl u⟩
  have hc : Continuous f := by
    apply Continuous.subtype_mk
    exact continuousOn_halfPlaneDisk.comp_continuous S.curve.continuous S.nonneg
  let : PreconnectedSpace DiskRayTime := Subtype.preconnectedSpace
    (isPreconnected_Iio (a := (⊤ : PathTime)))
  have he := ((R.isLocallyConstant_side hH).comp_continuous hc).apply_eq_of_preconnectedSpace
    t (⟨0, bot_lt_top⟩ : DiskRayTime)
  have hs0 : S.curve ⟨0, bot_lt_top⟩ = ((S.curve ⟨0, bot_lt_top⟩).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using S.start
  have hm : halfPlaneDisk ((S.curve ⟨0, bot_lt_top⟩).re : ℂ) ∉ range R.crosscut := by
    rw [← hs0]
    exact translated_curve_avoids_crosscut γ hγ hkl ⟨0, bot_lt_top⟩
  have hb := R.side_boundary hH (S.curve ⟨0, bot_lt_top⟩).re hm
  have he' : (if halfPlaneDisk (S.curve t) ∈ closure (jordanInterior H) then false else true) =
      (if halfPlaneDisk ((S.curve ⟨0, bot_lt_top⟩).re : ℂ) ∈ closure (jordanInterior H) then false else true) := by
    change (if halfPlaneDisk (S.curve t) ∈ closure (jordanInterior H) then false else true) =
      (if halfPlaneDisk (S.curve ⟨0, bot_lt_top⟩) ∈ closure (jordanInterior H) then false else true) at he
    rw [hs0] at he
    exact he
  have hle : (S.curve ⟨0, bot_lt_top⟩).re ≤ (R.curve ⟨0, bot_lt_top⟩).re ↔ l ≤ k := by
    simp only [S, R, translatedHalfPlaneRay, ContinuousMap.coe_mk, Complex.add_re,
      diskRayComplex, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.intCast_re,
      add_le_add_iff_left, Int.cast_le]
  exact he'.trans (hb.trans (by simp only [hle]))

theorem later_ray_right (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    {k l : ℤ} (hkl : k < l) (H : ℂ ≃ₜ ℂ)
    (hH : (translatedHalfPlaneRay γ hγ k).IsJordan H) (t : DiskRayTime) :
    halfPlaneDisk ((translatedHalfPlaneRay γ hγ l).curve t) ∉ closure (jordanInterior H) := by
  have h := translated_ray_side_value γ hγ hkl.ne H hH t
  rw [ite_eq_right (not_le_of_gt hkl)] at h
  intro hi
  rw [ite_eq_left hi] at h
  cases h

theorem earlier_ray_left (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    {k l : ℤ} (hlk : l < k) (H : ℂ ≃ₜ ℂ)
    (hH : (translatedHalfPlaneRay γ hγ k).IsJordan H) (t : DiskRayTime) :
    halfPlaneDisk ((translatedHalfPlaneRay γ hγ l).curve t) ∈ closure (jordanInterior H) := by
  have h := translated_ray_side_value γ hγ hlk.ne' H hH t
  rw [ite_eq_left hlk.le] at h
  by_contra hi
  rw [ite_eq_right hi] at h
  cases h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TranslatedSideNesting
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right components of integer translates form a decreasing family.
This is derived from crosscut separation and the order of the actual starts. -/

open Set Function Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem HalfPlaneRay.boundary_right (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ}
    (hH : R.IsJordan H) {x : ℝ} (hx : (R.curve ⟨0, bot_lt_top⟩).re < x) :
    halfPlaneDisk x ∉ closure (jordanInterior H) := by
  have hm : halfPlaneDisk x ∉ range R.crosscut := by
    rw [R.boundary_hit_iff]
    exact ne_of_gt hx
  have hb := R.side_boundary hH x hm
  change (if halfPlaneDisk x ∈ closure (jordanInterior H) then false else true) = _ at hb
  rw [ite_eq_right (not_le_of_gt hx)] at hb
  intro hi
  rw [ite_eq_left hi] at hb
  cases hb

 theorem earlier_crosscut_in_later_filling (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) {k l : ℤ} (hkl : k < l)
    (H : ℂ ≃ₜ ℂ) (hH : (translatedHalfPlaneRay γ hγ l).IsJordan H) :
    range (translatedHalfPlaneRay γ hγ k).crosscut ⊆ closure (jordanInterior H) := by
  rintro z ⟨t, rfl⟩
  by_cases ht : t < ⊤
  · change (translatedHalfPlaneRay γ hγ k).compactify t ∈ _
    rw [HalfPlaneRay.compactify, dite_eq_left ht]
    exact earlier_ray_left γ hγ hkl H hH ⟨t, ht⟩
  · have he : t = ⊤ := top_le_iff.mp (not_lt.mp ht)
    subst t
    have hf : (1 : ℂ) ∈ frontier (jordanInterior H) := by
      rw [hH]
      left
      exact ⟨⊤, (translatedHalfPlaneRay γ hγ l).compactify_top⟩
    change (translatedHalfPlaneRay γ hγ k).compactify ⊤ ∈ _
    rw [HalfPlaneRay.compactify_top]
    exact frontier_subset_closure hf

 theorem translated_rightSide_antitone (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    {k l : ℤ} (hkl : k < l) (Hk Hl : ℂ ≃ₜ ℂ)
    (hk : (translatedHalfPlaneRay γ hγ k).IsJordan Hk)
    (hl : (translatedHalfPlaneRay γ hγ l).IsJordan Hl) :
    Metric.closedBall 0 1 \ closure (jordanInterior Hl) ⊆
      Metric.closedBall 0 1 \ closure (jordanInterior Hk) := by
  let R := translatedHalfPlaneRay γ hγ k
  let S := translatedHalfPlaneRay γ hγ l
  let A := Metric.closedBall (0 : ℂ) 1 \ closure (jordanInterior Hl)
  have havoid : ∀ z : A, z.val ∉ range R.crosscut := by
    intro z hz
    exact z.property.2 (earlier_crosscut_in_later_filling γ hγ hkl Hl hl hz)
  let f : A → R.CutDomain := fun z => ⟨z.val, z.property.1, havoid z⟩
  have hc : Continuous f := continuous_subtype_val.subtype_mk _
  let : PreconnectedSpace A := Subtype.preconnectedSpace
    (S.rightSide_connected hsep Hl hl).isPreconnected
  let x : ℝ := max (R.curve ⟨0, bot_lt_top⟩).re (S.curve ⟨0, bot_lt_top⟩).re + 1
  have hkx : (R.curve ⟨0, bot_lt_top⟩).re < x := by
    exact lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one
  have hlx : (S.curve ⟨0, bot_lt_top⟩).re < x := by
    exact lt_add_of_le_of_pos (le_max_right _ _) zero_lt_one
  let z₀ : A := ⟨halfPlaneDisk x, Metric.mem_closedBall.mpr
    (by simpa only [dist_zero_right] using (cayleyBoundary_norm x).le), S.boundary_right hl hlx⟩
  intro z hz
  let w : A := ⟨z, hz⟩
  have he := ((R.isLocallyConstant_side hk).comp_continuous hc).apply_eq_of_preconnectedSpace w z₀
  have he' : (if z ∈ closure (jordanInterior Hk) then false else true) = true := by
    simpa only [Function.comp_apply, HalfPlaneRay.side, f, w, z₀,
      ite_eq_right (R.boundary_right hk hkx)] using he
  refine ⟨hz.1, ?_⟩
  intro hi
  rw [ite_eq_left hi] at he'
  cases he'

 theorem rayRightIndices_downward (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im)
    {k l : ℤ} (hkl : k ≤ l) (hl : l ∈ rayRightIndices hsch γ hγ z) :
    k ∈ rayRightIndices hsch γ hγ z := by
  rcases hkl.eq_or_lt with rfl | hlt
  · exact hl
  · exact (translated_rightSide_antitone hsep γ hγ hlt
      (rayJordan hsch γ hγ k) (rayJordan hsch γ hγ l)
      (rayJordan_spec hsch γ hγ k) (rayJordan_spec hsch γ hγ l)
      ⟨Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le hz), hl⟩).2

 theorem mem_rayRightIndices_iff_le (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) (k : ℤ) :
    k ∈ rayRightIndices hsch γ hγ z ↔ k ≤ geometricRayIndex hsch γ hγ z := by
  have hg := geometricRayIndex_isGreatest hsch γ hγ z hz
  exact ⟨fun hk => hg.2 hk, fun hk => rayRightIndices_downward hsch hsep γ hγ z hz hk hg.1⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RayProjection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic half-plane projection sends every integer translate
back to the original terminal arc. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem continuous_diskRayProjection : Continuous diskRayProjection := by
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp Complex.continuous_im.neg)
  · exact continuous_subtype_val.comp
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.comp
        ((AddCircle.continuous_mk' (1 : ℝ)).comp Complex.continuous_re))

theorem diskRayProjection_norm (z : ℂ) : ‖diskRayProjection z‖ = Real.exp (-z.im) := by
  rw [diskRayProjection, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hn : ‖standardCirclePoint (z.re : UnitAddCircle)‖ = 1 := Circle.norm_coe _
  rw [hn, mul_one]

theorem diskRayProjection_argument (z : ℂ) :
    normalizedArgument (diskRayProjection z) = (z.re : UnitAddCircle) := by
  rw [diskRayProjection, normalizedArgument,
    Complex.arg_real_mul _ (Real.exp_pos _)]
  exact normalizedArgument_standardCirclePoint _

theorem diskRayProjection_translated (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) (t : DiskRayTime) :
    diskRayProjection ((translatedHalfPlaneRay γ hγ k).curve t) = γ t.val := by
  apply Complex.ext_norm_arg
  · rw [diskRayProjection_norm]
    change Real.exp (-((diskRayComplex γ hγ.1 hγ.2.2.1 t + (k : ℂ)).im)) = _
    rw [Complex.add_im, Complex.intCast_im, add_zero, diskRayComplex_im,
      diskRayDepth, neg_neg, Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hγ.1 hγ.2.2.1 t))]
  · apply Complex.arg_coe_angle_eq_iff.mp
    apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
    change normalizedArgument (diskRayProjection ((translatedHalfPlaneRay γ hγ k).curve t)) = _
    rw [diskRayProjection_argument]
    have hr : ((translatedHalfPlaneRay γ hγ k).curve t).re =
        diskRayAngle γ hγ.1 hγ.2.2.1 t + (k : ℝ) := by
      simp only [translatedHalfPlaneRay, ContinuousMap.coe_mk, Complex.add_re,
        Complex.intCast_re, diskRayComplex, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [hr]
    have hk : ((k : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 (k : ℝ) 0).mpr ⟨k, by simp⟩
    rw [AddCircle.coe_add, hk, add_zero]
    exact diskRayAngle_projects γ hγ.1 hγ.2.2.1 t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathImageCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct image intersections with a closed set. Finite separated
image witnesses make this count Borel without counting repeated visits. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem isClosed_separatedImageHits {H : Set X} (hH : IsClosed H) (n : ℕ) (r : ℝ) :
    IsClosed (separatedImageHits H n r) := by
  let E : Set (C(PathTime, X) × (Fin n → PathTime)) :=
    {p | (∀ i j, i ≠ j → r ≤ dist (p.1 (p.2 i)) (p.1 (p.2 j))) ∧
      ∀ i, p.1 (p.2 i) ∈ H}
  have he (i : Fin n) : Continuous (fun p : C(PathTime, X) × (Fin n → PathTime) =>
      p.1 (p.2 i)) := continuous_eval.comp
    (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))
  have hE : IsClosed E := by
    have hsep : IsClosed {p : C(PathTime, X) × (Fin n → PathTime) |
        ∀ i j, i ≠ j → r ≤ dist (p.1 (p.2 i)) (p.1 (p.2 j))} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le continuous_const ((he i).dist (he j))
    have hmem : IsClosed {p : C(PathTime, X) × (Fin n → PathTime) |
        ∀ i, p.1 (p.2 i) ∈ H} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun i => hH.preimage (he i)
    exact hsep.inter hmem
  have hp : Prod.fst '' E = separatedImageHits H n r := by
    ext γ
    constructor
    · rintro ⟨⟨_, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(γ, t), ht, rfl⟩
  rw [← hp]
  exact isClosedMap_fst_of_compactSpace E hE

theorem imageHitAtLeast_eq_iUnion (H : Set X) (n : ℕ) :
    imageHitAtLeast H n = ⋃ m : ℕ, separatedImageHits H n (1 / ((m : ℝ) + 1)) := by
  ext γ
  constructor
  · rintro ⟨t, ht, hH⟩
    obtain ⟨m, hm⟩ := exists_reciprocal_separation (γ ∘ t) ht
    exact mem_iUnion.mpr ⟨m, t, hm, hH⟩
  · intro h
    obtain ⟨m, t, ht, hH⟩ := mem_iUnion.mp h
    refine ⟨t, ?_, hH⟩
    intro i j he
    by_contra hij
    have hd := ht i j hij
    change γ (t i) = γ (t j) at he
    rw [he, dist_self] at hd
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith

theorem pathImageCount_eq_iSup (H : Set X) (γ : C(PathTime, X)) :
    pathImageCount H γ = ⨆ n : ℕ,
      if γ ∈ imageHitAtLeast H n then (n : ℝ≥0∞) else 0 := by
  apply le_antisymm
  · rw [pathImageCount, ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    let E := F.filter (fun x => x ∈ range γ ∩ H)
    let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
    have hE (i : Fin (Fintype.card E)) : (e i).val ∈ range γ ∩ H :=
      (Finset.mem_filter.mp (e i).property).2
    choose t ht using fun i => (hE i).1
    have he : γ ∈ imageHitAtLeast H (Fintype.card E) := by
      refine ⟨t, ?_, fun i => (ht i).symm ▸ (hE i).2⟩
      intro i j hij
      apply e.injective
      apply Subtype.ext
      exact (ht i).symm.trans (hij.trans (ht j))
    have hn : (Fintype.card E : ℝ≥0∞) ≤ ⨆ n : ℕ,
        if γ ∈ imageHitAtLeast H n then (n : ℝ≥0∞) else 0 := by
      exact (ite_eq_left he).symm.le.trans (le_iSup
        (fun n : ℕ => if γ ∈ imageHitAtLeast H n then (n : ℝ≥0∞) else 0) _)
    simpa only [Finset.sum_boole, Fintype.card_coe] using hn
  · apply iSup_le
    intro n
    split
    · rename_i hn
      obtain ⟨t, ht, hH⟩ := hn
      have hm (i : Fin n) : γ (t i) ∈ range γ ∩ H := ⟨mem_range_self _, hH i⟩
      calc
        (n : ℝ≥0∞) = ∑' i : Fin n,
            if γ (t i) ∈ range γ ∩ H then (1 : ℝ≥0∞) else 0 := by
          simp only [hm, ite_true, if_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
        _ ≤ pathImageCount H γ := ENNReal.tsum_comp_le_tsum_of_injective ht
          (fun x => if x ∈ range γ ∩ H then (1 : ℝ≥0∞) else 0)
    · exact bot_le

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_pathImageCount {H : Set X} (hH : IsClosed H) :
    Measurable (pathImageCount H) := by
  change Measurable (fun γ => pathImageCount H γ)
  simp_rw [pathImageCount_eq_iSup]
  apply Measurable.iSup
  intro n
  apply measurable_const.piecewise _ measurable_const
  rw [imageHitAtLeast_eq_iUnion]
  exact MeasurableSet.iUnion fun m =>
    (isClosed_separatedImageHits hH n (1 / ((m : ℝ) + 1))).measurableSet

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RayIndexCrossings
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every integer between two index values forces a distinct intersection.
Injectivity of the projected test path makes these physical intersections distinct. -/

open Set Function Classical
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem HalfPlaneRay.cayley_mem_crosscut_iff (R : HalfPlaneRay) {z : ℂ} (hz : 0 ≤ z.im) :
    halfPlaneDisk z ∈ range R.crosscut ↔ z ∈ range R.curve := by
  constructor
  · rintro ⟨t, ht⟩
    have hlt : t < ⊤ := by
      by_contra hn
      have he : t = ⊤ := top_le_iff.mp (not_lt.mp hn)
      subst t
      change R.compactify ⊤ = halfPlaneDisk z at ht
      rw [R.compactify_top] at ht
      exact halfPlaneDisk_ne_one hz ht.symm
    refine ⟨⟨t, hlt⟩, ?_⟩
    change R.compactify t = halfPlaneDisk z at ht
    rw [HalfPlaneRay.compactify, dite_eq_left hlt] at ht
    exact halfPlaneDisk_injOn (R.nonneg _) hz ht
  · rintro ⟨t, rfl⟩
    exact ⟨t.val, by change R.compactify t.val = _; rw [HalfPlaneRay.compactify, dite_eq_left t.property]⟩

theorem translated_ray_hit_between_indices (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (k : ℤ) (h0 : geometricRayIndex hsch γ hγ (δ 0) < k)
    (h1 : k ≤ geometricRayIndex hsch γ hγ (δ 1)) :
    ∃ s : PathTime, ∃ t : DiskRayTime, δ s = (translatedHalfPlaneRay γ hγ k).curve t := by
  let R := translatedHalfPlaneRay γ hγ k
  let H := rayJordan hsch γ hγ k
  have ha : halfPlaneDisk (δ 0) ∈ closure (jordanInterior H) := by
    by_contra hn
    have hm : k ∈ rayRightIndices hsch γ hγ (δ 0) := hn
    exact (not_le_of_gt h0) ((mem_rayRightIndices_iff_le hsch hsep γ hγ (δ 0) (hδ 0) k).mp hm)
  have hb : halfPlaneDisk (δ 1) ∉ closure (jordanInterior H) :=
    (mem_rayRightIndices_iff_le hsch hsep γ hγ (δ 1) (hδ 1) k).mpr h1
  by_contra hn
  have hmiss : ∀ s, halfPlaneDisk (δ s) ∉ range R.crosscut := by
    intro s hs
    obtain ⟨t, ht⟩ := (R.cayley_mem_crosscut_iff (hδ s)).mp hs
    exact hn ⟨s, t, ht.symm⟩
  let f : PathTime → R.CutDomain := fun s => ⟨halfPlaneDisk (δ s),
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le (hδ s)), hmiss s⟩
  have hc : Continuous f := (continuousOn_halfPlaneDisk.comp_continuous δ.continuous hδ).subtype_mk _
  have he := ((R.isLocallyConstant_side (rayJordan_spec hsch γ hγ k)).comp_continuous hc).apply_eq_of_preconnectedSpace
    (0 : PathTime) 1
  change (if halfPlaneDisk (δ 0) ∈ closure (jordanInterior H) then false else true) =
    (if halfPlaneDisk (δ 1) ∈ closure (jordanInterior H) then false else true) at he
  rw [ite_eq_left ha, ite_eq_right hb] at he
  cases he

theorem geometric_index_interval_count (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (hinj : Injective (diskRayProjection ∘ δ)) :
    ((Finset.Ioc (geometricRayIndex hsch γ hγ (δ 0))
      (geometricRayIndex hsch γ hγ (δ 1))).card : ℝ≥0∞) ≤
      pathImageCount (diskRayProjection '' range δ) γ := by
  let F := Finset.Ioc (geometricRayIndex hsch γ hγ (δ 0)) (geometricRayIndex hsch γ hγ (δ 1))
  have hex : ∀ k : F, ∃ s : PathTime, ∃ t : DiskRayTime,
      δ s = (translatedHalfPlaneRay γ hγ k.val).curve t := by
    intro k
    have hk := Finset.mem_Ioc.mp k.property
    exact translated_ray_hit_between_indices hsch hsep γ hγ δ hδ k.val hk.1 hk.2
  choose s t ht using hex
  let x : F → ℂ := fun k => diskRayProjection (δ (s k))
  have hx (k : F) : x k ∈ range γ ∩ diskRayProjection '' range δ := by
    refine ⟨⟨(t k).val, ?_⟩, δ (s k), mem_range_self _, rfl⟩
    dsimp [x]
    rw [ht k, diskRayProjection_translated]
  have hxi : Injective x := by
    intro k l hkl
    have hs : s k = s l := hinj hkl
    have hh : (translatedHalfPlaneRay γ hγ k.val).curve (t k) =
        (translatedHalfPlaneRay γ hγ l.val).curve (t l) := (ht k).symm.trans (hs ▸ ht l)
    exact Subtype.ext ((translatedHalfPlaneRay_meet_iff γ hγ k.val l.val (t k) (t l)).mp hh).1
  calc
    (F.card : ℝ≥0∞) = ∑' k : F, if x k ∈ range γ ∩ diskRayProjection '' range δ then (1 : ℝ≥0∞) else 0 := by
      simp only [hx, ite_true, if_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_coe, nsmul_eq_mul, mul_one]
    _ ≤ pathImageCount (diskRayProjection '' range δ) γ :=
      ENNReal.tsum_comp_le_tsum_of_injective hxi
        (fun z => if z ∈ range γ ∩ diskRayProjection '' range δ then (1 : ℝ≥0∞) else 0)

theorem geometric_index_difference_le_intersections (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (hinj : Injective (diskRayProjection ∘ δ)) :
    ENNReal.ofReal |(geometricRayIndex hsch γ hγ (δ 1) : ℝ) -
      (geometricRayIndex hsch γ hγ (δ 0) : ℝ)| ≤
      pathImageCount (diskRayProjection '' range δ) γ := by
  have hforward (ε : C(PathTime, ℂ)) (hε : ∀ t, 0 ≤ (ε t).im)
      (hi : Injective (diskRayProjection ∘ ε))
      (hle : geometricRayIndex hsch γ hγ (ε 0) ≤ geometricRayIndex hsch γ hγ (ε 1)) :
      ENNReal.ofReal ((geometricRayIndex hsch γ hγ (ε 1) : ℝ) -
        (geometricRayIndex hsch γ hγ (ε 0) : ℝ)) ≤
        pathImageCount (diskRayProjection '' range ε) γ := by
    have hcard := Int.card_Ioc_of_le _ _ hle
    have hr : ((Finset.Ioc (geometricRayIndex hsch γ hγ (ε 0))
        (geometricRayIndex hsch γ hγ (ε 1))).card : ℝ) =
        (geometricRayIndex hsch γ hγ (ε 1) : ℝ) -
        (geometricRayIndex hsch γ hγ (ε 0) : ℝ) := by exact_mod_cast hcard
    rw [← hr, ENNReal.ofReal_natCast]
    exact geometric_index_interval_count hsch hsep γ hγ ε hε hi
  by_cases hle : geometricRayIndex hsch γ hγ (δ 0) ≤ geometricRayIndex hsch γ hγ (δ 1)
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hle))]
    exact hforward δ hδ hinj hle
  · let ε : C(PathTime, ℂ) := ⟨δ ∘ unitInterval.symm, δ.continuous.comp unitInterval.continuous_symm⟩
    have hε0 : ε 0 = δ 1 := congrArg δ unitInterval.symm_zero
    have hε1 : ε 1 = δ 0 := congrArg δ unitInterval.symm_one
    have hrange : range ε = range δ := unitInterval.symmHomeomorph.surjective.range_comp δ
    have hi : Injective (diskRayProjection ∘ ε) := hinj.comp unitInterval.symmHomeomorph.injective
    have hh := hforward ε (fun t => hδ _) hi (by rw [hε0, hε1]; exact le_of_not_ge hle)
    rw [hε0, hε1, hrange] at hh
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hle))), neg_sub]
    exact hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RayFamilyMeasurable
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel dependence of the compactified rays on the actual arc sample.
No measurable choice of Schoenflies homeomorphisms is used. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

variable (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)

theorem continuous_initialArcAngles_family (c : PathTime) (hc : c < ⊤) :
    Continuous (fun γ : K => initialArcAngles puncturedArgument γ.val
      (hKS γ.property).1 (hKS γ.property).2.2.1 c hc) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply puncturedArgument.continuous.comp
  apply Continuous.subtype_mk
  exact continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_snd.mul continuous_const))

theorem measurable_diskRayAngle_family (t : DiskRayTime) :
    Measurable (fun γ : K => diskRayAngle γ.val (hKS γ.property).1
      (hKS γ.property).2.2.1 t) := by
  have hs : Measurable (fun γ : K => circleRepresentative (normalizedArgument (γ.val 0))) :=
    measurable_circleRepresentative_dup1.comp (measurable_normalizedArgument.comp
      ((continuous_eval_const 0).comp continuous_subtype_val).measurable)
  have hi := continuous_circlePathIncrement.comp (continuous_initialArcAngles_family K hKS t.val t.property)
  convert hs.add hi.measurable using 1
  all_goals try with_reducible_and_instances rfl
  funext γ
  exact diskRayAngle_eq_increment _ _ _ t

theorem measurable_translatedRay_family (k : ℤ) (t : DiskRayTime) :
    Measurable (fun γ : K => (translatedHalfPlaneRay γ.val (hKS γ.property) k).curve t) := by
  have ha := measurable_diskRayAngle_family K hKS t
  have hd : Measurable (fun γ : K => diskRayDepth γ.val t) :=
    (((continuous_eval_const t.val).comp continuous_subtype_val).measurable.norm.log).neg
  exact ((Complex.continuous_ofReal.measurable.comp ha).add
    ((Complex.continuous_ofReal.measurable.comp hd).mul_const Complex.I)).add_const (k : ℂ)

theorem measurable_translatedCrosscut_family (k : ℤ) :
    Measurable (fun γ : K => (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut.toContinuousMap) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  by_cases ht : t < ⊤
  · have hc : Measurable halfPlaneDisk := by
      unfold halfPlaneDisk
      fun_prop
    have hm := hc.comp (measurable_translatedRay_family K hKS k ⟨t, ht⟩)
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    funext γ
    change (translatedHalfPlaneRay γ.val (hKS γ.property) k).compactify t = halfPlaneDisk _
    rw [HalfPlaneRay.compactify, dite_eq_left ht]
  · have he : t = ⊤ := top_le_iff.mp (not_lt.mp ht)
    subst t
    have heq : (fun γ : K => (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut.toContinuousMap ⊤) =
        fun _ => (1 : ℂ) := by
      funext γ
      exact HalfPlaneRay.compactify_top _
    rw [heq]
    exact measurable_const

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CutPathComponents
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed-disk crosscut complement is locally path connected. Thus the
connected sides already proved are its actual path components. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.HalfPlaneRay

 theorem cutDomain_locallyPathConnected (R : HalfPlaneRay) : LocallyPathConnectedSpace R.CutDomain := by
  constructor
  intro x
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨r, hr, hrmiss⟩ := Metric.isOpen_iff.mp
    (isCompact_range R.crosscut.continuous).isClosed.isOpen_compl x.val x.property.2
  let d := min ε r
  have hd : 0 < d := lt_min hε hr
  refine ⟨Metric.ball x d, Metric.ball_mem_nhds _ hd, ?_, ?_⟩
  · apply Topology.IsInducing.subtypeVal.isPathConnected_iff.mpr
    have he : Subtype.val '' Metric.ball x d =
        Metric.ball x.val d ∩ Metric.closedBall (0 : ℂ) 1 := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨hw, w.property.1⟩
      · intro hz
        have hzr : z ∈ Metric.ball x.val r :=
          (Metric.ball_subset_ball (min_le_right ε r)) hz.1
        have hm : z ∉ range R.crosscut := hrmiss hzr
        exact ⟨⟨z, hz.2, hm⟩, hz.1, rfl⟩
    rw [he]
    exact ((convex_ball x.val d).inter (convex_closedBall (0 : ℂ) 1)).isPathConnected
      ⟨x.val, Metric.mem_ball_self hd, x.property.1⟩
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans hεU

 theorem side_fiber_preconnected (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) (b : Bool) :
    IsPreconnected {z : R.CutDomain | R.side H z = b} := by
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  cases b with
  | false =>
    have he : Subtype.val '' {z : R.CutDomain | R.side H z = false} =
        closure (jordanInterior H) \ range R.crosscut := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨?_, w.property.2⟩
        by_contra hn
        change (if w.val ∈ closure (jordanInterior H) then false else true) = false at hw
        rw [ite_eq_right hn] at hw
        cases hw
      · intro hz
        refine ⟨⟨z, (R.filling_subset hH).1 hz.1, hz.2⟩, ?_, rfl⟩
        exact ite_eq_left hz.1
    rw [he]
    exact (R.leftSide_connected H hH).isPreconnected
  | true =>
    have he : Subtype.val '' {z : R.CutDomain | R.side H z = true} =
        Metric.closedBall 0 1 \ closure (jordanInterior H) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w.property.1, ?_⟩
        intro hi
        change (if w.val ∈ closure (jordanInterior H) then false else true) = true at hw
        rw [ite_eq_left hi] at hw
        cases hw
      · intro hz
        have hm : z ∉ range R.crosscut := fun hp => hz.2
          (frontier_subset_closure (hH ▸ Or.inl hp))
        refine ⟨⟨z, hz.1, hm⟩, ?_, rfl⟩
        exact ite_eq_right hz.2
    rw [he]
    exact (R.rightSide_connected hsep H hH).isPreconnected

 theorem side_eq_iff_joined (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) (x y : R.CutDomain) :
    R.side H x = R.side H y ↔ Joined x y := by
  let : LocallyPathConnectedSpace R.CutDomain := R.cutDomain_locallyPathConnected
  constructor
  · intro he
    have hc : IsConnected {z : R.CutDomain | R.side H z = R.side H x} :=
      ⟨⟨x, rfl⟩, R.side_fiber_preconnected hsep hH _⟩
    have hp := ((R.isLocallyConstant_side hH).isOpen_fiber _).isConnected_iff_isPathConnected.mp hc
    exact (hp.joinedIn x rfl y he.symm).joined
  · intro h
    have hc := h.somePath.continuous
    have he := ((R.isLocallyConstant_side hH).comp_continuous hc).apply_eq_of_preconnectedSpace
      (0 : PathTime) 1
    simpa only [Function.comp_apply, Path.source, Path.target] using he

end CircleDomainRigidity.HalfPlaneRay

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CrosscutPathSides
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Side membership is characterized by a path avoiding the crosscut to
the corresponding explicit real-boundary point. -/

open Set Function Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

namespace HalfPlaneRay

theorem side_eq_iff_avoidingPath (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) (x y : R.CutDomain) :
    R.side H x = R.side H y ↔ DiskAvoidingPath R.crosscut.toContinuousMap x.val y.val := by
  constructor
  · intro h
    have hj := (R.side_eq_iff_joined hsep hH x y).mp h
    let p := hj.somePath
    refine ⟨⟨fun t => (p t).val, continuous_subtype_val.comp p.continuous⟩, ?_, ?_, ?_⟩
    · exact congrArg Subtype.val p.source
    · exact congrArg Subtype.val p.target
    · exact fun t => (p t).property
  · rintro ⟨δ, h0, h1, hδ⟩
    let f : PathTime → R.CutDomain := fun t => ⟨δ t, hδ t⟩
    have hf : Continuous f := δ.continuous.subtype_mk _
    have he := ((R.isLocallyConstant_side hH).comp_continuous hf).apply_eq_of_preconnectedSpace
      (0 : PathTime) 1
    change (if δ 0 ∈ closure (jordanInterior H) then false else true) =
      (if δ 1 ∈ closure (jordanInterior H) then false else true) at he
    rw [h0, h1] at he
    exact he

theorem right_iff_avoidingPath (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 1) :
    z ∉ closure (jordanInterior H) ↔ DiskAvoidingPath R.crosscut.toContinuousMap z
      (halfPlaneDisk (((R.curve ⟨0, bot_lt_top⟩).re + 1 : ℝ) : ℂ)) := by
  let a := (R.curve ⟨0, bot_lt_top⟩).re + 1
  have ha : (R.curve ⟨0, bot_lt_top⟩).re < a := lt_add_one _
  have hmiss : halfPlaneDisk a ∉ range R.crosscut := by
    rw [R.boundary_hit_iff]
    exact ne_of_gt ha
  let y : R.CutDomain := ⟨halfPlaneDisk a,
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (cayleyBoundary_norm a).le), hmiss⟩
  have hy : R.side H y = true := by
    exact ite_eq_right (R.boundary_right hH ha)
  constructor
  · intro hn
    have hm : z ∉ range R.crosscut := fun hp => hn (frontier_subset_closure (hH ▸ Or.inl hp))
    apply (R.side_eq_iff_avoidingPath hsep hH ⟨z, hz, hm⟩ y).mp
    exact (ite_eq_right hn).trans hy.symm
  · rintro ⟨δ, h0, h1, hδ⟩
    have hm : z ∉ range R.crosscut := h0 ▸ (hδ 0).2
    have he := (R.side_eq_iff_avoidingPath hsep hH ⟨z, hz, hm⟩ y).mpr ⟨δ, h0, h1, hδ⟩
    rw [hy] at he
    intro hi
    change (if z ∈ closure (jordanInterior H) then false else true) = true at he
    rw [ite_eq_left hi] at he
    cases he

theorem left_iff_hit_or_avoidingPath (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 1) :
    z ∈ closure (jordanInterior H) ↔ z ∈ range R.crosscut ∨
      DiskAvoidingPath R.crosscut.toContinuousMap z
        (halfPlaneDisk (((R.curve ⟨0, bot_lt_top⟩).re - 1 : ℝ) : ℂ)) := by
  let a := (R.curve ⟨0, bot_lt_top⟩).re - 1
  have ha : a < (R.curve ⟨0, bot_lt_top⟩).re := sub_one_lt _
  have hmiss : halfPlaneDisk a ∉ range R.crosscut := by
    rw [R.boundary_hit_iff]
    exact ne_of_lt ha
  let y : R.CutDomain := ⟨halfPlaneDisk a,
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (cayleyBoundary_norm a).le), hmiss⟩
  have hy : R.side H y = false := by
    have hb := R.side_boundary hH a hmiss
    exact hb.trans (ite_eq_left ha.le)
  constructor
  · intro hi
    by_cases hm : z ∈ range R.crosscut
    · exact Or.inl hm
    · right
      apply (R.side_eq_iff_avoidingPath hsep hH ⟨z, hz, hm⟩ y).mp
      exact (ite_eq_left hi).trans hy.symm
  · rintro (hm | hp)
    · exact frontier_subset_closure (hH ▸ Or.inl hm)
    · obtain ⟨δ, h0, h1, hδ⟩ := hp
      have hm : z ∉ range R.crosscut := h0 ▸ (hδ 0).2
      have he := (R.side_eq_iff_avoidingPath hsep hH ⟨z, hz, hm⟩ y).mpr ⟨δ, h0, h1, hδ⟩
      rw [hy] at he
      by_contra hi
      change (if z ∈ closure (jordanInterior H) then false else true) = false at he
      rw [ite_eq_right hi] at he
      cases he

end HalfPlaneRay
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasurableRaySides
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both sides have analytic path descriptions, so their membership sets
are Borel by Suslin's theorem. This avoids a measurable Schoenflies choice. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem isClosed_pathPairMeet :
    IsClosed {p : C(PathTime, ℂ) × C(PathTime, ℂ) | ¬ Disjoint (range p.1) (range p.2)} := by
  let E : Set ((C(PathTime, ℂ) × C(PathTime, ℂ)) × (PathTime × PathTime)) :=
    {p | p.1.1 p.2.1 = p.1.2 p.2.2}
  have hE : IsClosed E := isClosed_eq
    (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd.fst))
    (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd.snd))
  have he : Prod.fst '' E = {p : C(PathTime, ℂ) × C(PathTime, ℂ) |
      ¬ Disjoint (range p.1) (range p.2)} := by
    ext p
    constructor
    · rintro ⟨⟨_, s, t⟩, h, rfl⟩ hd
      exact Set.disjoint_left.mp hd (mem_range_self s) (h ▸ mem_range_self t)
    · intro h
      obtain ⟨z, hz, hw⟩ := Set.not_disjoint_iff.mp h
      obtain ⟨s, hs⟩ := hz
      obtain ⟨t, ht⟩ := hw
      exact ⟨(p, s, t), hs.trans ht.symm, rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace E hE

 theorem analyticSet_diskAvoidingPath {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (p : X → C(PathTime, ℂ)) (hp : Measurable p)
    (z w : X → ℂ) (hz : Measurable z) (hw : Measurable w) :
    AnalyticSet {x | DiskAvoidingPath (p x) (z x) (w x)} := by
  let E : Set (X × C(PathTime, ℂ)) := {q |
    q.2 0 = z q.1 ∧ q.2 1 = w q.1 ∧
      (∀ t, q.2 t ∈ Metric.closedBall 0 1) ∧ Disjoint (range (p q.1)) (range q.2)}
  have hball : IsClosed {δ : C(PathTime, ℂ) | ∀ t, δ t ∈ Metric.closedBall 0 1} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => Metric.isClosed_closedBall.preimage (continuous_eval_const t)
  have hE : MeasurableSet E := by
    have hmiss : MeasurableSet {q : X × C(PathTime, ℂ) |
        Disjoint (range (p q.1)) (range q.2)} := by
      convert (isClosed_pathPairMeet.measurableSet.compl.preimage
        ((hp.comp measurable_fst).prodMk measurable_snd)) using 1
      all_goals try with_reducible_and_instances rfl
      ext q
      change Disjoint (range (p q.1)) (range q.2) ↔ ¬¬ Disjoint (range (p q.1)) (range q.2)
      exact not_not.symm
    exact (measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_snd)
      (hz.comp measurable_fst)).inter
      ((measurableSet_eq_fun ((continuous_eval_const 1).measurable.comp measurable_snd)
        (hw.comp measurable_fst)).inter
        ((hball.measurableSet.preimage measurable_snd).inter hmiss))
  have he : Prod.fst '' E = {x | DiskAvoidingPath (p x) (z x) (w x)} := by
    ext x
    constructor
    · rintro ⟨⟨x, δ⟩, h, rfl⟩
      refine ⟨δ, h.1, h.2.1, fun t => ⟨h.2.2.1 t, ?_⟩⟩
      intro ht
      exact Set.disjoint_left.mp h.2.2.2 ht (mem_range_self t)
    · rintro ⟨δ, h0, h1, hδ⟩
      refine ⟨(x, δ), ⟨h0, h1, fun t => (hδ t).1, ?_⟩, rfl⟩
      apply Set.disjoint_left.mpr
      rintro u hu ⟨t, rfl⟩
      exact (hδ t).2 hu
  rw [← he]
  exact hE.analyticSet.image_of_continuous continuous_fst

 theorem measurableSet_rayRightFamily {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (hsep : UnitDiskCrosscutSeparation)
    (R : X → HalfPlaneRay) (H : X → ℂ ≃ₜ ℂ) (hH : ∀ x, (R x).IsJordan (H x))
    (hp : Measurable (fun x => (R x).crosscut.toContinuousMap))
    (ha : Measurable (fun x => ((R x).curve ⟨0, bot_lt_top⟩).re))
    (z : X → ℂ) (hz : Measurable z) (hzd : ∀ x, z x ∈ Metric.closedBall 0 1) :
    MeasurableSet {x | z x ∉ closure (jordanInterior (H x))} := by
  have hM : Measurable halfPlaneDisk := by unfold halfPlaneDisk; fun_prop
  have hplus : Measurable (fun x => halfPlaneDisk
      ((((R x).curve ⟨0, bot_lt_top⟩).re + 1 : ℝ) : ℂ)) :=
    hM.comp (Complex.continuous_ofReal.measurable.comp (ha.add_const 1))
  have hminus : Measurable (fun x => halfPlaneDisk
      ((((R x).curve ⟨0, bot_lt_top⟩).re - 1 : ℝ) : ℂ)) :=
    hM.comp (Complex.continuous_ofReal.measurable.comp (ha.sub_const 1))
  have hright : AnalyticSet {x | z x ∉ closure (jordanInterior (H x))} := by
    have he : {x | z x ∉ closure (jordanInterior (H x))} =
        {x | DiskAvoidingPath (R x).crosscut.toContinuousMap (z x)
          (halfPlaneDisk ((((R x).curve ⟨0, bot_lt_top⟩).re + 1 : ℝ) : ℂ))} := by
      ext x
      exact (R x).right_iff_avoidingPath hsep (hH x) (hzd x)
    rw [he]
    exact analyticSet_diskAvoidingPath _ hp z _ hz hplus
  apply hright.measurableSet_of_compl
  have hhit : MeasurableSet {x | z x ∈ range (R x).crosscut} :=
    isClosed_pathHitSet.measurableSet.preimage (hp.prodMk hz)
  have hleft := analyticSet_diskAvoidingPath _ hp z _ hz hminus
  have he : {x | z x ∉ closure (jordanInterior (H x))}ᶜ =
      {x | z x ∈ range (R x).crosscut} ∪
      {x | DiskAvoidingPath (R x).crosscut.toContinuousMap (z x)
        (halfPlaneDisk ((((R x).curve ⟨0, bot_lt_top⟩).re - 1 : ℝ) : ℂ))} := by
    ext x
    simpa only [mem_compl_iff, mem_ofPred_eq, not_not, mem_union] using
      (R x).left_iff_hit_or_avoidingPath hsep (hH x) (hzd x)
  rw [he]
  have hu := AnalyticSet.iUnion (s := fun b : Bool => if b then
      {x | DiskAvoidingPath (R x).crosscut.toContinuousMap (z x)
        (halfPlaneDisk ((((R x).curve ⟨0, bot_lt_top⟩).re - 1 : ℝ) : ℂ))}
      else {x | z x ∈ range (R x).crosscut})
    (fun b => by cases b; exact hhit.analyticSet; exact hleft)
  convert hu using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  constructor
  · rintro (h | h)
    · exact mem_iUnion.mpr ⟨false, h⟩
    · exact mem_iUnion.mpr ⟨true, h⟩
  · intro h
    obtain ⟨b, hb⟩ := mem_iUnion.mp h
    cases b
    · exact Or.inl hb
    · exact Or.inr hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GeometricIndexLocal
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local constancy of the greatest-translate index follows from the common
finite strip bound and local constancy of each of the finitely many relevant sides. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem isLocallyConstant_rayIndexSide (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) :
    IsLocallyConstant (rayIndexSide hsch γ hγ k) := by
  have hc : Continuous (fun z : RayIndexDomain γ hγ => halfPlaneDisk z.val) :=
    continuousOn_halfPlaneDisk.comp_continuous continuous_subtype_val (fun z => z.property.1)
  exact ((translatedHalfPlaneRay γ hγ k).isLocallyConstant_side
    (rayJordan_spec hsch γ hγ k)).comp_continuous (hc.subtype_mk _)

theorem rayIndexSide_eq_true_iff (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) (z : RayIndexDomain γ hγ) :
    rayIndexSide hsch γ hγ k z = true ↔ k ∈ rayRightIndices hsch γ hγ z.val := by
  unfold rayIndexSide HalfPlaneRay.side rayRightIndices
  split_ifs <;> simp_all

theorem isLocallyConstant_geometricRayIndex (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) :
    IsLocallyConstant (fun z : RayIndexDomain γ hγ => geometricRayIndex hsch γ hγ z.val) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro z
  let X := |z.val.re| + 1
  let Y := z.val.im + 1
  have hX : 0 ≤ X := by dsimp [X] <;> positivity
  have hY : 0 ≤ Y := by dsimp [Y] <;> linarith [z.property.1]
  obtain ⟨N, _, hN⟩ := translated_sides_eventually_fixed {γ} isCompact_singleton
    (by simpa only [singleton_subset_iff] using hγ) X Y hX hY
  obtain ⟨B, hB⟩ := exists_int_gt N
  have hfar (w : RayIndexDomain γ hγ) (hwX : |w.val.re| ≤ X) (hwY : w.val.im ≤ Y) (k : ℤ) :
      (N < (k : ℝ) → k ∉ rayRightIndices hsch γ hγ w.val) ∧
      ((k : ℝ) < -N → k ∈ rayRightIndices hsch γ hγ w.val) := by
    have h := hN ⟨γ, mem_singleton γ⟩ w.val.re w.val.im hwX w.property.1 hwY k
      (rayJordan hsch γ hγ k) (rayJordan_spec hsch γ hγ k)
    have he := Complex.re_add_im w.val
    constructor
    · intro hk hm
      exact hm (he ▸ h.1 hk)
    · intro hk
      exact he ▸ h.2 hk
  have hzX : |z.val.re| ≤ X := by dsimp [X]; linarith
  have hzY : z.val.im ≤ Y := by dsimp [Y] <;> linarith
  have hnearX : ∀ᶠ w : RayIndexDomain γ hγ in 𝓝 z, |w.val.re| ≤ X := by
    have hc : Continuous (fun w : RayIndexDomain γ hγ => |w.val.re|) :=
      (Complex.continuous_re.comp continuous_subtype_val).abs
    have hzlt : |z.val.re| < X := by dsimp [X]; linarith
    exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds hzlt)).mono
      (fun _ h => h.le)
  have hnearY : ∀ᶠ w : RayIndexDomain γ hγ in 𝓝 z, w.val.im ≤ Y := by
    have hc : Continuous (fun w : RayIndexDomain γ hγ => w.val.im) :=
      Complex.continuous_im.comp continuous_subtype_val
    have hzlt : z.val.im < Y := by dsimp [Y] <;> linarith
    exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds hzlt)).mono
      (fun _ h => h.le)
  have hfinite : ∀ᶠ w : RayIndexDomain γ hγ in 𝓝 z,
      ∀ k : {k : ℤ // k ∈ Icc (-B) B}, rayIndexSide hsch γ hγ k.val w = rayIndexSide hsch γ hγ k.val z := by
    apply Filter.eventually_all.mpr
    intro k
    exact (isLocallyConstant_rayIndexSide hsch γ hγ k.val).eventually_eq z
  filter_upwards [hnearX, hnearY, hfinite] with w hwX hwY hw
  have heq : rayRightIndices hsch γ hγ w.val = rayRightIndices hsch γ hγ z.val := by
    ext k
    by_cases hk : k ∈ Icc (-B) B
    · rw [← rayIndexSide_eq_true_iff, ← rayIndexSide_eq_true_iff, hw ⟨k, hk⟩]
    · have hsplit : k < -B ∨ B < k := by
        simpa only [mem_Icc, not_and_or, not_le] using hk
      rcases hsplit with hleft | hright
      · have hkn : (k : ℝ) < -N := by
          have hk' : (k : ℝ) < (-B : ℤ) := by exact_mod_cast hleft
          rw [Int.cast_neg] at hk'
          linarith
        exact iff_of_true ((hfar w hwX hwY k).2 hkn) ((hfar z hzX hzY k).2 hkn)
      · have hkn : N < (k : ℝ) := hB.trans (by exact_mod_cast hright)
        exact iff_of_false ((hfar w hwX hwY k).1 hkn) ((hfar z hzX hzY k).1 hkn)
  exact congrArg sSup heq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_GeometricIndexMeasurable
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual greatest-translate index is Borel in a compact arc sample.
Its definition may use arbitrary Jordan charts; measurability does not. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem measurableSet_rayRightIndices (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) (k : ℤ) :
    MeasurableSet {γ : K | k ∈ rayRightIndices hsch γ.val (hKS γ.property) z} := by
  let : PolishSpace K := hK.isClosed.polishSpace
  apply measurableSet_rayRightFamily hsep
    (fun γ : K => translatedHalfPlaneRay γ.val (hKS γ.property) k)
    (fun γ : K => rayJordan hsch γ.val (hKS γ.property) k)
    (fun γ => rayJordan_spec hsch γ.val (hKS γ.property) k)
    (measurable_translatedCrosscut_family K hKS k)
    (Complex.continuous_re.measurable.comp (measurable_translatedRay_family K hKS k ⟨0, bot_lt_top⟩))
    (fun _ => halfPlaneDisk z) measurable_const
  intro γ
  exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le hz)

 theorem measurable_geometricRayIndex (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) :
    Measurable (fun γ : K => geometricRayIndex hsch γ.val (hKS γ.property) z) := by
  apply measurable_of_Ioi
  intro k
  have hm := measurableSet_rayRightIndices hsch hsep K hK hKS z hz (k + 1)
  have he : {γ : K | k + 1 ∈ rayRightIndices hsch γ.val (hKS γ.property) z} =
      (fun γ : K => geometricRayIndex hsch γ.val (hKS γ.property) z) ⁻¹' Ioi k := by
    ext γ
    rw [mem_ofPred_eq, mem_rayRightIndices_iff_le hsch hsep γ.val (hKS γ.property) z hz]
    change k + 1 ≤ geometricRayIndex hsch γ.val (hKS γ.property) z ↔
      k < geometricRayIndex hsch γ.val (hKS γ.property) z
    omega
  exact he ▸ hm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanGeometricIndex
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the actual geometric index of a compact arc law. Uniform
bounds come from the ray geometry, rather than a domination hypothesis. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem integrable_geometricRayIndex (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) :
    Integrable (fun γ : K => (geometricRayIndex hsch γ.val (hKS γ.property) z.val : ℝ))
      (η : Measure K) := by
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS |z.val.re| z.val.im
    (abs_nonneg _) z.property
  apply Integrable.of_bound
    ((show Continuous (fun n : ℤ => (n : ℝ)) from continuous_of_discreteTopology).measurable.comp
      (measurable_geometricRayIndex hsch hsep K hK hKS z.val z.property)).aestronglyMeasurable M
  apply Eventually.of_forall
  intro γ
  have he := Complex.re_add_im z.val
  simpa only [Function.comp_apply, he, Real.norm_eq_abs] using hM γ z.val.re z.val.im le_rfl z.property le_rfl

 theorem rayIndexDomain_of_projection_avoids (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ClosedUpperHalfPlane)
    (hz : diskRayProjection z.val ∉ range γ) :
    ∀ k : ℤ, halfPlaneDisk z.val ∉ range (translatedHalfPlaneRay γ hγ k).crosscut := by
  intro k hk
  obtain ⟨t, ht⟩ := ((translatedHalfPlaneRay γ hγ k).cayley_mem_crosscut_iff z.property).mp hk
  apply hz
  refine ⟨t.val, ?_⟩
  rw [← diskRayProjection_translated γ hγ k t, ht]

 theorem continuousAt_geometricRayIndex_of_avoids (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (z : ClosedUpperHalfPlane)
    (hz : diskRayProjection z.val ∉ range γ) :
    ContinuousAt (fun w : ClosedUpperHalfPlane =>
      (geometricRayIndex hsch γ hγ w.val : ℝ)) z := by
  let U := {w : ClosedUpperHalfPlane | diskRayProjection w.val ∉ range γ}
  have ho : IsOpen U := (isCompact_range γ.continuous).isClosed.isOpen_compl.preimage
    (continuous_diskRayProjection.comp continuous_subtype_val)
  have hc : ContinuousOn (fun w : ClosedUpperHalfPlane =>
      (geometricRayIndex hsch γ hγ w.val : ℝ)) U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let f : U → RayIndexDomain γ hγ := fun w => ⟨w.val.val, w.val.property,
      rayIndexDomain_of_projection_avoids γ hγ w.val w.property⟩
    have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (show Continuous (fun n : ℤ => (n : ℝ)) from continuous_of_discreteTopology).comp
      ((isLocallyConstant_geometricRayIndex hsch γ hγ).continuous.comp hf)
  exact hc.continuousAt (ho.mem_nhds hz)

 theorem continuousAt_meanGeometricIndex (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane)
    (hz : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection z.val ∉ range γ.val) :
    ContinuousAt (meanGeometricIndex hsch K hKS η) z := by
  let X := |z.val.re| + 1
  let Y := z.val.im + 1
  have hX : 0 ≤ X := by dsimp [X] <;> positivity
  have hY : 0 ≤ Y := by dsimp [Y] <;> linarith [z.property]
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS X Y hX hY
  have hx : ∀ᶠ w : ClosedUpperHalfPlane in 𝓝 z, |w.val.re| ≤ X := by
    have hc := (Complex.continuous_re.comp (continuous_subtype_val (p := fun z : ℂ => 0 ≤ z.im))).abs
    have hl : |z.val.re| < X := by dsimp [X]; linarith
    exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds hl)).mono (fun _ h => h.le)
  have hy : ∀ᶠ w : ClosedUpperHalfPlane in 𝓝 z, w.val.im ≤ Y := by
    have hc := Complex.continuous_im.comp (continuous_subtype_val (p := fun z : ℂ => 0 ≤ z.im))
    have hl : z.val.im < Y := by dsimp [Y] <;> linarith
    exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds hl)).mono (fun _ h => h.le)
  refine tendsto_integral_filter_of_dominated_convergence (fun _ : K => M)
    (Eventually.of_forall fun w =>
      (integrable_geometricRayIndex hsch hsep K hK hKS η w).aestronglyMeasurable)
    ?_ (integrable_const M) ?_
  · filter_upwards [hx, hy] with w hwX hwY
    apply Eventually.of_forall
    intro γ
    have he := Complex.re_add_im w.val
    simpa only [he, Real.norm_eq_abs] using hM γ w.val.re w.val.im hwX w.property hwY
  · filter_upwards [hz] with γ hγ
    exact continuousAt_geometricRayIndex_of_avoids hsch γ.val (hKS γ.property) z hγ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LiftedMeanContinuity
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous local representatives of the geometric mean index.
Point avoidance is transported through the actual injective Jordan map. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem liftedMeanGeometricIndex_eq (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (Ψ : ℂ → ℂ) (z : ℂ) (hz : 0 ≤ (Ψ z).im) :
    liftedMeanGeometricIndex hsch K hKS η Ψ z =
      meanGeometricIndex hsch K hKS η ⟨Ψ z, hz⟩ := dite_eq_left hz

 theorem continuousOn_liftedMeanGeometricIndex
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) {S : Set ℂ}
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ S)
    (hpos : ∀ z ∈ S, 0 ≤ (Ψ z).im)
    (hmiss : ∀ z ∈ S, ∀ᵐ γ : K ∂(η : Measure K),
      diskRayProjection (Ψ z) ∉ range γ.val) :
    ContinuousOn (liftedMeanGeometricIndex hsch K hKS η Ψ) S := by
  let L : S → ClosedUpperHalfPlane := fun z => ⟨Ψ z.val, hpos z.val z.property⟩
  have hL : Continuous L := (continuousOn_iff_continuous_domRestrict.mp hΨ).subtype_mk _
  have hm : Continuous (fun z : S => meanGeometricIndex hsch K hKS η (L z)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (continuousAt_meanGeometricIndex hsch hsep K hK hKS η (L z)
      (hmiss z.val z.property)).comp hL.continuousAt
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hm.congr
  intro z
  exact (liftedMeanGeometricIndex_eq hsch K hKS η Ψ z.val (hpos z.val z.property)).symm

 theorem bounded_liftedMeanGeometricIndex_on_compact
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K)
    {S : Set ℂ} (hS : IsCompact S) (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ S)
    (hpos : ∀ z ∈ S, 0 ≤ (Ψ z).im) :
    ∃ M : ℝ, ∀ z ∈ S, ‖liftedMeanGeometricIndex hsch K hKS η Ψ z‖ ≤ M := by
  obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn hΨ
  let T := max R 0
  have hT : 0 ≤ T := le_max_right _ _
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS T T hT hT
  refine ⟨M, ?_⟩
  intro z hz
  rw [liftedMeanGeometricIndex_eq hsch K hKS η Ψ z (hpos z hz)]
  have hb : ‖Ψ z‖ ≤ T := (hR z hz).trans (le_max_left _ _)
  have hx : |(Ψ z).re| ≤ T := (Complex.abs_re_le_norm _).trans hb
  have hy : (Ψ z).im ≤ T := (Complex.im_le_norm _).trans hb
  have hi : ∀ᵐ γ : K ∂(η : Measure K),
      ‖(geometricRayIndex hsch γ.val (hKS γ.property) (Ψ z) : ℝ)‖ ≤ M := by
    apply Eventually.of_forall
    intro γ
    simpa only [Complex.re_add_im, Real.norm_eq_abs] using
      hM γ (Ψ z).re (Ψ z).im hx (hpos z hz) hy
  simpa only [meanGeometricIndex, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const hi

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)]

 theorem ae_mapped_arc_avoids
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hx : ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x})) :
    ∀ᵐ γ : K ∂((η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure K) : Measure K), F x ∉ range γ.val := by
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff hf.aemeasurable ?_).mpr
  · filter_upwards [hx] with γ hγ
    rw [hmap γ]
    rintro ⟨t, ht⟩
    exact hγ ⟨t, hF γ (Or.inl (mem_range_self t)) (Or.inr (mem_singleton x)) ht⟩
  · exact ((isClosed_pathHitSet.preimage
      (continuous_subtype_val.prodMk continuous_const)).isOpen_compl.measurableSet)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RayIndexOscillation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Near an interior point, a simple lifted ray has index jump at most
one. The jump is zero when the projected point misses the arc. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem geometricRayIndex_on_translated_ray
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) (t : DiskRayTime) :
    geometricRayIndex hsch γ hγ ((translatedHalfPlaneRay γ hγ k).curve t) = k - 1 := by
  let z := (translatedHalfPlaneRay γ hγ k).curve t
  have hz : 0 ≤ z.im := (translatedHalfPlaneRay γ hγ k).nonneg t
  have hlo : k - 1 ≤ geometricRayIndex hsch γ hγ z := by
    apply (mem_rayRightIndices_iff_le hsch hsep γ hγ z hz (k - 1)).mp
    exact later_ray_right γ hγ (by omega) _ (rayJordan_spec hsch γ hγ (k - 1)) t
  have hnot : k ∉ rayRightIndices hsch γ hγ z := by
    intro hk
    apply hk
    apply frontier_subset_closure
    rw [rayJordan_spec hsch γ hγ k]
    left
    exact ⟨t.val, by
      change (translatedHalfPlaneRay γ hγ k).compactify t.val = halfPlaneDisk z
      rw [HalfPlaneRay.compactify, dite_eq_left t.property]⟩
  have hhi : ¬ k ≤ geometricRayIndex hsch γ hγ z :=
    fun hk => hnot ((mem_rayRightIndices_iff_le hsch hsep γ hγ z hz k).mpr hk)
  change geometricRayIndex hsch γ hγ z = k - 1
  omega

 theorem rayInterior_of_index_lt_of_avoids
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    {z : ℂ} (hz : 0 < z.im) (k : ℤ) (hk : geometricRayIndex hsch γ hγ z < k)
    (hmiss : halfPlaneDisk z ∉ range (translatedHalfPlaneRay γ hγ k).crosscut) :
    halfPlaneDisk z ∈ jordanInterior (rayJordan hsch γ hγ k) := by
  have hcl : halfPlaneDisk z ∈ closure (jordanInterior (rayJordan hsch γ hγ k)) := by
    by_contra hn
    exact (not_le_of_gt hk)
      ((mem_rayRightIndices_iff_le hsch hsep γ hγ z hz.le k).mp hn)
  by_contra hi
  have hfront : halfPlaneDisk z ∈ frontier (jordanInterior (rayJordan hsch γ hγ k)) := by
    rw [(jordanInterior_isOpen _).frontier_eq]
    exact ⟨hcl, hi⟩
  rw [rayJordan_spec hsch γ hγ k] at hfront
  rcases hfront with hc | ⟨t, ht⟩
  · exact hmiss hc
  · have hn := halfPlaneDisk_norm_lt hz
    rw [← ht, boundaryClosingArc_norm] at hn
    exact lt_irrefl _ hn

 theorem eventually_geometricRayIndex_bounds
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (z : ClosedUpperHalfPlane) (hz : 0 < z.val.im) :
    ∀ᶠ w : ClosedUpperHalfPlane in 𝓝 z,
      geometricRayIndex hsch γ hγ z.val ≤ geometricRayIndex hsch γ hγ w.val ∧
      geometricRayIndex hsch γ hγ w.val ≤ geometricRayIndex hsch γ hγ z.val +
        if diskRayProjection z.val ∈ range γ then 1 else 0 := by
  let n := geometricRayIndex hsch γ hγ z.val
  let k := n + if diskRayProjection z.val ∈ range γ then 2 else 1
  have hnk : n < k := by dsimp [k]; split_ifs <;> omega
  have hmiss : halfPlaneDisk z.val ∉ range (translatedHalfPlaneRay γ hγ k).crosscut := by
    intro hh
    obtain ⟨t, ht⟩ := ((translatedHalfPlaneRay γ hγ k).cayley_mem_crosscut_iff z.property).mp hh
    have hidx := geometricRayIndex_on_translated_ray hsch hsep γ hγ k t
    rw [ht] at hidx
    have hhit : diskRayProjection z.val ∈ range γ := by
      refine ⟨t.val, ?_⟩
      rw [← diskRayProjection_translated γ hγ k t, ht]
    dsimp [k] at hidx
    rw [ite_eq_left hhit] at hidx
    dsimp [n] at hidx
    omega
  have hleft := rayInterior_of_index_lt_of_avoids hsch hsep γ hγ hz k hnk hmiss
  have hright : halfPlaneDisk z.val ∉ closure (jordanInterior (rayJordan hsch γ hγ n)) :=
    (geometricRayIndex_isGreatest hsch γ hγ z.val z.property).1
  have hD : Continuous (fun w : ClosedUpperHalfPlane => halfPlaneDisk w.val) :=
    continuousOn_halfPlaneDisk.comp_continuous continuous_subtype_val (fun w => w.property)
  have hnearlo := hD.continuousAt.eventually (isClosed_closure.isOpen_compl.mem_nhds hright)
  have hnearhi := hD.continuousAt.eventually ((jordanInterior_isOpen _).mem_nhds hleft)
  filter_upwards [hnearlo, hnearhi] with w hwlo hwhi
  refine ⟨(mem_rayRightIndices_iff_le hsch hsep γ hγ w.val w.property n).mp hwlo, ?_⟩
  have hlt : geometricRayIndex hsch γ hγ w.val < k := by
    by_contra hn
    have hm := (mem_rayRightIndices_iff_le hsch hsep γ hγ w.val w.property k).mpr
      (le_of_not_gt hn)
    exact hm (subset_closure hwhi)
  dsimp [k] at hlt
  dsimp [n] at *
  split_ifs at * <;> omega

 theorem eventually_geometricRayIndex_pair_difference
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (z : ClosedUpperHalfPlane) (hz : 0 < z.val.im) :
    ∀ᶠ p : ClosedUpperHalfPlane × ClosedUpperHalfPlane in 𝓝 (z, z),
      |(geometricRayIndex hsch γ hγ p.1.val : ℝ) -
        (geometricRayIndex hsch γ hγ p.2.val : ℝ)| ≤
          if diskRayProjection z.val ∈ range γ then 1 else 0 := by
  have hb := eventually_geometricRayIndex_bounds hsch hsep γ hγ z hz
  have h₁ := (continuous_fst.tendsto (z, z)).eventually hb
  have h₂ := (continuous_snd.tendsto (z, z)).eventually hb
  filter_upwards [h₁, h₂] with p hp hq
  split_ifs at * with hhit
  · apply abs_le.mpr
    constructor
    · have h : -(1 : ℤ) ≤ geometricRayIndex hsch γ hγ p.1.val - geometricRayIndex hsch γ hγ p.2.val := by omega
      exact_mod_cast h
    · have h : geometricRayIndex hsch γ hγ p.1.val - geometricRayIndex hsch γ hγ p.2.val ≤ (1 : ℤ) := by omega
      exact_mod_cast h
  · have he : geometricRayIndex hsch γ hγ p.1.val =
        geometricRayIndex hsch γ hγ p.2.val := by omega
    simp only [he, sub_self, abs_zero, le_refl]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MeanIndexOscillation
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local oscillation of the averaged index is bounded by the
probability that the sampled arc hits the projected point. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem meanGeometricIndex_oscillation_le_hit
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) (hz : 0 < z.val.im)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ClosedUpperHalfPlane × ClosedUpperHalfPlane in 𝓝 (z, z),
      |meanGeometricIndex hsch K hKS η p.1 - meanGeometricIndex hsch K hKS η p.2| <
        (η : Measure K).real {γ | diskRayProjection z.val ∈ range γ.val} + ε := by
  classical
  let H : Set K := {γ | diskRayProjection z.val ∈ range γ.val}
  have hH : MeasurableSet H := (isClosed_paths_hitting (diskRayProjection z.val)).measurableSet.preimage
    measurable_subtype_coe
  let I : K → ℝ := H.indicator 1
  let n : ClosedUpperHalfPlane → K → ℝ := fun w γ =>
    geometricRayIndex hsch γ.val (hKS γ.property) w.val
  let E : ClosedUpperHalfPlane × ClosedUpperHalfPlane → K → ℝ := fun p γ =>
    max (|n p.1 γ - n p.2 γ| - I γ) 0
  have hI : Integrable I (η : Measure K) := (integrable_const 1).indicator hH
  have hInon (γ : K) : 0 ≤ I γ := by by_cases h : γ ∈ H <;> simp [I, h]
  have hn (w : ClosedUpperHalfPlane) : Integrable (n w) (η : Measure K) :=
    integrable_geometricRayIndex hsch hsep K hK hKS η w
  have hE (p : ClosedUpperHalfPlane × ClosedUpperHalfPlane) : Integrable (E p) (η : Measure K) :=
    (((hn p.1).sub (hn p.2)).abs.sub hI).sup (integrable_const 0)
  have hlim : ∀ᵐ γ : K ∂(η : Measure K),
      Tendsto (fun p => E p γ) (𝓝 (z, z)) (𝓝 0) := by
    apply Eventually.of_forall
    intro γ
    have hb := eventually_geometricRayIndex_pair_difference hsch hsep γ.val (hKS γ.property) z hz
    have he : ∀ᶠ p in 𝓝 (z, z), E p γ = 0 := by
      filter_upwards [hb] with p hp
      dsimp [E, n]
      apply max_eq_right
      have hi : I γ = if diskRayProjection z.val ∈ range γ.val then 1 else 0 := by
        rfl
      rw [hi]
      linarith
    exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
  let X := |z.val.re| + 1
  let Y := z.val.im + 1
  have hX : 0 ≤ X := by dsimp [X] <;> positivity
  have hY : 0 ≤ Y := by dsimp [Y] <;> linarith
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS X Y hX hY
  have hnear : ∀ᶠ w : ClosedUpperHalfPlane in 𝓝 z,
      |w.val.re| ≤ X ∧ w.val.im ≤ Y := by
    have h₁ := ((Complex.continuous_re.comp continuous_subtype_val).abs.continuousAt
      (x := z)).eventually (isOpen_Iio.mem_nhds (show |z.val.re| < X by dsimp [X]; linarith))
    have h₂ := (Complex.continuous_im.comp continuous_subtype_val).continuousAt
      (x := z) |>.eventually (isOpen_Iio.mem_nhds (show z.val.im < Y by dsimp [Y] <;> linarith))
    filter_upwards [h₁, h₂] with w hw₁ hw₂
    exact ⟨hw₁.le, hw₂.le⟩
  have hbound : ∀ᶠ p : ClosedUpperHalfPlane × ClosedUpperHalfPlane in 𝓝 (z, z),
      ∀ᵐ γ : K ∂(η : Measure K), ‖E p γ‖ ≤ 2 * |M| := by
    filter_upwards [(continuous_fst.tendsto (z, z)).eventually hnear,
      (continuous_snd.tendsto (z, z)).eventually hnear] with p hp hq
    apply Eventually.of_forall
    intro γ
    have h₁ : |n p.1 γ| ≤ M := by
      simpa only [n, Complex.re_add_im] using hM γ p.1.val.re p.1.val.im hp.1 p.1.property hp.2
    have h₂ : |n p.2 γ| ≤ M := by
      simpa only [n, Complex.re_add_im] using hM γ p.2.val.re p.2.val.im hq.1 p.2.property hq.2
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · have ht := abs_sub (n p.1 γ) (n p.2 γ)
      linarith [hInon γ, le_abs_self M]
    · positivity
  have hconv := tendsto_integral_filter_of_dominated_convergence (fun _ : K => 2 * |M|)
    (Eventually.of_forall fun p => (hE p).aestronglyMeasurable) hbound
    (integrable_const _) hlim
  have hconv' : Tendsto (fun p => ∫ γ, E p γ ∂(η : Measure K)) (𝓝 (z, z)) (𝓝 0) := by
    simpa only [integral_zero] using hconv
  have hevent : ∀ᶠ p in 𝓝 (z, z), (∫ γ, E p γ ∂(η : Measure K)) < ε :=
    hconv'.eventually (isOpen_Iio.mem_nhds hε)
  filter_upwards [hevent] with p hp
  have hcomp : |meanGeometricIndex hsch K hKS η p.1 - meanGeometricIndex hsch K hKS η p.2| ≤
      (∫ γ, I γ ∂(η : Measure K)) + ∫ γ, E p γ ∂(η : Measure K) := by
    change |(∫ γ, n p.1 γ ∂(η : Measure K)) - (∫ γ, n p.2 γ ∂(η : Measure K))| ≤ _
    rw [← integral_sub (hn p.1) (hn p.2), ← integral_add hI (hE p)]
    apply abs_integral_le_integral_abs.trans
    apply integral_mono ((hn p.1).sub (hn p.2)).abs (hI.add (hE p))
    intro γ
    dsimp [E]
    linarith [le_max_left (|n p.1 γ - n p.2 γ| - I γ) 0]
  have hmass : (∫ γ, I γ ∂(η : Measure K)) = (η : Measure K).real H :=
    integral_indicator_one hH
  rw [hmass] at hcomp
  change _ < (η : Measure K).real H + ε
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanIndexBands
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary band widths of the actual mean are bounded by point hit
probabilities. This applies after any continuous local lift, including
limits along the physical domain at a collapsed complementary component. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem limsup_sub_liminf_le_of_pair_oscillation
    {X : Type*} (l : Filter X) [NeBot l] (u : X → ℝ) (C : ℝ)
    (hlo : IsBoundedUnder (· ≥ ·) l u) (hhi : IsBoundedUnder (· ≤ ·) l u)
    (hpair : ∀ ε : ℝ, 0 < ε → ∀ᶠ p : X × X in l ×ˢ l, |u p.1 - u p.2| < C + ε) :
    limsup u l - liminf u l ≤ C := by
  by_contra hn
  let ε := (limsup u l - liminf u l - C) / 2
  have hε : 0 < ε := by dsimp [ε] <;> linarith
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp (hpair ε hε)
  have he : ∀ᶠ y in l, limsup u l - C - ε ≤ u y := by
    filter_upwards [hQ] with y hy
    have hb : limsup u l ≤ u y + C + ε := by
      apply limsup_le_of_le hlo.isCoboundedUnder_le
      filter_upwards [hP] with x hx
      have hh := hPQ hx hy
      have ha := le_abs_self (u x - u y)
      linarith
    linarith
  have hl := le_liminf_of_le hhi.isCoboundedUnder_ge he
  dsimp [ε] at hl
  linarith

 theorem meanGeometricIndex_band_width
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    {X : Type*} [TopologicalSpace X] (S : Set X) (s : X) (hs : s ∈ closure S)
    (L : X → ClosedUpperHalfPlane) (hL : ContinuousWithinAt L S s)
    (hz : 0 < (L s).val.im) :
    limsup (fun x => meanGeometricIndex hsch K hKS η (L x)) (𝓝[S] s) -
      liminf (fun x => meanGeometricIndex hsch K hKS η (L x)) (𝓝[S] s) ≤
        (η : Measure K).real {γ | diskRayProjection (L s).val ∈ range γ.val} := by
  let : NeBot (𝓝[S] s) := mem_closure_iff_nhdsWithin_neBot.mp hs
  let u : X → ℝ := fun x => meanGeometricIndex hsch K hKS η (L x)
  let C := (η : Measure K).real {γ | diskRayProjection (L s).val ∈ range γ.val}
  have hbase := meanGeometricIndex_oscillation_le_hit hsch hsep K hK hKS η (L s) hz zero_lt_one
  have hnear : ∀ᶠ x in 𝓝[S] s, |u x - u s| < C + 1 :=
    (hL.prodMk_nhds tendsto_const_nhds).eventually hbase
  have hlo : IsBoundedUnder (· ≥ ·) (𝓝[S] s) u :=
    isBoundedUnder_of_eventually_ge (hnear.mono fun x hx => by
      have hh := (abs_lt.mp hx).1
      exact (show u s - C - 1 ≤ u x by linarith))
  have hhi : IsBoundedUnder (· ≤ ·) (𝓝[S] s) u :=
    isBoundedUnder_of_eventually_le (hnear.mono fun x hx => by
      have hh := (abs_lt.mp hx).2
      exact (show u x ≤ u s + C + 1 by linarith))
  apply limsup_sub_liminf_le_of_pair_oscillation (𝓝[S] s) u C hlo hhi
  intro ε hε
  have hmap := Filter.Tendsto.prodMap
    (show Tendsto L (𝓝[S] s) (𝓝 (L s)) from hL)
    (show Tendsto L (𝓝[S] s) (𝓝 (L s)) from hL)
  rw [← nhds_prod_eq] at hmap
  exact hmap.eventually (meanGeometricIndex_oscillation_le_hit hsch hsep K hK hKS η (L s) hz hε)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MappedMeanBands
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mean-index band bound in the original path law. Injectivity of
the actual Jordan coordinate identifies the hit event exactly. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)]

 theorem mapped_arc_hit_probability_eq
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x})) :
    ((η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure K) : Measure K).real {γ | F x ∈ range γ.val} =
      (η : Measure A).real {γ | x ∈ range γ.val} := by
  have hH : MeasurableSet {γ : K | F x ∈ range γ.val} :=
    (isClosed_paths_hitting (F x)).measurableSet.preimage measurable_subtype_coe
  have he : f ⁻¹' {γ : K | F x ∈ range γ.val} = {γ : A | x ∈ range γ.val} := by
    ext γ
    change F x ∈ range (f γ).val ↔ x ∈ range γ.val
    rw [hmap γ]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, hF γ (Or.inl (mem_range_self t)) (Or.inr (mem_singleton x)) ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, congrArg F ht⟩
  rw [measureReal_def, ProbabilityMeasure.toMeasure_map, Measure.map_apply hf hH, he,
    measureReal_def]

 theorem mapped_meanGeometricIndex_band_width
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x}))
    {Y : Type*} [TopologicalSpace Y] (S : Set Y) (s : Y) (hs : s ∈ closure S)
    (L : Y → ClosedUpperHalfPlane) (hL : ContinuousWithinAt L S s)
    (hz : 0 < (L s).val.im) (hproj : diskRayProjection (L s).val = F x) :
    limsup (fun y => meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L y)) (𝓝[S] s) -
      liminf (fun y => meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L y)) (𝓝[S] s) ≤
        (η : Measure A).real {γ | x ∈ range γ.val} := by
  have hb := meanGeometricIndex_band_width hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) S s hs L hL hz
  rw [hproj, mapped_arc_hit_probability_eq A K η F f hf hmap x hF] at hb
  exact hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LiftedMeanBands
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dust-band estimates for the same local representative used in the
Sobolev construction. The lift only needs nonnegative height on the domain. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem continuous_upperHalfPlaneClamp : Continuous upperHalfPlaneClamp :=
  (Complex.equivRealProdCLM.symm.continuous.comp
    (Complex.continuous_re.prodMk (Complex.continuous_im.max continuous_const))).subtype_mk _

 theorem upperHalfPlaneClamp_val {z : ℂ} (hz : 0 ≤ z.im) :
    (upperHalfPlaneClamp z).val = z :=
  Complex.ext rfl (max_eq_left hz)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSmoothPartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact smooth partition functions on an open planar domain. The
family is locally finite in the domain, allowing accumulation at its boundary. -/

open Set Function Filter TopologicalSpace
open scoped Topology Manifold

noncomputable section

namespace CircleDomainRigidity

theorem exists_openPlanePartition
    (Ω : Opens EuclideanPlane) (U : Ω → Set Ω) (hU : ∀x, U x ∈ 𝓝 x) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : OpenPlanePartition Ω ι) (c : ι → Ω),
      ∀i, tsupport (ρ.weight i) ⊆ Subtype.val '' U (c i) := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  obtain ⟨ι, b, hb⟩ := SmoothBumpCovering.exists_isSubordinate
    (𝓘(ℝ, EuclideanPlane)) (M := Ω) isClosed_univ (fun x _ => hU x)
  let : Encodable ι := b.locallyFinite.encodable (fun i => (b i).nonempty_support)
  let ρ := b.toSmoothPartitionOfUnity
  have hc (i : ι) : HasCompactSupport (ρ i) :=
    (b i).hasCompactSupport.of_isClosed_subset isClosed_closure
      (closure_mono (b.support_toSmoothPartitionOfUnity_subset i))
  let ψ : ι → EuclideanPlane → ℝ := fun i => Subtype.val.extend (ρ i) 0
  have hon (i : ι) (x : Ω) : ψ i x = ρ i x :=
    congrFun (Function.extend_comp Subtype.val_injective (ρ i) 0) x
  have hsub (i : ι) : tsupport (ψ i) ⊆ Subtype.val '' U (b.c i) := by
    apply ((hc i).tsupport_extend_zero_subset continuous_subtype_val).trans
    exact image_mono (hb.toSmoothPartitionOfUnity i)
  have hin (i : ι) : tsupport (ψ i) ⊆ Ω :=
    (hsub i).trans (image_subset_iff.mpr (fun x _ => x.property))
  have hsmooth (i : ι) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) := by
    apply contMDiff_iff_contDiff.mp
    exact ContMDiff.extend_zero (hc i) (ρ i).contMDiff
  have hloc : LocallyFinite (fun i => Subtype.val ⁻¹' Function.support (ψ i) :
      ι → Set Ω) := by
    have heq : (fun i => Subtype.val ⁻¹' Function.support (ψ i) : ι → Set Ω) =
        fun i => Function.support (ρ i) := by
      funext i
      ext x
      simp only [mem_preimage, Function.mem_support, hon]
    rw [heq]
    exact ρ.locallyFinite
  have hn (i : ι) (x : EuclideanPlane) : 0 ≤ ψ i x := by
    by_cases hx : x ∈ Ω
    · rw [show x = ((⟨x, hx⟩ : Ω) : EuclideanPlane) from rfl, hon]
      exact ρ.nonneg i _
    · have hz : ψ i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hin i h))
      rw [hz]
  refine ⟨ι, inferInstance, ⟨ψ, hsmooth,
    fun i => (hc i).extend_zero continuous_subtype_val, hin, hloc, hn, ?_⟩, b.c, hsub⟩
  intro x
  simp only [hon]
  exact ρ.sum_eq_one (mem_univ x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionMixing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth mixing on an open planar domain. The locally finite sum is
represented by an actual finite sum in a neighborhood of each point. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
  (ρ : OpenPlanePartition Ω ι)

theorem point_finite (x : EuclideanPlane) : HasFiniteSupport (fun i => ρ.weight i x) := by
  by_cases hx : x ∈ Ω
  · exact ρ.locallyFinite.point_finite ⟨x, hx⟩
  · have hz : ∀i, ρ.weight i x = 0 := fun i =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (ρ.inside i h))
    change (Function.support (fun i => ρ.weight i x)).Finite
    apply finite_empty.subset
    intro i hi
    exact False.elim (hi (hz i))

theorem mix_mem_Icc (v : ι → EuclideanPlane → ℝ) {x : EuclideanPlane}
    (hx : x ∈ Ω) {a b : ℝ} (hv : ∀i, ρ.weight i x ≠ 0 → v i x ∈ Icc a b) :
    ρ.mix v x ∈ Icc a b := by
  simpa only [mix, smul_eq_mul] using (convex_Icc a b).finsum_mem
    (fun i => ρ.nonneg i x) (ρ.sum_one ⟨x, hx⟩) hv

theorem eventually_finite_weights {x : EuclideanPlane} (hx : x ∈ Ω) :
    ∃s : Finset ι, ∀ᶠ y in 𝓝 x, ∀i ∉ s, ρ.weight i y = 0 := by
  classical
  obtain ⟨T, hT, hfin⟩ := ρ.locallyFinite ⟨x, hx⟩
  refine ⟨hfin.toFinset, ?_⟩
  have hsub : ∀ᶠ y : Ω in 𝓝 ⟨x, hx⟩, ∀i ∉ hfin.toFinset, ρ.weight i y = 0 := by
    filter_upwards [hT] with y hy i hi
    by_contra hn
    apply hi
    exact hfin.mem_toFinset.mpr ⟨y, hn, hy⟩
  have hmap : ∀ᶠ y in Filter.map (Subtype.val : Ω → EuclideanPlane) (𝓝 ⟨x, hx⟩),
      ∀i ∉ hfin.toFinset, ρ.weight i y = 0 := hsub
  have hm : Filter.map (Subtype.val : Ω → EuclideanPlane) (𝓝 (⟨x, hx⟩ : Ω)) = 𝓝 x :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x, hx⟩
  rwa [hm] at hmap

theorem mix_eventually_eq_sum (v : ι → EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ Ω) :
    ∃s : Finset ι, ρ.mix v =ᶠ[𝓝 x] fun y => ∑ i ∈ s, ρ.weight i y * v i y := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  refine ⟨s, hs.mono fun y hy => ?_⟩
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra his
  apply hi
  change ρ.weight i y * v i y = 0
  rw [hy i his, zero_mul]

end OpenPlanePartition

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleLiftTransitions
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous real branches of one circle coordinate differ locally by
a constant integer. Their ordinary derivatives therefore agree. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem circle_lift_difference_eventually_constant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {u v : E → ℝ}
    (hu : ContinuousOn u U) (hv : ContinuousOn v U)
    (he : ∀ x ∈ U, (u x : UnitAddCircle) = (v x : UnitAddCircle))
    {x : E} (hx : x ∈ U) :
    (fun y => u y - v y) =ᶠ[𝓝 x] (fun _ => u x - v x) := by
  let a := u x - v x - 1 / 2
  have hmem : u x - v x ∈ Ioo a (a + 1) := by dsimp [a]; constructor <;> linarith
  have hnear := ((hu.sub hv).continuousAt (hU.mem_nhds hx)).eventually
    (isOpen_Ioo.mem_nhds hmem)
  filter_upwards [hU.mem_nhds hx, hnear] with y hy hyI
  have hmod : ((u y - v y : ℝ) : UnitAddCircle) = ((u x - v x : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_sub, he y hy, sub_self, AddCircle.coe_sub, he x hx, sub_self]
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hyI)
    (Ioo_subset_Ico_self hmem)).mp hmod

 theorem circle_lift_difference_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {u v : E → ℝ}
    (hu : ContinuousOn u U) (hv : ContinuousOn v U)
    (he : ∀ x ∈ U, (u x : UnitAddCircle) = (v x : UnitAddCircle))
    {x : E} (hx : x ∈ U) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => u y - v y) x :=
  contDiffAt_const.congr_of_eventuallyEq
    (circle_lift_difference_eventually_constant hU hu hv he hx)

 theorem contDiffAt_circle_quotient_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ (⊤ : ℕ∞) u x)
    (a : ℝ) (ha : (u x : UnitAddCircle) ≠ (a : UnitAddCircle)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => (AddCircle.equivIco (1 : ℝ) a (u y : UnitAddCircle) : ℝ)) x := by
  have hmod : ¬ u x ≡ a [PMOD (1 : ℝ)] := AddCommGroup.not_modEq_iff_ne_mod_zmultiples.mpr ha
  have hconst := (eventuallyEq_toIcoDiv_nhds (by norm_num : (0 : ℝ) < 1) a hmod).comp_tendsto
    hu.continuousAt
  have heq : (fun y => (AddCircle.equivIco (1 : ℝ) a (u y : UnitAddCircle) : ℝ))
      =ᶠ[𝓝 x] (fun y => u y - (toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u x) : ℝ)) := by
    filter_upwards [hconst] with y hy
    change toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u y) =
      toIcoDiv (by norm_num : (0 : ℝ) < 1) a (u x) at hy
    change toIcoMod (by norm_num : (0 : ℝ) < 1) a (u y) = _
    simp only [toIcoMod, hy, zsmul_eq_mul, mul_one]
  exact (hu.sub contDiffAt_const).congr_of_eventuallyEq heq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CirclePartitionSmoothing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gluing smooth approximants to continuous real circle branches. The
integer transition functions cancel in the partition sum. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

namespace OpenPlanePartition
variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

 theorem mix_add_scalar (v : ι → EuclideanPlane → ℝ) (c : EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ Ω) :
    ρ.mix (fun i y => v i y + c y) x = ρ.mix v x + c x := by
  classical
  let s := (ρ.point_finite x).toFinset
  have hz (i : ι) (hi : i ∉ s) : ρ.weight i x = 0 := by
    by_contra h
    exact hi ((ρ.point_finite x).mem_toFinset.mpr h)
  have hs (f : ι → ℝ) : (∑ᶠ i, ρ.weight i x * f i) = ∑ i ∈ s, ρ.weight i x * f i := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra his
    apply hi
    change ρ.weight i x * f i = 0
    rw [hz i his, zero_mul]
  have hone : (∑ i ∈ s, ρ.weight i x) = 1 := by
    have hh := hs (fun _ => 1)
    simp only [mul_one] at hh
    exact hh.symm.trans (ρ.sum_one ⟨x, hx⟩)
  change (∑ᶠ i, ρ.weight i x * (v i x + c x)) = (∑ᶠ i, ρ.weight i x * v i x) + c x
  rw [hs (fun i => v i x + c x), hs (fun i => v i x)]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hone, one_mul]

 theorem circleMix_smooth
    (W : ι → Set EuclideanPlane) (hW : ∀ i, IsOpen (W i))
    (hsub : ∀ i, tsupport (ρ.weight i) ⊆ W i)
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ i, ContinuousOn (u i) (W i))
    (hlift : ∀ i x, x ∈ W i → (u i x : UnitAddCircle) = f x)
    (hv : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (v i)) :
    SmoothCircleOn (ρ.circleMix f u v) Ω := by
  classical
  intro x hx a ha
  have hj : ∃ j, ρ.weight j x ≠ 0 := by
    by_contra hn
    have hz : ∀ j, ρ.weight j x = 0 := fun j => not_not.mp (fun h => hn ⟨j, h⟩)
    have hh := ρ.sum_one ⟨x, hx⟩
    simp only [hz, finsum_zero] at hh
    norm_num at hh
  obtain ⟨j, hj⟩ := hj
  have hxj : x ∈ W j := hsub j (subset_tsupport (ρ.weight j) hj)
  let r : ι → EuclideanPlane → ℝ := fun i y => v i y + (u j y - u i y)
  have hterm (i : ι) : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ρ.weight i y * r i y) x := by
    by_cases hi : x ∈ tsupport (ρ.weight i)
    · have hxi := hsub i hi
      have ht := circle_lift_difference_contDiffAt ((hW j).inter (hW i))
        ((hu j).mono inter_subset_left) ((hu i).mono inter_subset_right)
        (fun y hy => (hlift j y hy.1).trans (hlift i y hy.2).symm) ⟨hxj, hxi⟩
      exact (ρ.smooth i).contDiffAt.mul ((hv i).contDiffAt.add ht)
    · have hz : (fun y => ρ.weight i y * r i y) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport (ρ.weight i)).isOpen_compl.mem_nhds hi] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  obtain ⟨s, hs⟩ := ρ.mix_eventually_eq_sum r hx
  have hr : ContDiffAt ℝ (⊤ : ℕ∞) (ρ.mix r) x :=
    (ContDiffAt.sum (fun i _ => hterm i)).congr_of_eventuallyEq hs
  have he : ρ.circleMix f u v =ᶠ[𝓝 x] (fun y => (ρ.mix r y : UnitAddCircle)) := by
    filter_upwards [Ω.isOpen.mem_nhds hx, (hW j).mem_nhds hxj] with y hyΩ hyj
    rw [circleMix, ← hlift j y hyj, ← AddCircle.coe_add]
    congr 1
    have hm := ρ.mix_add_scalar (fun i y => v i y - u i y) (u j) hyΩ
    have hre : r = fun i y => (v i y - u i y) + u j y := by
      funext i y
      dsimp [r]
      ring
    rw [hre, hm, add_comm]
  have hne : (ρ.mix r x : UnitAddCircle) ≠ (a : UnitAddCircle) := he.eq_of_nhds ▸ ha
  have hchart := contDiffAt_circle_quotient_chart hr a hne
  exact hchart.congr_of_eventuallyEq (he.mono fun y hy => congrArg
    (fun z => (AddCircle.equivIco (1 : ℝ) a z : ℝ)) hy)

 theorem mix_sub_continuousOn
    (W : ι → Set EuclideanPlane) (hW : ∀ i, IsOpen (W i))
    (hsub : ∀ i, tsupport (ρ.weight i) ⊆ W i)
    (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ i, ContinuousOn (u i) (W i)) (hv : ∀ i, Continuous (v i)) :
    ContinuousOn (ρ.mix (fun i y => v i y - u i y)) Ω := by
  intro x hx
  have hterm (i : ι) : ContinuousAt (fun y => ρ.weight i y * (v i y - u i y)) x := by
    by_cases hi : x ∈ tsupport (ρ.weight i)
    · exact (ρ.smooth i).continuous.continuousAt.mul
        ((hv i).continuousAt.sub ((hu i).continuousAt ((hW i).mem_nhds (hsub i hi))))
    · have hz : (fun y => ρ.weight i y * (v i y - u i y)) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport (ρ.weight i)).isOpen_compl.mem_nhds hi] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      exact continuousAt_const.congr_of_eventuallyEq hz
  obtain ⟨s, hs⟩ := ρ.mix_eventually_eq_sum (fun i y => v i y - u i y) hx
  have hsum : ContinuousAt (fun y => ∑ i ∈ s, ρ.weight i y * (v i y - u i y)) x := by
    classical
    clear hs
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (continuousAt_const : ContinuousAt (fun _ : EuclideanPlane => (0 : ℝ)) x)
    | @insert i s hi ih =>
        have hh : ContinuousAt (fun y => ρ.weight i y * (v i y - u i y) +
            ∑ k ∈ s, ρ.weight k y * (v k y - u k y)) x := (hterm i).add ih
        simpa only [Finset.sum_insert hi] using hh
  exact (hsum.congr_of_eventuallyEq hs).continuousWithinAt

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CirclePartitionBands
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive smoothing of local circle branches preserves the limiting
bands in every comparison branch. Connected sampling patches fix the
integer transition before averaging. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

 theorem circleMix_eq_adjusted
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (w : EuclideanPlane → ℝ) {x : EuclideanPlane} (hx : x ∈ Ω)
    (hw : (w x : UnitAddCircle) = f x) :
    ρ.circleMix f u v x = (ρ.adjustedCircleMix u v w x : UnitAddCircle) := by
  rw [circleMix, ← hw, ← AddCircle.coe_add]
  congr 1
  have hm := ρ.mix_add_scalar (fun i y => v i y - u i y) w hx
  have he : (fun i y => v i y + (w y - u i y)) = fun i y => (v i y - u i y) + w y := by
    funext i y
    ring
  rw [adjustedCircleMix, he, hm, add_comm]

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocallyFiniteL2Sum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L² control of a pointwise finite sum by the sum of its local error
norms. This applies to the countable partition-of-unity error terms. -/

open Set Filter MeasureTheory Function
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem finiteSupport_hasSum_finsum {ι : Type*} (f : ι → ℝ)
    (hf : HasFiniteSupport f) : HasSum f (∑ᶠ i, f i) := by
  rw [← show (∑' i, f i) = ∑ᶠ i, f i from tsum_eq_finsum hf]
  exact (summable_of_hasFiniteSupport hf).hasSum

theorem aestronglyMeasurable_finsum_of_pointFinite
    {ι : Type*} [Countable ι] (μ : Measure EuclideanPlane)
    (f : ι → EuclideanPlane → ℝ) (hf : ∀i, AEStronglyMeasurable (f i) μ)
    (hfin : ∀x, HasFiniteSupport (fun i => f i x)) :
    AEStronglyMeasurable (fun x => ∑ᶠ i, f i x) μ := by
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
    (f := fun s x => ∑ i ∈ s, f i x)
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s (fun i _ => hf i)
  · exact Eventually.of_forall fun x => finiteSupport_hasSum_finsum _ (hfin x)

theorem eLpNorm_finsum_le_tsum_of_pointFinite
    {ι : Type*} [Countable ι] (μ : Measure EuclideanPlane)
    (f : ι → EuclideanPlane → ℝ) (hf : ∀i, AEStronglyMeasurable (f i) μ)
    (hfin : ∀x, HasFiniteSupport (fun i => f i x)) :
    eLpNorm (fun x => ∑ᶠ i, f i x) 2 μ ≤ ∑' i, eLpNorm (f i) 2 μ := by
  apply Lp.eLpNorm_le_of_ae_tendsto
    (u := (atTop : Filter (Finset ι)))
    (f := fun s x => ∑ i ∈ s, f i x)
  · apply Eventually.of_forall
    intro s
    have h := eLpNorm_sum_le (hfs := fun _ _ => by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (f := f) (s := s) (μ := μ) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have he : (fun x => ∑ i ∈ s, f i x) = ∑i ∈ s, f i := by
      ext x
      simp only [Finset.sum_apply]
    rw [he]
    exact h.trans (ENNReal.sum_le_tsum s)
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s (fun i _ => hf i)
  · exact Eventually.of_forall fun x => finiteSupport_hasSum_finsum _ (hfin x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PositiveMollification
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized smooth mollifiers preserve actual interval bounds and
constant plateaus. These are pointwise bounds on the input neighborhood. -/

open Set MeasureTheory Metric
open scoped Convolution

noncomputable section

namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem normed_convolution_eq_of_constant
    [HasContDiffBump E] (β : ContDiffBump (0 : E)) {u : E → ℝ} {x : E} {c : ℝ}
    (hc : ∀y ∈ ball x β.rOut, u y = c) :
    ((β.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x) = c := by
  rw [β.normed_convolution_eq_right (fun y hy => (hc y hy).trans
    (hc x (mem_ball_self β.rOut_pos)).symm)]
  exact hc x (mem_ball_self β.rOut_pos)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PositiveSobolevApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit positive mollification of a compactly supported planar
Sobolev function. The values and weak derivatives converge in L². -/

open Set Filter MeasureTheory
open scoped ENNReal Topology Convolution

noncomputable section

namespace CircleDomainRigidity

theorem planarMollification_tsupport_subset (u : EuclideanPlane → ℝ) (n : ℕ) :
    tsupport (planarMollification u n) ⊆
      Metric.cthickening (DeGiorgi.shrinkingBump (d := 2) n).rOut (tsupport u) := by
  have hs := support_convolution_subset
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (f := (DeGiorgi.shrinkingBump (d := 2) n).normed volume) (g := u)
  apply closure_minimal (hs.trans ?_) Metric.isClosed_cthickening
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx
  rw [(DeGiorgi.shrinkingBump (d := 2) n).support_normed_eq] at ha
  have ha' : ‖a‖ < (DeGiorgi.shrinkingBump (d := 2) n).rOut := by
    simpa only [Metric.mem_ball, dist_zero_right] using ha
  apply Metric.mem_cthickening_of_dist_le (x := a + b) (y := b)
    (δ := (DeGiorgi.shrinkingBump (d := 2) n).rOut) (tsupport u)
    (subset_tsupport u hb)
  simpa only [dist_eq_norm, add_sub_cancel_right] using ha'.le

theorem planarMollification_support_eventually {u : EuclideanPlane → ℝ}
    (hu : HasCompactSupport u) {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    (hsub : tsupport u ⊆ Ω) : ∀ᶠ n in atTop, tsupport (planarMollification u n) ⊆ Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hu.isCompact.exists_cthickening_subset_open hΩ hsub
  have hr : ∀ᶠ n in atTop, (DeGiorgi.shrinkingBump (d := 2) n).rOut < δ :=
    (tendsto_order.1 tendsto_planarMollifier_radius).2 δ hδ
  filter_upwards [hr] with n hn
  exact (planarMollification_tsupport_subset u n).trans
      ((Metric.cthickening_mono hn.le _).trans hδΩ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactMollifierSampling
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform sampling control on compact sets, including exact preservation
of constant regions and smooth cutoffs equal to one near a compact set. -/

open Set Filter MeasureTheory Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem planarMollifier_samples_eventually
    {K V : Set EuclideanPlane} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∀ᶠ n in atTop, ∀x ∈ K,
      ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut ⊆ V := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  have hr : ∀ᶠ n in atTop, (DeGiorgi.shrinkingBump (d := 2) n).rOut < δ :=
    (tendsto_order.1 tendsto_planarMollifier_radius).2 δ hδ
  filter_upwards [hr] with n hn x hx y hy
  apply hδV
  exact mem_cthickening_of_dist_le y x δ K hx
    ((mem_ball.1 hy).le.trans hn.le)

theorem planarMollification_eq_on_compact_eventually
    {u : EuclideanPlane → ℝ} {K V : Set EuclideanPlane}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    {c : ℝ} (hc : ∀y ∈ V, u y = c) :
    ∀ᶠ n in atTop, ∀x ∈ K, planarMollification u n x = c := by
  filter_upwards [planarMollifier_samples_eventually hK hV hKV] with n hn x hx
  exact normed_convolution_eq_of_constant volume (DeGiorgi.shrinkingBump n)
    (fun y hy => hc y (hn x hx hy))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevSmoothing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local positive smoothing with errors relative to the original weak
gradient. Compact cutoffs are removed on a neighborhood of the core. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem tendsto_eLpNorm_restrict_zero
    {f : ℕ → EuclideanPlane → ℝ} {V : Set EuclideanPlane}
    (hf : Tendsto (fun n => eLpNorm (f n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict V)) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf
    (fun _ => bot_le) (fun n => eLpNorm_mono_measure (f n) Measure.restrict_le_self)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedSobolevErrors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative error estimates for multiplying local Sobolev
approximations by smooth partition functions. -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem aestronglyMeasurable_mul_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f ψ : EuclideanPlane → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V))
    (hψ : Continuous ψ) (hs : Function.support ψ ⊆ V) :
    AEStronglyMeasurable (fun x => ψ x * f x) volume := by
  have hi : V.indicator (fun x => ψ x * f x) = fun x => ψ x * f x := by
    funext x
    by_cases hx : x ∈ V
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, Function.notMem_support.mp (fun h => hx (hs h)), zero_mul]
  rw [← hi]
  exact (aestronglyMeasurable_indicator_iff hV).2 (hψ.aestronglyMeasurable.restrict.mul hf)

theorem eLpNorm_mul_le_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f ψ : EuclideanPlane → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V))
    (hψ : Continuous ψ) {C : ℝ≥0} (hC : ∀x, ‖ψ x‖ ≤ C)
    (hs : Function.support ψ ⊆ V) :
    eLpNorm (fun x => ψ x * f x) 2 volume ≤ C * eLpNorm f 2 (volume.restrict V) := by
  have hi : V.indicator (fun x => ψ x * f x) = fun x => ψ x * f x := by
    funext x
    by_cases hx : x ∈ V
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, Function.notMem_support.mp (fun h => hx (hs h)), zero_mul]
  rw [← hi, eLpNorm_indicator_eq_eLpNorm_restrict hV]
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
  exact Eventually.of_forall fun x => by
    have hnn : ‖ψ x‖₊ ≤ C := by exact_mod_cast hC x
    simpa only [Pi.mul_apply, nnnorm_mul] using mul_le_mul' hnn (le_refl ‖f x‖₊)

theorem tendsto_eLpNorm_mul_zero_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f : ℕ → EuclideanPlane → ℝ} (hf : ∀n, AEStronglyMeasurable (f n) (volume.restrict V))
    {ψ : EuclideanPlane → ℝ} (hψ : Continuous ψ) (hsψ : HasCompactSupport ψ)
    (hs : Function.support ψ ⊆ V)
    (hlim : Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict V)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => ψ x * f n x) 2 volume) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := hψ.bounded_above_of_compact_support hsψ
  let C : ℝ≥0 := ⟨max A 0, le_max_right _ _⟩
  have hC : ∀x, ‖ψ x‖ ≤ C := fun x => (hA x).trans (le_max_left _ _)
  have hl : Tendsto (fun n => (C : ℝ≥0∞) * eLpNorm (f n) 2 (volume.restrict V))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => bot_le) (fun n => eLpNorm_mul_le_of_support hV (hf n) hψ hC hs)

theorem tendsto_partition_derivative_error
    {V : Set EuclideanPlane} (hV : IsOpen V)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u V)
    {φ : ℕ → EuclideanPlane → ℝ} (hφ : ∀n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hv : Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (volume.restrict V))
      atTop (𝓝 0))
    (hg : ∀i : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
      (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
      2 (volume.restrict V)) atTop (𝓝 0))
    {ψ : EuclideanPlane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsψ : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ V) (i : Fin 2) :
    Tendsto (fun n => eLpNorm (fun x =>
      ψ x * ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i) +
      (fderiv ℝ ψ x) (EuclideanSpace.single i 1) * (φ n x - u x)) 2 volume)
      atTop (𝓝 0) := by
  let dψ : EuclideanPlane → ℝ := fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)
  have hdψ : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsdψ : HasCompactSupport dψ := hsψ.fderiv_apply (𝕜 := ℝ) _
  have hsubdψ : Function.support dψ ⊆ V :=
    (subset_tsupport dψ).trans ((tsupport_fderiv_apply_subset ℝ _).trans hsub)
  have hv' := tendsto_eLpNorm_mul_zero_of_support hV.measurableSet
    (fun n => (hφ n).continuous.aestronglyMeasurable.restrict.sub hu.memLp.aestronglyMeasurable)
    hdψ hsdψ hsubdψ hv
  have hg' := tendsto_eLpNorm_mul_zero_of_support hV.measurableSet
    (fun n => ((hφ n).continuous_fderiv (by simp)).clm_apply continuous_const
      |>.aestronglyMeasurable.restrict.sub (hu.weakGrad_component_memLp i).aestronglyMeasurable)
    hψ.continuous hsψ ((subset_tsupport ψ).trans hsub) (hg i)
  have hl := hg'.add hv'
  simp only [zero_add] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => bot_le)
  intro n
  have key : ∀ {a b : EuclideanPlane → ℝ}, Function.support a ⊆ V → Continuous a →
      AEStronglyMeasurable b (volume.restrict V) → AEStronglyMeasurable (fun x => a x * b x) volume := by
    intro a b ha hac hb
    have he : (fun x => a x * b x) = V.indicator (fun x => a x * b x) := by
      funext x
      by_cases hx : x ∈ V
      · simp [hx]
      · have : a x = 0 := Function.notMem_support.mp (fun h => hx (ha h))
        simp [hx, this]
    rw [he]
    exact (aestronglyMeasurable_indicator_iff hV.measurableSet).mpr
      (hac.aestronglyMeasurable.restrict.mul hb)
  exact eLpNorm_add_le
    (key ((subset_tsupport ψ).trans hsub) hψ.continuous
      (((hφ n).continuous_fderiv (by simp)).clm_apply continuous_const
        |>.aestronglyMeasurable.restrict.sub (hu.weakGrad_component_memLp i).aestronglyMeasurable))
    (key hsubdψ hdψ ((hφ n).continuous.aestronglyMeasurable.restrict.sub hu.memLp.aestronglyMeasurable))
    (by norm_num)
theorem aestronglyMeasurable_partition_derivative_error
    {V : Set EuclideanPlane} (hV : IsOpen V)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u V)
    {v ψ : EuclideanPlane → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hsub : tsupport ψ ⊆ V) (i : Fin 2) :
    AEStronglyMeasurable (fun x =>
      ψ x * ((fderiv ℝ v x) (EuclideanSpace.single i 1) - hu.weakGrad x i) +
      (fderiv ℝ ψ x) (EuclideanSpace.single i 1) * (v x - u x)) volume := by
  have hdv : Continuous (fun x => (fderiv ℝ v x) (EuclideanSpace.single i 1)) :=
    (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ : Continuous (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (aestronglyMeasurable_mul_of_support hV.measurableSet
    (hdv.aestronglyMeasurable.restrict.sub (hu.weakGrad_component_memLp i).aestronglyMeasurable)
    hψ.continuous ((subset_tsupport ψ).trans hsub)).add
      (aestronglyMeasurable_mul_of_support hV.measurableSet
        (hv.continuous.aestronglyMeasurable.restrict.sub hu.memLp.aestronglyMeasurable)
        hdψ ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ _).trans hsub)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionGradientIdentity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The total selected error is the derivative of the smooth partition
sum minus the corresponding partition of local weak gradients. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
  (ρ : OpenPlanePartition Ω ι)

theorem finite_weights_and_derivatives {x : EuclideanPlane} (hx : x ∈ Ω) :
    ∃s : Finset ι,
      (∀j ∉ s, ρ.weight j x = 0 ∧ fderiv ℝ (ρ.weight j) x = 0) ∧
      (ρ.mix (fun _ _ => 1) =ᶠ[𝓝 x] fun y => ∑j ∈ s, ρ.weight j y) ∧
      (∑j ∈ s, ρ.weight j x) = 1 ∧ (∑j ∈ s, fderiv ℝ (ρ.weight j) x) = 0 := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  have heq : ρ.mix (fun _ _ => 1) =ᶠ[𝓝 x] fun y => ∑j ∈ s, ρ.weight j y := by
    filter_upwards [hs] with y hy
    simp only [mix, mul_one]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    exact hj (hy j hjs)
  have hone : (fun y => ∑j ∈ s, ρ.weight j y) =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [hs, Ω.isOpen.mem_nhds hx] with y hy hyΩ
    rw [← ρ.sum_one ⟨y, hyΩ⟩]
    symm
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    exact hj (hy j hjs)
  refine ⟨s, ?_, heq, hone.eq_of_nhds, ?_⟩
  · intro j hj
    have hz : ρ.weight j =ᶠ[𝓝 x] (fun _ => 0) := hs.mono fun _ hy => hy j hj
    refine ⟨hz.eq_of_nhds, ?_⟩
    rw [hz.fderiv_eq]
    exact fderiv_const_apply 0
  · calc
      _ = fderiv ℝ (fun y => ∑j ∈ s, ρ.weight j y) x :=
        (fderiv_fun_sum (fun j _ => (ρ.smooth j).differentiable (by simp) x)).symm
      _ = fderiv ℝ (fun _ : EuclideanPlane => (1 : ℝ)) x := hone.fderiv_eq
      _ = 0 := fderiv_const_apply 1

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionGradientBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive partition preserves a common pointwise bound on local
weak-gradient components, and hence their common L² bound. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem partition_component_pointFinite
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (G : ι → EuclideanPlane → ℝ) (x : EuclideanPlane) :
    HasFiniteSupport (fun j => ρ.weight j x * G j x) := by
  apply (ρ.point_finite x).subset
  intro j hj
  by_contra hn
  apply hj
  change ρ.weight j x * G j x = 0
  rw [show ρ.weight j x = 0 from not_not.mp hn, zero_mul]

theorem partition_component_aestronglyMeasurable
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ)
    (hG : ∀j, AEStronglyMeasurable (G j) (volume.restrict (W j))) :
    AEStronglyMeasurable (fun x => ∑ᶠ j, ρ.weight j x * G j x) volume := by
  exact aestronglyMeasurable_finsum_of_pointFinite volume _
    (fun j => aestronglyMeasurable_mul_of_support (hW j) (hG j) (ρ.smooth j).continuous
      ((subset_tsupport (ρ.weight j)).trans (hsub j)))
    (partition_component_pointFinite ρ G)

theorem partition_component_bound
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ) (g : EuclideanPlane → ℝ)
    (hG : ∀j, ∀ᵐ x ∂volume.restrict (W j), |G j x| ≤ g x) :
    ∀ᵐ x ∂volume.restrict Ω, |∑ᶠ j, ρ.weight j x * G j x| ≤ g x := by
  have hglobal : ∀ᵐ x ∂(volume : Measure EuclideanPlane), ∀j, x ∈ W j → |G j x| ≤ g x :=
    ae_all_iff.mpr (fun j => (ae_restrict_iff' (hW j)).1 (hG j))
  filter_upwards [ae_restrict_of_ae hglobal, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  have hb : (∑ᶠ j, ρ.weight j x * G j x) ∈ Icc (-g x) (g x) := by
    simpa only [smul_eq_mul] using (convex_Icc (-g x) (g x)).finsum_mem
      (fun j => ρ.nonneg j x) (ρ.sum_one ⟨x, hxΩ⟩)
      (fun j hj => abs_le.mp (hx j (hsub j (subset_tsupport (ρ.weight j) hj))))
  exact abs_le.mpr hb

theorem partition_component_memLp
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ)
    (hGm : ∀j, AEStronglyMeasurable (G j) (volume.restrict (W j)))
    {g : EuclideanPlane → ℝ} (hg : MemLp g 2 (volume.restrict Ω))
    (hG : ∀j, ∀ᵐ x ∂volume.restrict (W j), |G j x| ≤ g x) :
    MemLp (fun x => ∑ᶠ j, ρ.weight j x * G j x) 2 (volume.restrict Ω) := by
  apply hg.of_le (partition_component_aestronglyMeasurable ρ W hW hsub G hGm).restrict
  filter_upwards [partition_component_bound ρ W hW hsub G g hG] with x hx
  simpa only [Real.norm_eq_abs] using hx.trans (le_abs_self (g x))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionLocalDerivatives
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivatives of a partition sum require smoothness only of its
weighted local terms, as needed for different real circle branches. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

 theorem mix_fderiv_of_products (v : ι → EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ Ω)
    (hv : ∀ i, DifferentiableAt ℝ (fun y => ρ.weight i y * v i y) x) :
    fderiv ℝ (ρ.mix v) x = ∑ᶠ i, fderiv ℝ (fun y => ρ.weight i y * v i y) x := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  have he : ρ.mix v =ᶠ[𝓝 x] fun y => ∑ i ∈ s, ρ.weight i y * v i y := by
    filter_upwards [hs] with y hy
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra his
    apply hi
    change ρ.weight i y * v i y = 0
    rw [hy i his, zero_mul]
  rw [he.fderiv_eq, fderiv_fun_sum (fun i _ => hv i)]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra his
  apply hi
  change fderiv ℝ (fun y => ρ.weight i y * v i y) x = 0
  have hz : (fun y => ρ.weight i y * v i y) =ᶠ[𝓝 x] (fun _ => 0) :=
    hs.mono fun y hy => by
      change ρ.weight i y * v i y = 0
      rw [hy i his, zero_mul]
  rw [hz.fderiv_eq]
  exact fderiv_const_apply 0

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CirclePartitionGradient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative of every local branch of the smoothed circle map.
The integer transition derivatives vanish and the partition derivatives
sum to zero, leaving one global scalar derivative expression. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

 theorem adjustedCircleMix_contDiffAt
    (W : ι → Set EuclideanPlane) (hW : ∀ k, IsOpen (W k))
    (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ k, ContinuousOn (u k) (W k))
    (hlift : ∀ k y, y ∈ W k → (u k y : UnitAddCircle) = f y)
    (hv : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (v k))
    (j : ι) {x : EuclideanPlane} (hx : x ∈ Ω) (hxj : x ∈ W j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (ρ.adjustedCircleMix u v (u j)) x := by
  classical
  let r : ι → EuclideanPlane → ℝ := fun k y => v k y + (u j y - u k y)
  have hterm (k : ι) : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ρ.weight k y * r k y) x := by
    by_cases hk : x ∈ tsupport (ρ.weight k)
    · have ht := circle_lift_difference_contDiffAt ((hW j).inter (hW k))
        ((hu j).mono inter_subset_left) ((hu k).mono inter_subset_right)
        (fun y hy => (hlift j y hy.1).trans (hlift k y hy.2).symm) ⟨hxj, hsub k hk⟩
      exact (ρ.smooth k).contDiffAt.mul ((hv k).contDiffAt.add ht)
    · have hz : (fun y => ρ.weight k y * r k y) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport (ρ.weight k)).isOpen_compl.mem_nhds hk] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  obtain ⟨s, hs⟩ := ρ.mix_eventually_eq_sum r hx
  exact (ContDiffAt.sum (fun k _ => hterm k)).congr_of_eventuallyEq hs

 theorem adjustedCircleMix_derivative
    (W : ι → Set EuclideanPlane) (hW : ∀ k, IsOpen (W k))
    (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ k, ContinuousOn (u k) (W k))
    (hlift : ∀ k y, y ∈ W k → (u k y : UnitAddCircle) = f y)
    (hv : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (v k))
    (j : ι) {x : EuclideanPlane} (hx : x ∈ Ω) (hxj : x ∈ W j) (i : Fin 2) :
    (fderiv ℝ (ρ.adjustedCircleMix u v (u j)) x) (EuclideanSpace.single i 1) =
      ∑ᶠ k, (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
        (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x)) := by
  classical
  let r : ι → EuclideanPlane → ℝ := fun k y => v k y + (u j y - u k y)
  have hp (k : ι) :
      DifferentiableAt ℝ (fun y => ρ.weight k y * r k y) x ∧
      (fderiv ℝ (fun y => ρ.weight k y * r k y) x) (EuclideanSpace.single i 1) =
        ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
          (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * r k x := by
    by_cases hk : x ∈ tsupport (ρ.weight k)
    · have hxk := hsub k hk
      have ht := circle_lift_difference_eventually_constant ((hW j).inter (hW k))
        ((hu j).mono inter_subset_left) ((hu k).mono inter_subset_right)
        (fun y hy => (hlift j y hy.1).trans (hlift k y hy.2).symm) ⟨hxj, hxk⟩
      have hdiff : DifferentiableAt ℝ (fun y => u j y - u k y) x :=
        ((show ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : EuclideanPlane => u j x - u k x) x from
          contDiffAt_const).congr_of_eventuallyEq ht).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      have hd : fderiv ℝ (fun y => u j y - u k y) x = 0 := by
        rw [ht.fderiv_eq]
        exact fderiv_const_apply _
      have hrv : DifferentiableAt ℝ (r k) x := ((hv k).differentiable (by simp) x).add hdiff
      refine ⟨((ρ.smooth k).differentiable (by simp) x).mul hrv, ?_⟩
      rw [fderiv_fun_mul ((ρ.smooth k).differentiable (by simp) x) hrv]
      change ((ρ.weight k x) • fderiv ℝ (fun y => v k y + (u j y - u k y)) x +
        r k x • fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) = _
      rw [fderiv_fun_add ((hv k).differentiable (by simp) x) hdiff, hd, add_zero]
      simp only [add_apply, smul_apply, smul_eq_mul, mul_comm (r k x)]
    · have hz : (fun y => ρ.weight k y * r k y) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport (ρ.weight k)).isOpen_compl.mem_nhds hk] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      refine ⟨((show ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : EuclideanPlane => (0 : ℝ)) x from
        contDiffAt_const).congr_of_eventuallyEq hz).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), ?_⟩
      rw [hz.fderiv_eq, fderiv_const_apply, image_eq_zero_of_notMem_tsupport hk,
        fderiv_of_notMem_tsupport ℝ hk]
      simp
  obtain ⟨s, hs, _, _, hd⟩ := ρ.finite_weights_and_derivatives hx
  have hleft : (∑ᶠ k, fderiv ℝ (fun y => ρ.weight k y * r k y) x) =
      ∑ k ∈ s, fderiv ℝ (fun y => ρ.weight k y * r k y) x := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hks
    apply hk
    change fderiv ℝ (fun y => ρ.weight k y * r k y) x = 0
    have hw : ρ.weight k x = 0 := (hs k hks).1
    have hdw : fderiv ℝ (ρ.weight k) x = 0 := (hs k hks).2
    by_cases ht : x ∈ tsupport (ρ.weight k)
    · have hxk := hsub k ht
      have hdiff := circle_lift_difference_contDiffAt ((hW j).inter (hW k))
        ((hu j).mono inter_subset_left) ((hu k).mono inter_subset_right)
        (fun y hy => (hlift j y hy.1).trans (hlift k y hy.2).symm) ⟨hxj, hxk⟩
      have hr := (hv k).contDiffAt.add hdiff
      rw [fderiv_fun_mul ((ρ.smooth k).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)
        (hr.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)), hw, hdw]
      simp
    · have hzero : (fun y => ρ.weight k y * r k y) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport (ρ.weight k)).isOpen_compl.mem_nhds ht] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      rw [hzero.fderiv_eq]
      exact fderiv_const_apply 0
  have hright : (∑ᶠ k, (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
      (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x))) =
      ∑ k ∈ s, (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
        (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x)) := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hks
    apply hk
    simp only [(hs k hks).1, (hs k hks).2, zero_apply, zero_mul, zero_add]
  have hd' : (∑ k ∈ s, (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1)) = 0 := by
    simpa only [sum_apply, zero_apply] using
      congrArg (fun A : EuclideanPlane →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) hd
  change (fderiv ℝ (ρ.mix r) x) _ = _
  rw [ρ.mix_fderiv_of_products r hx (fun k => (hp k).1), hleft, hright]
  simp only [sum_apply]
  have heq (k : ι) :
      (fderiv ℝ (fun y => ρ.weight k y * r k y) x) (EuclideanSpace.single i 1) =
        (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
          (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x)) +
        (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * u j x := by
    rw [(hp k).2]
    dsimp [r]
    ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hd', zero_mul, add_zero]

 theorem circleMix_derivative
    (W : ι → Set EuclideanPlane) (hW : ∀ k, IsOpen (W k))
    (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ k, ContinuousOn (u k) (W k))
    (hlift : ∀ k y, y ∈ W k → (u k y : UnitAddCircle) = f y)
    (hv : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (v k))
    {x : EuclideanPlane} (hx : x ∈ Ω) (i : Fin 2) :
    FiniteTransfer.circleFDeriv (ρ.circleMix f u v) x (EuclideanSpace.single i 1) =
      ∑ᶠ k, (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
        (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x)) := by
  classical
  have hj : ∃ j, ρ.weight j x ≠ 0 := by
    by_contra hn
    have hz : ∀ j, ρ.weight j x = 0 := fun j => not_not.mp (fun h => hn ⟨j, h⟩)
    have hh := ρ.sum_one ⟨x, hx⟩
    simp only [hz, finsum_zero] at hh
    norm_num at hh
  obtain ⟨j, hj⟩ := hj
  have hxj := hsub j (subset_tsupport (ρ.weight j) hj)
  have hsm := ρ.circleMix_smooth W hW hsub f u v hu hlift hv
  have hr := ρ.adjustedCircleMix_contDiffAt W hW hsub f u v hu hlift hv j hx hxj
  have he : (fun y => (ρ.adjustedCircleMix u v (u j) y : UnitAddCircle))
      =ᶠ[𝓝 x] ρ.circleMix f u v := by
    filter_upwards [Ω.isOpen.mem_nhds hx, (hW j).mem_nhds hxj] with y hy hyj
    exact (ρ.circleMix_eq_adjusted f u v (u j) hy (hlift j y hyj)).symm
  rw [FiniteTransfer.circleFDeriv_eq_lift
    (hsm.continuousOn.continuousAt (Ω.isOpen.mem_nhds hx)) hr.continuousAt he]
  exact ρ.adjustedCircleMix_derivative W hW hsub f u v hu hlift hv j hx hxj i

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalLiftSmoothing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive local smoothing of real branches, without imposing a global
unit-interval range on the branches of a circle-valued coordinate. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_local_lift_sobolev_smoothing
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω) :
    ∃ (V : Set EuclideanPlane) (φ : ℕ → EuclideanPlane → ℝ),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      (∀n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n)) ∧
      (∀ᶠ n in atTop, tsupport (φ n) ⊆ Ω) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (volume.restrict V))
        atTop (𝓝 0) ∧
      (∀i : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
        (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
        2 (volume.restrict V)) atTop (𝓝 0)) ∧
      (∀W : Set EuclideanPlane, IsOpen W → K ⊆ W → ∀c : ℝ,
        (∀x ∈ W, u x = c) → ∀ᶠ n in atTop, ∀x ∈ K, φ n x = c) ∧
      (∀ᶠ n in atTop, ∀a b : ℝ, (∀x ∈ Ω, u x ∈ Icc a b) →
        ∀x ∈ K, φ n x ∈ Icc a b) ∧
      (ContinuousOn u Ω → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ x ∈ K, |φ n x - u x| < ε) := by
  obtain ⟨η, V, hη, hsη, _, hsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro x hx
    apply hsub
    apply subset_tsupport η
    change η x ≠ 0
    rw [hone x hx]
    exact one_ne_zero
  let w : EuclideanPlane → ℝ := fun x => η x * u x
  obtain ⟨hw⟩ := exists_global_compact_cutoff_witness hΩ hu.memW1p hη hsη hsub
  have hwLp : MemLp w 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have hw_eq : EqOn w u V := fun x hx => by dsimp [w]; rw [hone x hx, one_mul]
  refine ⟨V, planarMollification w, hV, hKV, hVΩ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨planarMollification_smooth (hwLp.locallyIntegrable (by norm_num)) n,
      planarMollification_hasCompactSupport hsη.mul_right n⟩
  · exact planarMollification_support_eventually hsη.mul_right hΩ
      (tsupport_mul_subset_left.trans hsub)
  · have hl := tendsto_eLpNorm_restrict_zero (V := V) (planarMollification_tendsto_L2 hwLp)
    convert hl using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    rw [hw_eq hx]
  · intro i
    have hgi := weakGrad_eq_on_cutoff_plateau hV hVΩ hu hw hone i
    have hl := tendsto_eLpNorm_restrict_zero (V := V)
      (planarMollification_tendsto_gradient_L2 hw i)
    convert hl using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [hgi] with x hx
    rw [hx]
  · intro W hW hKW c hc
    apply planarMollification_eq_on_compact_eventually hK (hV.inter hW)
      (subset_inter hKV hKW)
    intro x hx
    rw [hw_eq hx.1, hc x hx.2]
  · filter_upwards [planarMollifier_samples_eventually hK hV hKV] with n hn a b hab x hx
    apply normed_convolution_mem_Icc volume (DeGiorgi.shrinkingBump n) hwLp.aestronglyMeasurable
    intro y hy
    have hyV := hn x hx hy
    rw [hw_eq hyV]
    exact hab y (hVΩ hyV)

  · intro hc ε hε
    have hwc : ContinuousOn w V := (hη.continuous.continuousOn).mul (hc.mono hVΩ)
    filter_upwards [planarMollification_uniform_on_compact hwLp.aestronglyMeasurable
      hK hV hKV hwc hε] with n hn x hx
    simpa only [hw_eq (hKV hx)] using hn x hx

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionLiftApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth approximants of the local real branches, preserving
interval bounds and prescribed weighted L2 derivative errors. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_partition_lift_approximants_with_accuracy
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, IsOpen (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (u : ι → EuclideanPlane → ℝ) (hu : ∀j, DeGiorgi.MemW1pWitness 2 (u j) (W j))
    (hc : ∀ j, ContinuousOn (u j) (W j))
    (δ : ι → ℝ) (hδ : ∀ j, 0 < δ j)
    (ε : ι → ℝ≥0∞) (hε : ∀j, 0 < ε j) :
    ∃v : ι → EuclideanPlane → ℝ, ∀j,
      (ContDiff ℝ (⊤ : ℕ∞) (v j) ∧ HasCompactSupport (v j)) ∧
      (∀a b : ℝ, (∀x ∈ W j, u j x ∈ Icc a b) →
        ∀x ∈ tsupport (ρ.weight j), v j x ∈ Icc a b) ∧
      (∀ x ∈ tsupport (ρ.weight j), |v j x - u j x| < δ j) ∧
      (∀i : Fin 2, eLpNorm (fun x =>
        ρ.weight j x * ((fderiv ℝ (v j) x) (EuclideanSpace.single i 1) -
          (hu j).weakGrad x i) +
        (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v j x - u j x))
        2 volume < ε j) := by
  classical
  suffices H : ∀j, ∃v : EuclideanPlane → ℝ,
      (ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport v) ∧
      (∀a b : ℝ, (∀x ∈ W j, u j x ∈ Icc a b) →
        ∀x ∈ tsupport (ρ.weight j), v x ∈ Icc a b) ∧
      (∀ x ∈ tsupport (ρ.weight j), |v x - u j x| < δ j) ∧
      (∀i : Fin 2, eLpNorm (fun x =>
        ρ.weight j x * ((fderiv ℝ v x) (EuclideanSpace.single i 1) -
          (hu j).weakGrad x i) +
        (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v x - u j x))
        2 volume < ε j) by
    choose v hv using H
    exact ⟨v, hv⟩
  intro j
  obtain ⟨V, φ, hV, hKV, hVW, hsmooth, _, hvalue, hgrad, _, hinterval, huniform⟩ :=
    exists_local_lift_sobolev_smoothing (hW j) (ρ.compact j).isCompact
      (hsub j) (hu j)
  let hw := (hu j).restrict hV hVW
  have hgrad' (i : Fin 2) : Tendsto (fun n => eLpNorm (fun x =>
      (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
      2 (volume.restrict V)) atTop (𝓝 0) := by
    simpa only [hw, DeGiorgi.MemW1pWitness.restrict] using hgrad i
  have herr (i : Fin 2) := tendsto_partition_derivative_error hV hw
    (fun n => (hsmooth n).1) hvalue hgrad' (ρ.smooth j) (ρ.compact j) hKV i
  have he : ∀ᶠ n in atTop, ∀i : Fin 2, eLpNorm (fun x =>
      ρ.weight j x * ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
        (hu j).weakGrad x i) +
      (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (φ n x - u j x))
      2 volume < ε j := by
    apply eventually_all.mpr
    intro i
    simpa only [hw, DeGiorgi.MemW1pWitness.restrict] using
      (tendsto_order.1 (herr i)).2 (ε j) (hε j)
  obtain ⟨n, hn, hb, hv⟩ := (he.and (hinterval.and (huniform (hc j) (δ j) (hδ j)))).exists
  exact ⟨φ n, hsmooth n, hb, hv, hn⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionLiftErrorSum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected local smoothing errors have a globally controlled L²
sum. Finiteness at each point follows from local finiteness of the weights. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem partitionLiftDerivativeError_pointFinite
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (u : ι → EuclideanPlane → ℝ)
    (G : ι → EuclideanPlane → EuclideanPlane) (v : ι → EuclideanPlane → ℝ)
    (i : Fin 2) (x : EuclideanPlane) :
    HasFiniteSupport (fun j => partitionLiftDerivativeError ρ u G v i j x) := by
  classical
  by_cases hx : x ∈ Ω
  · obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
    apply s.finite_toSet.subset
    intro j hj
    by_contra hjs
    apply hj
    change partitionLiftDerivativeError ρ u G v i j x = 0
    have hz : ρ.weight j =ᶠ[𝓝 x] (fun _ => 0) := hs.mono fun _ hy => hy j hjs
    have hd : fderiv ℝ (ρ.weight j) x = 0 := by
      rw [hz.fderiv_eq]
      exact fderiv_const_apply 0
    simp only [partitionLiftDerivativeError, hz.eq_of_nhds, hd,
      zero_apply, zero_mul, zero_add]
  · apply finite_empty.subset
    intro j hj
    apply False.elim
    apply hj
    change partitionLiftDerivativeError ρ u G v i j x = 0
    have hnot : x ∉ tsupport (ρ.weight j) := fun h => hx (ρ.inside j h)
    simp only [partitionLiftDerivativeError, image_eq_zero_of_notMem_tsupport hnot,
      fderiv_of_notMem_tsupport ℝ hnot, zero_apply, zero_mul, zero_add]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CirclePartitionError
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The intrinsic differential of the glued circle coordinate differs
from the partition of local weak derivatives by exactly the selected
summable approximation errors. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

theorem circleMix_gradient_error_identity
    (W : ι → Set EuclideanPlane) (hW : ∀ k, IsOpen (W k))
    (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (hu : ∀ k, ContinuousOn (u k) (W k))
    (hlift : ∀ k y, y ∈ W k → (u k y : UnitAddCircle) = f y)
    (hv : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (v k))
    (G : ι → EuclideanPlane → EuclideanPlane)
    {x : EuclideanPlane} (hx : x ∈ Ω) (i : Fin 2) :
    FiniteTransfer.circleFDeriv (ρ.circleMix f u v) x (EuclideanSpace.single i 1) -
      (∑ᶠ k, ρ.weight k x * G k x i) =
      ∑ᶠ k, partitionLiftDerivativeError ρ u G v i k x := by
  classical
  obtain ⟨s, hs, _, _, _⟩ := ρ.finite_weights_and_derivatives hx
  have hleft : (∑ᶠ k, (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
      (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x))) =
      ∑ k ∈ s, (ρ.weight k x * (fderiv ℝ (v k) x) (EuclideanSpace.single i 1) +
        (fderiv ℝ (ρ.weight k) x) (EuclideanSpace.single i 1) * (v k x - u k x)) := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hks
    apply hk
    simp only [(hs k hks).1, (hs k hks).2, zero_apply, zero_mul, zero_add]
  have hG : (∑ᶠ k, ρ.weight k x * G k x i) = ∑ k ∈ s, ρ.weight k x * G k x i := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hks
    apply hk
    change ρ.weight k x * G k x i = 0
    rw [(hs k hks).1, zero_mul]
  have herr : (∑ᶠ k, partitionLiftDerivativeError ρ u G v i k x) =
      ∑ k ∈ s, partitionLiftDerivativeError ρ u G v i k x := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hks
    apply hk
    change partitionLiftDerivativeError ρ u G v i k x = 0
    simp only [partitionLiftDerivativeError, (hs k hks).1, (hs k hks).2,
      zero_apply, zero_mul, zero_add]
  rw [ρ.circleMix_derivative W hW hsub f u v hu hlift hv hx i, hleft, hG, herr,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [partitionLiftDerivativeError]
  ring

end OpenPlanePartition

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CirclePartitionEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative energy control for the actual smooth circle map. Local
weak-gradient bounds survive positive mixing, while the selected smoothing
errors contribute an arbitrarily small additive L² term. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem partition_field_energy
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀ k, MeasurableSet (W k)) (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (G : ι → EuclideanPlane → ℝ)
    (hGm : ∀ k, AEStronglyMeasurable (G k) (volume.restrict (W k)))
    {g D : EuclideanPlane → ℝ} (hg : MemLp g 2 (volume.restrict Ω))
    (hG : ∀ k, ∀ᵐ x ∂volume.restrict (W k), |G k x| ≤ g x)
    {ε : ℝ≥0∞} (hDm : AEStronglyMeasurable D (volume.restrict Ω))
    (herr : eLpNorm (fun x => D x - ∑ᶠ k, ρ.weight k x * G k x)
      2 (volume.restrict Ω) < ε) :
    MemLp D 2 (volume.restrict Ω) ∧
      eLpNorm D 2 (volume.restrict Ω) ≤ ε + eLpNorm g 2 (volume.restrict Ω) := by
  let P : EuclideanPlane → ℝ := fun x => ∑ᶠ k, ρ.weight k x * G k x
  have hP : MemLp P 2 (volume.restrict Ω) :=
    partition_component_memLp ρ W hW hsub G hGm hg hG
  have hE : MemLp (fun x => D x - P x) 2 (volume.restrict Ω) :=
    ⟨hDm.sub hP.1, herr.trans_le le_top⟩
  have hsum : (fun x => (D x - P x) + P x) = D := by
    funext x
    exact sub_add_cancel _ _
  have hnormP : eLpNorm P 2 (volume.restrict Ω) ≤ eLpNorm g 2 (volume.restrict Ω) := by
    apply eLpNorm_mono_ae_real
    simpa only [Real.norm_eq_abs] using partition_component_bound ρ W hW hsub G g hG
  constructor
  · have hh := hE.add hP
    change MemLp (fun x => (D x - P x) + P x) 2 (volume.restrict Ω) at hh
    rwa [hsum] at hh
  · calc
      _ = eLpNorm (fun x => (D x - P x) + P x) 2 (volume.restrict Ω) := by rw [hsum]
      _ ≤ eLpNorm (fun x => D x - P x) 2 (volume.restrict Ω) +
          eLpNorm P 2 (volume.restrict Ω) := eLpNorm_add_le hE.1 hP.1 (by norm_num)
      _ ≤ _ := add_le_add herr.le hnormP

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleSmoothingTolerance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle smoothing with a prescribed continuous positive pointwise
error. The same choice controls all local derivative errors and preserves
interval bounds on each sampling patch. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

 theorem exists_circle_smoothing_with_tolerance
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀ k, IsOpen (W k)) (hsub : ∀ k, tsupport (ρ.weight k) ⊆ W k)
    (f : EuclideanPlane → UnitAddCircle) (u : ι → EuclideanPlane → ℝ)
    (hc : ∀ k, ContinuousOn (u k) (W k))
    (hlift : ∀ k x, x ∈ W k → (u k x : UnitAddCircle) = f x)
    (hu : ∀ k, DeGiorgi.MemW1pWitness 2 (u k) (W k))
    (e : EuclideanPlane → ℝ) (he : ContinuousOn e Ω) (hepos : ∀ x ∈ Ω, 0 < e x)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ v : ι → EuclideanPlane → ℝ,
      (∀ k, (ContDiff ℝ (⊤ : ℕ∞) (v k) ∧ HasCompactSupport (v k)) ∧
        ∀ a b : ℝ, (∀ x ∈ W k, u k x ∈ Icc a b) →
          ∀ x ∈ tsupport (ρ.weight k), v k x ∈ Icc a b) ∧
      FiniteTransfer.SmoothCircleOn (ρ.circleMix f u v) Ω ∧
      (∀ x ∈ Ω, |ρ.mix (fun k y => v k y - u k y) x| ≤ e x) ∧
      ∀ i : Fin 2, eLpNorm (fun x =>
        FiniteTransfer.circleFDeriv (ρ.circleMix f u v) x (EuclideanSpace.single i 1) -
          ∑ᶠ k, ρ.weight k x * (hu k).weakGrad x i) 2 (volume.restrict Ω) < ε := by
  have hd (k : ι) : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ tsupport (ρ.weight k), δ ≤ e x :=
    (ρ.compact k).isCompact.exists_forall_le' (he.mono (ρ.inside k))
      (fun x hx => hepos x (ρ.inside k hx))
  choose δ hδ hδe using hd
  obtain ⟨ξ, hξ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ι
  obtain ⟨v, hv⟩ := exists_partition_lift_approximants_with_accuracy ρ W hW hsub u hu hc δ hδ ξ hξ
  have hs (k : ι) := (hv k).1.1
  refine ⟨v, (fun k => ⟨(hv k).1, (hv k).2.1⟩),
    ρ.circleMix_smooth W hW hsub f u v hc hlift hs, ?_, ?_⟩
  · intro x hx
    apply abs_le.mpr
    apply ρ.mix_mem_Icc _ hx
    intro k hk
    have hxk := subset_tsupport (ρ.weight k) hk
    have hb := abs_lt.mp ((hv k).2.2.1 x hxk)
    have he' := hδe k x hxk
    constructor <;> linarith [hb.1, hb.2]
  · intro i
    have hsumerr : eLpNorm (fun x => ∑ᶠ k,
        partitionLiftDerivativeError ρ u (fun k => (hu k).weakGrad) v i k x)
        2 volume ≤ ∑' k, ξ k := by
      apply (eLpNorm_finsum_le_tsum_of_pointFinite volume _ ?_
        (partitionLiftDerivativeError_pointFinite ρ u _ v i)).trans
      · exact ENNReal.tsum_le_tsum (fun k => ((hv k).2.2.2 i).le)
      · intro k
        exact aestronglyMeasurable_partition_derivative_error (hW k) (hu k)
          (hv k).1.1 (ρ.smooth k) (hsub k) i
    calc
      _ = eLpNorm (fun x => ∑ᶠ k,
          partitionLiftDerivativeError ρ u (fun k => (hu k).weakGrad) v i k x)
          2 (volume.restrict Ω) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
        exact ρ.circleMix_gradient_error_identity W hW hsub f u v hc hlift hs _ hx i
      _ ≤ eLpNorm (fun x => ∑ᶠ k,
          partitionLiftDerivativeError ρ u (fun k => (hu k).weakGrad) v i k x) 2 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ < ε := hsumerr.trans_lt hsum

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleSmoothingBands
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smoothing discrepancy tending to zero leaves both endpoints of
every bounded local real band unchanged. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem tendsto_zero_of_abs_le_tolerance
    {X : Type*} {l : Filter X} {r e : X → ℝ}
    (he : Tendsto e l (𝓝 0)) (hbound : ∀ᶠ x in l, |r x| ≤ e x) :
    Tendsto r l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hbound, (tendsto_order.mp he).2 ε hε] with x hx he'
  simpa only [dist_zero_right, Real.norm_eq_abs] using hx.trans_lt he'

 theorem bounded_bands_eq_of_sub_tendsto_zero
    {X : Type*} {l : Filter X} [NeBot l] {u v : X → ℝ}
    (hul : IsBoundedUnder (· ≥ ·) l u) (huu : IsBoundedUnder (· ≤ ·) l u)
    (hsub : Tendsto (fun x => v x - u x) l (𝓝 0)) :
    liminf v l = liminf u l ∧ limsup v l = limsup u l := by
  let r := fun x => v x - u x
  have heq : u + r = v := by
    funext x
    dsimp [r]
    ring
  have heq' : r + u = v := by rw [add_comm, heq]
  have hrl : IsBoundedUnder (· ≥ ·) l r := hsub.isBoundedUnder_ge
  have hru : IsBoundedUnder (· ≤ ·) l r := hsub.isBoundedUnder_le
  have hlo := le_liminf_add (u := u) (v := r) hul huu hrl hru.isCoboundedUnder_ge
  have hhi := liminf_add_le (u := r) (v := u) hrl hru hul huu.isCoboundedUnder_ge
  have hsuplo := le_limsup_add (u := u) (v := r) huu hul.isCoboundedUnder_le hru hrl
  have hsuphi := limsup_add_le (u := u) (v := r) hul huu hrl.isCoboundedUnder_le hru
  have hliminf : liminf r l = 0 := hsub.liminf_eq
  have hlimsup : limsup r l = 0 := hsub.limsup_eq
  rw [heq, hliminf, add_zero] at hlo hsuplo
  rw [heq', hlimsup, zero_add] at hhi
  rw [heq, hlimsup, add_zero] at hsuphi
  exact ⟨le_antisymm hhi hlo, le_antisymm hsuphi hsuplo⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PerturbedMeanBands
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smoothed stream has the same dust bands as the actual mean when
its real correction vanishes there. The width remains the original
point-hit probability. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem perturbed_mapped_mean_bands
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x}))
    {Y : Type*} [TopologicalSpace Y] (S : Set Y) (s : Y) (hs : s ∈ closure S)
    (L : Y → ClosedUpperHalfPlane) (hL : ContinuousWithinAt L S s)
    (hz : 0 < (L s).val.im) (hproj : diskRayProjection (L s).val = F x)
    (v : Y → ℝ)
    (herr : Tendsto (fun y => v y - meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L y))
      (𝓝[S] s) (𝓝 0)) :
    (liminf v (𝓝[S] s) =
      liminf (fun y => meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L y)) (𝓝[S] s)) ∧
    (limsup v (𝓝[S] s) =
      limsup (fun y => meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L y)) (𝓝[S] s)) ∧
    limsup v (𝓝[S] s) - liminf v (𝓝[S] s) ≤
      (η : Measure A).real {γ | x ∈ range γ.val} := by
  let : NeBot (𝓝[S] s) := mem_closure_iff_nhdsWithin_neBot.mp hs
  let u : Y → ℝ := fun y => meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L y)
  let C := ((η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure K) : Measure K).real
    {γ | diskRayProjection (L s).val ∈ range γ.val}
  have hbase := meanGeometricIndex_oscillation_le_hit hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
    (L s) hz zero_lt_one
  have hnear : ∀ᶠ y in 𝓝[S] s, |u y - u s| < C + 1 :=
    (hL.prodMk_nhds tendsto_const_nhds).eventually hbase
  have hlo : IsBoundedUnder (· ≥ ·) (𝓝[S] s) u :=
    isBoundedUnder_of_eventually_ge (hnear.mono fun y hy => by
      have hh := (abs_lt.mp hy).1
      exact (show u s - C - 1 ≤ u y by linarith))
  have hhi : IsBoundedUnder (· ≤ ·) (𝓝[S] s) u :=
    isBoundedUnder_of_eventually_le (hnear.mono fun y hy => by
      have hh := (abs_lt.mp hy).2
      exact (show u y ≤ u s + C + 1 by linarith))
  have heq := bounded_bands_eq_of_sub_tendsto_zero hlo hhi herr
  refine ⟨heq.1, heq.2, ?_⟩
  rw [heq.1, heq.2]
  exact mapped_meanGeometricIndex_band_width hsch hsep A K hK hKS η F f hf hmap
    x hF S s hs L hL hz hproj

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LogarithmicDiskLift
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual continuous logarithmic lifts on simply connected physical
patches. The real coordinate is obtained from the existing circle cover. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_logarithmic_disk_lift {U : Set ℂ}
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    (w : ℂ → ℂ) (hw : ContinuousOn w U)
    (hw0 : ∀ z ∈ U, w z ≠ 0) (hw1 : ∀ z ∈ U, ‖w z‖ ≤ 1)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ U ∧
      (∀ z ∈ U, 0 ≤ (Ψ z).im) ∧
      ∀ z ∈ U, diskRayProjection (Ψ z) = w z := by
  have harg : ContinuousOn (normalizedArgument ∘ w) U := fun z hz =>
    (continuousAt_normalizedArgument (hw0 z hz)).comp_continuousWithinAt (hw z hz)
  obtain ⟨r, _, hr⟩ := AddCircle.eq_coe_Ico (normalizedArgument (w z₀))
  obtain ⟨u, hu, _, hproj⟩ := exists_continuous_circle_lift (normalizedArgument ∘ w) harg hz₀ r hr
  let Ψ : ℂ → ℂ := fun z => (u z : ℂ) + ((-Real.log ‖w z‖ : ℝ) : ℂ) * Complex.I
  have him (z : ℂ) : (Ψ z).im = -Real.log ‖w z‖ := by simp [Ψ]
  have hre (z : ℂ) : (Ψ z).re = u z := by simp [Ψ]
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp_continuousOn hu).add
      ((Complex.continuous_ofReal.comp_continuousOn
        ((hw.norm.log (fun z hz => norm_ne_zero_iff.mpr (hw0 z hz))).neg)).mul_const _)
  · intro z hz
    rw [him]
    exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hw1 z hz))
  · intro z hz
    apply Complex.ext_norm_arg
    · rw [diskRayProjection_norm, him, neg_neg,
        Real.exp_log (norm_pos_iff.mpr (hw0 z hz))]
    · apply Complex.arg_coe_angle_eq_iff.mp
      apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
      change normalizedArgument (diskRayProjection (Ψ z)) = normalizedArgument (w z)
      rw [diskRayProjection_argument, hre]
      exact hproj z hz

 theorem exists_logarithmic_disk_lift_ball (w : ℂ → ℂ) {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hw : ContinuousOn w (Metric.ball z₀ r))
    (hw0 : ∀ z ∈ Metric.ball z₀ r, w z ≠ 0)
    (hw1 : ∀ z ∈ Metric.ball z₀ r, ‖w z‖ ≤ 1) :
    ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, 0 ≤ (Ψ z).im) ∧
      ∀ z ∈ Metric.ball z₀ r, diskRayProjection (Ψ z) = w z := by
  let : ContractibleSpace (Metric.ball z₀ r) :=
    (convex_ball z₀ r).contractibleSpace (Metric.nonempty_ball.mpr hr)
  let : LocallyPathConnectedSpace (Metric.ball z₀ r) := Metric.isOpen_ball.locallyPathConnectedSpace
  exact exists_logarithmic_disk_lift w hw hw0 hw1 (Metric.mem_ball_self hr)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_LogarithmicCutCharts
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two explicit argument cuts give local logarithmic branches on any
topological source of a continuous punctured-disk map. No local
connectedness of the source is needed for this chart construction. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem logarithmicCutChart_nonneg (a : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    0 ≤ (logarithmicCutChart a w).im := by
  change 0 ≤ (((AddCircle.equivIco (1 : ℝ) a (normalizedArgument w) : ℝ) : ℂ) +
    ((-Real.log ‖w‖ : ℝ) : ℂ) * Complex.I).im
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
    zero_add] using neg_nonneg.mpr (Real.log_nonpos (norm_nonneg w) hw)

theorem logarithmicCutChart_projection (a : ℝ) {w : ℂ} (hw : w ≠ 0) :
    diskRayProjection (logarithmicCutChart a w) = w := by
  apply Complex.ext_norm_arg
  · rw [diskRayProjection_norm]
    simp only [logarithmicCutChart, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add, neg_neg]
    exact Real.exp_log (norm_pos_iff.mpr hw)
  · apply Complex.arg_coe_angle_eq_iff.mp
    apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
    change normalizedArgument (diskRayProjection (logarithmicCutChart a w)) =
      normalizedArgument w
    rw [diskRayProjection_argument]
    simp only [logarithmicCutChart, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero]
    exact AddCircle.coe_equivIco

theorem continuousAt_logarithmicCutChart (a : ℝ) {w : ℂ} (hw : w ≠ 0)
    (ha : normalizedArgument w ≠ (a : UnitAddCircle)) :
    ContinuousAt (logarithmicCutChart a) w := by
  have hangle := continuous_subtype_val.continuousAt.comp
    ((AddCircle.continuousAt_equivIco (1 : ℝ) a ha).comp
      (continuousAt_normalizedArgument hw))
  exact (Complex.continuous_ofReal.continuousAt.comp hangle).add
    ((Complex.continuous_ofReal.continuousAt.comp
      ((continuous_norm.continuousAt.log (norm_ne_zero_iff.mpr hw)).neg)).mul_const _)

theorem isOpen_logarithmicCutDomain {X : Type*} [TopologicalSpace X]
    (F : X → ℂ) (hF : Continuous F) {S : Set X} (hS : IsOpen S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (a : ℝ) : IsOpen (logarithmicCutDomain F S a) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have harg : ContinuousAt (fun y => normalizedArgument (F y)) x :=
    (continuousAt_normalizedArgument (h0 x hx.1)).comp hF.continuousAt
  exact inter_mem (hS.mem_nhds hx.1)
    (harg.eventually (isOpen_ne.mem_nhds hx.2))

theorem logarithmicCutDomain_cover {X : Type*} (F : X → ℂ) (S : Set X) :
    S ⊆ logarithmicCutDomain F S 0 ∪ logarithmicCutDomain F S (1 / 2) := by
  intro x hx
  by_cases h : normalizedArgument (F x) = (0 : UnitAddCircle)
  · right
    refine ⟨hx, ?_⟩
    rw [h]
    intro he
    have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show (0 : ℝ) ∈ Ico 0 (0 + 1) by norm_num)
      (show (1 / 2 : ℝ) ∈ Ico 0 (0 + 1) by norm_num)).mp he
    norm_num at hh
  · exact Or.inl ⟨hx, h⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MeanPeriodBudget
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smoothed mean-period graph is paid for by the selected
law's point-hit probabilities, with unit budget at its terminal point. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
theorem logarithmicCutChart_im_pos (a : ℝ) {z : ℂ} (h0 : z ≠ 0) (h1 : ‖z‖ < 1) :
    0 < (logarithmicCutChart a z).im := by
  have hlog := Real.log_neg (norm_pos_iff.mpr h0) h1
  simpa only [logarithmicCutChart, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, zero_add] using neg_pos.mpr hlog

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HalfPlaneDiskInverse
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse Cayley coordinate on the punctured closed disk. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem diskHalfPlane_den_ne_zero {w : ℂ} (hw : w ≠ 1) : 1 - w ≠ 0 := by
  exact sub_ne_zero.mpr hw.symm

theorem diskHalfPlane_add_I {w : ℂ} (hw : w ≠ 1) :
    diskHalfPlane w + Complex.I = (2 * Complex.I) / (1 - w) := by
  unfold diskHalfPlane
  field_simp [diskHalfPlane_den_ne_zero hw]
  ring

theorem diskHalfPlane_add_I_ne_zero {w : ℂ} (hw : w ≠ 1) :
    diskHalfPlane w + Complex.I ≠ 0 := by
  rw [diskHalfPlane_add_I hw]
  exact div_ne_zero (by simp) (diskHalfPlane_den_ne_zero hw)

theorem halfPlaneDisk_diskHalfPlane {w : ℂ} (hw : w ≠ 1) :
    halfPlaneDisk (diskHalfPlane w) = w := by
  rw [halfPlaneDisk, div_eq_iff (diskHalfPlane_add_I_ne_zero hw)]
  unfold diskHalfPlane
  field_simp [diskHalfPlane_den_ne_zero hw]
  ring

theorem diskHalfPlane_halfPlaneDisk {z : ℂ} (hz : 0 ≤ z.im) :
    diskHalfPlane (halfPlaneDisk z) = z := by
  rw [diskHalfPlane, div_eq_iff (diskHalfPlane_den_ne_zero (halfPlaneDisk_ne_one hz))]
  unfold halfPlaneDisk
  field_simp [halfPlaneDisk_den_ne_zero hz]
  ring

theorem diskHalfPlane_nonneg {w : ℂ} (hw : w ≠ 1) (hn : ‖w‖ ≤ 1) :
    0 ≤ (diskHalfPlane w).im := by
  have hh : ‖halfPlaneDisk (diskHalfPlane w)‖ ≤ 1 := by rw [halfPlaneDisk_diskHalfPlane hw]; exact hn
  rw [halfPlaneDisk, norm_div] at hh
  have hb : ‖diskHalfPlane w - Complex.I‖ ≤ ‖diskHalfPlane w + Complex.I‖ :=
    (div_le_one (norm_pos_iff.mpr (diskHalfPlane_add_I_ne_zero hw))).mp hh
  have hs := halfPlaneDisk_normSq (diskHalfPlane w)
  simp only [← Complex.sq_norm] at hs
  nlinarith [norm_nonneg (diskHalfPlane w - Complex.I)]

theorem continuousOn_diskHalfPlane : ContinuousOn diskHalfPlane {w : ℂ | w ≠ 1} :=
  (continuous_const.mul (continuous_const.add continuous_id)).continuousOn.div
    (continuous_const.sub continuous_id).continuousOn (fun _ h => diskHalfPlane_den_ne_zero h)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HalfPlanePathSides
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The side path test in the original half-plane coordinates. -/

open Set Function Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem HalfPlaneRay.diskAvoiding_iff_halfPlaneAvoiding (R : HalfPlaneRay)
    {z w : ℂ} (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    DiskAvoidingPath R.crosscut.toContinuousMap (halfPlaneDisk z) (halfPlaneDisk w) ↔
      HalfPlaneAvoidingPath R z w := by
  constructor
  · rintro ⟨δ, h0, h1, hδ⟩
    have hne : ∀ t, δ t ≠ 1 := by
      intro t ht
      apply (hδ t).2
      exact ⟨⊤, R.compactify_top.trans ht.symm⟩
    let ε : C(PathTime, ℂ) := ⟨diskHalfPlane ∘ δ,
      continuousOn_diskHalfPlane.comp_continuous δ.continuous hne⟩
    refine ⟨ε, ?_, ?_, ?_⟩
    · change diskHalfPlane (δ 0) = z
      rw [h0, diskHalfPlane_halfPlaneDisk hz]
    · change diskHalfPlane (δ 1) = w
      rw [h1, diskHalfPlane_halfPlaneDisk hw]
    · intro t
      have hn : ‖δ t‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using (hδ t).1
      refine ⟨diskHalfPlane_nonneg (hne t) hn, ?_⟩
      rintro ⟨s, hs⟩
      apply (hδ t).2
      have he : δ t = halfPlaneDisk (R.curve s) := by
        rw [← halfPlaneDisk_diskHalfPlane (hne t)]
        exact congrArg halfPlaneDisk hs.symm
      rw [he]
      exact (R.cayley_mem_crosscut_iff (R.nonneg s)).mpr (mem_range_self s)
  · rintro ⟨δ, h0, h1, hδ⟩
    let ε : C(PathTime, ℂ) := ⟨halfPlaneDisk ∘ δ,
      continuousOn_halfPlaneDisk.comp_continuous δ.continuous (fun t => (hδ t).1)⟩
    refine ⟨ε, congrArg halfPlaneDisk h0, congrArg halfPlaneDisk h1, ?_⟩
    intro t
    refine ⟨Metric.mem_closedBall.mpr ?_, ?_⟩
    · simpa only [ε, ContinuousMap.coe_mk, Function.comp_apply, dist_zero_right] using
        halfPlaneDisk_norm_le (hδ t).1
    · exact fun hm => (hδ t).2 ((R.cayley_mem_crosscut_iff (hδ t).1).mp hm)

 theorem HalfPlaneRay.right_iff_halfPlanePath (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) {z : ℂ} (hz : 0 ≤ z.im) :
    halfPlaneDisk z ∉ closure (jordanInterior H) ↔ HalfPlaneAvoidingPath R z
      (((R.curve ⟨0, bot_lt_top⟩).re + 1 : ℝ) : ℂ) := by
  rw [R.right_iff_avoidingPath hsep hH
    (Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le hz))]
  exact R.diskAvoiding_iff_halfPlaneAvoiding hz (by simp)

 theorem HalfPlaneRay.translated_right (hsep : UnitDiskCrosscutSeparation)
    (R S : HalfPlaneRay) {H J : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) (hJ : S.IsJordan J)
    (a : ℝ) (ha : ∀ t, S.curve t = R.curve t + (a : ℂ))
    {z : ℂ} (hz : 0 ≤ z.im) (hr : halfPlaneDisk z ∉ closure (jordanInterior H)) :
    halfPlaneDisk (z + (a : ℂ)) ∉ closure (jordanInterior J) := by
  have hza : 0 ≤ (z + (a : ℂ)).im := by simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hz
  apply (S.right_iff_halfPlanePath hsep hJ hza).mpr
  obtain ⟨δ, h0, h1, hδ⟩ := (R.right_iff_halfPlanePath hsep hH hz).mp hr
  refine ⟨⟨fun t => δ t + (a : ℂ), δ.continuous.add continuous_const⟩,
    congrArg (fun w => w + (a : ℂ)) h0, ?_, ?_⟩
  · change δ 1 + (a : ℂ) = _
    rw [h1, ha, Complex.add_re, Complex.ofReal_re]
    push_cast
    ring
  · intro t
    refine ⟨?_, ?_⟩
    · simpa only [ContinuousMap.coe_mk, Complex.add_im, Complex.ofReal_im, add_zero] using (hδ t).1
    · rintro ⟨s, hs⟩
      rw [ha s] at hs
      exact (hδ t).2 ⟨s, add_right_cancel hs⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GeometricIndexPeriod
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deck translation adds the corresponding integer to the actual ray
index and hence to its expectation. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem translatedHalfPlaneRay_curve_add (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k n : ℤ) (t : DiskRayTime) :
    (translatedHalfPlaneRay γ hγ (k + n)).curve t =
      (translatedHalfPlaneRay γ hγ k).curve t + (n : ℂ) := by
  change diskRayComplex γ hγ.1 hγ.2.2.1 t + ((k + n : ℤ) : ℂ) =
    (diskRayComplex γ hγ.1 hγ.2.2.1 t + (k : ℂ)) + (n : ℂ)
  rw [Int.cast_add, add_assoc]

 theorem rayRightIndices_translate_iff (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (z : ℂ) (hz : 0 ≤ z.im) (k n : ℤ) :
    k + n ∈ rayRightIndices hsch γ hγ (z + (n : ℂ)) ↔ k ∈ rayRightIndices hsch γ hγ z := by
  constructor
  · intro hm
    have hza : 0 ≤ (z + (n : ℂ)).im := by simpa only [Complex.add_im, Complex.intCast_im, add_zero] using hz
    have hh := HalfPlaneRay.translated_right hsep
      (translatedHalfPlaneRay γ hγ (k + n)) (translatedHalfPlaneRay γ hγ k)
      (rayJordan_spec hsch γ hγ (k + n)) (rayJordan_spec hsch γ hγ k)
      (-(n : ℝ)) (fun t => by
        rw [translatedHalfPlaneRay_curve_add]
        push_cast
        simp only [add_neg_cancel_right]) hza hm
    simpa only [rayRightIndices, mem_ofPred_eq, Complex.ofReal_neg, Complex.ofReal_intCast,
      add_neg_cancel_right] using hh
  · intro hm
    have hh := HalfPlaneRay.translated_right hsep
      (translatedHalfPlaneRay γ hγ k) (translatedHalfPlaneRay γ hγ (k + n))
      (rayJordan_spec hsch γ hγ k) (rayJordan_spec hsch γ hγ (k + n))
      (n : ℝ) (fun t => by simpa only [Complex.ofReal_intCast] using
        translatedHalfPlaneRay_curve_add γ hγ k n t) hz hm
    simpa only [rayRightIndices, mem_ofPred_eq, Complex.ofReal_intCast] using hh

 theorem geometricRayIndex_translate (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (z : ℂ) (hz : 0 ≤ z.im) (n : ℤ) :
    geometricRayIndex hsch γ hγ (z + (n : ℂ)) = geometricRayIndex hsch γ hγ z + n := by
  have hza : 0 ≤ (z + (n : ℂ)).im := by simpa only [Complex.add_im, Complex.intCast_im, add_zero] using hz
  have h0 := geometricRayIndex_isGreatest hsch γ hγ z hz
  have h1 := geometricRayIndex_isGreatest hsch γ hγ (z + (n : ℂ)) hza
  apply le_antisymm
  · have hm : geometricRayIndex hsch γ hγ (z + (n : ℂ)) - n ∈ rayRightIndices hsch γ hγ z := by
      apply (rayRightIndices_translate_iff hsch hsep γ hγ z hz _ n).mp
      simpa only [sub_add_cancel] using h1.1
    have hb := h0.2 hm
    omega
  · exact h1.2 ((rayRightIndices_translate_iff hsch hsep γ hγ z hz _ n).mpr h0.1)

 theorem meanGeometricIndex_translate (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) (n : ℤ) :
    meanGeometricIndex hsch K hKS η (z.translate n) = meanGeometricIndex hsch K hKS η z + (n : ℝ) := by
  have hi := integrable_geometricRayIndex hsch hsep K hK hKS η z
  simp only [meanGeometricIndex, ClosedUpperHalfPlane.translate,
    geometricRayIndex_translate hsch hsep _ _ _ z.property, Int.cast_add,
    integral_add hi (integrable_const (n : ℝ)), integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, one_smul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MeanIndexCircle
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mean index descends through the logarithmic cover to a
circle-valued coordinate. Every continuous local lift represents the
same coordinate; no choice of branch is part of the resulting map. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem diskRayProjection_eq_implies_translate
    (z w : ClosedUpperHalfPlane) (h : diskRayProjection z.val = diskRayProjection w.val) :
    ∃ n : ℤ, z = w.translate n := by
  have hi : z.val.im = w.val.im := by
    have hn := congrArg norm h
    rw [diskRayProjection_norm, diskRayProjection_norm] at hn
    have he := Real.exp_injective hn
    linarith
  have hr : (z.val.re : UnitAddCircle) = (w.val.re : UnitAddCircle) := by
    simpa only [diskRayProjection_argument] using congrArg normalizedArgument h
  obtain ⟨n, hn⟩ := (addCircle_eq_iff_exists_int 1 z.val.re w.val.re).mp hr
  refine ⟨n, Subtype.ext ?_⟩
  apply Complex.ext
  · simpa only [ClosedUpperHalfPlane.translate, Complex.add_re, Complex.intCast_re, mul_one] using hn
  · simpa only [ClosedUpperHalfPlane.translate, Complex.add_im, Complex.intCast_im, add_zero] using hi

 theorem meanGeometricIndex_mod_eq_of_projection_eq
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (z w : ClosedUpperHalfPlane)
    (h : diskRayProjection z.val = diskRayProjection w.val) :
    (meanGeometricIndex hsch K hKS η z : UnitAddCircle) =
      (meanGeometricIndex hsch K hKS η w : UnitAddCircle) := by
  obtain ⟨n, rfl⟩ := diskRayProjection_eq_implies_translate z w h
  apply (addCircle_eq_iff_exists_int 1 _ _).mpr
  exact ⟨n, by simpa only [mul_one] using meanGeometricIndex_translate hsch hsep K hK hKS η w n⟩

 theorem diskMeanCircle_projection
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) :
    diskMeanCircle hsch K hKS η (diskRayProjection z.val) =
      (meanGeometricIndex hsch K hKS η z : UnitAddCircle) := by
  have hex : ∃ w : ClosedUpperHalfPlane, diskRayProjection w.val = diskRayProjection z.val := ⟨z, rfl⟩
  rw [diskMeanCircle, dite_eq_left hex]
  exact meanGeometricIndex_mod_eq_of_projection_eq hsch hsep K hK hKS η
    (Classical.choose hex) z (Classical.choose_spec hex)

 theorem diskMeanCircle_eq_local_mean
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (Q Ψ : ℂ → ℂ) (z : ℂ)
    (hz : 0 ≤ (Ψ z).im) (hproj : diskRayProjection (Ψ z) = Q z) :
    diskMeanCircle hsch K hKS η (Q z) =
      (liftedMeanGeometricIndex hsch K hKS η Ψ z : UnitAddCircle) := by
  rw [liftedMeanGeometricIndex_eq hsch K hKS η Ψ z hz, ← hproj]
  exact diskMeanCircle_projection hsch hsep K hK hKS η ⟨Ψ z, hz⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PerturbedMeanFreeTrace
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a point avoided by the compact arc law, a vanishing correction
leaves a genuine mean trace. Its entire interval-band fiber is therefore
the single value used in ordered compatibility. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem tendsto_perturbed_mean_at_avoided_point
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) {X : Type*} [TopologicalSpace X]
    (D : Set X) (x : X) (L : X → ClosedUpperHalfPlane)
    (hL : ContinuousWithinAt L D x)
    (hmiss : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (L x).val ∉ range γ.val)
    (u R : X → ℝ) (hR : Tendsto R (𝓝[D] x) (𝓝 0))
    (hu : u =ᶠ[𝓝[D] x] fun y => meanGeometricIndex hsch K hKS η (L y) + R y) :
    Tendsto u (𝓝[D] x) (𝓝 (meanGeometricIndex hsch K hKS η (L x))) := by
  have hmean := (continuousAt_meanGeometricIndex hsch hsep K hK hKS η (L x) hmiss).tendsto.comp hL
  have hsum := hmean.add hR
  simp only [add_zero] at hsum
  exact Tendsto.congr' hu.symm hsum

theorem perturbed_mean_band_at_avoided_point
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [CompactSpace X] [T2Space X]
    (D : Set X) (x : X) (hx : x ∈ closure D) (L : X → ClosedUpperHalfPlane)
    (hL : ContinuousWithinAt L D x)
    (hmiss : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (L x).val ∉ range γ.val)
    (u R : X → ℝ) (hR : Tendsto R (𝓝[D] x) (𝓝 0))
    (hu : u =ᶠ[𝓝[D] x] fun y => meanGeometricIndex hsch K hKS η (L y) + R y)
    {B : ℝ} (hbound : ∀ y ∈ D, |u y| ≤ B) (θ : UnitAddCircle) :
    (x, θ) ∈ circleBandGraph D u ↔
      diskMeanCircle hsch K hKS η (diskRayProjection (L x).val) = θ := by
  rw [circleBandGraph_of_trace hbound hx
    (tendsto_perturbed_mean_at_avoided_point hsch hsep K hK hKS η D x L hL hmiss u R hR hu)]
  rw [diskMeanCircle_projection hsch hsep K hK hKS η]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanPeriodFreeValues
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual period graph has the original mean value at every free
dust point avoided by the selected law. Vanishing smoothing error leaves
its limiting bands unchanged. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem period_graph_mean_free_value
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    (D M S Free : Set Sphere) (hdense : Dense D) (b : Sphere) (hb : b ∉ Free)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hmiss : ∀ x ∈ Free ∩ S, ∀ᵐ γ : K ∂(η : Measure K), F x ∉ range γ.val)
    {I : Type*} (V : I → Set Sphere) (hV : ∀ i, IsOpen (V i))
    (hVS : ∀ i, closure (V i) ⊆ S) (hbV : ∀ i, b ∉ V i)
    (hcover : M \ {b} ⊆ ⋃ i, V i)
    (a B : I → ℝ) (f : I → Sphere → ℝ)
    (hbound : ∀ i x, x ∈ D → |f i x| ≤ B i)
    (hlog : ∀ i, ContinuousOn (fun x => logarithmicCutChart (a i) (F x)) (closure (V i)))
    (htrans : ∀ i j x, x ∈ V i → x ∈ V j →
      ∃ k : ℤ, f j =ᶠ[𝓝[D] x] fun y => f i y + k)
    (R : Sphere → ℝ) (hR : ∀ x ∈ Free, Tendsto R (𝓝[D] x) (𝓝 0))
    (hf : ∀ i x, x ∈ V i → f i x =
      meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart (a i) (F x))) + R x)
    (x : Sphere) (hx : x ∈ Free) (θ : UnitAddCircle) :
    (x, θ) ∈ periodBandGraph D M b V f ↔
      x ∈ M ∧ diskMeanCircle hsch K hKS η (F x) = θ := by
  by_cases hxM : x ∈ M
  · have hxb : x ≠ b := fun he => hb (he ▸ hx)
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hxM, hxb⟩)
    have hcompat : ∀ i j x, x ∈ V i → x ∈ V j → ∀ θ,
        (x, θ) ∈ circleBandGraph D (f i) ↔ (x, θ) ∈ circleBandGraph D (f j) := by
      intro i j x hxi hxj θ
      obtain ⟨k, hk⟩ := htrans i j x hxi hxj
      exact (Set.ext_iff.mp (circleBand_fiber_eq_of_eventually_add_int hk) θ).symm
    rw [periodBandGraph_on_patch D M b V f hbV hcompat hi θ]
    have hxS : x ∈ S := hVS i (subset_closure hi)
    let L : Sphere → ClosedUpperHalfPlane := fun y =>
      upperHalfPlaneClamp (logarithmicCutChart (a i) (F y))
    have hLC : ContinuousAt L x := continuous_upperHalfPlaneClamp.continuousAt.comp
      ((hlog i).continuousAt (mem_of_superset ((hV i).mem_nhds hi) subset_closure))
    have hproj : diskRayProjection (L x).val = F x := by
      dsimp only [L]
      rw [upperHalfPlaneClamp_val (logarithmicCutChart_nonneg (a i) (h1 x hxS))]
      exact logarithmicCutChart_projection (a i) (h0 x hxS)
    have havoid : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (L x).val ∉ range γ.val := by
      simpa only [hproj] using hmiss x ⟨hx, hxS⟩
    have heq : f i =ᶠ[𝓝[D] x] fun y => meanGeometricIndex hsch K hKS η (L y) + R y := by
      filter_upwards [nhdsWithin_le_nhds ((hV i).mem_nhds hi)] with y hy
      exact hf i y hy
    have hbnd := perturbed_mean_band_at_avoided_point hsch hsep K hK hKS η D x
      (by rw [hdense.closure_eq]; trivial) L hLC.continuousWithinAt havoid
      (f i) R (hR x hx) heq (hbound i) θ
    rw [hproj] at hbnd
    rw [hbnd]
  · constructor
    · exact fun h => (hxM h.1).elim
    · exact fun h => (hxM h.1).elim

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanIndexIntersections
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The expected distinct intersection count controls increments of the
actual averaged index. Infinite counts are allowed. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

 theorem meanGeometricIndex_difference_le_intersections (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K)
    (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (hinj : Injective (diskRayProjection ∘ δ)) :
    ENNReal.ofReal |meanGeometricIndex hsch K hKS η ⟨δ 1, hδ 1⟩ -
      meanGeometricIndex hsch K hKS η ⟨δ 0, hδ 0⟩| ≤
      ∫⁻ γ : K, pathImageCount (diskRayProjection '' range δ) γ.val ∂(η : Measure K) := by
  have h0 := integrable_geometricRayIndex hsch hsep K hK hKS η ⟨δ 0, hδ 0⟩
  have h1 := integrable_geometricRayIndex hsch hsep K hK hKS η ⟨δ 1, hδ 1⟩
  unfold meanGeometricIndex
  rw [← integral_sub h1 h0]
  calc
    _ ≤ ∫⁻ γ : K, ‖(geometricRayIndex hsch γ.val (hKS γ.property) (δ 1) : ℝ) -
        (geometricRayIndex hsch γ.val (hKS γ.property) (δ 0) : ℝ)‖ₑ ∂(η : Measure K) := by
      simpa only [Real.enorm_eq_ofReal_abs] using enorm_integral_le_lintegral_enorm
        (μ := (η : Measure K)) (fun γ : K =>
          (geometricRayIndex hsch γ.val (hKS γ.property) (δ 1) : ℝ) -
            (geometricRayIndex hsch γ.val (hKS γ.property) (δ 0) : ℝ))
    _ ≤ _ := lintegral_mono (fun γ => by
      simpa only [Real.enorm_eq_ofReal_abs] using
        geometric_index_difference_le_intersections hsch hsep γ.val (hKS γ.property) δ hδ hinj)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathImageCountMap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injective coordinate changes preserve the distinct intersection
bound used by the physical slice estimate. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

 theorem pathImageCount_map_le (F : C(X, Y)) (γ : C(PathTime, X)) (H : Set X)
    (hF : InjOn F (range γ ∪ H)) :
    pathImageCount (F '' H) (F.comp γ) ≤ pathImageCount H γ := by
  rw [pathImageCount_eq_iSup]
  apply iSup_le
  intro n
  split
  · rename_i hn
    obtain ⟨t, ht, hH⟩ := hn
    have hti : Injective (γ ∘ t) := by
      intro i j hij
      exact ht (congrArg F hij)
    have hm (i : Fin n) : γ (t i) ∈ H := by
      obtain ⟨x, hx, heq⟩ := hH i
      have he : x = γ (t i) := hF (Or.inr hx) (Or.inl (mem_range_self _)) heq
      exact he ▸ hx
    rw [pathImageCount_eq_iSup]
    exact (ite_eq_left (show γ ∈ imageHitAtLeast H n from ⟨t, hti, hm⟩)).symm.le.trans
      (le_iSup (fun k => if γ ∈ imageHitAtLeast H k then (k : ℝ≥0∞) else 0) n)
  · exact bot_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_TransportedMeanIndex
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mean-index increment estimate in the original physical
coordinates. The Jordan map is used only through continuity and injectivity. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
 theorem meanGeometricIndex_mapped_difference_le_intersections
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (α : C(PathTime, X)) (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (hproj : ∀ t, diskRayProjection (δ t) = F (α t))
    (hinj : Injective (diskRayProjection ∘ δ))
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ range α)) :
    ENNReal.ofReal |meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) ⟨δ 1, hδ 1⟩ -
      meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) ⟨δ 0, hδ 0⟩| ≤
      ∫⁻ γ : A, pathImageCount (range α) γ.val ∂(η : Measure A) := by
  have hclosed : IsClosed (diskRayProjection '' range δ) :=
    ((isCompact_range δ.continuous).image continuous_diskRayProjection).isClosed
  have he : diskRayProjection '' range δ = F '' range α := by
    rw [← range_comp, ← range_comp]
    congr 1
    funext t
    exact hproj t
  apply (meanGeometricIndex_difference_le_intersections hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
    δ hδ hinj).trans
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map]
  · apply lintegral_mono
    intro γ
    change pathImageCount (diskRayProjection '' range δ) (f γ).val ≤
      pathImageCount (range α) γ.val
    rw [hmap γ, he]
    exact pathImageCount_map_le F γ.val (range α) (hF γ)
  · exact (measurable_pathImageCount hclosed).comp measurable_subtype_coe
  · exact hf

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CurveCoareaInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The plane-to-line specialization of Esmayli–Hajłasz, *The Coarea
Inequality*, Ann. Fenn. Math. 46 (2021), 965–991, Theorem 1.1,
DOI 10.5186/aasfm.2021.4654. The authors' manuscript is
https://arxiv.org/pdf/2006.00419 (Theorem 1.1, p. 1; proof, §7).

Only s=t=1, X=ℂ and Y=ℝ is retained. The Hausdorff normalization
constant is one in these dimensions. The source's measurability clause
requires finite H¹ measure and a measurable set in a boundedly compact
space; all these hypotheses are retained. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

 theorem cardinalitySum_le_hausdorffZero (A : Set ℂ) :
    (∑' z : ℂ, if z ∈ A then (1 : ℝ≥0∞) else 0) ≤ (μH[0] : Measure ℂ) A := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  let E := F.filter (fun z => z ∈ A)
  calc
    (∑ z ∈ F, if z ∈ A then (1 : ℝ≥0∞) else 0) =
        ∑ z ∈ E, (μH[0] : Measure ℂ) {z} := by
      simp only [E, Finset.sum_filter, Measure.hausdorffMeasure_zero_singleton]
    _ = (μH[0] : Measure ℂ) E := sum_measure_singleton
    _ ≤ (μH[0] : Measure ℂ) A := measure_mono (fun z hz => (Finset.mem_filter.mp hz).2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SubarcIntersectionCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct intersections decrease under subarc selection. Conditioning
on a compact family of mass at least one half costs at most a factor two. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem pathImageCount_le_timeCount (H : Set X) (γ : C(PathTime, X)) :
    pathImageCount H γ ≤ timeCount {p : C(PathTime, X) × PathTime | p.1 p.2 ∈ H} γ := by
  rw [pathImageCount_eq_iSup]
  apply iSup_le
  intro n
  split
  · rename_i hn
    obtain ⟨t, ht, hH⟩ := hn
    have hti : Injective t := fun i j hij => ht (congrArg γ hij)
    rw [timeCount_eq_iSup]
    exact (ite_eq_left (show γ ∈ timeWitnessSet
      {p : C(PathTime, X) × PathTime | p.1 p.2 ∈ H} n from ⟨t, hti, hH⟩)).symm.le.trans
        (le_iSup (fun k : ℕ => if γ ∈ timeWitnessSet
          {p : C(PathTime, X) × PathTime | p.1 p.2 ∈ H} k then (k : ℝ≥0∞) else 0) n)
  · exact bot_le

theorem pathImageCount_eq_timeCount_of_injective (H : Set X)
    (γ : C(PathTime, X)) (hγ : Injective γ) :
    pathImageCount H γ = timeCount {p : C(PathTime, X) × PathTime | p.1 p.2 ∈ H} γ := by
  apply le_antisymm (pathImageCount_le_timeCount H γ)
  rw [timeCount_eq_iSup]
  apply iSup_le
  intro n
  split
  · rename_i hn
    obtain ⟨t, ht, hH⟩ := hn
    rw [pathImageCount_eq_iSup]
    exact (ite_eq_left (show γ ∈ imageHitAtLeast H n from ⟨t, hγ.comp ht, hH⟩)).symm.le.trans
      (le_iSup (fun k : ℕ => if γ ∈ imageHitAtLeast H k then (k : ℝ≥0∞) else 0) n)
  · exact bot_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactPhysicalFiberCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarea for the actual distinct intersections of quotient arcs with
compact physical slices. Length is measured before the coordinate change. -/

open Set Function MeasureTheory
open scoped Topology ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
 theorem pathImageCount_image_le_hausdorffZero (π : ℂ → X) (A : Set ℂ)
    (γ : C(PathTime, X)) :
    pathImageCount (π '' A) γ ≤ (μH[0] : Measure ℂ) (A ∩ π ⁻¹' range γ) := by
  rw [pathImageCount_eq_iSup]
  apply iSup_le
  intro n
  split
  · rename_i hn
    obtain ⟨t, ht, hA⟩ := hn
    choose z hz he using hA
    have hzinj : Injective z := by
      intro i j hij
      apply ht
      change γ (t i) = γ (t j)
      rw [← he i, ← he j, hij]
    have hmem (i : Fin n) : z i ∈ A ∩ π ⁻¹' range γ :=
      ⟨hz i, ⟨t i, (he i).symm⟩⟩
    calc
      (n : ℝ≥0∞) = ∑' i : Fin n,
          if z i ∈ A ∩ π ⁻¹' range γ then (1 : ℝ≥0∞) else 0 := by simp [hmem]
      _ ≤ ∑' w : ℂ, if w ∈ A ∩ π ⁻¹' range γ then (1 : ℝ≥0∞) else 0 :=
        by
          simpa [mem_inter_iff] using ENNReal.tsum_comp_le_tsum_of_injective hzinj
            (fun w : ℂ => if w ∈ A ∩ π ⁻¹' range γ then (1 : ℝ≥0∞) else 0)
      _ ≤ _ := by
        simpa [mem_inter_iff] using
          cardinalitySum_le_hausdorffZero (A ∩ π ⁻¹' range γ)
  · exact bot_le

 theorem measurable_compactPhysicalFiberCount
    (π : ℂ → X) (hπ : Continuous π) {A : Set ℂ} (hA : IsCompact A)
    (f : ℂ → ℝ) (hf : Continuous f) (K : Set C(PathTime, X))
    (hK : ∀ γ ∈ K, Injective γ) :
    Measurable (fun p : K × ℝ => pathImageCount (π '' (A ∩ f ⁻¹' {p.2})) p.1.val) := by
  let H : Set (X × ℝ) := (fun z => (π z, f z)) '' A
  have hH : IsClosed H := (hA.image (hπ.prodMk hf)).isClosed
  let R : Set ((K × ℝ) × PathTime) :=
    {p | (p.1.1.val p.2, p.1.2) ∈ H}
  have hR : IsClosed R := hH.preimage
    ((continuous_eval.comp
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd)).prodMk
        (continuous_snd.comp continuous_fst))
  convert measurable_timeCount hR using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rw [pathImageCount_eq_timeCount_of_injective _ p.1.val (hK _ p.1.property)]
  apply tsum_congr
  intro t
  have heq : p.1.val t ∈ π '' (A ∩ f ⁻¹' {p.2}) ↔ ((p, t) ∈ R) := by
    change (∃ z, (z ∈ A ∧ f z ∈ ({p.2} : Set ℝ)) ∧ π z = p.1.val t) ↔
      ∃ z ∈ A, (π z, f z) = (p.1.val t, p.2)
    simp only [mem_singleton_iff, Prod.mk.injEq]
    aesop
  exact if_congr heq rfl rfl

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
 theorem compactPhysicalFiberCount_integral_le
    (hcoarea : PlanarLipschitzFiberCoarea)
    (π : ℂ → X) (hπ : Continuous π) {A : Set ℂ} (hA : IsCompact A)
    (γ : C(PathTime, X)) (L : ℝ≥0) (f : ℂ → ℝ) (hf : LipschitzWith L f)
    (hfin : (μH[1] : Measure ℂ) (A ∩ π ⁻¹' range γ) < ∞) :
    (∫⁻ y, pathImageCount (π '' (A ∩ f ⁻¹' {y})) γ) ≤
      (L : ℝ≥0∞) * (μH[1] : Measure ℂ) (A ∩ π ⁻¹' range γ) := by
  let E := A ∩ π ⁻¹' range γ
  have hE : IsCompact E := hA.inter_right ((isCompact_range γ.continuous).isClosed.preimage hπ)
  apply (lintegral_mono (fun y =>
    pathImageCount_image_le_hausdorffZero π (A ∩ f ⁻¹' {y}) γ)).trans
  convert (hcoarea E hE.measurableSet hfin L f hf).2 using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext y
  congr 1
  ext z
  simp only [E, mem_inter_iff, mem_preimage]
  tauto

 theorem mean_compactPhysicalFiberCount_integral_le
    (hcoarea : PlanarLipschitzFiberCoarea)
    (π : ℂ → X) (hπ : Continuous π) {A : Set ℂ} (hA : IsCompact A)
    (K : Set C(PathTime, X)) (hK : ∀ γ ∈ K, Injective γ)
    (η : Measure K) [SFinite η]
    (L : ℝ≥0) (f : ℂ → ℝ) (hf : LipschitzWith L f)
    (hfin : ∀ᵐ γ : K ∂η, (μH[1] : Measure ℂ) (A ∩ π ⁻¹' range γ.val) < ∞) :
    (∫⁻ y, ∫⁻ γ : K, pathImageCount (π '' (A ∩ f ⁻¹' {y})) γ.val ∂η) ≤
      (L : ℝ≥0∞) * ∫⁻ γ : K, (μH[1] : Measure ℂ) (A ∩ π ⁻¹' range γ.val) ∂η := by
  calc
    _ = ∫⁻ γ : K, ∫⁻ y, pathImageCount (π '' (A ∩ f ⁻¹' {y})) γ.val ∂volume ∂η := by
      apply lintegral_lintegral_swap
      exact ((measurable_compactPhysicalFiberCount π hπ hA f hf.continuous K hK).comp
        measurable_swap).aemeasurable
    _ ≤ ∫⁻ γ : K, (L : ℝ≥0∞) * (μH[1] : Measure ℂ) (A ∩ π ⁻¹' range γ.val) ∂η :=
      lintegral_mono_ae (hfin.mono fun γ hγ =>
        compactPhysicalFiberCount_integral_le hcoarea π hπ hA γ.val L f hf hγ)
    _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MappedPointAvoidance
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Point avoidance passes to the actual compact disk-arc image law.
Injectivity is required only on each sampled arc together with the
single point under consideration. -/

open Set Function Filter MeasureTheory

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem mapped_arc_point_avoidance
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x}))
    (hmiss : ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val) :
    ∀ᵐ γ : K ∂((η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure K) : Measure K), F x ∉ range γ.val := by
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff hf.aemeasurable ?_).mpr
  · filter_upwards [hmiss] with γ hγ
    rintro ⟨t, ht⟩
    apply hγ
    refine ⟨t, ?_⟩
    apply hF γ (Or.inl (mem_range_self t)) (Or.inr (mem_singleton x))
    simpa only [mem_preimage, hmap γ, ContinuousMap.comp_apply] using ht
  · exact ((isClosed_paths_hitting (F x)).measurableSet.preimage measurable_subtype_coe).compl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableLogarithmicCover
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable atlas of bounded logarithmic branches on the actual
punctured spherical mask. The closures stay inside that mask. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem exists_countable_bounded_logarithmic_cover
    (F : C(Sphere, ℂ)) (S : Set Sphere) (hS : IsOpen S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1) :
    ∃ (T : Set Sphere) (V : Sphere → Set Sphere) (a M : Sphere → ℝ),
      T ⊆ S ∧ T.Countable ∧ S ⊆ ⋃ x ∈ T, V x ∧
      ∀ x ∈ T, IsOpen (V x) ∧ x ∈ V x ∧ closure (V x) ⊆ S ∧
        ContinuousOn (fun y => logarithmicCutChart (a x) (F y)) (closure (V x)) ∧
        (∀ y ∈ closure (V x), ‖logarithmicCutChart (a x) (F y)‖ ≤ M x) ∧
        (∀ y ∈ closure (V x), 0 ≤ (logarithmicCutChart (a x) (F y)).im) ∧
        (∀ y ∈ closure (V x), diskRayProjection (logarithmicCutChart (a x) (F y)) = F y) := by
  have hlocal (x : Sphere) (hx : x ∈ S) :
      ∃ (V : Set Sphere) (a M : ℝ), IsOpen V ∧ x ∈ V ∧ closure V ⊆ S ∧
        ContinuousOn (fun y => logarithmicCutChart a (F y)) (closure V) ∧
        (∀ y ∈ closure V, ‖logarithmicCutChart a (F y)‖ ≤ M) ∧
        (∀ y ∈ closure V, 0 ≤ (logarithmicCutChart a (F y)).im) ∧
        (∀ y ∈ closure V, diskRayProjection (logarithmicCutChart a (F y)) = F y) := by
    have ha : ∃ a : ℝ, x ∈ logarithmicCutDomain F S a := by
      rcases logarithmicCutDomain_cover F S hx with h | h
      · exact ⟨0, h⟩
      · exact ⟨1 / 2, h⟩
    obtain ⟨a, hxa⟩ := ha
    have hW := isOpen_logarithmicCutDomain F F.continuous hS h0 a
    obtain ⟨V, hV, hxV, hVW, _⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := x)) hW (singleton_subset_iff.mpr hxa)
    have hclS : closure V ⊆ S := fun y hy => (hVW hy).1
    have hΨ : ContinuousOn (fun y => logarithmicCutChart a (F y)) (closure V) := by
      intro y hy
      exact ((continuousAt_logarithmicCutChart a (h0 y (hclS hy))
        (hVW hy).2).comp F.continuous.continuousAt).continuousWithinAt
    obtain ⟨M, hM⟩ := (isClosed_closure.isCompact : IsCompact (closure V)).exists_bound_of_continuousOn hΨ
    exact ⟨V, a, M, hV, hxV (mem_singleton x), hclS, hΨ, hM,
      fun y hy => logarithmicCutChart_nonneg a (h1 y (hclS hy)),
      fun y hy => logarithmicCutChart_projection a (h0 y (hclS hy))⟩
  have hchoice (x : Sphere) : ∃ (V : Set Sphere) (a M : ℝ), x ∈ S →
      IsOpen V ∧ x ∈ V ∧ closure V ⊆ S ∧
        ContinuousOn (fun y => logarithmicCutChart a (F y)) (closure V) ∧
        (∀ y ∈ closure V, ‖logarithmicCutChart a (F y)‖ ≤ M) ∧
        (∀ y ∈ closure V, 0 ≤ (logarithmicCutChart a (F y)).im) ∧
        (∀ y ∈ closure V, diskRayProjection (logarithmicCutChart a (F y)) = F y) := by
    by_cases hx : x ∈ S
    · obtain ⟨V, a, M, h⟩ := hlocal x hx
      exact ⟨V, a, M, fun _ => h⟩
    · exact ⟨∅, 0, 0, fun h => (hx h).elim⟩
  choose V a M hV using hchoice
  obtain ⟨T, hTS, hTc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := S) (f := V) (fun x hx => mem_nhdsWithin_of_mem_nhds
      ((hV x hx).1.mem_nhds (hV x hx).2.1))
  exact ⟨T, V, a, M, hTS, hTc, hcover, fun x hx => hV x (hTS hx)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanBranchBounds
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact arc family's geometric index bound also bounds every
mean branch on a bounded logarithmic chart. -/

open Set Function MeasureTheory

noncomputable section
namespace CircleDomainRigidity

theorem bounded_meanGeometricIndex_on_chart
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K)
    {X : Type*} (S : Set X) (L : X → ClosedUpperHalfPlane) (R : ℝ)
    (hR : ∀ x ∈ S, ‖(L x).val‖ ≤ R) :
    ∃ M : ℝ, ∀ x ∈ S, |meanGeometricIndex hsch K hKS η (L x)| ≤ M := by
  let T := max R 0
  have hT : 0 ≤ T := le_max_right _ _
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS T T hT hT
  refine ⟨M, ?_⟩
  intro x hx
  have hb : ‖(L x).val‖ ≤ T := (hR x hx).trans (le_max_left _ _)
  have hi : ∀ᵐ γ : K ∂(η : Measure K),
      ‖(geometricRayIndex hsch γ.val (hKS γ.property) (L x).val : ℝ)‖ ≤ M := by
    apply Filter.Eventually.of_forall
    intro γ
    simpa only [Complex.re_add_im, Real.norm_eq_abs] using
      hM γ (L x).val.re (L x).val.im ((Complex.abs_re_le_norm _).trans hb)
        (L x).property ((Complex.im_le_norm _).trans hb)
  simpa only [meanGeometricIndex, Real.norm_eq_abs, measureReal_def, measure_univ,
    ENNReal.toReal_one, mul_one] using norm_integral_le_of_norm_le_const hi

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BoundedLocalBranches
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local bounded lifts can be used in the compact-band construction by
setting them to zero outside their patch. Their bands, local continuity,
and physical derivatives within the open patch are unchanged. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem localBranchRepresentative_bound {X : Type*} {D V : Set X}
    {u : X → ℝ} {M : ℝ} (hM : 0 ≤ M) (hu : ∀ x ∈ D ∩ V, |u x| ≤ M) :
    ∀ x ∈ D, |localBranchRepresentative V u x| ≤ M := by
  classical
  intro x hx
  by_cases hV : x ∈ V
  · simpa only [localBranchRepresentative, indicator_of_mem hV] using hu x ⟨hx, hV⟩
  · simpa only [localBranchRepresentative, indicator_of_notMem hV, abs_zero] using hM

theorem localBranchRepresentative_continuousOn
    {X : Type*} [TopologicalSpace X] {D V : Set X} {u : X → ℝ}
    (hu : ContinuousOn u (D ∩ V)) : ContinuousOn (localBranchRepresentative V u) (D ∩ V) := by
  apply hu.congr
  intro x hx
  exact indicator_of_mem hx.2 u

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanBranchAtlas
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded real representatives for the actual mean on a punctured
spherical mask. The countable logarithmic atlas and every bound are
constructed from the compact arc law. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem exists_bounded_mean_branch_atlas
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    (S U : Set Sphere) (hS : IsOpen S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : K ∂(η : Measure K), F x ∉ range γ.val) :
    ∃ (I : Type) (_ : Countable I) (V : I → Set Sphere) (a M : I → ℝ)
      (u : I → Sphere → ℝ),
      S ⊆ ⋃ i, V i ∧
      (∀ i, IsOpen (V i) ∧ closure (V i) ⊆ S) ∧
      (∀ i, ContinuousOn (fun x => logarithmicCutChart (a i) (F x)) (closure (V i))) ∧
      (∀ i x, |u i x| ≤ M i) ∧
      (∀ i, ContinuousOn (u i) (U ∩ V i)) ∧
      (∀ i x, x ∈ V i →
        u i x = meanGeometricIndex hsch K hKS η
          (upperHalfPlaneClamp (logarithmicCutChart (a i) (F x)))) ∧
      (∀ i x, x ∈ V i → (u i x : UnitAddCircle) = diskMeanCircle hsch K hKS η (F x)) := by
  obtain ⟨T, V, a, R, _, hTc, hcover, hlocal⟩ :=
    exists_countable_bounded_logarithmic_cover F S hS h0 h1
  let : Countable T := hTc
  let L : T → Sphere → ClosedUpperHalfPlane := fun i x =>
    upperHalfPlaneClamp (logarithmicCutChart (a i.val) (F x))
  let v : T → Sphere → ℝ := fun i x => meanGeometricIndex hsch K hKS η (L i x)
  have hbound (i : T) : ∃ M : ℝ, ∀ x ∈ V i.val, |v i x| ≤ M := by
    apply bounded_meanGeometricIndex_on_chart hsch K hK hKS η (V i.val) (L i) (R i.val)
    intro x hx
    dsimp only [L]
    rw [upperHalfPlaneClamp_val ((hlocal i.val i.property).2.2.2.2.2.1 x (subset_closure hx))]
    exact (hlocal i.val i.property).2.2.2.2.1 x (subset_closure hx)
  choose M hM using hbound
  let u : T → Sphere → ℝ := fun i => localBranchRepresentative (V i.val) (v i)
  have hMn (i : T) : 0 ≤ M i :=
    (abs_nonneg (v i i.val)).trans (hM i i.val (hlocal i.val i.property).2.1)
  have hcont (i : T) : ContinuousOn (v i) (U ∩ V i.val) := by
    have hL : ContinuousOn (L i) (closure (V i.val)) :=
      continuous_upperHalfPlaneClamp.comp_continuousOn (hlocal i.val i.property).2.2.2.1
    intro x hx
    have hxcl := subset_closure hx.2
    have hxS := (hlocal i.val i.property).2.2.1 hxcl
    have hp : diskRayProjection (L i x).val = F x := by
      dsimp only [L]
      rw [upperHalfPlaneClamp_val ((hlocal i.val i.property).2.2.2.2.2.1 x hxcl)]
      exact (hlocal i.val i.property).2.2.2.2.2.2 x hxcl
    have hm := continuousAt_meanGeometricIndex hsch hsep K hK hKS η (L i x)
      (by simpa only [hp] using hmiss x ⟨hx.1, hxS⟩)
    exact hm.comp_continuousWithinAt ((hL x hxcl).mono (inter_subset_right.trans subset_closure))
  refine ⟨T, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), (fun i => V i.val), (fun i => a i.val), M, u, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hiT, hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨⟨i, hiT⟩, hxi⟩
  · intro i
    exact ⟨(hlocal i.val i.property).1, (hlocal i.val i.property).2.2.1⟩
  · intro i
    exact (hlocal i.val i.property).2.2.2.1
  · intro i x
    exact localBranchRepresentative_bound (D := univ) (hMn i)
      (fun x hx => hM i x hx.2) x (mem_univ x)
  · intro i
    exact localBranchRepresentative_continuousOn (hcont i)
  · intro i x hx
    exact indicator_of_mem hx (v i)
  · intro i x hx
    have hp : diskRayProjection (L i x).val = F x := by
      dsimp only [L]
      rw [upperHalfPlaneClamp_val ((hlocal i.val i.property).2.2.2.2.2.1 x (subset_closure hx))]
      exact (hlocal i.val i.property).2.2.2.2.2.2 x (subset_closure hx)
    change (((V i.val).indicator (v i) x : ℝ) : UnitAddCircle) = _
    rw [indicator_of_mem hx]
    exact hp ▸ (diskMeanCircle_projection hsch hsep K hK hKS η (L i x)).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanBranchTransitions
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mean branches have integer transitions before and after
adding a common smoothing correction. Thus their interval bands glue. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem mean_logarithmic_branches_eventually_add_int
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) {X : Type*} [TopologicalSpace X]
    (Q : X → ℂ) (a b : ℝ) (x : X)
    (ha : ContinuousAt (fun y => logarithmicCutChart a (Q y)) x)
    (hb : ContinuousAt (fun y => logarithmicCutChart b (Q y)) x) :
    ∃ k : ℤ, ∀ᶠ y in 𝓝 x,
      meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart b (Q y))) =
      meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart a (Q y))) + k := by
  have hquot (c : ℝ) (y : X) :
      ((logarithmicCutChart c (Q y)).re : UnitAddCircle) = normalizedArgument (Q y) := by
    simp only [logarithmicCutChart, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, AddCircle.coe_equivIco]
  obtain ⟨k, hk⟩ := FiniteTransfer.eventually_lifts_differ_by_integer
    (Complex.continuous_re.continuousAt.comp hb) (Complex.continuous_re.continuousAt.comp ha)
    (Eventually.of_forall (fun y => (hquot b y).trans (hquot a y).symm))
  refine ⟨k, hk.mono fun y hy => ?_⟩
  have he : upperHalfPlaneClamp (logarithmicCutChart b (Q y)) =
      (upperHalfPlaneClamp (logarithmicCutChart a (Q y))).translate k := by
    apply Subtype.ext
    apply Complex.ext
    · simpa only [upperHalfPlaneClamp, ClosedUpperHalfPlane.translate,
        Complex.add_re, Complex.intCast_re, Function.comp_apply] using hy
    · simp [upperHalfPlaneClamp, ClosedUpperHalfPlane.translate, logarithmicCutChart]
  rw [he, meanGeometricIndex_translate hsch hsep K hK hKS η]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PeriodDomainValues
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On the physical domain, the assembled period bands are the actual
circle-valued coordinate. Only continuity in the local patch is needed. -/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem circleBandGraph_of_continuousAt
    {X : Type*} [TopologicalSpace X] {D : Set X} {f : X → ℝ}
    {x : X} (hf : ContinuousAt f x) (hx : x ∈ D) (θ : UnitAddCircle) :
    (x, θ) ∈ circleBandGraph D f ↔ (f x : UnitAddCircle) = θ := by
  have hband (t : ℝ) : (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = f x := by
    constructor
    · intro ht
      obtain ⟨a, b, s, ha, hb, _, heq⟩ := mem_intervalFiberHull_iff.mp ht
      rw [clusterGraph_fiber_eq_of_continuousAt hf ha,
        clusterGraph_fiber_eq_of_continuousAt hf hb] at heq
      nlinarith [heq]
    · rintro rfl
      exact subset_intervalFiberHull _ (subset_closure ⟨x, hx, rfl⟩)
  constructor
  · rintro ⟨⟨y, t⟩, ht, he⟩
    have hy : y = x := congrArg Prod.fst he
    subst y
    simpa only [(hband t).mp ht] using congrArg Prod.snd he
  · intro he
    exact ⟨(x, f x), (hband (f x)).mpr rfl, Prod.ext rfl he⟩

theorem periodBandGraph_on_domain {ι : Type*}
    {D : Set Sphere} (hD : IsOpen D) (M : Set Sphere) (b : Sphere) (hb : b ∉ D)
    (V : ι → Set Sphere) (hV : ∀ i, IsOpen (V i)) (hcover : M \ {b} ⊆ ⋃ i, V i)
    (f : ι → Sphere → ℝ) (hf : ∀ i, ContinuousOn (f i) (D ∩ V i))
    (w : Sphere → UnitAddCircle)
    (hw : ∀ i x, x ∈ D ∩ V i → (f i x : UnitAddCircle) = w x)
    {x : Sphere} (hx : x ∈ D) (θ : UnitAddCircle) :
    (x, θ) ∈ periodBandGraph D M b V f ↔ x ∈ M ∧ w x = θ := by
  have hxb : x ≠ b := fun he => hb (he ▸ hx)
  have hlocal (i : ι) (hi : x ∈ V i) :
      (x, θ) ∈ circleBandGraph D (f i) ↔ w x = θ := by
    rw [circleBandGraph_of_continuousAt
      ((hf i).continuousAt ((hD.inter (hV i)).mem_nhds ⟨hx, hi⟩)) hx,
      hw i x ⟨hx, hi⟩]
  constructor
  · rintro ⟨hxM, heq | ⟨i, hi, hband⟩⟩
    · exact (hxb heq).elim
    · exact ⟨hxM, (hlocal i hi).mp hband⟩
  · rintro ⟨hxM, hθ⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hxM, hxb⟩)
    exact ⟨hxM, Or.inr ⟨i, hi, (hlocal i hi).mpr hθ⟩⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PerturbedMeanPeriodGraph
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the actual closed period-level graph from a compact
mean law and a shared bounded continuous smoothing correction. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem exists_perturbed_mean_period_graph
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    (S U M : Set Sphere) (hS : IsOpen S) (hU : IsOpen U) (hM : IsClosed M)
    (b : Sphere) (hbS : b ∉ S) (hbU : b ∉ U) (hMS : M \ {b} ⊆ S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : K ∂(η : Measure K), F x ∉ range γ.val)
    (R : Sphere → ℝ) (hR : ContinuousOn R (U ∩ S)) (hRbound : ∀ x, |R x| ≤ 1) :
    ∃ (I : Type) (_ : Countable I) (V : I → Set Sphere) (a B : I → ℝ)
      (f : I → Sphere → ℝ),
      S ⊆ ⋃ i, V i ∧ (∀ i, IsOpen (V i) ∧ closure (V i) ⊆ S) ∧
      (∀ i, ContinuousOn (fun x => logarithmicCutChart (a i) (F x)) (closure (V i))) ∧
      (∀ i x, |f i x| ≤ B i) ∧ (∀ i, ContinuousOn (f i) (U ∩ V i)) ∧
      (∀ i x, x ∈ V i → f i x =
        meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart (a i) (F x))) + R x) ∧
      (∀ i j x, x ∈ V i → x ∈ V j →
        ∃ k : ℤ, f j =ᶠ[𝓝[U] x] fun y => f i y + k) ∧
      IsClosed (periodBandGraph U M b V f) ∧
      ∀ x ∈ U, ∀ θ : UnitAddCircle,
        (x, θ) ∈ periodBandGraph U M b V f ↔
          x ∈ M ∧ diskMeanCircle hsch K hKS η (F x) + (R x : UnitAddCircle) = θ := by
  obtain ⟨I, hI, V, a, B, u, hcover, hV, hlog, hbound, hcont, hu, hcircle⟩ :=
    exists_bounded_mean_branch_atlas hsch hsep K hK hKS η F S U hS h0 h1 hmiss
  let : Countable I := hI
  let f : I → Sphere → ℝ := fun i => localBranchRepresentative (V i) (fun x => u i x + R x)
  have hf (i : I) (x : Sphere) (hx : x ∈ V i) : f i x =
      meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart (a i) (F x))) + R x := by
    change (V i).indicator (fun y => u i y + R y) x = _
    rw [indicator_of_mem hx, hu i x hx]
  have hfb (i : I) (x : Sphere) : |f i x| ≤ B i + 1 := by
    have hB : 0 ≤ B i := (abs_nonneg (u i b)).trans (hbound i b)
    apply localBranchRepresentative_bound (D := univ) (by linarith : 0 ≤ B i + 1)
      (fun y _ => (abs_add_le (u i y) (R y)).trans (add_le_add (hbound i y) (hRbound y))) x (mem_univ x)
  have hfc (i : I) : ContinuousOn (f i) (U ∩ V i) := by
    apply localBranchRepresentative_continuousOn
    exact (hcont i).add (hR.mono (fun x hx => ⟨hx.1, (hV i).2 (subset_closure hx.2)⟩))
  have htrans (i j : I) (x : Sphere) (hi : x ∈ V i) (hj : x ∈ V j) :
      ∃ k : ℤ, f j =ᶠ[𝓝[U] x] fun y => f i y + k := by
    have hiC : ContinuousAt (fun y => logarithmicCutChart (a i) (F y)) x :=
      (hlog i).continuousAt (mem_of_superset ((hV i).1.mem_nhds hi) subset_closure)
    have hjC : ContinuousAt (fun y => logarithmicCutChart (a j) (F y)) x :=
      (hlog j).continuousAt (mem_of_superset ((hV j).1.mem_nhds hj) subset_closure)
    obtain ⟨k, hk⟩ := mean_logarithmic_branches_eventually_add_int hsch hsep K hK hKS η
      F (a i) (a j) x hiC hjC
    have heq : f j =ᶠ[𝓝 x] fun y => f i y + k := by
      filter_upwards [hk, (hV i).1.mem_nhds hi, (hV j).1.mem_nhds hj] with y hy hiy hjy
      rw [hf j y hjy, hf i y hiy, hy]
      ring
    exact ⟨k, heq.filter_mono nhdsWithin_le_nhds⟩
  have hbV (i : I) : b ∉ V i := fun hi => hbS ((hV i).2 (subset_closure hi))
  have hcoverM : M \ {b} ⊆ ⋃ i, V i := hMS.trans hcover
  refine ⟨I, hI, V, a, (fun i => B i + 1), f, hcover, hV, hlog, hfb, hfc, hf, htrans, ?_, ?_⟩
  · exact isClosed_periodBandGraph_of_integer_transitions U M hM b V
      (fun i => (hV i).1) hbV hcoverM f (fun i => B i + 1) (fun i x _ => hfb i x) htrans
  · intro x hx θ
    apply periodBandGraph_on_domain hU M b hbU V (fun i => (hV i).1) hcoverM f hfc
      (fun y => diskMeanCircle hsch K hKS η (F y) + (R y : UnitAddCircle)) _ hx θ
    intro i y hy
    change (((V i).indicator (fun z => u i z + R z) y : ℝ) : UnitAddCircle) = _
    rw [indicator_of_mem hy.2, AddCircle.coe_add, hcircle i y hy.2]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PlaneCovectorEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two actual coordinate derivatives control the full covector
energy on the physical plane. No measurability of the covector field
beyond that of the two given derivatives is needed for this bound. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem planeCovector_norm_le (L : EuclideanPlane →L[ℝ] ℝ) :
    ‖L‖ ≤ ‖L (EuclideanSpace.single 0 1)‖ + ‖L (EuclideanSpace.single 1 1)‖ := by
  apply L.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  have hx : x = (x 0) • EuclideanSpace.single 0 1 + (x 1) • EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;> simp
  calc
    ‖L x‖ = ‖(x 0) • L (EuclideanSpace.single 0 1) +
        (x 1) • L (EuclideanSpace.single 1 1)‖ := by
      conv_lhs => rw [hx, map_add, map_smul, map_smul]
    _ ≤ ‖x 0‖ * ‖L (EuclideanSpace.single 0 1)‖ +
        ‖x 1‖ * ‖L (EuclideanSpace.single 1 1)‖ := by
      simpa only [norm_smul] using norm_add_le
        ((x 0) • L (EuclideanSpace.single 0 1)) ((x 1) • L (EuclideanSpace.single 1 1))
    _ ≤ ‖x‖ * ‖L (EuclideanSpace.single 0 1)‖ +
        ‖x‖ * ‖L (EuclideanSpace.single 1 1)‖ := by
      gcongr
      · exact PiLp.norm_apply_le x 0
      · exact PiLp.norm_apply_le x 1
    _ = _ := by ring

theorem lintegral_planeCovector_sq_lt_top
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (L : X → EuclideanPlane →L[ℝ] ℝ)
    (h : ∀ i : Fin 2, MemLp (fun x => L x (EuclideanSpace.single i 1)) 2 μ) :
    (∫⁻ x, ENNReal.ofReal ‖L x‖ ^ 2 ∂μ) < ∞ := by
  let s : X → ℝ := fun x => ‖L x (EuclideanSpace.single 0 1)‖ +
    ‖L x (EuclideanSpace.single 1 1)‖
  have hs : MemLp s 2 μ := (h 0).norm.add (h 1).norm
  have hfin := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hs.eLpNorm_lt_top
  have heq : (fun x => ‖s x‖ₑ ^ (2 : ℝ≥0∞).toReal) =
      (fun x => ENNReal.ofReal (s x) ^ 2) := by
    funext x
    rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, ENNReal.rpow_two,
      ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [heq] at hfin
  apply lt_of_le_of_lt _ hfin
  apply lintegral_mono
  intro x
  change ENNReal.ofReal ‖L x‖ ^ 2 ≤ ENNReal.ofReal (s x) ^ 2
  exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (planeCovector_norm_le (L x))) 2

end CircleDomainRigidity

end

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalDensityIntegrability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite spherical quadratic energy supplies finite planar line density
on almost every horizontal and vertical line in each compact chart patch. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem ennreal_le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ 2 := by
  by_cases h : a ≤ 1
  · exact h.trans le_self_add
  · have ha : 1 ≤ a := le_of_not_ge h
    calc
      a = a * 1 := (mul_one a).symm
      _ ≤ a * a := mul_le_mul' le_rfl ha
      _ ≤ 1 + a ^ 2 := by rw [pow_two]; exact le_add_self

theorem lintegral_lt_top_of_sq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (g : X → ℝ≥0∞)
    (hg : (∫⁻x, g x ^ 2 ∂μ) < ∞) : (∫⁻x, g x ∂μ) < ∞ := by
  apply lt_of_le_of_lt (lintegral_mono fun x => ennreal_le_one_add_sq (g x))
  rw [lintegral_add_left measurable_const, lintegral_const, one_mul]
  exact ENNReal.add_lt_top.mpr ⟨measure_lt_top μ univ, hg⟩

attribute [local instance] sphereMetric sphereBorel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_IntegralLineAbsoluteContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A linewise integral bound yields actual absolute continuity, without
first choosing a measurable representative for the bounded potential. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem absolutelyContinuousOnInterval_of_dist_le
    {f : ℝ → X} {g : ℝ → Y} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀x ∈ uIcc a b, ∀y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hg ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  apply lt_of_le_of_lt _ (h E hE hlen)
  exact Finset.sum_le_sum fun i hi => hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

theorem absolutelyContinuousOnInterval_of_integral_bound
    {f : ℝ → X} {g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hfg : ∀x ∈ uIcc a b, ∀y ∈ uIcc a b,
      dist (f x) (f y) ≤ ∫t in uIoc x y, g t) :
    AbsolutelyContinuousOnInterval f a b := by
  apply absolutelyContinuousOnInterval_of_dist_le
    (hg.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc))
  intro x hx y hy
  apply (hfg x hx y hy).trans
  rw [Real.dist_eq, intervalIntegral.integral_interval_sub_left
    (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc left_mem_uIcc hx)))
    (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc left_mem_uIcc hy))),
    intervalIntegral.abs_intervalIntegral_eq]
  simpa only [uIoc_comm y x] using (le_abs_self (∫t in uIoc x y, g t))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LineLIntegralAbsoluteContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The line-integral criterion in extended nonnegative form. It applies
directly to the measurable path densities used by the barrier. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

open AbsolutelyContinuousOnInterval

variable {X : Type*} [PseudoMetricSpace X]

theorem absolutelyContinuousOnInterval_of_lintegral_bound
    {f : ℝ → X} {g : ℝ → ℝ≥0∞} {a b : ℝ}
    (hg : (∫⁻t in uIoc a b, g t) < ∞)
    (hfg : ∀x ∈ uIcc a b, ∀y ∈ uIcc a b,
      ENNReal.ofReal (dist (f x) (f y)) ≤ ∫⁻t in uIoc x y, g t) :
    AbsolutelyContinuousOnInterval f a b := by
  let S (E : ℕ × (ℕ → ℝ × ℝ)) := ⋃i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have hlim : Tendsto (fun E => ∫⁻t in S E, g t ∂volume.restrict (uIoc a b))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero hg.ne (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero a b)
  have hr := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hlim
  simp only [ENNReal.toReal_zero] at hr
  apply squeeze_zero' (Eventually.of_forall fun E =>
    Finset.sum_nonneg (fun _ _ => dist_nonneg)) _ hr
  have hev : ∀ᶠ E in totalLengthFilter ⊓ 𝓟 (disjWithin a b), E ∈ disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hev] with E hE
  have hfin : (∫⁻t in S E, g t ∂volume.restrict (uIoc a b)) ≠ ∞ :=
    (lt_of_le_of_lt (lintegral_mono_set (subset_univ (S E)))
      (by simpa only [Measure.restrict_univ] using hg)).ne
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => dist_nonneg)]
  change (∑i ∈ Finset.range E.1, ENNReal.ofReal (dist (f (E.2 i).1) (f (E.2 i).2))) ≤
    ∫⁻t in ⋃i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2,
      g t ∂volume.restrict (uIoc a b)
  rw [lintegral_biUnion_finset hE.2 (fun _ _ => measurableSet_uIoc)]
  apply Finset.sum_le_sum
  intro i hi
  rw [Measure.restrict_restrict_of_subset
    (uIoc_subset_of_mem_disjWithin hE (Finset.mem_range.mp hi))]
  exact hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzIntervalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete paths obtained by traversing a real interval in a Lipschitz chart. -/

open Set Function Metric
open scoped NNReal ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem realIntervalPath_antilipschitz {a b : ℝ} (hab : a ≠ b) :
    AntilipschitzWith (nndist a b)⁻¹ (realIntervalPath a b) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro s t
  change dist s t ≤ _ * dist (AffineMap.lineMap a b (s : ℝ))
    (AffineMap.lineMap a b (t : ℝ))
  rw [dist_lineMap_lineMap, Subtype.dist_eq, NNReal.coe_inv, coe_nndist,
    mul_left_comm, inv_mul_cancel₀ (dist_ne_zero.mpr hab), mul_one]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleComplexEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the actual smoothed stream to the complex physical chart.
Its two L2 partial derivatives give finite full differential energy. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem complexPlaneCoordinates_symm_measurePreserving :
    MeasurePreserving complexPlaneCoordinates.symm volume volume := by
  exact euclideanPlaneCoordinates_symm_measurePreserving.comp
    Complex.volume_preserving_equiv_real_prod

theorem smooth_circle_complex_energy_finite
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω) (w : EuclideanPlane → UnitAddCircle)
    (hw : SmoothCircleOn w Ω)
    (hpartial : ∀ i : Fin 2, MemLp
      (fun x => circleFDeriv w x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω)) :
    SmoothCircleOn (w ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates.symm ⁻¹' Ω) ∧
    (∫⁻ z in complexPlaneCoordinates.symm ⁻¹' Ω,
      ENNReal.ofReal ‖circleFDeriv (w ∘ complexPlaneCoordinates.symm) z‖ ^ 2) < ∞ := by
  let q := complexPlaneCoordinates.symm
  have hq : MeasurePreserving q volume volume := complexPlaneCoordinates_symm_measurePreserving
  have hmp := hq.restrict_preimage hΩ.measurableSet
  have henergy := lintegral_planeCovector_sq_lt_top (volume.restrict Ω) (circleFDeriv w) hpartial
  have hpull : (∫⁻ z, ENNReal.ofReal ‖circleFDeriv w (q z)‖ ^ 2
      ∂(volume.restrict (q ⁻¹' Ω))) =
      ∫⁻ x, ENNReal.ofReal ‖circleFDeriv w x‖ ^ 2 ∂(volume.restrict Ω) :=
    hmp.lintegral_comp_emb q.toHomeomorph.measurableEmbedding
      (fun x => ENNReal.ofReal ‖circleFDeriv w x‖ ^ 2)
  refine ⟨?_, ?_⟩
  · intro z hz a ha
    exact (hw (q z) hz a ha).comp z q.contDiff.contDiffAt
  · have hmajor : (∫⁻ z, ENNReal.ofReal ‖q.toContinuousLinearMap‖ ^ 2 *
        ENNReal.ofReal ‖circleFDeriv w (q z)‖ ^ 2 ∂(volume.restrict (q ⁻¹' Ω))) < ∞ := by
      rw [lintegral_const_mul' _ _ (by finiteness), hpull]
      exact ENNReal.mul_lt_top (by finiteness) henergy
    apply lt_of_le_of_lt (lintegral_mono_ae ?_) hmajor
    filter_upwards [ae_restrict_mem (hΩ.preimage q.continuous).measurableSet] with z hz
    rw [circleFDeriv_comp hΩ hw q.differentiableAt hz, q.fderiv]
    calc
      ENNReal.ofReal ‖(circleFDeriv w (q z)).comp q.toContinuousLinearMap‖ ^ 2 ≤
          (ENNReal.ofReal ‖circleFDeriv w (q z)‖ * ENNReal.ofReal ‖q.toContinuousLinearMap‖) ^ 2 := by
        rw [← ENNReal.ofReal_mul (norm_nonneg _)]
        exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (ContinuousLinearMap.opNorm_comp_le _ _)) 2
      _ = _ := by rw [mul_pow, mul_comm]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothRealLift
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous real lift of a smooth circle map is automatically smooth,
with exactly its intrinsic differential and no additional energy cost. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_real_lift {U : Set E} (hU : IsOpen U)
    {f : E → UnitAddCircle} (hf : SmoothCircleOn f U)
    {u : E → ℝ} (hu : ContinuousOn u U)
    (hproj : ∀ x ∈ U, (u x : UnitAddCircle) = f x) :
    ContDiffOn ℝ ∞ u U := by
  intro x hx
  have hux : ContinuousAt u x := (hu x hx).continuousAt (hU.mem_nhds hx)
  have hb := hf x hx (circleCut f x) (circleCut_ne f x)
  have heq : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x]
      fun y => (circleBranch f (circleCut f x) y : UnitAddCircle) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [hproj y hy, coe_circleBranch]
  obtain ⟨m, hm⟩ := eventually_lifts_differ_by_integer hux hb.continuousAt heq
  exact ((hb.add contDiffAt_const).congr_of_eventuallyEq hm).contDiffWithinAt

theorem fderiv_real_lift {U : Set E} (hU : IsOpen U)
    {f : E → UnitAddCircle} (hf : SmoothCircleOn f U)
    {u : E → ℝ} (hu : ContinuousOn u U)
    (hproj : ∀ x ∈ U, (u x : UnitAddCircle) = f x) {x : E} (hx : x ∈ U) :
    fderiv ℝ u x = circleFDeriv f x := by
  symm
  apply circleFDeriv_eq_lift
    ((hf.continuousOn x hx).continuousAt (hU.mem_nhds hx))
    ((hu x hx).continuousAt (hU.mem_nhds hx))
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hproj y hy

theorem real_lift_energy_le [MeasurableSpace E] {U A : Set E}
    (hA : IsOpen A) (hAU : A ⊆ U)
    {f : E → UnitAddCircle} (hf : SmoothCircleOn f U)
    {u : E → ℝ} (hu : ContinuousOn u A)
    (hproj : ∀ x ∈ A, (u x : UnitAddCircle) = f x) (μ : Measure E)
    (hAm : MeasurableSet A) :
    (∫⁻ x in A, ENNReal.ofReal ‖fderiv ℝ u x‖ ^ 2 ∂μ) ≤
      ∫⁻ x in U, ENNReal.ofReal ‖circleFDeriv f x‖ ^ 2 ∂μ := by
  calc
    _ = ∫⁻ x in A, ENNReal.ofReal ‖circleFDeriv f x‖ ^ 2 ∂μ := by
      apply setLIntegral_congr_fun hAm
      intro x hx
      dsimp only
      rw [fderiv_real_lift hA (fun x hx => hf x (hAU hx)) hu hproj hx]
    _ ≤ _ := lintegral_mono_set hAU

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PeriodBranchPhysicalEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local branches of the constructed circle stream satisfy the exact
physical regularity hypotheses of the period generic-level theorem. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem period_branch_physical_energy
    {G U S V : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hV : IsOpen V) (hVS : V ⊆ S)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (u : Sphere → ℝ) (hu : ContinuousOn u (U ∩ V))
    (w : ℂ → UnitAddCircle)
    (hw : FiniteTransfer.SmoothCircleOn w
      (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S))
    (hproj : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ V →
      (u (π (z : Sphere)) : UnitAddCircle) = w z)
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' S,
      ENNReal.ofReal ‖FiniteTransfer.circleFDeriv w z‖ ^ 2) < ∞) :
    ContDiffOn ℝ 1 (fun z : ℂ => u (π (z : Sphere)))
        (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V) ∧
    (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => u (π (z : Sphere))) z‖ ^ 2) < ∞ := by
  let A := ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V
  have hA : IsOpen A := (hG.preimage OnePoint.continuous_coe).inter
    (hV.preimage (hπ.comp OnePoint.continuous_coe))
  have hsub : A ⊆ ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S :=
    fun z hz => ⟨hz.1, hVS hz.2⟩
  have hcont : ContinuousOn (fun z : ℂ => u (π (z : Sphere))) A := by
    apply hu.comp (hπ.comp OnePoint.continuous_coe).continuousOn
    intro z hz
    refine ⟨?_, hz.2⟩
    change π (z : Sphere) ∈ U
    rw [← he ⟨(z : Sphere), hz.1⟩]
    exact (e ⟨(z : Sphere), hz.1⟩).property
  have hp : ∀ z ∈ A, (u (π (z : Sphere)) : UnitAddCircle) = w z :=
    fun z hz => hproj z hz.1 hz.2
  exact ⟨(FiniteTransfer.contDiffOn_real_lift hA
      (fun z hz => hw z (hsub hz)) hcont hp).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),
    (FiniteTransfer.real_lift_energy_le hA hsub hw hcont hp volume hA.measurableSet).trans_lt henergy⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PlanarSliceIntegrals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangles with arbitrary compact transverse sets, and their exact
slice integrals. Coordinates are Euclidean physical coordinates. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

 theorem planarSliceBox_eq_image (I J : Set ℝ) :
    planarSliceBox I J = Complex.measurableEquivRealProd.symm '' (I ×ˢ J) := by
  ext z
  constructor
  · intro hz
    exact ⟨(z.re, z.im), hz, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact hp

 theorem isCompact_planarSliceBox {I J : Set ℝ} (hI : IsCompact I) (hJ : IsCompact J) :
    IsCompact (planarSliceBox I J) := by
  rw [planarSliceBox_eq_image]
  exact (hI.prod hJ).image Complex.equivRealProdCLM.symm.continuous

 theorem planarSliceBox_mono {I I' J J' : Set ℝ} (hI : I ⊆ I') (hJ : J ⊆ J') :
    planarSliceBox I J ⊆ planarSliceBox I' J' := fun _ hz => ⟨hI hz.1, hJ hz.2⟩

 theorem lintegral_planarSliceBox {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z in planarSliceBox I J, g z) =
      ∫⁻ y in J, ∫⁻ x in I, g ⟨x, y⟩ := by
  let e := Complex.measurableEquivRealProd.symm
  have hm : MeasurableSet (planarSliceBox I J) :=
    (hI.preimage Complex.continuous_re.measurable).inter
      (hJ.preimage Complex.continuous_im.measurable)
  rw [← lintegral_indicator hm,
    ← Complex.volume_preserving_equiv_real_prod.symm.lintegral_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
  change (∫⁻ p : ℝ × ℝ, (planarSliceBox I J).indicator g (e p)) = _
  have heq : (fun p : ℝ × ℝ => (planarSliceBox I J).indicator g (e p)) =
      (I ×ˢ J).indicator (fun p : ℝ × ℝ => g ⟨p.1, p.2⟩) := by
    funext p
    simp only [e, Complex.measurableEquivRealProd_symm_apply, Set.indicator_apply,
      planarSliceBox, mem_ofPred_eq, mem_prod]
  rw [heq, Measure.volume_eq_prod, lintegral_indicator (hI.prod hJ)]
  apply setLIntegral_prod_symm
  exact (hg.comp (show Continuous (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) from
    Complex.equivRealProdCLM.symm.continuous).measurable).aemeasurable

 theorem planarSliceBox_fiber_restrict (I J B : Set ℝ) (y : ℝ) :
    planarSliceBox I (J ∩ B) ∩ Complex.im ⁻¹' {y} =
      if y ∈ B then planarSliceBox I J ∩ Complex.im ⁻¹' {y} else ∅ := by
  ext z
  by_cases hy : y ∈ B <;> simp only [hy, ite_true, if_true, ite_false, if_false]
  · simp only [planarSliceBox, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    aesop
  · simp only [planarSliceBox, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff,
      mem_empty_iff_false]
    aesop

variable {X : Type*} [MetricSpace X]

 theorem pathImageCount_planarSliceBox_restrict (π : ℂ → X) (γ : C(PathTime, X))
    (I J B : Set ℝ) (y : ℝ) :
    pathImageCount (π '' (planarSliceBox I (J ∩ B) ∩ Complex.im ⁻¹' {y})) γ =
      B.indicator (fun y => pathImageCount (π '' (planarSliceBox I J ∩ Complex.im ⁻¹' {y})) γ) y := by
  rw [planarSliceBox_fiber_restrict]
  by_cases hy : y ∈ B <;> simp [hy, pathImageCount]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SliceMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability from almost-everywhere continuous horizontal sections
and measurable vertical sections on a dense set. Finite simple sampling
provides the measurable approximants. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {A B : Type*} [MetricSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A] [Nonempty A] [MeasurableSpace B]

theorem aestronglyMeasurable_of_dense_measurable_slices
    (μ : Measure A) (ν : Measure B) [SFinite ν] (f : A × B → ℝ)
    (D : Set A) (hD : Dense D)
    (hvertical : ∀x ∈ D, Measurable fun y => f (x, y))
    (hhorizontal : ∀ᵐ y ∂ν, Continuous fun x => f (x, y)) :
    AEStronglyMeasurable f (μ.prod ν) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hD.nonempty
  let q (n : ℕ) : SimpleFunc A A := SimpleFunc.approxOn id measurable_id D x₀ hx₀ n
  have hq (n : ℕ) (x : A) : q n x ∈ D := SimpleFunc.approxOn_mem measurable_id hx₀ n x
  let F (n : ℕ) (p : A × B) := f (q n p.1, p.2)
  have hF (n : ℕ) : Measurable (F n) := by
    let Q := {x : A // x ∈ (q n).range}
    let q' : A → Q := fun x => ⟨q n x, (q n).mem_range_self x⟩
    have hq' : Measurable q' := (q n).measurable.subtype_mk
    have hv : Measurable (fun p : Q × B => f (p.1.val, p.2)) := by
      apply measurable_from_prod_countable_right
      intro x
      apply hvertical x.val
      obtain ⟨a, ha⟩ := SimpleFunc.mem_range.mp x.property
      exact ha ▸ hq n a
    exact hv.comp ((hq'.comp measurable_fst).prodMk measurable_snd)
  apply aestronglyMeasurable_of_tendsto_ae (f := F) atTop
    (fun n => (hF n).stronglyMeasurable.aestronglyMeasurable)
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hhorizontal] with p hp
  exact hp.tendsto p.1 |>.comp (SimpleFunc.tendsto_approxOn measurable_id hx₀ (hD p.1))

theorem aestronglyMeasurable_of_ae_continuous_slices
    [TopologicalSpace B] [BorelSpace B]
    (μ : Measure A) [μ.IsOpenPosMeasure] (ν : Measure B) [SFinite ν]
    (f : A × B → ℝ)
    (hvertical : ∀ᵐ x ∂μ, Continuous fun y => f (x, y))
    (hhorizontal : ∀ᵐ y ∂ν, Continuous fun x => f (x, y)) :
    AEStronglyMeasurable f (μ.prod ν) := by
  apply aestronglyMeasurable_of_dense_measurable_slices μ ν f
    {x | Continuous fun y => f (x, y)} (μ.dense_of_ae hvertical)
  · intro x hx
    exact hx.measurable
  · exact hhorizontal

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RectangleMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local ACL gives a measurable representative on the open rectangle.
This avoids any analyticity assumption on the finite-chain infimum. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem aestronglyMeasurable_on_rectangle_of_ACL
    (f : ℝ × ℝ → ℝ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hh : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b)
    (hv : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d) :
    AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)) := by
  let U := Ioo a b
  let V := Ioo c d
  let μ : Measure U := volume.comap ((↑) : U → ℝ)
  let ν : Measure V := volume.comap ((↑) : V → ℝ)
  obtain ⟨u, hau, hub⟩ := exists_between hab
  let : Nonempty U := ⟨⟨u, hau, hub⟩⟩
  let : μ.IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume isOpen_Ioo.isOpenEmbedding_subtypeVal
  have hμuniv : μ univ = volume U := by
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioo).comap_apply]
    simp only [image_univ, Subtype.range_coe]
    rfl
  have hνuniv : ν univ = volume V := by
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioo).comap_apply]
    simp only [image_univ, Subtype.range_coe]
    rfl
  let : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact measure_Ioo_lt_top⟩
  let : IsFiniteMeasure ν := ⟨by rw [hνuniv]; exact measure_Ioo_lt_top⟩
  have hhv : ∀ᵐ y ∂ν, Continuous fun x : U => f (x.val, y.val) := by
    have h := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hh
    have h' : ∀ᵐ y : V ∂ν, AbsolutelyContinuousOnInterval (fun x => f (x, y.val)) a b :=
      (ae_restrict_iff_subtype (s := V) measurableSet_Ioo).mp h
    filter_upwards [h'] with y hy
    have hc : ContinuousOn (fun x => f (x, y.val)) (Icc a b) := by
      simpa only [uIcc_of_le hab.le] using hy.continuousOn
    exact (hc.mono Ioo_subset_Icc_self).domRestrict
  have hvh : ∀ᵐ x ∂μ, Continuous fun y : V => f (x.val, y.val) := by
    have h := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hv
    have h' : ∀ᵐ x : U ∂μ, AbsolutelyContinuousOnInterval (fun y => f (x.val, y)) c d :=
      (ae_restrict_iff_subtype (s := U) measurableSet_Ioo).mp h
    filter_upwards [h'] with x hx
    have hc : ContinuousOn (fun y => f (x.val, y)) (Icc c d) := by
      simpa only [uIcc_of_le hcd.le] using hx.continuousOn
    exact (hc.mono Ioo_subset_Icc_self).domRestrict
  have hF : AEStronglyMeasurable (fun p : U × V => f (p.1.val, p.2.val)) (μ.prod ν) :=
    aestronglyMeasurable_of_ae_continuous_slices μ ν _ hvh hhv
  have hmap : (μ.prod ν).map (Prod.map ((↑) : U → ℝ) ((↑) : V → ℝ)) =
      volume.restrict (Ioo a b ×ˢ Ioo c d) := by
    rw [← Measure.map_prod_map μ ν measurable_subtype_coe measurable_subtype_coe,
      map_comap_subtype_coe measurableSet_Ioo, map_comap_subtype_coe measurableSet_Ioo,
      Measure.prod_restrict]
    rfl
  rw [← hmap]
  exact ((MeasurableEmbedding.subtype_coe measurableSet_Ioo).prodMap
    (MeasurableEmbedding.subtype_coe measurableSet_Ioo)).aestronglyMeasurable_map_iff.mpr hF

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RectangleNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact rectangles form a neighborhood basis inside a planar open
set; countably many of their interiors suffice to patch measurability. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

namespace CircleDomainRigidity

theorem exists_closed_rectangle_inside_open
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {p : ℝ × ℝ} (hp : p ∈ U) :
    ∃a b c d : ℝ, a < b ∧ c < d ∧ p ∈ Ioo a b ×ˢ Ioo c d ∧
      Icc a b ×ˢ Icc c d ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  refine ⟨p.1 - ε/2, p.1 + ε/2, p.2 - ε/2, p.2 + ε/2,
    by linarith, by linarith, ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ?_⟩
  intro q hq
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> apply abs_lt.mpr
  · constructor <;> linarith [hq.1.1, hq.1.2]
  · constructor <;> linarith [hq.2.1, hq.2.2]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LogarithmicRectangleCover
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the nested rectangular lift charts and subordinate smooth
partition used to smooth the mean index. The logarithmic lifts come from
the actual covering map, not additional hypotheses. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem exists_logarithmic_rectangle_data
    {D : Set ℂ} (hD : IsOpen D) (w : ℂ → ℂ) (hw : ContinuousOn w D)
    (hw0 : ∀ z ∈ D, w z ≠ 0) (hw1 : ∀ z ∈ D, ‖w z‖ ≤ 1)
    {x : ℂ} (hx : x ∈ D) :
    ∃ a₀ a b b₀ c₀ c d d₀ : ℝ, ∃ Ψ : ℂ → ℂ,
      a₀ < a ∧ a < b ∧ b < b₀ ∧ c₀ < c ∧ c < d ∧ d < d₀ ∧
      x ∈ planarSliceBox (Ioo a b) (Ioo c d) ∧
      planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀) ⊆ D ∧
      ContinuousOn Ψ (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)) ∧
      (∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀), 0 ≤ (Ψ z).im) ∧
      ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀), diskRayProjection (Ψ z) = w z := by
  obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.mp hD x hx
  obtain ⟨Ψ, hΨ, hpos, hproj⟩ := exists_logarithmic_disk_lift_ball w hr
    (hw.mono hrD) (fun z hz => hw0 z (hrD hz)) (fun z hz => hw1 z (hrD hz))
  have hO : IsOpen (Complex.equivRealProdCLM '' ball x r) :=
    Complex.equivRealProdCLM.toHomeomorph.isOpenMap _ isOpen_ball
  obtain ⟨a₀, b₀, c₀, d₀, hab, hcd, hp, hrect⟩ :=
    exists_closed_rectangle_inside_open hO (mem_image_of_mem _ (mem_ball_self hr))
  change x.re ∈ Ioo a₀ b₀ ∧ x.im ∈ Ioo c₀ d₀ at hp
  have hrect' : planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀) ⊆ ball x r := by
    intro z hz
    have hz' : Complex.equivRealProdCLM z ∈ Icc a₀ b₀ ×ˢ Icc c₀ d₀ := hz
    obtain ⟨y, hy, hyz⟩ := hrect hz'
    exact Complex.equivRealProdCLM.injective hyz ▸ hy
  refine ⟨a₀, (a₀ + x.re) / 2, (x.re + b₀) / 2, b₀,
    c₀, (c₀ + x.im) / 2, (x.im + d₀) / 2, d₀, Ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hrect'.trans hrD, hΨ.mono hrect', ?_, ?_⟩
  · linarith [hp.1.1]
  · linarith
  · linarith [hp.1.2]
  · linarith [hp.2.1]
  · linarith
  · linarith [hp.2.2]
  · exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  · exact fun z hz => hpos z (hrect' hz)
  · exact fun z hz => hproj z (hrect' hz)

 theorem exists_logarithmic_rectangle_partition
    (D : TopologicalSpace.Opens ℂ) (w : ℂ → ℂ) (hw : ContinuousOn w D)
    (hw0 : ∀ z ∈ D, w z ≠ 0) (hw1 : ∀ z ∈ D, ‖w z‖ ≤ 1) :
    let Ω : TopologicalSpace.Opens EuclideanPlane :=
      ⟨complexPlaneCoordinates ⁻¹' D, D.isOpen.preimage complexPlaneCoordinates.continuous⟩
    ∃ (ι : Type) (_ : Countable ι) (ρ : OpenPlanePartition Ω ι)
      (a₀ a b b₀ c₀ c d d₀ : ι → ℝ) (Ψ : ι → ℂ → ℂ),
      (∀ j, a₀ j < a j ∧ a j < b j ∧ b j < b₀ j ∧
        c₀ j < c j ∧ c j < d j ∧ d j < d₀ j) ∧
      (∀ j, planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)) ⊆ D) ∧
      (∀ j, ContinuousOn (Ψ j) (planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)))) ∧
      (∀ j z, z ∈ planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)) → 0 ≤ (Ψ j z).im) ∧
      (∀ j z, z ∈ planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)) →
        diskRayProjection (Ψ j z) = w z) ∧
      ∀ j, tsupport (ρ.weight j) ⊆
        euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (d j)) := by
  let Ω : TopologicalSpace.Opens EuclideanPlane :=
    ⟨complexPlaneCoordinates ⁻¹' D, D.isOpen.preimage complexPlaneCoordinates.continuous⟩
  choose a₀ a b b₀ c₀ c d d₀ Ψ ha hab hb hc hcd hd hp hrect hΨ hpos hproj using
    fun x : Ω => exists_logarithmic_rectangle_data D.isOpen w hw hw0 hw1 x.property
  let V : Ω → Set Ω := fun x => (fun y : Ω => euclideanPlaneCoordinates y) ⁻¹'
    (Ioo (a x) (b x) ×ˢ Ioo (c x) (d x))
  have hV (x : Ω) : V x ∈ 𝓝 x := by
    apply IsOpen.mem_nhds
    · exact (isOpen_Ioo.prod isOpen_Ioo).preimage
        (euclideanPlaneCoordinates.continuous.comp continuous_subtype_val)
    · exact hp x
  obtain ⟨ι, hι, ρ, center, hsub⟩ := exists_openPlanePartition Ω V hV
  refine ⟨ι, hι, ρ, a₀ ∘ center, a ∘ center, b ∘ center, b₀ ∘ center,
    c₀ ∘ center, c ∘ center, d ∘ center, d₀ ∘ center, Ψ ∘ center,
    (fun j => ⟨ha (center j), hab (center j), hb (center j),
      hc (center j), hcd (center j), hd (center j)⟩),
    (fun j => hrect (center j)), (fun j => hΨ (center j)),
    (fun j => hpos (center j)), (fun j => hproj (center j)), ?_⟩
  intro j x hx
  obtain ⟨y, hy, rfl⟩ := hsub j hx
  exact hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_HorizontalMeanIndexBound
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a physical horizontal segment, a local logarithmic lift of the
actual mean index is bounded by the original-law intersection count. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
 theorem pathImageCount_mono_set {S T : Set X} (h : S ⊆ T) (γ : C(PathTime, X)) :
    pathImageCount S γ ≤ pathImageCount T γ := by
  unfold pathImageCount
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : z ∈ range γ ∩ S
  · simp only [hz, show z ∈ range γ ∩ T from ⟨hz.1, h hz.2⟩, ite_true, if_true, le_refl]
  · simp only [hz, ite_false, if_false, zero_le]

omit [BorelSpace C(PathTime, X)] in
 theorem meanIndex_horizontal_segment_bound
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (Q : C(ℂ, X)) (I J : Set ℝ)
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox I J))
    (hpos : ∀ z ∈ planarSliceBox I J, 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox I J, diskRayProjection (Ψ z) = F (Q z))
    (v : ℂ → ℝ) (hv : ∀ z (hz : z ∈ planarSliceBox I J),
      v z = meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) ⟨Ψ z, hpos z hz⟩)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ Q '' planarSliceBox I J))
    (hinj : InjOn (F ∘ Q) (planarSliceBox I J))
    {x y s : ℝ} (hxy : x < y) (hI : Icc x y ⊆ I) (hs : s ∈ J) :
    ENNReal.ofReal |v ⟨y, s⟩ - v ⟨x, s⟩| ≤
      ∫⁻ γ : A, pathImageCount
        (Q '' (planarSliceBox (Icc x y) J ∩ Complex.im ⁻¹' {s})) γ.val ∂(η : Measure A) := by
  let β : C(PathTime, ℂ) := ⟨fun t => ⟨realIntervalPath x y t, s⟩,
    Complex.equivRealProdCLM.symm.continuous.comp
      ((realIntervalPath x y).continuous.prodMk continuous_const)⟩
  have hβ (t : PathTime) : β t ∈ planarSliceBox I J :=
    ⟨hI (realIntervalPath_mem hxy.le t), hs⟩
  let α := Q.comp β
  let δ : C(PathTime, ℂ) := ⟨Ψ ∘ β, hΨ.comp_continuous β.continuous hβ⟩
  have hδ (t : PathTime) : 0 ≤ (δ t).im := hpos (β t) (hβ t)
  have hδproj (t : PathTime) : diskRayProjection (δ t) = F (α t) :=
    hproj (β t) (hβ t)
  have hβinj : Injective β := by
    intro t u he
    exact (realIntervalPath_antilipschitz hxy.ne).injective (congrArg Complex.re he)
  have hδinj : Injective (diskRayProjection ∘ δ) := by
    intro t u he
    apply hβinj
    apply hinj (hβ t) (hβ u)
    exact (hδproj t).symm.trans (he.trans (hδproj u))
  have hα : range α ⊆ Q '' planarSliceBox I J := by
    rintro _ ⟨t, rfl⟩
    exact ⟨β t, hβ t, rfl⟩
  have hb := meanGeometricIndex_mapped_difference_le_intersections hsch hsep A K hK hKS η F f hf
    hmap α δ hδ hδproj hδinj (fun γ => (hF γ).mono (union_subset_union Subset.rfl hα))
  have hx : (⟨x, s⟩ : ℂ) ∈ planarSliceBox I J := ⟨hI ⟨le_rfl, hxy.le⟩, hs⟩
  have hy : (⟨y, s⟩ : ℂ) ∈ planarSliceBox I J := ⟨hI ⟨hxy.le, le_rfl⟩, hs⟩
  have h0 : δ 0 = Ψ ⟨x, s⟩ := by
    change Ψ ⟨realIntervalPath x y ⊥, s⟩ = _
    rw [realIntervalPath_zero]
  have h1 : δ 1 = Ψ ⟨y, s⟩ := by
    change Ψ ⟨realIntervalPath x y ⊤, s⟩ = _
    rw [realIntervalPath_one]
  have he0 : (⟨δ 0, hδ 0⟩ : ClosedUpperHalfPlane) = ⟨Ψ ⟨x, s⟩, hpos _ hx⟩ := Subtype.ext h0
  have he1 : (⟨δ 1, hδ 1⟩ : ClosedUpperHalfPlane) = ⟨Ψ ⟨y, s⟩, hpos _ hy⟩ := Subtype.ext h1
  rw [he0, he1, ← hv _ hx, ← hv _ hy] at hb
  apply hb.trans
  apply lintegral_mono
  intro γ
  apply pathImageCount_mono_set
  rintro _ ⟨t, rfl⟩
  exact ⟨β t, ⟨⟨realIntervalPath_mem hxy.le t, hs⟩, rfl⟩, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_IncrementDerivativeBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increment domination passes to derivatives. The integral criterion
then yields the linewise weak-gradient bound used by the barrier. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem abs_derivative_le_of_increment_domination
    {f F : ℝ → ℝ} {x f' F' : ℝ}
    (hf : HasDerivAt f f' x) (hF : HasDerivAt F F' x)
    (h : ∀ᶠ y in 𝓝 x, |f y - f x| ≤ |F y - F x|) : |f'| ≤ |F'| := by
  apply le_of_tendsto_of_tendsto hf.tendsto_slope.abs hF.tendsto_slope.abs
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with y hy
  simp only [slope, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)

theorem ae_abs_deriv_le_of_integral_bound
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b)
    (hgnonneg : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ g x)
    (hbound : ∀x ∈ Icc a b, ∀y ∈ Icc a b,
      |f x - f y| ≤ ∫t in uIoc x y, g t) :
    ∀ᵐ x ∂volume.restrict (Icc a b), |deriv f x| ≤ g x := by
  have hac : AbsolutelyContinuousOnInterval f a b :=
    absolutelyContinuousOnInterval_of_integral_bound hg (by
      simpa only [uIcc_of_le hab, Real.dist_eq] using hbound)
  have hd := hac.ae_differentiableAt
  have hH := hg.ae_hasDerivAt_integral
  have hi : ∀ᵐ x ∂volume.restrict (Icc a b), x ∈ Ioo a b := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff], show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff]] with x hxa hxb hx
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_of_ae hH, hgnonneg, hi] with x hdx hHx hpos hx
  have hdx' : DifferentiableAt ℝ f x := hdx (by simpa only [uIcc_of_le hab] using ⟨hx.1.le, hx.2.le⟩)
  have hHx' := hHx (by simpa only [uIcc_of_le hab] using (show x ∈ Icc a b from ⟨hx.1.le, hx.2.le⟩))
    a left_mem_uIcc
  have hdom : ∀ᶠ y in 𝓝 x, |f y - f x| ≤
      |(∫t in a..y, g t) - ∫t in a..x, g t| := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    apply (hbound y ⟨hy.1.le, hy.2.le⟩ x ⟨hx.1.le, hx.2.le⟩).trans
    rw [intervalIntegral.integral_interval_sub_left
      (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc
        (uIcc_subset_uIcc left_mem_uIcc (by simpa only [uIcc_of_le hab] using (show y ∈ Icc a b from ⟨hy.1.le, hy.2.le⟩)))))
      (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc
        (uIcc_subset_uIcc left_mem_uIcc (by simpa only [uIcc_of_le hab] using (show x ∈ Icc a b from ⟨hx.1.le, hx.2.le⟩))))),
      intervalIntegral.abs_intervalIntegral_eq]
    simpa only [uIoc_comm x y] using (le_abs_self (∫t in uIoc y x, g t))
  simpa only [abs_of_nonneg hpos] using
    abs_derivative_le_of_increment_domination hdx'.hasDerivAt hHx' hdom

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LineLIntegralDerivativeBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path inequality is naturally extended-valued. On each finite
slice it bounds the ordinary derivative by the real density. -/

open Set Filter MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity

theorem ae_abs_deriv_le_of_lintegral_bound
    {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞} {a b : ℝ} (hab : a ≤ b)
    (hg : Measurable g) (hfinite : (∫⁻t in Icc a b, g t) < ∞)
    (hbound : ∀x ∈ Icc a b, ∀y ∈ Icc a b,
      ENNReal.ofReal |f x - f y| ≤ ∫⁻t in uIoc x y, g t) :
    ∀ᵐ x ∂volume.restrict (Icc a b), |deriv f x| ≤ (g x).toReal := by
  have hgint : Integrable (fun t => (g t).toReal) (volume.restrict (Icc a b)) :=
    integrable_toReal_of_lintegral_ne_top hg.aemeasurable hfinite.ne
  apply ae_abs_deriv_le_of_integral_bound hab
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hgint)
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  intro x hx y hy
  have hsub : uIoc x y ⊆ Icc a b :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc hx hy)
  have hfin : (∫⁻t in uIoc x y, g t) < ∞ :=
    (lintegral_mono_set hsub).trans_lt hfinite
  have hreal : |f x - f y| ≤ (∫⁻t in uIoc x y, g t).toReal := by
    exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 (hbound x hx y hy)
  rw [integral_toReal hg.aemeasurable (ae_lt_top hg hfin.ne)]
  exact hreal

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RationalIntervalControl
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on rational intervals extend to all compact interior intervals
by continuity from above. No pointwise continuity of a density is required. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

 theorem le_measure_Icc_of_rational_enclosures (μ : Measure ℝ)
    {a b x y : ℝ} (hax : a < x) (hyb : y < b)
    (hfin : μ (Icc a b) < ∞) (c : ℝ≥0∞)
    (h : ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < x →
      y < (q : ℝ) → (q : ℝ) < b → c ≤ μ (Icc (p : ℝ) q)) :
    c ≤ μ (Icc x y) := by
  obtain ⟨p, hp, hpmem, hplim⟩ :=
    Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt Rat.cast_mono hax
  obtain ⟨q, hq, hqmem, hqlim⟩ :=
    Rat.denseRange_cast.exists_seq_strictAnti_tendsto_of_lt Rat.cast_mono hyb
  let V : ℕ → Set ℝ := fun n => Icc (p n : ℝ) (q n : ℝ)
  have hanti : Antitone V := fun i j hij =>
    Icc_subset_Icc (Rat.cast_mono (hp.monotone hij)) (Rat.cast_mono (hq.antitone hij))
  have hinter : (⋂ n, V n) = Icc x y := by
    ext z
    constructor
    · intro hz
      exact ⟨le_of_tendsto hplim (Eventually.of_forall fun n => (mem_iInter.mp hz n).1),
        ge_of_tendsto hqlim (Eventually.of_forall fun n => (mem_iInter.mp hz n).2)⟩
    · intro hz
      exact mem_iInter.mpr fun n =>
        ⟨(hpmem n).2.le.trans hz.1, hz.2.trans (hqmem n).1.le⟩
  have hVfin : μ (V 0) ≠ ∞ :=
    ((measure_mono (Icc_subset_Icc (hpmem 0).1.le (hqmem 0).2.le)).trans_lt hfin).ne
  rw [← hinter, hanti.measure_iInter (fun _ => measurableSet_Icc.nullMeasurableSet) ⟨0, hVfin⟩]
  exact le_iInf fun n => h (p n) (q n) (hpmem n).1 (hpmem n).2 (hqmem n).1 (hqmem n).2

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RationalAbsoluteContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many rational interval estimates suffice for local absolute
continuity. This is the passage needed after the common full-measure set
of physical slice bounds has been selected. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

 theorem lintegral_bound_of_rational_enclosures {g : ℝ → ℝ≥0∞}
    {a b x y : ℝ} (hax : a < x) (hyb : y < b)
    (hfin : (∫⁻ t in Icc a b, g t) < ∞) (c : ℝ≥0∞)
    (h : ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < x →
      y < (q : ℝ) → (q : ℝ) < b → c ≤ ∫⁻ t in Icc (p : ℝ) q, g t) :
    c ≤ ∫⁻ t in Icc x y, g t := by
  have hμfin : (volume.withDensity g) (Icc a b) < ∞ := by
    rwa [withDensity_apply _ measurableSet_Icc]
  have hh := le_measure_Icc_of_rational_enclosures (volume.withDensity g) hax hyb hμfin c
    (fun p q hp hpx hyq hq => by
      rw [withDensity_apply _ measurableSet_Icc]
      exact h p q hp hpx hyq hq)
  rwa [withDensity_apply _ measurableSet_Icc] at hh

 theorem locally_absolutelyContinuous_of_rational_bounds
    {X : Type*} [PseudoMetricSpace X] (f : ℝ → X) (g : ℝ → ℝ≥0∞)
    {a b c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (hfin : (∫⁻ t in Icc a b, g t) < ∞)
    (hbound : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x < y →
      ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < x →
        y < (q : ℝ) → (q : ℝ) < b →
          ENNReal.ofReal (dist (f x) (f y)) ≤ ∫⁻ t in Icc (p : ℝ) q, g t) :
    AbsolutelyContinuousOnInterval f c d := by
  have hsub : Icc c d ⊆ Ioo a b := fun _ hx => ⟨hac.trans_le hx.1, hx.2.trans_lt hdb⟩
  have hcdab : Icc c d ⊆ Icc a b := Icc_subset_Icc hac.le hdb.le
  have hfin' : (∫⁻ t in uIoc c d, g t) < ∞ := by
    apply (lintegral_mono_set ?_).trans_lt hfin
    rw [uIoc_of_le hcd]
    exact Ioc_subset_Icc_self.trans hcdab
  apply absolutelyContinuousOnInterval_of_lintegral_bound hfin'
  intro x hx y hy
  rw [uIcc_of_le hcd] at hx hy
  have hseg (u v : ℝ) (hu : u ∈ Icc c d) (hv : v ∈ Icc c d) (huv : u < v) :
      ENNReal.ofReal (dist (f u) (f v)) ≤ ∫⁻ t in uIoc u v, g t := by
    rw [uIoc_of_le huv.le]
    have he : (∫⁻ t in Ioc u v, g t) = ∫⁻ t in Icc u v, g t :=
      setLIntegral_congr Ioc_ae_eq_Icc
    rw [he]
    exact lintegral_bound_of_rational_enclosures (hsub hu).1 (hsub hv).2 hfin _
      (hbound u (hsub hu) v (hsub hv) huv)
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact hseg x y hx hy hxy
  · subst y
    simp only [dist_self, ENNReal.ofReal_zero, zero_le]
  · simpa only [dist_comm, uIoc_comm y x] using hseg y x hy hx hyx

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RationalLineDerivative
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same rational interval estimates control the almost-everywhere
ordinary derivative by the actual measurable line density. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

 theorem locally_ae_abs_deriv_le_of_rational_bounds
    (f : ℝ → ℝ) (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    {a b c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (hfin : (∫⁻ t in Icc a b, g t) < ∞)
    (hbound : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x < y →
      ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < x →
        y < (q : ℝ) → (q : ℝ) < b →
          ENNReal.ofReal (dist (f x) (f y)) ≤ ∫⁻ t in Icc (p : ℝ) q, g t) :
    ∀ᵐ x ∂volume.restrict (Icc c d), |deriv f x| ≤ (g x).toReal := by
  have hsub : Icc c d ⊆ Ioo a b := fun _ hx => ⟨hac.trans_le hx.1, hx.2.trans_lt hdb⟩
  have hcdab : Icc c d ⊆ Icc a b := Icc_subset_Icc hac.le hdb.le
  apply ae_abs_deriv_le_of_lintegral_bound hcd hg ((lintegral_mono_set hcdab).trans_lt hfin)
  intro x hx y hy
  have hseg (u v : ℝ) (hu : u ∈ Icc c d) (hv : v ∈ Icc c d) (huv : u < v) :
      ENNReal.ofReal (dist (f u) (f v)) ≤ ∫⁻ t in uIoc u v, g t := by
    rw [uIoc_of_le huv.le]
    have he : (∫⁻ t in Ioc u v, g t) = ∫⁻ t in Icc u v, g t :=
      setLIntegral_congr Ioc_ae_eq_Icc
    rw [he]
    exact lintegral_bound_of_rational_enclosures (hsub hu).1 (hsub hv).2 hfin _
      (hbound u (hsub hu) v (hsub hv) huv)
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · simpa only [Real.dist_eq] using hseg x y hx hy hxy
  · subst y
    simp only [sub_self, abs_zero, ENNReal.ofReal_zero, zero_le]
  · simpa only [Real.dist_eq, abs_sub_comm, uIoc_comm y x] using hseg y x hy hx hyx

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanIndexHorizontalACL
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual locally lifted mean index is absolutely continuous on
almost every physical horizontal line. Rational slice estimates are
simultaneous, and continuity from above supplies arbitrary endpoints. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
 theorem meanIndex_horizontal_ACL_derivative
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (Q : C(ℂ, X)) {a b c d : ℝ} (J : Set ℝ) (hJ : MeasurableSet J)
    (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox (Icc a b) J))
    (hpos : ∀ z ∈ planarSliceBox (Icc a b) J, 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox (Icc a b) J, diskRayProjection (Ψ z) = F (Q z))
    (v : ℂ → ℝ) (hv : ∀ z (hz : z ∈ planarSliceBox (Icc a b) J),
      v z = meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) ⟨Ψ z, hpos z hz⟩)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ Q '' planarSliceBox (Icc a b) J))
    (hinj : InjOn (F ∘ Q) (planarSliceBox (Icc a b) J))
    (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ)
    (hfin : (∫⁻ z in planarSliceBox (Icc a b) J, ρ z) < ∞)
    (hcounts : ∀ᵐ y ∂volume, ∀ p q : ℚ, Icc (p : ℝ) q ⊆ Icc a b →
      (∫⁻ γ : A, pathImageCount
        (Q '' (planarSliceBox (Icc (p : ℝ) q) J ∩ Complex.im ⁻¹' {y})) γ.val ∂(η : Measure A)) ≤
        ∫⁻ x in Icc (p : ℝ) q, ρ ⟨x, y⟩) :
    ∀ᵐ y ∂volume.restrict J,
      AbsolutelyContinuousOnInterval (fun x => v ⟨x, y⟩) c d ∧
        (∀ᵐ x ∂volume.restrict (Icc c d),
          |deriv (fun t => v ⟨t, y⟩) x| ≤ (ρ ⟨x, y⟩).toReal) := by
  have hG : Measurable (fun y : ℝ => ∫⁻ x in Icc a b, ρ ⟨x, y⟩) :=
    (hρ.comp (Complex.equivRealProdCLM.symm.continuous.comp continuous_swap).measurable).lintegral_prod_right'
  have hfinite : ∀ᵐ y ∂volume.restrict J, (∫⁻ x in Icc a b, ρ ⟨x, y⟩) < ∞ := by
    apply ae_lt_top hG
    rw [← lintegral_planarSliceBox measurableSet_Icc hJ ρ hρ]
    exact hfin.ne
  filter_upwards [ae_restrict_mem hJ, hfinite, ae_mono Measure.restrict_le_self hcounts]
    with s hs hsfin hscount
  have hlocal : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x < y →
      ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < x → y < (q : ℝ) → (q : ℝ) < b →
        ENNReal.ofReal (dist (v ⟨x, s⟩) (v ⟨y, s⟩)) ≤ ∫⁻ t in Icc (p : ℝ) q, ρ ⟨t, s⟩ := by
    intro x hx y hy hxy p q hp hpx hyq hq
    have hIxy : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1.le hy.2.le
    have hIpq : Icc (p : ℝ) q ⊆ Icc a b := Icc_subset_Icc hp.le hq.le
    have hxy_pq : Icc x y ⊆ Icc (p : ℝ) q := Icc_subset_Icc hpx.le hyq.le
    have hb := meanIndex_horizontal_segment_bound hsch hsep A K hK hKS η F f hf hmap
      Q (Icc a b) J Ψ hΨ hpos hproj v hv hF hinj hxy hIxy hs
    have hwide : ENNReal.ofReal |v ⟨y, s⟩ - v ⟨x, s⟩| ≤
        ∫⁻ γ : A, pathImageCount
          (Q '' (planarSliceBox (Icc (p : ℝ) q) J ∩ Complex.im ⁻¹' {s})) γ.val ∂(η : Measure A) :=
      hb.trans (lintegral_mono fun γ => pathImageCount_mono_set
        (image_mono (inter_subset_inter_left _ (planarSliceBox_mono hxy_pq Subset.rfl))) γ.val)
    simpa only [Real.dist_eq, abs_sub_comm] using hwide.trans (hscount p q hIpq)
  exact ⟨locally_absolutelyContinuous_of_rational_bounds (fun x => v ⟨x, s⟩)
      (fun x => ρ ⟨x, s⟩) hac hcd hdb hsfin hlocal,
    locally_ae_abs_deriv_le_of_rational_bounds (fun x => v ⟨x, s⟩)
      (fun x => ρ ⟨x, s⟩)
      (hρ.comp (Complex.equivRealProdCLM.symm.continuous.comp
        (continuous_id.prodMk continuous_const)).measurable) hac hcd hdb hsfin hlocal⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathHausdorffLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every continuous path has image Hausdorff length at most its metric
variation. Small dyadic images supply the covers in the definition. -/

open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_small_dyadic_images {X : Type*} [MetricSpace X]
    (γ : C(PathTime, X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ i : Fin (2 ^ n),
      ediam (γ '' Icc (dyadicLeft n i) (dyadicRight n i)) ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) ε hε
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hz : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hp)
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hz).2 δ hδ).exists
  refine ⟨n, fun i => ediam_le ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hd ((dyadicCell_dist_le n i hs ht).trans_lt hn)).le

theorem path_hausdorff_length_le_variation {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (γ : C(PathTime, X)) :
    (μH[1] : Measure X) (range γ) ≤ eVariationOn γ univ := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r] <;> positivity
  choose k hk using fun n => exists_small_dyadic_images γ (hr n)
  let A : ∀ n : ℕ, Fin (2 ^ k n) → Set X :=
    fun n i => γ '' Icc (dyadicLeft (k n) i) (dyadicRight (k n) i)
  have hcover (n : ℕ) : range γ ⊆ ⋃ i, A n i := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := exists_dyadicCell_mem (k n) t
    exact mem_iUnion.mpr ⟨i, t, hi, rfl⟩
  have hrad : Tendsto (fun n => ENNReal.ofReal (r n)) atTop (𝓝 0) := by
    simpa only [r, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  apply (Measure.hausdorffMeasure_le_liminf_sum 1 (range γ)
    (fun n => ENNReal.ofReal (r n)) hrad A
    (Eventually.of_forall hk) (Eventually.of_forall hcover)).trans
  apply liminf_le_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [] with n
  simp only [ENNReal.rpow_one]
  calc
    ∑ i, ediam (A n i) ≤
        ∑ i : Fin (2 ^ k n), eVariationOn γ (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i)) := by
      apply Finset.sum_le_sum
      intro i _
      apply ediam_le
      rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
      exact eVariationOn.edist_le γ hs ht
    _ = _ := sum_dyadic_variations γ (k n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathImageOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Hausdorff measure of a path image counts each point once; arclength
occupation counts every traversal. Compact time sets and fine dyadic covers
prove the resulting measure domination without an injectivity assumption. -/

open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

lemma eventually_dyadic_cells_inside_compact {K V : Set PathTime}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 ^ n),
      (Icc (dyadicLeft n i) (dyadicRight n i) ∩ K).Nonempty →
      Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V := by
  obtain ⟨δ, hδ, hd⟩ := hK.exists_thickening_subset_open hV hKV
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hz : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hp
  filter_upwards [(tendsto_order.mp hz).2 δ hδ] with n hn i hi t ht
  obtain ⟨s, hs, hsK⟩ := hi
  exact hd (mem_thickening_iff.mpr ⟨s, hsK, (dyadicCell_dist_le n i ht hs).trans_lt hn⟩)

lemma exists_small_dyadic_images_ge {X : Type*} [MetricSpace X]
    (γ : C(PathTime, X)) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∀ i : Fin (2 ^ n),
      ediam (γ '' Icc (dyadicLeft n i) (dyadicRight n i)) ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) ε hε
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hz : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hp
  obtain ⟨n, hn, hN⟩ := (((tendsto_order.mp hz).2 δ hδ).and (eventually_ge_atTop N)).exists
  refine ⟨n, hN, fun i => ediam_le ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hd ((dyadicCell_dist_le n i hs ht).trans_lt hn)).le

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma path_hausdorff_image_compact_le_open (γ : RectifiablePath X)
    {K V : Set PathTime} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    (μH[1] : Measure X) (γ.val '' K) ≤ pathLengthMeasure γ V := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r] <;> positivity
  choose k hkn hk using fun n => exists_small_dyadic_images_ge γ.val (hr n) n
  let A : ∀ n : ℕ, Fin (2 ^ k n) → Set X :=
    fun n i => γ.val '' (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i) ∩ K)
  have hcover (n : ℕ) : γ.val '' K ⊆ ⋃ i, A n i := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨i, hi⟩ := exists_dyadicCell_mem (k n) t
    exact mem_iUnion.mpr ⟨i, t, ⟨hi, ht⟩, rfl⟩
  have hrad : Tendsto (fun n => ENNReal.ofReal (r n)) atTop (𝓝 0) := by
    simpa only [r, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hfine : ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 ^ k n),
      (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i) ∩ K).Nonempty →
      Icc (dyadicLeft (k n) i) (dyadicRight (k n) i) ⊆ V :=
    (tendsto_atTop_mono hkn tendsto_id).eventually
      (eventually_dyadic_cells_inside_compact hK hV hKV)
  apply (Measure.hausdorffMeasure_le_liminf_sum 1 (γ.val '' K)
    (fun n => ENNReal.ofReal (r n)) hrad A
    (Eventually.of_forall fun n i => (ediam_mono (image_mono inter_subset_left)).trans (hk n i))
    (Eventually.of_forall hcover)).trans
  apply liminf_le_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [hfine] with n hn
  simp only [ENNReal.rpow_one]
  calc
    ∑ i, ediam (A n i) ≤ ∑ i : Fin (2 ^ k n),
        (pathLengthMeasure γ).restrict (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i)) V := by
      apply Finset.sum_le_sum
      intro i _
      rw [Measure.restrict_apply hV.measurableSet]
      by_cases hi : (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i) ∩ K).Nonempty
      · rw [inter_eq_self_of_subset_right (hn i hi), pathLengthMeasure_Icc γ (dyadicLeft_le_right _ _)]
        apply ediam_le
        rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
        exact eVariationOn.edist_le γ.val hs.1 ht.1
      · have he : A n i = ∅ := by simp only [A, not_nonempty_iff_eq_empty.mp hi, image_empty]
        rw [he, ediam_empty]
        exact bot_le
    _ = pathLengthMeasure γ V := by
      rw [← Measure.finsetSum_apply, sum_dyadic_restrict]

lemma path_hausdorff_image_compact_le_length (γ : RectifiablePath X)
    {K : Set PathTime} (hK : IsCompact K) :
    (μH[1] : Measure X) (γ.val '' K) ≤ pathLengthMeasure γ K := by
  rw [K.measure_eq_iInf_isOpen (pathLengthMeasure γ)]
  exact le_iInf fun V => le_iInf fun hKV => le_iInf fun hV =>
    path_hausdorff_image_compact_le_open γ hK hV hKV

/-- A curve's occupation dominates Hausdorff measure on its image, even
when the curve retraces itself. -/
theorem path_image_hausdorff_le_occupation (γ : RectifiablePath X) :
    (μH[1] : Measure X).restrict (range γ.val) ≤ pathOccupation γ := by
  let ν := (μH[1] : Measure X).restrict (range γ.val)
  have hfin : ν univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (path_hausdorff_length_le_variation γ.val).trans_lt (lt_top_iff_ne_top.mpr γ.property)
  let : IsFiniteMeasure ν := ⟨hfin⟩
  apply Measure.le_iff.mpr
  intro S hS
  change ν S ≤ pathOccupation γ S
  rw [hS.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top ν S)]
  apply iSup_le
  intro F
  apply iSup_le
  intro hFS
  apply iSup_le
  intro hF
  apply le_trans ?_ (measure_mono hFS)
  change (μH[1] : Measure X).restrict (range γ.val) F ≤ pathOccupation γ F
  rw [Measure.restrict_apply hF.measurableSet, pathOccupation_apply γ hF.measurableSet]
  have he : F ∩ range γ.val = γ.val '' (γ.val ⁻¹' F) := by
    ext x
    simp only [mem_inter_iff, mem_range, mem_image, mem_preimage]
    aesop
  rw [he]
  exact path_hausdorff_image_compact_le_length γ (hF.preimage γ.val.continuous).isCompact

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalImageOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! General physical paths pay for the Hausdorff measure of their images.
Together with the opposite simple-arc bound this makes erasing loops decrease
physical occupation, including for arbitrary measurable densities. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma physicalSubpath_range (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X))
    {a b : PathTime} (hab : a ≤ b) (hγ : γ ∈ pathsInsideOn U a b) :
    range (physicalSubpath e hab ⟨γ, hγ⟩) =
      (physicalValue e y₀ ∘ γ) '' Icc a b := by
  have he : (physicalSubpath e hab ⟨γ, hγ⟩ : PathTime → Y) =
      (physicalValue e y₀ ∘ γ) ∘ timeClip a b := by
    funext t
    have ht : timeClip a b t ∈ Icc a b := by
      rw [← range_timeClip hab]
      exact mem_range_self t
    exact ((congrArg (fun f : C(PathTime, Y) => f t)
      (physicalSubpath_comp_clip e hab ⟨γ, hγ⟩)).symm).trans
        (physicalValue_subpath e y₀ hab ⟨γ, hγ⟩ ht).symm
  rw [he, range_comp, range_timeClip hab]

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma physicalStageImage_subset (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) (n : ℕ) :
    physicalStageImage e y₀ γ n ⊆ (physicalValue e y₀ ∘ γ) '' (γ ⁻¹' U) := by
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  split_ifs at hi with hgood
  · exact image_mono hgood hi
  · exact False.elim hi

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma monotone_physicalStageImage (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) :
    Monotone (physicalStageImage e y₀ γ) := by
  apply monotone_nat_of_le_succ
  intro n y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  split_ifs at hi with hgood
  · obtain ⟨t, ht, rfl⟩ := hi
    rw [dyadicCell_split] at ht
    rcases ht with ht | ht
    · apply mem_iUnion.mpr
      refine ⟨dyadicEven n i, ?_⟩
      have hc : γ ∈ pathsInsideOn U (dyadicLeft (n+1) (dyadicEven n i))
          (dyadicRight (n+1) (dyadicEven n i)) := by
        apply hgood.mono_left
        rw [dyadicCell_split n i]
        exact subset_union_left
      simp only [ite_eq_left hc]
      exact ⟨t, ht, rfl⟩
    · apply mem_iUnion.mpr
      refine ⟨dyadicOdd n i, ?_⟩
      have hc : γ ∈ pathsInsideOn U (dyadicLeft (n+1) (dyadicOdd n i))
          (dyadicRight (n+1) (dyadicOdd n i)) := by
        apply hgood.mono_left
        rw [dyadicCell_split n i]
        exact subset_union_right
      simp only [ite_eq_left hc]
      exact ⟨t, ht, rfl⟩
  · exact False.elim hi

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma iUnion_physicalStageImage (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : C(PathTime, X)) :
    (⋃ n, physicalStageImage e y₀ γ n) = (physicalValue e y₀ ∘ γ) '' (γ ⁻¹' U) := by
  apply Subset.antisymm (iUnion_subset (physicalStageImage_subset e y₀ γ))
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨p, hp⟩ := mem_iUnion.mp ((iUnion_insideDyadicCell (hU.preimage γ.continuous)).symm ▸ ht)
  apply mem_iUnion.mpr
  refine ⟨p.val.1, mem_iUnion.mpr ⟨p.val.2, ?_⟩⟩
  have hg : γ ∈ pathsInsideOn U (dyadicLeft p.val.1 p.val.2) (dyadicRight p.val.1 p.val.2) := p.property
  rw [ite_eq_left hg]
  exact ⟨t, hp, rfl⟩

lemma physicalStageImage_hausdorff_le (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    (μH[1] : Measure Y).restrict (physicalStageImage e y₀ γ.val n) ≤
      physicalStageOccupation e y₀ n γ.val := by
  unfold physicalStageImage physicalStageOccupation
  apply le_trans Measure.restrict_iUnion_le
  rw [Measure.sum_fintype]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · rw [ite_eq_left hi]
    have hr := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi] at hr ⊢
    rw [← physicalSubpath_range e y₀ γ.val (dyadicLeft_le_right n i) hi,
      rectifiableOccupationCode_eq hr]
    exact path_image_hausdorff_le_occupation ⟨_, hr⟩
  · rw [ite_eq_right hi, Measure.restrict_empty]
    exact bot_le

theorem physical_image_hausdorff_le_occupation (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    (μH[1] : Measure Y).restrict ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U)) ≤
      dyadicPhysicalOccupation e y₀ γ := by
  rw [← iUnion_physicalStageImage e hU y₀ γ.val]
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.restrict_iUnion_apply_eq_iSup (monotone_physicalStageImage e y₀ γ.val).directed_le hS,
    dyadicPhysicalOccupation_apply e y₀ γ hS]
  exact iSup_mono fun n => physicalStageImage_hausdorff_le e y₀ γ n S

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalOccupationCode
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel physical occupation on ordinary path space, with zero extension
off the finite-length paths. This lets measurable arc selection act directly
on path laws without introducing a new code law. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

lemma physicalOccupationCode_eq (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    physicalOccupationCode e y₀ γ.val = dyadicPhysicalOccupation e y₀ γ := by
  simp only [physicalOccupationCode, dite_eq_left γ.property]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

lemma measurable_physicalOccupationCode (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (physicalOccupationCode e y₀) := by
  have hm := (measurable_dyadicPhysicalOccupation e hU y₀).dite
    (show Measurable (fun _ => (0 : Measure Y)) from measurable_const)
    (measurableSet_finitePhysicalDomainLength e hU y₀)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext γ
  unfold physicalOccupationCode
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact (h₂ h₁).elim
  · exact (h₁ h₂).elim
  · rfl

lemma meanPhysicalOccupation_apply (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) {S : Set Y} (hS : MeasurableSet S) :
    meanPhysicalOccupation e y₀ μ S =
      ∫⁻ γ, physicalOccupationCode e y₀ γ S ∂(μ : Measure C(PathTime, X)) :=
  Measure.bind_apply hS (measurable_physicalOccupationCode e hU y₀).aemeasurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalSliceOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical occupation measure controls compact physical slices. A local inverse chart bound suffices; no regularity
of the Jordan coordinate change is used. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

omit [MeasurableSpace Y] [BorelSpace Y] in
 theorem physical_chart_image_subset (e : G ≃ₜ U) (y₀ : Y)
    (π : Y → X) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) {A : Set ℂ} (hA : MapsTo φ A G) (γ : C(PathTime, X)) :
    φ '' (A ∩ (π ∘ φ) ⁻¹' range γ) ⊆
      (physicalValue e y₀ ∘ γ) '' (γ ⁻¹' U) := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨t, ht⟩ := hz.2
  have hez := he ⟨φ z, hA hz.1⟩
  have htu : γ t ∈ U := by
    rw [ht]
    change π (φ z) ∈ U
    rw [← hez]
    exact (e ⟨φ z, hA hz.1⟩).property
  refine ⟨t, htu, ?_⟩
  change physicalValue e y₀ (γ t) = φ z
  rw [physicalValue, dite_eq_left htu]
  have heq : (⟨γ t, htu⟩ : U) = e ⟨φ z, hA hz.1⟩ :=
    Subtype.ext (ht.trans hez.symm)
  rw [heq, e.symm_apply_apply]

 theorem compact_chart_length_le_occupation (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) {A : Set ℂ} (hA : MapsTo φ A G)
    (j : Y → ℂ) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (hφA : MeasurableSet (φ '' A)) (γ : FinitePhysicalPath e y₀) :
    (μH[1] : Measure ℂ) (A ∩ (π ∘ φ) ⁻¹' range γ.val) ≤
      (B : ℝ≥0∞) * physicalOccupationCode e y₀ γ.val (φ '' A) := by
  let E := A ∩ (π ∘ φ) ⁻¹' range γ.val
  have hEA : E ⊆ A := inter_subset_left
  have hid : j '' (φ '' E) = E := by
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hj z (hEA hz)]
    · intro hw
      exact ⟨φ w, ⟨w, hw, rfl⟩, hj w (hEA hw)⟩
  calc
    (μH[1] : Measure ℂ) E = (μH[1] : Measure ℂ) (j '' (φ '' E)) := congrArg _ hid.symm
    _ ≤ (B : ℝ≥0∞) * (μH[1] : Measure Y) (φ '' E) := by
      simpa only [ENNReal.rpow_one] using
        (hB.mono (image_mono hEA)).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ (B : ℝ≥0∞) * physicalOccupationCode e y₀ γ.val (φ '' A) := by
      apply mul_le_mul' le_rfl
      rw [physicalOccupationCode_eq e y₀ γ]
      have hsub := physical_chart_image_subset e y₀ π he φ hA γ.val
      calc
        (μH[1] : Measure Y) (φ '' E) ≤ (μH[1] : Measure Y)
            ((φ '' A) ∩ ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U))) :=
          measure_mono (subset_inter (image_mono hEA) hsub)
        _ = ((μH[1] : Measure Y).restrict
            ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U))) (φ '' A) :=
          (Measure.restrict_apply hφA).symm
        _ ≤ _ := physical_image_hausdorff_le_occupation e hU y₀ γ _

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

 theorem mean_compactChartFiberCount_le_occupation
    (hcoarea : PlanarLipschitzFiberCoarea)
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A : Set ℂ} (hA : IsCompact A) (hAG : MapsTo φ A G)
    (j : Y → ℂ) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (K : Set C(PathTime, X)) (hK : ∀ γ ∈ K, Injective γ)
    (η : ProbabilityMeasure K)
    (hfinite : ∀ γ ∈ K, physicalDomainLength e y₀ γ < ∞)
    (L : ℝ≥0) (f : ℂ → ℝ) (hf : LipschitzWith L f) :
    (∫⁻ y, ∫⁻ γ : K, pathImageCount ((π ∘ φ) '' (A ∩ f ⁻¹' {y})) γ.val
      ∂(η : Measure K)) ≤
      (L : ℝ≥0∞) * B * meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (φ '' A) := by
  have hφA : MeasurableSet (φ '' A) := (hA.image hφ).measurableSet
  have hlen (γ : K) := compact_chart_length_le_occupation e hU y₀ π he φ hAG j hj B hB hφA
    ⟨γ.val, hfinite γ.val γ.property⟩
  have hfin (γ : K) : (μH[1] : Measure ℂ) (A ∩ (π ∘ φ) ⁻¹' range γ.val) < ∞ := by
    apply (hlen γ).trans_lt
    apply ENNReal.mul_lt_top ENNReal.coe_lt_top
    rw [physicalOccupationCode_eq e y₀ ⟨γ.val, hfinite γ.val γ.property⟩]
    exact lt_of_le_of_lt (measure_mono (subset_univ _))
      (by rw [dyadicPhysicalOccupation_univ]; exact hfinite γ.val γ.property)
  calc
    _ ≤ (L : ℝ≥0∞) * ∫⁻ γ : K, (μH[1] : Measure ℂ)
        (A ∩ (π ∘ φ) ⁻¹' range γ.val) ∂(η : Measure K) :=
      mean_compactPhysicalFiberCount_integral_le hcoarea (π ∘ φ) (hπ.comp hφ) hA K hK
        (η : Measure K) L f hf (Eventually.of_forall hfin)
    _ ≤ (L : ℝ≥0∞) * ∫⁻ γ : K,
        (B : ℝ≥0∞) * physicalOccupationCode e y₀ γ.val (φ '' A) ∂(η : Measure K) :=
      mul_le_mul' le_rfl (lintegral_mono hlen)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, mul_assoc,
        meanPhysicalOccupation_apply e hU y₀ _ hφA, ProbabilityMeasure.toMeasure_map,
        lintegral_map]
      · exact (Measure.measurable_coe hφA).comp (measurable_physicalOccupationCode e hU y₀)
      · exact measurable_subtype_coe

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalBallArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem sphericalAreaDensity_le_four (z : ℂ) : sphericalAreaDensity z ≤ 4 := by
  rw [sphericalAreaDensity, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ ^ 2)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SphericalSliceDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical occupation density gives a square-integrable planar
slice density in every finite inverse-chart neighborhood. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_6
theorem sphericalArea_setLIntegral_coe {A : Set ℂ} (hA : MeasurableSet A)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p in ((↑) : ℂ → Sphere) '' A, g p ∂sphericalArea) =
      ∫⁻ z in A, ENNReal.ofReal (sphericalAreaDensity z) * g (z : Sphere) := by
  have hm : MeasurableSet (((↑) : ℂ → Sphere) '' A) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hA
  rw [← lintegral_indicator hm, lintegral_sphericalArea _ (hg.indicator hm),
    ← lintegral_indicator hA]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ A <;> simp [hz]

 theorem measurable_sliceChartDensity (B : ℝ≥0) {g : Sphere → ℝ≥0∞} (hg : Measurable g) :
    Measurable (sliceChartDensity B g) :=
  (measurable_const.mul continuous_sphericalAreaDensity.measurable.ennreal_ofReal).mul
    (hg.comp OnePoint.continuous_coe.measurable)

 theorem sliceChartDensity_sq_integral_le (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z, sliceChartDensity B g z ^ 2) ≤
      (4 * (B : ℝ≥0∞) ^ 2) * ∫⁻ p, g p ^ 2 ∂sphericalArea := by
  rw [lintegral_sphericalArea _ (hg.pow_const 2)]
  calc
    _ ≤ ∫⁻ z : ℂ, (4 * (B : ℝ≥0∞) ^ 2) *
        (ENNReal.ofReal (sphericalAreaDensity z) * g (z : Sphere) ^ 2) := by
      apply lintegral_mono
      intro z
      have ha : ENNReal.ofReal (sphericalAreaDensity z) ≤ 4 :=
        (ENNReal.ofReal_le_ofReal (sphericalAreaDensity_le_four z)).trans_eq (by norm_num)
      calc
        sliceChartDensity B g z ^ 2 = (B : ℝ≥0∞) ^ 2 *
            ((ENNReal.ofReal (sphericalAreaDensity z)) ^ 2 * g (z : Sphere) ^ 2) := by
          simp only [sliceChartDensity, mul_pow, mul_assoc]
        _ ≤ (B : ℝ≥0∞) ^ 2 * ((4 * ENNReal.ofReal (sphericalAreaDensity z)) *
            g (z : Sphere) ^ 2) := by
          have ha2 : ENNReal.ofReal (sphericalAreaDensity z) ^ 2 ≤
              4 * ENNReal.ofReal (sphericalAreaDensity z) := by
            simpa only [pow_two] using
              mul_le_mul' ha (le_refl (ENNReal.ofReal (sphericalAreaDensity z)))
          exact mul_le_mul' le_rfl (mul_le_mul' ha2 le_rfl)
        _ = _ := by ring
    _ = _ := lintegral_const_mul' _ _ (by finiteness)

 theorem sliceChartDensity_sq_integral_finite (B : ℝ≥0) (g : Sphere → ℝ≥0∞)
    (hg : Measurable g) (hfin : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻ z, sliceChartDensity B g z ^ 2) < ∞ :=
  (sliceChartDensity_sq_integral_le B g hg).trans_lt
    (ENNReal.mul_lt_top (by finiteness) hfin)

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem mean_sphericalSliceCount_le_density
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {A : Set ℂ} (hA : IsCompact A) (hAG : MapsTo ((↑) : ℂ → Sphere) A G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord (((↑) : ℂ → Sphere) '' A))
    (K : Set C(PathTime, Sphere)) (hK : ∀ γ ∈ K, Injective γ)
    (η : ProbabilityMeasure K) (hfinite : ∀ γ ∈ K, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (L : ℝ≥0) (f : ℂ → ℝ) (hf : LipschitzWith L f) :
    (∫⁻ y, ∫⁻ γ : K, pathImageCount
      ((fun z : ℂ => π (z : Sphere)) '' (A ∩ f ⁻¹' {y})) γ.val ∂(η : Measure K)) ≤
      (L : ℝ≥0∞) * ∫⁻ z in A, sliceChartDensity B g z := by
  have hm := (hA.image OnePoint.continuous_coe).measurableSet
  have hb := mean_compactChartFiberCount_le_occupation hcoarea e hU y₀ π hπ he
    ((↑) : ℂ → Sphere) OnePoint.continuous_coe hA hAG finiteCoord
    (fun z _ => finiteCoord_coe z) B hB K hK η hfinite L f hf
  rw [hocc, withDensity_apply _ hm, sphericalArea_setLIntegral_coe hA.measurableSet g hg] at hb
  simpa only [Function.comp_def, sliceChartDensity, mul_assoc,
    lintegral_const_mul' _ _ ENNReal.coe_ne_top] using hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactIntegralComparison
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite measurable slice density is controlled almost everywhere
when all of its compact-set integrals are controlled. -/

open Set Filter MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity

 theorem ae_le_of_compact_setLIntegral_le {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hfin : (∫⁻ x, f x) < ∞)
    (h : ∀ K : Set ℝ, IsCompact K → (∫⁻ x in K, f x) ≤ ∫⁻ x in K, g x) :
    f ≤ᵐ[volume] g := by
  let ν : Measure ℝ := volume.withDensity f
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfin.ne
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf
  intro S hS _
  rw [← withDensity_apply f hS]
  change ν S ≤ _
  rw [hS.measure_eq_iSup_isCompact ν]
  apply iSup_le
  intro K
  apply iSup_le
  intro hKS
  apply iSup_le
  intro hK
  change (volume.withDensity f) K ≤ _
  rw [withDensity_apply f hK.measurableSet]
  exact (h K hK).trans (lintegral_mono_set hKS)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanSlicePointwise
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact transverse tests turn the integrated coarea estimate into
an almost-everywhere bound on each physical horizontal slice. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
 theorem meanSliceCount_restrict (π : ℂ → X) (K : Set C(PathTime, X))
    (η : Measure K) (I J B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ y, ∫⁻ γ : K, pathImageCount
      (π '' (planarSliceBox I (J ∩ B) ∩ Complex.im ⁻¹' {y})) γ.val ∂η) =
      ∫⁻ y in B, ∫⁻ γ : K, pathImageCount
        (π '' (planarSliceBox I J ∩ Complex.im ⁻¹' {y})) γ.val ∂η := by
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ B
  · simp only [indicator_of_mem hy]
    apply lintegral_congr
    intro γ
    rw [pathImageCount_planarSliceBox_restrict, indicator_of_mem hy]
  · simp only [indicator_of_notMem hy]
    have he : (fun γ : K => pathImageCount
        (π '' (planarSliceBox I (J ∩ B) ∩ Complex.im ⁻¹' {y})) γ.val) = 0 := by
      funext γ
      rw [pathImageCount_planarSliceBox_restrict, indicator_of_notMem hy]
      rfl
    rw [he]
    change (∫⁻ _ : K, (0 : ℝ≥0∞) ∂η) = 0
    exact lintegral_zero

 theorem ae_meanSliceCount_le
    (π : ℂ → X) (hπ : Continuous π) (K : Set C(PathTime, X))
    (hK : ∀ γ ∈ K, Injective γ) (η : Measure K) [SFinite η]
    {I J : Set ℝ} (hI : IsCompact I) (hJ : IsCompact J)
    (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ)
    (hfin : (∫⁻ z in planarSliceBox I J, ρ z) < ∞)
    (hcoarea : ∀ B : Set ℝ, IsCompact B → B ⊆ J →
      (∫⁻ y, ∫⁻ γ : K, pathImageCount
        (π '' (planarSliceBox I B ∩ Complex.im ⁻¹' {y})) γ.val ∂η) ≤
          ∫⁻ z in planarSliceBox I B, ρ z) :
    ∀ᵐ y ∂volume, (∫⁻ γ : K, pathImageCount
      (π '' (planarSliceBox I J ∩ Complex.im ⁻¹' {y})) γ.val ∂η) ≤
        ∫⁻ x in I, ρ ⟨x, y⟩ := by
  have hN := (measurable_compactPhysicalFiberCount π hπ (isCompact_planarSliceBox hI hJ)
    Complex.im Complex.continuous_im K hK).comp measurable_swap
  apply ae_le_of_compact_setLIntegral_le hN.lintegral_prod_right'
    ((hcoarea J hJ Subset.rfl).trans_lt hfin)
  intro B hB
  change (∫⁻ y in B, ∫⁻ γ : K, pathImageCount
    (π '' (planarSliceBox I J ∩ Complex.im ⁻¹' {y})) γ.val ∂η) ≤ _
  rw [← meanSliceCount_restrict π K η I J B hB.measurableSet]
  apply (hcoarea (J ∩ B) (hJ.inter hB) inter_subset_left).trans
  rw [lintegral_planarSliceBox hI.measurableSet (hJ.inter hB).measurableSet ρ hρ]
  exact lintegral_mono_set inter_subset_right

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphericalSlicePointwise
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The almost-everywhere physical line estimate for the compact simple-arc
law. The only coarea hypothesis is the cited plane-to-line theorem. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r609189_1 : BorelSpace Sphere := ⟨rfl⟩
theorem ae_sphericalHorizontalCount_le_density
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {I J : Set ℝ} (hI : IsCompact I) (hJ : IsCompact J)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox I J) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox I J))
    (K : Set C(PathTime, Sphere)) (hK : ∀ γ ∈ K, Injective γ)
    (η : ProbabilityMeasure K) (hfinite : ∀ γ ∈ K, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐ y ∂volume, (∫⁻ γ : K, pathImageCount
      ((fun z : ℂ => π (z : Sphere)) ''
        (planarSliceBox I J ∩ Complex.im ⁻¹' {y})) γ.val ∂(η : Measure K)) ≤
      ∫⁻ x in I, sliceChartDensity B g ⟨x, y⟩ := by
  have hA := isCompact_planarSliceBox hI hJ
  have hρ := measurable_sliceChartDensity B hg
  have hfin : (∫⁻ z in planarSliceBox I J, sliceChartDensity B g z) < ∞ := by
    let : IsFiniteMeasure (volume.restrict (planarSliceBox I J)) :=
      isFiniteMeasure_restrict.mpr hA.measure_lt_top.ne
    apply lintegral_lt_top_of_sq
    exact (lintegral_mono_set (subset_univ _)).trans_lt
      (by simpa only [Measure.restrict_univ] using sliceChartDensity_sq_integral_finite B g hg henergy)
  apply ae_meanSliceCount_le (fun z : ℂ => π (z : Sphere))
    (hπ.comp OnePoint.continuous_coe) K hK (η : Measure K) hI hJ _ hρ hfin
  intro C hC hCJ
  have hsub : planarSliceBox I C ⊆ planarSliceBox I J := planarSliceBox_mono Subset.rfl hCJ
  have hb := mean_sphericalSliceCount_le_density hcoarea e hU y₀ π hπ he
    (isCompact_planarSliceBox hI hC) (hAG.mono_left hsub) B (hB.mono (image_mono hsub))
    K hK η hfinite g hg hocc 1 Complex.im RCLike.lipschitzWith_im
  simpa only [ENNReal.coe_one, one_mul] using hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RationalSliceCounts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common full-measure set for every rational horizontal interval. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r609189_2 : BorelSpace Sphere := ⟨rfl⟩
theorem ae_sphericalHorizontal_rational_counts
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {I J : Set ℝ} (hJ : IsCompact J)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox I J) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox I J))
    (K : Set C(PathTime, Sphere)) (hK : ∀ γ ∈ K, Injective γ)
    (η : ProbabilityMeasure K) (hfinite : ∀ γ ∈ K, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐ y ∂volume, ∀ p q : ℚ, Icc (p : ℝ) q ⊆ I →
      (∫⁻ γ : K, pathImageCount
        ((fun z : ℂ => π (z : Sphere)) ''
          (planarSliceBox (Icc (p : ℝ) q) J ∩ Complex.im ⁻¹' {y})) γ.val ∂(η : Measure K)) ≤
        ∫⁻ x in Icc (p : ℝ) q, sliceChartDensity B g ⟨x, y⟩ := by
  refine ae_all_iff.mpr fun p => ae_all_iff.mpr fun q => ?_
  by_cases hpq : Icc (p : ℝ) q ⊆ I
  · have hsub := planarSliceBox_mono hpq (Subset.rfl : J ⊆ J)
    exact (ae_sphericalHorizontalCount_le_density hcoarea e hU y₀ π hπ he
      isCompact_Icc hJ (hAG.mono_left hsub) B (hB.mono (image_mono hsub))
      K hK η hfinite g hg hocc henergy).mono fun _ h _ => h
  · exact Eventually.of_forall fun _ h => (hpq h).elim

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalMeanIndexHorizontal
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal absolute continuity and derivative bounds for the local
mean index, from physical coarea and its occupation density. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r609189_3 : BorelSpace Sphere := ⟨rfl⟩
theorem physicalMeanIndex_horizontal_ACL_derivative
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {a b c d : ℝ} (J : Set ℝ) (hJ : IsCompact J)
    (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox (Icc a b) J) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox (Icc a b) J))
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox (Icc a b) J))
    (hpos : ∀ z ∈ planarSliceBox (Icc a b) J, 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox (Icc a b) J, diskRayProjection (Ψ z) = F (π (z : Sphere)))
    (v : ℂ → ℝ) (hv : ∀ z (hz : z ∈ planarSliceBox (Icc a b) J),
      v z = meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) ⟨Ψ z, hpos z hz⟩)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox (Icc a b) J))
    (hinj : InjOn (fun z : ℂ => F (π (z : Sphere))) (planarSliceBox (Icc a b) J)) :
    ∀ᵐ y ∂volume.restrict J,
      AbsolutelyContinuousOnInterval (fun x => v ⟨x, y⟩) c d ∧
        (∀ᵐ x ∂volume.restrict (Icc c d), |deriv (fun t => v ⟨t, y⟩) x| ≤
          (sliceChartDensity B g ⟨x, y⟩).toReal) := by
  let Q : C(ℂ, Sphere) := ⟨fun z => π (z : Sphere), hπ.comp OnePoint.continuous_coe⟩
  have hρ := measurable_sliceChartDensity B hg
  have hrect := isCompact_planarSliceBox (I := Icc a b) isCompact_Icc hJ
  have hfin : (∫⁻ z in planarSliceBox (Icc a b) J, sliceChartDensity B g z) < ∞ := by
    let : IsFiniteMeasure (volume.restrict (planarSliceBox (Icc a b) J)) :=
      isFiniteMeasure_restrict.mpr hrect.measure_lt_top.ne
    apply lintegral_lt_top_of_sq
    exact (lintegral_mono_set (subset_univ _)).trans_lt
      (by simpa only [Measure.restrict_univ] using sliceChartDensity_sq_integral_finite B g hg henergy)
  exact meanIndex_horizontal_ACL_derivative hsch hsep A K hK hKS η F f hf hmap
    Q J hJ.measurableSet hac hcd hdb Ψ hΨ hpos hproj v hv hF hinj
    (sliceChartDensity B g) hρ hfin
    (ae_sphericalHorizontal_rational_counts hcoarea e hU y₀ π hπ he hJ hAG B hB
      A hA η hfinite g hg hocc henergy)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarAxisSwap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interchanging physical coordinate axes preserves area and exchanges
horizontal and vertical fiber tests. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

 theorem continuous_planarAxisSwap : Continuous planarAxisSwap :=
  Complex.equivRealProdCLM.symm.continuous.comp
    (continuous_swap.comp Complex.equivRealProdCLM.continuous)

 theorem planarAxisSwap_bijective : Bijective planarAxisSwap :=
  (show Involutive planarAxisSwap from planarAxisSwap_involutive).bijective

 theorem planarAxisSwap_measurePreserving : MeasurePreserving planarAxisSwap := by
  have hs : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
    simpa only [Measure.volume_eq_prod] using
      Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  exact Complex.volume_preserving_equiv_real_prod.symm.comp
    (hs.comp Complex.volume_preserving_equiv_real_prod)

 theorem planarAxisSwap_preimage_box (I J : Set ℝ) :
    planarAxisSwap ⁻¹' planarSliceBox I J = planarSliceBox J I := by
  ext z
  change (z.im ∈ I ∧ z.re ∈ J) ↔ (z.re ∈ J ∧ z.im ∈ I)
  exact and_comm

 theorem planarAxisSwap_image_box (I J : Set ℝ) :
    planarAxisSwap '' planarSliceBox I J = planarSliceBox J I := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw.2, hw.1⟩
  · intro hz
    exact ⟨planarAxisSwap z, ⟨hz.2, hz.1⟩, planarAxisSwap_involutive z⟩

 theorem planarAxisSwap_image_horizontal_fiber (I J : Set ℝ) (x : ℝ) :
    planarAxisSwap '' (planarSliceBox I J ∩ Complex.im ⁻¹' {x}) =
      planarSliceBox J I ∩ Complex.re ⁻¹' {x} := by
  ext z
  constructor
  · rintro ⟨w, ⟨hw, hx⟩, rfl⟩
    exact ⟨⟨hw.2, hw.1⟩, hx⟩
  · rintro ⟨hz, hx⟩
    exact ⟨planarAxisSwap z, ⟨⟨hz.2, hz.1⟩, hx⟩, planarAxisSwap_involutive z⟩

 theorem lintegral_planarAxisSwap_box (I J : Set ℝ) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ) :
    (∫⁻ z in planarSliceBox I J, ρ (planarAxisSwap z)) =
      ∫⁻ z in planarSliceBox J I, ρ z := by
  have hm : MeasurableSet (planarSliceBox J I) :=
    (hJ.preimage Complex.continuous_re.measurable).inter
      (hI.preimage Complex.continuous_im.measurable)
  rw [← planarAxisSwap_preimage_box J I]
  exact planarAxisSwap_measurePreserving.setLIntegral_comp_preimage hm hρ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VerticalSliceCounts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical physical slice bounds from planar coarea, with the
coordinate axes interchanged. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r609189_4 : BorelSpace Sphere := ⟨rfl⟩
theorem ae_sphericalVerticalCount_le_density
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {I J : Set ℝ} (hI : IsCompact I) (hJ : IsCompact J)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox I J) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox I J))
    (K : Set C(PathTime, Sphere)) (hK : ∀ γ ∈ K, Injective γ)
    (η : ProbabilityMeasure K) (hfinite : ∀ γ ∈ K, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐ x ∂volume, (∫⁻ γ : K, pathImageCount
      ((fun z : ℂ => π (z : Sphere)) ''
        (planarSliceBox I J ∩ Complex.re ⁻¹' {x})) γ.val ∂(η : Measure K)) ≤
      ∫⁻ y in J, sliceChartDensity B g ⟨x, y⟩ := by
  let Q : ℂ → Sphere := fun z => π (z : Sphere)
  let ρ : ℂ → ℝ≥0∞ := sliceChartDensity B g
  have hρ : Measurable ρ := measurable_sliceChartDensity B hg
  have hfin : (∫⁻ z in planarSliceBox I J, ρ z) < ∞ := by
    let : IsFiniteMeasure (volume.restrict (planarSliceBox I J)) :=
      isFiniteMeasure_restrict.mpr (isCompact_planarSliceBox hI hJ).measure_lt_top.ne
    apply lintegral_lt_top_of_sq
    exact (lintegral_mono_set (subset_univ _)).trans_lt
      (by simpa only [Measure.restrict_univ] using sliceChartDensity_sq_integral_finite B g hg henergy)
  have hswapfin : (∫⁻ z in planarSliceBox J I, (ρ ∘ planarAxisSwap) z) < ∞ := by
    simpa only [Function.comp_apply, lintegral_planarAxisSwap_box J I hJ.measurableSet hI.measurableSet ρ hρ] using hfin
  have hswap := ae_meanSliceCount_le (Q ∘ planarAxisSwap)
    ((hπ.comp OnePoint.continuous_coe).comp continuous_planarAxisSwap)
    K hK (η : Measure K) hJ hI (ρ ∘ planarAxisSwap)
    (hρ.comp continuous_planarAxisSwap.measurable)
    hswapfin ?_
  · filter_upwards [hswap] with x hx
    simpa only [image_comp, planarAxisSwap_image_horizontal_fiber,
      Function.comp_apply, planarAxisSwap, Q, ρ] using hx
  · intro C hC hCI
    have hsub : planarSliceBox C J ⊆ planarSliceBox I J :=
      planarSliceBox_mono hCI Subset.rfl
    have hb := mean_sphericalSliceCount_le_density hcoarea e hU y₀ π hπ he
      (isCompact_planarSliceBox hC hJ) (hAG.mono_left hsub) B
      (hB.mono (image_mono hsub)) K hK η hfinite g hg hocc
      1 Complex.re RCLike.lipschitzWith_re
    change (∫⁻ y, ∫⁻ γ : K, pathImageCount
      (((fun z : ℂ => π (z : Sphere)) ∘ planarAxisSwap) ''
        (planarSliceBox J C ∩ Complex.im ⁻¹' {y})) γ.val ∂(η : Measure K)) ≤ _
    simp only [image_comp, planarAxisSwap_image_horizontal_fiber]
    simpa only [Function.comp_apply, lintegral_planarAxisSwap_box J C hJ.measurableSet
        hC.measurableSet ρ hρ, ENNReal.coe_one, one_mul, ρ] using hb

 theorem ae_sphericalVertical_rational_counts
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {I J : Set ℝ} (hI : IsCompact I)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox I J) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox I J))
    (K : Set C(PathTime, Sphere)) (hK : ∀ γ ∈ K, Injective γ)
    (η : ProbabilityMeasure K) (hfinite : ∀ γ ∈ K, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐ x ∂volume, ∀ p q : ℚ, Icc (p : ℝ) q ⊆ J →
      (∫⁻ γ : K, pathImageCount
        ((fun z : ℂ => π (z : Sphere)) ''
          (planarSliceBox I (Icc (p : ℝ) q) ∩ Complex.re ⁻¹' {x})) γ.val ∂(η : Measure K)) ≤
        ∫⁻ y in Icc (p : ℝ) q, sliceChartDensity B g ⟨x, y⟩ := by
  refine ae_all_iff.mpr fun p => ae_all_iff.mpr fun q => ?_
  by_cases hpq : Icc (p : ℝ) q ⊆ J
  · have hsub := planarSliceBox_mono (Subset.rfl : I ⊆ I) hpq
    exact (ae_sphericalVerticalCount_le_density hcoarea e hU y₀ π hπ he
      hI isCompact_Icc (hAG.mono_left hsub) B (hB.mono (image_mono hsub))
      K hK η hfinite g hg hocc henergy).mono fun _ h _ => h
  · exact Eventually.of_forall fun _ h => (hpq h).elim

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalMeanIndexVertical
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical absolute continuity and derivative bounds for the local mean
index. Coordinate interchange preserves physical area, and coarea bounds
the slices by the occupation density. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r609189_5 : BorelSpace Sphere := ⟨rfl⟩
theorem physicalMeanIndex_vertical_ACL_derivative
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {a b c d : ℝ} (I : Set ℝ) (hI : IsCompact I)
    (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox I (Icc a b)) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox I (Icc a b)))
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox I (Icc a b)))
    (hpos : ∀ z ∈ planarSliceBox I (Icc a b), 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox I (Icc a b), diskRayProjection (Ψ z) = F (π (z : Sphere)))
    (v : ℂ → ℝ) (hv : ∀ z (hz : z ∈ planarSliceBox I (Icc a b)),
      v z = meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) ⟨Ψ z, hpos z hz⟩)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox I (Icc a b)))
    (hinj : InjOn (fun z : ℂ => F (π (z : Sphere))) (planarSliceBox I (Icc a b))) :
    ∀ᵐ x ∂volume.restrict I,
      AbsolutelyContinuousOnInterval (fun y => v ⟨x, y⟩) c d ∧
        (∀ᵐ y ∂volume.restrict (Icc c d), |deriv (fun t => v ⟨x, t⟩) y| ≤
          (sliceChartDensity B g ⟨x, y⟩).toReal) := by
  let Q : C(ℂ, Sphere) := ⟨fun z => π ((planarAxisSwap z : ℂ) : Sphere),
    (hπ.comp OnePoint.continuous_coe).comp continuous_planarAxisSwap⟩
  let ρ : ℂ → ℝ≥0∞ := sliceChartDensity B g
  have hρ : Measurable ρ := measurable_sliceChartDensity B hg
  have hswap : MapsTo planarAxisSwap (planarSliceBox (Icc a b) I)
      (planarSliceBox I (Icc a b)) := fun _ hz => ⟨hz.2, hz.1⟩
  have hQimage : Q '' planarSliceBox (Icc a b) I =
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox I (Icc a b) := by
    change ((fun z : ℂ => π (z : Sphere)) ∘ planarAxisSwap) '' _ = _
    rw [image_comp, planarAxisSwap_image_box]
  have hfin : (∫⁻ z in planarSliceBox I (Icc a b), ρ z) < ∞ := by
    let : IsFiniteMeasure (volume.restrict (planarSliceBox I (Icc a b))) :=
      isFiniteMeasure_restrict.mpr (isCompact_planarSliceBox hI isCompact_Icc).measure_lt_top.ne
    apply lintegral_lt_top_of_sq
    exact (lintegral_mono_set (subset_univ _)).trans_lt
      (by simpa only [Measure.restrict_univ] using sliceChartDensity_sq_integral_finite B g hg henergy)
  have hc := ae_sphericalVertical_rational_counts hcoarea e hU y₀ π hπ he hI
    hAG B hB A hA η hfinite g hg hocc henergy
  have hswapfin : (∫⁻ z in planarSliceBox (Icc a b) I, (ρ ∘ planarAxisSwap) z) < ∞ := by
    simpa only [Function.comp_apply, lintegral_planarAxisSwap_box (Icc a b) I measurableSet_Icc hI.measurableSet ρ hρ] using hfin
  have hr := meanIndex_horizontal_ACL_derivative hsch hsep A K hK hKS η F f hf hmap
    Q I hI.measurableSet hac hcd hdb (Ψ ∘ planarAxisSwap)
    (hΨ.comp continuous_planarAxisSwap.continuousOn hswap)
    (fun z hz => hpos _ (hswap hz)) (fun z hz => hproj _ (hswap hz))
    (v ∘ planarAxisSwap) (fun z hz => hv _ (hswap hz))
    (fun γ => by simpa only [hQimage] using hF γ) ?_
    (ρ ∘ planarAxisSwap) (hρ.comp continuous_planarAxisSwap.measurable)
    hswapfin ?_
  · simpa only [Function.comp_apply, planarAxisSwap, ρ] using hr
  · intro z hz w hw hzw
    apply planarAxisSwap_bijective.injective
    exact hinj (hswap hz) (hswap hw) hzw
  · filter_upwards [hc] with x hx
    intro p q hpq
    have hi := hx p q hpq
    change (∫⁻ γ : A, pathImageCount
      (((fun z : ℂ => π (z : Sphere)) ∘ planarAxisSwap) ''
        (planarSliceBox (Icc (p : ℝ) q) I ∩ Complex.im ⁻¹' {x})) γ.val ∂(η : Measure A)) ≤ _
    simpa only [image_comp, planarAxisSwap_image_horizontal_fiber,
      Function.comp_apply, planarAxisSwap, ρ] using hi

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_DensityL2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real representative of a finite-energy density is locally L² in
the physical planar chart, including densities that are infinite on a null set. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem memLp_two_toReal_of_lintegral_sq_ne_top
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {g : X → ℝ≥0∞}
    (hg : Measurable g) (hfinite : (∫⁻x, g x ^ 2 ∂μ) ≠ ∞) :
    MemLp (fun x => (g x).toReal) 2 μ := by
  apply (memLp_two_iff_integrable_sq hg.ennreal_toReal.aestronglyMeasurable).2
  simpa only [ENNReal.toReal_pow] using
    integrable_toReal_of_lintegral_ne_top (hg.pow_const 2).aemeasurable hfinite

attribute [local instance] sphereMetric sphereBorel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MeasurableLineDerivatives
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On an open set, almost everywhere line differentiability of a measurable
function makes its line derivative measurable. The proof uses actual
difference quotients of the zero extension, so no continuity across the
exceptional lines is required. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddRightInvariant μ]

/-- A Borel representative agrees with the line derivative at every
differentiability point outside one fixed null set. This implication form
can be sliced by Fubini before asserting almost everywhere differentiability. -/
theorem exists_measurable_lineDeriv_representative
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} (v : E)
    (hf : AEStronglyMeasurable f (μ.restrict U)) :
    ∃ G : E → ℝ, Measurable G ∧
      ∀ᵐ x ∂μ, x ∈ U → LineDifferentiableAt ℝ f x v →
        G x = lineDeriv ℝ f x v := by
  let F : E → ℝ := U.indicator f
  have hF : AEStronglyMeasurable F μ :=
    (aestronglyMeasurable_indicator_iff hU.measurableSet).2 hf
  let F₀ := hF.mk F
  let h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let q : ℕ → E → ℝ := fun n x => (h n)⁻¹ * (F₀ (x + h n • v) - F₀ x)
  have hq (n : ℕ) : Measurable (q n) :=
    ((hF.measurable_mk.comp (continuous_id.add continuous_const).measurable).sub
      hF.measurable_mk).const_mul _
  refine ⟨fun x => limsup (fun n => q n x) atTop, Measurable.limsup hq, ?_⟩
  have he (n : ℕ) : ∀ᵐ x ∂μ, F (x + h n • v) = F₀ (x + h n • v) :=
    (measurePreserving_add_right μ (h n • v)).quasiMeasurePreserving.ae hF.ae_eq_mk
  filter_upwards [hF.ae_eq_mk, ae_all_iff.2 he] with x hx₀ hx₁ hx hd
  have hx₀' : F x = F₀ x := hx₀
  have hh : Tendsto h atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => by
        change 1 / ((n : ℝ) + 1) ≠ 0
        positivity)⟩
  have hlim := hd.hasDerivAt.tendsto_slope_zero.comp hh
  have hin : ∀ᶠ n in atTop, x + h n • v ∈ U := by
    have ht : Tendsto (fun n => x + h n • v) atTop (𝓝 x) := by
      simpa only [zero_smul, add_zero] using
        tendsto_const_nhds.add ((tendsto_nhds_of_tendsto_nhdsWithin hh).smul_const v)
    exact ht (hU.mem_nhds hx)
  have hq_lim : Tendsto (fun n => q n x) atTop (𝓝 (lineDeriv ℝ f x v)) := by
    apply hlim.congr'
    filter_upwards [hin] with n hn
    simp only [q, ← hx₀', ← hx₁ n, F, indicator_of_mem hn,
      indicator_of_mem hx, zero_add, zero_smul, add_zero, smul_eq_mul, Function.comp_apply]
  exact hq_lim.limsup_eq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RectangleDerivativeRepresentatives
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable representatives of the two ACL derivatives in a physical
rectangle. The null set is chosen before slicing, and exceptional lines
are discarded only after applying Fubini. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem ae_mem_Ioo_of_Icc (a b : ℝ) :
    ∀ᵐ x ∂volume.restrict (Icc a b), x ∈ Ioo a b := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff],
    show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff]] with x hxa hxb hx
  exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩

theorem lineDeriv_horizontal (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    lineDeriv ℝ f p (1, 0) = deriv (fun t => f (t, p.2)) p.1 := by
  rcases p with ⟨x, y⟩
  simp only [lineDeriv, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
    Prod.mk_add_mk, add_zero]
  simpa only [add_zero] using deriv_comp_const_add (fun t => f (t, y)) x 0

theorem lineDeriv_vertical (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    lineDeriv ℝ f p (0, 1) = deriv (fun t => f (p.1, t)) p.2 := by
  rcases p with ⟨x, y⟩
  simp only [lineDeriv, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
    Prod.mk_add_mk, add_zero]
  simpa only [add_zero] using deriv_comp_const_add (fun t => f (x, t)) y 0

theorem exists_measurable_horizontal_derivative
    (f : ℝ × ℝ → ℝ) {a b c d : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hac : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b) :
    ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
      ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
        G (x, y) = deriv (fun t => f (t, y)) x := by
  let : Measure.IsAddRightInvariant (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨G, hG, hrep⟩ := exists_measurable_lineDeriv_representative
    (isOpen_Ioo.prod isOpen_Ioo) (1, 0) hf
  have hrep' : ∀ᵐ y ∂volume, ∀ᵐ x ∂volume,
      (x, y) ∈ Ioo a b ×ˢ Ioo c d → LineDifferentiableAt ℝ f (x, y) (1, 0) →
        G (x, y) = lineDeriv ℝ f (x, y) (1, 0) := by
    have hr := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae (by
        simpa only [Measure.volume_eq_prod] using hrep)
    exact Measure.ae_ae_of_ae_prod hr
  refine ⟨G, hG, ?_⟩
  filter_upwards [hac, ae_mem_Ioo_of_Icc c d, ae_restrict_of_ae hrep'] with y hy hyI hyr
  filter_upwards [ae_mem_Ioo_of_Icc a b,
    ae_restrict_of_ae hy.ae_differentiableAt, ae_restrict_of_ae hyr] with x hxI hxd hxr
  have hd := hxd (Icc_subset_uIcc ⟨hxI.1.le, hxI.2.le⟩)
  have hline : LineDifferentiableAt ℝ f (x, y) (1, 0) := by
    have h : HasDerivAt (fun t => f (t, y)) (deriv (fun t => f (t, y)) x) (x + 0) := by
      simpa only [add_zero] using hd.hasDerivAt
    have ht := h.comp_const_add x 0
    simpa only [LineDifferentiableAt, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, Prod.mk_add_mk, add_zero] using ht.differentiableAt
  exact (hxr ⟨hxI, hyI⟩ hline).trans (lineDeriv_horizontal f (x, y))

theorem exists_measurable_vertical_derivative
    (f : ℝ × ℝ → ℝ) {a b c d : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hac : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d) :
    ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
      ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
        G (x, y) = deriv (fun t => f (x, t)) y := by
  let : Measure.IsAddRightInvariant (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨G, hG, hrep⟩ := exists_measurable_lineDeriv_representative
    (isOpen_Ioo.prod isOpen_Ioo) (0, 1) hf
  have hrep' : ∀ᵐ x ∂volume, ∀ᵐ y ∂volume,
      (x, y) ∈ Ioo a b ×ˢ Ioo c d → LineDifferentiableAt ℝ f (x, y) (0, 1) →
        G (x, y) = lineDeriv ℝ f (x, y) (0, 1) :=
    Measure.ae_ae_of_ae_prod (by simpa only [Measure.volume_eq_prod] using hrep)
  refine ⟨G, hG, ?_⟩
  filter_upwards [hac, ae_mem_Ioo_of_Icc a b, ae_restrict_of_ae hrep'] with x hx hxI hxr
  filter_upwards [ae_mem_Ioo_of_Icc c d,
    ae_restrict_of_ae hx.ae_differentiableAt, ae_restrict_of_ae hxr] with y hyI hyd hyr
  have hd := hyd (Icc_subset_uIcc ⟨hyI.1.le, hyI.2.le⟩)
  have hline : LineDifferentiableAt ℝ f (x, y) (0, 1) := by
    have h : HasDerivAt (fun t => f (x, t)) (deriv (fun t => f (x, t)) y) (y + 0) := by
      simpa only [add_zero] using hd.hasDerivAt
    have ht := h.comp_const_add y 0
    simpa only [LineDifferentiableAt, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, Prod.mk_add_mk, add_zero] using ht.differentiableAt
  exact (hyr ⟨hxI, hyI⟩ hline).trans (lineDeriv_vertical f (x, y))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ACLWeakDerivatives
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts for the Borel representatives of ACL derivatives.
This converts the actual slice derivative into a planar weak derivative. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem integral_mul_horizontal_deriv_eq_neg
    {f G : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hf : Integrable f (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hG : Integrable G (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hac : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b)
    (hrep : ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
      G (x, y) = deriv (fun t => f (t, y)) x)
    {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ioo a b ×ˢ Ioo c d) :
    (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
      -(∫p in Icc a b ×ˢ Icc c d, G p * φ p) := by
  have hcD : Continuous (fun p => (fderiv ℝ φ p) (1, 0)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := hcD.bounded_above_of_compact_support (hsupp.fderiv_apply (𝕜 := ℝ) (1, 0))
  obtain ⟨D, hD⟩ := hφ.continuous.bounded_above_of_compact_support hsupp
  have hl : Integrable (fun p => f p * (fderiv ℝ φ p) (1, 0))
      (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hf.mul_bdd hcD.aestronglyMeasurable (Eventually.of_forall hC)
  have hr : Integrable (fun p => G p * φ p)
      (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hG.mul_bdd hφ.continuous.aestronglyMeasurable (Eventually.of_forall hD)
  have hp (x y : ℝ) : deriv (fun t => φ (t, y)) x = (fderiv ℝ φ (x, y)) (1, 0) := by
    exact ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv
  have hzero (x y : ℝ) (hx : x ∉ Ioo a b) : φ (x, y) = 0 := by
    by_contra hn
    exact hx (hsub (subset_tsupport φ hn)).1
  have hline : ∀ᵐ y ∂volume.restrict (Icc c d),
      (∫x in Icc a b, f (x, y) * (fderiv ℝ φ (x, y)) (1, 0)) =
        -(∫x in Icc a b, G (x, y) * φ (x, y)) := by
    filter_upwards [hac, hrep] with y hy hyr
    have hφline : AbsolutelyContinuousOnInterval (fun x => φ (x, y)) a b :=
      ((hφ.comp (contDiff_id.prodMk contDiff_const)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn.absolutelyContinuousOnInterval
    have hi := hy.integral_mul_deriv_eq_deriv_mul hφline
    rw [hzero b y (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), hzero a y (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), mul_zero, mul_zero, sub_self,
      zero_sub] at hi
    simp only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hi
    calc
      _ = ∫x in Icc a b, f (x, y) * deriv (fun t => φ (t, y)) x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => congrArg (fun z => f (x, y) * z) (hp x y).symm
      _ = -(∫x in Icc a b, deriv (fun t => f (t, y)) x * φ (x, y)) := hi
      _ = -(∫x in Icc a b, G (x, y) * φ (x, y)) := by
        congr 1
        exact integral_congr_ae (hyr.mono fun x hx => congrArg (fun z => z * φ (x, y)) hx.symm)
  have he : (volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c d) =
      (volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [he] at hl hr ⊢
  rw [integral_prod_symm _ hl, integral_prod_symm _ hr, ← integral_neg]
  exact integral_congr_ae hline

theorem integral_mul_vertical_deriv_eq_neg
    {f G : ℝ × ℝ → ℝ} {a b c d : ℝ} (hcd : c ≤ d)
    (hf : Integrable f (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hG : Integrable G (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hac : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d)
    (hrep : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
      G (x, y) = deriv (fun t => f (x, t)) y)
    {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ioo a b ×ˢ Ioo c d) :
    (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
      -(∫p in Icc a b ×ˢ Icc c d, G p * φ p) := by
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have hswap : MeasurePreserving e
      (volume.restrict (Icc c d ×ˢ Icc a b))
      (volume.restrict (Icc a b ×ˢ Icc c d)) := by
    change MeasurePreserving Prod.swap _ _
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict]
    exact Measure.measurePreserving_swap
  have hs : tsupport (φ ∘ e) ⊆ Ioo c d ×ˢ Ioo a b := by
    change tsupport (φ ∘ e.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage φ e.toHomeomorph]
    intro p hp
    exact ⟨(hsub hp).2, (hsub hp).1⟩
  have hi := integral_mul_horizontal_deriv_eq_neg hcd
    (hswap.integrable_comp_of_integrable hf) (hswap.integrable_comp_of_integrable hG)
    hac hrep (hφ.comp e.contDiff) (hsupp.comp_homeomorph e.toHomeomorph) hs
  have hd (p : ℝ × ℝ) :
      (fderiv ℝ (φ ∘ e) p) (1, 0) = (fderiv ℝ φ (e p)) (0, 1) := by
    rw [fderiv_comp p (hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt e.differentiableAt,
      e.fderiv]
    rfl
  simp only [Function.comp_apply, hd] at hi
  calc
    _ = ∫p in Icc c d ×ˢ Icc a b, f (e p) * (fderiv ℝ φ (e p)) (0, 1) :=
      (hswap.integral_comp e.toHomeomorph.measurableEmbedding _).symm
    _ = -(∫p in Icc c d ×ˢ Icc a b, G (e p) * φ (e p)) := hi
    _ = _ := congrArg Neg.neg (hswap.integral_comp e.toHomeomorph.measurableEmbedding
      (fun p => G p * φ p))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RectangleSobolev
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ACL and an L² bound on the line derivatives produce an actual local
Sobolev gradient. All gradient fields here are constructed Borel functions. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem rectangle_restrict_Ioo_eq_Icc (a b c d : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Ioo a b ×ˢ Ioo c d) =
      volume.restrict (Icc a b ×ˢ Icc c d) := by
  rw [Measure.volume_eq_prod]
  exact Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)

theorem exists_rectangle_weak_gradient
    {f ρ : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hρ : Measurable ρ) (hρ₂ : MemLp ρ 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hacx : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b)
    (hacy : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d)
    (hbx : ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
      |deriv (fun t => f (t, y)) x| ≤ ρ (x, y))
    (hby : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
      |deriv (fun t => f (x, t)) y| ≤ ρ (x, y)) :
    ∃ Gx Gy : ℝ × ℝ → ℝ, Measurable Gx ∧ Measurable Gy ∧
      MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
      MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
      (∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), |Gx p| ≤ ρ p ∧ |Gy p| ≤ ρ p) ∧
      ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ioo c d →
        (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
          -(∫p in Icc a b ×ˢ Icc c d, Gx p * φ p) ∧
        (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
          -(∫p in Icc a b ×ˢ Icc c d, Gy p * φ p) := by
  let : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c d)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)) := by
    rw [rectangle_restrict_Ioo_eq_Icc]
    exact hf.aestronglyMeasurable
  obtain ⟨Gx, hGx, hrx⟩ := exists_measurable_horizontal_derivative f hfmeas hacx
  obtain ⟨Gy, hGy, hry⟩ := exists_measurable_vertical_derivative f hfmeas hacy
  have hx : ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
      |Gx (x, y)| ≤ ρ (x, y) := by
    filter_upwards [hrx, hbx] with y hy hb
    filter_upwards [hy, hb] with x hx hb
    simpa only [hx] using hb
  have hy : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
      |Gy (x, y)| ≤ ρ (x, y) := by
    filter_upwards [hry, hby] with x hx hb
    filter_upwards [hx, hb] with y hy hb
    simpa only [hy] using hb
  have hmeasx : MeasurableSet {p : ℝ × ℝ | |Gx p| ≤ ρ p} :=
    by simpa only [Real.norm_eq_abs] using measurableSet_le hGx.norm hρ
  have hmeasy : MeasurableSet {p : ℝ × ℝ | |Gy p| ≤ ρ p} :=
    by simpa only [Real.norm_eq_abs] using measurableSet_le hGy.norm hρ
  have hBx : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), |Gx p| ≤ ρ p := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (Measure.ae_prod_iff_ae_ae hmeasx).2 ((Measure.ae_ae_comm hmeasx).2 hx)
  have hBy : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), |Gy p| ≤ ρ p := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (Measure.ae_prod_iff_ae_ae hmeasy).2 hy
  have hx₂ : MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hρ₂.of_le hGx.aestronglyMeasurable (hBx.mono fun p hp => by
      simpa only [Real.norm_eq_abs] using hp.trans (le_abs_self _))
  have hy₂ : MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hρ₂.of_le hGy.aestronglyMeasurable (hBy.mono fun p hp => by
      simpa only [Real.norm_eq_abs] using hp.trans (le_abs_self _))
  refine ⟨Gx, Gy, hGx, hGy, hx₂, hy₂, hBx.and hBy, ?_⟩
  intro φ hφ hs hsub
  exact ⟨integral_mul_horizontal_deriv_eq_neg hab (hf.integrable (by norm_num))
    (hx₂.integrable (by norm_num)) hacx hrx hφ hs hsub,
    integral_mul_vertical_deriv_eq_neg hcd (hf.integrable (by norm_num))
    (hy₂.integrable (by norm_num)) hacy hry hφ hs hsub⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PlanarSobolevTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the actual planar weak derivative identities to the
Euclidean coordinates of the repository's Sobolev approximation library. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem weakPartial_of_planar_identity
    {f G : ℝ × ℝ → ℝ} {a b c d : ℝ} (i : Fin 2) (v : ℝ × ℝ)
    (hv : euclideanPlaneCoordinates (EuclideanSpace.single i 1) = v)
    (hweak : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b ×ˢ Ioo c d →
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ ψ p) v) =
        -(∫p in Icc a b ×ˢ Icc c d, G p * ψ p)) :
    DeGiorgi.HasWeakPartialDeriv i (G ∘ euclideanPlaneCoordinates)
      (f ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)) := by
  intro φ hφ hs hsub
  let e := euclideanPlaneCoordinates
  change (∫x in e ⁻¹' (Ioo a b ×ˢ Ioo c d),
    f (e x) * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
      -(∫x in e ⁻¹' (Ioo a b ×ˢ Ioo c d), G (e x) * φ x)
  change e (EuclideanSpace.single i 1) = v at hv
  let ψ : ℝ × ℝ → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp e.symm.contDiff
  have hsψ : HasCompactSupport ψ := hs.comp_homeomorph e.symm.toHomeomorph
  have hsubψ : tsupport ψ ⊆ Ioo a b ×ˢ Ioo c d := by
    change tsupport (φ ∘ e.symm.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage]
    intro p hp
    have hh := hsub hp
    change e (e.symm p) ∈ Ioo a b ×ˢ Ioo c d at hh
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  have hd (p : ℝ × ℝ) :
      (fderiv ℝ ψ p) v = (fderiv ℝ φ (e.symm p)) (EuclideanSpace.single i 1) := by
    rw [fderiv_comp p (hφ.differentiable (by simp)).differentiableAt e.symm.differentiableAt,
      e.symm.fderiv]
    change (fderiv ℝ φ (e.symm p)) (e.symm v) = _
    rw [← hv, ContinuousLinearEquiv.symm_apply_apply]
  have hp := hweak ψ hψ hsψ hsubψ
  rw [← rectangle_restrict_Ioo_eq_Icc] at hp
  have hmp : MeasurePreserving e (volume.restrict (e ⁻¹' (Ioo a b ×ˢ Ioo c d)))
      (volume.restrict (Ioo a b ×ˢ Ioo c d)) :=
    euclideanPlaneCoordinates_measurePreserving.restrict_preimage
      (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  calc
    _ = ∫x in e ⁻¹' (Ioo a b ×ˢ Ioo c d), f (e x) * (fderiv ℝ ψ (e x)) v := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp only [hd,
        ContinuousLinearEquiv.symm_apply_apply]
    _ = ∫p in Ioo a b ×ˢ Ioo c d, f p * (fderiv ℝ ψ p) v :=
      hmp.integral_comp e.toHomeomorph.measurableEmbedding
        (fun p => f p * (fderiv ℝ ψ p) v)
    _ = -(∫p in Ioo a b ×ˢ Ioo c d, G p * ψ p) := hp
    _ = _ := by
      rw [← hmp.integral_comp e.toHomeomorph.measurableEmbedding (fun p => G p * ψ p)]
      simp only [ψ, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalMeanIndexSobolev
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The locally lifted geometric mean has actual L² weak derivatives.
Both ACL directions follow from physical occupation and published coarea;
boundedness follows from the compact family of lifted terminal rays. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
 theorem sliceChartDensity_memLp_rectangle
    (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) (a b c d : ℝ) :
    MemLp (fun p : ℝ × ℝ => (sliceChartDensity B g ⟨p.1, p.2⟩).toReal) 2
      (volume.restrict (Icc a b ×ˢ Icc c d)) := by
  have hL := memLp_two_toReal_of_lintegral_sq_ne_top volume
    (measurable_sliceChartDensity B hg) (sliceChartDensity_sq_integral_finite B g hg henergy).ne
  have hP := hL.comp_measurePreserving
    (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd)
  exact hP.restrict (Icc a b ×ˢ Icc c d)

 local instance localInst_r609189_6 : BorelSpace Sphere := ⟨rfl⟩
theorem physicalMeanIndex_rectangle_weak_gradient
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {a₀ a b b₀ c₀ c d d₀ : ℝ}
    (ha : a₀ < a) (hab : a < b) (hb : b < b₀)
    (hc : c₀ < c) (hcd : c < d) (hd : d < d₀)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (hpos : ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀), 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀),
      diskRayProjection (Ψ z) = F (π (z : Sphere)))
    (hF : ∀ γ : A, InjOn F (range γ.val ∪
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (hinj : InjOn (fun z : ℂ => F (π (z : Sphere)))
      (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀))) :
    let v := liftedMeanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) Ψ
    let v₂ : ℝ × ℝ → ℝ := fun p => v ⟨p.1, p.2⟩
    MemLp v₂ 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
    ∃ Gx Gy : ℝ × ℝ → ℝ, Measurable Gx ∧ Measurable Gy ∧
      MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
      MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
      (∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d),
        |Gx p| ≤ (sliceChartDensity B g ⟨p.1, p.2⟩).toReal ∧
        |Gy p| ≤ (sliceChartDensity B g ⟨p.1, p.2⟩).toReal) ∧
      ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ioo c d →
        (∫p in Icc a b ×ˢ Icc c d, v₂ p * (fderiv ℝ φ p) (1, 0)) =
          -(∫p in Icc a b ×ˢ Icc c d, Gx p * φ p) ∧
        (∫p in Icc a b ×ˢ Icc c d, v₂ p * (fderiv ℝ φ p) (0, 1)) =
          -(∫p in Icc a b ×ˢ Icc c d, Gy p * φ p) := by
  let v := liftedMeanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) Ψ
  let v₂ : ℝ × ℝ → ℝ := fun p => v ⟨p.1, p.2⟩
  let ρ : ℝ × ℝ → ℝ := fun p => (sliceChartDensity B g ⟨p.1, p.2⟩).toReal
  have hsx : planarSliceBox (Icc a₀ b₀) (Icc c d) ⊆
      planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀) :=
    planarSliceBox_mono Subset.rfl (Icc_subset_Icc hc.le hd.le)
  have hsy : planarSliceBox (Icc a b) (Icc c₀ d₀) ⊆
      planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀) :=
    planarSliceBox_mono (Icc_subset_Icc ha.le hb.le) Subset.rfl
  have hs : planarSliceBox (Icc a b) (Icc c d) ⊆
      planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀) :=
    planarSliceBox_mono (Icc_subset_Icc ha.le hb.le) (Icc_subset_Icc hc.le hd.le)
  have hx := physicalMeanIndex_horizontal_ACL_derivative hsch hsep hcoarea e hU y₀ π hπ he
    A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap (Icc c d) isCompact_Icc
    ha hab.le hb (hAG.mono_left hsx) B (hB.mono (image_mono hsx)) Ψ (hΨ.mono hsx)
    (fun z hz => hpos z (hsx hz)) (fun z hz => hproj z (hsx hz)) v
    (fun z hz => liftedMeanGeometricIndex_eq hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) Ψ z (hpos z (hsx hz)))
    (fun γ => (hF γ).mono (union_subset_union Subset.rfl (image_mono hsx))) (hinj.mono hsx)
  have hy := physicalMeanIndex_vertical_ACL_derivative hsch hsep hcoarea e hU y₀ π hπ he
    A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap (Icc a b) isCompact_Icc
    hc hcd.le hd (hAG.mono_left hsy) B (hB.mono (image_mono hsy)) Ψ (hΨ.mono hsy)
    (fun z hz => hpos z (hsy hz)) (fun z hz => hproj z (hsy hz)) v
    (fun z hz => liftedMeanGeometricIndex_eq hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) Ψ z (hpos z (hsy hz)))
    (fun γ => (hF γ).mono (union_subset_union Subset.rfl (image_mono hsy))) (hinj.mono hsy)
  have hacx := hx.mono fun _ h => h.1
  have hacy := hy.mono fun _ h => h.1
  have hbx := hx.mono fun _ h => h.2
  have hby := hy.mono fun _ h => h.2
  have hvmeas : AEStronglyMeasurable v₂ (volume.restrict (Icc a b ×ˢ Icc c d)) := by
    rw [← rectangle_restrict_Ioo_eq_Icc]
    exact aestronglyMeasurable_on_rectangle_of_ACL v₂ hab hcd hacx hacy
  obtain ⟨M, hM⟩ := bounded_liftedMeanGeometricIndex_on_compact hsch K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
    (isCompact_planarSliceBox isCompact_Icc isCompact_Icc) Ψ hΨ hpos
  let : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c d)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hv₂ : MemLp v₂ 2 (volume.restrict (Icc a b ×ˢ Icc c d)) := by
    apply MemLp.of_bound hvmeas M
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    exact hM ⟨p.1, p.2⟩ (hs ⟨hp.1, hp.2⟩)
  have hρ : Measurable ρ := (measurable_sliceChartDensity B hg).ennreal_toReal.comp
    Complex.measurableEquivRealProd.symm.measurable
  exact ⟨hv₂, exists_rectangle_weak_gradient hab.le hcd.le hv₂ hρ
    (sliceChartDensity_memLp_rectangle B g hg henergy a b c d) hacx hacy hbx hby⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedSobolevTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preserve a common pointwise derivative bound when transporting rectangle
weak derivatives into the Euclidean Sobolev witness. -/

open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem exists_bounded_rectangle_sobolev_witness
    {f Gx Gy r : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hf : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hx : MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hy : MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hbound : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d),
      |Gx p| ≤ r p ∧ |Gy p| ≤ r p)
    (hweak : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ioo c d →
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
        -(∫p in Icc a b ×ˢ Icc c d, Gx p * φ p) ∧
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
        -(∫p in Icc a b ×ˢ Icc c d, Gy p * φ p)) :
    ∃H : DeGiorgi.MemW1pWitness 2 (f ∘ euclideanPlaneCoordinates)
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)),
      ∀i : Fin 2, ∀ᵐ x ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)),
        |H.weakGrad x i| ≤ r (euclideanPlaneCoordinates x) := by
  let W := Ioo a b ×ˢ Ioo c d
  have hmp := euclideanPlaneCoordinates_measurePreserving.restrict_preimage (s := W)
    (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  have hf' : MemLp f 2 (volume.restrict W) := by rwa [rectangle_restrict_Ioo_eq_Icc]
  have hx' : MemLp Gx 2 (volume.restrict W) := by rwa [rectangle_restrict_Ioo_eq_Icc]
  have hy' : MemLp Gy 2 (volume.restrict W) := by rwa [rectangle_restrict_Ioo_eq_Icc]
  have hb' : ∀ᵐ p ∂volume.restrict W, |Gx p| ≤ r p ∧ |Gy p| ≤ r p := by
    rwa [rectangle_restrict_Ioo_eq_Icc]
  let G : EuclideanPlane → EuclideanPlane := fun x =>
    WithLp.toLp 2 fun i => if i = 0 then Gx (euclideanPlaneCoordinates x)
      else Gy (euclideanPlaneCoordinates x)
  let H : DeGiorgi.MemW1pWitness 2 (f ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' W) := {
    memLp := hf'.comp_measurePreserving hmp
    weakGrad := G
    weakGrad_component_memLp := by
      intro i
      fin_cases i
      · exact hx'.comp_measurePreserving hmp
      · exact hy'.comp_measurePreserving hmp
    isWeakGrad := by
      intro i
      fin_cases i
      · exact weakPartial_of_planar_identity 0 (1, 0) euclideanPlaneCoordinates_single_zero
          (fun φ hφ hs hsub => (hweak φ hφ hs hsub).1)
      · exact weakPartial_of_planar_identity 1 (0, 1) euclideanPlaneCoordinates_single_one
          (fun φ hφ hs hsub => (hweak φ hφ hs hsub).2) }
  refine ⟨H, ?_⟩
  intro i
  have hb := hmp.quasiMeasurePreserving.ae hb'
  filter_upwards [hb] with x hx
  fin_cases i
  · exact hx.1
  · exact hx.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalMeanIndexWitness
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local mean-index weak derivatives, transported to the
Euclidean Sobolev witness used by positive partition smoothing. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r609189_7 : BorelSpace Sphere := ⟨rfl⟩
theorem physicalMeanIndex_rectangle_sobolev_witness
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {a₀ a b b₀ c₀ c d d₀ : ℝ}
    (ha : a₀ < a) (hab : a < b) (hb : b < b₀)
    (hc : c₀ < c) (hcd : c < d) (hd : d < d₀)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (hpos : ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀), 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀),
      diskRayProjection (Ψ z) = F (π (z : Sphere)))
    (hF : ∀ γ : A, InjOn F (range γ.val ∪
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (hinj : InjOn (fun z : ℂ => F (π (z : Sphere)))
      (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀))) :
    let v := liftedMeanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) Ψ
    let v₂ : EuclideanPlane → ℝ := fun p => v ⟨p 0, p 1⟩
    ∃ H : DeGiorgi.MemW1pWitness 2 v₂
      (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)),
      ∀ i : Fin 2, ∀ᵐ p ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)),
        |H.weakGrad p i| ≤ (sliceChartDensity B g ⟨p 0, p 1⟩).toReal := by
  obtain ⟨hm, Gx, Gy, _, _, hx, hy, hbound, hweak⟩ :=
    physicalMeanIndex_rectangle_weak_gradient hsch hsep hcoarea e hU y₀ π hπ he
      A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap
      ha hab hb hc hcd hd hAG B hB Ψ hΨ hpos hproj hF hinj
  exact exists_bounded_rectangle_sobolev_witness hm hx hy hbound hweak

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ContinuousMeanIndexWitness
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous Sobolev branches of the actual descended mean circle map.
Continuity is derived from avoidance of each physical point by the source law. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
 local instance localInst_r609189_8 : BorelSpace Sphere := ⟨rfl⟩
theorem continuous_meanIndex_rectangle_witness
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {a₀ a b b₀ c₀ c d d₀ : ℝ}
    (ha : a₀ < a) (hab : a < b) (hb : b < b₀)
    (hc : c₀ < c) (hcd : c < d) (hd : d < d₀)
    (hAG : MapsTo ((↑) : ℂ → Sphere) (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)) G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (Ψ : ℂ → ℂ) (hΨ : ContinuousOn Ψ (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (hpos : ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀), 0 ≤ (Ψ z).im)
    (hproj : ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀),
      diskRayProjection (Ψ z) = F (π (z : Sphere)))
    (hF : ∀ γ : A, InjOn F (range γ.val ∪
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (hinj : InjOn (fun z : ℂ => F (π (z : Sphere)))
      (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)))
    (hmiss : ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀),
      ∀ᵐ γ : A ∂(η : Measure A), π (z : Sphere) ∉ range γ.val) :
    let W := euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)
    let v : EuclideanPlane → ℝ := fun p =>
      liftedMeanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) Ψ ⟨p 0, p 1⟩
    ContinuousOn v W ∧
      (∀ p ∈ W, (v p : UnitAddCircle) =
        diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F (π ((⟨p 0, p 1⟩ : ℂ) : Sphere)))) ∧
      ∃ H : DeGiorgi.MemW1pWitness 2 v W,
        ∀ i : Fin 2, ∀ᵐ p ∂volume.restrict W,
          |H.weakGrad p i| ≤ (sliceChartDensity B g ⟨p 0, p 1⟩).toReal := by
  let S := planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)
  let W := euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)
  let Z : EuclideanPlane → ℂ := fun p => ⟨p 0, p 1⟩
  have hZ : Continuous Z :=
    Complex.equivRealProdCLM.symm.continuous.comp euclideanPlaneCoordinates.continuous
  have hZS : MapsTo Z W S := by
    intro p hp
    exact ⟨⟨ha.le.trans hp.1.1.le, hp.1.2.le.trans hb.le⟩,
      ⟨hc.le.trans hp.2.1.le, hp.2.2.le.trans hd.le⟩⟩
  have hm (z : ℂ) (hz : z ∈ S) :
      ∀ᵐ γ : K ∂((η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure K) : Measure K),
        diskRayProjection (Ψ z) ∉ range γ.val := by
    rw [hproj z hz]
    apply ae_mapped_arc_avoids A K η F f hf hmap _ (hmiss z hz)
    intro γ
    apply (hF γ).mono
    exact union_subset_union Subset.rfl (singleton_subset_iff.mpr ⟨z, hz, rfl⟩)
  have hv := continuousOn_liftedMeanGeometricIndex hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
    Ψ hΨ hpos hm
  refine ⟨hv.comp hZ.continuousOn hZS, ?_, ?_⟩
  · intro p hp
    exact (diskMeanCircle_eq_local_mean hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
      (fun z => F (π (z : Sphere))) Ψ (Z p) (hpos _ (hZS hp)) (hproj _ (hZS hp))).symm
  · exact physicalMeanIndex_rectangle_sobolev_witness hsch hsep hcoarea e hU y₀ π hπ he
      A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap
      ha hab hb hc hcd hd hAG B hB Ψ hΨ hpos hproj hF hinj

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SliceDensityLp
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-chart slice density has finite L² norm in complex,
Cartesian and Euclidean coordinates. -/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem sliceChartDensity_complex_memLp
    (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    MemLp (fun z : ℂ => (sliceChartDensity B g z).toReal) 2 volume :=
  memLp_two_toReal_of_lintegral_sq_ne_top volume
    (measurable_sliceChartDensity B hg) (sliceChartDensity_sq_integral_finite B g hg henergy).ne

 theorem sliceChartDensity_realProd_memLp
    (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    MemLp (fun p : ℝ × ℝ => (sliceChartDensity B g ⟨p.1, p.2⟩).toReal) 2 volume :=
  (sliceChartDensity_complex_memLp B g hg henergy).comp_measurePreserving
    (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd)

 theorem sliceChartDensity_euclidean_memLp
    (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    MemLp (fun p : EuclideanPlane => (sliceChartDensity B g ⟨p 0, p 1⟩).toReal) 2 volume := by
  have heq : (fun p : EuclideanPlane => (sliceChartDensity B g ⟨p 0, p 1⟩).toReal) =
      (fun p : ℝ × ℝ => (sliceChartDensity B g ⟨p.1, p.2⟩).toReal) ∘
        euclideanPlaneCoordinates := by
    funext p
    rfl
  rw [heq]
  exact (sliceChartDensity_realProd_memLp B g hg henergy).comp_measurePreserving
    euclideanPlaneCoordinates_measurePreserving

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCircleSmoothing
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive smoothing of the actual circle-valued mean of the physical
arc law. Every local Sobolev witness is derived from occupation and coarea;
the smoothing discrepancy obeys the prescribed pointwise tolerance. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel


variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r609189_9 : BorelSpace Sphere := ⟨rfl⟩
theorem physical_mean_circle_smoothing
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (a₀ a b b₀ c₀ c d d₀ : ι → ℝ)
    (ha : ∀ j, a₀ j < a j) (hab : ∀ j, a j < b j) (hb : ∀ j, b j < b₀ j)
    (hc : ∀ j, c₀ j < c j) (hcd : ∀ j, c j < d j) (hd : ∀ j, d j < d₀ j)
    (hAG : ∀ j, MapsTo ((↑) : ℂ → Sphere)
      (planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j))) G)
    (B : ℝ≥0) (hB : ∀ j, LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j))))
    (Ψ : ι → ℂ → ℂ) (hΨ : ∀ j, ContinuousOn (Ψ j)
      (planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j))))
    (hpos : ∀ j z, z ∈ planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)) →
      0 ≤ (Ψ j z).im)
    (hproj : ∀ j z, z ∈ planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)) →
      diskRayProjection (Ψ j z) = F (π (z : Sphere)))
    (hF : ∀ j (γ : A), InjOn F (range γ.val ∪
      (fun z : ℂ => π (z : Sphere)) '' planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j))))
    (hinj : ∀ j, InjOn (fun z : ℂ => F (π (z : Sphere)))
      (planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j))))
    (hmiss : ∀ j z, z ∈ planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)) →
      ∀ᵐ γ : A ∂(η : Measure A), π (z : Sphere) ∉ range γ.val)
    (hsub : ∀ j, tsupport (ρ.weight j) ⊆
      euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (d j)))
    (τ : EuclideanPlane → ℝ) (hτ : ContinuousOn τ Ω) (hτpos : ∀ x ∈ Ω, 0 < τ x)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    let m : EuclideanPlane → UnitAddCircle := fun p =>
      diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F (π ((⟨p 0, p 1⟩ : ℂ) : Sphere)))
    ∃ (w : EuclideanPlane → UnitAddCircle) (R : EuclideanPlane → ℝ),
      FiniteTransfer.SmoothCircleOn w Ω ∧ ContinuousOn R Ω ∧ (∀ x, w x = m x + (R x : UnitAddCircle)) ∧
      (∀ x ∈ Ω, |R x| ≤ τ x) ∧
      ∀ i : Fin 2,
        MemLp (fun x => FiniteTransfer.circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) ∧
        eLpNorm (fun x => FiniteTransfer.circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) ≤ ε +
          eLpNorm (fun x : EuclideanPlane => (sliceChartDensity B g ⟨x 0, x 1⟩).toReal)
            2 (volume.restrict Ω) := by
  let W : ι → Set EuclideanPlane := fun j =>
    euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (d j))
  let u : ι → EuclideanPlane → ℝ := fun j p =>
    liftedMeanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (Ψ j) ⟨p 0, p 1⟩
  let m : EuclideanPlane → UnitAddCircle := fun p =>
    diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F (π ((⟨p 0, p 1⟩ : ℂ) : Sphere)))
  have hW (j : ι) : IsOpen (W j) :=
    (isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous
  have hlocal (j : ι) := continuous_meanIndex_rectangle_witness hsch hsep hcoarea e hU y₀ π hπ he
    A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap
    (ha j) (hab j) (hb j) (hc j) (hcd j) (hd j) (hAG j) B (hB j) (Ψ j)
    (hΨ j) (hpos j) (hproj j) (hF j) (hinj j) (hmiss j)
  choose H hH using fun j => (hlocal j).2.2
  obtain ⟨v, hv, hs, hvalue, herr⟩ := exists_circle_smoothing_with_tolerance
    ρ W hW hsub m u (fun j => (hlocal j).1) (fun j => (hlocal j).2.1) H τ hτ hτpos hε
  refine ⟨ρ.circleMix m u v, ρ.mix (fun j x => v j x - u j x), hs,
    ρ.mix_sub_continuousOn W hW hsub u v (fun j => (hlocal j).1)
      (fun j => (hv j).1.1.continuous), (fun _ => rfl), hvalue, ?_⟩
  intro i
  exact partition_field_energy ρ W (fun j => (hW j).measurableSet) hsub
    (fun j x => (H j).weakGrad x i)
    (fun j => ((H j).weakGrad_component_memLp i).aestronglyMeasurable)
    ((sliceChartDensity_euclidean_memLp B g hg henergy).restrict Ω)
    (fun j => hH j i)
    (((FiniteTransfer.contDiffOn_circleFDeriv Ω.isOpen hs).continuousOn.clm_apply continuousOn_const).aestronglyMeasurable
      Ω.isOpen.measurableSet) (herr i)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_OpenMeanCircleSmoothing
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing the actual physical mean on an open disk chart, with all
local logarithmic charts and the partition constructed internally. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r609189_10 : BorelSpace Sphere := ⟨rfl⟩
theorem open_physical_mean_circle_smoothing
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (D : TopologicalSpace.Opens ℂ) (hDG : MapsTo ((↑) : ℂ → Sphere) D G)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord (((↑) : ℂ → Sphere) '' D))
    (hw0 : ∀ z ∈ D, F (π (z : Sphere)) ≠ 0)
    (hw1 : ∀ z ∈ D, ‖F (π (z : Sphere))‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ (fun z : ℂ => π (z : Sphere)) '' D))
    (hinj : InjOn (fun z : ℂ => F (π (z : Sphere))) D)
    (hmiss : ∀ z ∈ D, ∀ᵐ γ : A ∂(η : Measure A), π (z : Sphere) ∉ range γ.val)
    (τ : EuclideanPlane → ℝ)
    (hτ : ContinuousOn τ (complexPlaneCoordinates ⁻¹' D))
    (hτpos : ∀ x ∈ complexPlaneCoordinates ⁻¹' D, 0 < τ x)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    let Ω : TopologicalSpace.Opens EuclideanPlane :=
      ⟨complexPlaneCoordinates ⁻¹' D, D.isOpen.preimage complexPlaneCoordinates.continuous⟩
    let m : EuclideanPlane → UnitAddCircle := fun p =>
      diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F (π (planeSphere p)))
    ∃ (w : EuclideanPlane → UnitAddCircle) (R : EuclideanPlane → ℝ),
      FiniteTransfer.SmoothCircleOn w Ω ∧ ContinuousOn R Ω ∧
      (∀ x, w x = m x + (R x : UnitAddCircle)) ∧ (∀ x ∈ Ω, |R x| ≤ τ x) ∧
      ∀ i : Fin 2,
        MemLp (fun x => FiniteTransfer.circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) ∧
        eLpNorm (fun x => FiniteTransfer.circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) ≤ ε +
          eLpNorm (fun x : EuclideanPlane => (sliceChartDensity B g ⟨x 0, x 1⟩).toReal)
            2 (volume.restrict Ω) := by
  let Q : ℂ → ℂ := fun z => F (π (z : Sphere))
  have hQ : Continuous Q := F.continuous.comp (hπ.comp OnePoint.continuous_coe)
  obtain ⟨ι, hι, ρ, a₀, a, b, b₀, c₀, c, d, d₀, Ψ,
    hnest, hrect, hΨ, hpos, hproj, hsub⟩ :=
    exists_logarithmic_rectangle_partition D Q hQ.continuousOn hw0 hw1
  let : Countable ι := hι
  exact physical_mean_circle_smoothing hsch hsep hcoarea e hU y₀ π hπ he
    A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap
    ρ a₀ a b b₀ c₀ c d d₀
    (fun j => (hnest j).1) (fun j => (hnest j).2.1) (fun j => (hnest j).2.2.1)
    (fun j => (hnest j).2.2.2.1) (fun j => (hnest j).2.2.2.2.1)
    (fun j => (hnest j).2.2.2.2.2)
    (fun j => hDG.mono_left (hrect j)) B
    (fun j => hB.mono (image_mono (hrect j))) Ψ hΨ hpos hproj
    (fun j γ => (hF γ).mono (union_subset_union Subset.rfl (image_mono (hrect j))))
    (fun j => hinj.mono (hrect j)) (fun j z hz => hmiss z (hrect j hz))
    hsub τ hτ hτpos hε

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_DustSmoothingTolerance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete smoothing tolerance is positive off the dust, uniformly
small, and tends to zero at every dust point. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem continuous_dustSmoothingTolerance
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    {q : X → Y} (hq : Continuous q) (B : Set Y) (ε : ℝ) :
    Continuous (dustSmoothingTolerance q B ε) :=
  (continuous_const.min ((continuous_infDist_pt B).comp hq)).div_const 2

 theorem dustSmoothingTolerance_pos
    {X Y : Type*} [MetricSpace Y] (q : X → Y) {B : Set Y}
    (hB : IsClosed B) (hne : B.Nonempty) {ε : ℝ} (hε : 0 < ε)
    {x : X} (hx : q x ∉ B) : 0 < dustSmoothingTolerance q B ε x :=
  div_pos (lt_min hε ((hB.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)

 theorem dustSmoothingTolerance_le_half
    {X Y : Type*} [MetricSpace Y] (q : X → Y) (B : Set Y) (ε : ℝ) (x : X) :
    dustSmoothingTolerance q B ε x ≤ ε / 2 :=
  div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

 theorem dustSmoothingTolerance_tendsto_zero
    {X Y : Type*} [MetricSpace Y] {l : Filter X} (q : X → Y)
    (B : Set Y) {s : Y} (hs : s ∈ B) {ε : ℝ} (hε : 0 ≤ ε)
    (hq : Tendsto q l (𝓝 s)) : Tendsto (dustSmoothingTolerance q B ε) l (𝓝 0) := by
  have hd : Tendsto (fun x => infDist (q x) B) l (𝓝 0) := by
    simpa only [Function.comp_def, infDist_zero_of_mem hs] using
      ((continuous_infDist_pt B).tendsto s).comp hq
  have hc : Tendsto (fun _ : X => ε) l (𝓝 ε) := tendsto_const_nhds
  have ht := (hc.min hd).div_const (2 : ℝ)
  change Tendsto (fun x => min ε (infDist (q x) B) / 2) l (𝓝 0)
  simpa only [min_eq_right hε, zero_div] using ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientLocalChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quotient neighborhood whose closure misses the image of infinity
has a bounded inverse physical chart. Domain points in it are covered
by that chart using the actual domain homeomorphism. -/

open Set Function
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem quotient_neighborhood_chart_covers
    {G U V : Set Sphere} (e : G ≃ₜ U) (π : Sphere → Sphere)
    (he : ∀ y : G, (e y).val = π y.val)
    (hinfty : π OnePoint.infty ∉ V) :
    ∀ x ∈ U ∩ V, ∃ z : ℂ,
      z ∈ (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V) ∧
      π (z : Sphere) = x := by
  intro x hx
  let y := e.symm ⟨x, hx.1⟩
  have hy : π y.val = x := by rw [← he y]; exact congrArg Subtype.val (e.apply_symm_apply _)
  have hyG : y.val ∈ G := y.property
  cases hp : y.val using OnePoint.rec with
  | infty =>
    have hyV : π y.val ∈ V := hy.symm ▸ hx.2
    exact (hinfty (by simpa only [hp] using hyV)).elim
  | coe z =>
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · simpa only [mem_preimage, ← hp] using hyG
    · change π (z : Sphere) ∈ V
      rw [← hp, hy]
      exact hx.2
    · rw [← hp]
      exact hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LocalPlaneCorrection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A physical smoothing error on a finite quotient chart descends to a
bounded correction. Its dust-distance tolerance forces it to vanish at
every dust point, including along approaches from other charts. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem exists_local_plane_correction
    {G U S : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hS : IsOpen S)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ y : G, (e y).val = π y.val) (hinf : π OnePoint.infty ∉ S)
    (δ : ℝ) (hδ : δ ∈ Icc 0 1) (r : EuclideanPlane → ℝ)
    (hr : ContinuousOn r (planeSphere ⁻¹' (G ∩ π ⁻¹' S)))
    (hbound : ∀ p ∈ planeSphere ⁻¹' (G ∩ π ⁻¹' S),
      |r p| ≤ dustSmoothingTolerance (π ∘ planeSphere) Uᶜ δ p) :
    ∃ R : Sphere → ℝ,
      ContinuousOn R (U ∩ S) ∧
      (∀ p ∈ planeSphere ⁻¹' (G ∩ π ⁻¹' S), R (π (planeSphere p)) = r p) ∧
      (∀ x, |R x| ≤ dustSmoothingTolerance id Uᶜ δ x) ∧
      (∀ x, |R x| ≤ 1) ∧
      ∀ x ∈ Uᶜ, Tendsto R (𝓝 x) (𝓝 0) := by
  classical
  let R : Sphere → ℝ := fun x => if hx : x ∈ U ∩ S then
    sphereFromPlaneFunction r (e.symm ⟨x, hx.1⟩).val else 0
  have hmap (p : G) : π p.val = (e p).val := (he p).symm
  have hRmap (p : Sphere) (hp : p ∈ G) (hS' : π p ∈ S) :
      R (π p) = sphereFromPlaneFunction r p := by
    have hx : π p ∈ U ∩ S := ⟨(hmap ⟨p, hp⟩) ▸ (e ⟨p, hp⟩).property, hS'⟩
    have heq : (⟨π p, hx.1⟩ : U) = e ⟨p, hp⟩ := Subtype.ext (hmap ⟨p, hp⟩)
    simp only [R, dite_eq_left hx, heq, Homeomorph.symm_apply_apply]
  have hplane (p : EuclideanPlane) (hp : p ∈ planeSphere ⁻¹' (G ∩ π ⁻¹' S)) :
      R (π (planeSphere p)) = r p := by
    rw [hRmap (planeSphere p) hp.1 hp.2]
    change sphereFromPlaneFunction r (complexPlaneCoordinates p : Sphere) = r p
    rw [sphereFromPlaneFunction_coe, ContinuousLinearEquiv.symm_apply_apply]
  have hphysical : ContinuousOn (sphereFromPlaneFunction r) (G ∩ π ⁻¹' S) := by
    intro y hy
    cases y using OnePoint.rec with
    | infty => exact (hinf hy.2).elim
    | coe z =>
      have hz : complexPlaneCoordinates.symm z ∈ planeSphere ⁻¹' (G ∩ π ⁻¹' S) := by
        change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∈ G ∩ π ⁻¹' S
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy
      have hopen := (hG.inter (hS.preimage hπ)).preimage continuous_planeSphere
      exact (sphereFromPlaneFunction_continuousAt_coe
        (hr.continuousAt (hopen.mem_nhds hz))).continuousWithinAt
  have hRcont : ContinuousOn R (U ∩ S) := by
    let q : ↥(U ∩ S) → G := fun x => e.symm ⟨x.val, x.property.1⟩
    have hq : Continuous q := e.symm.continuous.comp
      (continuous_subtype_val.subtype_mk fun x => x.property.1)
    have hqs (x : ↥(U ∩ S)) : π (q x).val ∈ S := by
      have hx : π (q x).val = x.val := (he (q x)).symm.trans
        (congrArg Subtype.val (e.apply_symm_apply ⟨x.val, x.property.1⟩))
      rw [hx]
      exact x.property.2
    have hc := hphysical.comp_continuous (continuous_subtype_val.comp hq)
      (fun x => ⟨(q x).property, hqs x⟩)
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact dite_eq_left x.property
  have hb (x : Sphere) : |R x| ≤ dustSmoothingTolerance id Uᶜ δ x := by
    by_cases hx : x ∈ U ∩ S
    · obtain ⟨z, hz, hez⟩ := quotient_neighborhood_chart_covers e π he hinf x hx
      let p := complexPlaneCoordinates.symm z
      have hp : p ∈ planeSphere ⁻¹' (G ∩ π ⁻¹' S) := by
        change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∈ G ∩ π ⁻¹' S
        simpa only [ContinuousLinearEquiv.apply_symm_apply, mem_preimage, mem_inter_iff] using hz
      have hpq : π (planeSphere p) = x := by
        simpa only [p, planeSphere, ContinuousLinearEquiv.apply_symm_apply] using hez
      rw [← hpq, hplane p hp]
      exact hbound p hp
    · simp only [R, dite_eq_right hx, abs_zero]
      exact div_nonneg (le_min hδ.1 infDist_nonneg) (by norm_num)
  refine ⟨R, hRcont, hplane, hb, ?_, ?_⟩
  · intro x
    exact (hb x).trans ((dustSmoothingTolerance_le_half id Uᶜ δ x).trans (by linarith [hδ.2]))
  · intro x hx
    exact tendsto_zero_of_abs_le_tolerance
      (dustSmoothingTolerance_tendsto_zero id Uᶜ hx hδ.1 tendsto_id)
      (Eventually.of_forall hb)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OpenMeanCorrection
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the single-valued quotient correction from the actual
physical smoothing. The tolerance and all dust limits are derived here. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r609189_11 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_open_mean_circle_correction
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U S : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hU : IsOpen U) (hS : IsOpen S)
    (y₀ : Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ y : G, (e y).val = π y.val) (hinf : π OnePoint.infty ∉ S)
    (hne : Uᶜ.Nonempty)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' S)))
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ≥0∞} (hε : 0 < ε) :
    let Ω : TopologicalSpace.Opens EuclideanPlane :=
      ⟨planeSphere ⁻¹' (G ∩ π ⁻¹' S), (hG.inter (hS.preimage hπ)).preimage continuous_planeSphere⟩
    ∃ (w : EuclideanPlane → UnitAddCircle) (R : Sphere → ℝ),
      FiniteTransfer.SmoothCircleOn w Ω ∧ ContinuousOn R (U ∩ S) ∧
      (∀ x, |R x| ≤ dustSmoothingTolerance id Uᶜ δ x) ∧
      (∀ x, |R x| ≤ 1) ∧
      (∀ x ∈ Uᶜ, Tendsto R (𝓝 x) (𝓝 0)) ∧
      (∀ p ∈ Ω, w p = diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
        (F (π (planeSphere p))) + (R (π (planeSphere p)) : UnitAddCircle)) ∧
      ∀ i : Fin 2,
        MemLp (fun x => FiniteTransfer.circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) ∧
        eLpNorm (fun x => FiniteTransfer.circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict Ω) ≤ ε +
          eLpNorm (fun x : EuclideanPlane => (sliceChartDensity B g ⟨x 0, x 1⟩).toReal)
            2 (volume.restrict Ω) := by
  let D : TopologicalSpace.Opens ℂ :=
    ⟨((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S,
      (hG.preimage OnePoint.continuous_coe).inter
        (hS.preimage (hπ.comp OnePoint.continuous_coe))⟩
  have hqU (z : ℂ) (hz : z ∈ D) : π (z : Sphere) ∈ U := by
    rw [← he ⟨(z : Sphere), hz.1⟩]
    exact (e ⟨(z : Sphere), hz.1⟩).property
  have hQinj : InjOn (fun z : ℂ => F (π (z : Sphere))) D := by
    intro z hz t ht heq
    have hqt := hinj hz.2 ht.2 heq
    have het : e ⟨(z : Sphere), hz.1⟩ = e ⟨(t : Sphere), ht.1⟩ :=
      Subtype.ext ((he ⟨(z : Sphere), hz.1⟩).trans
        (hqt.trans (he ⟨(t : Sphere), ht.1⟩).symm))
    exact OnePoint.coe_injective (congrArg Subtype.val (e.injective het))
  let τ := dustSmoothingTolerance (π ∘ planeSphere) Uᶜ δ
  have hτ : Continuous τ := continuous_dustSmoothingTolerance
    (hπ.comp continuous_planeSphere) Uᶜ δ
  have hτpos : ∀ p ∈ complexPlaneCoordinates ⁻¹' D, 0 < τ p := by
    intro p hp
    apply dustSmoothingTolerance_pos (π ∘ planeSphere) hU.isClosed_compl hne hδ
    exact fun hn => hn (hqU (complexPlaneCoordinates p) hp)
  obtain ⟨w, r, hw, hr, hwr, hrtol, hgrad⟩ := open_physical_mean_circle_smoothing
    hsch hsep hcoarea e hU y₀ π hπ he A hA η hfinite g hg hocc henergy
    K hK hKS F f hf hmap D (fun _ hz => hz.1) B hB
    (fun z hz => h0 _ hz.2) (fun z hz => h1 _ hz.2)
    (fun γ => (hF γ).mono (union_subset_union Subset.rfl (by
      rintro _ ⟨z, hz, rfl⟩
      exact hz.2))) hQinj (fun z hz => hmiss _ ⟨hqU z hz, hz.2⟩)
    τ hτ.continuousOn hτpos hε
  change ContinuousOn r (planeSphere ⁻¹' (G ∩ π ⁻¹' S)) at hr
  change ∀ p ∈ planeSphere ⁻¹' (G ∩ π ⁻¹' S),
    |r p| ≤ dustSmoothingTolerance (π ∘ planeSphere) Uᶜ δ p at hrtol
  obtain ⟨R, hRc, hRp, hRb, hR1, hRlim⟩ := exists_local_plane_correction e hG hS π hπ he
    hinf δ ⟨hδ.le, hδ1⟩ r hr hrtol
  refine ⟨w, R, hw, hRc, hRb, hR1, hRlim, ?_, hgrad⟩
  intro p hp
  rw [hRp p hp]
  exact hwr p

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanPeriodData
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single constructed mean-period coordinate retains its real atlas,
closed masked levels, vanishing correction, and actual smooth physical
representative. The analytic and topological data come from one law. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r609189_12 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_smooth_mean_period_data
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U S M : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hU : IsOpen U)
    (hS : IsOpen S) (hM : IsClosed M) (b : Sphere) (hbS : b ∉ S) (hbU : b ∉ U)
    (hMS : M \ {b} ⊆ S) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (hinf : π OnePoint.infty ∉ S)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' S)))
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F G U S M b π,
      (∀ x, |Q.error x| ≤ dustSmoothingTolerance id Uᶜ δ x) ∧
      ∀ i : Fin 2,
        MemLp (fun x => FiniteTransfer.circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
          2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))) ∧
        eLpNorm (fun x => FiniteTransfer.circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
          2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))) ≤ ε +
          eLpNorm (fun x : EuclideanPlane => (sliceChartDensity B g ⟨x 0, x 1⟩).toReal)
            2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))) := by
  obtain ⟨w, R, hw, hRc, hRtol, hRb, hRlim, hwp, hwgrad⟩ := exists_open_mean_circle_correction
    hsch hsep hcoarea e hG hU hS y₀ π hπ he hinf ⟨b, hbU⟩ A hA η hfinite
    g hg hocc henergy K hK hKS F f hf hmap B hB h0 h1 hF hinj hmiss δ hδ hδ1 hε
  have hmissK : ∀ x ∈ U ∩ S, ∀ᵐ γ : K ∂((η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure K) : Measure K),
      F x ∉ range γ.val := by
    intro x hx
    exact mapped_arc_point_avoidance A K η F f hf hmap x
      (fun γ => (hF γ).mono (union_subset_union Subset.rfl (singleton_subset_iff.mpr hx.2)))
      (hmiss x hx)
  obtain ⟨I, hI, V, a, C, u, hcover, hV, hlog, hbound, hcont, hu, htrans, hclosed, hdomain⟩ :=
    exists_perturbed_mean_period_graph hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F S U M hS hU hM
      b hbS hbU hMS h0 h1 hmissK R hRc hRb
  let Ω : Set EuclideanPlane := planeSphere ⁻¹' (G ∩ π ⁻¹' S)
  have hΩ : IsOpen Ω := (hG.inter (hS.preimage hπ)).preimage continuous_planeSphere
  obtain ⟨hwc, hwE⟩ := smooth_circle_complex_energy_finite hΩ w hw (fun i => (hwgrad i).1)
  let v := w ∘ complexPlaneCoordinates.symm
  have hv (z : ℂ) (hzG : (z : Sphere) ∈ G) (hzS : π (z : Sphere) ∈ S) :
      v z = diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F (π (z : Sphere))) +
        (R (π (z : Sphere)) : UnitAddCircle) := by
    have hplane : planeSphere (complexPlaneCoordinates.symm z) = (z : Sphere) :=
      congrArg ((↑) : ℂ → Sphere) (complexPlaneCoordinates.apply_symm_apply z)
    have hp : complexPlaneCoordinates.symm z ∈ Ω := by
      change planeSphere (complexPlaneCoordinates.symm z) ∈ G ∩ π ⁻¹' S
      rw [hplane]
      exact ⟨hzG, hzS⟩
    simpa only [v, Function.comp_apply, hplane] using hwp _ hp
  have hDom : complexPlaneCoordinates.symm ⁻¹' Ω =
      ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S := by
    ext z
    change planeSphere (complexPlaneCoordinates.symm z) ∈ G ∩ π ⁻¹' S ↔ _
    have hp : planeSphere (complexPlaneCoordinates.symm z) = (z : Sphere) :=
      congrArg ((↑) : ℂ → Sphere) (complexPlaneCoordinates.apply_symm_apply z)
    rw [hp]
    rfl
  rw [hDom] at hwc hwE
  have hve : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G ∩
      (fun z : ℂ => π (z : Sphere)) ⁻¹' S,
      ENNReal.ofReal ‖FiniteTransfer.circleFDeriv v z‖ ^ 2) < ∞ := hwE
  have hvs : FiniteTransfer.SmoothCircleOn v
      (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S) := hwc
  have hproj (i : I) (z : ℂ) (hzG : (z : Sphere) ∈ G) (hzV : π (z : Sphere) ∈ V i) :
      (u i (π (z : Sphere)) : UnitAddCircle) = v z := by
    have hzS := (hV i).2 (subset_closure hzV)
    have hp : diskRayProjection
        (upperHalfPlaneClamp (logarithmicCutChart (a i) (F (π (z : Sphere))))).val =
        F (π (z : Sphere)) := by
      rw [upperHalfPlaneClamp_val (logarithmicCutChart_nonneg (a i) (h1 _ hzS))]
      exact logarithmicCutChart_projection (a i) (h0 _ hzS)
    rw [hu i _ hzV, AddCircle.coe_add, hv z hzG hzS]
    congr 1
    have hm := (diskMeanCircle_projection hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
      (upperHalfPlaneClamp (logarithmicCutChart (a i) (F (π (z : Sphere)))))).symm
    rw [hp] at hm
    exact hm
  have hbranches (i : I) := period_branch_physical_energy e hG (hV i).1
    (fun x hx => (hV i).2 (subset_closure hx)) π hπ he (u i) (hcont i) v hvs (hproj i) hve
  exact ⟨{
    Index := I, countableIndex := hI, patch := V, angle := a, bound := C,
    branch := u, error := R, physical := v, euclidean := w, physical_eq := rfl, cover := hcover,
    patch_open := fun i => (hV i).1, patch_closure := fun i => (hV i).2,
    log_continuous := hlog, bounded := hbound, continuous := hcont,
    branch_value := hu, transition := htrans, closed := hclosed, domain_value := hdomain,
    error_continuous := hRc, error_bound := hRb, error_vanishes := hRlim, physical_smooth := hvs,
    physical_value := hv, physical_energy := hve,
    branch_smooth := fun i => (hbranches i).1, branch_energy := fun i => (hbranches i).2 },
    hRtol, hwgrad⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanGraphGeometry
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smoothed mean has the local real-band width and free-fiber
properties used by mixed grid geometry. These are derived from its
retained correction and the original arc law. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_18
theorem SmoothMeanPeriodData.branch_width_le_hit
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M : Set Sphere} (hdense : Dense U) {b : Sphere} {π : Sphere → Sphere}
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F G U S M b π)
    (i : Q.Index) {x : Sphere} (hx : x ∈ M \ U) (hxi : x ∈ Q.patch i) :
    limsup (Q.branch i) (𝓝[U] x) - liminf (Q.branch i) (𝓝[U] x) ≤
      (η : Measure A).real {γ | x ∈ range γ.val} := by
  have hxS : x ∈ S := Q.patch_closure i (subset_closure hxi)
  let L : Sphere → ClosedUpperHalfPlane := fun z =>
    upperHalfPlaneClamp (logarithmicCutChart (Q.angle i) (F z))
  have hLC : ContinuousAt L x := continuous_upperHalfPlaneClamp.continuousAt.comp
    ((Q.log_continuous i).continuousAt
      (mem_of_superset ((Q.patch_open i).mem_nhds hxi) subset_closure))
  have him : 0 < (logarithmicCutChart (Q.angle i) (F x)).im :=
    logarithmicCutChart_im_pos (Q.angle i) (h0 x hxS) (h1 x hx)
  have hLv : (L x).val = logarithmicCutChart (Q.angle i) (F x) :=
    upperHalfPlaneClamp_val him.le
  have hproj : diskRayProjection (L x).val = F x := by
    rw [hLv]
    exact logarithmicCutChart_projection (Q.angle i) (h0 x hxS)
  have heq : (fun z => Q.branch i z - meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L z))
      =ᶠ[𝓝[U] x] Q.error := by
    filter_upwards [nhdsWithin_le_nhds ((Q.patch_open i).mem_nhds hxi)] with z hz
    rw [Q.branch_value i z hz]
    exact add_sub_cancel_left _ _
  have herr := ((Q.error_vanishes x hx.2).mono_left nhdsWithin_le_nhds).congr' heq.symm
  exact (perturbed_mapped_mean_bands hsch hsep A K hK hKS η F f hf hmap x
    (fun γ => (hF γ).mono (union_subset_union Subset.rfl (singleton_subset_iff.mpr hxS)))
    U x (by rw [hdense.closure_eq]; trivial) L hLC.continuousWithinAt
    (by simpa only [hLv] using him) hproj (Q.branch i) herr).2.2

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem SmoothMeanPeriodData.free_fiber_subsingleton
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} (hdense : Dense U) {b : Sphere} {π : Sphere → Sphere}
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (Free : Set Sphere) (hFree : Free ⊆ Uᶜ) (hb : b ∉ Free)
    (hMS : M \ {b} ⊆ S) (hbS : b ∉ S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hmiss : ∀ x ∈ Free ∩ S, ∀ᵐ γ : K ∂(η : Measure K), F x ∉ range γ.val)
    {x : Sphere} (hx : x ∈ Free) :
    {θ : UnitAddCircle | (x, θ) ∈ periodBandGraph U M b Q.patch Q.branch}.Subsingleton := by
  have heq (θ : UnitAddCircle) := period_graph_mean_free_value hsch hsep K hK hKS η F
    U M S Free hdense b hb h0 h1 hmiss Q.patch Q.patch_open Q.patch_closure
    (fun i hi => hbS (Q.patch_closure i (subset_closure hi)))
    (hMS.trans Q.cover) Q.angle Q.bound Q.branch (fun i y _ => Q.bounded i y)
    Q.log_continuous Q.transition Q.error
    (fun y hy => (Q.error_vanishes y (hFree hy)).mono_left nhdsWithin_le_nhds)
    Q.branch_value x hx θ
  intro s hs t ht
  exact ((heq s).mp hs).2.symm.trans ((heq t).mp ht).2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanPhysicalBranches
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained mean branches project to the actual physical circle
coordinate. Its smoothness upgrades those continuous branches to smooth
real functions on the physical patch, as required by terminal filling. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_19
theorem SmoothMeanPeriodData.branch_physical_projection
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} {b : Sphere} {π : Sphere → Sphere}
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (i : Q.Index) {z : ℂ} (hz : (z : Sphere) ∈ G) (hi : π (z : Sphere) ∈ Q.patch i) :
    (Q.branch i (π (z : Sphere)) : UnitAddCircle) = Q.physical z := by
  have hs : π (z : Sphere) ∈ S := Q.patch_closure i (subset_closure hi)
  rw [Q.branch_value i _ hi, Q.physical_value z hz hs, AddCircle.coe_add]
  congr 1
  rw [← diskMeanCircle_projection hsch hsep K hK hKS η,
    upperHalfPlaneClamp_val (logarithmicCutChart_nonneg (Q.angle i) (h1 _ hs)),
    logarithmicCutChart_projection (Q.angle i) (h0 _ hs)]

 theorem SmoothMeanPeriodData.branch_physical_smooth
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} (hG : IsOpen G) {b : Sphere}
    {π : Sphere → Sphere} (hπ : Continuous π)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π) (i : Q.Index) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℂ => Q.branch i (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' Q.patch i) := by
  have hO : IsOpen (((↑) : ℂ → Sphere) ⁻¹' G ∩
      (fun z : ℂ => π (z : Sphere)) ⁻¹' Q.patch i) :=
    (hG.preimage OnePoint.continuous_coe).inter
      ((Q.patch_open i).preimage (hπ.comp OnePoint.continuous_coe))
  apply contDiffOn_real_lift hO
    (fun z hz => Q.physical_smooth z
      ⟨hz.1, Q.patch_closure i (subset_closure hz.2)⟩)
    (Q.branch_smooth i).continuousOn
  intro z hz
  exact Q.branch_physical_projection hsch hsep K hK hKS η F h0 h1 i hz.1 hz.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_GraphBoundaryBranches
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The graph avoidance supplied by the subordinate contour construction
implies exactly the inactive lattice avoidance of its local real lifts.
This applies equally to real coordinates and genuine period coordinates. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity
open FiniteTransfer

 theorem SmoothMeanPeriodData.physical_mem_graph
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : MeasureTheory.ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} {b : Sphere} {π : Sphere → Sphere}
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    {z : ℂ} (hzG : (z : Sphere) ∈ G) (hzU : π (z : Sphere) ∈ U)
    (hzM : π (z : Sphere) ∈ M) (hzS : π (z : Sphere) ∈ S) :
    (π (z : Sphere), Q.physical z) ∈ periodBandGraph U M b Q.patch Q.branch := by
  exact (Q.domain_value _ hzU _).mpr ⟨hzM, (Q.physical_value z hzG hzS).symm⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RealCircleRepresentative
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable real-plane representatives of smooth circle coordinates,
with the exact original L2 partial norms. No global real lift is used. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_real_circle_representative
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) (w : EuclideanPlane → UnitAddCircle)
    (hw : SmoothCircleOn w (euclideanPlaneCoordinates ⁻¹' D))
    (henergy : ∀ i : Fin 2, MemLp (fun x => circleFDeriv w x (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D))) :
    ∃ f : (ℝ × ℝ) → UnitAddCircle, Measurable f ∧ Measurable (circleGradient f) ∧
      SmoothCircleOn f D ∧ MemLp (circleGradient f) 2 (volume.restrict D) ∧
      (∀ i : Fin 2, eLpNorm (fun p => circleFDeriv f p
          (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict D) =
        eLpNorm (fun x => circleFDeriv w x (EuclideanSpace.single i 1))
          2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D))) ∧
      ∀ p ∈ D, f p = w (euclideanPlaneCoordinates.symm p) := by
  let q := euclideanPlaneCoordinates.symm
  let f₁ := w ∘ q
  have hΩ := hD.preimage euclideanPlaneCoordinates.continuous
  have hqin (p : ℝ × ℝ) (hp : p ∈ D) : q p ∈ euclideanPlaneCoordinates ⁻¹' D := by
    simpa only [q, mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp
  have hs : SmoothCircleOn f₁ D := by
    intro p hp a ha
    exact (hw (q p) (hqin p hp) a ha).comp p q.contDiff.contDiffAt
  have hmp : MeasurePreserving q (volume.restrict D)
      (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) := by
    convert euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage hΩ.measurableSet using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  have hpartial (i : Fin 2) (p : ℝ × ℝ) (hp : p ∈ D) :
      circleFDeriv f₁ p (if i = 0 then (1, 0) else (0, 1)) =
        circleFDeriv w (q p) (EuclideanSpace.single i 1) := by
    rw [circleFDeriv_comp hΩ hw q.differentiableAt (hqin p hp), q.fderiv]
    change circleFDeriv w (q p) (euclideanPlaneCoordinates.symm
      (if i = 0 then (1, 0) else (0, 1))) = _
    rw [euclideanPlaneCoordinates_symm_axis]
  let f : (ℝ × ℝ) → UnitAddCircle := D.piecewise f₁ (fun _ => 0)
  have heq (p : ℝ × ℝ) (hp : p ∈ D) : f =ᶠ[𝓝 p] f₁ := by
    filter_upwards [hD.mem_nhds hp] with x hx
    exact piecewise_eq_of_mem D _ _ hx
  have hmeas : Measurable f := hs.continuousOn.measurable_piecewise continuousOn_const hD.measurableSet
  have hsf : SmoothCircleOn f D := by
    apply smoothCircleOn_iff_local_lifts.mpr
    intro p hp
    obtain ⟨u, hu, hproj⟩ := smoothCircleOn_iff_local_lifts.mp hs p hp
    exact ⟨u, hu, hproj.trans (heq p hp).symm⟩
  have hder (i : Fin 2) : (fun p => circleFDeriv f p
      (if i = 0 then (1, 0) else (0, 1))) =ᵐ[volume.restrict D]
      (fun p => circleFDeriv w (q p) (EuclideanSpace.single i 1)) := by
    filter_upwards [ae_restrict_mem hD.measurableSet] with p hp
    have he := (heq p hp)
    have hf' : circleFDeriv f p = circleFDeriv f₁ p := by
      have hu : ContinuousAt (circleBranch f₁ (circleCut f₁ p)) p :=
        (hs p hp _ (circleCut_ne f₁ p)).continuousAt
      have hlift : (fun x => (circleBranch f₁ (circleCut f₁ p) x : UnitAddCircle)) =ᶠ[𝓝 p] f :=
        (show (fun x => (circleBranch f₁ (circleCut f₁ p) x : UnitAddCircle)) =ᶠ[𝓝 p] f₁ from
          Eventually.of_forall (coe_circleBranch f₁ _)).trans he.symm
      exact circleFDeriv_eq_lift
        ((hs.continuousOn.continuousAt (hD.mem_nhds hp)).congr he.symm) hu hlift
    rw [hf']
    exact hpartial i p hp
  have hi (i : Fin 2) : MemLp (fun p => circleFDeriv f p
      (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict D) :=
    ((henergy i).comp_measurePreserving hmp).ae_eq (hder i).symm
  refine ⟨f, hmeas, measurable_circleGradient hmeas, hsf,
    memLp_prod_iff.mpr ⟨hi 0, hi 1⟩, ?_, fun p hp => (heq p hp).self_of_nhds⟩
  intro i
  rw [eLpNorm_congr_ae (hder i)]
  exact eLpNorm_comp_measurePreserving
    (g := fun x => circleFDeriv w x (EuclideanSpace.single i 1)) (henergy i).aestronglyMeasurable hmp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanRealRepresentative
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply real-plane coordinate transport to the
smooth mean. The original quantitative partial norms are
retained and the physical circle values are unchanged in the domain. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem SmoothMeanPeriodData.euclidean_smooth
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} {b : Sphere} {π : Sphere → Sphere}
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π) :
    SmoothCircleOn Q.euclidean (planeSphere ⁻¹' (G ∩ π ⁻¹' S)) := by
  have heq : Q.physical ∘ complexPlaneCoordinates = Q.euclidean := by
    funext x
    rw [Q.physical_eq]
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [← heq]
  intro x hx a ha
  exact (Q.physical_smooth (complexPlaneCoordinates x) hx a ha).comp x
    complexPlaneCoordinates.contDiff.contDiffAt

 theorem SmoothMeanPeriodData.exists_real_representative
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} (hG : IsOpen G) (hS : IsOpen S) {b : Sphere}
    {π : Sphere → Sphere} (hπ : Continuous π)
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (henergy : ∀ i : Fin 2, MemLp (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
      2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S)))) :
    ∃ f : (ℝ × ℝ) → UnitAddCircle, Measurable f ∧ Measurable (circleGradient f) ∧
      SmoothCircleOn f (realChartDomain (G ∩ π ⁻¹' S)) ∧
      MemLp (circleGradient f) 2 (volume.restrict (realChartDomain (G ∩ π ⁻¹' S))) ∧
      (∀ i : Fin 2, eLpNorm (fun p => circleFDeriv f p
          (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (realChartDomain (G ∩ π ⁻¹' S))) =
        eLpNorm (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
          2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S)))) ∧
      ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        f (Complex.equivRealProdCLM z) = Q.physical z := by
  let D := realChartDomain (G ∩ π ⁻¹' S)
  have hD : IsOpen D := _root_.OAI.CircleDomainRigidity.FiniteTransfer.isOpen_realChartDomain (hG.inter (hS.preimage hπ))
  have hΩ : euclideanPlaneCoordinates ⁻¹' D = planeSphere ⁻¹' (G ∩ π ⁻¹' S) := rfl
  obtain ⟨f, hm, hdm, hs, hE, hn, hv⟩ := exists_real_circle_representative hD Q.euclidean
    (by rw [hΩ]; exact Q.euclidean_smooth hsch K hKS η F)
    (by rw [hΩ]; exact henergy)
  refine ⟨f, hm, hdm, hs, hE, ?_, ?_⟩
  · simpa only [hΩ] using hn
  · intro z hzG hzS
    have hzD : Complex.equivRealProdCLM z ∈ D := by
      simpa only [D, realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using
        (show (z : Sphere) ∈ G ∩ π ⁻¹' S from ⟨hzG, hzS⟩)
    rw [hv _ hzD, Q.physical_eq]
    rfl


 theorem SmoothMeanPeriodData.real_branch_smooth
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} (hG : IsOpen G) {b : Sphere}
    {π : Sphere → Sphere} (hπ : Continuous π)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π) (i : Q.Index) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => Q.branch i (π (Complex.equivRealProdCLM.symm p : Sphere)))
      (realChartDomain G ∩ realChartDomain (π ⁻¹' Q.patch i)) := by
  exact (Q.branch_physical_smooth hsch hsep K hK hKS η F hG hπ h0 h1 i).comp
    Complex.equivRealProdCLM.symm.contDiff.contDiffOn (fun _ hp => hp)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MeanMaskedPhysicalData
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected smooth mean supplies the actual physical inputs to
masked finite transfer. Its closed-mask energy is obtained by restricting
the original open-mask energy, without enlarging any norm. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem SmoothMeanPeriodData.exists_masked_physical_data
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} (hG : IsOpen G) (hS : IsOpen S) (hM : IsClosed M)
    {b : Sphere} (hbU : b ∉ U) (hMS : M \ {b} ⊆ S)
    {π : Sphere → Sphere} (hπ : Continuous π)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (henergy : ∀ i : Fin 2, MemLp (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
      2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S)))) :
    ∃ f : (ℝ × ℝ) → UnitAddCircle, Measurable f ∧ Measurable (circleGradient f) ∧
      SmoothCircleOn f (realChartDomain G ∩ interior (physicalMask π M)) ∧
      MemLp (circleGradient f) 2 ((volume.restrict (realChartDomain G)).restrict (physicalMask π M)) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        f (Complex.equivRealProdCLM z) = Q.physical z) ∧
      (∀ x ∈ realChartDomain G ∩ interior (physicalMask π M),
        (π (Complex.equivRealProdCLM.symm x : Sphere), f x) ∈
          periodBandGraph U M b Q.patch Q.branch) ∧
      (∀ i, ContDiffOn ℝ ∞
        (fun x : ℝ × ℝ => Q.branch i (π (Complex.equivRealProdCLM.symm x : Sphere)))
        (realChartDomain G ∩ realChartDomain (π ⁻¹' Q.patch i))) ∧
      (∀ i x, x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' Q.patch i) →
        (Q.branch i (π (Complex.equivRealProdCLM.symm x : Sphere)) : UnitAddCircle) = f x) ∧
      (∀ i : Fin 2, eLpNorm (fun p => circleFDeriv f p
          (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (realChartDomain (G ∩ π ⁻¹' S))) =
        eLpNorm (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
          2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S)))) := by
  obtain ⟨f, hmf, hdf, hsf, hEf, hn, hval⟩ :=
    Q.exists_real_representative hsch K hKS η F hG hS hπ henergy
  have hMSphysical (z : ℂ) (hzG : (z : Sphere) ∈ G) (hzM : π (z : Sphere) ∈ M) :
      π (z : Sphere) ∈ S := by
    apply hMS
    refine ⟨hzM, ?_⟩
    intro heq
    exact hbU (heq ▸ hPU z hzG)
  have hsub : realChartDomain G ∩ physicalMask π M ⊆ realChartDomain (G ∩ π ⁻¹' S) := by
    intro x hx
    exact ⟨hx.1, hMSphysical _ hx.1 hx.2⟩
  have hMm : MeasurableSet (physicalMask π M) :=
    ((hM.preimage hπ).preimage
      (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)).measurableSet
  have hE : MemLp (circleGradient f) 2
      ((volume.restrict (realChartDomain G)).restrict (physicalMask π M)) := by
    rw [Measure.restrict_restrict hMm, inter_comm]
    exact hEf.mono_measure (Measure.restrict_mono_set volume hsub)
  refine ⟨f, hmf, hdf, (fun x hx => hsf x (hsub ⟨hx.1, interior_subset hx.2⟩)),
    hE, hval, ?_, ?_, ?_, hn⟩
  · intro x hx
    have hzG : (Complex.equivRealProdCLM.symm x : Sphere) ∈ G := hx.1
    have hzM : π (Complex.equivRealProdCLM.symm x : Sphere) ∈ M :=
      (show x ∈ physicalMask π M from interior_subset hx.2)
    have hzS := hMSphysical _ hzG hzM
    have hv := hval _ hzG hzS
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hv
    rw [hv]
    exact Q.physical_mem_graph hsch K hKS η F hzG (hPU _ hzG) hzM hzS
  · exact fun i => Q.real_branch_smooth hsch hsep K hK hKS η F hG hπ h0 h1 i
  · intro i x hx
    have hzS := Q.patch_closure i (subset_closure hx.2)
    have hv := hval _ hx.1 hzS
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hv
    exact (Q.branch_physical_projection hsch hsep K hK hKS η F h0 h1 i hx.1 hx.2).trans hv.symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanMarkedBranchBands
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chosen chart is retained together with each marked interval.
This lets the same branch supply both the graph incidence interval and
the physical terminal staircase estimate. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_20
theorem SmoothMeanPeriodData.exists_marked_branch_band
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M : Set Sphere} (hdense : Dense U) {b : Sphere} {π : Sphere → Sphere}
    (hMS : M \ {b} ⊆ S) (hbS : b ∉ S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F G U S M b π)
    {x : Sphere} (hx : x ∉ U) :
    ∃ lo hi : ℝ, 0 ≤ hi - lo ∧
      hi - lo ≤ (if x = b then 1 else (η : Measure A).real {γ | x ∈ range γ.val}) ∧
      {θ : UnitAddCircle | (x, θ) ∈ periodBandGraph U M b Q.patch Q.branch} ⊆
        ((↑) : ℝ → UnitAddCircle) '' Icc lo hi ∧
      (x ∈ M → x ≠ b → ∃ i : Q.Index, x ∈ Q.patch i ∧
        lo = liminf (Q.branch i) (𝓝[U] x) ∧ hi = limsup (Q.branch i) (𝓝[U] x)) := by
  classical
  by_cases hxb : x = b
  · refine ⟨0, 1, by norm_num, by simp only [hxb, ite_true, if_true, sub_zero, le_refl], ?_, ?_⟩
    intro θ _
    refine ⟨unitCircleCut θ, ?_, ?_⟩
    · simpa only [unitCircleCut, zero_add, mem_Icc] using
        (show (0 : ℝ) ≤ (AddCircle.equivIco (1 : ℝ) 0 θ : ℝ) ∧
          (AddCircle.equivIco (1 : ℝ) 0 θ : ℝ) ≤ 0 + 1 from
          ⟨(AddCircle.equivIco (1 : ℝ) 0 θ).property.1,
            (AddCircle.equivIco (1 : ℝ) 0 θ).property.2.le⟩)
    · simp only [unitCircleCut, AddCircle.coe_equivIco]
    · intro _ hne
      exact (hne hxb).elim
  by_cases hxM : x ∈ M
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp (Q.cover (hMS ⟨hxM, hxb⟩))
    let lo := liminf (Q.branch i) (𝓝[U] x)
    let hi := limsup (Q.branch i) (𝓝[U] x)
    let : NeBot (𝓝[U] x) := mem_closure_iff_nhdsWithin_neBot.mp
      (show x ∈ closure U by rw [hdense.closure_eq]; trivial)
    have hbnd : ∀ᶠ y in 𝓝[U] x, -(Q.bound i) ≤ Q.branch i y ∧ Q.branch i y ≤ Q.bound i :=
      Eventually.of_forall (fun y => abs_le.mp (Q.bounded i y))
    have hle : lo ≤ hi := liminf_le_limsup
      (isBoundedUnder_of_eventually_le (hbnd.mono fun _ h => h.2))
      (isBoundedUnder_of_eventually_ge (hbnd.mono fun _ h => h.1))
    refine ⟨lo, hi, sub_nonneg.mpr hle, ?_, ?_, ?_⟩
    · simpa only [hxb, ite_false, if_false] using Q.branch_width_le_hit hsch hsep A K hK hKS η F f hf
        hmap hdense h0 h1 hF i ⟨hxM, hx⟩ hxi
    · have hcompat : ∀ i j y, y ∈ Q.patch i → y ∈ Q.patch j → ∀ θ,
          (y, θ) ∈ circleBandGraph U (Q.branch i) ↔
            (y, θ) ∈ circleBandGraph U (Q.branch j) := by
        intro i j y hyi hyj θ
        obtain ⟨k, hk⟩ := Q.transition i j y hyi hyj
        exact (Set.ext_iff.mp (circleBand_fiber_eq_of_eventually_add_int hk) θ).symm
      rw [periodBandGraph_fiber_on_patch U M b Q.patch Q.branch
        (fun i hi => hbS (Q.patch_closure i (subset_closure hi))) hcompat hxM hxi,
        circleBandGraph_fiber_eq_image_realFiber,
        intervalFiberHull_clusterGraph_eq_boundary_band
          (fun y _ => Q.bounded i y) (show x ∈ closure U by rw [hdense.closure_eq]; trivial)]
    · exact fun _ _ => ⟨i, hxi, rfl, rfl⟩
  · refine ⟨0, 0, by norm_num, ?_, ?_, ?_⟩
    · simp only [hxb, ite_false, if_false, sub_self]
      exact measureReal_nonneg
    · intro θ hθ
      exact (hxM hθ.1).elim
    · exact fun h _ => (hxM h).elim

 theorem SmoothMeanPeriodData.exists_marked_branch_band_family
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M : Set Sphere} (hdense : Dense U) {b : Sphere} {π : Sphere → Sphere}
    (hMS : M \ {b} ⊆ S) (hbS : b ∉ S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F G U S M b π)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U)
    (hend : ∀ γ : A, b ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2)) :
    ∃ lo hi : T → ℝ,
      (∀ s, 0 ≤ hi s - lo s) ∧
      (∀ s, hi s - lo s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      Summable (fun s => (hi s - lo s) ^ 2) ∧
      (∀ s, {θ : UnitAddCircle | (σ s, θ) ∈ periodBandGraph U M b Q.patch Q.branch} ⊆
        ((↑) : ℝ → UnitAddCircle) '' Icc (lo s) (hi s)) ∧
      ∀ s, σ s ∈ M → σ s ≠ b → ∃ i : Q.Index, σ s ∈ Q.patch i ∧
        lo s = liminf (Q.branch i) (𝓝[U] (σ s)) ∧
        hi s = limsup (Q.branch i) (𝓝[U] (σ s)) := by
  classical
  choose lo hi hnon hbound hfiber hbranch using fun s =>
    Q.exists_marked_branch_band hsch hsep A K hK hKS η F f hf hmap hdense hMS hbS h0 h1 hF (hσ s)
  have hhit : (η : Measure A).real {γ | b ∈ range γ.val} = 1 := by
    have heq : {γ : A | b ∈ range γ.val} = univ := eq_univ_of_forall hend
    simp only [heq, measureReal_def, measure_univ, ENNReal.toReal_one]
  have hle (s : T) : hi s - lo s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val} := by
    by_cases hs : σ s = b
    · simpa only [hs, ite_true, if_true, hhit] using hbound s
    · simpa only [hs, ite_false, if_false] using hbound s
  refine ⟨lo, hi, hnon, hle, ?_, hfiber, hbranch⟩
  exact Summable.of_nonneg_of_le (fun s => sq_nonneg _) (fun s =>
    (sq_le_sq₀ (hnon s) measureReal_nonneg).mpr (hle s)) hbudget

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SourceStokesBudgetEstimate
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative bounds for the actual source budget, on the same closed
mask and with the singular label omitted from the point-hit norm. -/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateData.sourceStokesBudget_le
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) (hπ : Continuous π) {R : ℝ} (hR : 0 ≤ R)
    {A : ℝ≥0∞} (hA : A ≠ ∞)
    (hpartial : ∀ i : Fin 2, eLpNorm (fun x => circleFDeriv C.physical x
      (if i = 0 then (1, 0) else (0, 1))) 2
      (volume.restrict (realChartDomain G ∩ physicalMask π C.mask)) ≤ A)
    {T : Type*} (w : T → ℝ≥0∞) (e : {s : S // s ≠ C.singular} → T)
    (he : Function.Injective e)
    (hwidth : ∀ s : {s : S // s ≠ C.singular}, ENNReal.ofReal (C.upper s - C.lower s) ≤ w (e s))
    (hw : (∑' t, w t ^ 2) < ∞) :
    C.sourceStokesBudget R ≤
      2 * Real.sqrt Real.pi * R * A.toReal + 2 * Real.pi * R * (countingSquareNorm w).toReal := by
  have hmask : MeasurableSet (physicalMask π C.mask) := by
    exact ((C.mask_closed.preimage hπ).preimage
      (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)).measurableSet
  have henergy := C.energy
  rw [Measure.restrict_restrict hmask, inter_comm] at henergy
  have hx := ENNReal.toReal_mono hA (hpartial 0)
  have hy := ENNReal.toReal_mono hA (hpartial 1)
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero] at hx hy
  have hnorm := circle_gradient_norm_le_partial_norms henergy
  have hnorm' : Real.sqrt (∫ x in realChartDomain G ∩ physicalMask π C.mask,
      fieldEnergy (circleGradient C.physical) (fun z => sphericalMetricFactor z • 1) x) ≤
      2 * A.toReal := by linarith
  have hband := real_square_norm_le_counting
    (fun s : {s : S // s ≠ C.singular} => C.upper s - C.lower s) w e he
    (fun s => C.width_nonneg s) hwidth hw
  unfold sourceStokesBudget
  calc
    _ ≤ Real.sqrt Real.pi * R * (2 * A.toReal) +
        2 * Real.pi * R * (countingSquareNorm w).toReal := by gcongr
    _ = _ := by ring

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SliceDensityNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slice density used by the smoothed mean has a quantitative L²
bound in the same Euclidean chart as its partial derivatives. -/

open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

 theorem eLpNorm_toReal_le_square_integral
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (g : X → ℝ≥0∞)
    (hmem : MemLp (fun x => (g x).toReal) 2 μ) :
    eLpNorm (fun x => (g x).toReal) 2 μ ≤ (∫⁻ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply lintegral_mono
  intro x
  apply pow_le_pow_left'
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

 theorem sliceChartDensity_complex_eLpNorm_le
    (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    eLpNorm (fun z : ℂ => (sliceChartDensity B g z).toReal) 2 volume ≤
      (2 * (B : ℝ≥0∞)) * (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) := by
  apply (eLpNorm_toReal_le_square_integral volume (sliceChartDensity B g)
    (sliceChartDensity_complex_memLp B g hg henergy)).trans
  have h := ENNReal.rpow_le_rpow (sliceChartDensity_sq_integral_le B g hg)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h
  have hconst : (4 * (B : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) = 2 * B := by
    rw [show (4 : ℝ≥0∞) * B ^ 2 = (2 * (B : ℝ≥0∞)) ^ 2 by ring,
      ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  rwa [hconst] at h

 theorem sliceChartDensity_euclidean_eLpNorm_le
    (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (Ω : Set EuclideanPlane) :
    eLpNorm (fun x : EuclideanPlane => (sliceChartDensity B g ⟨x 0, x 1⟩).toReal)
      2 (volume.restrict Ω) ≤
      (2 * (B : ℝ≥0∞)) * (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) := by
  have hmp : MeasurePreserving complexPlaneCoordinates volume volume :=
    (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).comp
      euclideanPlaneCoordinates_measurePreserving
  calc
    _ ≤ eLpNorm (fun x : EuclideanPlane => (sliceChartDensity B g ⟨x 0, x 1⟩).toReal)
        2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm (fun z : ℂ => (sliceChartDensity B g z).toReal) 2 volume :=
      eLpNorm_comp_measurePreserving
        (sliceChartDensity_complex_memLp B g hg henergy).aestronglyMeasurable hmp
    _ ≤ _ := sliceChartDensity_complex_eLpNorm_le B g hg henergy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanCoordinateData
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mean of the chosen law supplies a masked coordinate,
including all marked bands and the original point-hit bound. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

theorem SmoothMeanPeriodData.exists_coordinate_data_with_norms
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M : Set Sphere} (hG : IsOpen G) (hdense : Dense U)
    (hS : IsOpen S) (hM : IsClosed M) (hboundary : frontier M ⊆ U)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U)
    (singular : T) (hbU : σ singular ∉ U)
    (hMS : M \ {σ singular} ⊆ S) (hbS : σ singular ∉ S)
    {π : Sphere → Sphere} (hπ : Continuous π)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (hfreeU : π '' Gᶜ ⊆ Uᶜ)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hstrict : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F G U S M (σ singular) π)
    (henergy : ∀ i : Fin 2, MemLp (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
      2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))))
    (hend : ∀ γ : A, σ singular ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2))
    (hmiss : ∀ x ∈ ((π '' Gᶜ) \ range σ) ∩ S,
      ∀ᵐ γ : K ∂(η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure K), F x ∉ range γ.val) :
    ∃ C : MaskedCoordinateData G U π σ,
      C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
      C.mask = M ∧ C.singular = singular ∧
      (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        C.physical (Complex.equivRealProdCLM z) = Q.physical z) ∧
      ∀ i : Fin 2, eLpNorm (fun x => circleFDeriv C.physical x
          (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (realChartDomain G ∩ physicalMask π C.mask)) ≤
        eLpNorm (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
          2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))) := by
  obtain ⟨p, hmp, hdp, hsp, hEp, hpval, hpgraph, hpbranch, hpproj, hnorm⟩ :=
    Q.exists_masked_physical_data hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F hG hS hM hbU hMS hπ hPU
      h0 h1 henergy
  obtain ⟨lo, hi, hn, hhit, hsum, hband, hbranches⟩ :=
    Q.exists_marked_branch_band_family hsch hsep A K hK hKS η F f hf hmap hdense hMS hbS
      h0 hstrict hF σ hσ hend hbudget
  refine ⟨{
    graph := periodBandGraph U M (σ singular) Q.patch Q.branch
    graph_closed := Q.closed
    mask := M
    mask_closed := hM
    mask_frontier := hboundary
    singular := singular
    Index := Q.Index
    patch := Q.patch
    patch_open := Q.patch_open
    cover := hMS.trans Q.cover
    branch := Q.branch
    bound := Q.bound
    branch_bounded := Q.bounded
    physical := p
    measurable := hmp
    gradient_measurable := hdp
    smooth := hsp
    energy := hEp
    physical_graph := hpgraph
    branch_smooth := hpbranch
    branch_projection := hpproj
    lower := lo
    upper := hi
    width_nonneg := hn
    width_summable := hsum
    marked_fiber := hband
    marked_branch := hbranches
    free_fiber := ?_ }, rfl, rfl, rfl, hhit, hpval, ?_⟩
  · intro x hx hxr
    exact Q.free_fiber_subsingleton hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F hdense
      ((π '' Gᶜ) \ range σ) (fun x hx => hfreeU hx.1)
      (fun h => h.2 (mem_range_self singular)) hMS hbS h0 h1 hmiss ⟨hx, hxr⟩
  · intro i
    rw [← hnorm i]
    apply eLpNorm_mono_measure
    apply Measure.restrict_mono_set
    intro x hx
    refine ⟨hx.1, hMS ⟨hx.2, ?_⟩⟩
    intro heq
    exact hbU (heq ▸ hPU _ hx.1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MeanCoordinateBudget
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original smoothed mean, with its quantitative source Stokes
budget retained through physical coordinate assembly. -/

open Set Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

theorem SmoothMeanPeriodData.exists_coordinate_data_with_budget
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M : Set Sphere} (hG : IsOpen G) (hdense : Dense U)
    (hS : IsOpen S) (hM : IsClosed M) (hboundary : frontier M ⊆ U)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U)
    (singular : T) (hbU : σ singular ∉ U)
    (hMS : M \ {σ singular} ⊆ S) (hbS : σ singular ∉ S)
    {π : Sphere → Sphere} (hπ : Continuous π)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (hfreeU : π '' Gᶜ ⊆ Uᶜ)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hstrict : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F G U S M (σ singular) π)
    (henergy : ∀ i : Fin 2, MemLp (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
      2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))))
    (hend : ∀ γ : A, σ singular ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2))
    (hmiss : ∀ x ∈ ((π '' Gᶜ) \ range σ) ∩ S,
      ∀ᵐ γ : K ∂(η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure K), F x ∉ range γ.val)
    {R : ℝ} (hR : 0 ≤ R) {N : ℝ≥0∞} (hN : N ≠ ∞)
    (hnorm : ∀ i : Fin 2,
      eLpNorm (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
        2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))) ≤ N)
    (w : T → ℝ≥0∞) (hw : (∑' t, w t ^ 2) < ∞)
    (hwp : ∀ s, s ≠ singular → (η : Measure A) {γ | σ s ∈ range γ.val} ≤ w s) :
    ∃ C : MaskedCoordinateData G U π σ,
      C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
      C.mask = M ∧ C.singular = singular ∧
      (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        C.physical (Complex.equivRealProdCLM z) = Q.physical z) ∧
      C.sourceStokesBudget R ≤ 2 * Real.sqrt Real.pi * R * N.toReal +
        2 * Real.pi * R * (countingSquareNorm w).toReal := by
  obtain ⟨C, hg, hm, hs, hwidth, hv, hn⟩ := Q.exists_coordinate_data_with_norms
    hsch hsep A K hK hKS η F f hf hmap hG hdense hS hM hboundary σ hσ singular hbU hMS hbS
    hπ hPU hfreeU h0 h1 hstrict hF henergy hend hbudget hmiss
  refine ⟨C, hg, hm, hs, hwidth, hv, ?_⟩
  apply C.sourceStokesBudget_le hπ hR hN (fun i => (hn i).trans (hnorm i))
    w Subtype.val Subtype.val_injective _ hw
  intro s
  have hs' : (s : T) ≠ singular := by simpa only [hs] using s.property
  calc
    ENNReal.ofReal (C.upper s - C.lower s) ≤
        ENNReal.ofReal ((η : Measure A).real {γ | σ s ∈ range γ.val}) :=
      ENNReal.ofReal_le_ofReal (hwidth s)
    _ = (η : Measure A) {γ | σ s ∈ range γ.val} := ofReal_measureReal (measure_ne_top _ _)
    _ ≤ w s := hwp s hs'

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SmallMeanBudget
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small occupation and punctured hit norms used by compact arc
reduction imply the quantitative strict Stokes budget needed for exclusion. -/

open Set MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem meanBudgetTolerance_pos (B : ℝ≥0) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    0 < meanBudgetTolerance B R δ := by
  apply ENNReal.ofReal_pos.mpr
  apply div_pos hδ
  have hc : 0 ≤ meanBudgetConstant B R := by unfold meanBudgetConstant; positivity
  linarith

 theorem meanBudgetTolerance_ne_top (B : ℝ≥0) (R δ : ℝ) :
    meanBudgetTolerance B R δ ≠ ∞ := ENNReal.ofReal_ne_top

 theorem mean_budget_lt_of_small_norms
    (B : ℝ≥0) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    {a b : ℝ≥0∞} (hsmall : a + b < meanBudgetTolerance B R δ) :
    2 * Real.sqrt Real.pi * R *
        (meanBudgetTolerance B R δ + (2 * (B : ℝ≥0∞)) * a).toReal +
      2 * Real.pi * R * b.toReal < δ := by
  let t : ℝ := δ / (meanBudgetConstant B R + 1)
  have hc : 0 ≤ meanBudgetConstant B R := by unfold meanBudgetConstant; positivity
  have ht : 0 < t := div_pos hδ (by linarith)
  have ha : a ≤ ENNReal.ofReal t := (le_add_right le_rfl).trans hsmall.le
  have hb : b ≤ ENNReal.ofReal t := (le_add_left le_rfl).trans hsmall.le
  have ha' : a.toReal ≤ t := by
    simpa only [ENNReal.toReal_ofReal ht.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top ha
  have hb' : b.toReal ≤ t := by
    simpa only [ENNReal.toReal_ofReal ht.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  have he : (meanBudgetTolerance B R δ + (2 * (B : ℝ≥0∞)) * a).toReal =
      t + (2 * (B : ℝ)) * a.toReal := by
    rw [ENNReal.toReal_add (meanBudgetTolerance_ne_top B R δ)
      (ENNReal.mul_ne_top (by finiteness) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha)),
      ENNReal.toReal_mul]
    simp only [meanBudgetTolerance, ENNReal.toReal_ofReal ht.le, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal, ENNReal.toReal_mul, t]
  rw [he]
  calc
    _ ≤ 2 * Real.sqrt Real.pi * R * (t + (2 * (B : ℝ)) * t) +
        2 * Real.pi * R * t := by gcongr
    _ = meanBudgetConstant B R * t := by unfold meanBudgetConstant; ring
    _ < (meanBudgetConstant B R + 1) * t := by nlinarith
    _ = δ := mul_div_cancel₀ δ (by linarith : meanBudgetConstant B R + 1 ≠ 0)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanCoordinateConstruction
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact arc law constructs one actual smooth masked coordinate,
with the smoothing error, original point-hit widths and full source
Stokes budget all retained from the same construction. -/

open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r609189_13 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_smooth_mean_coordinate_with_budget
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U S M : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hU : IsOpen U)
    (hdense : Dense U) (hS : IsOpen S) (hM : IsClosed M) (hboundary : frontier M ⊆ U)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U) (singular : T)
    (hbS : σ singular ∉ S) (hMS : M \ {σ singular} ⊆ S) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (hfreeU : π '' Gᶜ ⊆ Uᶜ) (hinf : π OnePoint.infty ∉ S)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' S)))
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hstrict : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (hmissFree : ∀ x ∈ ((π '' Gᶜ) \ range σ) ∩ S,
      ∀ᵐ γ : K ∂(η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure K), F x ∉ range γ.val)
    (hend : ∀ γ : A, σ singular ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2))
    (w : T → ℝ≥0∞) (hw : (∑' t, w t ^ 2) < ∞)
    (hwp : ∀ s, s ≠ singular → (η : Measure A) {γ | σ s ∈ range γ.val} ≤ w s)
    {R : ℝ} (hR : 0 ≤ R)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε : ℝ≥0∞} (hε : 0 < ε) (hεfin : ε ≠ ∞) :
    ∃ (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F G U S M (σ singular) π)
      (C : MaskedCoordinateData G U π σ),
      (∀ x, |Q.error x| ≤ dustSmoothingTolerance id Uᶜ δ x) ∧
      C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
      C.mask = M ∧ C.singular = singular ∧
      (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        C.physical (Complex.equivRealProdCLM z) = Q.physical z) ∧
      C.sourceStokesBudget R ≤
        2 * Real.sqrt Real.pi * R *
          (ε + (2 * (B : ℝ≥0∞)) * (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ)).toReal +
        2 * Real.pi * R * (countingSquareNorm w).toReal := by
  have hPU (z : ℂ) (hz : (z : Sphere) ∈ G) : π (z : Sphere) ∈ U := by
    rw [← he ⟨z, hz⟩]
    exact (e ⟨z, hz⟩).property
  obtain ⟨Q, herr, hgrad⟩ := exists_smooth_mean_period_data hsch hsep hcoarea e hG hU hS hM
    (σ singular) hbS (hσ singular) hMS y₀ π hπ he hinf A hA η hfinite g hg hocc henergy
    K hK hKS F f hf hmap B hB h0 h1 hF hinj hmiss δ hδ hδ1 hε
  let N := ε + (2 * (B : ℝ≥0∞)) * (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ)
  have hN : N ≠ ∞ := by
    apply ENNReal.add_ne_top.mpr
    refine ⟨hεfin, ENNReal.mul_ne_top (by finiteness) ?_⟩
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) henergy.ne
  have hn (i : Fin 2) : eLpNorm
      (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
      2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))) ≤ N :=
    (hgrad i).2.trans (add_le_add le_rfl
      (sliceChartDensity_euclidean_eLpNorm_le B g hg henergy _))
  obtain ⟨C, hc, hm, hs, hh, hv, hb⟩ := Q.exists_coordinate_data_with_budget
    hsch hsep A K hK hKS η F f hf hmap hG hdense hS hM hboundary σ hσ singular
    (hσ singular) hMS hbS hπ hPU hfreeU h0 h1 hstrict hF (fun i => (hgrad i).1)
    hend hbudget hmissFree hR hN hn w hw hwp
  exact ⟨Q, C, herr, hc, hm, hs, hh, hv, hb⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SmallMeanCoordinateConstruction
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily small compact-law norms produce the actual masked
coordinate with a strictly small full Stokes budget. -/

open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r609189_14 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_smooth_mean_coordinate_with_small_budget_oai
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U S M : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hU : IsOpen U)
    (hdense : Dense U) (hS : IsOpen S) (hM : IsClosed M) (hboundary : frontier M ⊆ U)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U) (singular : T)
    (hbS : σ singular ∉ S) (hMS : M \ {σ singular} ⊆ S) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (hfreeU : π '' Gᶜ ⊆ Uᶜ) (hinf : π OnePoint.infty ∉ S)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' S)))
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hstrict : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (hmissFree : ∀ x ∈ ((π '' Gᶜ) \ range σ) ∩ S,
      ∀ᵐ γ : K ∂(η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure K), F x ∉ range γ.val)
    (hend : ∀ γ : A, σ singular ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2))
    (w : T → ℝ≥0∞) (hw : (∑' t, w t ^ 2) < ∞)
    (hwp : ∀ s, s ≠ singular → (η : Measure A) {γ | σ s ∈ range γ.val} ≤ w s)
    {R : ℝ} (hR : 0 ≤ R)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hsmall : (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) + countingSquareNorm w <
      meanBudgetTolerance B R ξ) :
    ∃ (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F G U S M (σ singular) π)
      (C : MaskedCoordinateData G U π σ),
      (∀ x, |Q.error x| ≤ dustSmoothingTolerance id Uᶜ δ x) ∧
      C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
      C.mask = M ∧ C.singular = singular ∧
      (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        C.physical (Complex.equivRealProdCLM z) = Q.physical z) ∧
      C.sourceStokesBudget R < ξ := by
  obtain ⟨Q, C, herr, hc, hm, hs, hh, hv, hb⟩ := exists_smooth_mean_coordinate_with_budget
    hsch hsep hcoarea e hG hU hdense hS hM hboundary σ hσ singular hbS hMS y₀ π hπ he
    hfreeU hinf A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap B hB h0 h1
    hstrict hF hinj hmiss hmissFree hend hbudget w hw hwp hR δ hδ hδ1
    (meanBudgetTolerance_pos B hR hξ) (meanBudgetTolerance_ne_top B R ξ)
  exact ⟨Q, C, herr, hc, hm, hs, hh, hv,
    hb.trans_lt (mean_budget_lt_of_small_norms B hR hξ hsmall)⟩

end CircleDomainRigidity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CircleDomainRigidity.exists_smooth_mean_coordinate_with_small_budget_oai.{u_1} := @OAI.CircleDomainRigidity.exists_smooth_mean_coordinate_with_small_budget_oai.{u_1}
