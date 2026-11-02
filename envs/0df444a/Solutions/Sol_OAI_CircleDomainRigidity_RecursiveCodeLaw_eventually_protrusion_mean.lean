-- Prove2me | solution 1 for OAI.CircleDomainRigidity.RecursiveCodeLaw.eventually_protrusion_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:59:36.044864+00:00
-- url     : https://prove2.me/submissions/10b45724-97a1-4cfb-8d72-2f93b1779e06

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010
import Theorems.Thm_OAI_CircleDomainRigidity_exists_smooth_mean_coordinate_with_small_budget

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_HausdorffPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Length payment by crossing a ball

The generic-level-continua proof in Section 1 of `047-02` uses radial
distance on a subcontinuum crossing a ball contained in the physical
domain. Its image contains the radius interval, so one-dimensional
Hausdorff measure pays at least the ball radius.
-/

open Set Metric MeasureTheory
open scoped ENNReal Topology

namespace CircleDomainRigidity

/-- Radial distance is one-Lipschitz and maps a connected set containing
two points onto an interval of length their distance. -/
theorem dist_le_hausdorffMeasure_one_of_preconnected
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {C : Set X} (hC : IsPreconnected C) {p q : X} (hp : p ∈ C) (hq : q ∈ C) :
    ENNReal.ofReal (dist q p) ≤ (μH[1] : Measure X) C := by
  have himage : IsPreconnected ((fun z => dist z p) '' C) :=
    hC.image _ (LipschitzWith.dist_left p).continuous.continuousOn
  have hinterval : Icc 0 (dist q p) ⊆ (fun z => dist z p) '' C :=
    himage.Icc_subset ⟨p, hp, dist_self p⟩ ⟨q, hq, rfl⟩
  calc
    ENNReal.ofReal (dist q p) = (μH[1] : Measure ℝ) (Icc 0 (dist q p)) := by
      rw [hausdorffMeasure_real, Real.volume_Icc]
      simp only [sub_zero]
    _ ≤ (μH[1] : Measure ℝ) ((fun z => dist z p) '' C) := measure_mono hinterval
    _ ≤ (μH[1] : Measure X) C := by
      simpa using (LipschitzWith.dist_left p).hausdorffMeasure_image_le
        (show (0 : ℝ) ≤ 1 by norm_num) C

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathLawMixtures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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

section Paths

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
theorem pathHitReal_nonneg (μ : ProbabilityMeasure C(PathTime, X)) (x : X) :
    0 ≤ pathHitReal μ x := ENNReal.toReal_nonneg

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
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathVariation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
-- module Solutions.Q146_CD.CircleDomains_Topology_PathGates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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

variable [SecondCountableTopology X] [Countable D]

omit [BorelSpace X] [SecondCountableTopology X] in
theorem measurable_baseCodeOccupation (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) :
    Measurable (baseCodeOccupation d) :=
  (measurable_dyadicPhysicalOccupation d.domainEquiv hU d.basePoint).comp
    ((measurable_fst.comp measurable_subtype_coe).subtype_mk)

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

omit [BorelSpace X] [SecondCountableTopology X] in
theorem meanCodeOccupation_apply (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) {A : Set Y} (hA : MeasurableSet A) :
    meanCodeOccupation d P A = ∫⁻ Γ, baseCodeOccupation d Γ A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_baseCodeOccupation d hU).aemeasurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableVisitNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ResidualTailNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ShrinkingHitEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-summable hit probabilities have small punctured-collar tails. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem eventually_outside_shrinking_set {S : Type*} (U : ℕ → Set S)
    (hanti : Antitone U) (p : S) (hinter : (⋂ n, U n) ⊆ {p}) :
    ∀ s ≠ p, ∀ᶠ n in atTop, s ∉ U n := by
  intro s hsp
  have hn : ∃ n, s ∉ U n := by
    by_contra! h
    exact hsp (hinter (mem_iInter.mpr h))
  obtain ⟨n, hn⟩ := hn
  exact eventually_atTop.2 ⟨n, fun k hk hsk => hn (hanti hk hsk)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_UncountableHitTail
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shrinking hit estimates on the whole dust set. Square summability
itself supplies the countable support; the dust is not assumed countable. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem tendsto_punctured_hit_energy_of_finite_tsum {S : Type*}
    (m : S → ℝ≥0∞) (hm : (∑' s, m s ^ 2) ≠ ∞) (p : S) (U : ℕ → Set S)
    (hshrink : ∀ s ≠ p, ∀ᶠ n in atTop, s ∉ U n) :
    Tendsto (fun n => ∑' s, if s ∈ U n ∧ s ≠ p then m s ^ 2 else 0) atTop (𝓝 0) := by
  let T := support (fun s => m s ^ 2)
  have hT : T.Countable := Summable.countable_support_ennreal hm
  let : Countable T := hT.to_subtype
  have hsum : (∑' t : T, m t.val ^ 2) ≠ ∞ := by
    simpa only [T, tsum_subtype_support] using hm
  have hcover (t : T) : ∀ᶠ n in atTop, t ∈ {t : T | t.val ∉ U n ∨ t.val = p} := by
    by_cases ht : t.val = p
    · exact Eventually.of_forall fun _ => Or.inr ht
    · exact (hshrink t.val ht).mono fun _ h => Or.inl h
  have ht := tendsto_deleted_series_zero (fun t : T => m t.val ^ 2) hsum
    (fun n => {t : T | t.val ∉ U n ∨ t.val = p}) hcover
  have he (n : ℕ) : (∑' t : T, if t.val ∉ U n ∨ t.val = p then 0 else m t.val ^ 2) =
      ∑' s, if s ∈ U n ∧ s ≠ p then m s ^ 2 else 0 := by
    have hc : (fun t : T => if t.val ∉ U n ∨ t.val = p then 0 else m t.val ^ 2) =
        fun t => if t.val ∈ U n ∧ t.val ≠ p then m t.val ^ 2 else 0 := by
      funext t
      by_cases hu : t.val ∈ U n <;> by_cases hp : t.val = p <;> simp [hu, hp]
    rw [hc]
    apply tsum_subtype_eq_of_support_subset
      (f := fun s : S => if s ∈ U n ∧ s ≠ p then m s ^ 2 else 0) (s := T)
    intro s hs
    by_contra hn
    have hz : m s ^ 2 = 0 := notMem_support.mp hn
    simp only [mem_support, ne_eq] at hs
    split_ifs at hs <;> simp_all
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [← he n]
  apply tsum_congr
  intro t
  by_cases hu : t.val ∈ U n <;> by_cases hp : t.val = p <;> simp [hu, hp]

theorem tendsto_punctured_hit_norm_of_finite_tsum {S : Type*}
    (m : S → ℝ≥0∞) (hm : (∑' s, m s ^ 2) ≠ ∞) (p : S) (U : ℕ → Set S)
    (hshrink : ∀ s ≠ p, ∀ᶠ n in atTop, s ∉ U n) :
    Tendsto (fun n => countingSquareNorm
      (fun s => if s ∈ U n ∧ s ≠ p then m s else 0)) atTop (𝓝 0) := by
  have ht := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp
    (tendsto_punctured_hit_energy_of_finite_tsum m hm p U hshrink)
  have he (n : ℕ) : (∑' s, if s ∈ U n ∧ s ≠ p then m s ^ 2 else 0) =
      ∑' s, (if s ∈ U n ∧ s ≠ p then m s else 0) ^ 2 := by
    apply tsum_congr
    intro s
    split_ifs <;> simp
  simpa only [he, countingSquareNorm, Function.comp_def,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SimpleArcLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variation of an injective arc is paid by the Hausdorff length of
its image. Disjoint parameter intervals have disjoint half-open images. -/

open Set Function MeasureTheory Metric
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_edist_le_length_Ioc
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : PathTime → X) {s : Set PathTime} (hs : OrdConnected s)
    (hf : ContinuousOn f s) {a b : PathTime} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≤ b) : edist (f b) (f a) ≤ (μH[1] : Measure X) (f '' Ioc a b) := by
  let : NullSingletonClass (μH[1] : Measure X) :=
    Measure.nullSingletonClass_hausdorff X (by norm_num)
  have hsub : Icc a b ⊆ s := hs.out ha hb
  have hc : IsPreconnected (f '' Icc a b) :=
    isPreconnected_Icc.image f (hf.mono hsub)
  have hd := dist_le_hausdorffMeasure_one_of_preconnected hc
    (mem_image_of_mem f (left_mem_Icc.mpr hab))
    (mem_image_of_mem f (right_mem_Icc.mpr hab))
  rw [edist_dist]
  apply hd.trans
  have hi : f '' Icc a b ⊆ insert (f a) (f '' Ioc a b) := by
    rintro _ ⟨t, ht, rfl⟩
    rcases ht.1.eq_or_lt with h | h
    · exact Or.inl (congrArg f h.symm)
    · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
  calc
    _ ≤ (μH[1] : Measure X) (insert (f a) (f '' Ioc a b)) := measure_mono hi
    _ ≤ (μH[1] : Measure X) {f a} + (μH[1] : Measure X) (f '' Ioc a b) :=
      measure_union_le _ _
    _ = _ := by rw [measure_singleton, zero_add]

theorem simple_arc_variation_le_length
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : PathTime → X) {s : Set PathTime} (hs : OrdConnected s)
    (hf : ContinuousOn f s) (hinj : InjOn f s) :
    eVariationOn f s ≤ (μH[1] : Measure X) (f '' s) := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  let A : ℕ → Set X := fun i => f '' Ioc (u i) (u (i + 1))
  have hA (i : ℕ) : MeasurableSet (A i) := by
    have hsub : Icc (u i) (u (i + 1)) ⊆ s := hs.out (hus i) (hus (i + 1))
    have hcompact : IsCompact (f '' Icc (u i) (u (i + 1))) :=
      isCompact_Icc.image_of_continuousOn (hf.mono hsub)
    have he : A i = f '' Icc (u i) (u (i + 1)) \ {f (u i)} := by
      ext x
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨⟨t, Ioc_subset_Icc_self ht, rfl⟩, ?_⟩
        intro heq
        exact ht.1.ne' (hinj (hsub (Ioc_subset_Icc_self ht)) (hus i) heq)
      · rintro ⟨⟨t, ht, rfl⟩, hne⟩
        refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, ht.2⟩, rfl⟩
        intro heq
        exact hne (congrArg f heq.symm)
    rw [he]
    exact hcompact.isClosed.measurableSet.diff (measurableSet_singleton _)
  have hdis : Pairwise (Disjoint on A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ ⟨v, hv, heq⟩
    have hts : t ∈ s := hs.out (hus i) (hus (i + 1)) (Ioc_subset_Icc_self ht)
    have hvs : v ∈ s := hs.out (hus j) (hus (j + 1)) (Ioc_subset_Icc_self hv)
    have htv : t = v := hinj hts hvs heq.symm
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact (not_lt_of_ge (ht.2.trans (hu (Nat.succ_le_of_lt hij)))) (htv ▸ hv.1)
    · exact (not_lt_of_ge (hv.2.trans (hu (Nat.succ_le_of_lt hji)))) (htv.symm ▸ ht.1)
  calc
    _ ≤ ∑ i ∈ Finset.range n, (μH[1] : Measure X) (A i) := by
      apply Finset.sum_le_sum
      intro i _
      exact simple_arc_edist_le_length_Ioc f hs hf (hus i) (hus (i + 1))
        (hu (Nat.le_succ i))
    _ = (μH[1] : Measure X) (⋃ i ∈ Finset.range n, A i) := by
      rw [measure_biUnion_finset (fun i _ j _ hij => hdis hij) (fun i _ => hA i)]
    _ ≤ (μH[1] : Measure X) (f '' s) := by
      apply measure_mono
      intro x hx
      obtain ⟨i, _, t, ht, rfl⟩ := mem_iUnion₂.mp hx
      exact ⟨t, hs.out (hus i) (hus (i + 1)) (Ioc_subset_Icc_self ht), rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathHausdorffLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
-- module Solutions.Q146_CD.CircleDomains_Probability_SimpleArcOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arclength occupation of an injective continuous path. This
identifies weighted path cost with the Hausdorff integral on its image. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem arc_variation_eq_hausdorff_interval
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : C(PathTime, X)) {a b : PathTime} (hab : a ≤ b)
    (hinj : InjOn γ (Icc a b)) :
    eVariationOn γ (Icc a b) = (μH[1] : Measure X) (γ '' Icc a b) := by
  apply le_antisymm
  · exact simple_arc_variation_le_length γ ordConnected_Icc γ.continuous.continuousOn hinj
  · have h := path_hausdorff_length_le_variation (γ.comp (timeClip a b))
    rw [variation_timeClip γ hab] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    rw [ContinuousMap.coe_comp, range_comp, range_timeClip hab]

theorem simple_arc_length_measure
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) (hinj : Injective γ.val) :
    pathLengthMeasure γ = (μH[1] : Measure X).comap γ.val := by
  have he : MeasurableEmbedding γ.val := γ.val.continuous.isClosedEmbedding hinj |>.measurableEmbedding
  apply Measure.ext_of_Icc
  intro a b hab
  rw [pathLengthMeasure_Icc γ hab, he.comap_apply]
  exact arc_variation_eq_hausdorff_interval γ.val hab hinj.injOn

theorem simple_arc_occupation
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) (hinj : Injective γ.val) :
    pathOccupation γ = (μH[1] : Measure X).restrict (range γ.val) := by
  have he : MeasurableEmbedding γ.val := γ.val.continuous.isClosedEmbedding hinj |>.measurableEmbedding
  rw [pathOccupation, simple_arc_length_measure γ hinj]
  exact he.map_comap _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DisjointArcLengths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint compact portions of a simple arc have a total length bounded
by the Hausdorff length of the whole arc, even when the map is only
continuous on an open part of its parameter domain. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_Ioc_image_measurable
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {V : Set PathTime} (f : PathTime → X) (hf : ContinuousOn f V) (hinj : InjOn f V)
    {a b : PathTime} (hab : a ≤ b) (hsub : Icc a b ⊆ V) :
    MeasurableSet (f '' Ioc a b) := by
  have hcompact : IsCompact (f '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn (hf.mono hsub)
  have he : f '' Ioc a b = f '' Icc a b \ {f a} := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, Ioc_subset_Icc_self ht, rfl⟩, ?_⟩
      intro heq
      exact ht.1.ne' (hinj (hsub (Ioc_subset_Icc_self ht))
        (hsub (left_mem_Icc.mpr hab)) heq)
    · rintro ⟨⟨t, ht, rfl⟩, hne⟩
      refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, ht.2⟩, rfl⟩
      intro heq
      exact hne (congrArg f heq.symm)
  rw [he]
  exact hcompact.isClosed.measurableSet.diff (measurableSet_singleton _)

theorem simple_arc_variation_le_Ioc_image
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {V : Set PathTime} (f : PathTime → X) (hf : ContinuousOn f V) (hinj : InjOn f V)
    {a b : PathTime} (_hab : a ≤ b) (hsub : Icc a b ⊆ V) :
    eVariationOn f (Icc a b) ≤ (μH[1] : Measure X) (f '' Ioc a b) := by
  let : NullSingletonClass (μH[1] : Measure X) :=
    Measure.nullSingletonClass_hausdorff X (by norm_num)
  have hi : f '' Icc a b ⊆ {f a} ∪ (f '' Ioc a b) := by
    rintro _ ⟨t, ht, rfl⟩
    rcases ht.1.eq_or_lt with h | h
    · exact Or.inl (congrArg f h.symm)
    · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
  calc
    _ ≤ (μH[1] : Measure X) (f '' Icc a b) :=
      simple_arc_variation_le_length f ordConnected_Icc (hf.mono hsub) (hinj.mono hsub)
    _ ≤ (μH[1] : Measure X) ({f a} ∪ (f '' Ioc a b)) := measure_mono hi
    _ ≤ (μH[1] : Measure X) {f a} + (μH[1] : Measure X) (f '' Ioc a b) := measure_union_le _ _
    _ = _ := by rw [measure_singleton, zero_add]

theorem sum_disjoint_arc_variations_le {ι X : Type*} [Fintype ι]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {V : Set PathTime} (f : PathTime → X) (hf : ContinuousOn f V) (hinj : InjOn f V)
    (a b : ι → PathTime) (hab : ∀ i, a i ≤ b i)
    (hsub : ∀ i, Icc (a i) (b i) ⊆ V)
    (hdis : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    (∑ i, eVariationOn f (Icc (a i) (b i))) ≤ (μH[1] : Measure X) (f '' V) := by
  have himdis : Pairwise (fun i j => Disjoint
      (f '' Ioc (a i) (b i)) (f '' Ioc (a j) (b j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ ⟨s, hs, heq⟩
    have hts := hinj (hsub i (Ioc_subset_Icc_self ht)) (hsub j (Ioc_subset_Icc_self hs)) heq.symm
    exact Set.disjoint_left.mp (hdis hij) ht (hts.symm ▸ hs)
  calc
    _ ≤ ∑ i, (μH[1] : Measure X) (f '' Ioc (a i) (b i)) :=
      Finset.sum_le_sum (fun i _ => simple_arc_variation_le_Ioc_image f hf hinj (hab i) (hsub i))
    _ = (μH[1] : Measure X) (⋃ i, f '' Ioc (a i) (b i)) := by
      rw [measure_iUnion himdis (fun i => simple_arc_Ioc_image_measurable f hf hinj (hab i) (hsub i)),
        tsum_fintype]
    _ ≤ _ := measure_mono (iUnion_subset fun i => image_mono (Ioc_subset_Icc_self.trans (hsub i)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PartialSimpleArcLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite physical length of a simple quotient arc follows from the
Hausdorff length of its physical part. No boundary extension of its
physical lift is required. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

theorem partial_simple_arc_dyadic_sum_le
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {V : Set PathTime} (f : PathTime → Y) (hf : ContinuousOn f V) (hinj : InjOn f V)
    (n : ℕ) :
    (∑ i : Fin (2 ^ n), if Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V then
      eVariationOn f (Icc (dyadicLeft n i) (dyadicRight n i)) else 0) ≤
      (μH[1] : Measure Y) (f '' V) := by
  let J := {i : Fin (2 ^ n) | Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V}
  have hdis : Pairwise (fun i j : J => Disjoint
      (Ioc (dyadicLeft n i.val) (dyadicRight n i.val))
      (Ioc (dyadicLeft n j.val) (dyadicRight n j.val))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro t ht hs
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have hsep : dyadicRight n i.val ≤ dyadicLeft n j.val :=
        dyadicReal_mono n (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (ht.2.trans hsep)) hs.1
    · have hsep : dyadicRight n j.val ≤ dyadicLeft n i.val :=
        dyadicReal_mono n (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (hs.2.trans hsep)) ht.1
  have h := sum_disjoint_arc_variations_le f hf hinj
    (fun i : J => dyadicLeft n i.val) (fun i : J => dyadicRight n i.val)
    (fun i => dyadicLeft_le_right n i.val) (fun i => i.property) hdis
  have he : (∑ i : J, eVariationOn f (Icc (dyadicLeft n i.val) (dyadicRight n i.val))) =
      ∑ i : Fin (2 ^ n), if Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V then
        eVariationOn f (Icc (dyadicLeft n i) (dyadicRight n i)) else 0 := by
    simpa only [tsum_fintype, J, Set.indicator_apply, Set.mem_ofPred_eq] using
      tsum_subtype J (fun i => eVariationOn f (Icc (dyadicLeft n i) (dyadicRight n i)))
  rwa [he] at h

theorem physicalValue_path_continuousOn
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) :
    ContinuousOn (physicalValue e y₀ ∘ γ) (γ ⁻¹' U) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h : Continuous (fun t : γ ⁻¹' U => (e.symm ⟨γ t.val, t.property⟩).val) :=
    continuous_subtype_val.comp (e.symm.continuous.comp
      ((γ.continuous.comp continuous_subtype_val).subtype_mk _))
  apply h.congr
  intro t
  change (e.symm ⟨γ t.val, t.property⟩).val = physicalValue e y₀ (γ t.val)
  rw [physicalValue, dite_eq_left (show γ t.val ∈ U from t.property)]

theorem physicalValue_path_injOn
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) (hγ : Injective γ) :
    InjOn (physicalValue e y₀ ∘ γ) (γ ⁻¹' U) := by
  intro s hs t ht heq
  change γ s ∈ U at hs
  change γ t ∈ U at ht
  apply hγ
  simp only [Function.comp_apply, physicalValue, dite_eq_left hs, dite_eq_left ht] at heq
  have hsub : e.symm ⟨γ s, hs⟩ = e.symm ⟨γ t, ht⟩ := Subtype.ext heq
  exact congrArg Subtype.val (e.symm.injective hsub)

theorem physicalSubpath_variation_eq_value
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) {a b : PathTime}
    (hab : a ≤ b) (hγ : γ ∈ pathsInsideOn U a b) :
    eVariationOn (physicalSubpath e hab ⟨γ, hγ⟩) univ =
      eVariationOn (physicalValue e y₀ ∘ γ) (Icc a b) := by
  have he : (physicalSubpath e hab ⟨γ, hγ⟩ : PathTime → Y) =
      (physicalValue e y₀ ∘ γ) ∘ timeClip a b := by
    funext t
    have ht : timeClip a b t ∈ Icc a b := by
      rw [← range_timeClip hab]
      exact mem_range_self t
    simp only [Function.comp_apply, physicalSubpath, ContinuousMap.coe_mk,
      physicalValue, dite_eq_left (hγ ht)]
  rw [he, eVariationOn.comp_eq_of_monotoneOn _ _
    ((monotone_timeClip a b).monotoneOn univ), image_univ, range_timeClip hab]

theorem simple_quotient_arc_physical_length_le
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) (hγ : Injective γ) :
    physicalDomainLength e y₀ γ ≤
      (μH[1] : Measure Y) ((physicalValue e y₀ ∘ γ) '' (γ ⁻¹' U)) := by
  apply iSup_le
  intro n
  have he : physicalStageLength e y₀ n γ =
      ∑ i : Fin (2 ^ n), if Icc (dyadicLeft n i) (dyadicRight n i) ⊆ γ ⁻¹' U then
        eVariationOn (physicalValue e y₀ ∘ γ) (Icc (dyadicLeft n i) (dyadicRight n i)) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
    · have hi' : Icc (dyadicLeft n i) (dyadicRight n i) ⊆ γ ⁻¹' U := hi
      rw [physicalDyadicLength, physicalDyadicPath_of_mem e y₀ n i γ hi,
        physicalSubpath_variation_eq_value e y₀ γ _ hi, ite_eq_left hi']
    · have hi' : ¬ Icc (dyadicLeft n i) (dyadicRight n i) ⊆ γ ⁻¹' U := hi
      simp only [physicalDyadicLength, physicalDyadicPath, totalPhysicalSubpath,
        dite_eq_right hi, ite_eq_right hi']
      exact (eVariationOn.eq_zero_iff _).mpr (fun _ _ _ _ => edist_self _)
  rw [he]
  exact partial_simple_arc_dyadic_sum_le _ (physicalValue_path_continuousOn e y₀ γ)
    (physicalValue_path_injOn e y₀ γ hγ) n

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
-- module Solutions.Q146_CD.CircleDomains_Probability_ArcImageMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint portions of a simple arc have disjoint image measures after
their shared endpoints, which have zero Hausdorff length, are removed. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem arc_image_Icc_ae_eq_Ioc {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NullSingletonClass μ] (f : PathTime → X) (a b : PathTime) :
    f '' Icc a b =ᵐ[μ] f '' Ioc a b := by
  filter_upwards [μ.ae_ne (f a)] with x hx
  apply propext
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, ht.2⟩, rfl⟩
    intro heq
    exact hx (congrArg f heq.symm)
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Ioc_subset_Icc_self ht, rfl⟩

theorem sum_disjoint_arc_image_measures_le {ι X : Type*} [Fintype ι]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [NullSingletonClass μ]
    {V : Set PathTime} (f : PathTime → X) (hf : ContinuousOn f V) (hinj : InjOn f V)
    (a b : ι → PathTime) (hab : ∀ i, a i ≤ b i)
    (hsub : ∀ i, Icc (a i) (b i) ⊆ V)
    (hdis : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    (∑ i, μ.restrict (f '' Icc (a i) (b i))) ≤ μ.restrict (f '' V) := by
  have himdis : Pairwise (fun i j => Disjoint
      (f '' Ioc (a i) (b i)) (f '' Ioc (a j) (b j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ ⟨s, hs, heq⟩
    have hts := hinj (hsub i (Ioc_subset_Icc_self ht)) (hsub j (Ioc_subset_Icc_self hs)) heq.symm
    exact Set.disjoint_left.mp (hdis hij) ht (hts.symm ▸ hs)
  calc
    _ = ∑ i, μ.restrict (f '' Ioc (a i) (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Measure.restrict_congr_set (arc_image_Icc_ae_eq_Ioc μ f (a i) (b i))
    _ = μ.restrict (⋃ i, f '' Ioc (a i) (b i)) := by
      rw [Measure.restrict_iUnion himdis
        (fun i => simple_arc_Ioc_image_measurable f hf hinj (hab i) (hsub i)),
        Measure.sum_fintype]
    _ ≤ _ := Measure.restrict_mono
      (iUnion_subset fun i => image_mono (Ioc_subset_Icc_self.trans (hsub i))) le_rfl

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
-- module Solutions.Q146_CD.CircleDomains_Topology_RectifiableSubarcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual short rectifiable arcs between nearby parameters of a
finite-cost curve, with either orientation. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem pathOccupation_affine (γ : RectifiablePath X) {a b : PathTime} (hab : a < b) :
    pathOccupation (affineRectifiablePath γ hab) =
      ((pathLengthMeasure γ).restrict (Icc a b)).map γ.val := by
  rw [pathOccupation, pathLengthMeasure_affine]
  change (((pathLengthMeasure γ).restrict (Icc a b)).map (rescalePathTime a b)).map
    (affineRestrictedPath a b γ.val) = _
  rw [Measure.map_map (affineRestrictedPath a b γ.val).continuous.measurable
    (rescalePathTime a b).continuous.measurable]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change γ.val (affinePathTime a b (rescalePathTime a b t)) = γ.val t
  rw [affine_rescalePathTime hab ht]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ClippedArcOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A path that is injective only on a retained parameter interval has
exact Hausdorff occupation on that portion. Constant tails add no mass. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_portion_occupation
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) {a b : PathTime} (hab : a < b)
    (hinj : InjOn γ.val (Icc a b)) :
    pathPortionOccupation γ a b = (μH[1] : Measure X).restrict (γ.val '' Icc a b) := by
  let β := affineRectifiablePath γ hab
  have hβ : Injective β.val := by
    intro s t h
    exact (affinePathTime_strictMono hab).injective
      (hinj (affinePathTime_mem_Icc hab.le s) (affinePathTime_mem_Icc hab.le t) h)
  have hrange : range β.val = γ.val '' Icc a b := by
    change range (γ.val ∘ affinePathTime a b) = _
    rw [range_comp, range_affinePathTime hab]
  change ((pathLengthMeasure γ).restrict (Icc a b)).map γ.val = _
  rw [← pathOccupation_affine γ hab, simple_arc_occupation β hβ, hrange]

theorem clipped_simple_arc_occupation
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) {a b : PathTime} (hab : a < b)
    (hinj : InjOn γ.val (Icc a b)) :
    pathOccupation (clippedPath γ hab.le) =
      (μH[1] : Measure X).restrict (γ.val '' Icc a b) := by
  rw [pathOccupation_clipped γ hab.le, simple_arc_portion_occupation γ hab hinj]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PhysicalSimpleArcPortion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact domain portion of an injective quotient path has exactly
the Hausdorff occupation of its physical lift. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem physical_simple_arc_portion_occupation
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (hinj : Injective γ.val) {a b : PathTime} (hab : a < b)
    (hγ : γ.val ∈ pathsInsideOn U a b) :
    rectifiableOccupationCode (physicalSubpath e hab.le ⟨γ.val, hγ⟩) =
      (μH[1] : Measure Y).restrict ((physicalValue e y₀ ∘ γ.val) '' Icc a b) := by
  let β : RectifiablePath Y := ⟨physicalSubpath e hab.le ⟨γ.val, hγ⟩,
    physicalSubpath_rectifiable e hU hab.le γ.val hγ y₀ γ.property⟩
  have hβ : InjOn β.val (Icc a b) := by
    intro s hs t ht heq
    apply physicalValue_path_injOn e y₀ γ.val hinj (hγ hs) (hγ ht)
    exact (physicalValue_subpath e y₀ hab.le ⟨γ.val, hγ⟩ hs).trans
      (heq.trans (physicalValue_subpath e y₀ hab.le ⟨γ.val, hγ⟩ ht).symm)
  have hclip : clippedPath β hab.le = β := by
    apply Subtype.ext
    exact physicalSubpath_comp_clip e hab.le ⟨γ.val, hγ⟩
  have himage : β.val '' Icc a b = (physicalValue e y₀ ∘ γ.val) '' Icc a b := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, physicalValue_subpath e y₀ hab.le ⟨γ.val, hγ⟩ ht⟩
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, (physicalValue_subpath e y₀ hab.le ⟨γ.val, hγ⟩ ht).symm⟩
  rw [rectifiableOccupationCode_eq β.property]
  change pathOccupation β = _
  rw [← hclip, clipped_simple_arc_occupation β hab hβ, himage]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SimplePhysicalArcOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical occupation of a simple quotient arc is bounded by Hausdorff
length on its physical image. This retains arbitrary measurable densities. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_physical_stage_occupation_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (hinj : Injective γ.val) (n : ℕ) :
    physicalStageOccupation e y₀ n γ.val ≤ (μH[1] : Measure Y).restrict
      ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U)) := by
  let f := physicalValue e y₀ ∘ γ.val
  let J := {i : Fin (2 ^ n) | Icc (dyadicLeft n i) (dyadicRight n i) ⊆ γ.val ⁻¹' U}
  let : NullSingletonClass (μH[1] : Measure Y) :=
    Measure.nullSingletonClass_hausdorff Y (by norm_num)
  have hdis : Pairwise (fun i j : J => Disjoint
      (Ioc (dyadicLeft n i.val) (dyadicRight n i.val))
      (Ioc (dyadicLeft n j.val) (dyadicRight n j.val))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro t ht hs
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have hsep : dyadicRight n i.val ≤ dyadicLeft n j.val :=
        dyadicReal_mono n (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (ht.2.trans hsep)) hs.1
    · have hsep : dyadicRight n j.val ≤ dyadicLeft n i.val :=
        dyadicReal_mono n (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (hs.2.trans hsep)) ht.1
  have he : physicalStageOccupation e y₀ n γ.val =
      ∑ i : J, (μH[1] : Measure Y).restrict
        (f '' Icc (dyadicLeft n i.val) (dyadicRight n i.val)) := by
    apply Finset.sum_congr_set J
    · intro i hi
      rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi]
      apply physical_simple_arc_portion_occupation e hU y₀ γ hinj _ hi
      change (i.val : ℝ) / (2 : ℝ) ^ n < ((i.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n
      exact div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self i.val) (by positivity)
    · intro i hi
      have hi' : γ.val ∉ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i) := hi
      simp only [physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hi',
        rectifiableOccupationCode_const]
  rw [he]
  exact sum_disjoint_arc_image_measures_le (μH[1] : Measure Y) f
    (physicalValue_path_continuousOn e y₀ γ.val) (physicalValue_path_injOn e y₀ γ.val hinj)
    (fun i : J => dyadicLeft n i.val) (fun i : J => dyadicRight n i.val)
    (fun i => dyadicLeft_le_right n i.val) (fun i => i.property) hdis

theorem simple_arc_physical_occupation_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (hinj : Injective γ.val) :
    dyadicPhysicalOccupation e y₀ γ ≤ (μH[1] : Measure Y).restrict
      ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U)) := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [dyadicPhysicalOccupation_apply e y₀ γ hS]
  exact iSup_le fun n => Measure.le_iff.mp
    (simple_arc_physical_stage_occupation_le e hU y₀ γ hinj n) S hS

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

theorem simple_subarc_physical_length_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) (α : C(PathTime, X))
    (hinj : Injective α) (hsub : range α ⊆ range γ.val) :
    physicalDomainLength e y₀ α ≤ physicalDomainLength e y₀ γ.val := by
  apply (simple_quotient_arc_physical_length_le e y₀ α hinj).trans
  have hs : (physicalValue e y₀ ∘ α) '' (α ⁻¹' U) ⊆
      (physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U) := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨s, hs⟩ := hsub (mem_range_self t)
    exact ⟨s, by simpa only [mem_preimage, hs] using ht, by simp only [comp_apply, hs]⟩
  calc
    (μH[1] : Measure Y) ((physicalValue e y₀ ∘ α) '' (α ⁻¹' U)) ≤
      (μH[1] : Measure Y) ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U)) := measure_mono hs
    _ = ((μH[1] : Measure Y).restrict
      ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U))) univ := (Measure.restrict_apply_univ _).symm
    _ ≤ dyadicPhysicalOccupation e y₀ γ univ := physical_image_hausdorff_le_occupation e hU y₀ γ univ
    _ = _ := dyadicPhysicalOccupation_univ e y₀ γ

theorem simple_subarc_physical_occupation_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ α : FinitePhysicalPath e y₀)
    (hinj : Injective α.val) (hsub : range α.val ⊆ range γ.val) :
    dyadicPhysicalOccupation e y₀ α ≤ dyadicPhysicalOccupation e y₀ γ := by
  apply (simple_arc_physical_occupation_le e hU y₀ α hinj).trans
  apply le_trans (Measure.restrict_mono_set _ ?_) (physical_image_hausdorff_le_occupation e hU y₀ γ)
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨s, hs⟩ := hsub (mem_range_self t)
  exact ⟨s, by simpa only [mem_preimage, hs] using ht, by simp only [comp_apply, hs]⟩

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

lemma meanPhysicalOccupation_mono (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ ν : ProbabilityMeasure C(PathTime, X)) (c : ℝ≥0∞)
    (h : (μ : Measure C(PathTime, X)) ≤ c • (ν : Measure C(PathTime, X))) :
    meanPhysicalOccupation e y₀ μ ≤ c • meanPhysicalOccupation e y₀ ν := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [meanPhysicalOccupation_apply e hU y₀ μ hS, Measure.smul_apply,
    meanPhysicalOccupation_apply e hU y₀ ν hS, smul_eq_mul]
  simpa only [lintegral_smul_measure, smul_eq_mul] using
    (lintegral_mono' h (le_refl (fun γ => physicalOccupationCode e y₀ γ S)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawPhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Forgetting tags preserves the actual mean physical occupation. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r5b9296_1 : BorelSpace Sphere := ⟨rfl⟩
theorem meanPhysicalOccupation_codePathLaw (d : PathCodeData Sphere Sphere)
    (hU : IsOpen d.quotientDomain) (P : ProbabilityMeasure (BasePathCode d)) :
    meanPhysicalOccupation d.domainEquiv d.basePoint (codePathLaw d P) =
      meanCodeOccupation d P := by
  apply Measure.ext
  intro S hS
  have hm : Measurable (fun γ => physicalOccupationCode d.domainEquiv d.basePoint γ S) :=
    (Measure.measurable_coe hS).comp (measurable_physicalOccupationCode d.domainEquiv hU d.basePoint)
  rw [meanPhysicalOccupation_apply _ hU _ _ hS, meanCodeOccupation_apply d hU P hS,
    codePathLaw, ProbabilityMeasure.toMeasure_map, lintegral_map hm (measurable_codePath d)]
  apply lintegral_congr
  intro Γ
  exact congrArg (fun ν : Measure Sphere => ν S)
    (physicalOccupationCode_eq d.domainEquiv d.basePoint (baseCodePhysicalPath d Γ))

theorem codePathLaw_collar_endpoints (d : PathCodeData Sphere Sphere)
    (hU : IsOpen d.quotientDomain) (P : ProbabilityMeasure (BasePathCode d))
    (V : Set Sphere) (hV : IsOpen V) (hanchor : Disjoint d.anchor V) (hb : d.target ∈ V) :
    ∀ᵐ γ : C(PathTime, Sphere) ∂(codePathLaw d P : Measure C(PathTime, Sphere)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V ∧ γ ⊤ = d.target ∧ physicalDomainLength d.domainEquiv d.basePoint γ < ∞ := by
  change ∀ᵐ γ ∂(P : Measure (BasePathCode d)).map (codePath d), _
  apply (ae_map_iff (measurable_codePath d).aemeasurable ?_).mpr
  · exact Eventually.of_forall fun Γ =>
      ⟨fun hv => disjoint_left.mp hanchor Γ.property.2.1.1 hv,
       by change Γ.val.1 ⊤ ∈ V; rw [Γ.property.2.1.2.1]; exact hb,
       Γ.property.2.1.2.1, Γ.property.1.1⟩
  · exact (((continuous_eval_const ⊥).measurable hV.measurableSet).compl).inter
      (((continuous_eval_const ⊤).measurable hV.measurableSet).inter
        ((measurableSet_eq_fun (continuous_eval_const ⊤).measurable measurable_const).inter
          (measurableSet_finitePhysicalDomainLength d.domainEquiv hU d.basePoint)))

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
-- module Solutions.Q146_CD.CircleDomains_Probability_SimpleArcMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel simple-path and image-containment relations for the measurable
terminal-arc selection used in the stream construction. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem isClosed_pathsWithSeparatedCollision (r : ℝ) :
    IsClosed (pathsWithSeparatedCollision (X := X) r) := by
  let K : Set (C(PathTime, X) × (PathTime × PathTime)) :=
    {p | r ≤ dist p.2.1 p.2.2 ∧ p.1 p.2.1 = p.1 p.2.2}
  have hK : IsClosed K :=
    (isClosed_le continuous_const
      ((continuous_fst.comp continuous_snd).dist (continuous_snd.comp continuous_snd))).inter
      (isClosed_eq
        (continuous_eval.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
        (continuous_eval.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
  have he : Prod.fst '' K = pathsWithSeparatedCollision (X := X) r := by
    ext γ
    constructor
    · rintro ⟨⟨δ, s, t⟩, h, rfl⟩
      exact ⟨s, t, h⟩
    · rintro ⟨s, t, h⟩
      exact ⟨(γ, s, t), h, rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace K hK

theorem injective_path_iff_no_separated_collision (γ : C(PathTime, X)) :
    Injective γ ↔ ∀ n : ℕ, γ ∉ pathsWithSeparatedCollision (1 / ((n : ℝ) + 1)) := by
  constructor
  · intro h n ⟨s, t, hst, he⟩
    rw [h he, dist_self] at hst
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact hp.not_ge hst
  · intro h s t he
    by_contra hn
    have hd : 0 < dist s t := dist_pos.mpr hn
    obtain ⟨n, hn⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds hd)).exists
    exact h n ⟨s, t, hn.le, he⟩

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_injective_paths : MeasurableSet {γ : C(PathTime, X) | Injective γ} := by
  have he : {γ : C(PathTime, X) | Injective γ} =
      ⋂ n : ℕ, (pathsWithSeparatedCollision (1 / ((n : ℝ) + 1)))ᶜ := by
    ext γ
    simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff,
      injective_path_iff_no_separated_collision]
  rw [he]
  exact MeasurableSet.iInter fun n => (isClosed_pathsWithSeparatedCollision _).measurableSet.compl

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem isClosed_path_image_containment :
    IsClosed {p : C(PathTime, X) × C(PathTime, X) | range p.2 ⊆ range p.1} := by
  have he : {p : C(PathTime, X) × C(PathTime, X) | range p.2 ⊆ range p.1} =
      ⋂ t : PathTime, {p | (p.1, p.2 t) ∈ pathHitSet} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, range_subset_iff, pathHitSet, mem_range]
  rw [he]
  exact isClosed_iInter fun t => isClosed_pathHitSet.preimage
    (continuous_fst.prodMk ((continuous_eval_const t).comp continuous_snd))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TerminalPathMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable reparametrization of the path after its last collar hit. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem continuous_terminalPath :
    Continuous (fun p : C(PathTime, X) × PathTime => terminalPath p.1 p.2) := by
  have ht : Continuous (fun p : PathTime × PathTime => affinePathTime p.1 ⊤ p.2) := by
    apply Continuous.subtype_mk
    change Continuous (fun p : PathTime × PathTime =>
      (1 - (p.2 : ℝ)) * (p.1 : ℝ) + (p.2 : ℝ) * 1)
    fun_prop
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
    (ht.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_lastEntryPath (V : Set X) (hV : IsOpen V) :
    Measurable (fun γ : C(PathTime, X) => terminalPath γ (lastEntryTime γ V)) :=
  continuous_terminalPath.measurable.comp (measurable_id.prodMk (measurable_lastEntryTime V hV))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SimpleSubarcRelation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Borel relation used to select simple subarcs, including
the endpoint equalities and containment in the original path image. -/

open Set Function MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

variable [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_simpleSubarcRelation :
    MeasurableSet (simpleSubarcRelation (X := X)) := by
  have hs : IsClosed {p : C(PathTime, X) × C(PathTime, X) | p.2 ⊥ = p.1 ⊥} :=
    isClosed_eq ((continuous_eval_const ⊥).comp continuous_snd)
      ((continuous_eval_const ⊥).comp continuous_fst)
  have ht : IsClosed {p : C(PathTime, X) × C(PathTime, X) | p.2 ⊤ = p.1 ⊤} :=
    isClosed_eq ((continuous_eval_const ⊤).comp continuous_snd)
      ((continuous_eval_const ⊤).comp continuous_fst)
  exact (measurableSet_injective_paths.preimage measurable_snd).inter
    (hs.measurableSet.inter (ht.measurableSet.inter isClosed_path_image_containment.measurableSet))

end CircleDomainRigidity

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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathImageSimpleArc
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Loop erasure for a continuous sphere path. Its compact image is a
locally connected quotient of the interval, so the published simple-arc
input is applied only to the connected open set `univ` in that image. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem locallyConnected_pathTime : LocallyConnectedSpace PathTime := by
  apply locallyConnectedSpace_iff_connected_subsets.mpr
  intro x U hU
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball x r, Metric.ball_mem_nhds x hr, ?_, hsub⟩
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  have he : Subtype.val '' Metric.ball x r =
      Icc (0 : ℝ) 1 ∩ Metric.ball x.val r := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hy, hd⟩
      exact ⟨⟨y, hy⟩, hd, rfl⟩
  rw [he]
  exact (convex_Icc (0 : ℝ) 1 |>.inter (convex_ball x.val r)).isPreconnected

theorem exists_simple_subarc
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (γ : C(PathTime, Sphere)) (hne : γ ⊥ ≠ γ ⊤) :
    ∃ α : C(PathTime, Sphere), Injective α ∧ α ⊥ = γ ⊥ ∧ α ⊤ = γ ⊤ ∧
      range α ⊆ range γ := by
  let f : PathTime → range γ := fun t => ⟨γ t, mem_range_self t⟩
  have hf : Continuous f := γ.continuous.subtype_mk _
  have hsurj : Surjective f := by
    rintro ⟨x, t, rfl⟩
    exact ⟨t, rfl⟩
  let : LocallyConnectedSpace PathTime := locallyConnected_pathTime
  let : LocallyConnectedSpace (range γ) :=
    (Topology.IsQuotientMap.of_surjective_continuous hsurj hf).isCoinducing.locallyConnectedSpace
  have hc : IsCompact (range γ) := isCompact_range γ.continuous
  let : ConnectedSpace (range γ) := Subtype.connectedSpace (isConnected_range γ.continuous)
  have hconn : IsConnected (univ : Set (range γ)) :=
    isConnected_univ
  have hne' : f ⊥ ≠ f ⊤ := fun h => hne (congrArg Subtype.val h)
  obtain ⟨a, ha, _⟩ := harcs (range γ) hc inferInstance univ isOpen_univ hconn
    (f ⊥) (by trivial) (f ⊤) (by trivial) hne'
  refine ⟨⟨fun t => (a t).val, continuous_subtype_val.comp a.continuous⟩,
    Subtype.val_injective.comp ha, congrArg Subtype.val a.source,
    congrArg Subtype.val a.target, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact (a t).property

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasurableTerminalArcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the published measurable selection theorem to the actual Borel
relation of simple subarcs of the last-entry terminal path. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r5b9296_2 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_measurable_terminal_arc_selector
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (V : Set Sphere) (hV : IsOpen V) :
    ∃ f : C(PathTime, Sphere) → C(PathTime, Sphere), AEMeasurable f (μ : Measure _) ∧
      ∀ γ, γ ⊥ ∉ V → γ ⊤ ∈ V →
        (terminalPath γ (lastEntryTime γ V), f γ) ∈ simpleSubarcRelation := by
  let δ (γ : C(PathTime, Sphere)) := terminalPath γ (lastEntryTime γ V)
  have hδ : Measurable δ := measurable_lastEntryPath V hV
  let R : Set (C(PathTime, Sphere) × C(PathTime, Sphere)) :=
    {p | (δ p.1) ⊥ = (δ p.1) ⊤} ∪ {p | (δ p.1, p.2) ∈ simpleSubarcRelation}
  have hR : MeasurableSet R := by
    apply MeasurableSet.union
    · exact measurableSet_eq_fun
        ((continuous_eval_const ⊥).measurable.comp (hδ.comp measurable_fst))
        ((continuous_eval_const ⊤).measurable.comp (hδ.comp measurable_fst))
    · exact measurableSet_simpleSubarcRelation.preimage
        ((hδ.comp measurable_fst).prodMk measurable_snd)
  have hnon (γ : C(PathTime, Sphere)) : ∃ α, (γ, α) ∈ R := by
    by_cases he : δ γ ⊥ = δ γ ⊤
    · exact ⟨γ, Or.inl he⟩
    · obtain ⟨α, ha, h0, h1, hr⟩ := exists_simple_subarc harcs (δ γ) he
      exact ⟨α, Or.inr ⟨ha, h0, h1, hr⟩⟩
  obtain ⟨f, hfm, hf⟩ := hselect μ R hR hnon
  refine ⟨f, hfm.aemeasurable, ?_⟩
  intro γ hstart hend
  rcases hf γ with he | he
  · have hfront := lastEntry_frontier γ hV hstart hend
    change δ γ ⊥ = δ γ ⊤ at he
    have he' : γ (lastEntryTime γ V) = γ ⊤ := by
      simpa only [δ, terminalPath, ContinuousMap.comp_apply,
        affinePathTime_zero, affinePathTime_one] using he
    exact (disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hV)
      (he' ▸ hfront) hend).elim
  · exact he

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem terminal_arc_selector_properties
    {f : C(PathTime, Sphere) → C(PathTime, Sphere)} {V : Set Sphere} (hV : IsOpen V)
    (hf : ∀ γ, γ ⊥ ∉ V → γ ⊤ ∈ V →
      (terminalPath γ (lastEntryTime γ V), f γ) ∈ simpleSubarcRelation)
    (γ : C(PathTime, Sphere)) (hstart : γ ⊥ ∉ V) (hend : γ ⊤ ∈ V) :
    Injective (f γ) ∧ (f γ) ⊥ = γ (lastEntryTime γ V) ∧ (f γ) ⊤ = γ ⊤ ∧
      range (f γ) ⊆ lastEntryTail γ V ∧ (f γ) ⊥ ∈ frontier V ∧
      ∀ t ∈ Ioo (⊥ : PathTime) ⊤, (f γ) t ∈ V \ {γ ⊤} := by
  obtain ⟨hinj, h0, h1, hsub⟩ := hf γ hstart hend
  have h0' : (f γ) ⊥ = γ (lastEntryTime γ V) := by
    simpa only [terminalPath, ContinuousMap.comp_apply, affinePathTime_zero] using h0
  have h1' : (f γ) ⊤ = γ ⊤ := by
    simpa only [terminalPath, ContinuousMap.comp_apply, affinePathTime_one] using h1
  have htail : range (f γ) ⊆ lastEntryTail γ V := by
    intro x hx
    obtain ⟨t, rfl⟩ := hsub hx
    exact ⟨affinePathTime (lastEntryTime γ V) ⊤ t,
      (affinePathTime_mem_Icc le_top t).1, rfl⟩
  refine ⟨hinj, h0', h1', htail, ?_, ?_⟩
  · simpa only [h0'] using lastEntry_frontier γ hV hstart hend
  · intro t ht
    constructor
    · by_contra hn
      have he := lastEntryTail_outside γ V (htail (mem_range_self t)) hn
      exact ht.1.ne' (hinj (he.trans h0'.symm))
    · intro he
      exact ht.2.ne (hinj (he.trans h1'.symm))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TerminalArcLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable simple-arc reduction preserves the last-entry distribution
and cannot increase any point-hit probability. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

variable (μ : ProbabilityMeasure C(PathTime, Sphere))
  (V : Set Sphere) (hV : IsOpen V)
  (f : C(PathTime, Sphere) → C(PathTime, Sphere))
  (hfm : AEMeasurable f (μ : Measure C(PathTime, Sphere)))
  (hf : ∀ γ, γ ⊥ ∉ V → γ ⊤ ∈ V →
    (terminalPath γ (lastEntryTime γ V), f γ) ∈ simpleSubarcRelation)
  (hends : ∀ᵐ γ ∂(μ : Measure C(PathTime, Sphere)), γ ⊥ ∉ V ∧ γ ⊤ ∈ V)

include hV hfm hf hends

theorem terminalArcLaw_hit_le (x : Sphere) :
    pathHitProbability (μ.map hfm) x ≤ pathHitProbability μ x := by
  rw [pathHitProbability, ProbabilityMeasure.map_apply' μ hfm
    (isClosed_paths_hitting x).measurableSet]
  apply measure_mono_ae
  filter_upwards [hends] with γ hγ
  rintro ⟨t, ht⟩
  have hs := (terminal_arc_selector_properties hV hf γ hγ.1 hγ.2).2.2.2.1
  obtain ⟨s, _, he⟩ := hs (ht ▸ mem_range_self (f := f γ) t)
  exact ⟨s, he⟩

theorem terminalArcLaw_hit_eq_zero {x : Sphere} (hx : x ∉ closure V) :
    pathHitProbability (μ.map hfm) x = 0 := by
  rw [pathHitProbability, ProbabilityMeasure.map_apply' μ hfm
    (isClosed_paths_hitting x).measurableSet]
  apply measure_mono_null (t := {γ | ¬ (γ ⊥ ∉ V ∧ γ ⊤ ∈ V)})
  · intro γ hhit hγ
    obtain ⟨t, ht⟩ := hhit
    have hs := (terminal_arc_selector_properties hV hf γ hγ.1 hγ.2).2.2.2.1
    exact hx (lastEntryTail_subset_closure γ hV hγ.1 hγ.2
      (hs (ht ▸ mem_range_self (f := f γ) t)))
  · exact ae_iff.mp hends

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TerminalArcSet
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint and interior conditions of the compact arc reduction form
a Borel set. Consequently a full law of these arcs has a compact core. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_4
lemma measurableSet_pathsInsideOpenTime (V : Set Sphere) (hV : IsOpen V)
    (T : Set PathTime) (hT : IsOpen T) :
    MeasurableSet {α : C(PathTime, Sphere) | MapsTo α T V} := by
  have he : {α : C(PathTime, Sphere) | MapsTo α T V} =
      ⋂ p : DyadicInside T, pathsInsideOn V
        (dyadicLeft p.val.1 p.val.2) (dyadicRight p.val.1 p.val.2) := by
    ext α
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h p
      exact h.mono_left p.property
    · intro h t ht
      obtain ⟨p, hp⟩ := mem_iUnion.mp ((iUnion_insideDyadicCell hT).symm ▸ ht)
      exact h p hp
  rw [he]
  exact MeasurableSet.iInter fun p => (isOpen_pathsInsideOn hV _ _).measurableSet

lemma measurableSet_terminalArcSet (V : Set Sphere) (hV : IsOpen V) (b : Sphere) :
    MeasurableSet (terminalArcSet V b) := by
  exact measurableSet_injective_paths.inter
    (((continuous_eval_const ⊥).measurable isClosed_frontier.measurableSet).inter
      ((measurableSet_eq_fun (continuous_eval_const ⊤).measurable measurable_const).inter
        (measurableSet_pathsInsideOpenTime V hV (Ioo ⊥ ⊤) isOpen_Ioo)))

theorem terminalArcLaw_mem (μ : ProbabilityMeasure C(PathTime, Sphere))
    (V : Set Sphere) (hV : IsOpen V) (b : Sphere)
    (f : C(PathTime, Sphere) → C(PathTime, Sphere))
    (hfm : AEMeasurable f (μ : Measure C(PathTime, Sphere)))
    (hf : ∀ γ, γ ⊥ ∉ V → γ ⊤ ∈ V →
      (terminalPath γ (lastEntryTime γ V), f γ) ∈ simpleSubarcRelation)
    (hends : ∀ᵐ γ ∂(μ : Measure C(PathTime, Sphere)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V ∧ γ ⊤ = b) :
    ∀ᵐ α : C(PathTime, Sphere) ∂(μ.map (f := f) (by first | exact hfm | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, Sphere)),
      α ∈ terminalArcSet V b := by
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff hfm (measurableSet_terminalArcSet V hV b)).mpr
  filter_upwards [hends] with γ hγ
  obtain ⟨hi, h0, h1, hs, hfront, hinterior⟩ :=
    terminal_arc_selector_properties hV hf γ hγ.1 hγ.2.1
  exact ⟨hi, hfront, h1.trans hγ.2.2, fun t ht => (hinterior t ht).1⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactArcLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditioning the terminal-arc law on a compact family of mass greater
than one half loses at most a factor two in every measure bound. -/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

section Restriction
variable {Ω : Type*} [MeasurableSpace Ω]

theorem restrictProbability_le_two (μ : ProbabilityMeasure Ω) (K : Set Ω)
    (hK : (1 / 2 : ℝ≥0∞) ≤ (μ : Measure Ω) K) :
    (restrictProbability μ K (ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1/2).trans_le hK)) : Measure Ω) ≤
      (2 : ℝ≥0∞) • (μ : Measure Ω) := by
  apply Measure.le_iff.mpr
  intro S hS
  change cond (μ : Measure Ω) K S ≤ _
  rw [cond_apply' hS, Measure.smul_apply, smul_eq_mul]
  apply mul_le_mul' ?_ (measure_mono inter_subset_right)
  have hi := ENNReal.inv_le_inv.mpr hK
  norm_num at hi ⊢
  exact hi

theorem restrictProbability_ae_mem (μ : ProbabilityMeasure Ω) (K : Set Ω)
    (hK : (μ : Measure Ω) K ≠ 0) (hm : MeasurableSet K) :
    ∀ᵐ x ∂(restrictProbability μ K hK : Measure Ω), x ∈ K := ae_cond_mem hm

end Restriction

attribute [local instance] sphereMetric sphereBorel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SimpleArcPhysicalLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simple arc has no occupation atom at its starting point. Thus a
terminal arc whose other points lie inside a collar is paid for by the
original occupation restricted to that collar. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem simple_arc_physical_occupation (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (α : FinitePhysicalPath e y₀) (hi : Injective α.val) :
    dyadicPhysicalOccupation e y₀ α = (μH[1] : Measure Y).restrict
      ((physicalValue e y₀ ∘ α.val) '' (α.val ⁻¹' U)) :=
  le_antisymm (simple_arc_physical_occupation_le e hU y₀ α hi)
    (physical_image_hausdorff_le_occupation e hU y₀ α)

theorem simple_arc_physical_support (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (α : FinitePhysicalPath e y₀) (hi : Injective α.val)
    {W : Set Y} (hW : MeasurableSet W) (y : Y)
    (hout : ∀ t, α.val t ∈ U → physicalValue e y₀ (α.val t) ∉ W →
      physicalValue e y₀ (α.val t) = y) :
    (dyadicPhysicalOccupation e y₀ α).restrict W = dyadicPhysicalOccupation e y₀ α := by
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  change dyadicPhysicalOccupation e y₀ α Wᶜ = 0
  rw [simple_arc_physical_occupation e hU y₀ α hi, Measure.restrict_apply hW.compl]
  let : NullSingletonClass (μH[1] : Measure Y) :=
    Measure.nullSingletonClass_hausdorff Y (by norm_num)
  apply measure_mono_null (t := {y})
  · rintro z ⟨hz, t, ht, rfl⟩
    exact hout t ht hz
  · exact measure_singleton y

theorem simple_subarc_physical_localized_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ α : FinitePhysicalPath e y₀)
    (hi : Injective α.val) (hs : range α.val ⊆ range γ.val)
    {W : Set Y} (hW : MeasurableSet W) (y : Y)
    (hout : ∀ t, α.val t ∈ U → physicalValue e y₀ (α.val t) ∉ W →
      physicalValue e y₀ (α.val t) = y) :
    dyadicPhysicalOccupation e y₀ α ≤ (dyadicPhysicalOccupation e y₀ γ).restrict W := by
  rw [← simple_arc_physical_support e hU y₀ α hi hW y hout]
  exact Measure.restrict_mono_measure (simple_subarc_physical_occupation_le e hU y₀ γ α hi hs) W

variable [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace X] [BorelSpace X] in
lemma physicalValue_projects (e : G ≃ₜ U) (y₀ : Y) (π : Y → X)
    (hπ : ∀ y : G, π y.val = (e y).val) {x : X} (hx : x ∈ U) :
    π (physicalValue e y₀ x) = x := by
  simp only [physicalValue, dite_eq_left hx]
  rw [hπ]
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MeanArcLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localized occupation comparison after measurable simple-arc selection. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {G : Set Y} {U : Set X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma physicalOccupationCode_localized_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ α : C(PathTime, X)) (hγ : physicalDomainLength e y₀ γ < ∞)
    (hi : Injective α) (hs : range α ⊆ range γ)
    {W : Set Y} (hW : MeasurableSet W) (y : Y)
    (hout : ∀ t, α t ∈ U → physicalValue e y₀ (α t) ∉ W → physicalValue e y₀ (α t) = y) :
    physicalOccupationCode e y₀ α ≤ (physicalOccupationCode e y₀ γ).restrict W := by
  have hα : physicalDomainLength e y₀ α < ∞ :=
    (simple_subarc_physical_length_le e hU y₀ ⟨γ, hγ⟩ α hi hs).trans_lt hγ
  rw [physicalOccupationCode_eq e y₀ ⟨α, hα⟩, physicalOccupationCode_eq e y₀ ⟨γ, hγ⟩]
  exact simple_subarc_physical_localized_le e hU y₀ ⟨γ, hγ⟩ ⟨α, hα⟩ hi hs hW y hout

omit [BorelSpace X] in
lemma physicalOccupationCode_collar_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπm : Measurable π) (hπ : ∀ y : G, π y.val = (e y).val)
    (γ α : C(PathTime, X)) (hγ : physicalDomainLength e y₀ γ < ∞)
    (hi : Injective α) (hs : range α ⊆ range γ)
    (V : Set X) (hV : MeasurableSet V) (hout : ∀ t, α t ∉ V → α t = α ⊥) :
    physicalOccupationCode e y₀ α ≤ (physicalOccupationCode e y₀ γ).restrict (π ⁻¹' V) := by
  apply physicalOccupationCode_localized_le e hU y₀ γ α hγ hi hs (hπm hV)
    (physicalValue e y₀ (α ⊥))
  intro t ht hn
  apply congrArg (physicalValue e y₀)
  apply hout t
  simpa only [mem_preimage, physicalValue_projects e y₀ π hπ ht] using hn

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

omit [BorelSpace X] in
lemma meanPhysicalOccupation_map_collar_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπm : Measurable π) (hπ : ∀ y : G, π y.val = (e y).val)
    (μ : ProbabilityMeasure C(PathTime, X)) (f : C(PathTime, X) → C(PathTime, X))
    (hfm : AEMeasurable f (μ : Measure C(PathTime, X)))
    (V : Set X) (hV : MeasurableSet V)
    (hgood : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)),
      physicalDomainLength e y₀ γ < ∞ ∧ Injective (f γ) ∧ range (f γ) ⊆ range γ ∧
      ∀ t, (f γ) t ∉ V → (f γ) t = (f γ) ⊥) :
    meanPhysicalOccupation e y₀ (μ.map (f := f) (by first | exact hfm | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) ≤ (meanPhysicalOccupation e y₀ μ).restrict (π ⁻¹' V) := by
  apply Measure.le_iff.mpr
  intro S hS
  have hm : Measurable (fun γ => physicalOccupationCode e y₀ γ S) :=
    (Measure.measurable_coe hS).comp (measurable_physicalOccupationCode e hU y₀)
  rw [meanPhysicalOccupation_apply e hU y₀ _ hS, ProbabilityMeasure.toMeasure_map,
    lintegral_map' hm.aemeasurable hfm, Measure.restrict_apply hS,
    meanPhysicalOccupation_apply e hU y₀ _ (hS.inter (hπm hV))]
  apply lintegral_mono_ae
  filter_upwards [hgood] with γ hγ
  have h := physicalOccupationCode_collar_le e hU y₀ π hπm hπ γ (f γ)
    hγ.1 hγ.2.1 hγ.2.2.1 V hV hγ.2.2.2 S
  rwa [Measure.restrict_apply hS] at h

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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DominatedDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the pointwise density bound from domination of actual measures. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

theorem exists_density_le_of_domination (σ ν : Measure X) [SigmaFinite σ] [SigmaFinite ν]
    (g : X → ℝ≥0∞) (h : ν ≤ σ.withDensity g) :
    ∃ f : X → ℝ≥0∞, Measurable f ∧ ν = σ.withDensity f ∧ f ≤ᵐ[σ] g := by
  have hac : ν ≪ σ := (Measure.absolutelyContinuous_of_le h).trans (withDensity_absolutelyContinuous σ g)
  refine ⟨ν.rnDeriv σ, Measure.measurable_rnDeriv ν σ,
    (Measure.withDensity_rnDeriv_eq ν σ hac).symm, ?_⟩
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν σ)
  intro S hS _
  rw [← withDensity_apply _ hS, ← withDensity_apply _ hS]
  exact (Measure.withDensity_rnDeriv_le ν σ S).trans (h S)

theorem exists_localized_density_of_square_domination (σ ν : Measure X) [IsFiniteMeasure σ]
    (g : X → ℝ≥0∞) (hg : Measurable g) (he : (∫⁻ x, g x ^ 2 ∂σ) < ∞)
    (W : Set X) (hW : MeasurableSet W)
    (h : ν ≤ (2 : ℝ≥0∞) • (σ.withDensity g).restrict W) :
    ∃ f : X → ℝ≥0∞, Measurable f ∧ ν = σ.withDensity f ∧
      f ≤ᵐ[σ] (fun x => 2 * W.indicator g x) := by
  have hmass : (σ.withDensity g) univ < ∞ :=
    (mass_le_densityMassBound σ hg le_rfl).trans_lt (densityMassBound_lt_top σ he)
  let : IsFiniteMeasure (σ.withDensity g) := ⟨hmass⟩
  have hfin : ((2 : ℝ≥0∞) • (σ.withDensity g).restrict W) univ < ∞ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top _ _)
  let : IsFiniteMeasure ν := ⟨(h univ).trans_lt hfin⟩
  apply exists_density_le_of_domination σ ν (fun x => 2 * W.indicator g x)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  change σ.withDensity ((2 : ℝ≥0∞) • W.indicator g) = _
  rw [withDensity_smul 2 (hg.indicator hW), withDensity_indicator hW,
    restrict_withDensity hW]

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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem tendsto_shrinking_occupation_energy (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (σ : Measure Y)
    (g : Y → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanCodeOccupation d P = σ.withDensity g)
    (henergy : (∫⁻ x, g x ^ 2 ∂σ) < ∞)
    (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n)) (hanti : Antitone A)
    (hshrink : (⋂ n, A n) ⊆ d.physicalDomainᶜ) :
    Tendsto (fun n => ∫⁻ x in A n, g x ^ 2 ∂σ) atTop (𝓝 0) := by
  let ν := σ.withDensity (fun x => g x ^ 2)
  have hfin : IsFiniteMeasure ν := ⟨by
    simpa only [ν, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using henergy⟩
  have hz : ν d.physicalDomainᶜ = 0 :=
    square_density_null_of_density_null σ g hg hG.measurableSet.compl
      (hocc ▸ meanCodeOccupation_compl d hU hG P)
  have hint : ν (⋂ n, A n) = 0 := measure_mono_null hshrink hz
  have ht := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (hA n).nullMeasurableSet) hanti ⟨0, measure_ne_top ν _⟩
  rw [hint] at ht
  simpa only [ν, Function.comp_def, withDensity_apply _ (hA _)] using ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ArcReductionNormBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact factor-two density and hit estimates yield the L² bounds
used in the compact-arc smallness statement. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem countingSquareNorm_twice {S : Type*} (m : S → ℝ≥0∞) :
    countingSquareNorm (fun s => 2 * m s) = 2 * countingSquareNorm m := by
  simp only [countingSquareNorm, mul_pow]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have htwo : ((2 : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) = 2 := by
    simpa only [Nat.cast_ofNat, one_div] using ENNReal.pow_rpow_inv_natCast (by decide : (2 : ℕ) ≠ 0) (2 : ℝ≥0∞)
  rw [htwo]

theorem arc_density_squareNorm_le
    {X : Type*} [MeasurableSpace X] (σ : Measure X)
    (g f : X → ℝ≥0∞) (hg : Measurable g) (W : Set X) (hW : MeasurableSet W)
    (hf : f ≤ᵐ[σ] fun x => 2 * W.indicator g x) :
    (∫⁻ x, f x ^ 2 ∂σ) ^ (1 / 2 : ℝ) ≤
      2 * (∫⁻ x in W, g x ^ 2 ∂σ) ^ (1 / 2 : ℝ) := by
  have hbound : (∫⁻ x, f x ^ 2 ∂σ) ≤ (2 : ℝ≥0∞) ^ 2 * ∫⁻ x in W, g x ^ 2 ∂σ := by
    calc
      _ ≤ ∫⁻ x, (2 * W.indicator g x) ^ 2 ∂σ :=
        lintegral_mono_ae (hf.mono fun x hx => pow_le_pow_left' hx 2)
      _ = _ := by
        have he : (fun x => (2 * W.indicator g x) ^ 2) =
            fun x => (2 : ℝ≥0∞) ^ 2 * W.indicator (fun x => g x ^ 2) x := by
          funext x
          by_cases hx : x ∈ W <;> simp [hx, mul_pow]
        rw [he, lintegral_const_mul _ ((hg.pow_const 2).indicator hW), lintegral_indicator hW]
  calc
    _ ≤ ((2 : ℝ≥0∞) ^ 2 * ∫⁻ x in W, g x ^ 2 ∂σ) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      have htwo : ((2 : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) = 2 := by
        simpa only [Nat.cast_ofNat, one_div] using ENNReal.pow_rpow_inv_natCast (by decide : (2 : ℕ) ≠ 0) (2 : ℝ≥0∞)
      rw [htwo]

theorem arc_hit_squareNorm_le {S : Type*} (m h : S → ℝ≥0∞) (p : S) (W : Set S)
    (hle : ∀ s, h s ≤ 2 * m s) (hout : ∀ s ∉ W, h s = 0) :
    countingSquareNorm (fun s => if s ≠ p then h s else 0) ≤
      2 * countingSquareNorm (fun s => if s ∈ W ∧ s ≠ p then m s else 0) := by
  calc
    _ ≤ countingSquareNorm (fun s => 2 * (if s ∈ W ∧ s ≠ p then m s else 0)) := by
      apply countingSquareNorm_mono
      intro s
      by_cases hp : s = p
      · simp [hp]
      · by_cases hs : s ∈ W
        · simpa only [hp, ne_eq, not_false_eq_true, hs, and_self, ite_true, if_true] using hle s
        · simp [hp, hs, hout s hs]
    _ = _ := countingSquareNorm_twice _

end CircleDomainRigidity

end

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
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientDiskTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Topology of projected physical disks

Physical Jordan disks with boundary in the original domain have saturated
interiors and saturated closures. Their images are open with connected
complements, and disjoint physical closed disks give disjoint quotient closed
disks. These properties allow finite dust covers to be used in the descending
grid construction without postulating a disk-selection lemma.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem preimage_image_closure_of_singleton_boundary_fibers
    {X Y : Type*} [TopologicalSpace X]
    (π : X → Y) (hfibers : ∀ y, IsPreconnected (π ⁻¹' {y}))
    {U : Set X} (hU : IsOpen U)
    (hsing : ∀ p ∈ frontier U, ∀ q, π q = π p → q = p) :
    π ⁻¹' (π '' closure U) = closure U := by
  have hsat := preimage_image_open_of_singleton_boundary_fibers π hfibers hU hsing
  apply Set.Subset.antisymm
  · rintro q ⟨p, hp, hpq⟩
    by_cases hpU : p ∈ U
    · apply subset_closure
      rw [← hsat]
      exact ⟨p, hpU, hpq⟩
    · have hpfront : p ∈ frontier U := by
        rw [hU.frontier_eq]
        exact ⟨hp, hpU⟩
      have hqp : q = p := hsing p hpfront q hpq.symm
      simpa only [hqp] using hp
  · exact subset_preimage_image π (closure U)

theorem preimage_image_closed_jordanInterior_of_component_collapse
    {Y : Type*} (G : Set Sphere) (π : Sphere → Y) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior H))) =
      ((↑) : ℂ → Sphere) '' closure (jordanInterior H) := by
  rw [← closure_sphere_image_jordanInterior]
  apply preimage_image_closure_of_singleton_boundary_fibers π
    (fun y => (connected_fibers_of_component_collapse G π hsurj hr y).isPreconnected)
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H))
  intro p hp q hqp
  rw [frontier_sphere_image_jordanInterior] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  rcases (hr (z : Sphere) q).mp hqp.symm with heq | ⟨hznot, _⟩
  · exact heq.symm
  · exact (hznot (hboundary z hz)).elim

theorem closure_image_jordanInterior
    {Y : Type*} [TopologicalSpace Y] (π : Sphere → Y)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (H : ℂ ≃ₜ ℂ) :
    closure (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior H)) := by
  rw [hclosed.closure_image_eq_of_continuous hπ, closure_sphere_image_jordanInterior]

theorem infty_notMem_closure_image_jordanInterior
    {Y : Type*} [TopologicalSpace Y]
    (G : Set Sphere) (π : Sphere → Y) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    π OnePoint.infty ∉ closure (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  rw [closure_image_jordanInterior π hπ hclosed H]
  intro h
  have hmem : OnePoint.infty ∈ ((↑) : ℂ → Sphere) '' closure (jordanInterior H) := by
    rw [← preimage_image_closed_jordanInterior_of_component_collapse
      G π hsurj hr H hboundary]
    exact h
  obtain ⟨z, _, hz⟩ := hmem
  exact (OnePoint.coe_ne_infty z) hz

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalLawRebasing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical length and occupation do not depend on the fallback point at dust
parameters. This permits a recursive law to use the original domain presentation. -/
open Set Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {G : Set Y} {U : Set X}

 theorem physicalDomainLength_basePoint (e : G ≃ₜ U) (y₁ y₂ : Y)
    (γ : C(PathTime, X)) : physicalDomainLength e y₁ γ = physicalDomainLength e y₂ γ := by
  unfold physicalDomainLength physicalStageLength
  congr 1
  funext n
  apply Finset.sum_congr rfl
  intro i _
  unfold physicalDyadicLength physicalDyadicPath totalPhysicalSubpath
  split_ifs
  · rfl
  · have hz (y : Y) : eVariationOn (ContinuousMap.const PathTime y) univ = 0 := by
      apply (eVariationOn.eq_zero_iff _).mpr
      intro _ _ _ _
      exact edist_self y
    rw [hz, hz]


variable [MeasurableSpace Y] [BorelSpace Y]

 theorem physicalStageOccupation_basePoint (e : G ≃ₜ U) (y₁ y₂ : Y)
    (n : ℕ) (γ : C(PathTime, X)) :
    physicalStageOccupation e y₁ n γ = physicalStageOccupation e y₂ n γ := by
  unfold physicalStageOccupation
  apply Finset.sum_congr rfl
  intro i _
  unfold physicalDyadicPath totalPhysicalSubpath
  split_ifs
  · rfl
  · simp only [rectifiableOccupationCode_const]

 theorem physicalOccupationCode_basePoint (e : G ≃ₜ U) (y₁ y₂ : Y)
    (γ : C(PathTime, X)) : physicalOccupationCode e y₁ γ = physicalOccupationCode e y₂ γ := by
  have hlen := physicalDomainLength_basePoint e y₁ y₂ γ
  unfold physicalOccupationCode
  split_ifs with h₁ h₂ h₂
  · apply Measure.ext
    intro s hs
    rw [dyadicPhysicalOccupation_apply _ _ _ hs, dyadicPhysicalOccupation_apply _ _ _ hs]
    simp only [physicalStageOccupation_basePoint e y₁ y₂]
  · exact (h₂ (hlen ▸ h₁)).elim
  · exact (h₁ (hlen.symm ▸ h₂)).elim
  · rfl

 omit [MeasurableSpace Y] [BorelSpace Y] in
 theorem domainEquiv_eq_of_projection {G₁ G₂ : Set Y} {U₁ U₂ : Set X}
    (e₁ : G₁ ≃ₜ U₁) (e₂ : G₂ ≃ₜ U₂) (hG : G₁ = G₂) (hU : U₁ = U₂)
    (π : Y → X) (he₁ : ∀ x : G₁, (e₁ x).val = π x.val)
    (he₂ : ∀ x : G₂, (e₂ x).val = π x.val) :
    HEq e₁ e₂ := by
  subst G₂
  subst U₂
  apply heq_of_eq
  ext x
  exact (he₁ x).trans (he₂ x).symm

 omit [MeasurableSpace Y] [BorelSpace Y] in
 theorem physicalDomainLength_congr_projection {G₁ G₂ : Set Y} {U₁ U₂ : Set X}
    (e₁ : G₁ ≃ₜ U₁) (e₂ : G₂ ≃ₜ U₂) (hG : G₁ = G₂) (hU : U₁ = U₂)
    (π : Y → X) (he₁ : ∀ x : G₁, (e₁ x).val = π x.val)
    (he₂ : ∀ x : G₂, (e₂ x).val = π x.val) (y₁ y₂ : Y) (γ : C(PathTime, X)) :
    physicalDomainLength e₁ y₁ γ = physicalDomainLength e₂ y₂ γ := by
  have he := domainEquiv_eq_of_projection e₁ e₂ hG hU π he₁ he₂
  subst G₂
  subst U₂
  cases eq_of_heq he
  exact physicalDomainLength_basePoint e₁ y₁ y₂ γ

 theorem physicalOccupationCode_congr_projection {G₁ G₂ : Set Y} {U₁ U₂ : Set X}
    (e₁ : G₁ ≃ₜ U₁) (e₂ : G₂ ≃ₜ U₂) (hG : G₁ = G₂) (hU : U₁ = U₂)
    (π : Y → X) (he₁ : ∀ x : G₁, (e₁ x).val = π x.val)
    (he₂ : ∀ x : G₂, (e₂ x).val = π x.val) (y₁ y₂ : Y) (γ : C(PathTime, X)) :
    physicalOccupationCode e₁ y₁ γ = physicalOccupationCode e₂ y₂ γ := by
  have he := domainEquiv_eq_of_projection e₁ e₂ hG hU π he₁ he₂
  subst G₂
  subst U₂
  cases eq_of_heq he
  exact physicalOccupationCode_basePoint e₁ y₁ y₂ γ

variable [MeasurableSpace C(PathTime, X)]
 theorem meanPhysicalOccupation_congr_projection {G₁ G₂ : Set Y} {U₁ U₂ : Set X}
    (e₁ : G₁ ≃ₜ U₁) (e₂ : G₂ ≃ₜ U₂) (hG : G₁ = G₂) (hU : U₁ = U₂)
    (π : Y → X) (he₁ : ∀ x : G₁, (e₁ x).val = π x.val)
    (he₂ : ∀ x : G₂, (e₂ x).val = π x.val) (y₁ y₂ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) :
    meanPhysicalOccupation e₁ y₁ μ = meanPhysicalOccupation e₂ y₂ μ := by
  unfold meanPhysicalOccupation
  congr 1
  funext γ
  exact physicalOccupationCode_congr_projection e₁ e₂ hG hU π he₁ he₂ y₁ y₂ γ

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

theorem pathImageCount_mono_range (H : Set X) {α γ : C(PathTime, X)}
    (h : range α ⊆ range γ) : pathImageCount H α ≤ pathImageCount H γ := by
  unfold pathImageCount
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ range α ∩ H
  · have hy : x ∈ range γ ∩ H := ⟨h hx.1, hx.2⟩
    simp only [hx, hy, ite_true, if_true, le_refl]
  · simp only [hx, ite_false, if_false, zero_le]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem mean_subarc_intersections_le
    (μ η : ProbabilityMeasure C(PathTime, X)) (f : C(PathTime, X) → C(PathTime, X))
    (hf : AEMeasurable f (μ : Measure C(PathTime, X)))
    (hs : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), range (f γ) ⊆ range γ)
    (hη : (η : Measure C(PathTime, X)) ≤ (2 : ℝ≥0∞) • (μ.map (f := f) (by first | exact hf | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, X)))
    {H : Set X} (hH : IsClosed H) :
    (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, X))) ≤
      2 * ∫⁻ γ, pathImageCount H γ ∂(μ : Measure C(PathTime, X)) := by
  calc
    _ ≤ ∫⁻ α, pathImageCount H α ∂((2 : ℝ≥0∞) • (μ.map (f := f) (by first | exact hf | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, X))) :=
      lintegral_mono' hη le_rfl
    _ = 2 * ∫⁻ γ, pathImageCount H (f γ) ∂(μ : Measure C(PathTime, X)) := by
      rw [lintegral_smul_measure, ProbabilityMeasure.toMeasure_map,
        lintegral_map' (measurable_pathImageCount hH).aemeasurable hf]
      rfl
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_ae (hs.mono fun _ h => pathImageCount_mono_range H h))

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

local instance localInst_r5b9296_3 : BorelSpace Sphere := ⟨rfl⟩
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
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereSliceChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every finite physical point has a chart neighborhood with a concrete
inverse Lipschitz bound. This is used only on compact coordinate slices. -/

open Set Function Filter Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

 theorem exists_sphereSliceChart (z : ℂ) :
    ∃ (B : ℝ≥0) (V : Set ℂ), IsOpen V ∧ z ∈ V ∧
      LipschitzOnWith B finiteCoord (((↑) : ℂ → Sphere) '' V) := by
  obtain ⟨B, W, hW, hB⟩ := finite_sphere_chart_inverse_pairs z
  have hc : Continuous (fun w : ℂ => (roundSphereEquiv (w : Sphere) : RoundAmbient)) :=
    continuous_subtype_val.comp (roundSphereEquiv.continuous.comp OnePoint.continuous_coe)
  obtain ⟨V, hVW, hV, hzV⟩ := _root_.mem_nhds_iff.mp (hc.continuousAt.preimage_mem_nhds hW)
  refine ⟨B, V, hV, hzV, LipschitzOnWith.of_dist_le_mul ?_⟩
  rintro _ ⟨w, hw, rfl⟩ _ ⟨u, hu, rfl⟩
  change dist w u ≤ (B : ℝ) *
    dist (roundSphereEquiv (w : Sphere) : RoundAmbient) (roundSphereEquiv (u : Sphere) : RoundAmbient)
  exact hB w u (hVW hw) (hVW hu)

 theorem finiteCoord_lipschitz_on_compact_chart {A : Set ℂ} (hA : IsCompact A) :
    ∃ B : ℝ≥0, LipschitzOnWith B finiteCoord (((↑) : ℂ → Sphere) '' A) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hA.image OnePoint.continuous_coe)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨B, V, hV, hzV, hBV⟩ := exists_sphereSliceChart z
  refine ⟨B, ((↑) : ℂ → Sphere) '' V, mem_nhdsWithin_of_mem_nhds ?_, hBV⟩
  exact (OnePoint.isOpenEmbedding_coe.isOpenMap V hV).mem_nhds ⟨z, hzV, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SphericalChartCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-integrable planar derivatives give the finite spherical
weights used by each local tag payment measure. The inverse chart is
Borel, including its arbitrary value at infinity. -/

open Set Function MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_7
theorem measurable_finiteCoord : Measurable finiteCoord := by
  classical
  obtain ⟨j, hj, he⟩ := OnePoint.isOpenEmbedding_coe.measurableEmbedding.exists_measurable_extend
    (measurable_id (α := ℂ)) (fun _ => inferInstance)
  have hfun : ({OnePoint.infty} : Set Sphere).piecewise (fun _ => (0 : ℂ)) j = finiteCoord := by
    funext p
    cases p using OnePoint.rec with
    | infty => simp [finiteCoord]
    | coe z =>
      simpa only [mem_singleton_iff, OnePoint.coe_ne_infty, not_false_eq_true, piecewise_eq_of_notMem,
        finiteCoord_coe, comp_apply, id_eq] using congrFun he z
  rw [← hfun]
  exact measurable_const.piecewise (measurableSet_singleton _) hj

end CircleDomainRigidity

end

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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
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
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskCentering
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit disk automorphism used to move the marked endpoint to
the origin in a Jordan disk coordinate. -/

open Set Function Filter Metric
open scoped Topology ComplexConjugate

noncomputable section
namespace CircleDomainRigidity

theorem diskCentering_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  have hnorm : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_left hz (norm_nonneg a)).trans_lt (by simpa using ha)
  intro h
  rw [(sub_eq_zero.mp h).symm, norm_one] at hnorm
  exact lt_irrefl _ hnorm

theorem diskCentering_normSq_identity (a z : ℂ) :
    Complex.normSq (1 - conj a * z) - Complex.normSq (z - a) =
      (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem diskCentering_norm_le {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖diskCentering a z‖ ≤ 1 := by
  have ha2 : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hz2 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hi := diskCentering_normSq_identity a z
  simp only [← Complex.sq_norm] at hi
  have hsq : ‖z - a‖ ^ 2 ≤ ‖1 - conj a * z‖ ^ 2 := by
    nlinarith [mul_nonneg ha2 hz2]
  have hn : ‖z - a‖ ≤ ‖1 - conj a * z‖ := by
    nlinarith [norm_nonneg (z - a), norm_nonneg (1 - conj a * z)]
  rw [diskCentering, norm_div]
  exact (div_le_one (norm_pos_iff.mpr (diskCentering_den_ne_zero ha hz))).mpr hn

theorem diskCentering_norm_lt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskCentering a z‖ < 1 := by
  have ha2 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hz2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hi := diskCentering_normSq_identity a z
  simp only [← Complex.sq_norm] at hi
  have hsq : ‖z - a‖ ^ 2 < ‖1 - conj a * z‖ ^ 2 := by
    nlinarith [mul_pos ha2 hz2]
  have hn : ‖z - a‖ < ‖1 - conj a * z‖ := by
    nlinarith [norm_nonneg (z - a), norm_nonneg (1 - conj a * z)]
  rw [diskCentering, norm_div]
  exact (div_lt_one (norm_pos_iff.mpr (diskCentering_den_ne_zero ha hz.le))).mpr hn

theorem diskCentering_norm_eq_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    ‖diskCentering a z‖ = 1 := by
  have hi := diskCentering_normSq_identity a z
  simp only [← Complex.sq_norm, hz, one_pow, sub_self, mul_zero] at hi
  have hn : ‖z - a‖ = ‖1 - conj a * z‖ := by
    nlinarith [norm_nonneg (z - a), norm_nonneg (1 - conj a * z)]
  rw [diskCentering, norm_div, hn, div_self (norm_ne_zero_iff.mpr (diskCentering_den_ne_zero ha hz.le))]

theorem continuousOn_diskCentering {a : ℂ} (ha : ‖a‖ < 1) :
    ContinuousOn (diskCentering a) (closedBall (0 : ℂ) 1) := by
  apply (continuous_id.sub continuous_const).continuousOn.div
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  intro z hz
  exact diskCentering_den_ne_zero ha (by simpa only [mem_closedBall_zero_iff, id_eq] using hz)

theorem diskCentering_inverse {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskCentering (-a) (diskCentering a z) = z := by
  have hden := diskCentering_den_ne_zero ha hz
  have haa := diskCentering_den_ne_zero ha ha.le
  have hneg : ‖-a‖ < 1 := by simpa only [norm_neg] using ha
  have hout := diskCentering_den_ne_zero hneg (diskCentering_norm_le ha hz)
  unfold diskCentering at hout ⊢
  simp only [map_neg, neg_mul, sub_neg_eq_add] at hout ⊢
  have haux : 1 + conj a * ((z - a) / (1 - conj a * z)) =
      (1 - conj a * a) / (1 - conj a * z) := by
    field_simp
    ring
  rw [haux]
  have hden' : 1 - z * conj a ≠ 0 := by simpa only [mul_comm] using hden
  have haa' : 1 - a * conj a ≠ 0 := by simpa only [mul_comm] using haa
  field_simp [hden, hden', haa, haa']
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskCenteringHomeomorph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centering formula is an actual homeomorphism of the closed disk. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem diskCentering_injOn (a : ℂ) (ha : ‖a‖ < 1) :
    InjOn (diskCentering a) (closedBall (0 : ℂ) 1) := by
  intro z hz w hw h
  have he := congrArg (diskCentering (-a)) h
  rwa [diskCentering_inverse ha (mem_closedBall_zero_iff.mp hz),
    diskCentering_inverse ha (mem_closedBall_zero_iff.mp hw)] at he

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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CenteredJordanCoordinate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered disk coordinates for the actual spherical Jordan collars.
The continuous extension is used only to push path laws to path space. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem sphereJordanCoordinate_norm_lt (K : ℂ ≃ₜ ℂ) {x : Sphere}
    (hx : x ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) :
    ‖sphereJordanCoordinate K x‖ < 1 := by
  obtain ⟨z, ⟨w, hw, rfl⟩, rfl⟩ := hx
  simpa only [sphereJordanCoordinate, finiteCoord_coe, K.symm_apply_apply,
    mem_ball_zero_iff] using hw

theorem sphereJordanCoordinate_norm_boundary (K : ℂ ≃ₜ ℂ) {x : Sphere}
    (hx : x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K)) :
    ‖sphereJordanCoordinate K x‖ = 1 := by
  rw [← range_sphereJordanBoundary] at hx
  obtain ⟨θ, rfl⟩ := hx
  change ‖K.symm (K (standardCirclePoint θ))‖ = 1
  rw [K.symm_apply_apply]
  exact Circle.norm_coe _

theorem centeredJordanCoordinate_continuousOn (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) :
    ContinuousOn (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) :=
  (continuousOn_diskCentering (sphereJordanCoordinate_norm_lt K hb)).comp
    (sphereJordanCoordinate_continuousOn K) (sphereJordanCoordinate_mapsTo K)

theorem centeredJordanCoordinate_injOn (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) :
    InjOn (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) := by
  intro x hx y hy he
  apply sphereJordanCoordinate_injOn K hx hy
  exact diskCentering_injOn _ (sphereJordanCoordinate_norm_lt K hb)
    (sphereJordanCoordinate_mapsTo K hx) (sphereJordanCoordinate_mapsTo K hy) he

theorem centeredJordanCoordinate_norm_le (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) {x : Sphere}
    (hx : x ∈ closure (((↑) : ℂ → Sphere) '' jordanInterior K)) :
    ‖centeredJordanCoordinate K b x‖ ≤ 1 :=
  diskCentering_norm_le (sphereJordanCoordinate_norm_lt K hb)
    (mem_closedBall_zero_iff.mp (sphereJordanCoordinate_mapsTo K hx))

theorem centeredJordanCoordinate_norm_boundary (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) {x : Sphere}
    (hx : x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K)) :
    ‖centeredJordanCoordinate K b x‖ = 1 :=
  diskCentering_norm_eq_one (sphereJordanCoordinate_norm_lt K hb)
    (sphereJordanCoordinate_norm_boundary K hx)

theorem exists_centeredJordanExtension (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) :
    ∃ F : C(Sphere, ℂ), EqOn F (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) := by
  let : TietzeExtension ℂ := TietzeExtension.of_homeo Complex.equivRealProdCLM.toHomeomorph
  let S := closure (((↑) : ℂ → Sphere) '' jordanInterior K)
  let f : C(S, ℂ) := ⟨fun x => centeredJordanCoordinate K b x.val,
    continuousOn_iff_continuous_domRestrict.mp (centeredJordanCoordinate_continuousOn K hb)⟩
  obtain ⟨F, hF⟩ := f.exists_restrict_eq isClosed_closure
  refine ⟨F, fun x hx => ?_⟩
  exact congrArg (fun g : C(S, ℂ) => g ⟨x, hx⟩) hF

end CircleDomainRigidity

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
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryIndexMean
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the proved boundary indices against an atomless starting
law gives a continuous boundary coordinate with positive period one. -/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer

lemma measurable_boundaryIndex (x : ℝ) :
    Measurable (fun a : UnitAddCircle => (⌊x - unitCircleCut a⌋ : ℝ)) :=
  (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
    (measurable_const.sub measurable_unitCircleCut).floor

lemma boundaryIndex_bound (x : ℝ) (a : UnitAddCircle) :
    |(⌊x - unitCircleCut a⌋ : ℝ)| ≤ |x| + 2 := by
  have ha := unitCircleCut_mem a
  have hlo := Int.floor_le (x - unitCircleCut a)
  have hhi := Int.lt_floor_add_one (x - unitCircleCut a)
  apply abs_le.mpr
  constructor <;> linarith [ha.1, ha.2, le_abs_self x, neg_abs_le x]

lemma integrable_boundaryIndex (β : ProbabilityMeasure UnitAddCircle) (x : ℝ) :
    Integrable (fun a : UnitAddCircle => (⌊x - unitCircleCut a⌋ : ℝ))
      (β : Measure UnitAddCircle) :=
  Integrable.of_bound (measurable_boundaryIndex x).aestronglyMeasurable (|x| + 2)
    (Eventually.of_forall fun a => by simpa only [Real.norm_eq_abs] using boundaryIndex_bound x a)

lemma continuousAt_boundaryIndex (a : UnitAddCircle) (x : ℝ) (ha : a ≠ (x : UnitAddCircle)) :
    ContinuousAt (fun y : ℝ => (⌊y - unitCircleCut a⌋ : ℝ)) x := by
  let y := x - unitCircleCut a
  have hne : (⌊y⌋ : ℝ) ≠ y := by
    intro h
    have hx : x = unitCircleCut a + (⌊y⌋ : ℝ) := by dsimp [y] at h <;> linarith
    apply ha
    rw [hx, AddCircle.coe_add]
    have hn : ((⌊y⌋ : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 (⌊y⌋ : ℝ) 0).mpr ⟨⌊y⌋, by simp⟩
    rw [hn, add_zero]
    exact AddCircle.coe_equivIco.symm
  have hy : (⌊y⌋ : ℝ) < y := lt_of_le_of_ne (Int.floor_le y) hne
  have hn : Ico (⌊y⌋ : ℝ) ((⌊y⌋ : ℝ) + 1) ∈ 𝓝 y :=
    mem_of_superset (Ioo_mem_nhds hy (Int.lt_floor_add_one y)) Ioo_subset_Ico_self
  exact ((continuousOn_floor ⌊y⌋).continuousAt hn).comp
    (f := fun z : ℝ => z - unitCircleCut a) (continuous_id.sub continuous_const).continuousAt

theorem continuous_boundaryIndexMean (β : ProbabilityMeasure UnitAddCircle)
    [NullSingletonClass (β : Measure UnitAddCircle)] : Continuous (boundaryIndexMean β) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated (bound := fun _ => |x| + 3)
  · exact Eventually.of_forall fun y => (measurable_boundaryIndex y).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    apply Eventually.of_forall
    intro a
    have hd : |y - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hy
    have hb := boundaryIndex_bound y a
    have ha : |y| ≤ |y - x| + |x| := by
      simpa only [sub_add_cancel] using abs_add_le (y - x) x
    simpa only [Real.norm_eq_abs] using (show |(⌊y - unitCircleCut a⌋ : ℝ)| ≤ |x| + 3 by linarith)
  · exact integrable_const _
  · have ha : ∀ᵐ a ∂(β : Measure UnitAddCircle), a ≠ (x : UnitAddCircle) := by
      exact ae_iff.mpr (by simp)
    exact ha.mono fun a h => continuousAt_boundaryIndex a x h

theorem boundaryIndexMean_add_one (β : ProbabilityMeasure UnitAddCircle) (x : ℝ) :
    boundaryIndexMean β (x + 1) = boundaryIndexMean β x + 1 := by
  have he : (fun a : UnitAddCircle => (⌊x + 1 - unitCircleCut a⌋ : ℝ)) =
      fun a => (⌊x - unitCircleCut a⌋ : ℝ) + 1 := by
    funext a
    rw [show x + 1 - unitCircleCut a = (x - unitCircleCut a) + 1 by ring,
      Int.floor_add_one, Int.cast_add, Int.cast_one]
  simp only [boundaryIndexMean, he, integral_add (integrable_boundaryIndex β x)
    (integrable_const 1), integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MeanArcIndex
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Borel arc index is averaged against the actual arc law. On the
boundary its average is the positive Stieltjes coordinate already proved. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem measurable_arcStartingAngle :
    Measurable (fun γ : C(PathTime, ℂ) => normalizedArgument (γ 0)) :=
  measurable_normalizedArgument.comp (continuous_eval_const 0).measurable

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CenteredArcLaw
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of the constructed terminal arc law to centered disk coordinates.
The coordinate extension is only evaluated on the closed collar. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

lemma terminalArcSet_mapsTo_closure {V : Set Sphere} {b : Sphere}
    {γ : C(PathTime, Sphere)} (hγ : γ ∈ terminalArcSet V b) (hb : b ∈ V) :
    MapsTo γ univ (closure V) := by
  intro t _
  by_cases h0 : t = ⊥
  · exact h0 ▸ frontier_subset_closure hγ.2.1
  by_cases h1 : t = ⊤
  · exact h1 ▸ hγ.2.2.1.symm ▸ subset_closure hb
  exact subset_closure (hγ.2.2.2 ⟨lt_of_le_of_ne bot_le (Ne.symm h0),
    lt_of_le_of_ne le_top h1⟩)

theorem centeredJordanPath_mem (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)))
    {γ : C(PathTime, Sphere)}
    (hγ : γ ∈ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior K) b) :
    F.comp γ ∈ diskTerminalArcSet := by
  have hcl := terminalArcSet_mapsTo_closure hγ hb
  have he (t : PathTime) : (F.comp γ) t = centeredJordanCoordinate K b (γ t) :=
    hF (hcl (mem_univ t))
  refine ⟨fun s t h => hγ.1 ?_, ?_, ?_, ?_⟩
  · exact centeredJordanCoordinate_injOn K hb (hcl (mem_univ s))
      (hcl (mem_univ t)) ((he s).symm.trans (h.trans (he t)))
  · rw [he]
    exact centeredJordanCoordinate_norm_boundary K hb hγ.2.1
  · rw [he]
    change centeredJordanCoordinate K b (γ ⊤) = 0
    rw [hγ.2.2.1, centeredJordanCoordinate_self]
  · intro t ht
    rw [he]
    exact diskCentering_norm_lt (sphereJordanCoordinate_norm_lt K hb)
      (sphereJordanCoordinate_norm_lt K (hγ.2.2.2 ht))

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem centeredArcLaw_hit (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)))
    (η : ProbabilityMeasure C(PathTime, Sphere))
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, Sphere)),
      γ ∈ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior K) b)
    {x : Sphere} (hx : x ∈ closure (((↑) : ℂ → Sphere) '' jordanInterior K)) :
    pathHitProbability (centeredArcLaw η F) (centeredJordanCoordinate K b x) =
      pathHitProbability η x := by
  rw [pathHitProbability, centeredArcLaw, ProbabilityMeasure.map_apply' η
    F.continuous_postcomp.measurable.aemeasurable (isClosed_paths_hitting _).measurableSet]
  apply measure_congr
  filter_upwards [hη] with γ hγ
  apply propext
  change (∃ t, F (γ t) = centeredJordanCoordinate K b x) ↔ ∃ t, γ t = x
  constructor
  · rintro ⟨t, ht⟩
    have hcl := terminalArcSet_mapsTo_closure hγ hb (mem_univ t)
    exact ⟨t, centeredJordanCoordinate_injOn K hb hcl hx ((hF hcl).symm.trans ht)⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, hF (terminalArcSet_mapsTo_closure hγ hb (mem_univ t))⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DiskStartLaw
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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

theorem diskStartingAngleLaw_atomless (η : ProbabilityMeasure C(PathTime, ℂ))
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)), ‖γ 0‖ = 1)
    (havoid : ∀ z : ℂ, ‖z‖ = 1 → pathHitProbability η z = 0) :
    NullSingletonClass (arcStartingAngleLaw η : Measure UnitAddCircle) := by
  constructor
  intro θ
  rw [arcStartingAngleLaw, ProbabilityMeasure.map_apply' η
    measurable_arcStartingAngle.aemeasurable (measurableSet_singleton θ)]
  by_cases hz : ∃ z : ℂ, ‖z‖ = 1 ∧ normalizedArgument z = θ
  · obtain ⟨z, hz, hθ⟩ := hz
    apply le_antisymm ?_ bot_le
    calc
      (η : Measure C(PathTime, ℂ))
          ((fun γ => normalizedArgument (γ 0)) ⁻¹' {θ}) ≤ pathHitProbability η z := by
        apply measure_mono_ae
        filter_upwards [hη] with γ hγ he
        exact ⟨0, normalizedArgument_injOn_unit_sphere hγ hz (he.trans hθ.symm)⟩
      _ = 0 := havoid z hz
  · apply measure_mono_null (t := {γ : C(PathTime, ℂ) | ¬ ‖γ 0‖ = 1})
    · intro γ he hγ
      exact hz ⟨γ 0, hγ, he⟩
    · exact ae_iff.mp hη

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CenteredBoundary
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive angular parametrization and inverse of a centered Jordan boundary. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric

theorem continuous_centeredJordanBoundary (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) :
    Continuous (centeredJordanBoundary K b) := by
  have ha : ‖-sphereJordanCoordinate K b‖ < 1 := by
    simpa only [norm_neg] using sphereJordanCoordinate_norm_lt K hb
  apply OnePoint.continuous_coe.comp
  apply K.continuous.comp
  apply (continuousOn_diskCentering ha).comp_continuous
    (continuous_subtype_val.comp (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous)
  intro θ
  exact mem_closedBall_zero_iff.mpr (Circle.norm_coe _).le

theorem centeredJordanBoundary_mem_frontier (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) (θ : UnitAddCircle) :
    centeredJordanBoundary K b θ ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K) := by
  rw [frontier_sphere_image_jordanInterior, frontier_jordanInterior]
  refine ⟨_, ⟨_, ?_, rfl⟩, rfl⟩
  apply mem_sphere_zero_iff_norm.mpr
  apply diskCentering_norm_eq_one
  · simpa only [norm_neg] using sphereJordanCoordinate_norm_lt K hb
  · exact Circle.norm_coe _

theorem centeredJordanCoordinate_boundary (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) (θ : UnitAddCircle) :
    centeredJordanCoordinate K b (centeredJordanBoundary K b θ) = standardCirclePoint θ := by
  change diskCentering (sphereJordanCoordinate K b)
    (K.symm (K (diskCentering (-sphereJordanCoordinate K b) (standardCirclePoint θ)))) = _
  rw [K.symm_apply_apply]
  have h := diskCentering_inverse
    (a := -sphereJordanCoordinate K b) (z := standardCirclePoint θ)
    (by simpa only [norm_neg] using sphereJordanCoordinate_norm_lt K hb)
    (Circle.norm_coe _).le
  simpa only [neg_neg] using h

theorem centeredJordanBoundary_inverse (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) {x : Sphere}
    (hx : x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K)) :
    centeredJordanBoundary K b (normalizedArgument (centeredJordanCoordinate K b x)) = x := by
  apply centeredJordanCoordinate_injOn K hb
    (frontier_subset_closure (centeredJordanBoundary_mem_frontier K hb _))
    (frontier_subset_closure hx)
  rw [centeredJordanCoordinate_boundary K hb,
    standardCirclePoint_normalizedArgument (centeredJordanCoordinate_norm_boundary K hb hx)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ArcBoundaryMeasure
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Stieltjes boundary integral is the integral over the starts of the
original spherical arcs, with no change of law hidden in the identity. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem centeredArcLaw_start_atomless (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)))
    (η : ProbabilityMeasure C(PathTime, Sphere))
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, Sphere)),
      γ ∈ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior K) b)
    (havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K),
      pathHitProbability η x = 0) :
    NullSingletonClass (arcStartingAngleLaw (centeredArcLaw η F) : Measure UnitAddCircle) := by
  apply diskStartingAngleLaw_atomless
  · rw [centeredArcLaw, ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff F.continuous_postcomp.measurable.aemeasurable
      (measurableSet_eq_fun ((continuous_eval_const 0).norm.measurable) measurable_const)).mpr
    exact hη.mono fun _ h => (centeredJordanPath_mem K hb F hF h).2.1
  · intro z hz
    let x := centeredJordanBoundary K b (normalizedArgument z)
    have hx : x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K) :=
      centeredJordanBoundary_mem_frontier K hb _
    have he : centeredJordanCoordinate K b x = z := by
      rw [centeredJordanCoordinate_boundary K hb, standardCirclePoint_normalizedArgument hz]
    rw [← he, centeredArcLaw_hit K hb F hF η hη (frontier_subset_closure hx)]
    exact havoid x hx

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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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

theorem diskRayAngle_zero (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0) :
    diskRayAngle γ hi he ⟨0, bot_lt_top⟩ = circleRepresentative (normalizedArgument (γ 0)) := by
  have h := diskRayAngle_mul_prefix γ hi he (⟨0, bot_lt_top⟩ : DiskRayTime) 0
  simpa only [zero_mul, realCirclePathLift,
    (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_zero,
    initialArcAngles, ContinuousMap.coe_mk, puncturedArgument] using h

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

theorem rayRightIndices_boundary_iff (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (x : ℝ)
    (hx : ∀ k : ℤ, x ≠ circleRepresentative (normalizedArgument (γ 0)) + (k : ℝ)) (k : ℤ) :
    k ∈ rayRightIndices hsch γ hγ (x : ℂ) ↔
      (k : ℝ) < x - circleRepresentative (normalizedArgument (γ 0)) := by
  let R := translatedHalfPlaneRay γ hγ k
  have hstart : (R.curve ⟨0, bot_lt_top⟩).re =
      circleRepresentative (normalizedArgument (γ 0)) + (k : ℝ) := by
    simp only [R, translatedHalfPlaneRay, ContinuousMap.coe_mk, Complex.add_re, Complex.intCast_re]
    simp only [diskRayComplex, ContinuousMap.coe_mk, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero, diskRayAngle_zero]
  have hmiss : halfPlaneDisk x ∉ range R.crosscut := by
    rw [R.boundary_hit_iff, hstart]
    exact hx k
  have hb := R.side_boundary (rayJordan_spec hsch γ hγ k) x hmiss
  change (if halfPlaneDisk x ∈ closure (jordanInterior (rayJordan hsch γ hγ k)) then false else true) = _ at hb
  rw [hstart] at hb
  by_cases hc : halfPlaneDisk x ∈ closure (jordanInterior (rayJordan hsch γ hγ k))
  · have hle : x ≤ circleRepresentative (normalizedArgument (γ 0)) + (k : ℝ) := by
      by_contra hn
      simp only [ite_eq_left hc, ite_eq_right hn] at hb
      cases hb
    exact iff_of_false (fun h => h hc) (by linarith)
  · have hlt : circleRepresentative (normalizedArgument (γ 0)) + (k : ℝ) < x := by
      by_contra hn
      have hle := le_of_not_gt hn
      simp only [ite_eq_right hc, ite_eq_left hle] at hb
      cases hb
    exact iff_of_true hc (by linarith)

theorem geometricRayIndex_boundary_floor (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (x : ℝ)
    (hx : ∀ k : ℤ, x ≠ circleRepresentative (normalizedArgument (γ 0)) + (k : ℝ)) :
    geometricRayIndex hsch γ hγ (x : ℂ) =
      ⌊x - circleRepresentative (normalizedArgument (γ 0))⌋ := by
  let a := circleRepresentative (normalizedArgument (γ 0))
  have hfloor : (⌊x - a⌋ : ℝ) < x - a := by
    apply lt_of_le_of_ne (Int.floor_le _)
    intro he
    exact hx ⌊x - a⌋ (by linarith)
  have hmem : ⌊x - a⌋ ∈ rayRightIndices hsch γ hγ (x : ℂ) :=
    (rayRightIndices_boundary_iff hsch γ hγ x hx _).mpr hfloor
  have hJ := geometricRayIndex_isGreatest hsch γ hγ (x : ℂ) (by simp)
  apply le_antisymm
  · apply Int.le_floor.mpr
    exact ((rayRightIndices_boundary_iff hsch γ hγ x hx _).mp hJ.1).le
  · exact hJ.2 hmem

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
-- module Solutions.Q146_CD.CircleDomains_Selection_RayIndexCrossings
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
-- module Solutions.Q146_CD.CircleDomains_Topology_MeanIndexBoundary
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mean index has the previously constructed positive
Stieltjes boundary coordinate for the actual starting-angle law. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem translatedHalfPlaneRay_start (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) :
    (translatedHalfPlaneRay γ hγ k).curve ⟨0, bot_lt_top⟩ =
      ((circleRepresentative (normalizedArgument (γ 0)) + (k : ℝ) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [translatedHalfPlaneRay, ContinuousMap.coe_mk, Complex.add_re,
      Complex.intCast_re, diskRayComplex, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, diskRayAngle_zero]
  · simpa only [Complex.ofReal_im] using (translatedHalfPlaneRay γ hγ k).start

 theorem geometricRayIndex_boundary_of_avoids (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (x : ℝ)
    (hx : diskRayProjection (x : ℂ) ∉ range γ) :
    geometricRayIndex hsch γ hγ (x : ℂ) =
      ⌊x - circleRepresentative (normalizedArgument (γ 0))⌋ := by
  apply geometricRayIndex_boundary_floor hsch γ hγ x
  intro k hk
  apply hx
  refine ⟨0, ?_⟩
  rw [hk, ← translatedHalfPlaneRay_start γ hγ k,
    diskRayProjection_translated]

 theorem measurable_compactArcStartingAngle (K : Set C(PathTime, ℂ)) :
    Measurable (fun γ : K => normalizedArgument (γ.val 0)) :=
  measurable_normalizedArgument.comp ((continuous_eval_const 0).comp continuous_subtype_val).measurable

 theorem meanGeometricIndex_boundary (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (x : ℝ)
    (hx : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (x : ℂ) ∉ range γ.val) :
    meanGeometricIndex hsch K hKS η ⟨(x : ℂ), by simp⟩ =
      boundaryIndexMean (compactArcStartingAngleLaw K η) x := by
  have he : (fun γ : K => (geometricRayIndex hsch γ.val (hKS γ.property) (x : ℂ) : ℝ)) =ᵐ[(η : Measure K)]
      fun γ => (⌊x - circleRepresentative (normalizedArgument (γ.val 0))⌋ : ℝ) := by
    filter_upwards [hx] with γ hγ
    rw [geometricRayIndex_boundary_of_avoids hsch γ.val (hKS γ.property) x hγ]
  rw [meanGeometricIndex, integral_congr_ae he]
  symm
  rw [boundaryIndexMean, compactArcStartingAngleLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_compactArcStartingAngle K).aemeasurable
      (measurable_boundaryIndex x).aestronglyMeasurable]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactArcBoundary
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On the unit boundary a terminal arc meets only its starting point.
Thus atomlessness of the starting law is exactly the needed point avoidance. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem diskTerminalArc_boundary_hit_iff
    {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet) {w : ℂ} (hw : ‖w‖ = 1) :
    w ∈ range γ ↔ γ 0 = w := by
  constructor
  · rintro ⟨t, ht⟩
    by_cases h0 : t = 0
    · simpa only [h0] using ht
    by_cases h1 : t = 1
    · rw [h1, hγ.2.2.1] at ht
      have hh := hw
      rw [← ht, norm_zero] at hh
      norm_num at hh
    · have hlt := hγ.2.2.2 t ⟨lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm h0),
        lt_of_le_of_ne (unitInterval.le_one t) h1⟩
      rw [ht, hw] at hlt
      exact (lt_irrefl _ hlt).elim
  · intro h
    exact ⟨0, h⟩

 theorem compactArc_boundary_avoidance
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)] (x : ℝ) :
    ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (x : ℂ) ∉ range γ.val := by
  have hnull : (η : Measure K) ((fun γ : K => normalizedArgument (γ.val 0)) ⁻¹'
      {(x : UnitAddCircle)}) = 0 := by
    rw [← ProbabilityMeasure.map_apply' η (measurable_compactArcStartingAngle K).aemeasurable
      (measurableSet_singleton (x : UnitAddCircle))]
    change (compactArcStartingAngleLaw K η : Measure UnitAddCircle) {(x : UnitAddCircle)} = 0
    exact measure_singleton _
  have ha : ∀ᵐ γ : K ∂(η : Measure K), normalizedArgument (γ.val 0) ≠ (x : UnitAddCircle) :=
    by
      apply ae_iff.mpr
      have hs : {γ : K | ¬ normalizedArgument (γ.val 0) ≠ (x : UnitAddCircle)} =
          ((fun γ : K => normalizedArgument (γ.val 0)) ⁻¹' {(x : UnitAddCircle)}) := by
        ext γ
        simp only [mem_ofPred_eq, not_not, mem_preimage, mem_singleton_iff]
      rw [hs]
      exact hnull
  filter_upwards [ha] with γ hγ hh
  have hw : ‖diskRayProjection (x : ℂ)‖ = 1 := by
    simp only [diskRayProjection_norm, Complex.ofReal_im, neg_zero, Real.exp_zero]
  have he := (diskTerminalArc_boundary_hit_iff (hKS γ.property) hw).mp hh
  apply hγ
  rw [he, diskRayProjection_argument, Complex.ofReal_re]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_StartingLawBoundaryGate
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The boundary starting law of the compact disk-arc family is the actual
pushed-forward law of the original arc starts. Gate inequalities and
atomlessness therefore pass to the mean construction without an extra
hypothesis about its boundary measure. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem compact_startingLaw_eq_centered
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val) :
    compactArcStartingAngleLaw K (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) =
      arcStartingAngleLaw (centeredArcLaw (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [compactArcStartingAngleLaw, arcStartingAngleLaw, centeredArcLaw,
    ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_compactArcStartingAngle K) hf,
    Measure.map_map measurable_arcStartingAngle F.continuous_postcomp.measurable,
    Measure.map_map (measurable_arcStartingAngle.comp F.continuous_postcomp.measurable)
      measurable_subtype_coe]
  apply Measure.map_congr
  exact Eventually.of_forall (fun γ => by simp only [Function.comp_apply, hmap γ, ContinuousMap.comp_apply])

 theorem compact_startingLaw_atomless
    (J : ℂ ≃ₜ ℂ) {b : Sphere} (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate J b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J)))
    (f : A → K) (hf : Measurable f) (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior J),
      pathHitProbability (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) x = 0) :
    NullSingletonClass (compactArcStartingAngleLaw K (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) : Measure UnitAddCircle) := by
  rw [compact_startingLaw_eq_centered A K η F f hf hmap]
  apply centeredArcLaw_start_atomless J hb F hF (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) _ havoid
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff measurable_subtype_coe.aemeasurable (measurableSet_terminalArcSet _ (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)) b)).mpr
  exact Eventually.of_forall fun γ => hAS γ.property

local instance localInst_r5b9296_4 : BorelSpace Sphere := ⟨rfl⟩
omit [BorelSpace C(PathTime, Sphere)] in
 theorem compact_startingLaw_gate
    (J : ℂ ≃ₜ ℂ) {b : Sphere} (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate J b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J)))
    (f : A → K) (hf : Measurable f) (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (ψ : Sphere → ℝ) (hψ : Measurable ψ) (c : ℝ)
    (hgate : ∀ᵐ γ : A ∂(η : Measure A), c ≤ ψ (γ.val 0)) :
    ∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) : Measure UnitAddCircle),
      c ≤ ψ (centeredJordanBoundary J b θ) := by
  have hm : Measurable (fun θ => ψ (centeredJordanBoundary J b θ)) :=
    hψ.comp (continuous_centeredJordanBoundary J hb).measurable
  have hs := measurableSet_le (measurable_const (a := c)) hm
  rw [compactArcStartingAngleLaw, ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (measurable_compactArcStartingAngle K).aemeasurable hs).mpr
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff hf.aemeasurable (hs.preimage (measurable_compactArcStartingAngle K))).mpr
  filter_upwards [hgate] with γ hγ
  change c ≤ ψ (centeredJordanBoundary J b (normalizedArgument ((f γ).val 0)))
  rw [hmap γ, ContinuousMap.comp_apply]
  change c ≤ ψ (centeredJordanBoundary J b (normalizedArgument (F (γ.val ⊥))))
  rw [hF (frontier_subset_closure (hAS γ.property).2.1),
    centeredJordanBoundary_inverse J hb (hAS γ.property).2.1]
  exact hγ

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

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteCircleStokes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-region Stokes identity and area bound for the actual
intrinsic differential of a smooth circle coordinate. The only additional
published input is the precisely stated classical Green formula. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem circleFormIntegral_eq_real_lift
    {O : Set ℂ} (hO : IsOpen O) {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    (φ : ℂ → ℝ) (γ : ℝ → ℂ) (hγ : Differentiable ℝ γ) (hγO : ∀ t, γ t ∈ O)
    (v : ℝ → ℝ) (hv : Continuous v) (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t)) :
    circleFormIntegral φ u γ = ∫ t in (0 : ℝ)..1, φ (γ t) * deriv v t := by
  have hd (t : ℝ) : deriv v t = circleFDeriv u (γ t) (deriv γ t) := by
    have he : fderiv ℝ v t = circleFDeriv (u ∘ γ) t := by
      symm
      apply circleFDeriv_eq_lift
        ((hu.continuousOn.continuousAt (hO.mem_nhds (hγO t))).comp (hγ t).continuousAt)
        hv.continuousAt
      exact Eventually.of_forall hproj
    rw [← fderiv_apply_one_eq_deriv, he, circleFDeriv_comp hO hu (hγ t) (hγO t)]
    simp only [ContinuousLinearMap.comp_apply, fderiv_apply_one_eq_deriv]
  unfold circleFormIntegral planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _
  change (φ (γ t) * circleFDeriv u (γ t) 1) * (deriv γ t).re +
    (φ (γ t) * circleFDeriv u (γ t) Complex.I) * (deriv γ t).im =
    φ (γ t) * deriv v t
  conv_rhs => rw [hd t, complexCovector_apply]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CircuitReparametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Changing the starting point or direction of a periodic circuit preserves
its image and the absolute value of its one-form integral. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem periodic_eq_of_close {α : Type*} {f : ℝ → α}
    (hp : Function.Periodic f 1) (hi : InjOn f (Ico (0 : ℝ) 1))
    {x y : ℝ} (he : f x = f y) (hd : |x - y| < 1) : x = y := by
  have hx : f (Int.fract x) = f x := by
    simpa only [Int.fract, mul_one] using hp.sub_int_mul_eq (x := x) ⌊x⌋
  have hy : f (Int.fract y) = f y := by
    simpa only [Int.fract, mul_one] using hp.sub_int_mul_eq (x := y) ⌊y⌋
  have hh := hi ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
    ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩ (hx.trans (he.trans hy.symm))
  have hk : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) = x - y := by
    simp only [Int.fract, Int.cast_sub] at hh ⊢
    linarith
  have hb := abs_lt.mp hd
  have hklo : (-1 : ℤ) < ⌊x⌋ - ⌊y⌋ := by exact_mod_cast (show (-1 : ℝ) < ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) by rw [hk]; exact hb.1)
  have hkhi : ⌊x⌋ - ⌊y⌋ < (1 : ℤ) := by exact_mod_cast (show ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) < (1 : ℝ) by rw [hk]; exact hb.2)
  have hk0 : ⌊x⌋ - ⌊y⌋ = 0 := by omega
  rw [hk0, Int.cast_zero] at hk
  linarith

 theorem periodic_shift_injOn {α : Type*} {f : ℝ → α}
    (hp : Function.Periodic f 1) (hi : InjOn f (Ico (0 : ℝ) 1)) (a : ℝ) :
    InjOn (fun t => f (a + t)) (Ico (0 : ℝ) 1) := by
  intro x hx y hy he
  have hh := periodic_eq_of_close hp hi he (show |(a + x) - (a + y)| < 1 by
    apply abs_lt.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])
  linarith

 theorem periodic_shift {α : Type*} {f : ℝ → α}
    (hp : Function.Periodic f 1) (a : ℝ) :
    Function.Periodic (fun t => f (a + t)) 1 := by
  intro t
  simpa only [← add_assoc] using hp (a + t)

 theorem periodic_reverse {α : Type*} {f : ℝ → α}
    (hp : Function.Periodic f 1) : Function.Periodic (fun t => f (1 - t)) 1 := by
  intro t
  change f (1 - (t + 1)) = f (1 - t)
  rw [show 1 - (t + 1) = (1 - t) - 1 by ring]
  exact hp.sub_eq (1 - t)

 theorem deriv_periodic {f : ℝ → ℂ} (hp : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro t
  rw [← deriv_comp_add_const]
  exact congrArg (fun g : ℝ → ℂ => deriv g t) (funext hp)

 theorem planarFormIntegral_shift (P Q : ℂ → ℝ) {γ : ℝ → ℂ}
    (hp : Function.Periodic γ 1) (a : ℝ) :
    planarFormIntegral P Q (fun t => γ (a + t)) = planarFormIntegral P Q γ := by
  let f : ℝ → ℝ := fun t => P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im
  have hfp : Function.Periodic f 1 := by
    intro t
    simp only [f, hp t, deriv_periodic hp t]
  have hd (t : ℝ) : deriv (fun s => γ (a + s)) t = deriv γ (a + t) := by
    exact deriv_comp_const_add γ a t
  change (∫ t in (0 : ℝ)..1, _) = ∫ t in (0 : ℝ)..1, f t
  simp_rw [hd]
  change (∫ t in (0 : ℝ)..1, f (a + t)) = _
  rw [intervalIntegral.integral_comp_add_left]
  simpa only [add_zero, zero_add] using hfp.intervalIntegral_add_eq a 0

 theorem planarFormIntegral_reverse (P Q : ℂ → ℝ) {γ : ℝ → ℂ}
    (hγ : Differentiable ℝ γ) :
    planarFormIntegral P Q (fun t => γ (1 - t)) = -planarFormIntegral P Q γ := by
  have hd (t : ℝ) : deriv (fun s => γ (1 - s)) t = -deriv γ (1 - t) := by
    simpa only [Function.comp_def, neg_one_smul] using
      ((hγ (1 - t)).hasDerivAt.scomp t ((hasDerivAt_id t).const_sub 1)).deriv
  unfold planarFormIntegral
  simp_rw [hd, Complex.neg_re, Complex.neg_im, mul_neg, ← neg_add]
  rw [intervalIntegral.integral_neg]
  change -(∫ t in (0 : ℝ)..1, (fun s => P (γ s) * (deriv γ s).re +
    Q (γ s) * (deriv γ s).im) (1 - t)) = _
  exact congrArg Neg.neg (by
    simpa only [sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left
        (fun s : ℝ => P (γ s) * (deriv γ s).re + Q (γ s) * (deriv γ s).im)
        (a := 0) (b := 1) (1 : ℝ))

 theorem circleFormIntegral_shift (φ : ℂ → ℝ) (u : ℂ → UnitAddCircle)
    {γ : ℝ → ℂ} (hp : Function.Periodic γ 1) (a : ℝ) :
    circleFormIntegral φ u (fun t => γ (a + t)) = circleFormIntegral φ u γ :=
  planarFormIntegral_shift _ _ hp a

 theorem circleFormIntegral_reverse (φ : ℂ → ℝ) (u : ℂ → UnitAddCircle)
    {γ : ℝ → ℂ} (hγ : Differentiable ℝ γ) :
    circleFormIntegral φ u (fun t => γ (1 - t)) = -circleFormIntegral φ u γ :=
  planarFormIntegral_reverse _ _ hγ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryLiftOrder
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An embedded circle has a monotone or antitone normalized real boundary
lift, with one turn in absolute value. This fixes the orientation issue for
the physical collar without differentiating its topological disk chart. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem strictMonoOn_Icc_of_continuous_strictMonoOn_Ioo
    (q : ℝ → ℝ) (hq : Continuous q) (hm : StrictMonoOn q (Ioo (0 : ℝ) 1)) :
    StrictMonoOn q (Icc (0 : ℝ) 1) := by
  have h0 : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact ⟨zero_le_one, le_rfl⟩
  have hm0 := hm.monotoneOn.insert_of_continuousWithinAt
    (mem_closure_iff_clusterPt.mp h0) hq.continuousAt.continuousWithinAt
  have hm1 := hm0.insert_of_continuousWithinAt
    (mem_closure_iff_clusterPt.mp ((closure_mono (subset_insert 0 _)) h1))
    hq.continuousAt.continuousWithinAt
  have hs : insert (1 : ℝ) (insert 0 (Ioo (0 : ℝ) 1)) = Icc 0 1 := by
    ext x
    simp only [mem_insert_iff, mem_Ioo, mem_Icc]
    constructor
    · rintro (rfl | rfl | hx)
      · exact ⟨zero_le_one, le_rfl⟩
      · exact ⟨le_rfl, zero_le_one⟩
      · exact ⟨hx.1.le, hx.2.le⟩
    · intro hx
      by_cases h0x : x = 0
      · exact Or.inr (Or.inl h0x)
      by_cases h1x : x = 1
      · exact Or.inl h1x
      exact Or.inr (Or.inr ⟨lt_of_le_of_ne hx.1 (Ne.symm h0x), lt_of_le_of_ne hx.2 h1x⟩)
  rw [hs] at hm1
  intro x hx y hy hxy
  obtain ⟨a, hxa, hay⟩ := exists_between hxy
  obtain ⟨b, hab, hby⟩ := exists_between hay
  have ha : a ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hx.1 hxa, hay.trans_le hy.2⟩
  have hb : b ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans hab, hby.trans_le hy.2⟩
  exact (hm1 hx ⟨ha.1.le, ha.2.le⟩ hxa.le).trans_lt
    ((hm ha hb hab).trans_le (hm1 ⟨hb.1.le, hb.2.le⟩ hy hby.le))

 theorem positive_boundary_lift_one_turn
    (q : ℝ → ℝ) (hq : Continuous q) (hq0 : q 0 = 0)
    (hinj : InjOn (fun t => (q t : UnitAddCircle)) (Ico (0 : ℝ) 1))
    (hloop : (q 1 : UnitAddCircle) = (q 0 : UnitAddCircle)) (hpos : 0 < q 1) :
    q 1 = 1 := by
  obtain ⟨k, hk⟩ := (addCircle_eq_iff_exists_int 1 (q 1) (q 0)).mp hloop
  have hk' : q 1 = (k : ℝ) := by simpa only [hq0, zero_add, mul_one] using hk
  have hkpos : (0 : ℤ) < k := by exact_mod_cast (hk' ▸ hpos)
  have hle : (1 : ℝ) ≤ q 1 := by rw [hk']; exact_mod_cast (Int.add_one_le_iff.mpr hkpos)
  apply le_antisymm _ hle
  by_contra hn
  have hlt : 1 < q 1 := lt_of_not_ge hn
  obtain ⟨t, ht, hqt⟩ := intermediate_value_Icc zero_le_one hq.continuousOn
    (show (1 : ℝ) ∈ Icc (q 0) (q 1) by rw [hq0]; exact ⟨zero_le_one, hlt.le⟩)
  have ht0 : t ≠ 0 := by intro h; rw [h, hq0] at hqt; norm_num at hqt
  have ht1 : t ≠ 1 := by intro h; rw [h] at hqt; linarith
  have heq : (q t : UnitAddCircle) = (q 0 : UnitAddCircle) := by
    rw [hqt, hq0]
    exact (addCircle_eq_iff_exists_int 1 (1 : ℝ) 0).mpr ⟨1, by norm_num⟩
  exact ht0 (hinj ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩ ⟨le_rfl, zero_lt_one⟩ heq)

 theorem boundary_lift_order_and_period
    (q : ℝ → ℝ) (hq : Continuous q) (hq0 : q 0 = 0)
    (hinj : InjOn (fun t => (q t : UnitAddCircle)) (Ico (0 : ℝ) 1))
    (hloop : (q 1 : UnitAddCircle) = (q 0 : UnitAddCircle)) :
    (StrictMonoOn q (Icc (0 : ℝ) 1) ∧ q 1 = 1) ∨
      (StrictAntiOn q (Icc (0 : ℝ) 1) ∧ q 1 = -1) := by
  have hqi : InjOn q (Ioo (0 : ℝ) 1) := by
    intro x hx y hy heq
    exact hinj (Ioo_subset_Ico_self hx) (Ioo_subset_Ico_self hy) (congrArg (fun r : ℝ => (r : UnitAddCircle)) heq)
  rcases hq.continuousOn.strictMonoOn_of_injOn_Ioo zero_lt_one hqi with hm | ha
  · have hm' := strictMonoOn_Icc_of_continuous_strictMonoOn_Ioo q hq hm
    refine Or.inl ⟨hm', positive_boundary_lift_one_turn q hq hq0 hinj hloop ?_⟩
    simpa only [hq0] using hm' (left_mem_Icc.mpr zero_le_one)
      (right_mem_Icc.mpr zero_le_one) zero_lt_one
  · have hn : StrictMonoOn (fun t => -q t) (Ioo (0 : ℝ) 1) := by
      intro x hx y hy hxy
      exact neg_lt_neg (ha hx hy hxy)
    have hn' := strictMonoOn_Icc_of_continuous_strictMonoOn_Ioo _ hq.neg hn
    have hni : InjOn (fun t => ((-q t : ℝ) : UnitAddCircle)) (Ico (0 : ℝ) 1) := by
      intro x hx y hy heq
      apply hinj hx hy
      exact neg_injective (by simpa only [AddCircle.coe_neg] using heq)
    have hp : 0 < -q 1 := by
      have hh : -q 0 < -q 1 := hn' (left_mem_Icc.mpr zero_le_one)
        (right_mem_Icc.mpr zero_le_one) zero_lt_one
      simpa only [hq0, neg_zero] using hh
    have hperiod := positive_boundary_lift_one_turn (fun t => -q t) hq.neg
      (by simp only [hq0, neg_zero]) hni
      (by simpa only [AddCircle.coe_neg] using congrArg Neg.neg hloop) hp
    refine Or.inr ⟨?_, by linarith⟩
    intro x hx y hy hxy
    exact neg_lt_neg_iff.mp (hn' hx hy hxy)

 theorem exists_ordered_circle_boundary_lift
    (g : ℝ → UnitAddCircle) (hg : Continuous g) (hperiod : Function.Periodic g 1)
    (hg0 : g 0 = 0) (hinj : InjOn g (Ico (0 : ℝ) 1)) :
    ∃ q : ℝ → ℝ, Continuous q ∧ q 0 = 0 ∧ (∀ t, (q t : UnitAddCircle) = g t) ∧
      ((StrictMonoOn q (Icc (0 : ℝ) 1) ∧ q 1 = 1) ∨
        (StrictAntiOn q (Icc (0 : ℝ) 1) ∧ q 1 = -1)) := by
  let : ContractibleSpace (univ : Set ℝ) := convex_univ.contractibleSpace Set.univ_nonempty
  let : LocallyPathConnectedSpace (univ : Set ℝ) := isOpen_univ.locallyPathConnectedSpace
  obtain ⟨q, hq, hq0, hqp⟩ := exists_continuous_circle_lift g hg.continuousOn (mem_univ 0) 0
    (by simpa only [AddCircle.coe_zero] using hg0.symm)
  have hqp' : ∀ t, (q t : UnitAddCircle) = g t := fun t => hqp t (mem_univ t)
  have hqi : InjOn (fun t => (q t : UnitAddCircle)) (Ico (0 : ℝ) 1) := by
    intro x hx y hy heq
    apply hinj hx hy
    simpa only [hqp'] using heq
  refine ⟨q, continuousOn_univ.mp hq, hq0, hqp', ?_⟩
  apply boundary_lift_order_and_period q (continuousOn_univ.mp hq) hq0 hqi
  rw [hqp', hqp', hperiod.eq]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryOrderExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend the increasing boundary-angle parametrization of the unit
interval to an order isomorphism of the real line. Its outside values
are irrelevant to the boundary pairing. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

 theorem exists_boundary_orderIso
    (q : ℝ → ℝ) (hq : Continuous q) (hm : StrictMonoOn q (Icc (0 : ℝ) 1))
    (hq0 : q 0 = 0) (hq1 : q 1 = 1) :
    ∃ e : ℝ ≃o ℝ, e 0 = 0 ∧ e 1 = 1 ∧ EqOn e q (Icc (0 : ℝ) 1) := by
  classical
  let f : ℝ → ℝ := fun x => if x < 0 then x else if 1 < x then x else q x
  have hfx {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : f x = q x := by
    simp only [f, ite_eq_right (not_lt.mpr hx.1), ite_eq_right (not_lt.mpr hx.2)]
  have hb {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ q x ∧ q x ≤ 1 := by
    have h0 := hm.monotoneOn (left_mem_Icc.mpr zero_le_one) hx hx.1
    have h1 := hm.monotoneOn hx (right_mem_Icc.mpr zero_le_one) hx.2
    simpa only [hq0, hq1] using And.intro h0 h1
  have hf : StrictMono f := by
    intro x y hxy
    by_cases hx : x < 0
    · by_cases hy : y < 0
      · simpa only [f, ite_eq_left hx, ite_eq_left hy] using hxy
      · by_cases hy1 : 1 < y
        · simpa only [f, ite_eq_left hx, ite_eq_right hy, ite_eq_left hy1] using hxy
        · rw [show f x = x by simp only [f, ite_eq_left hx], hfx ⟨le_of_not_gt hy, le_of_not_gt hy1⟩]
          exact hx.trans_le (hb ⟨le_of_not_gt hy, le_of_not_gt hy1⟩).1
    · by_cases hx1 : 1 < x
      · have hy : ¬ y < 0 := by linarith
        have hy1 : 1 < y := hx1.trans hxy
        simpa only [f, ite_eq_right hx, ite_eq_left hx1, ite_eq_right hy, ite_eq_left hy1] using hxy
      · have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_gt hx, le_of_not_gt hx1⟩
        have hy : ¬ y < 0 := by linarith [hxI.1]
        by_cases hy1 : 1 < y
        · rw [hfx hxI, show f y = y by simp only [f, ite_eq_right hy, ite_eq_left hy1]]
          exact (hb hxI).2.trans_lt hy1
        · have hyI : y ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_gt hy, le_of_not_gt hy1⟩
          rw [hfx hxI, hfx hyI]
          exact hm hxI hyI hxy
  have hs : Surjective f := by
    intro y
    by_cases hy : y < 0
    · exact ⟨y, by simp only [f, ite_eq_left hy]⟩
    · by_cases hy1 : 1 < y
      · exact ⟨y, by simp only [f, ite_eq_right hy, ite_eq_left hy1]⟩
      · obtain ⟨x, hx, hqx⟩ := intermediate_value_Icc zero_le_one hq.continuousOn
          (show y ∈ Icc (q 0) (q 1) by rw [hq0, hq1]; exact ⟨le_of_not_gt hy, le_of_not_gt hy1⟩)
        exact ⟨x, (hfx hx).trans hqx⟩
  let e := hf.orderIsoOfSurjective f hs
  refine ⟨e, ?_, ?_, ?_⟩
  · change f 0 = 0
    rw [hfx (left_mem_Icc.mpr zero_le_one), hq0]
  · change f 1 = 1
    rw [hfx (right_mem_Icc.mpr zero_le_one), hq1]
  · exact fun x hx => hfx hx

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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularJordanCollar
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth inward collars for regular Jordan boundaries.

Published input: J. M. Lee, Introduction to Smooth Manifolds, second edition
(2013), Theorem 9.25, pp.222--223 (Collar Neighborhood Theorem), together with
its regular-domain interpretation in Proposition5.47, p.121. The formulation
below is the compact planar Jordan-boundary specialization: parametrize the
boundary circle (Milnor's compact one-manifold classification), take inward
collar slices, and use their bounded Jordan sides (planar Schoenflies).
It is a specialization/corollary, not a verbatim transcription of Theorem9.25.
The continuous-tangent clause retains the C¹ dependence of its smooth
collar embedding and is used only for the uniform boundary variation bound.
The regular-level hypothesis is retained explicitly.
https://thunv.wordpress.com/wp-content/uploads/2015/09/graduate-texts-in-mathematics-vol-218-john-m-lee-introduction-to-smooth-manifolds-springer-2013.pdf
DOI: 10.1007/978-1-4419-9982-5.
-/

open Set Function Filter Metric
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

 theorem WeightedCollar.exists_regular_inward_collar
    (hcollar : SmoothRegularJordanCollars)
    {G : Set Sphere} {π : Sphere → Sphere} {B : Set Sphere} {p : Sphere} {g : ℂ → ℝ≥0∞}
    (D : WeightedCollar G π B p g) : Nonempty (RegularJordanInwardCollar D.disk) :=
  hcollar D.disk D.function D.level D.smooth D.regular D.frontier_level

 theorem RegularJordanInwardCollar.uniform_approach
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) :
    ∀ ε > 0, ∃ η > 0, η ≤ C.width ∧ ∀ ρ ∈ Icc 0 η,
      ∀ t ∈ Icc (0 : ℝ) 1, dist (C.curve ρ t) (C.curve 0 t) < ε := by
  have hsub : Icc (0 : ℝ) C.width ×ˢ Icc (0 : ℝ) 1 ⊆ Icc 0 C.width ×ˢ (univ : Set ℝ) :=
    prod_mono Subset.rfl (subset_univ _)
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (C.continuous.mono hsub)
  intro ε hε
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let η := min C.width (d / 2)
  have hη : 0 < η := lt_min C.width_pos (half_pos hd)
  have hηw : η ≤ C.width := min_le_left _ _
  refine ⟨η, hη, hηw, ?_⟩
  intro ρ hρ t ht
  apply hdist (ρ, t) ⟨⟨hρ.1, hρ.2.trans hηw⟩, ht⟩
    (0, t) ⟨⟨le_rfl, C.width_pos.le⟩, ht⟩
  rw [Prod.dist_eq, dist_self, max_eq_left (show (0 : ℝ) ≤ dist ρ 0 from dist_nonneg),
    Real.dist_eq, sub_zero, abs_of_nonneg hρ.1]
  exact hρ.2.trans_lt ((min_le_right C.width (d / 2)).trans_lt (half_lt_self hd))

 theorem RegularJordanInwardCollar.eventually_in_boundary_neighborhood
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    {U : Set ℂ} (hU : IsOpen U) (hCU : frontier (jordanInterior H) ⊆ U) :
    ∃ η > 0, η ≤ C.width ∧ ∀ ρ ∈ Icc 0 η, ∀ t ∈ Icc (0 : ℝ) 1, C.curve ρ t ∈ U := by
  have hcompact := (isCompact_closure_jordanInterior H).of_isClosed_subset
    isClosed_frontier frontier_subset_closure
  obtain ⟨d, hd, hthick⟩ := hcompact.exists_cthickening_subset_open hU hCU
  obtain ⟨η, hη, hηw, hnear⟩ := C.uniform_approach d hd
  refine ⟨η, hη, hηw, ?_⟩
  intro ρ hρ t ht
  have hpar0 := C.parametrization 0 ⟨le_rfl, C.width_pos.le⟩
  have hzero : C.curve 0 t ∈ frontier (jordanInterior H) := by
    have hz : C.curve 0 t ∈ frontier (jordanInterior (C.disk 0)) :=
      hpar0.boundary ▸ mem_image_of_mem _ ht
    simpa only [C.disk_zero] using hz
  exact hthick (mem_cthickening_of_dist_le _ _ _ _ hzero (hnear ρ hρ t ht).le)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_InwardMaskSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select a genuine smooth inner mask while retaining a compact core,
remaining in a prescribed physical boundary neighborhood, and controlling
the parametrized displacement. The choices use a single collar. -/

open Set Function Filter Metric
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

 theorem RegularJordanInwardCollar.folded_continuous
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) :
    ContinuousOn (fun p : ℝ × ℝ => C.curve |p.1| p.2)
      (Ioo (-C.width) C.width ×ˢ univ) := by
  apply C.continuous.comp (continuous_fst.abs.prodMk continuous_snd).continuousOn
  intro p hp
  exact ⟨⟨abs_nonneg _, (abs_lt.mpr hp.1).le⟩, mem_univ _⟩

 theorem RegularJordanInwardCollar.select_inner
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    {K O : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ jordanInterior H)
    (hO : IsOpen O) (hboundary : frontier (jordanInterior H) ⊆ O)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ρ ≤ C.width ∧ K ⊆ jordanInterior (C.disk ρ) ∧
      closure (jordanInterior (C.disk ρ)) ⊆ jordanInterior H ∧
      frontier (jordanInterior (C.disk ρ)) ⊆ O ∧
      ∀ t ∈ Icc (0 : ℝ) 1, dist (C.curve ρ t) (C.curve 0 t) < ε := by
  obtain ⟨a, ha, haw, hcore⟩ := C.retains_compact K hK hKH
  obtain ⟨b, hb, hbw, hnear⟩ := C.eventually_in_boundary_neighborhood hO hboundary
  obtain ⟨c, hc, hcw, hmove⟩ := C.uniform_approach ε hε
  let ρ := min a (min b c) / 2
  have hρ : 0 < ρ := half_pos (lt_min ha (lt_min hb hc))
  have hρa : ρ ≤ a := (half_le_self (le_of_lt (lt_min ha (lt_min hb hc)))).trans (min_le_left _ _)
  have hρb : ρ ≤ b := (half_le_self (le_of_lt (lt_min ha (lt_min hb hc)))).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hρc : ρ ≤ c := (half_le_self (le_of_lt (lt_min ha (lt_min hb hc)))).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hρw : ρ ≤ C.width := hρa.trans haw
  refine ⟨ρ, hρ, hρw, hcore ρ ⟨hρ, hρa⟩, C.inward ρ ⟨hρ, hρw⟩, ?_,
    hmove ρ ⟨hρ.le, hρc⟩⟩
  intro z hz
  obtain ⟨t, ht, rfl⟩ := (C.parametrization ρ ⟨hρ.le, hρw⟩).boundary.symm ▸ hz
  exact hnear ρ ⟨hρ.le, hρb⟩ t ht

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
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryCollarLift
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize one logarithmic lift of a punctured-disk collar by its
boundary parametrization. Joint continuity then gives uniform convergence
to the boundary lift, not merely pointwise convergence of angles. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_boundary_normalized_logarithmic_lift
    {δ : ℝ} (hδ : 0 < δ) (w : ℝ × ℝ → ℂ)
    (hw : ContinuousOn w (Ioo (-δ) δ ×ˢ univ))
    (hw0 : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), w p ≠ 0)
    (hw1 : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), ‖w p‖ ≤ 1)
    (q : ℝ → ℝ) (hq : Continuous q) (hq0 : q 0 = 0)
    (hboundary : ∀ t, w (0, t) = diskRayProjection (q t : ℂ)) :
    ∃ L : ℝ × ℝ → ClosedUpperHalfPlane,
      ContinuousOn L (Ioo (-δ) δ ×ˢ univ) ∧
      (∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), diskRayProjection (L p).val = w p) ∧
      (∀ t, (L (0, t)).val = (q t : ℂ)) := by
  let D : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ univ
  have hzero : (0, 0) ∈ D := ⟨⟨by linarith, hδ⟩, mem_univ _⟩
  have hD : IsOpen D := isOpen_Ioo.prod isOpen_univ
  let : ContractibleSpace D :=
    ((convex_Ioo (-δ) δ).prod convex_univ).contractibleSpace ⟨_, hzero⟩
  let : LocallyPathConnectedSpace D := hD.locallyPathConnectedSpace
  have ha : ContinuousOn (normalizedArgument ∘ w) D := fun p hp =>
    (continuousAt_normalizedArgument (hw0 p hp)).comp_continuousWithinAt (hw p hp)
  obtain ⟨u, hu, hu0, hup⟩ := exists_continuous_circle_lift (normalizedArgument ∘ w) ha hzero 0 (by
    change (0 : UnitAddCircle) = normalizedArgument (w (0, 0))
    rw [hboundary, diskRayProjection_argument]
    simp only [Complex.ofReal_re, hq0, AddCircle.coe_zero])
  have huB : Continuous (fun t : ℝ => u (0, t)) :=
    hu.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨hzero.1, mem_univ _⟩)
  have hdiff := isLocallyConstant_real_lift_difference huB hq (fun t => by
    rw [hup (0, t) ⟨hzero.1, mem_univ _⟩]
    change normalizedArgument (w (0, t)) = (q t : UnitAddCircle)
    rw [hboundary, diskRayProjection_argument, Complex.ofReal_re])
  have huBq (t : ℝ) : u (0, t) = q t := by
    have he := hdiff.apply_eq_of_preconnectedSpace t 0
    rw [hu0, hq0] at he
    linarith
  let Ψ : ℝ × ℝ → ℂ := fun p => (u p : ℂ) + ((-Real.log ‖w p‖ : ℝ) : ℂ) * Complex.I
  have him (p) : (Ψ p).im = -Real.log ‖w p‖ := by simp [Ψ]
  have hre (p) : (Ψ p).re = u p := by simp [Ψ]
  have hc : ContinuousOn Ψ D :=
    (Complex.continuous_ofReal.comp_continuousOn hu).add
      ((Complex.continuous_ofReal.comp_continuousOn
        ((hw.norm.log (fun p hp => norm_ne_zero_iff.mpr (hw0 p hp))).neg)).mul_const _)
  have hn (p) (hp : p ∈ D) : 0 ≤ (Ψ p).im := by
    rw [him]
    exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hw1 p hp))
  let L : ℝ × ℝ → ClosedUpperHalfPlane := fun p => upperHalfPlaneClamp (Ψ p)
  have hLv (p) (hp : p ∈ D) : (L p).val = Ψ p := upperHalfPlaneClamp_val (hn p hp)
  refine ⟨L, continuous_upperHalfPlaneClamp.comp_continuousOn hc, ?_, ?_⟩
  · intro p hp
    rw [hLv p hp]
    apply Complex.ext_norm_arg
    · rw [diskRayProjection_norm, him, neg_neg,
        Real.exp_log (norm_pos_iff.mpr (hw0 p hp))]
    · apply Complex.arg_coe_angle_eq_iff.mp
      apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
      change normalizedArgument (diskRayProjection (Ψ p)) = normalizedArgument (w p)
      rw [diskRayProjection_argument, hre]
      exact hup p hp
  · intro t
    rw [hLv (0, t) ⟨hzero.1, mem_univ _⟩]
    apply Complex.ext
    · simpa only [Complex.ofReal_re, hre] using huBq t
    · rw [him, hboundary, diskRayProjection_norm]
      simp

 theorem uniform_collar_lift_approach
    {δ : ℝ} (hδ : 0 < δ) (L : ℝ × ℝ → ClosedUpperHalfPlane)
    (hL : ContinuousOn L (Ioo (-δ) δ ×ˢ univ))
    (q : ℝ → ℝ) (hboundary : ∀ t, (L (0, t)).val = (q t : ℂ)) :
    ∀ ε > 0, ∃ η > 0, η < δ ∧ ∀ ρ ∈ Ioo (-η) η,
      ∀ t ∈ Icc (0 : ℝ) 1, dist (L (ρ, t)).val (q t : ℂ) < ε := by
  let K : Set (ℝ × ℝ) := Icc (-δ / 2) (δ / 2) ×ˢ Icc 0 1
  have hKD : K ⊆ Ioo (-δ) δ ×ˢ (univ : Set ℝ) := by
    rintro ⟨ρ, t⟩ ⟨hρ, _⟩
    exact ⟨⟨by linarith [hρ.1], by linarith [hρ.2]⟩, mem_univ _⟩
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    ((continuous_subtype_val.comp_continuousOn hL).mono hKD)
  intro ε hε
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let η := min (δ / 4) (d / 2)
  have hη : 0 < η := lt_min (by linarith) (half_pos hd)
  refine ⟨η, hη, (min_le_left _ _).trans_lt (by linarith), ?_⟩
  intro ρ hρ t ht
  have hr : |ρ| < η := abs_lt.mpr hρ
  have hρK : (ρ, t) ∈ K := by
    refine ⟨⟨?_, ?_⟩, ht⟩ <;> dsimp only [η] at hr <;>
      have hh := min_le_left (δ / 4) (d / 2) <;> linarith [(abs_lt.mp hr).1, (abs_lt.mp hr).2]
  have h0K : (0, t) ∈ K := ⟨⟨by linarith, by linarith⟩, ht⟩
  have hp : dist (ρ, t) (0, t) < d := by
    rw [Prod.dist_eq, dist_self, max_eq_left (show (0 : ℝ) ≤ dist ρ 0 from dist_nonneg), Real.dist_eq, sub_zero]
    exact hr.trans_le ((show η ≤ d / 2 from min_le_right _ _).trans (by linarith))
  simpa only [Function.comp_apply, hboundary] using hdist (ρ, t) hρK (0, t) h0K hp

 theorem boundary_normalized_collar_lift_period
    {δ : ℝ} (hδ : 0 < δ) (w : ℝ × ℝ → ℂ)
    (L : ℝ × ℝ → ClosedUpperHalfPlane)
    (hL : ContinuousOn L (Ioo (-δ) δ ×ˢ univ))
    (hproj : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), diskRayProjection (L p).val = w p)
    (hloop : ∀ ρ ∈ Ioo (-δ) δ, w (ρ, 1) = w (ρ, 0))
    (q : ℝ → ℝ) (hq : q 1 = q 0 + 1)
    (hboundary : ∀ t, (L (0, t)).val = (q t : ℂ)) :
    ∀ ρ ∈ Ioo (-δ) δ, L (ρ, 1) = (L (ρ, 0)).translate 1 := by
  let A := Ioo (-δ) δ
  let : PreconnectedSpace A := Subtype.preconnectedSpace (convex_Ioo (-δ) δ).isPreconnected
  let u₁ : A → ℝ := fun ρ => (L (ρ, 1)).val.re
  let u₀ : A → ℝ := fun ρ => (L (ρ, 0)).val.re
  have hu₁ : Continuous u₁ := Complex.continuous_re.comp
    (continuous_subtype_val.comp (hL.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) (fun ρ => ⟨ρ.property, mem_univ _⟩)))
  have hu₀ : Continuous u₀ := Complex.continuous_re.comp
    (continuous_subtype_val.comp (hL.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) (fun ρ => ⟨ρ.property, mem_univ _⟩)))
  have hc := isLocallyConstant_real_lift_difference hu₁ hu₀ (fun ρ => by
    change ((L (ρ, 1)).val.re : UnitAddCircle) = ((L (ρ, 0)).val.re : UnitAddCircle)
    rw [← diskRayProjection_argument, ← diskRayProjection_argument,
      hproj (ρ, 1) ⟨ρ.property, mem_univ _⟩,
      hproj (ρ, 0) ⟨ρ.property, mem_univ _⟩, hloop ρ ρ.property])
  have hz : (0 : ℝ) ∈ A := ⟨by linarith, hδ⟩
  intro ρ hρ
  have hreal := hc.apply_eq_of_preconnectedSpace ⟨ρ, hρ⟩ ⟨0, hz⟩
  change (L (ρ, 1)).val.re - (L (ρ, 0)).val.re =
    (L (0, 1)).val.re - (L (0, 0)).val.re at hreal
  rw [hboundary, hboundary, Complex.ofReal_re, Complex.ofReal_re, hq] at hreal
  have hp : diskRayProjection (L (ρ, 1)).val = diskRayProjection (L (ρ, 0)).val := by
    rw [hproj (ρ, 1) ⟨hρ, mem_univ _⟩, hproj (ρ, 0) ⟨hρ, mem_univ _⟩, hloop ρ hρ]
  have him := congrArg norm hp
  rw [diskRayProjection_norm, diskRayProjection_norm] at him
  have him' := Real.exp_injective him
  apply Subtype.ext
  apply Complex.ext
  · change (L (ρ, 1)).val.re = ((L (ρ, 0)).val + (1 : ℤ)).re
    simp only [Int.cast_one, Complex.add_re, Complex.one_re]
    linarith
  · change (L (ρ, 1)).val.im = ((L (ρ, 0)).val + (1 : ℤ)).im
    simp only [Int.cast_one, Complex.add_im, Complex.one_im, add_zero]
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PhysicalCollarCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered Jordan coordinate on the constructed inward collar is a
jointly continuous punctured-disk family. Compact retention keeps the
singularity strictly on the inside of every small collar. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem RegularJordanInwardCollar.curve_mem_original_closure
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) {ρ : ℝ}
    (hρ : ρ ∈ Icc 0 C.width) (t : ℝ) : C.curve ρ t ∈ closure (jordanInterior H) := by
  have hm := frontier_subset_closure ((C.parametrization ρ hρ).mem_frontier t)
  by_cases hz : ρ = 0
  · subst ρ
    simpa only [C.disk_zero] using hm
  · exact subset_closure (C.inward ρ ⟨lt_of_le_of_ne hρ.1 (Ne.symm hz), hρ.2⟩ hm)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleArgumentOrder
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the argument of the actual centered collar boundary by its
first value. Its real lift runs once around the circle, in one of the two
orientations; no differentiability of the centered Jordan map is assumed. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem normalizedArgument_injective_on_unit_sphere {z w : ℂ}
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (h : normalizedArgument z = normalizedArgument w) : z = w := by
  apply Complex.ext_norm_arg
  · exact hz.trans hw.symm
  · apply Complex.arg_coe_angle_eq_iff.mp
    exact (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective h

 theorem normalizedArgument_div {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    normalizedArgument (z / w) = normalizedArgument z - normalizedArgument w := by
  let e : Real.Angle ≃+ UnitAddCircle :=
    AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
  change e (Complex.arg (z / w) : Real.Angle) = e (Complex.arg z) - e (Complex.arg w)
  rw [Complex.arg_div_coe_angle hz hw, e.map_sub]

 theorem exists_ordered_argument_lift
    (z : ℝ → ℂ) (hz : Continuous z) (hnorm : ∀ t, ‖z t‖ = 1)
    (hperiod : Function.Periodic z 1) (hinj : InjOn z (Ico (0 : ℝ) 1)) :
    ∃ q : ℝ → ℝ, Continuous q ∧ q 0 = 0 ∧
      (∀ t, (q t : UnitAddCircle) = normalizedArgument (z t / z 0)) ∧
      ((StrictMonoOn q (Icc (0 : ℝ) 1) ∧ q 1 = 1) ∨
        (StrictAntiOn q (Icc (0 : ℝ) 1) ∧ q 1 = -1)) := by
  have hne (t : ℝ) : z t ≠ 0 := by
    intro h
    have hn := hnorm t
    rw [h, norm_zero] at hn
    norm_num at hn
  let g : ℝ → UnitAddCircle := fun t => normalizedArgument (z t) - normalizedArgument (z 0)
  have hc : Continuous (fun t : ℝ => normalizedArgument (z t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_normalizedArgument (hne t)).comp hz.continuousAt
  have hcont : Continuous g := hc.sub continuous_const
  have hgperiod : Function.Periodic g 1 := fun t => by dsimp only [g]; rw [hperiod t]
  have hgi : InjOn g (Ico (0 : ℝ) 1) := by
    intro x hx y hy heq
    exact hinj hx hy (normalizedArgument_injective_on_unit_sphere (hnorm x) (hnorm y)
      (by simpa only [g, sub_left_inj] using heq))
  obtain ⟨q, hq, hq0, hqp, hord⟩ := exists_ordered_circle_boundary_lift g hcont hgperiod
    (sub_self _) hgi
  refine ⟨q, hq, hq0, ?_, hord⟩
  intro t
  exact (hqp t).trans (normalizedArgument_div (hne t) (hne 0)).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OrderedPhysicalCollar
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual centered Jordan boundary admits a smooth physical circuit
whose disk angle is increasing from zero to one. Only the starting point
and direction of the original regular circuit are changed. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem contDiff_orientedParameter (a : ℝ) (reverse : Bool) :
    ContDiff ℝ (⊤ : ℕ∞) (orientedParameter a reverse) := by
  cases reverse
  · exact contDiff_const.add contDiff_id
  · exact contDiff_const.add (contDiff_const.sub contDiff_id)

 theorem orientedCircuit_periodic {α : Type*} {γ : ℝ → α}
    (hp : Function.Periodic γ 1) (a : ℝ) (reverse : Bool) :
    Function.Periodic (γ ∘ orientedParameter a reverse) 1 := by
  cases reverse
  · exact periodic_shift hp a
  · exact periodic_reverse (periodic_shift hp a)

 theorem abs_circleFormIntegral_oriented
    (φ : ℂ → ℝ) (u : ℂ → UnitAddCircle) {γ : ℝ → ℂ}
    (hγ : Differentiable ℝ γ) (hp : Function.Periodic γ 1) (a : ℝ) (reverse : Bool) :
    |circleFormIntegral φ u (γ ∘ orientedParameter a reverse)| = |circleFormIntegral φ u γ| := by
  cases reverse
  · exact congrArg abs (circleFormIntegral_shift φ u hp a)
  · change |circleFormIntegral φ u (fun t => (fun s => γ (a + s)) (1 - t))| = _
    have hd : Differentiable ℝ (fun s : ℝ => γ (a + s)) := by
      apply hγ.comp
      exact (contDiff_const.add contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => a + s)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    rw [circleFormIntegral_reverse φ u hd, abs_neg, circleFormIntegral_shift φ u hp a]

 theorem exists_ordered_unit_circuit
    (γ : ℝ → ℂ) (hc : Continuous γ) (hn : ∀ t, ‖γ t‖ = 1)
    (hper : Function.Periodic γ 1) (hi : InjOn γ (Ico (0 : ℝ) 1))
    (hstart : ∃ a, γ a = 1) :
    ∃ (a : ℝ) (reverse : Bool) (q : ℝ → ℝ), Continuous q ∧ q 0 = 0 ∧ q 1 = 1 ∧
      StrictMonoOn q (Icc (0 : ℝ) 1) ∧
      ∀ t, γ (orientedParameter a reverse t) = diskRayProjection (q t : ℂ) := by
  obtain ⟨a, ha⟩ := hstart
  let z : ℝ → ℂ := fun t => γ (a + t)
  have hz : Continuous z := hc.comp (continuous_const.add continuous_id)
  have hz0 : z 0 = 1 := by simpa only [z, add_zero] using ha
  obtain ⟨q, hq, hq0, hproj, hord⟩ := exists_ordered_argument_lift z hz
    (fun t => hn (a + t)) (periodic_shift hper a) (periodic_shift_injOn hper hi a)
  have hp (t : ℝ) : z t = diskRayProjection (q t : ℂ) := by
    apply normalizedArgument_injective_on_unit_sphere (hn (a + t))
      (by rw [diskRayProjection_norm]; simp)
    rw [diskRayProjection_argument, Complex.ofReal_re, hproj t, hz0, div_one]
  rcases hord with ⟨hm, hq1⟩ | ⟨hm, hq1⟩
  · exact ⟨a, false, q, hq, hq0, hq1, hm, hp⟩
  · let r : ℝ → ℝ := fun t => q (1 - t) + 1
    have hr0 : r 0 = 0 := by simp only [r, sub_zero, hq1, neg_add_cancel]
    have hr1 : r 1 = 1 := by simp only [r, sub_self, hq0, zero_add]
    have hrm : StrictMonoOn r (Icc (0 : ℝ) 1) := by
      intro s hs t ht hst
      dsimp only [r]
      have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hs' : 1 - s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hh : q (1 - s) < q (1 - t) := hm ht' hs' (by linarith)
      exact add_lt_add_of_lt_of_le hh le_rfl
    refine ⟨a, true, r, (hq.comp (continuous_const.sub continuous_id)).add continuous_const,
      hr0, hr1, hrm, ?_⟩
    intro t
    change z (1 - t) = diskRayProjection (r t : ℂ)
    rw [hp]
    apply normalizedArgument_injective_on_unit_sphere
      (by rw [diskRayProjection_norm]; simp)
      (by rw [diskRayProjection_norm]; simp)
    rw [diskRayProjection_argument, diskRayProjection_argument, Complex.ofReal_re, Complex.ofReal_re]
    have hone : ((1 : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 1 0).mpr ⟨1, by norm_num⟩
    simp only [r, AddCircle.coe_add, hone, add_zero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OrderedCollarLift
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A jointly lifted physical collar, normalized at the boundary. All
fields below are constructed from the regular collar and its actual disk
coordinate; in particular, positive winding is not an input assumption. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_ordered_collar_lift_of_parameter
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) (F : C(Sphere, ℂ))
    (a : ℝ) (reverse : Bool) (q : ℝ → ℝ) (hq : Continuous q)
    (hq0 : q 0 = 0) (hq1 : q 1 = 1) (hqm : StrictMonoOn q (Icc (0 : ℝ) 1))
    (hqb : ∀ t, F (C.curve 0 (orientedParameter a reverse t) : Sphere) =
      diskRayProjection (q t : ℂ))
    (δ : ℝ) (hδ : 0 < δ) (hδw : δ ≤ C.width)
    (hw : ContinuousOn (fun p : ℝ × ℝ => F (C.curve |p.1| p.2 : Sphere))
      (Ioo (-δ) δ ×ˢ univ))
    (hw0 : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), F (C.curve |p.1| p.2 : Sphere) ≠ 0)
    (hw1 : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), ‖F (C.curve |p.1| p.2 : Sphere)‖ ≤ 1) :
    Nonempty (OrderedCollarLift C F) := by
  obtain ⟨e, he0, he1, heq⟩ := exists_boundary_orderIso q hq hqm hq0 hq1
  let w : ℝ × ℝ → ℂ := fun p => F (C.curve |p.1| (orientedParameter a reverse p.2) : Sphere)
  have hc : ContinuousOn w (Ioo (-δ) δ ×ˢ univ) := by
    apply hw.comp (continuous_fst.prodMk
      ((contDiff_orientedParameter a reverse).continuous.comp continuous_snd)).continuousOn
    intro p hp
    exact ⟨hp.1, mem_univ _⟩
  have hzero (p : ℝ × ℝ) (hp : p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ)) : w p ≠ 0 :=
    hw0 (p.1, orientedParameter a reverse p.2) ⟨hp.1, mem_univ _⟩
  have hnorm (p : ℝ × ℝ) (hp : p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ)) : ‖w p‖ ≤ 1 :=
    hw1 (p.1, orientedParameter a reverse p.2) ⟨hp.1, mem_univ _⟩
  have hboundary (t : ℝ) : w (0, t) = diskRayProjection (q t : ℂ) := by
    simpa only [w, abs_zero] using hqb t
  obtain ⟨L, hL, hp, hB⟩ := exists_boundary_normalized_logarithmic_lift hδ w hc hzero hnorm
    q hq hq0 hboundary
  have hloop (ρ : ℝ) (hρ : ρ ∈ Ioo (-δ) δ) : w (ρ, 1) = w (ρ, 0) := by
    have habs : |ρ| ∈ Icc 0 C.width := ⟨abs_nonneg _, (abs_lt.mpr hρ).le.trans hδw⟩
    exact congrArg (fun z : ℂ => F (z : Sphere))
      (orientedCircuit_periodic (C.parametrization |ρ| habs).periodic a reverse).eq
  have hperiod := boundary_normalized_collar_lift_period hδ w L hL hp hloop q
    (by rw [hq0, hq1]; norm_num) hB
  refine ⟨{
    start := a, reverse := reverse, width := δ, width_pos := hδ, width_le := hδw,
    angle := e, angle_zero := he0, angle_one := he1,
    lift := L, continuous := hL, projects := hp, period := hperiod,
    boundary := ?_, approach := ?_ }⟩
  · intro t ht
    rw [hB t, heq ht]
  · intro ε hε
    obtain ⟨η, hη, hηδ, hnear⟩ := uniform_collar_lift_approach hδ L hL q hB ε hε
    refine ⟨η, hη, hηδ, ?_⟩
    intro ρ hρ t ht
    rw [heq ht]
    exact hnear ρ hρ t ht

namespace OrderedCollarLift

 theorem circuit_smooth {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) {ρ : ℝ} (hρ : ρ ∈ Icc 0 C.width) :
    ContDiff ℝ (⊤ : ℕ∞) (D.circuit ρ) :=
  (C.parametrization ρ hρ).smooth.comp (contDiff_orientedParameter D.start D.reverse)

 theorem circuit_periodic {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) {ρ : ℝ} (hρ : ρ ∈ Icc 0 C.width) :
    Function.Periodic (D.circuit ρ) 1 :=
  orientedCircuit_periodic (C.parametrization ρ hρ).periodic D.start D.reverse

 theorem circuit_mem_frontier {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) {ρ : ℝ} (hρ : ρ ∈ Icc 0 C.width) (t : ℝ) :
    D.circuit ρ t ∈ frontier (jordanInterior (C.disk ρ)) :=
  (C.parametrization ρ hρ).mem_frontier _

 theorem abs_circleFormIntegral {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) {ρ : ℝ} (hρ : ρ ∈ Icc 0 C.width)
    (φ : ℂ → ℝ) (u : ℂ → UnitAddCircle) :
    |circleFormIntegral φ u (D.circuit ρ)| = |circleFormIntegral φ u (C.curve ρ)| :=
  abs_circleFormIntegral_oriented φ u ((C.parametrization ρ hρ).smooth.differentiable (by simp))
    (C.parametrization ρ hρ).periodic D.start D.reverse

 theorem continuous_slice {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) {ρ : ℝ} (hρ : ρ ∈ Ioo (-D.width) D.width) :
    Continuous (fun t : ℝ => D.lift (ρ, t)) :=
  D.continuous.comp_continuous (continuous_const.prodMk continuous_id)
    (fun _ => ⟨hρ, mem_univ _⟩)

 theorem inverse_angle_mem {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F) (θ : UnitAddCircle) :
    D.angle.symm (unitCircleCut θ) ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply D.angle.le_iff_le.mp
    simpa only [D.angle_zero, D.angle.apply_symm_apply] using (unitCircleCut_mem θ).1
  · apply D.angle.le_iff_le.mp
    simpa only [D.angle_one, D.angle.apply_symm_apply] using (unitCircleCut_mem θ).2.le

end OrderedCollarLift
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PuncturedPhysicalCollar
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Punctured disk collars for a continuous physical coordinate, including
coordinates pulled back through the component quotient. Boundary avoidance
suffices: compactness supplies one common inward width. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem exists_punctured_physical_collar
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) (F : C(Sphere, ℂ))
    (hbound : ∀ z ∈ closure (jordanInterior H), ‖F (z : Sphere)‖ ≤ 1)
    (hboundary : ∀ z ∈ frontier (jordanInterior H), F (z : Sphere) ≠ 0) :
    ∃ η > 0, η ≤ C.width ∧
      ContinuousOn (fun p : ℝ × ℝ => F (C.curve |p.1| p.2 : Sphere))
        (Ioo (-η) η ×ˢ univ) ∧
      (∀ p ∈ Ioo (-η) η ×ˢ (univ : Set ℝ), F (C.curve |p.1| p.2 : Sphere) ≠ 0) ∧
      (∀ p ∈ Ioo (-η) η ×ˢ (univ : Set ℝ), ‖F (C.curve |p.1| p.2 : Sphere)‖ ≤ 1) := by
  let O : Set ℂ := {z | F (z : Sphere) ≠ 0}
  have hO : IsOpen O := isOpen_compl_singleton.preimage (F.continuous.comp OnePoint.continuous_coe)
  obtain ⟨η, hη, hηw, hnear⟩ := C.eventually_in_boundary_neighborhood hO hboundary
  have habs {ρ : ℝ} (hρ : ρ ∈ Ioo (-η) η) : |ρ| ∈ Icc 0 C.width :=
    ⟨abs_nonneg _, (abs_lt.mpr hρ).le.trans hηw⟩
  refine ⟨η, hη, hηw, ?_, ?_, ?_⟩
  · apply (F.continuous.comp OnePoint.continuous_coe).comp_continuousOn
    apply C.folded_continuous.mono
    intro p hp
    exact ⟨⟨lt_of_le_of_lt (neg_le_neg hηw) hp.1.1, hp.1.2.trans_le hηw⟩, hp.2⟩
  · intro p hp
    have hi : |p.1| ∈ Icc (0 : ℝ) η := ⟨abs_nonneg _, (abs_lt.mpr hp.1).le⟩
    have hγ := C.parametrization |p.1| (habs hp.1)
    have he : C.curve |p.1| (Int.fract p.2) = C.curve |p.1| p.2 := by
      simpa only [Int.fract, mul_one] using hγ.periodic.sub_int_mul_eq (x := p.2) ⌊p.2⌋
    have hh := hnear |p.1| hi (Int.fract p.2) ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    change F (C.curve |p.1| (Int.fract p.2) : Sphere) ≠ 0 at hh
    rwa [he] at hh
  · intro p hp
    exact hbound _ (C.curve_mem_original_closure (habs hp.1) p.2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientOrderedCollar
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered collar construction for the actual component quotient.
The physical collar stays smooth although the quotient Jordan coordinate
need only be continuous. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem frontier_quotient_jordan_collar
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H J : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G)
    (hregion : π '' (((↑) : ℂ → Sphere) '' jordanInterior H) =
      ((↑) : ℂ → Sphere) '' jordanInterior J) :
    frontier (((↑) : ℂ → Sphere) '' jordanInterior J) =
      π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) := by
  rw [← hregion]
  rw [frontier_image_of_saturated_open π hπ
    (((↑) : ℂ → Sphere) '' jordanInterior H)
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H))
    (isOpen_image_jordanInterior_of_component_collapse G π hπ hclosed hsurj hr H hboundary)
    (hclosed _ isClosed_closure)
    (preimage_image_jordanInterior_of_component_collapse G π hsurj hr H hboundary),
    frontier_sphere_image_jordanInterior]

 theorem exists_quotient_ordered_collar_lift
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H J : ℂ ≃ₜ ℂ) (C : RegularJordanInwardCollar H)
    (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G)
    (hregion : π '' (((↑) : ℂ → Sphere) '' jordanInterior H) =
      ((↑) : ℂ → Sphere) '' jordanInterior J)
    {b : Sphere} (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate J b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J))) :
    Nonempty (OrderedCollarLift C (F.comp ⟨π, hπ⟩)) := by
  let P : C(Sphere, ℂ) := F.comp ⟨π, hπ⟩
  have hfront := frontier_quotient_jordan_collar G π hπ hclosed hsurj hr H J hboundary hregion
  have hcl (z : ℂ) (hz : z ∈ closure (jordanInterior H)) :
      π (z : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' jordanInterior J) := by
    rw [← hregion]
    apply image_closure_subset_closure_image hπ
    refine ⟨(z : Sphere), ?_, rfl⟩
    rw [closure_sphere_image_jordanInterior]
    exact ⟨z, hz, rfl⟩
  have hf (z : ℂ) (hz : z ∈ frontier (jordanInterior H)) :
      π (z : Sphere) ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior J) := by
    rw [hfront]
    exact ⟨(z : Sphere), ⟨z, hz, rfl⟩, rfl⟩
  have hn (z : ℂ) (hz : z ∈ closure (jordanInterior H)) : ‖P (z : Sphere)‖ ≤ 1 := by
    change ‖F (π (z : Sphere))‖ ≤ 1
    rw [hF (hcl z hz)]
    exact centeredJordanCoordinate_norm_le J hb (hcl z hz)
  have hbn (z : ℂ) (hz : z ∈ frontier (jordanInterior H)) : ‖P (z : Sphere)‖ = 1 := by
    change ‖F (π (z : Sphere))‖ = 1
    rw [hF (frontier_subset_closure (hf z hz))]
    exact centeredJordanCoordinate_norm_boundary J hb (hf z hz)
  have hb0 (z : ℂ) (hz : z ∈ frontier (jordanInterior H)) : P (z : Sphere) ≠ 0 := by
    intro he
    have hh := hbn z hz
    rw [he, norm_zero] at hh
    norm_num at hh
  have hpar := C.parametrization 0 ⟨le_rfl, C.width_pos.le⟩
  have hparfront (t : ℝ) : C.curve 0 t ∈ frontier (jordanInterior H) := by
    simpa only [C.disk_zero] using hpar.mem_frontier t
  have hnorm (t : ℝ) : ‖P (C.curve 0 t : Sphere)‖ = 1 := hbn _ (hparfront t)
  have hi : InjOn (fun t => P (C.curve 0 t : Sphere)) (Ico (0 : ℝ) 1) := by
    intro s hs t ht he
    have hp : π (C.curve 0 s : Sphere) = π (C.curve 0 t : Sphere) := by
      apply centeredJordanCoordinate_injOn J hb
        (frontier_subset_closure (hf _ (hparfront s)))
        (frontier_subset_closure (hf _ (hparfront t)))
      change F (π (C.curve 0 s : Sphere)) = F (π (C.curve 0 t : Sphere)) at he
      rwa [hF (frontier_subset_closure (hf _ (hparfront s))),
        hF (frontier_subset_closure (hf _ (hparfront t)))] at he
    rcases (hr _ _).mp hp with h | h
    · exact hpar.injective hs ht (OnePoint.coe_injective h)
    · exact (h.1 (hboundary _ (hparfront s))).elim
  have hstart : ∃ a, P (C.curve 0 a : Sphere) = 1 := by
    have hx := centeredJordanBoundary_mem_frontier J hb (0 : UnitAddCircle)
    rw [hfront] at hx
    obtain ⟨_, ⟨z, hz, rfl⟩, he⟩ := hx
    have hzb : z ∈ C.curve 0 '' Icc (0 : ℝ) 1 := by
      have hh : C.curve 0 '' Icc (0 : ℝ) 1 = frontier (jordanInterior H) := by
        simpa only [C.disk_zero] using hpar.boundary
      rw [hh]
      exact hz
    obtain ⟨a, _ha, hca⟩ := hzb
    refine ⟨a, ?_⟩
    change F (π (C.curve 0 a : Sphere)) = 1
    rw [hca, hF (frontier_subset_closure (hf z hz)), he,
      centeredJordanCoordinate_boundary J hb, standardCirclePoint_zero]
  obtain ⟨a, reverse, q, hq, hq0, hq1, hqm, hqb⟩ := exists_ordered_unit_circuit
    (fun t => P (C.curve 0 t : Sphere))
    (P.continuous.comp (OnePoint.continuous_coe.comp hpar.smooth.continuous))
    hnorm (hpar.periodic.comp (fun z : ℂ => P (z : Sphere))) hi hstart
  obtain ⟨δ, hδ, hδw, hw, hw0, hw1⟩ := exists_punctured_physical_collar C P hn hb0
  exact exists_ordered_collar_lift_of_parameter C P a reverse q hq hq0 hq1 hqm hqb
    δ hδ hδw hw hw0 hw1

 theorem OrderedCollarLift.quotient_boundary_identification
    {π : Sphere → Sphere} (hπ : Continuous π)
    {H J : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C (F.comp ⟨π, hπ⟩))
    (hfront : frontier (((↑) : ℂ → Sphere) '' jordanInterior J) =
      π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)))
    {b : Sphere} (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (hF : EqOn F (centeredJordanCoordinate J b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J))) (θ : UnitAddCircle) :
    π (D.circuit 0 (D.angle.symm (unitCircleCut θ)) : Sphere) = centeredJordanBoundary J b θ := by
  let t := D.angle.symm (unitCircleCut θ)
  have ht := D.inverse_angle_mem θ
  have hz : π (D.circuit 0 t : Sphere) ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior J) := by
    rw [hfront]
    refine ⟨_, ⟨D.circuit 0 t, ?_, rfl⟩, rfl⟩
    simpa only [C.disk_zero] using D.circuit_mem_frontier ⟨le_rfl, C.width_pos.le⟩ t
  apply centeredJordanCoordinate_injOn J hb (frontier_subset_closure hz)
    (frontier_subset_closure (centeredJordanBoundary_mem_frontier J hb θ))
  rw [← hF (frontier_subset_closure hz), centeredJordanCoordinate_boundary J hb]
  have hp := D.projects (0, t) ⟨⟨by linarith [D.width_pos], D.width_pos⟩, mem_univ _⟩
  rw [D.boundary t ht] at hp
  simp only [abs_zero] at hp
  change diskRayProjection (D.angle t : ℂ) = F (π (D.circuit 0 t : Sphere)) at hp
  rw [← hp]
  simp only [diskRayProjection, Complex.ofReal_im, neg_zero, Real.exp_zero, Complex.ofReal_one,
    Complex.ofReal_re, one_mul, t, D.angle.apply_symm_apply, unitCircleCut, AddCircle.coe_equivIco]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PhysicalBoundaryGate
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original gate on physical arc starts gives the required lower
bound for the actual physical collar. The inverse quotient map is used
only on its homeomorphic domain. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
 theorem physicalValue_quotient {G U : Set Sphere} (e : G ≃ₜ U) (y₀ : Sphere)
    (π : Sphere → Sphere) (he : ∀ x : G, (e x).val = π x.val) {x : Sphere} (hx : x ∈ G) :
    physicalValue e y₀ (π x) = x := by
  have hp : π x ∈ U := (he ⟨x, hx⟩) ▸ (e ⟨x, hx⟩).property
  have hh : (⟨π x, hp⟩ : U) = e ⟨x, hx⟩ := Subtype.ext (he ⟨x, hx⟩).symm
  simp only [physicalValue, dite_eq_left hp, hh, e.symm_apply_apply]

local instance localInst_r5b9296_5 : BorelSpace Sphere := ⟨rfl⟩
omit [BorelSpace C(PathTime, Sphere)] in
 theorem compact_startingLaw_physical_gate
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ x : G, (e x).val = π x.val)
    {H J : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H}
    (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G)
    (hfront : frontier (((↑) : ℂ → Sphere) '' jordanInterior J) =
      π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)))
    {b : Sphere} (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate J b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J)))
    (D : OrderedCollarLift C (F.comp ⟨π, hπ⟩))
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b)
    (f : A → K) (hf : Measurable f) (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (Φ : ℂ → ℝ) (hΦ : Measurable Φ) (d : ℝ)
    (hgate : ∀ᵐ γ : A ∂(η : Measure A), d ≤ Φ (finiteCoord (physicalValue e y₀ (γ.val 0)))) :
    ∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) : Measure UnitAddCircle),
      d ≤ Φ (D.circuit 0 (D.angle.symm (unitCircleCut θ))) := by
  let ψ : Sphere → ℝ := fun x => Φ (finiteCoord (physicalValue e y₀ x))
  have hψ : Measurable ψ := hΦ.comp (measurable_finiteCoord.comp (measurable_physicalValue e hU y₀))
  have hg := compact_startingLaw_gate J hb A K η hAS F hF f hf hmap ψ hψ d hgate
  filter_upwards [hg] with θ hθ
  have hident := D.quotient_boundary_identification hπ hfront hb hF θ
  have hx : (D.circuit 0 (D.angle.symm (unitCircleCut θ)) : Sphere) ∈ G := by
    apply hboundary
    simpa only [C.disk_zero] using
      D.circuit_mem_frontier ⟨le_rfl, C.width_pos.le⟩ (D.angle.symm (unitCircleCut θ))
  change d ≤ Φ (finiteCoord (physicalValue e y₀ (centeredJordanBoundary J b θ))) at hθ
  rw [← hident, physicalValue_quotient e y₀ π he hx, finiteCoord_coe] at hθ
  exact hθ

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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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

local instance localInst_r5b9296_6 : BorelSpace Sphere := ⟨rfl⟩
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

local instance localInst_r5b9296_7 : BorelSpace Sphere := ⟨rfl⟩
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

local instance localInst_r5b9296_8 : BorelSpace Sphere := ⟨rfl⟩
theorem density_measurable : Measurable L.density := (Classical.choose_spec L.candidate.1.2).1

theorem occupation_eq : meanCodeOccupation L.data L.law = sphericalArea.withDensity L.density :=
  (Classical.choose_spec L.candidate.1.2).2.1

theorem density_energy_finite : (∫⁻ x, L.density x ^ 2 ∂sphericalArea) < ∞ :=
  (Classical.choose_spec L.candidate.1.2).2.2.trans_lt L.energy_finite

variable [BorelSpace C(PathTime, Sphere)]

theorem hit_square_finite : (∑' x : base.dust, codeHitProbability L.data L.law x.val ^ 2) < ∞ := by
  have h := (codeHit_square_tsum_le L.data L.law L.hitConstant L.finite_hit_tests).trans_lt
    ENNReal.ofReal_lt_top
  change (∑' x : L.data.dust, codeHitProbability L.data L.law x.val ^ 2) < ∞ at h
  rw [L.dust_eq] at h
  exact h

end RecursiveCodeLaw
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SupportedProbability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A probability measure supported on a measurable set is the pushforward
of an actual probability measure on that set. -/

open Set Filter MeasureTheory

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

 theorem supportedProbability_map (μ : ProbabilityMeasure X) (A : Set X)
    (hA : MeasurableSet A) (hmem : ∀ᵐ x ∂(μ : Measure X), x ∈ A) :
    (supportedProbability μ A hA hmem).map (f := Subtype.val) measurable_subtype_coe.aemeasurable = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  ext s hs
  rw [Measure.map_apply measurable_subtype_coe hs]
  change (μ : Measure X).comap Subtype.val (Subtype.val ⁻¹' s) = (μ : Measure X) s
  rw [(MeasurableEmbedding.subtype_coe hA).comap_apply]
  rw [image_preimage_eq_inter_range, Subtype.range_coe]
  apply measure_congr
  filter_upwards [hmem] with x hx
  show (x ∈ s ∩ A) = (x ∈ s)
  simp only [mem_inter_iff, and_iff_left hx]


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactArcIntersections
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical compact-arc construction simultaneously retains every
closed-set distinct-intersection estimate of the original endpoint law. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r5b9296_9 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_compact_physical_arc_law_with_selection
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ y : G, π y.val = (e y).val)
    (μ : ProbabilityMeasure C(PathTime, Sphere)) (V : Set Sphere) (hV : IsOpen V)
    (b : Sphere)
    (hμ : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V ∧ γ ⊤ = b ∧ physicalDomainLength e y₀ γ < ∞) :
    ∃ (K : Set C(PathTime, Sphere)) (η : ProbabilityMeasure C(PathTime, Sphere)),
      IsCompact K ∧
      (∀ α ∈ K, α ∈ terminalArcSet V b ∧ physicalDomainLength e y₀ α < ∞) ∧
      (∀ᵐ α ∂(η : Measure C(PathTime, Sphere)), α ∈ K) ∧
      (∀ x, pathHitProbability η x ≤ 2 * pathHitProbability μ x) ∧
      (∀ x ∉ closure V, pathHitProbability η x = 0) ∧
      meanPhysicalOccupation e y₀ η ≤
        (2 : ℝ≥0∞) • (meanPhysicalOccupation e y₀ μ).restrict (π ⁻¹' V) ∧
      (∀ H : Set Sphere, IsClosed H →
        (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, Sphere))) ≤
          2 * ∫⁻ γ, pathImageCount H γ ∂(μ : Measure C(PathTime, Sphere))) ∧
      IsSubarcLawReduction μ η := by
  obtain ⟨f, hfm, hf⟩ := exists_measurable_terminal_arc_selector hselect harcs μ V hV
  have hends : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      γ ⊥ ∉ V ∧ γ ⊤ ∈ V := hμ.mono fun _ h => ⟨h.1, h.2.1⟩
  have hgood : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      physicalDomainLength e y₀ γ < ∞ ∧ Injective (f γ) ∧ range (f γ) ⊆ range γ ∧
      ∀ t, (f γ) t ∉ V → (f γ) t = (f γ) ⊥ := by
    filter_upwards [hμ] with γ hγ
    obtain ⟨hi, h0, _, hs, _, _⟩ := terminal_arc_selector_properties hV hf γ hγ.1 hγ.2.1
    refine ⟨hγ.2.2.2, hi, ?_, ?_⟩
    · exact hs.trans (image_subset_range γ _)
    · intro t ht
      exact (lastEntryTail_outside γ V (hs (mem_range_self t)) ht).trans h0.symm
  have hfinite : ∀ᵐ α : C(PathTime, Sphere) ∂(μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, Sphere)),
      physicalDomainLength e y₀ α < ∞ := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff hfm (measurableSet_finitePhysicalDomainLength e hU y₀)).mpr
    filter_upwards [hgood] with γ hγ
    exact (simple_subarc_physical_length_le e hU y₀ ⟨γ, hγ.1⟩ (f γ) hγ.2.1 hγ.2.2.1).trans_lt hγ.1
  let S := terminalArcSet V b ∩ {α : C(PathTime, Sphere) | physicalDomainLength e y₀ α < ∞}
  have hS : MeasurableSet S := (measurableSet_terminalArcSet V hV b).inter
    (measurableSet_finitePhysicalDomainLength e hU y₀)
  have hall : ∀ᵐ α : C(PathTime, Sphere) ∂(μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, Sphere)), α ∈ S := by
    filter_upwards [terminalArcLaw_mem μ V hV b f hfm hf
      (hμ.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩), hfinite] with α hα hfα
    exact ⟨hα, hfα⟩
  have hmass : (μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, Sphere)) S = 1 := by
    rw [← measure_univ (μ := (μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, Sphere)))]
    exact measure_congr (Filter.eventuallyEq_univ.mpr hall)
  obtain ⟨K, hKS, hK, hhalf⟩ := hS.exists_lt_isCompact
    (show (1/2 : ℝ≥0∞) < (μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, Sphere)) S by rw [hmass]; norm_num)
  have hpos : (μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, Sphere)) K ≠ 0 :=
    ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1/2).trans hhalf)
  let η := restrictProbability (μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) K hpos
  have hηle : (η : Measure C(PathTime, Sphere)) ≤
      (2 : ℝ≥0∞) • (μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, Sphere)) :=
    restrictProbability_le_two (μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) K hhalf.le
  refine ⟨K, η, hK, hKS, restrictProbability_ae_mem (μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) K hpos hK.measurableSet, ?_, ?_, ?_, ?_,
    ⟨f, hfm, hgood.mono (fun _ h => h.2.2.1), hηle⟩⟩
  · intro x
    exact (hηle _).trans (mul_le_mul' le_rfl
      (terminalArcLaw_hit_le μ V hV f hfm hf hends x))
  · intro x hx
    apply le_antisymm ?_ bot_le
    have h := hηle {α | ∃ t : PathTime, α t = x}
    change pathHitProbability η x ≤ 2 * pathHitProbability (μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) x at h
    rw [terminalArcLaw_hit_eq_zero μ V hV f hfm hf hends hx, mul_zero] at h
    exact h
  · apply (meanPhysicalOccupation_mono e hU y₀ η (μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) 2 hηle).trans
    apply Measure.le_iff.mpr
    intro S hS
    simpa only [Measure.smul_apply, smul_eq_mul] using
      mul_le_mul' (le_refl (2 : ℝ≥0∞))
        ((meanPhysicalOccupation_map_collar_le e hU y₀ π hπ.measurable he
          μ f hfm V hV.measurableSet hgood) S)

  · intro H hH
    apply mean_subarc_intersections_le μ η f hfm _ hηle hH
    exact hgood.mono fun _ h => h.2.2.1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactReductionIntersections
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact simple-arc reduction for the actual endpoint code law, with
its pointwise density bound and all closed-set intersection bounds. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r5b9296_10 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_compact_arc_reduction_with_selection
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    (P : ProbabilityMeasure (BasePathCode d))
    (σ : Measure Sphere) [IsFiniteMeasure σ] (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanCodeOccupation d P = σ.withDensity g)
    (henergy : (∫⁻ x, g x ^ 2 ∂σ) < ∞)
    (V : Set Sphere) (hV : IsOpen V) (hanchor : Disjoint d.anchor V) (hb : d.target ∈ V) :
    ∃ (K : Set C(PathTime, Sphere)) (η : ProbabilityMeasure C(PathTime, Sphere))
      (gη : Sphere → ℝ≥0∞),
      IsCompact K ∧
      (∀ α ∈ K, α ∈ terminalArcSet V d.target ∧
        physicalDomainLength d.domainEquiv d.basePoint α < ∞) ∧
      (∀ᵐ α ∂(η : Measure C(PathTime, Sphere)), α ∈ K) ∧
      Measurable gη ∧ meanPhysicalOccupation d.domainEquiv d.basePoint η = σ.withDensity gη ∧
      (gη ≤ᵐ[σ] fun x => 2 * (π ⁻¹' V ∩ d.physicalDomain).indicator g x) ∧
      (∀ x, pathHitProbability η x ≤ 2 * pathHitProbability (codePathLaw d P) x) ∧
      (∀ x ∉ closure V, pathHitProbability η x = 0) ∧
      (∀ H : Set Sphere, IsClosed H →
        (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, Sphere))) ≤
          2 * ∫⁻ γ, pathImageCount H γ ∂(codePathLaw d P : Measure C(PathTime, Sphere))) ∧
      IsSubarcLawReduction (codePathLaw d P) η := by
  obtain ⟨K, η, hK, hKS, hη, hhit, hout, hbound, hcounts, hsel⟩ :=
    exists_compact_physical_arc_law_with_selection hselect harcs d.domainEquiv hU d.basePoint π hπ he
      (codePathLaw d P) V hV d.target (codePathLaw_collar_endpoints d hU P V hV hanchor hb)
  rw [meanPhysicalOccupation_codePathLaw d hU P, hocc] at hbound
  have hmem : ∀ᵐ x ∂σ.withDensity g, x ∈ d.physicalDomain := by
    rw [ae_iff]
    exact hocc ▸ meanCodeOccupation_compl d hU hG P
  have hset : (π ⁻¹' V ∩ d.physicalDomain : Set Sphere) =ᵐ[σ.withDensity g] (π ⁻¹' V : Set Sphere) := by
    filter_upwards [hmem] with x hx
    show (x ∈ π ⁻¹' V ∩ d.physicalDomain) = (x ∈ π ⁻¹' V)
    simp only [mem_inter_iff, and_iff_left hx]
  have hbound' : meanPhysicalOccupation d.domainEquiv d.basePoint η ≤
      (2 : ℝ≥0∞) • (σ.withDensity g).restrict (π ⁻¹' V ∩ d.physicalDomain) := by
    rwa [Measure.restrict_congr_set hset]
  obtain ⟨gη, hgη, hηg, hle⟩ := exists_localized_density_of_square_domination σ
    (meanPhysicalOccupation d.domainEquiv d.basePoint η) g hg henergy
    (π ⁻¹' V ∩ d.physicalDomain) ((hπ.measurable hV.measurableSet).inter hG.measurableSet) hbound'
  exact ⟨K, η, gη, hK, hKS, hη, hgη, hηg, hle, hhit, hout, hcounts, hsel⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallCompactArcReduction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every sufficiently deep prescribed collar supports the actual compact
simple-arc law with arbitrarily small density and punctured hit norms. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r5b9296_11 : BorelSpace Sphere := ⟨rfl⟩
theorem eventually_exists_small_compact_arc_law_with_selection
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    (P : ProbabilityMeasure (BasePathCode d))
    (σ : Measure Sphere) [IsFiniteMeasure σ] (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanCodeOccupation d P = σ.withDensity g)
    (henergy : (∫⁻ x, g x ^ 2 ∂σ) < ∞)
    (hb : d.target ∈ d.dust) (htarget : d.target ∉ d.quotientDomain)
    (hhit : (∑' s : d.dust, pathHitProbability (codePathLaw d P) s.val ^ 2) < ∞)
    (V : ℕ → Set Sphere) (hV : ∀ n, IsOpen (V n))
    (hanchor : ∀ n, Disjoint d.anchor (V n)) (hbV : ∀ n, d.target ∈ V n)
    (hanti : Antitone V) (hshrink : (⋂ n, closure (V n)) ⊆ {d.target})
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∃ (K : Set C(PathTime, Sphere)) (η : ProbabilityMeasure C(PathTime, Sphere))
        (gη : Sphere → ℝ≥0∞),
        IsCompact K ∧
        (∀ α ∈ K, α ∈ terminalArcSet (V n) d.target ∧
          physicalDomainLength d.domainEquiv d.basePoint α < ∞) ∧
        (∀ᵐ α ∂(η : Measure C(PathTime, Sphere)), α ∈ K) ∧
        Measurable gη ∧ meanPhysicalOccupation d.domainEquiv d.basePoint η = σ.withDensity gη ∧
        (gη ≤ᵐ[σ] fun x => 2 * (π ⁻¹' V n ∩ d.physicalDomain).indicator g x) ∧
        (∀ x, pathHitProbability η x ≤ 2 * pathHitProbability (codePathLaw d P) x) ∧
        (∀ x ∉ closure (V n), pathHitProbability η x = 0) ∧
        (∫⁻ x, gη x ^ 2 ∂σ) ^ (1 / 2 : ℝ) +
          countingSquareNorm (fun s : d.dust =>
            if s ≠ ⟨d.target, hb⟩ then pathHitProbability η s.val else 0) < ε ∧
        (∀ H : Set Sphere, IsClosed H →
          (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, Sphere))) ≤
            2 * ∫⁻ γ, pathImageCount H γ ∂(codePathLaw d P : Measure C(PathTime, Sphere))) ∧
        IsSubarcLawReduction (codePathLaw d P) η := by
  let A : ℕ → Set Sphere := fun n => π ⁻¹' V n ∩ d.physicalDomain
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (hπ.measurable (hV n).measurableSet).inter hG.measurableSet
  have hAa : Antitone A := fun i j hij x hx => ⟨hanti hij hx.1, hx.2⟩
  have hAi : (⋂ n, A n) ⊆ d.physicalDomainᶜ := by
    intro x hx hxG
    have hpx : π x = d.target := hshrink (mem_iInter.mpr fun n =>
      subset_closure (mem_iInter.mp hx n).1)
    have hu : π x ∈ d.quotientDomain := by
      rw [he ⟨x, hxG⟩]
      exact (d.domainEquiv ⟨x, hxG⟩).property
    exact htarget (hpx ▸ hu)
  have hE := tendsto_shrinking_occupation_energy d hU hG P σ g hg hocc henergy A hAm hAa hAi
  have hgNorm : Tendsto (fun n => (∫⁻ x in A n, g x ^ 2 ∂σ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
      (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hE
  let W : ℕ → Set d.dust := fun n => {s | s.val ∈ closure (V n)}
  have hWa : Antitone (fun n => closure (V n)) := fun i j hij => closure_mono (hanti hij)
  have hW : ∀ s : d.dust, s ≠ ⟨d.target, hb⟩ → ∀ᶠ n in atTop, s ∉ W n := by
    intro s hs
    exact eventually_outside_shrinking_set (fun n => closure (V n)) hWa d.target hshrink
      s.val (fun h => hs (Subtype.ext h))
  have hmNorm := tendsto_punctured_hit_norm_of_finite_tsum
    (fun s : d.dust => pathHitProbability (codePathLaw d P) s.val) hhit.ne
    ⟨d.target, hb⟩ W hW
  have hsum := (ENNReal.Tendsto.const_mul hgNorm (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ∞))).add
    (ENNReal.Tendsto.const_mul hmNorm (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ∞)))
  simp only [mul_zero, add_zero] at hsum
  filter_upwards [hsum.eventually (gt_mem_nhds hε)] with n hn
  obtain ⟨K, η, gη, hK, hKS, hη, hgm, hgmean, hgl, hhi, hho, hcounts, hsel⟩ :=
    exists_compact_arc_reduction_with_selection hselect harcs d hU hG π hπ he P σ g hg hocc henergy
      (V n) (hV n) (hanchor n) (hbV n)
  refine ⟨K, η, gη, hK, hKS, hη, hgm, hgmean, hgl, hhi, hho, ?_, hcounts, hsel⟩
  have hN : countingSquareNorm (fun s : d.dust =>
      if s ≠ ⟨d.target, hb⟩ then pathHitProbability η s.val else 0) ≤
      2 * countingSquareNorm (fun s : d.dust =>
        if s ∈ W n ∧ s ≠ ⟨d.target, hb⟩ then pathHitProbability (codePathLaw d P) s.val else 0) := by
    convert arc_hit_squareNorm_le _ _ ⟨d.target, hb⟩ (W n)
      (fun s => hhi s.val) (fun s hs => hho s.val hs) using 2 <;>
      (congr 1; funext s; split_ifs <;> rfl)
  apply lt_of_le_of_lt (add_le_add (arc_density_squareNorm_le σ g gη hg (A n) (hAm n) hgl) hN)
  convert hn using 2
  all_goals try with_reducible_and_instances rfl
  congr 2
  funext s
  split_ifs <;> rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SubarcGates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original endpoint law's prescribed closed gates survive measurable subarc
selection and compact conditioning. In particular the localized arc starts satisfy
the very same collar gate used by the positive-law construction. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

 theorem GateRule.of_range_subset {C K : Set X} {γ α : C(PathTime, X)}
    (hγ : GateRule C K γ) (hsub : range α ⊆ range γ) : GateRule C K α := by
  intro t ht
  obtain ⟨u, hu⟩ := hsub (mem_range_self t)
  rw [← hu] at ht ⊢
  exact hγ u ht

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

 theorem IsSubarcLawReduction.gates
    {μ ν : ProbabilityMeasure C(PathTime, X)} (hred : IsSubarcLawReduction μ ν)
    (C K : ℕ → Set X) (hC : ∀ n, IsClosed (C n)) (hK : ∀ n, IsClosed (K n))
    (hμ : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), GateRules C K γ) :
    ∀ᵐ γ ∂(ν : Measure C(PathTime, X)), GateRules C K γ := by
  obtain ⟨f, hf, hs, hν⟩ := hred
  have hsel : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), GateRules C K (f γ) := by
    filter_upwards [hμ, hs] with γ hγ hsub
    exact fun n => (hγ n).of_range_subset hsub
  have hmap : ∀ᵐ γ ∂(μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, X)), GateRules C K γ := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact (ae_map_iff hf (measurableSet_gateRules hC hK)).mpr hsel
  exact (Measure.absolutelyContinuous_of_le_smul hν).ae_le hmap

attribute [local instance] sphereMetric sphereBorel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RecursiveCompactReduction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The recursive positive law gives an actual compactly supported terminal-arc law at
sufficiently deep collars. Its physical density and punctured hit norm are arbitrarily
small, and the original prescribed gates survive the reduction. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r5b9296_12 : BorelSpace Sphere := ⟨rfl⟩
theorem RecursiveCodeLaw.eventually_compact_reduction
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    (L : RecursiveCodeLaw base π Flags ω)
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hU : IsOpen base.quotientDomain) (hG : IsOpen base.physicalDomain)
    (hπ : Continuous π) (hdisj : Disjoint base.quotientDomain base.dust)
    (V : ℕ → Set Sphere) (hV : ∀ n, IsOpen (V n))
    (hanchor : ∀ n, Disjoint base.anchor (V n)) (hbV : ∀ n, L.data.target ∈ V n)
    (hanti : Antitone V) (hshrink : (⋂ n, closure (V n)) ⊆ {L.data.target})
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n in atTop, Nonempty (CompactRecursiveReduction L (V n) ε) := by
  have hb : L.data.target ∈ L.data.dust := L.dust_eq.symm ▸ L.target_dust
  have hout : L.data.target ∉ L.data.quotientDomain := by
    intro h
    exact disjoint_left.mp hdisj (L.quotient_eq ▸ h) L.target_dust
  have hhit : (∑' s : L.data.dust, pathHitProbability (codePathLaw L.data L.law) s.val ^ 2) < ∞ := by
    rw [L.dust_eq]
    simpa only [pathHitProbability_codePathLaw] using L.hit_square_finite
  filter_upwards [eventually_exists_small_compact_arc_law_with_selection hselect harcs L.data
    (L.quotient_eq.symm ▸ hU) (L.physical_eq.symm ▸ hG) π hπ
    (fun y => (L.domain_agrees y).symm) L.law sphericalArea L.density L.density_measurable
    L.occupation_eq L.density_energy_finite hb hout hhit V hV
    (fun n => L.anchor_eq.symm ▸ hanchor n) hbV hanti hshrink hε] with n hn
  obtain ⟨K, ν, g, hK, hterminal, hν, hg, hocc, _, hhitν, houtν, hsmall, _, hred⟩ := hn
  let η := supportedProbability ν K hK.measurableSet hν
  have hη : η.map (f := Subtype.val) measurable_subtype_coe.aemeasurable = ν := supportedProbability_map ν K hK.measurableSet hν
  refine ⟨{
    arcs := K
    compact := hK
    terminal := fun _ h => (hterminal _ h).1
    finite_length := fun _ h => (hterminal _ h).2
    law := η
    density := g
    density_measurable := hg
    occupation := by rw [hη]; exact hocc
    hit_le := by rw [hη]; exact hhitν
    outside := by rw [hη]; exact houtν
    small := ?_
    reduction := by rw [hη]; exact hred }⟩
  rw [hη]
  convert hsmall using 2
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext s
  have hs : s ≠ (⟨L.data.target, hb⟩ : L.data.dust) ↔ s.val ≠ L.data.target := by
    simp only [ne_eq, Subtype.ext_iff]
  simp only [hs]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RecursiveReductionBounds
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact recursive law supplies the quantitative hypotheses used by the mean
construction: finite physical energy, square-summable actual hit weights, and the lower
bound imposed by its original physical collar gate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

namespace CompactRecursiveReduction
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
  {L : RecursiveCodeLaw base π Flags ω} {V : Set Sphere} {ε : ℝ≥0∞}
  (Q : CompactRecursiveReduction L V ε)

 theorem hit_probability (x : Sphere) :
    pathHitProbability (Q.law.map (f := Subtype.val) measurable_subtype_coe.aemeasurable) x =
      (Q.law : Measure Q.arcs) {γ | x ∈ range γ.val} := by
  rw [pathHitProbability, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply measurable_subtype_coe (isClosed_paths_hitting x).measurableSet]
  rfl

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem density_energy_finite :
    (∫⁻ x, Q.density x ^ 2 ∂sphericalArea) < ∞ := by
  apply (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp
  exact ((le_add_right le_rfl).trans_lt Q.small).trans_le le_top

 theorem hit_square_summable :
    Summable (fun s : L.data.dust => ((Q.law : Measure Q.arcs).real {γ | s.val ∈ range γ.val}) ^ 2) := by
  have hr (x : Sphere) : pathHitReal (Q.law.map (f := Subtype.val) measurable_subtype_coe.aemeasurable) x ≤
      2 * pathHitReal (codePathLaw L.data L.law) x := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by norm_num) (ne_top_of_le_ne_top (by norm_num)
        (pathHitProbability_le_one (codePathLaw L.data L.law) x))) (Q.hit_le x)
    simpa only [pathHitReal, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h
  have ht : Summable (fun s : L.data.dust => pathHitReal (Q.law.map (f := Subtype.val) measurable_subtype_coe.aemeasurable) s.val ^ 2) := by
    apply summable_of_sum_le (fun _ => sq_nonneg _) (c := (2 * L.hitConstant) ^ 2)
    intro F
    calc
      _ ≤ ∑ s ∈ F, (2 * pathHitReal (codePathLaw L.data L.law) s.val) ^ 2 := by
        apply Finset.sum_le_sum
        intro s _
        exact pow_le_pow_left₀ (pathHitReal_nonneg _ _) (hr s.val) 2
      _ = 4 * ∑ s ∈ F, pathHitReal (codePathLaw L.data L.law) s.val ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ ≤ 4 * L.hitConstant ^ 2 := mul_le_mul_of_nonneg_left (L.finite_hit_tests F) (by norm_num)
      _ = _ := by ring
  exact ht.congr (fun s => congrArg (fun t : ℝ≥0∞ => t.toReal ^ 2) (Q.hit_probability s.val))

end CompactRecursiveReduction
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SubarcPointAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Point avoidance outside the original law's positive-hit set survives
the actual subarc selector and compact conditioning. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem IsSubarcLawReduction.avoids_point
    {μ ν : ProbabilityMeasure C(PathTime, Sphere)} (hred : IsSubarcLawReduction μ ν)
    {x : Sphere} (hx : pathHitProbability μ x = 0) :
    ∀ᵐ γ : C(PathTime, Sphere) ∂(ν : Measure C(PathTime, Sphere)), x ∉ range γ := by
  obtain ⟨f, hf, hs, hν⟩ := hred
  have hμ : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)), x ∉ range γ := by
    apply ae_iff.mpr
    simpa only [not_not, mem_range, pathHitProbability] using hx
  have hsel : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      x ∉ range (f γ) := by
    filter_upwards [hμ, hs] with γ hγ hsub
    exact fun hx => hγ (hsub hx)
  have hmap : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, Sphere)),
      x ∉ range γ := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff hf ?_).mpr hsel
    exact (isClosed_paths_hitting x).isOpen_compl.measurableSet
  exact (Measure.absolutelyContinuous_of_le_smul hν).ae_le hmap

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RecursiveReductionBase
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact recursive law in the original base presentation. The fallback
point and the equivalent restricted homeomorphism have no effect on physical costs. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
namespace CompactRecursiveReduction
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
  {L : RecursiveCodeLaw base π Flags ω} {V : Set Sphere} {ε : ℝ≥0∞}
  (Q : CompactRecursiveReduction L V ε)

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem base_finite_length
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val) :
    ∀ γ ∈ Q.arcs, physicalDomainLength base.domainEquiv base.basePoint γ < ∞ := by
  intro γ hγ
  rw [← physicalDomainLength_congr_projection L.data.domainEquiv base.domainEquiv
    L.physical_eq L.quotient_eq π L.domain_agrees he L.data.basePoint base.basePoint γ]
  exact Q.finite_length γ hγ

 local instance localInst_r5b9296_13 : BorelSpace Sphere := ⟨rfl⟩
omit [BorelSpace C(PathTime, Sphere)] in
 theorem base_occupation
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val) :
    meanPhysicalOccupation base.domainEquiv base.basePoint (Q.law.map (f := Subtype.val) measurable_subtype_coe.aemeasurable) =
      sphericalArea.withDensity Q.density := by
  rw [← meanPhysicalOccupation_congr_projection L.data.domainEquiv base.domainEquiv
    L.physical_eq L.quotient_eq π L.domain_agrees he L.data.basePoint base.basePoint]
  exact Q.occupation

 theorem base_hit_square_summable :
    Summable (fun s : base.dust => ((Q.law : Measure Q.arcs).real {γ | s.val ∈ range γ.val}) ^ 2) := by
  have h := Q.hit_square_summable
  rw [L.dust_eq] at h
  exact h

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem base_small :
    (∫⁻ x, Q.density x ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) +
      countingSquareNorm Q.baseHitWeight < ε := by
  have h := Q.small
  rw [L.dust_eq] at h
  exact h

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem baseHitWeight_square_finite : (∑' s, Q.baseHitWeight s ^ 2) < ∞ := by
  have h : countingSquareNorm Q.baseHitWeight < ∞ :=
    ((le_add_left le_rfl).trans_lt Q.base_small).trans_le le_top
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp h

 theorem baseHitWeight_le (s : base.dust) (hs : s.val ≠ L.data.target) :
    (Q.law : Measure Q.arcs) {γ | s.val ∈ range γ.val} ≤ Q.baseHitWeight s := by
  rw [baseHitWeight, ite_eq_left hs, Q.hit_probability]

 theorem avoids_domain
    (hU : IsOpen base.quotientDomain) (hG : IsOpen base.physicalDomain)
    (hdust : base.dust = base.quotientDomainᶜ)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (x : Sphere) (hx : x ∈ base.quotientDomain) (hxi : x ≠ π OnePoint.infty) :
    ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs), x ∉ range γ.val := by
  have hout : L.data.target ∉ L.data.quotientDomain := by
    rw [L.quotient_eq]
    have hb := L.target_dust
    rw [hdust] at hb
    exact hb
  have hz := codeHitProbability_zero_off_dust L.data
    (L.quotient_eq.symm ▸ hU) (L.physical_eq.symm ▸ hG)
    (by rw [L.dust_eq, L.quotient_eq, hdust, compl_compl])
    π hπ hclosed hsurj (L.physical_eq.symm ▸ hr) L.domain_agrees hout
    L.law L.density L.density_measurable L.occupation_eq L.density_energy_finite
    x (by rw [L.dust_eq, hdust, mem_compl_iff, not_not]; exact hx) hxi
  have havoid := Q.reduction.avoids_point (by rwa [pathHitProbability_codePathLaw])
  rw [ProbabilityMeasure.toMeasure_map] at havoid
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable havoid

end CompactRecursiveReduction
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RelativelyClosedGates
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
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

 theorem codePathLaw_gates_of_inter_closed (d : PathCodeData X X)
    (hC : ∀ n, IsClosed (d.gateContours n))
    (hCK : ∀ n, IsClosed (d.gateContours n ∩ d.gateSets n))
    (P : ProbabilityMeasure (BasePathCode d)) :
    ∀ᵐ γ ∂(codePathLaw d P : Measure C(PathTime, X)),
      GateRules d.gateContours d.gateSets γ := by
  change ∀ᵐ γ ∂(P.map (f := (codePath d)) (by first | (apply Measurable.aemeasurable; apply measurable_codePath <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, X)), _
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (measurable_codePath d).aemeasurable
    (measurableSet_gateRules_of_inter_closed hC hCK)).mpr
  exact Eventually.of_forall fun Γ => Γ.property.2.2

 theorem IsSubarcLawReduction.code_gates_of_inter_closed
    (d : PathCodeData X X) (P : ProbabilityMeasure (BasePathCode d))
    {ν : ProbabilityMeasure C(PathTime, X)} (hred : IsSubarcLawReduction (codePathLaw d P) ν)
    (hC : ∀ n, IsClosed (d.gateContours n))
    (hCK : ∀ n, IsClosed (d.gateContours n ∩ d.gateSets n)) :
    ∀ᵐ γ ∂(ν : Measure C(PathTime, X)), GateRules d.gateContours d.gateSets γ := by
  have hμ := codePathLaw_gates_of_inter_closed d hC hCK P
  have hμ' : ∀ᵐ γ ∂(codePathLaw d P : Measure C(PathTime, X)),
      GateRules d.gateContours (fun n => d.gateContours n ∩ d.gateSets n) γ := by
    filter_upwards [hμ] with γ hγ
    exact fun n => (gateRule_inter_contour γ).mpr (hγ n)
  filter_upwards [hred.gates _ _ hC hCK hμ'] with γ hγ
  exact fun n => (gateRule_inter_contour γ).mp (hγ n)

variable [BorelSpace X] [SecondCountableTopology X] [CompleteSpace X]

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
namespace CompactRecursiveReduction
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
  {L : RecursiveCodeLaw base π Flags ω} {V : Set Sphere} {ε : ℝ≥0∞}
  (Q : CompactRecursiveReduction L V ε)

 theorem start_gate_of_inter_closed
    (hC : ∀ n, IsClosed (L.data.gateContours n))
    (hCK : ∀ n, IsClosed (L.data.gateContours n ∩ L.data.gateSets n))
    (n : ℕ) (hfront : frontier V ⊆ L.data.gateContours n) :
    ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs), γ.val ⊥ ∈ L.data.gateSets n := by
  have hgate := Q.reduction.code_gates_of_inter_closed L.data L.law hC hCK
  rw [ProbabilityMeasure.toMeasure_map] at hgate
  filter_upwards [ae_of_ae_map measurable_subtype_coe.aemeasurable hgate] with γ hγ
  exact hγ n ⊥ (hfront (Q.terminal γ.property).2.1)

 theorem physical_start_distance_of_inter_closed
    (hC : ∀ n, IsClosed (L.data.gateContours n))
    (hCK : ∀ n, IsClosed (L.data.gateContours n ∩ L.data.gateSets n))
    (n : ℕ) (hfront : frontier V ⊆ L.data.gateContours n)
    (f : base.quotientDomain → Sphere) (W : Set Sphere)
    (hgate : L.data.gateSets n = Subtype.val '' (f ⁻¹' closure W))
    (F₀ : ℂ → ℂ)
    (hF : ∀ x : base.quotientDomain, f x ∈ closure W →
      f x = (F₀ (finiteCoord (physicalValue base.domainEquiv base.basePoint x.val)) : Sphere))
    (c : ℂ) (r : ℝ≥0) (δ : ℝ)
    (hgap : ∀ z : ℂ, (z : Sphere) ∈ closure W →
      δ ≤ Metric.infDist z (Metric.closedBall c (r : ℝ))) :
    ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs),
      δ ≤ Metric.infDist
        (F₀ (finiteCoord (physicalValue base.domainEquiv base.basePoint (γ.val 0))))
        (Metric.closedBall c (r : ℝ)) := by
  filter_upwards [Q.start_gate_of_inter_closed hC hCK n hfront] with γ hγ
  rw [hgate] at hγ
  obtain ⟨x, hx, hxeq⟩ := hγ
  apply hgap
  change f x ∈ closure W at hx
  have heq := hF x hx
  rw [heq, hxeq] at hx
  exact hx

end CompactRecursiveReduction
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_GatedQuotientMap
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
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

 theorem quotientNormalizedMap_finite_gate {G U : Set Sphere} (e : G ≃ₜ U) (F : ℂ → ℂ)
    (y₀ : Sphere) {W : Set Sphere} (hW : OnePoint.infty ∉ W) :
    ∀ x : U, quotientNormalizedMap e F x ∈ W →
      quotientNormalizedMap e F x =
        (F (finiteCoord (physicalValue e y₀ x.val)) : Sphere) := by
  intro x hx
  have hphys : physicalValue e y₀ x.val = (e.symm x).val := by
    simp only [physicalValue, dite_eq_left x.property]
  rw [hphys]
  change extendAtInfinity F (e.symm x).val = _
  cases hy : (e.symm x).val using OnePoint.rec with
  | infty =>
    apply (hW ?_).elim
    simpa only [quotientNormalizedMap, hy, extendAtInfinity_infty] using hx
  | coe z => simp only [extendAtInfinity_coe, finiteCoord_coe]

 theorem exists_uniform_infDist_gap {K : Set ℂ} (hK : IsCompact K) (hKn : K.Nonempty)
    {D : Set ℂ} (hD : IsClosed D) (hDn : D.Nonempty) (hKD : Disjoint K D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ ≤ infDist z D := by
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hKn (continuous_infDist_pt D).continuousOn
  exact ⟨infDist z D, (hD.notMem_iff_infDist_pos hDn).mp
    (fun hd => disjoint_left.mp hKD hz hd), hmin⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalizedSourceRepresentative
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A globally measurable representative of the actual normalized map,
with the same values and derivatives on the physical domain. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_normalized_source_representative
    {G : Set Sphere} (hG : IsOpen G) (F : ℂ → ℂ)
    (hF : IsConformalOn (extendAtInfinity F) G) :
    ∃ F₀ : ℂ → ℂ, Measurable F₀ ∧
      ContDiffOn ℝ (⊤ : ℕ∞) F₀ (((↑) : ℂ → Sphere) ⁻¹' G) ∧
      EqOn F₀ F (((↑) : ℂ → Sphere) ⁻¹' G) := by
  classical
  let D := ((↑) : ℂ → Sphere) ⁻¹' G
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) F D := by
    intro z hz
    have ha := analyticAt_finite_map_of_conformal hG hF hz
      (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    simp only [extendAtInfinity_coe, finiteCoord_coe] at ha
    exact (ha.contDiffAt.restrict_scalars ℝ).contDiffWithinAt
  let F₀ : ℂ → ℂ := D.piecewise F (fun _ => 0)
  have hEq : EqOn F₀ F D := fun z hz => piecewise_eq_of_mem D F (fun _ => 0) hz
  exact ⟨F₀, hs.continuousOn.measurable_piecewise continuousOn_const
    (hG.preimage OnePoint.continuous_coe).measurableSet,
    hs.congr hEq, hEq⟩

 theorem quotientNormalizedMap_eq_of_eqOn {G U : Set Sphere} (e : G ≃ₜ U)
    {F₀ F : ℂ → ℂ} (hEq : EqOn F₀ F (((↑) : ℂ → Sphere) ⁻¹' G)) :
    quotientNormalizedMap e F₀ = quotientNormalizedMap e F := by
  funext x
  unfold quotientNormalizedMap
  have hy : (e.symm x).val ∈ G := (e.symm x).property
  cases h : (e.symm x).val using OnePoint.rec with
  | infty => rfl
  | coe z =>
    simp only [extendAtInfinity_coe]
    have hz : z ∈ ((↑) : ℂ → Sphere) ⁻¹' G := by
      change (z : Sphere) ∈ G
      simpa only [h] using hy
    have hval : F₀ z = F z := hEq hz
    exact congrArg ((↑) : ℂ → Sphere) hval

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

 theorem dustSmoothingTolerance_le_half
    {X Y : Type*} [MetricSpace Y] (q : X → Y) (B : Set Y) (ε : ℝ) (x : X) :
    dustSmoothingTolerance q B ε x ≤ ε / 2 :=
  div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientLocalChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
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

theorem finiteCoord_lipschitz_quotient_neighborhood
    (π : Sphere → Sphere) (hπ : Continuous π) (G V : Set Sphere)
    (hinfty : π OnePoint.infty ∉ closure V) :
    ∃ L : ℝ≥0, LipschitzOnWith L finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V)) := by
  have hK : IsCompact (((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' closure V)) :=
    isCompact_finite_preimage (isClosed_closure.preimage hπ) hinfty
  obtain ⟨L, hL⟩ := finiteCoord_lipschitz_on_compact_chart hK
  refine ⟨L, hL.mono (image_mono ?_)⟩
  intro z hz
  exact subset_closure hz.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleFormBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual boundary terms for the finite-circle Stokes formula. Smoothness
and integrability of real lifts follow from the circle coordinate, rather
than being extra analytic hypotheses on each boundary. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem contDiff_real_lift_along
    {O : Set ℂ} {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O)
    {v : ℝ → ℝ} (hv : Continuous v) (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t)) :
    ContDiff ℝ (⊤ : ℕ∞) v := by
  apply contDiffOn_univ.mp
  apply contDiffOn_real_lift isOpen_univ _ hv.continuousOn (fun t _ => hproj t)
  intro t _ a ha
  exact (hu (γ t) (hγO t) a ha).comp t hγ.contDiffAt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundDiskDistance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distance weight in the Stokes estimate: it is smooth off
the closed round disk and equals the offset on a concentric circle. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem infDist_closedBall_of_dist_gt (c z : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hz : r < dist z c) :
    infDist z (closedBall c r) = dist z c - r := by
  have hd : 0 < dist z c := hr.trans_lt hz
  have hne : dist z c ≠ 0 := hd.ne'
  let a := r / dist z c
  let p := c + a • (z - c)
  have ha : 0 ≤ a := div_nonneg hr hd.le
  have ha1 : a ≤ 1 := (div_le_one hd).mpr hz.le
  have hp : p ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm]
    dsimp only [p]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    rw [← dist_eq_norm, div_mul_cancel₀ r hne]
  have hdist : dist z p = dist z c - r := by
    have heq : z - p = (1 - a) • (z - c) := by dsimp only [p]; module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ha1), ← dist_eq_norm]
    dsimp only [a]
    rw [sub_mul, one_mul, div_mul_cancel₀ r hne]
  apply le_antisymm
  · exact (infDist_le_dist_of_mem hp).trans_eq hdist
  · apply (le_infDist ⟨c, mem_closedBall_self hr⟩).mpr
    intro y hy
    have htri := dist_triangle z y c
    have hy' := mem_closedBall.mp hy
    linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundBoundaryStability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative persistence of the fixed-source boundary integral under
uniform changes of the map and center-radius changes of the target disk. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem infDist_closedBall_eq_max (c z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    infDist z (closedBall c r) = max (dist z c - r) 0 := by
  by_cases hz : dist z c ≤ r
  · rw [infDist_zero_of_mem (mem_closedBall.mpr hz), max_eq_right (sub_nonpos.mpr hz)]
  · rw [infDist_closedBall_of_dist_gt c z hr (lt_of_not_ge hz),
      max_eq_left (sub_nonneg.mpr (le_of_not_ge hz))]

 theorem round_disk_distance_change (c d z w : ℂ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |infDist z (closedBall c r) - infDist w (closedBall d s)| ≤
      dist z w + dist c d + |r - s| := by
  rw [infDist_closedBall_eq_max c z hr, infDist_closedBall_eq_max d w hs]
  calc
    _ ≤ max |(dist z c - r) - (dist w d - s)| |(0 : ℝ) - 0| :=
      abs_max_sub_max_le_max _ _ _ _
    _ = |(dist z c - dist w d) - (r - s)| := by
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      congr 1
      ring
    _ ≤ |dist z c - dist w d| + |r - s| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (dist z c - dist w d) (-(r - s))
    _ ≤ dist z w + dist c d + |r - s| := by
      exact add_le_add (by simpa only [Real.dist_eq] using dist_dist_dist_le z c w d) le_rfl

 theorem roundDiskBoundaryPairing_stability
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (c d : ℂ) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {e M : ℝ} (he : 0 ≤ e)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1, dist (f t) (g t) ≤ e)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, |deriv v t| ≤ M) :
    |roundDiskBoundaryPairing f c r v - roundDiskBoundaryPairing g d s v| ≤
      (e + dist c d + |r - s|) * M := by
  have hdv : Continuous (deriv v) := hv.continuous_deriv (by simp)
  have hfi : IntervalIntegrable (fun t => infDist (f t) (closedBall c r) * deriv v t) volume 0 1 := ((continuous_infDist_pt _).comp hf).mul hdv |>.intervalIntegrable 0 1
  have hgi : IntervalIntegrable (fun t => infDist (g t) (closedBall d s) * deriv v t) volume 0 1 := ((continuous_infDist_pt _).comp hg).mul hdv |>.intervalIntegrable 0 1
  unfold roundDiskBoundaryPairing
  rw [← intervalIntegral.integral_sub hfi hgi]
  have hb : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖infDist (f t) (closedBall c r) * deriv v t -
        infDist (g t) (closedBall d s) * deriv v t‖ ≤
      (e + dist c d + |r - s|) * M := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hweight := (round_disk_distance_change c d (f t) (g t) hr hs).trans
      (add_le_add (add_le_add (hclose t ht') le_rfl) le_rfl)
    rw [← sub_mul, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right hweight (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hderiv t ht') (by positivity))
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun t ht => hb t (by simpa only [uIoc_of_le zero_le_one] using ht))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryPairNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open exclusion neighborhoods use the actual fixed-source boundary
functional. Its continuity is proved from the disk-distance estimate;
no stability or exclusion assertion is assumed. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

 theorem boundaryPairFunctional_trace (γ : ℝ → ℂ) (hγ : Continuous γ)
    (c : ℂ) (r : ℝ≥0) (v : ℝ → ℝ) :
    boundaryPairFunctional v (boundaryCurveTrace γ hγ, c, r) =
      roundDiskBoundaryPairing γ c r v := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  change infDist (γ (projIcc 0 1 zero_le_one t)) (closedBall c (r : ℝ)) * deriv v t = _
  rw [coe_projIcc, min_eq_right ht'.2, max_eq_right ht'.1]

 theorem boundaryPairFunctional_lipschitz (v : ℝ → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ∃ L : ℝ≥0, LipschitzWith L (boundaryPairFunctional v) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (hv.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp))
  refine ⟨⟨3 * M, by positivity⟩, LipschitzWith.of_dist_le_mul ?_⟩
  intro p q
  have h := roundDiskBoundaryPairing_stability
    (p.1 ∘ projIcc 0 1 zero_le_one) (q.1 ∘ projIcc 0 1 zero_le_one)
    (p.1.continuous.comp continuous_projIcc) (q.1.continuous.comp continuous_projIcc)
    p.2.1 q.2.1 p.2.2.property q.2.2.property v hv (dist_nonneg (x := p.1) (y := q.1))
    (fun t _ => ContinuousMap.dist_apply_le_dist (projIcc 0 1 zero_le_one t))
    (fun t ht => by simpa only [Real.norm_eq_abs] using hM t ht)
  have hf : dist p.1 q.1 ≤ dist p q := by
    exact le_max_left _ _
  have hc : dist p.2.1 q.2.1 ≤ dist p q :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hr : |(p.2.2 : ℝ) - q.2.2| ≤ dist p q := by
    change dist p.2.2 q.2.2 ≤ dist p q
    exact (le_max_right _ _).trans (le_max_right _ _)
  change |boundaryPairFunctional v p - boundaryPairFunctional v q| ≤ 3 * M * dist p q
  have hs : dist p.1 q.1 + dist p.2.1 q.2.1 + |(p.2.2 : ℝ) - q.2.2| ≤ 3 * dist p q := by
    linarith
  exact h.trans ((mul_le_mul_of_nonneg_right hs hM0).trans_eq (by ring))

 theorem continuous_boundaryPairFunctional (v : ℝ → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) : Continuous (boundaryPairFunctional v) :=
  (boundaryPairFunctional_lipschitz v hv).choose_spec.continuous

 theorem isOpen_boundaryExclusionSet (v : ℝ → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (budget : ℝ) :
    IsOpen (boundaryExclusionSet v budget) :=
  isOpen_lt continuous_const (continuous_boundaryPairFunctional v hv).abs

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FixedCircuitExclusion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single actual smooth source coordinate supplies a fixed real lift
and an open neighborhood of boundary-map/disk data. Its lower integral
is the same functional used to exclude diagonal Stokes limits. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_smooth_real_circuit_lift
    {O : Set ℂ} (hO : IsOpen O) {w : ℂ → UnitAddCircle} (hw : SmoothCircleOn w O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧ ∀ t, (v t : UnitAddCircle) = w (γ t) := by
  let : ContractibleSpace (univ : Set ℝ) := convex_univ.contractibleSpace Set.univ_nonempty
  let : LocallyPathConnectedSpace (univ : Set ℝ) := isOpen_univ.locallyPathConnectedSpace
  have hc : Continuous (w ∘ γ) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (hw.continuousOn.continuousAt (hO.mem_nhds (hγO t))).comp hγ.continuous.continuousAt)
  obtain ⟨v, hv, _, hp⟩ := exists_continuous_circle_lift (w ∘ γ) hc.continuousOn
    (mem_univ 0) ((AddCircle.equivIco (1 : ℝ) 0 (w (γ 0))) : ℝ) (by
      simp only [Function.comp_apply, AddCircle.coe_equivIco])
  have hv' := continuousOn_univ.mp hv
  have hp' : ∀ t, (v t : UnitAddCircle) = w (γ t) := fun t => hp t (mem_univ t)
  exact ⟨v, contDiff_real_lift_along hw hγ hγO hv' hp', hp'⟩

 theorem contDiffOn_distance_from_disk_comp
    {O : Set ℂ} {f : ℂ → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (houtside : ∀ z ∈ O, r < dist (f z) c) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => infDist (f z) (closedBall c r)) O := by
  have hne : ∀ z ∈ O, f z ≠ c := by
    intro z hz h
    have := houtside z hz
    rw [h, dist_self] at this
    linarith
  have hs := (hf.dist ℝ contDiffOn_const hne).sub (contDiffOn_const (c := r))
  apply hs.congr
  intro z hz
  exact infDist_closedBall_of_dist_gt c (f z) hr (houtside z hz)

 theorem circleFormIntegral_eq_boundaryPairFunctional
    {O : Set ℂ} (hO : IsOpen O) {w : ℂ → UnitAddCircle} (hw : SmoothCircleOn w O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O)
    (f : ℂ → ℂ) (hf : ContinuousOn f O) (c : ℂ) (r : ℝ≥0)
    (v : ℝ → ℝ) (hv : Continuous v) (hproj : ∀ t, (v t : UnitAddCircle) = w (γ t)) :
    circleFormIntegral (fun z => infDist (f z) (closedBall c (r : ℝ))) w γ =
      boundaryPairFunctional v
        (boundaryCurveTrace (f ∘ γ) (hf.comp_continuous hγ.continuous hγO), c, r) := by
  rw [boundaryPairFunctional_trace,
    circleFormIntegral_eq_real_lift hO hw _ γ (hγ.differentiable (by simp)) hγO v hv hproj]
  rfl

 theorem exists_open_fixed_circuit_exclusion
    {O : Set ℂ} (hO : IsOpen O) {w : ℂ → UnitAddCircle} (hw : SmoothCircleOn w O)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O)
    (f : ℂ → ℂ) (hf : ContinuousOn f O) (c : ℂ) (r : ℝ≥0) (budget : ℝ)
    (hlower : budget < |circleFormIntegral (fun z => infDist (f z) (closedBall c (r : ℝ))) w γ|) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      (∀ t, (v t : UnitAddCircle) = w (γ t)) ∧
      IsOpen (boundaryExclusionSet v budget) ∧
      (boundaryCurveTrace (f ∘ γ) (hf.comp_continuous hγ.continuous hγO), c, r) ∈
        boundaryExclusionSet v budget := by
  obtain ⟨v, hv, hproj⟩ := exists_smooth_real_circuit_lift hO hw hγ hγO
  refine ⟨v, hv, hproj, isOpen_boundaryExclusionSet v hv budget, ?_⟩
  change budget < |boundaryPairFunctional v _|
  rwa [← circleFormIntegral_eq_boundaryPairFunctional hO hw hγ hγO f hf c r v hv.continuous hproj]

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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual projected Jordan collars have connected complements and
their closed regions miss the image of physical infinity. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

namespace WeightedCollar

variable {G : Set Sphere} {π : Sphere → Sphere} {B : Set Sphere}
  {p : Sphere} {g : ℂ → ℝ≥0∞} (D : WeightedCollar G π B p g)

theorem infty_notMem_closure_region (hπ : Continuous π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    π OnePoint.infty ∉ closure D.region := by
  intro hinfty
  obtain ⟨_, ⟨z, hz, rfl⟩, heq⟩ := D.closure_region_subset_image hπ hinfty
  have hsat := preimage_image_jordanInterior_of_component_collapse
    G π hsurj hr D.disk (fun z hz => (D.level_good z (D.frontier_level hz)).1)
  have hznot : z ∉ jordanInterior D.disk := by
    intro hzin
    have hi : π OnePoint.infty ∈ D.region := heq ▸ ⟨(z : Sphere), ⟨z, hzin, rfl⟩, rfl⟩
    have hi' : OnePoint.infty ∈ π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' jordanInterior D.disk)) := hi
    rw [hsat] at hi'
    exact OnePoint.infty_notMem_image_coe hi'
  have hzfront : z ∈ frontier (jordanInterior D.disk) := by
    rw [(jordanInterior_isOpen D.disk).frontier_eq]
    exact ⟨hz, hznot⟩
  rcases (hr (z : Sphere) OnePoint.infty).mp heq with h | ⟨h, _⟩
  · exact OnePoint.coe_ne_infty z h
  · exact h (D.level_good z (D.frontier_level hzfront)).1

end WeightedCollar
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CenteredTerminalLaw
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete centered disk data of a compact terminal-arc family. All
injectivity and unit bounds hold on the actual punctured Jordan interior. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 theorem exists_centered_terminal_family (J : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (A : Set C(PathTime, Sphere)) (hA : IsCompact A)
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b) :
    Nonempty (CenteredTerminalFamily J b A) := by
  obtain ⟨F, hF⟩ := exists_centeredJordanExtension J hb
  let K := F.comp '' A
  let f : A → K := fun γ => ⟨F.comp γ.val, mem_image_of_mem F.comp γ.property⟩
  refine ⟨⟨F, hF, K, hA.image F.continuous_postcomp, ?_, f,
    (F.continuous_postcomp.comp continuous_subtype_val).subtype_mk _, fun _ => rfl⟩⟩
  rintro _ ⟨γ, hγ, rfl⟩
  exact centeredJordanPath_mem J hb F hF (hAS hγ)

namespace CenteredTerminalFamily
variable {J : ℂ ≃ₜ ℂ} {b : Sphere} {A : Set C(PathTime, Sphere)}
    (P : CenteredTerminalFamily J b A)
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)

 theorem punctured_open : IsOpen P.punctured :=
  (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)).sdiff isClosed_singleton

 include hb

 theorem nonzero : ∀ x ∈ P.punctured, P.map x ≠ 0 := by
  intro x hx he
  apply hx.2
  apply (centeredJordanCoordinate_injOn J hb (subset_closure hx.1) (subset_closure hb))
  rw [← P.map_eq (subset_closure hx.1), centeredJordanCoordinate_self]
  exact he

 theorem norm_lt : ∀ x ∈ ((↑) : ℂ → Sphere) '' jordanInterior J, ‖P.map x‖ < 1 := by
  intro x hx
  rw [P.map_eq (subset_closure hx)]
  exact diskCentering_norm_lt (sphereJordanCoordinate_norm_lt J hb)
    (sphereJordanCoordinate_norm_lt J hx)

 theorem norm_le : ∀ x ∈ P.punctured, ‖P.map x‖ ≤ 1 :=
  fun x hx => (P.norm_lt hb x hx.1).le

 theorem injective : InjOn P.map (closure (((↑) : ℂ → Sphere) '' jordanInterior J)) := by
  intro x hx y hy he
  apply centeredJordanCoordinate_injOn J hb hx hy
  rwa [← P.map_eq hx, ← P.map_eq hy]

 theorem injective_punctured : InjOn P.map P.punctured :=
  (P.injective hb).mono (fun _ hx => subset_closure hx.1)

 theorem injective_arcs
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b) :
    ∀ γ : A, InjOn P.map (range γ.val ∪ P.punctured) := by
  intro γ
  apply (P.injective hb).mono
  rintro x (⟨t, rfl⟩ | hx)
  · exact terminalArcSet_mapsTo_closure (hAS γ.property) hb (mem_univ t)
  · exact subset_closure hx.1

 omit hb in
 theorem endpoint
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b) :
    ∀ γ : A, b ∈ range γ.val := fun γ => ⟨⊤, (hAS γ.property).2.2.1⟩

end CenteredTerminalFamily
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_InnerPeriodMask
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integration curve strictly inside the outer collar admits an enclosing closed
period mask still strictly inside that collar. Thus the centered disk coordinate is
needed only on its genuine open disk, while the integration curve lies in the interior
of the physical mask. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

 theorem RegularJordanInwardCollar.exists_inner_period_mask
    {G U : Set Sphere} (hG : IsOpen G) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ jordanInterior H) :
    ∃ M : Set Sphere, IsClosed M ∧ frontier M ⊆ U ∧
      π OnePoint.infty ∉ M ∧ M ⊆ π '' (((↑) : ℂ → Sphere) '' jordanInterior H) ∧
      realChartDomain (((↑) : ℂ → Sphere) '' K) ⊆ interior (physicalMask π M) := by
  obtain ⟨t, ht, htw, hKt, hin, hbd, _⟩ := C.select_inner hK hKH
    (hG.preimage OnePoint.continuous_coe) hboundary (by norm_num : (0 : ℝ) < 1)
  let V := π '' (((↑) : ℂ → Sphere) '' jordanInterior (C.disk t))
  have hbdG : ∀ z ∈ frontier (jordanInterior (C.disk t)), (z : Sphere) ∈ G := hbd
  have hVo : IsOpen V := isOpen_image_jordanInterior_of_component_collapse G π hπ hclosed
    hsurj hr (C.disk t) hbdG
  have hsat := preimage_image_jordanInterior_of_component_collapse G π hsurj hr (C.disk t) hbdG
  have hfront : frontier V = π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk t))) := by
    change frontier (π '' (((↑) : ℂ → Sphere) '' jordanInterior (C.disk t))) = _
    rw [frontier_image_of_saturated_open π hπ
      (((↑) : ℂ → Sphere) '' jordanInterior (C.disk t))
      (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen _)) hVo
      (hclosed _ isClosed_closure) hsat, frontier_sphere_image_jordanInterior]
  refine ⟨closure V, isClosed_closure, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxV := frontier_closure_subset hx
    rw [hfront] at hxV
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hxV
    exact hPU z (hbdG z hz)
  · exact infty_notMem_closure_image_jordanInterior G π hπ hclosed hsurj hr (C.disk t) hbdG
  · change closure (π '' (((↑) : ℂ → Sphere) '' jordanInterior (C.disk t))) ⊆ _
    rw [closure_image_jordanInterior π hπ hclosed]
    exact image_mono (image_mono hin)
  · have hopen : IsOpen (realChartDomain (π ⁻¹' V)) :=
      isOpen_realChartDomain (hVo.preimage hπ)
    have hsub : realChartDomain (π ⁻¹' V) ⊆ physicalMask π (closure V) :=
      preimage_mono (preimage_mono subset_closure)
    intro x hx
    apply (hopen.subset_interior_iff.mpr hsub)
    change π ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ V
    change (Complex.equivRealProdCLM.symm x : Sphere) ∈ ((↑) : ℂ → Sphere) '' K at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have heq : z = Complex.equivRealProdCLM.symm x := OnePoint.coe_injective hzx
    exact ⟨(z : Sphere), ⟨z, hKt hz, rfl⟩, by rw [heq]⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MeanBoundaryCollar
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform approach to the actual boundary mean. Only avoidance at the
boundary is used: the nearby lifted points need not avoid every sample arc. -/

open Set Function Filter MeasureTheory
open scoped Topology Uniformity

noncomputable section
namespace CircleDomainRigidity

 theorem mean_uniform_boundary_approximation_of_dist
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    (hmiss : ∀ x ∈ Icc (0 : ℝ) 1,
      ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (x : ℂ) ∉ range γ.val)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ClosedUpperHalfPlane,
      dist z.val (t : ℂ) < δ →
      |meanGeometricIndex hsch K hKS η z -
        boundaryIndexMean (compactArcStartingAngleLaw K η) t| < ε := by
  let B : ℝ → ClosedUpperHalfPlane := fun x => ⟨(x : ℂ), by simp⟩
  have hB : Continuous B := Complex.continuous_ofReal.subtype_mk _
  have hc : IsCompact (B '' Icc (0 : ℝ) 1) := isCompact_Icc.image hB
  have hcont : ∀ z ∈ B '' Icc (0 : ℝ) 1,
      ContinuousAt (meanGeometricIndex hsch K hKS η) z := by
    rintro _ ⟨x, hx, rfl⟩
    exact continuousAt_meanGeometricIndex hsch hsep K hK hKS η (B x) (hmiss x hx)
  have hu := hc.uniformContinuousAt_of_continuousAt
    (meanGeometricIndex hsch K hKS η) hcont (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨δ, hδ, ?_⟩
  intro t ht z hz
  have hdist : dist (B t) z < δ := by
    change dist (t : ℂ) z.val < δ
    simpa only [dist_comm] using hz
  have he := hd hdist ⟨t, ht, rfl⟩
  change dist (meanGeometricIndex hsch K hKS η (B t))
    (meanGeometricIndex hsch K hKS η z) < ε at he
  rw [meanGeometricIndex_boundary hsch K hKS η t (hmiss t ht)] at he
  simpa only [Real.dist_eq, abs_sub_comm] using he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PeriodicBoundaryPairing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A boundary pairing defined for continuous lifts is stable under
uniform perturbations of the same period. For smooth lifts it is the
ordinary boundary integral, by integration by parts. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem liftedBoundaryPairing_eq_integral
    (φ dφ v dv : ℝ → ℝ)
    (hφ : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt φ (dφ x) x)
    (hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt v (dv x) x)
    (hdφ : IntervalIntegrable dφ volume 0 1)
    (hdv : IntervalIntegrable dv volume 0 1) :
    liftedBoundaryPairing φ dφ v = ∫ x in (0 : ℝ)..1, φ x * dv x :=
  (intervalIntegral.integral_mul_deriv_eq_deriv_mul hφ hv hdφ hdv).symm

theorem liftedBoundaryPairing_stability
    (φ dφ u v : ℝ → ℝ) (hφ : φ 1 = φ 0)
    (hperiod : u 1 - u 0 = v 1 - v 0)
    (hu : ContinuousOn u (Icc (0 : ℝ) 1))
    (hv : ContinuousOn v (Icc (0 : ℝ) 1))
    (hdφ : IntervalIntegrable dφ volume 0 1)
    (δ : ℝ) (hclose : ∀ x ∈ Icc (0 : ℝ) 1, |u x - v x| ≤ δ) :
    |liftedBoundaryPairing φ dφ u - liftedBoundaryPairing φ dφ v| ≤
      δ * ∫ x in (0 : ℝ)..1, |dφ x| := by
  have hu' : ContinuousOn u (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hu
  have hv' : ContinuousOn v (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hv
  have hdu := hdφ.mul_continuousOn hu'
  have hdv := hdφ.mul_continuousOn hv'
  have hi : (∫ x in (0 : ℝ)..1, dφ x * (u x - v x)) =
      (∫ x in (0 : ℝ)..1, dφ x * u x) - ∫ x in (0 : ℝ)..1, dφ x * v x := by
    simp_rw [mul_sub]
    exact intervalIntegral.integral_sub hdu hdv
  have he : liftedBoundaryPairing φ dφ u - liftedBoundaryPairing φ dφ v =
      -(∫ x in (0 : ℝ)..1, dφ x * (u x - v x)) := by
    unfold liftedBoundaryPairing
    rw [hi, hφ]
    have hp := congrArg (fun t : ℝ => φ 0 * t) hperiod
    nlinarith only [hp]
  have hw : IntervalIntegrable (fun x => δ * |dφ x|) volume 0 1 := by
    simpa only [Real.norm_eq_abs] using hdφ.norm.const_mul δ
  have hb : ‖∫ x in (0 : ℝ)..1, dφ x * (u x - v x)‖ ≤
      ∫ x in (0 : ℝ)..1, δ * |dφ x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one _ hw
    apply Eventually.of_forall
    intro x hx
    simp only [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hclose x ⟨hx.1.le, hx.2⟩) (abs_nonneg _)).trans_eq
      (mul_comm _ _)
  rw [he, abs_neg]
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul] using hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ReparametrizedBoundaryPairing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive boundary identity in a physical boundary parameter.
The increasing angle change is only a homeomorphism; it is not differentiated. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem integral_single_reparametrized_boundary_index
    (q : ℝ ≃o ℝ) (hq0 : q 0 = 0) (hq1 : q 1 = 1)
    (φ dφ : ℝ → ℝ) (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : Continuous dφ)
    (a : UnitAddCircle) :
    (∫ x in (0 : ℝ)..1, dφ x * (⌊q x - unitCircleCut a⌋ : ℝ)) =
      φ 0 - φ (q.symm (unitCircleCut a)) := by
  let t := q.symm (unitCircleCut a)
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · apply q.le_iff_le.mp
      simpa only [hq0, t, q.apply_symm_apply] using (unitCircleCut_mem a).1
    · apply q.le_iff_le.mp
      simpa only [hq1, t, q.apply_symm_apply] using (unitCircleCut_mem a).2.le
  have he : (fun x => dφ x * (⌊q x - unitCircleCut a⌋ : ℝ)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun x => -((Iic t).indicator dφ x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc (0 : ℝ) 1)).ae_ne 1,
      (volume.restrict (Ioc (0 : ℝ) 1)).ae_ne t] with x hx hx1 hxt
    have hqx0 : 0 < q x := by simpa only [hq0] using q.strictMono hx.1
    have hqx1 : q x < 1 := by
      simpa only [hq1] using q.strictMono (lt_of_le_of_ne hx.2 hx1)
    by_cases hlt : x < t
    · have hqt : q x < unitCircleCut a := by
        simpa only [t, q.apply_symm_apply] using q.strictMono hlt
      have hfloor : ⌊q x - unitCircleCut a⌋ = (-1 : ℤ) := by
        apply Int.floor_eq_iff.mpr
        constructor <;> norm_num
        · linarith [(unitCircleCut_mem a).2]
        · linarith
      simp only [hfloor, Int.cast_neg, Int.cast_one, mul_neg, mul_one,
        indicator_of_mem (show x ∈ Iic t from hlt.le)]
    · have htx : t < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hxt)
      have hqt : unitCircleCut a < q x := by
        simpa only [t, q.apply_symm_apply] using q.strictMono htx
      have hfloor : ⌊q x - unitCircleCut a⌋ = (0 : ℤ) := by
        apply Int.floor_eq_iff.mpr
        constructor <;> norm_num
        · linarith
        · linarith [(unitCircleCut_mem a).1]
      simp only [hfloor, Int.cast_zero, mul_zero,
        indicator_of_notMem (show x ∉ Iic t from not_le_of_gt htx), neg_zero]
  have hEq : (∫ x in (0 : ℝ)..1, dφ x * (⌊q x - unitCircleCut a⌋ : ℝ)) =
      -(∫ x in (0 : ℝ)..t, dφ x) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_congr_ae he, integral_neg,
      ← intervalIntegral.integral_of_le zero_le_one]
    exact congrArg Neg.neg (intervalIntegral.integral_indicator (f := dφ) (μ := volume) ht)
  rw [hEq, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hφ x) (hdφ.intervalIntegrable 0 t)]
  ring

 theorem integrable_weighted_reparametrized_boundary_index
    (β : ProbabilityMeasure UnitAddCircle) (q : ℝ ≃o ℝ)
    (hq0 : q 0 = 0) (hq1 : q 1 = 1) (dφ : ℝ → ℝ) (hdφ : Continuous dφ) :
    Integrable (fun p : ℝ × UnitAddCircle => dφ p.1 * (⌊q p.1 - unitCircleCut p.2⌋ : ℝ))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (β : Measure UnitAddCircle)) := by
  have hidx : Measurable (fun p : ℝ × UnitAddCircle => (⌊q p.1 - unitCircleCut p.2⌋ : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      ((q.continuous.measurable.comp measurable_fst).sub
        (measurable_unitCircleCut.comp measurable_snd)).floor
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hdφ.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg (dφ 0)).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  have hfirst : ∀ᵐ p : ℝ × UnitAddCircle
      ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (β : Measure UnitAddCircle)),
      p.1 ∈ Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    exact (ae_restrict_mem measurableSet_Ioc).mono fun x hx => Eventually.of_forall fun _ => hx
  apply Integrable.of_bound ((hdφ.measurable.comp measurable_fst).mul hidx).aestronglyMeasurable
    (C * 3)
  filter_upwards [hfirst] with p hp
  have hq : q p.1 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [hq0] using q.monotone hp.1.le
    · simpa only [hq1] using q.monotone hp.2
  have hcount : |(⌊q p.1 - unitCircleCut p.2⌋ : ℝ)| ≤ 3 := by
    have hb := boundaryIndex_bound (q p.1) p.2
    have habs : |q p.1| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1], hq.2⟩
    linarith
  change ‖dφ p.1 * (⌊q p.1 - unitCircleCut p.2⌋ : ℝ)‖ ≤ C * 3
  rw [norm_mul, Real.norm_eq_abs (⌊q p.1 - unitCircleCut p.2⌋ : ℝ)]
  exact mul_le_mul (hC p.1 ⟨hp.1.le, hp.2⟩) hcount (abs_nonneg _) hC0

 theorem liftedBoundaryPairing_reparametrized_boundaryIndexMean
    (β : ProbabilityMeasure UnitAddCircle) (q : ℝ ≃o ℝ)
    (hq0 : q 0 = 0) (hq1 : q 1 = 1) (φ dφ : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : Continuous dφ)
    (hperiod : φ 1 = φ 0) :
    liftedBoundaryPairing φ dφ (boundaryIndexMean β ∘ q) =
      ∫ a, φ (q.symm (unitCircleCut a)) ∂(β : Measure UnitAddCircle) := by
  have hF := integrable_weighted_reparametrized_boundary_index β q hq0 hq1 dφ hdφ
  have hc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hc.continuousOn
  have ht (a : UnitAddCircle) : q.symm (unitCircleCut a) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · apply q.le_iff_le.mp
      simpa only [hq0, q.apply_symm_apply] using (unitCircleCut_mem a).1
    · apply q.le_iff_le.mp
      simpa only [hq1, q.apply_symm_apply] using (unitCircleCut_mem a).2.le
  have hi : Integrable (fun a : UnitAddCircle => φ (q.symm (unitCircleCut a)))
      (β : Measure UnitAddCircle) := by
    apply Integrable.of_bound (hc.measurable.comp
      (q.symm.continuous.measurable.comp measurable_unitCircleCut)).aestronglyMeasurable C
    exact Eventually.of_forall fun a => hC _ (ht a)
  have hswap : (∫ x in (0 : ℝ)..1, dφ x * boundaryIndexMean β (q x)) =
      ∫ a, φ 0 - φ (q.symm (unitCircleCut a)) ∂(β : Measure UnitAddCircle) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    calc
      _ = ∫ x, ∫ a, dφ x * (⌊q x - unitCircleCut a⌋ : ℝ)
          ∂(β : Measure UnitAddCircle) ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        change dφ x * (∫ a, (⌊q x - unitCircleCut a⌋ : ℝ) ∂(β : Measure UnitAddCircle)) = _
        exact (integral_const_mul (dφ x) (fun a => (⌊q x - unitCircleCut a⌋ : ℝ))).symm
      _ = ∫ a, ∫ x, dφ x * (⌊q x - unitCircleCut a⌋ : ℝ)
          ∂(volume.restrict (Ioc (0 : ℝ) 1)) ∂(β : Measure UnitAddCircle) :=
        integral_integral_swap hF
      _ = _ := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro a
        simpa only [intervalIntegral.integral_of_le zero_le_one] using
          integral_single_reparametrized_boundary_index q hq0 hq1 φ dφ hφ hdφ a
  have hb : boundaryIndexMean β 1 = boundaryIndexMean β 0 + 1 := by
    simpa only [zero_add] using boundaryIndexMean_add_one β 0
  unfold liftedBoundaryPairing
  simp only [Function.comp_apply, hq0, hq1]
  rw [hperiod, hswap, integral_sub (integrable_const (φ 0)) hi, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hb]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ReparametrizedBoundaryLowerBound
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive starting-point law gives the lower bound on any sufficiently
close smooth inward circuit. The boundary angle parameter need not be smooth. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem smooth_reparametrized_boundary_integral_lower_bound
    (β : ProbabilityMeasure UnitAddCircle) [NullSingletonClass (β : Measure UnitAddCircle)]
    (q : ℝ ≃o ℝ) (hq0 : q 0 = 0) (hq1 : q 1 = 1)
    (φ dφ u du : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : Continuous dφ) (hφperiod : φ 1 = φ 0)
    (hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt u (du x) x)
    (hdu : IntervalIntegrable du volume 0 1) (huperiod : u 1 = u 0 + 1)
    (δ c : ℝ) (hclose : ∀ x ∈ Icc (0 : ℝ) 1, |u x - boundaryIndexMean β (q x)| ≤ δ)
    (hpositive : ∀ᵐ a : UnitAddCircle ∂(β : Measure UnitAddCircle),
      c ≤ φ (q.symm (unitCircleCut a))) :
    c ≤ (∫ x in (0 : ℝ)..1, φ x * du x) + δ * ∫ x in (0 : ℝ)..1, |dφ x| := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hφc.continuousOn
  have hi : Integrable (fun a : UnitAddCircle => φ (q.symm (unitCircleCut a)))
      (β : Measure UnitAddCircle) := by
    apply Integrable.of_bound (hφc.measurable.comp
      (q.symm.continuous.measurable.comp measurable_unitCircleCut)).aestronglyMeasurable C
    apply Eventually.of_forall
    intro a
    apply hC
    constructor
    · apply q.le_iff_le.mp
      simpa only [Function.comp_apply, hq0, q.apply_symm_apply] using (unitCircleCut_mem a).1
    · apply q.le_iff_le.mp
      simpa only [Function.comp_apply, hq1, q.apply_symm_apply] using (unitCircleCut_mem a).2.le
  have hc : c ≤ ∫ a, φ (q.symm (unitCircleCut a)) ∂(β : Measure UnitAddCircle) := by
    calc
      c = ∫ _a : UnitAddCircle, c ∂(β : Measure UnitAddCircle) := by simp
      _ ≤ _ := integral_mono_ae (integrable_const c) hi hpositive
  have huc : ContinuousOn u (Icc (0 : ℝ) 1) := by
    intro x hx
    exact (hu x (by simpa only [uIcc_of_le zero_le_one] using hx)).continuousAt.continuousWithinAt
  have hvperiod : boundaryIndexMean β (q 1) = boundaryIndexMean β (q 0) + 1 := by
    simpa only [hq0, hq1, zero_add] using boundaryIndexMean_add_one β 0
  have hsame : u 1 - u 0 = (boundaryIndexMean β ∘ q) 1 - (boundaryIndexMean β ∘ q) 0 := by
    simp only [Function.comp_apply]
    rw [huperiod, hvperiod]
    ring
  have hs := liftedBoundaryPairing_stability φ dφ u (boundaryIndexMean β ∘ q) hφperiod hsame
    huc ((continuous_boundaryIndexMean β).comp q.continuous).continuousOn
    (hdφ.intervalIntegrable 0 1) δ hclose
  rw [liftedBoundaryPairing_eq_integral φ dφ u du (fun x _ => hφ x) hu
    (hdφ.intervalIntegrable 0 1) hdu,
    liftedBoundaryPairing_reparametrized_boundaryIndexMean β q hq0 hq1 φ dφ hφ hdφ hφperiod] at hs
  linarith [neg_abs_le ((∫ x in (0 : ℝ)..1, φ x * du x) -
    ∫ a, φ (q.symm (unitCircleCut a)) ∂(β : Measure UnitAddCircle))]

 theorem exists_mean_collar_boundary_lower_bound
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)]
    (q : ℝ ≃o ℝ) (hq0 : q 0 = 0) (hq1 : q 1 = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (L : ℝ → ClosedUpperHalfPlane) (φ dφ u du : ℝ → ℝ),
      (∀ x, HasDerivAt φ (dφ x) x) → Continuous dφ → φ 1 = φ 0 →
      (∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt u (du x) x) →
      IntervalIntegrable du volume 0 1 → u 1 = u 0 + 1 →
      (∀ x ∈ Icc (0 : ℝ) 1, dist (L x).val (q x : ℂ) < δ) →
      (∀ x ∈ Icc (0 : ℝ) 1, |u x - meanGeometricIndex hsch K hKS η (L x)| ≤ ε) →
      ∀ c : ℝ, (∀ᵐ a : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
        c ≤ φ (q.symm (unitCircleCut a))) →
      c ≤ (∫ x in (0 : ℝ)..1, φ x * du x) + (2 * ε) * ∫ x in (0 : ℝ)..1, |dφ x| := by
  obtain ⟨δ, hδ, hd⟩ := mean_uniform_boundary_approximation_of_dist hsch hsep K hK hKS η
    (fun x _ => compactArc_boundary_avoidance K hKS η x) hε
  refine ⟨δ, hδ, ?_⟩
  intro L φ dφ u du hφ hdφ hφperiod hu hdu huperiod hL herror c hpositive
  apply smooth_reparametrized_boundary_integral_lower_bound
    (compactArcStartingAngleLaw K η) q hq0 hq1 φ dφ u du hφ hdφ hφperiod
    hu hdu huperiod (2 * ε) c ?_ hpositive
  intro x hx
  have hqx : q x ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [hq0] using q.monotone hx.1
    · simpa only [hq1] using q.monotone hx.2
  have hb := hd (q x) hqx (L x) (hL x hx)
  have he := herror x hx
  calc
    |u x - boundaryIndexMean (compactArcStartingAngleLaw K η) (q x)| =
        |(u x - meanGeometricIndex hsch K hKS η (L x)) +
          (meanGeometricIndex hsch K hKS η (L x) -
            boundaryIndexMean (compactArcStartingAngleLaw K η) (q x))| := by congr 1; ring
    _ ≤ |u x - meanGeometricIndex hsch K hKS η (L x)| +
        |meanGeometricIndex hsch K hKS η (L x) -
          boundaryIndexMean (compactArcStartingAngleLaw K η) (q x)| := abs_add_le _ _
    _ ≤ 2 * ε := by linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanCircuit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A physical smooth circle coordinate has an actual smooth, period-one
real lift on a circuit whenever it is the perturbed mean on a lifted
punctured-disk circuit. No smoothness of the boundary angle is required. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_smooth_mean_circuit_lift
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (L : ℝ → ClosedUpperHalfPlane) (hL : Continuous L)
    (hmiss : ∀ t, ∀ᵐ α : K ∂(η : Measure K), diskRayProjection (L t).val ∉ range α.val)
    (hperiod : L 1 = (L 0).translate 1)
    (O : Set ℂ) (w : ℂ → UnitAddCircle) (hw : SmoothCircleOn w O)
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγO : ∀ t, γ t ∈ O)
    (hloop : γ 1 = γ 0) (R : ℂ → ℝ) (hR : Continuous (R ∘ γ))
    (hvalue : ∀ t, w (γ t) = diskMeanCircle hsch K hKS η (diskRayProjection (L t).val) +
      (R (γ t) : UnitAddCircle)) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      (∀ t, v t = meanGeometricIndex hsch K hKS η (L t) + R (γ t)) ∧
      (∀ t, (v t : UnitAddCircle) = w (γ t)) ∧ v 1 = v 0 + 1 := by
  let v : ℝ → ℝ := fun t => meanGeometricIndex hsch K hKS η (L t) + R (γ t)
  have hc : Continuous v := by
    apply Continuous.add _ hR
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_meanGeometricIndex hsch hsep K hK hKS η (L t) (hmiss t)).comp
      hL.continuousAt
  have hp (t : ℝ) : (v t : UnitAddCircle) = w (γ t) := by
    rw [hvalue t, diskMeanCircle_projection hsch hsep K hK hKS η]
    simp only [v, AddCircle.coe_add]
  refine ⟨v, contDiff_real_lift_along hw hγ hγO hc hp, fun _ => rfl, hp, ?_⟩
  change meanGeometricIndex hsch K hKS η (L 1) + R (γ 1) =
    (meanGeometricIndex hsch K hKS η (L 0) + R (γ 0)) + 1
  rw [hperiod, hloop, meanGeometricIndex_translate hsch hsep K hK hKS η]
  simp only [Int.cast_one]
  ring

 theorem mean_circuit_integral_lower_bound
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)]
    (q : ℝ ≃o ℝ) (hq0 : q 0 = 0) (hq1 : q 1 = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (L : ℝ → ClosedUpperHalfPlane), Continuous L →
      (∀ t, ∀ᵐ α : K ∂(η : Measure K), diskRayProjection (L t).val ∉ range α.val) →
      L 1 = (L 0).translate 1 →
      ∀ (O : Set ℂ), IsOpen O → ∀ (w : ℂ → UnitAddCircle), SmoothCircleOn w O →
      ∀ (γ : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) γ → (∀ t, γ t ∈ O) → γ 1 = γ 0 →
      ∀ (R : ℂ → ℝ), Continuous (R ∘ γ) →
      (∀ t, w (γ t) = diskMeanCircle hsch K hKS η (diskRayProjection (L t).val) +
        (R (γ t) : UnitAddCircle)) →
      (∀ t ∈ Icc (0 : ℝ) 1, |R (γ t)| ≤ ε) →
      (∀ t ∈ Icc (0 : ℝ) 1, dist (L t).val (q t : ℂ) < δ) →
      ∀ (Φ : ℂ → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) Φ O →
      ∀ c : ℝ, (∀ᵐ a : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
        c ≤ Φ (γ (q.symm (unitCircleCut a)))) →
      c ≤ circleFormIntegral Φ w γ +
        (2 * ε) * ∫ t in (0 : ℝ)..1, |deriv (Φ ∘ γ) t| := by
  obtain ⟨δ, hδ, hbound⟩ := exists_mean_collar_boundary_lower_bound hsch hsep K hK hKS η
    q hq0 hq1 hε
  refine ⟨δ, hδ, ?_⟩
  intro L hL hmiss hperiod O hO w hw γ hγ hγO hloop R hR hvalue hRbound hnear Φ hΦ c hpositive
  obtain ⟨v, hv, hvvalue, hvproj, hvperiod⟩ := exists_smooth_mean_circuit_lift hsch hsep
    K hK hKS η L hL hmiss hperiod O w hw γ hγ hγO hloop R hR hvalue
  have hΦγ : ContDiff ℝ (⊤ : ℕ∞) (Φ ∘ γ) := by
    apply contDiffOn_univ.mp
    intro t _
    exact ((hΦ.contDiffAt (hO.mem_nhds (hγO t))).comp t hγ.contDiffAt).contDiffWithinAt
  have hb := hbound L (Φ ∘ γ) (deriv (Φ ∘ γ)) v (deriv v)
    (fun t => (hΦγ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasDerivAt)
    (hΦγ.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (by simp only [Function.comp_apply, hloop])
    (fun t _ => (hv.differentiable (by simp) t).hasDerivAt)
    ((hv.continuous_deriv (by simp)).intervalIntegrable 0 1) hvperiod hnear
    (fun t ht => by rw [hvvalue t]; simpa only [add_sub_cancel_left] using hRbound t ht)
    c hpositive
  rw [circleFormIntegral_eq_real_lift hO hw Φ γ (hγ.differentiable (by simp)) hγO v
    hv.continuous hvproj]
  exact hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CollarMeanLowerBound
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The boundary lower bound on an actual smooth inward collar. The
orientation-normalized circuit is used to evaluate the mean, and its
absolute integral is then returned to the original positive circuit. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem OrderedCollarLift.mean_boundary_lower_bound
    {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F)
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ > 0, σ < D.width ∧ ∀ ρ ∈ Ioc (0 : ℝ) σ,
      ∀ (O : Set ℂ), IsOpen O → ∀ (w : ℂ → UnitAddCircle), SmoothCircleOn w O →
      (∀ t, D.circuit ρ t ∈ O) →
      (∀ t, ∀ᵐ α : K ∂(η : Measure K), F (D.circuit ρ t : Sphere) ∉ range α.val) →
      ∀ (R : ℂ → ℝ), Continuous (R ∘ D.circuit ρ) →
      (∀ t, w (D.circuit ρ t) = diskMeanCircle hsch K hKS η (F (D.circuit ρ t : Sphere)) +
        (R (D.circuit ρ t) : UnitAddCircle)) →
      (∀ t ∈ Icc (0 : ℝ) 1, |R (D.circuit ρ t)| ≤ ε) →
      ∀ (Φ : ℂ → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) Φ O →
      ∀ c : ℝ, (∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
        c ≤ Φ (D.circuit ρ (D.angle.symm (unitCircleCut θ)))) →
      c ≤ |circleFormIntegral Φ w (C.curve ρ)| +
        (2 * ε) * ∫ t in (0 : ℝ)..1, |deriv (Φ ∘ D.circuit ρ) t| := by
  obtain ⟨δ, hδ, hbound⟩ := mean_circuit_integral_lower_bound hsch hsep K hK hKS η
    D.angle D.angle_zero D.angle_one hε
  obtain ⟨σ, hσ, hσw, hnear⟩ := D.approach δ hδ
  refine ⟨σ / 2, half_pos hσ, (half_lt_self hσ).trans hσw, ?_⟩
  intro ρ hρ O hO w hw hc hm R hR hv hRb Φ hΦ c hpositive
  have hρw : ρ ∈ Ioo (-D.width) D.width :=
    ⟨by linarith [D.width_pos, hρ.1], by linarith [hρ.2]⟩
  have hρC : ρ ∈ Icc (0 : ℝ) C.width :=
    ⟨hρ.1.le, hρw.2.le.trans D.width_le⟩
  have hp (t : ℝ) : diskRayProjection (D.lift (ρ, t)).val = F (D.circuit ρ t : Sphere) := by
    simpa only [abs_of_pos hρ.1, OrderedCollarLift.circuit, Function.comp_apply] using
      D.projects (ρ, t) ⟨hρw, mem_univ _⟩
  have hb := hbound (fun t => D.lift (ρ, t)) (D.continuous_slice hρw)
    (fun t => by simpa only [hp t] using hm t) (D.period ρ hρw)
    O hO w hw (D.circuit ρ) (D.circuit_smooth hρC) hc (D.circuit_periodic hρC).eq
    R hR (fun t => by simpa only [hp t] using hv t) hRb
    (hnear ρ ⟨by linarith [hρ.1], by linarith [hρ.2]⟩)
    Φ hΦ c hpositive
  calc
    c ≤ circleFormIntegral Φ w (D.circuit ρ) +
        (2 * ε) * ∫ t in (0 : ℝ)..1, |deriv (Φ ∘ D.circuit ρ) t| := hb
    _ ≤ |circleFormIntegral Φ w (D.circuit ρ)| +
        (2 * ε) * ∫ t in (0 : ℝ)..1, |deriv (Φ ∘ D.circuit ρ) t| :=
      add_le_add (le_abs_self _) le_rfl
    _ = _ := by rw [D.abs_circleFormIntegral hρC Φ w]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CollarScalarControl
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform control of a fixed smooth weight on the inward collar. The
smooth collar's continuous tangent gives a common variation bound before
the smoothing accuracy for the mean coordinate is chosen. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem RegularJordanInwardCollar.scalar_uniform_approach
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    {O : Set ℂ} (hO : IsOpen O) (hCO : frontier (jordanInterior H) ⊆ O)
    (Φ : ℂ → ℝ) (hΦ : ContinuousOn Φ O) :
    ∀ ε > 0, ∃ η > 0, η ≤ C.width ∧ ∀ ρ ∈ Icc 0 η, ∀ t : ℝ,
      |Φ (C.curve ρ t) - Φ (C.curve 0 t)| < ε := by
  obtain ⟨ζ, hζ, hζw, hinside⟩ := C.eventually_in_boundary_neighborhood hO hCO
  let K : Set (ℝ × ℝ) := Icc 0 ζ ×ˢ Icc 0 1
  have hsub : K ⊆ Icc 0 C.width ×ˢ (univ : Set ℝ) := fun p hp =>
    ⟨⟨hp.1.1, hp.1.2.trans hζw⟩, mem_univ _⟩
  have hc : ContinuousOn (fun p : ℝ × ℝ => Φ (C.curve p.1 p.2)) K :=
    hΦ.comp (C.continuous.mono hsub) (fun p hp => hinside p.1 hp.1 p.2 hp.2)
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hc
  intro ε hε
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let η := min ζ (d / 2)
  have hη : 0 < η := lt_min hζ (half_pos hd)
  have hηζ : η ≤ ζ := min_le_left _ _
  refine ⟨η, hη, hηζ.trans hζw, ?_⟩
  intro ρ hρ t
  have hρζ : ρ ∈ Icc (0 : ℝ) ζ := ⟨hρ.1, hρ.2.trans hηζ⟩
  have ht : Int.fract t ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hb := hdist (ρ, Int.fract t) ⟨hρζ, ht⟩ (0, Int.fract t) ⟨⟨le_rfl, hζ.le⟩, ht⟩
    (show dist (ρ, Int.fract t) (0, Int.fract t) < d by
      rw [Prod.dist_eq, dist_self, max_eq_left (show (0 : ℝ) ≤ dist ρ 0 from dist_nonneg),
        Real.dist_eq, sub_zero, abs_of_nonneg hρ.1]
      exact hρ.2.trans_lt ((min_le_right ζ (d / 2)).trans_lt (half_lt_self hd)))
  have heρ : C.curve ρ (Int.fract t) = C.curve ρ t := by
    simpa only [Int.fract, mul_one] using
      (C.parametrization ρ ⟨hρ.1, hρζ.2.trans hζw⟩).periodic.sub_int_mul_eq (x := t) ⌊t⌋
  have he0 : C.curve 0 (Int.fract t) = C.curve 0 t := by
    simpa only [Int.fract, mul_one] using
      (C.parametrization 0 ⟨le_rfl, C.width_pos.le⟩).periodic.sub_int_mul_eq (x := t) ⌊t⌋
  simpa only [heρ, he0, Real.dist_eq] using hb

 theorem abs_deriv_oriented (f : ℝ → ℝ) (a : ℝ) (reverse : Bool) (t : ℝ) :
    |deriv (f ∘ orientedParameter a reverse) t| = |deriv f (orientedParameter a reverse t)| := by
  cases reverse
  · exact congrArg abs (deriv_comp_const_add f a t)
  · change |deriv (fun s => (fun x => f (a + x)) (1 - s)) t| = _
    rw [deriv_comp_const_sub (fun x => f (a + x)) 1 t, abs_neg, deriv_comp_const_add]
    rfl

 theorem real_deriv_periodic {f : ℝ → ℝ} (hp : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro t
  rw [← deriv_comp_add_const]
  exact congrArg (fun g : ℝ → ℝ => deriv g t) (funext hp)

 theorem RegularJordanInwardCollar.scalar_derivative_bound
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    {O : Set ℂ} (hO : IsOpen O) (hCO : frontier (jordanInterior H) ⊆ O)
    (Φ : ℂ → ℝ) (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ O) :
    ∃ (ζ B : ℝ), 0 < ζ ∧ ζ ≤ C.width ∧ 0 ≤ B ∧
      ∀ ρ ∈ Icc 0 ζ, ∀ (a : ℝ) (reverse : Bool) (t : ℝ),
        |deriv (Φ ∘ C.curve ρ ∘ orientedParameter a reverse) t| ≤ B := by
  obtain ⟨ζ, hζ, hζw, hinside⟩ := C.eventually_in_boundary_neighborhood hO hCO
  let K : Set (ℝ × ℝ) := Icc 0 ζ ×ˢ Icc 0 1
  have hsub : K ⊆ Icc 0 C.width ×ˢ (univ : Set ℝ) := fun p hp =>
    ⟨⟨hp.1.1, hp.1.2.trans hζw⟩, mem_univ _⟩
  have hf : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ Φ (C.curve p.1 p.2)) K :=
    ((hΦ.fderiv_of_isOpen (m := 0) hO (by simp)).continuousOn).comp
      (C.continuous.mono hsub) (fun p hp => hinside p.1 hp.1 p.2 hp.2)
  have hc := hf.clm_apply (C.tangent_continuous.mono hsub)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (0, 0) ⟨⟨le_rfl, hζ.le⟩, ⟨le_rfl, zero_le_one⟩⟩)
  refine ⟨ζ, B, hζ, hζw, hB0, ?_⟩
  intro ρ hρ a reverse t
  let s := orientedParameter a reverse t
  have hρw : ρ ∈ Icc (0 : ℝ) C.width := ⟨hρ.1, hρ.2.trans hζw⟩
  have hper : Function.Periodic (deriv (Φ ∘ C.curve ρ)) 1 :=
    real_deriv_periodic ((C.parametrization ρ hρw).periodic.comp Φ)
  have he : deriv (Φ ∘ C.curve ρ) (Int.fract s) = deriv (Φ ∘ C.curve ρ) s := by
    simpa only [Int.fract, mul_one] using hper.sub_int_mul_eq (x := s) ⌊s⌋
  change |deriv ((Φ ∘ C.curve ρ) ∘ orientedParameter a reverse) t| ≤ B
  rw [abs_deriv_oriented (Φ ∘ C.curve ρ) a reverse t]
  change |deriv (Φ ∘ C.curve ρ) s| ≤ B
  rw [← he]
  have hs : Int.fract s ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hd : deriv (Φ ∘ C.curve ρ) (Int.fract s) =
      (fderiv ℝ Φ (C.curve ρ (Int.fract s))) (deriv (C.curve ρ) (Int.fract s)) := by
    exact (((hΦ.contDiffAt (hO.mem_nhds (hinside ρ hρ _ hs))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp_hasDerivAt _
      (((C.parametrization ρ hρw).smooth.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _).hasDerivAt)).deriv
  rw [hd]
  simpa only [Real.norm_eq_abs] using hB (ρ, Int.fract s) ⟨hρ, hs⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothCollarLowerBound
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the smoothing accuracy before the inward circuit. Uniform
variation of the fixed smooth weight and the actual starting-point law
give a strictly positive boundary integral on every sufficiently small
inward circuit. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem OrderedCollarLift.exists_strict_mean_lower_bound
    {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F)
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)]
    (O : Set ℂ) (hO : IsOpen O) (hCO : frontier (jordanInterior H) ⊆ O)
    (Φ : ℂ → ℝ) (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ O)
    {d : ℝ} (hd : 0 < d)
    (hgate : ∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
      d ≤ Φ (D.circuit 0 (D.angle.symm (unitCircleCut θ)))) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ σ > 0, σ < D.width ∧ ∀ ρ ∈ Ioc (0 : ℝ) σ,
      ∀ (W : Set ℂ), IsOpen W → ∀ (w : ℂ → UnitAddCircle), SmoothCircleOn w W →
      (∀ t, D.circuit ρ t ∈ W) →
      (∀ t, ∀ᵐ α : K ∂(η : Measure K), F (D.circuit ρ t : Sphere) ∉ range α.val) →
      ∀ (R : ℂ → ℝ), Continuous (R ∘ D.circuit ρ) →
      (∀ t, w (D.circuit ρ t) = diskMeanCircle hsch K hKS η (F (D.circuit ρ t : Sphere)) +
        (R (D.circuit ρ t) : UnitAddCircle)) →
      (∀ t ∈ Icc (0 : ℝ) 1, |R (D.circuit ρ t)| ≤ ε) →
      d / 2 < |circleFormIntegral Φ w (C.curve ρ)| := by
  obtain ⟨ζ, B, hζ, hζw, hB, hderiv⟩ := C.scalar_derivative_bound hO hCO Φ hΦ
  let ε := min 1 (d / (16 * (B + 1)))
  have hden : 0 < 16 * (B + 1) := by positivity
  have hε : 0 < ε := lt_min zero_lt_one (div_pos hd hden)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hprod : ε * (16 * (B + 1)) ≤ d :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have herror : 2 * ε * B < d / 8 := by nlinarith
  obtain ⟨α, hα, _hαw, hnear⟩ := C.scalar_uniform_approach hO hCO Φ hΦ.continuousOn (d / 8) (by positivity)
  obtain ⟨μ, hμ, hμw, hinside⟩ := C.eventually_in_boundary_neighborhood hO hCO
  obtain ⟨τ, hτ, hτw, hmean⟩ := D.mean_boundary_lower_bound hsch hsep K hK hKS η hε
  let σ := min ζ (min α (min μ τ))
  have hσ : 0 < σ := lt_min hζ (lt_min hα (lt_min hμ hτ))
  have hσζ : σ ≤ ζ := min_le_left _ _
  have hσα : σ ≤ α := (min_le_right _ _).trans (min_le_left _ _)
  have hσμ : σ ≤ μ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hστ : σ ≤ τ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, hε, hε1, σ, hσ, hστ.trans_lt hτw, ?_⟩
  intro ρ hρ W hW w hw hγW hmiss R hR hv hRb
  have hρζ : ρ ∈ Icc (0 : ℝ) ζ := ⟨hρ.1.le, hρ.2.trans hσζ⟩
  have hρα : ρ ∈ Icc (0 : ℝ) α := ⟨hρ.1.le, hρ.2.trans hσα⟩
  have hρμ : ρ ∈ Icc (0 : ℝ) μ := ⟨hρ.1.le, hρ.2.trans hσμ⟩
  have hρC : ρ ∈ Icc (0 : ℝ) C.width := ⟨hρ.1.le, hρμ.2.trans hμw⟩
  have hγO (t : ℝ) : D.circuit ρ t ∈ O := by
    let s := orientedParameter D.start D.reverse t
    have hh := hinside ρ hρμ (Int.fract s) ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    have he : C.curve ρ (Int.fract s) = C.curve ρ s := by
      simpa only [Int.fract, mul_one] using
        (C.parametrization ρ hρC).periodic.sub_int_mul_eq (x := s) ⌊s⌋
    rwa [he] at hh
  have hpositive : ∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
      d - d / 8 ≤ Φ (D.circuit ρ (D.angle.symm (unitCircleCut θ))) := by
    filter_upwards [hgate] with θ hθ
    have hn := hnear ρ hρα (orientedParameter D.start D.reverse (D.angle.symm (unitCircleCut θ)))
    change |Φ (D.circuit ρ (D.angle.symm (unitCircleCut θ))) -
      Φ (D.circuit 0 (D.angle.symm (unitCircleCut θ)))| < d / 8 at hn
    linarith [(abs_lt.mp hn).1]
  have hb := hmean ρ ⟨hρ.1, hρ.2.trans hστ⟩ (O ∩ W) (hO.inter hW) w
    (fun x hx => hw x hx.2) (fun t => ⟨hγO t, hγW t⟩) hmiss
    R hR hv hRb Φ (hΦ.mono inter_subset_left) (d - d / 8) hpositive
  have hV : (∫ t in (0 : ℝ)..1, |deriv (Φ ∘ D.circuit ρ) t|) ≤ B := by
    have hbound (t : ℝ) : |deriv (Φ ∘ D.circuit ρ) t| ≤ B :=
      hderiv ρ hρζ D.start D.reverse t
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun t : ℝ => |deriv (Φ ∘ D.circuit ρ) t|) (C := B)
      (fun t _ => by simpa only [Real.norm_eq_abs, abs_abs] using hbound t)
    have hh' : |(∫ t in (0 : ℝ)..1, |deriv (Φ ∘ D.circuit ρ) t|)| ≤ B := by
      simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hh
    exact (le_abs_self _).trans hh'
  have hVε := mul_le_mul_of_nonneg_left hV (show 0 ≤ 2 * ε by positivity)
  nlinarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskIndependentMeanLowerBound
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The collar tolerance and depth are selected before a period mask is chosen.
This follows from the same physical strict lower bound, whose estimates do not use
the mask. It allows an inner mask to enclose the chosen integration curve. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
 theorem exists_smooth_mean_collar_lower_bound_all_masks
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)]
    (G U S : Set Sphere) (hG : IsOpen G) (hS : IsOpen S) (b : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (hπU : ∀ x ∈ G, π x ∈ U)
    (F : C(Sphere, ℂ))
    {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H}
    (D : OrderedCollarLift C (F.comp ⟨π, hπ⟩))
    (O : Set ℂ) (hO : IsOpen O) (hCO : frontier (jordanInterior H) ⊆ O)
    (Φ : ℂ → ℝ) (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ O)
    {d : ℝ} (hd : 0 < d)
    (hgate : ∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
      d ≤ Φ (D.circuit 0 (D.angle.symm (unitCircleCut θ)))) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ σ > 0, σ < D.width ∧ ∀ ρ ∈ Ioc (0 : ℝ) σ,
      ∀ (M : Set Sphere) (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π),
      (∀ x, |Q.error x| ≤ ε) →
      (∀ t, (D.circuit ρ t : Sphere) ∈ G ∧ π (D.circuit ρ t : Sphere) ∈ S) →
      (∀ t, ∀ᵐ α : K ∂(η : Measure K), F (π (D.circuit ρ t : Sphere)) ∉ range α.val) →
      d / 2 < |circleFormIntegral Φ Q.physical (C.curve ρ)| := by
  obtain ⟨ε, hε, hε1, σ, hσ, hσw, hbound⟩ :=
    D.exists_strict_mean_lower_bound hsch hsep K hK hKS η O hO hCO Φ hΦ hd hgate
  refine ⟨ε, hε, hε1, σ, hσ, hσw, ?_⟩
  intro ρ hρ M Q herror hcurve hmiss
  let W : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S
  have hW : IsOpen W := (hG.preimage OnePoint.continuous_coe).inter
    (hS.preimage (hπ.comp OnePoint.continuous_coe))
  have hρC : ρ ∈ Icc (0 : ℝ) C.width :=
    ⟨hρ.1.le, hρ.2.trans (hσw.le.trans D.width_le)⟩
  have hRc : Continuous (fun t => Q.error (π (D.circuit ρ t : Sphere))) := by
    apply Q.error_continuous.comp_continuous
      (hπ.comp (OnePoint.continuous_coe.comp (D.circuit_smooth hρC).continuous))
    intro t
    exact ⟨hπU _ (hcurve t).1, (hcurve t).2⟩
  exact hbound ρ hρ W hW Q.physical Q.physical_smooth hcurve hmiss
    (fun z => Q.error (π (z : Sphere))) hRc
    (fun t => Q.physical_value _ (hcurve t).1 (hcurve t).2)
    (fun t _ => herror _)

 theorem exists_gated_mean_collar_lower_bound_all_masks
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (G U S : Set Sphere) (e : G ≃ₜ U)
    (hG : IsOpen G) (hU : IsOpen U) (hS : IsOpen S) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ x : G, (e x).val = π x.val)
    {H J : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H}
    (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G)
    (hfront : frontier (((↑) : ℂ → Sphere) '' jordanInterior J) =
      π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)))
    {b : Sphere} (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate J b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J)))
    (D : OrderedCollarLift C (F.comp ⟨π, hπ⟩))
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b)
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (f : A → K) (hf : Measurable f) (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior J),
      pathHitProbability (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) x = 0)
    (O : Set ℂ) (hO : IsOpen O) (hCO : frontier (jordanInterior H) ⊆ O)
    (Φ : ℂ → ℝ) (hΦm : Measurable Φ) (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ O)
    {d : ℝ} (hd : 0 < d)
    (hgate : ∀ᵐ γ : A ∂(η : Measure A), d ≤ Φ (finiteCoord (physicalValue e y₀ (γ.val 0)))) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ σ > 0, σ < D.width ∧ ∀ ρ ∈ Ioc (0 : ℝ) σ,
      ∀ (M : Set Sphere) (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (hf.aemeasurable)) F G U S M b π),
      (∀ x, |Q.error x| ≤ ε) →
      (∀ t, (D.circuit ρ t : Sphere) ∈ G ∧ π (D.circuit ρ t : Sphere) ∈ S) →
      (∀ t, ∀ᵐ α : K ∂(η.map (f := f) (hf.aemeasurable) : Measure K), F (π (D.circuit ρ t : Sphere)) ∉ range α.val) →
      d / 2 < |circleFormIntegral Φ Q.physical (C.curve ρ)| := by
  let := compact_startingLaw_atomless J hb A K η hAS F hF f hf hmap havoid
  have hgate' := compact_startingLaw_physical_gate e hU y₀ π hπ he hboundary hfront hb
    F hF D A K η hAS f hf hmap Φ hΦm d hgate
  exact exists_smooth_mean_collar_lower_bound_all_masks hsch hsep K hK hKS (η.map (f := f) (hf.aemeasurable))
    G U S hG hS b π hπ (fun x hx => (he ⟨x, hx⟩) ▸ (e ⟨x, hx⟩).property)
    F D O hO hCO Φ hΦ hd hgate'

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MapDiskExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-circuit exclusions in the compact-open space of maps and disks.
The circuit restriction is continuous, so these are the open sets used by
countable selection, not just open sets of boundary traces. -/

open Set Function Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem continuous_circuitRestriction {G : Set Sphere} (γ : C(PathTime, FiniteSource G)) :
    Continuous (circuitRestriction γ) :=
  ((ContinuousMap.continuous_precomp γ).comp continuous_fst).prodMk continuous_snd

 theorem isOpen_mapDiskExclusion {G : Set Sphere} (γ : C(PathTime, FiniteSource G))
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (budget : ℝ) :
    IsOpen (mapDiskExclusion γ v budget) :=
  (isOpen_boundaryExclusionSet v hv budget).preimage (continuous_circuitRestriction γ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CoordinateMapExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed actual masked coordinate defines an open excluded neighborhood
in map--disk space whenever its boundary integral exceeds its source budget. -/

open Set Function Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateData.exists_mapDisk_exclusion
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) (hG : IsOpen G)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π C.mask))
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (c : ℂ) (r : ℝ≥0) (R : ℝ)
    (hlower : C.sourceStokesBudget R < |circleFormIntegral
      (fun z => Metric.infDist (F z) (Metric.closedBall c (r : ℝ)))
      (C.physical ∘ Complex.equivRealProdCLM) γ|) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      (∀ t, (v t : UnitAddCircle) = C.physical (Complex.equivRealProdCLM (γ t))) ∧
      IsOpen (mapDiskExclusion
        (sourceCircuit γ hγ.smooth.continuous (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t))))
        v (C.sourceStokesBudget R)) ∧
      (finiteSourceMap F hF, c, r) ∈ mapDiskExclusion
        (sourceCircuit γ hγ.smooth.continuous (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t))))
        v (C.sourceStokesBudget R) := by
  let W := Complex.equivRealProdCLM ⁻¹' (realChartDomain G ∩ interior (physicalMask π C.mask))
  have hW : IsOpen W := ((isOpen_realChartDomain hG).inter isOpen_interior).preimage
    Complex.equivRealProdCLM.continuous
  have hγW : ∀ t, γ t ∈ W := by
    intro t
    refine ⟨?_, ?_⟩
    · change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈ G
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact hbd (mem_image_of_mem _ (hγ.mem_frontier t))
    · apply hmask
      change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈
        closedTerminalCap H
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact mem_image_of_mem _ (frontier_subset_closure (hγ.mem_frontier t))
  have hw : SmoothCircleOn (C.physical ∘ Complex.equivRealProdCLM) W := by
    intro z hz a ha
    exact (C.smooth _ hz a ha).comp z Complex.equivRealProdCLM.contDiff.contDiffAt
  have hFW : ContinuousOn F W := hF.mono (by
    intro z hz
    have hzG := hz.1
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ G at hzG
    rw [ContinuousLinearEquiv.symm_apply_apply] at hzG
    change (z : Sphere) ∈ G
    exact hzG)
  obtain ⟨v, hv, hp, _, hmem⟩ := exists_open_fixed_circuit_exclusion hW hw hγ.smooth hγW
    F hFW c r (C.sourceStokesBudget R) hlower
  refine ⟨v, hv, hp, isOpen_mapDiskExclusion _ v hv _, ?_⟩
  exact hmem

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleIntegralCongruence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equality of smooth circle coordinates along the whole parametrized
circuit is enough to identify their original form integrals. -/

open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem circleFormIntegral_eq_of_eq_on_curve
    {O P : Set ℂ} (hO : IsOpen O) (hP : IsOpen P)
    {u v : ℂ → UnitAddCircle} (hu : SmoothCircleOn u O) (hv : SmoothCircleOn v P)
    (φ : ℂ → ℝ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ)
    (hγO : ∀ t, γ t ∈ O) (hγP : ∀ t, γ t ∈ P)
    (heq : ∀ t, u (γ t) = v (γ t)) :
    circleFormIntegral φ u γ = circleFormIntegral φ v γ := by
  obtain ⟨w, hw, hproj⟩ := exists_smooth_real_circuit_lift hO hu hγ hγO
  rw [circleFormIntegral_eq_real_lift hO hu φ γ (hγ.differentiable (by simp))
    hγO w hw.continuous hproj,
    circleFormIntegral_eq_real_lift hP hv φ γ (hγ.differentiable (by simp))
    hγP w hw.continuous (fun t => (hproj t).trans (heq t))]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanCircuitExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A strict lower bound for the constructed mean excludes the same
map--disk pair after passing to its measurable physical coordinate. -/

open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateData.circleFormIntegral_eq_of_physical_values
    {T : Type*} {G U S : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    (C : MaskedCoordinateData G U π σ) (hG : IsOpen G) (hS : IsOpen S) (hπ : Continuous π)
    (u : ℂ → UnitAddCircle)
    (hu : SmoothCircleOn u (((↑) : ℂ → Sphere) ⁻¹' G ∩
      (fun z : ℂ => π (z : Sphere)) ⁻¹' S))
    (hvalue : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
      C.physical (Complex.equivRealProdCLM z) = u z)
    (φ : ℂ → ℝ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ)
    (hγG : ∀ t, (γ t : Sphere) ∈ G) (hγS : ∀ t, π (γ t : Sphere) ∈ S)
    (hγM : ∀ t, Complex.equivRealProdCLM (γ t) ∈ interior (physicalMask π C.mask)) :
    circleFormIntegral φ (C.physical ∘ Complex.equivRealProdCLM) γ =
      circleFormIntegral φ u γ := by
  let O := Complex.equivRealProdCLM ⁻¹'
    (realChartDomain G ∩ interior (physicalMask π C.mask))
  have hO : IsOpen O := ((isOpen_realChartDomain hG).inter isOpen_interior).preimage
    Complex.equivRealProdCLM.continuous
  have hP : IsOpen (((↑) : ℂ → Sphere) ⁻¹' G ∩
      (fun z : ℂ => π (z : Sphere)) ⁻¹' S) :=
    (hG.preimage OnePoint.continuous_coe).inter
      (hS.preimage (hπ.comp OnePoint.continuous_coe))
  apply circleFormIntegral_eq_of_eq_on_curve hO hP _ hu φ hγ _
    (fun t => ⟨hγG t, hγS t⟩) (fun t => hvalue _ (hγG t) (hγS t))
  · intro z hz a ha
    exact (C.smooth _ hz a ha).comp z Complex.equivRealProdCLM.contDiff.contDiffAt
  · intro t
    refine ⟨?_, hγM t⟩
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈ G
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hγG t

 theorem MaskedCoordinateData.exists_mapDisk_exclusion_of_mean
    {T : Type*} {G U S : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    (C : MaskedCoordinateData G U π σ) (hG : IsOpen G) (hS : IsOpen S) (hπ : Continuous π)
    (u : ℂ → UnitAddCircle)
    (hu : SmoothCircleOn u (((↑) : ℂ → Sphere) ⁻¹' G ∩
      (fun z : ℂ => π (z : Sphere)) ⁻¹' S))
    (hvalue : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
      C.physical (Complex.equivRealProdCLM z) = u z)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hmask : realChartDomain (closedTerminalCap H) ⊆ interior (physicalMask π C.mask))
    (hγS : ∀ t, π (γ t : Sphere) ∈ S)
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (c : ℂ) (r : ℝ≥0) (R : ℝ) (a : ℝ)
    (hbudget : C.sourceStokesBudget R ≤ a)
    (hlower : a < |circleFormIntegral
      (fun z => Metric.infDist (F z) (Metric.closedBall c (r : ℝ))) u γ|) :
    ∃ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      (∀ t, (v t : UnitAddCircle) = C.physical (Complex.equivRealProdCLM (γ t))) ∧
      IsOpen (mapDiskExclusion
        (sourceCircuit γ hγ.smooth.continuous (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t))))
        v (C.sourceStokesBudget R)) ∧
      (finiteSourceMap F hF, c, r) ∈ mapDiskExclusion
        (sourceCircuit γ hγ.smooth.continuous (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t))))
        v (C.sourceStokesBudget R) := by
  apply C.exists_mapDisk_exclusion hG H γ hγ hbd hmask F hF c r R
  rw [C.circleFormIntegral_eq_of_physical_values hG hS hπ u hu hvalue _ hγ.smooth
    (fun t => hbd (mem_image_of_mem _ (hγ.mem_frontier t))) hγS]
  · exact hbudget.trans_lt hlower
  · intro t
    apply hmask
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈
      closedTerminalCap H
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact mem_image_of_mem _ (frontier_subset_closure (hγ.mem_frontier t))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_InnerCollarCoordinate
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive collar slices lie inside the punctured coordinate disk. The outer
boundary is used only as a limit, so it need not lie in the open coordinate domain. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem orientedParameter_surjective (a : ℝ) (reverse : Bool) :
    Surjective (orientedParameter a reverse) := by
  intro t
  cases reverse
  · exact ⟨t - a, by dsimp [orientedParameter] <;> ring⟩
  · exact ⟨1 + a - t, by dsimp [orientedParameter] <;> ring⟩

 theorem OrderedCollarLift.inner_frontier_punctured
    {H J : ℂ ≃ₜ ℂ} {L : RegularJordanInwardCollar H}
    {π : Sphere → Sphere} (hπ : Continuous π) {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift L (F.comp ⟨π, hπ⟩)) {b : Sphere} (hb : F b = 0)
    (hregion : π '' (((↑) : ℂ → Sphere) '' jordanInterior H) =
      ((↑) : ℂ → Sphere) '' jordanInterior J)
    {ρ : ℝ} (hρ : 0 < ρ) (hρw : ρ < D.width) :
    ∀ z ∈ frontier (jordanInterior (L.disk ρ)),
      π (z : Sphere) ∈ (((↑) : ℂ → Sphere) '' jordanInterior J) \ {b} := by
  intro z hz
  have hρL : ρ ∈ Icc (0 : ℝ) L.width := ⟨hρ.le, hρw.le.trans D.width_le⟩
  refine ⟨?_, ?_⟩
  · rw [← hregion]
    exact ⟨(z : Sphere), ⟨z, L.inward ρ ⟨hρ, hρL.2⟩ (frontier_subset_closure hz), rfl⟩, rfl⟩
  · obtain ⟨s, _, hzs⟩ := (L.parametrization ρ hρL).boundary.symm ▸ hz
    obtain ⟨t, hts⟩ := orientedParameter_surjective D.start D.reverse s
    have hp := D.projects (ρ, t) ⟨⟨by linarith, hρw⟩, mem_univ _⟩
    change diskRayProjection (D.lift (ρ, t)).val =
      F (π (L.curve |ρ| (orientedParameter D.start D.reverse t) : Sphere)) at hp
    rw [abs_of_pos hρ, hts, hzs] at hp
    intro heq
    rw [mem_singleton_iff.mp heq, hb] at hp
    have hn := congrArg norm hp
    rw [diskRayProjection_norm, norm_zero] at hn
    exact (Real.exp_pos _).ne' hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_InnerMeanCoordinateExclusion
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select the integration curve before its enclosing inner period mask.
The disk coordinate is used only inside its genuine outer Jordan disk. -/

open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_r5b9296_14 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_gated_small_inner_mean_exclusion
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U S : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hU : IsOpen U)
    (hdense : Dense U) (hS : IsOpen S)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U) (singular : T)
    (hbS : σ singular ∉ S) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (he : ∀ y : G, (e y).val = π y.val)
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
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (hmissFree : ∀ x ∈ ((π '' Gᶜ) \ range σ) ∩ S,
      ∀ᵐ γ : K ∂(η.map (f := f) (hf.aemeasurable) : Measure K), F x ∉ range γ.val)
    (hend : ∀ γ : A, σ singular ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2))
    (w : T → ℝ≥0∞) (hw : (∑' t, w t ^ 2) < ∞)
    (hwp : ∀ s, s ≠ singular → (η : Measure A) {γ | σ s ∈ range γ.val} ≤ w s)
    {R : ℝ} (hR : 0 ≤ R)
    {H J : ℂ ≃ₜ ℂ} (L : RegularJordanInwardCollar H)
    (hfront : frontier (((↑) : ℂ → Sphere) '' jordanInterior J) =
      π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)))
    (hbJ : σ singular ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (hFJ : EqOn F (centeredJordanCoordinate J (σ singular))
      (closure (((↑) : ℂ → Sphere) '' jordanInterior J)))
    (D : OrderedCollarLift L (F.comp ⟨π, hπ⟩))
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) (σ singular))
    (havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior J),
      pathHitProbability (η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) x = 0)
    (O : Set ℂ) (hO : IsOpen O) (hHO : frontier (jordanInterior H) ⊆ O)
    (hOG : ∀ z ∈ O, (z : Sphere) ∈ G)
    (hregion : π '' (((↑) : ℂ → Sphere) '' jordanInterior H) =
      ((↑) : ℂ → Sphere) '' jordanInterior J)
    (hJS : (((↑) : ℂ → Sphere) '' jordanInterior J) \ {σ singular} ⊆ S)
    (hstrict : ∀ x ∈ (((↑) : ℂ → Sphere) '' jordanInterior J) \ U, ‖F x‖ < 1)
    (F₀ : ℂ → ℂ) (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G))
    (hF₀m : Measurable F₀)
    (hF₀smooth : ContDiffOn ℝ (⊤ : ℕ∞) F₀ O)
    (c : ℂ) (r : ℝ≥0) (houtside : ∀ z ∈ O, (r : ℝ) < dist (F₀ z) c)
    {d₀ : ℝ} (hd₀ : 0 < d₀)
    (hgate : ∀ᵐ γ : A ∂(η : Measure A),
      d₀ ≤ Metric.infDist (F₀ (finiteCoord (physicalValue e y₀ (γ.val 0))))
        (Metric.closedBall c (r : ℝ)))
    (hsmall : (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) + countingSquareNorm w <
      meanBudgetTolerance B R (d₀ / 4)) :
    ∃ (M : Set Sphere), IsClosed M ∧ frontier M ⊆ U ∧ σ singular ∈ M ∧
      π OnePoint.infty ∉ M ∧ M ⊆ ((↑) : ℂ → Sphere) '' jordanInterior J ∧
      ∃ (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (hf.aemeasurable)) F G U S M (σ singular) π)
      (C : MaskedCoordinateData G U π σ),
      C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
      C.mask = M ∧ C.singular = singular ∧
      (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      C.sourceStokesBudget R < d₀ / 4 ∧
      ∃ (ρ : ℝ) (v : ℝ → ℝ), ρ ∈ Ioc (0 : ℝ) D.width ∧
        realChartDomain (closedTerminalCap (L.disk ρ)) ⊆ interior (physicalMask π C.mask) ∧
        π ⁻¹' {σ singular} ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (L.disk ρ) ∧
        ContDiff ℝ (⊤ : ℕ∞) v ∧
        (∀ t, (v t : UnitAddCircle) = C.physical (Complex.equivRealProdCLM (L.curve ρ t))) ∧
        ∃ V : Set (MapDiskData G), IsOpen V ∧
          (finiteSourceMap F₀ hF₀, c, r) ∈ V ∧
          ∃ (γ : C(PathTime, FiniteSource G)),
            (∀ t, (γ t).val = L.curve ρ t) ∧ V = mapDiskExclusion γ v (C.sourceStokesBudget R) := by
  let Φ : ℂ → ℝ := fun z => Metric.infDist (F₀ z) (Metric.closedBall c (r : ℝ))
  have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ O :=
    contDiffOn_distance_from_disk_comp hF₀smooth c r.property houtside
  have hΦm : Measurable Φ :=
    (Metric.continuous_infDist_pt (Metric.closedBall c (r : ℝ))).measurable.comp hF₀m
  obtain ⟨δ, hδ, hδ1, a, ha, haD, hlower⟩ := exists_gated_mean_collar_lower_bound_all_masks
    hsch hsep G U S e hG hU hS y₀ π hπ he
    (fun z hz => hOG z (hHO hz)) hfront hbJ F hFJ D A K η hAS hK hKS
    f hf hmap havoid O hO hHO Φ hΦm hΦ hd₀ hgate
  obtain ⟨b, hb, hbL, hnear⟩ := L.eventually_in_boundary_neighborhood hO hHO
  have htarget : σ singular ∈ π '' (((↑) : ℂ → Sphere) '' jordanInterior H) := by
    rw [hregion]
    exact hbJ
  obtain ⟨_, ⟨z, hz, rfl⟩, hzb⟩ := htarget
  obtain ⟨a₀, ha₀, ha₀w, hkeep⟩ := L.retains_compact {z} isCompact_singleton
    (singleton_subset_iff.mpr hz)
  let ρ := min a (min b a₀) / 2
  have hmin : 0 < min a (min b a₀) := lt_min ha (lt_min hb ha₀)
  have hρ : 0 < ρ := half_pos hmin
  have hhalf : ρ ≤ min a (min b a₀) := half_le_self hmin.le
  have hρa : ρ ≤ a := hhalf.trans (min_le_left _ _)
  have hρb : ρ ≤ b := hhalf.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρa₀ : ρ ≤ a₀ := hhalf.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρD : ρ ∈ Ioc (0 : ℝ) D.width := ⟨hρ, hρa.trans haD.le⟩
  have hρL : ρ ∈ Icc (0 : ℝ) L.width := ⟨hρ.le, hρD.2.trans D.width_le⟩
  have hboundaryO : frontier (jordanInterior (L.disk ρ)) ⊆ O := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := (L.parametrization ρ hρL).boundary.symm ▸ hz
    exact hnear ρ ⟨hρ.le, hρb⟩ t ht
  have hinnerS : ∀ z ∈ frontier (jordanInterior (L.disk ρ)), π (z : Sphere) ∈ S := by
    intro z hz
    apply hJS
    exact D.inner_frontier_punctured hπ
      (by rw [hFJ (subset_closure hbJ), centeredJordanCoordinate_self])
      hregion hρ (hρa.trans_lt haD) z hz
  have hcurve (t : ℝ) : (D.circuit ρ t : Sphere) ∈ G ∧
      π (D.circuit ρ t : Sphere) ∈ S :=
    ⟨hOG _ (hboundaryO (D.circuit_mem_frontier hρL t)),
      hinnerS _ (D.circuit_mem_frontier hρL t)⟩
  have havoidK (t : ℝ) : ∀ᵐ α : K ∂(η.map (f := f) (hf.aemeasurable) : Measure K),
      F (π (D.circuit ρ t : Sphere)) ∉ range α.val := by
    apply mapped_arc_point_avoidance A K η F f hf hmap
    · intro γ
      exact (hF γ).mono (union_subset_union Subset.rfl
        (singleton_subset_iff.mpr (hcurve t).2))
    · apply hmiss _ ⟨?_, (hcurve t).2⟩
      rw [← he ⟨_, (hcurve t).1⟩]
      exact (e ⟨_, (hcurve t).1⟩).property
  obtain ⟨M, hM, hboundary, hinfM, hMH, hcap⟩ := L.exists_inner_period_mask hG π hπ
    hclosed hsurj hr (fun z hz => (he ⟨_, hz⟩) ▸ (e ⟨_, hz⟩).property)
    (fun z hz => hOG z (hHO hz))
    (isCompact_closure_jordanInterior (L.disk ρ)) (L.inward ρ ⟨hρ, hρL.2⟩)
  have hMJ : M ⊆ ((↑) : ℂ → Sphere) '' jordanInterior J := by
    rw [← hregion]
    exact hMH
  have hbM : σ singular ∈ M := by
    have hzcap : z ∈ closure (jordanInterior (L.disk ρ)) :=
      subset_closure (hkeep ρ ⟨hρ, hρa₀⟩ (mem_singleton z))
    have hzmask := interior_subset (hcap (show Complex.equivRealProdCLM z ∈
        realChartDomain (((↑) : ℂ → Sphere) '' closure (jordanInterior (L.disk ρ))) from by
      exact ⟨z, hzcap, by
        exact congrArg ((↑) : ℂ → Sphere) (Complex.equivRealProdCLM.symm_apply_apply z).symm⟩))
    change π ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ M at hzmask
    simpa only [ContinuousLinearEquiv.symm_apply_apply, hzb] using hzmask
  have hMS : M \ {σ singular} ⊆ S := fun x hx => hJS ⟨hMJ hx.1, hx.2⟩
  have hstrictM : ∀ x ∈ M \ U, ‖F x‖ < 1 := fun x hx => hstrict x ⟨hMJ hx.1, hx.2⟩
  obtain ⟨Q, C, herr, hgraph, hmask, hsing, hwidth, hvalue, hbudget⟩ :=
    exists_smooth_mean_coordinate_with_small_budget hsch hsep hcoarea e hG hU hdense
      hS hM hboundary σ hσ singular hbS hMS y₀ π hπ he hfreeU hinf A hA η hfinite
      g hg hocc henergy K hK hKS F f hf hmap B hB h0 h1 hstrictM hF hinj hmiss hmissFree
      hend hbudget w hw hwp hR δ hδ hδ1 (by positivity : 0 < d₀ / 4) hsmall
  have herror : ∀ x, |Q.error x| ≤ δ := fun x =>
    (herr x).trans ((dustSmoothingTolerance_le_half id Uᶜ δ x).trans (by linarith))
  have hlow := hlower ρ ⟨hρ, hρa⟩ M Q herror hcurve havoidK
  have hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (L.disk ρ)) ⊆ G := by
    rintro _ ⟨z, hz, rfl⟩
    exact hOG z (hboundaryO hz)
  have hmask' : realChartDomain (closedTerminalCap (L.disk ρ)) ⊆
      interior (physicalMask π C.mask) := by rw [hmask]; exact hcap
  have hfiber : π ⁻¹' {σ singular} ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (L.disk ρ) := by
    have hsat := preimage_image_jordanInterior_of_component_collapse G π hsurj hr
      (L.disk ρ) (fun z hz => hbd (mem_image_of_mem _ hz))
    intro p hp
    rw [← hsat]
    exact ⟨(z : Sphere), ⟨z, hkeep ρ ⟨hρ, hρa₀⟩ (mem_singleton z), rfl⟩,
      hzb.trans (mem_singleton_iff.mp hp).symm⟩
  obtain ⟨v, hv, hproj, hV, hmem⟩ := C.exists_mapDisk_exclusion_of_mean hG hS hπ
    Q.physical Q.physical_smooth hvalue (L.disk ρ) (L.curve ρ) (L.parametrization ρ hρL)
    hbd hmask' (fun t => hinnerS _ ((L.parametrization ρ hρL).mem_frontier t))
    F₀ hF₀ c r R (d₀ / 4) hbudget.le (by exact lt_trans (by linarith) hlow)
  let γ := sourceCircuit (L.curve ρ) (L.parametrization ρ hρL).smooth.continuous
    (fun t => hbd (mem_image_of_mem _ ((L.parametrization ρ hρL).mem_frontier t)))
  exact ⟨M, hM, hboundary, hbM, hinfM, hMJ, Q, C, hgraph, hmask, hsing, hwidth, hbudget, ρ, v, hρD, hmask', hfiber, hv, hproj,
    mapDiskExclusion γ v (C.sourceStokesBudget R), hV, hmem, γ, (fun _ => rfl), rfl⟩

end CircleDomainRigidity

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

 theorem closure_openGate : closure T.openGate =
    ((↑) : ℂ → Sphere) '' closedBall T.center (2 * T.radius) := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono ball_subset_closedBall)
      (OnePoint.isClosed_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall _ _⟩)
  · rw [← closure_ball T.center (show 2 * T.radius ≠ 0 by linarith [T.radius_pos])]
    exact image_closure_subset_closure_image OnePoint.continuous_coe

 theorem infinity_notMem_closure_openGate : OnePoint.infty ∉ closure T.openGate := by
  rw [T.closure_openGate]
  exact OnePoint.infty_notMem_image_coe

 theorem uniform_gate_gap {s : S}
    (hsep : Disjoint (closedBall T.center (2 * T.radius))
      (closedBall (A.center s) (A.radius s))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, (z : Sphere) ∈ closure T.openGate →
      δ ≤ infDist z (closedBall (A.center s) (A.radius s)) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_uniform_infDist_gap
    (isCompact_closedBall T.center (2 * T.radius))
    (nonempty_closedBall.mpr (by linarith [T.radius_pos])) isClosed_closedBall
    (nonempty_closedBall.mpr (A.bounds s).2.1) hsep
  refine ⟨δ, hδ, fun z hz => hgap z ?_⟩
  rw [T.closure_openGate] at hz
  exact OnePoint.coe_injective.mem_set_image.mp hz

end LocalEndTestGeometry

namespace RealTargetEnd
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd A q)

include E in
 theorem source_outside_marked_disk
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {s : S} (hqs : π q = σ s) :
    ∀ z : ℂ, (z : Sphere) ∈ G → A.radius s < dist (A.function z) (A.center s) := by
  intro z hz
  apply lt_of_not_ge
  intro hdist
  have hmem : (A.function z : Sphere) ∈
      connectedComponentIn (extendAtInfinity A.function '' G)ᶜ E.point :=
    E.marked_disk_subset hr hq hqs (mem_image_of_mem _ hdist)
  exact connectedComponentIn_subset _ _ hmem ⟨(z : Sphere), hz, rfl⟩

end RealTargetEnd
end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RecursiveMeanExclusion
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact recursive positive law constructs an inner masked mean
and its open map--disk exclusion. Its energy and point-hit hypotheses are all
supplied by the law; only the geometric collar and prescribed gate are inputs. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem CompactRecursiveReduction.exists_mean_exclusion
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    {L : RecursiveCodeLaw base π Flags ω}
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    {H J : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    (hregion : π '' (((↑) : ℂ → Sphere) '' jordanInterior H) =
      ((↑) : ℂ → Sphere) '' jordanInterior J)
    (hbJ : L.data.target ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (hinfty : π OnePoint.infty ∉ closure (((↑) : ℂ → Sphere) '' jordanInterior J))
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹'
          ((((↑) : ℂ → Sphere) '' jordanInterior J) \ {L.data.target}))))
    {R : ℝ} (hR : 0 ≤ R) {d₀ : ℝ} (hd₀ : 0 < d₀)
    (Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J)
      (meanBudgetTolerance B R (d₀ / 4)))
    (O : Set ℂ) (hO : IsOpen O) (hHO : frontier (jordanInterior H) ⊆ O)
    (hOG : ∀ z ∈ O, (z : Sphere) ∈ base.physicalDomain)
    (F₀ : ℂ → ℂ)
    (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain))
    (hF₀m : Measurable F₀) (hF₀smooth : ContDiffOn ℝ (⊤ : ℕ∞) F₀ O)
    (c : ℂ) (r : ℝ≥0) (houtside : ∀ z ∈ O, (r : ℝ) < dist (F₀ z) c)
    (hgate : ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs),
      d₀ ≤ Metric.infDist (F₀ (finiteCoord (physicalValue base.domainEquiv base.basePoint (γ.val 0))))
        (Metric.closedBall c (r : ℝ))) :
    Nonempty (RecursiveMeanOutput hsch Q F₀ hF₀ c r R (d₀ / 4)) := by
  obtain ⟨P⟩ := exists_centered_terminal_family J hbJ Q.arcs Q.compact Q.terminal
  have hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ base.physicalDomain :=
    fun z hz => hOG z (hHO hz)
  have hfront := frontier_quotient_jordan_collar base.physicalDomain π hπ hclosed hsurj hr
    H J hboundary hregion
  obtain ⟨D⟩ := exists_quotient_ordered_collar_lift base.physicalDomain π hπ hclosed hsurj hr
    H J C hboundary hregion hbJ P.map P.map_eq
  let singular : base.dust := ⟨L.data.target, L.target_dust⟩
  have hσ : ∀ s : base.dust, s.val ∉ base.quotientDomain := by
    intro s
    exact (Set.ext_iff.mp hdust s.val).mp s.property
  have hmiss : ∀ x ∈ base.quotientDomain ∩ P.punctured,
      ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs), x ∉ range γ.val := by
    intro x hx
    apply Q.avoids_domain hU hG hdust hπ hclosed hsurj hr x hx.1
    intro hxi
    exact hinfty (hxi ▸ subset_closure hx.2.1)
  have havoid : ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior J),
      pathHitProbability (Q.law.map (f := Subtype.val) measurable_subtype_coe.aemeasurable) x = 0 := by
    intro x hx
    have hxU : x ∈ base.quotientDomain := by
      rw [hfront] at hx
      obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hx
      rw [← he ⟨_, hboundary z hz⟩]
      exact (base.domainEquiv ⟨_, hboundary z hz⟩).property
    have hz := Q.avoids_domain hU hG hdust hπ hclosed hsurj hr x hxU
      (fun hxi => hinfty (hxi ▸ frontier_subset_closure hx))
    rw [Q.hit_probability]
    apply ae_iff.mp at hz
    simpa only [not_not] using hz
  have hmissFree : ∀ x ∈ ((π '' base.physicalDomainᶜ) \ range (fun s : base.dust => s.val)) ∩ P.punctured,
      ∀ᵐ γ : P.diskArcs ∂(Q.law.map P.continuous_arcMap.measurable.aemeasurable : Measure P.diskArcs),
        P.map x ∉ range γ.val := by
    rintro x ⟨⟨⟨p, hp, rfl⟩, hx⟩, _⟩
    exact (hx ⟨⟨π p, hdust.symm ▸ hbad p hp⟩, rfl⟩).elim
  have hwp : ∀ s : base.dust, s ≠ singular →
      (Q.law : Measure Q.arcs) {γ | s.val ∈ range γ.val} ≤ Q.baseHitWeight s := by
    intro s hs
    apply Q.baseHitWeight_le s
    exact fun heq => hs (Subtype.ext heq)
  obtain ⟨M, hM, hbdM, hbM, hinfM, hMJ, u, N, hN, hNM, hNb, _, hbudget,
    ρ, v, hρ, hcap, hfiber, hv, hproj, V, _, hmem, γ, hγ, hV⟩ :=
    exists_gated_small_inner_mean_exclusion hsch hsep hcoarea base.domainEquiv hG hU hdense
      P.punctured_open (fun s : base.dust => s.val) hσ singular
      (by exact fun h => h.2 rfl) base.basePoint π hπ hclosed hsurj hr he
      (by rintro _ ⟨p, hp, rfl⟩; exact hbad p hp)
      (fun h => hinfty (subset_closure h.1)) Q.arcs (fun γ hγ => (Q.terminal hγ).1)
      Q.law (Q.base_finite_length he) Q.density Q.density_measurable (Q.base_occupation he)
      Q.density_energy_finite P.diskArcs P.compact P.terminal P.map P.arcMap
      P.continuous_arcMap.measurable P.arcMap_eq B hB (P.nonzero hbJ) (P.norm_le hbJ)
      (P.injective_arcs hbJ Q.terminal) (P.injective_punctured hbJ) hmiss hmissFree
      (CenteredTerminalFamily.endpoint Q.terminal) Q.base_hit_square_summable Q.baseHitWeight
      Q.baseHitWeight_square_finite hwp hR C hfront hbJ P.map_eq D Q.terminal havoid
      O hO hHO hOG hregion Subset.rfl (fun x hx => P.norm_lt hbJ x hx.1)
      F₀ hF₀ hF₀m hF₀smooth c r houtside hd₀ hgate Q.base_small
  have hρC : ρ ∈ Icc (0 : ℝ) C.width := ⟨hρ.1.le, hρ.2.trans D.width_le⟩
  have hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk ρ)) ⊆ base.physicalDomain := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (C.parametrization ρ hρC).boundary.symm ▸ hz
    have h := (γ ⟨t, ht⟩).property
    rwa [hγ] at h
  let γ₀ := sourceCircuit (C.curve ρ) (C.parametrization ρ hρC).smooth.continuous
    (fun t => hbd (mem_image_of_mem _ ((C.parametrization ρ hρC).mem_frontier t)))
  have hγeq : γ = γ₀ := by
    ext t
    exact hγ t
  have hexclusion : MeanExclusionWitness N F₀ hF₀ c r R := {
    disk := C.disk ρ
    curve := C.curve ρ
    regular := C.parametrization ρ hρC
    boundary := hbd
    mask := hcap
    fiber := by simpa only [hNb] using hfiber
    lift := v
    smooth_lift := hv
    projects := hproj
    member := by simpa only [hV, hγeq] using hmem }
  exact ⟨{
    centered := P, mask := M, closed := hM, frontier := hbdM, target_mem := hbM,
    infty_not_mem := hinfM, inner := hMJ, mean := u, coordinate := N, graph := hN,
    mask_eq := hNM, singular_eq := congrArg Subtype.val hNb, budget := hbudget,
    exclusion := hexclusion }⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_NestedCollarMeanExclusion
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single physical chart bound works throughout the nested collars. The
actual recursive law then supplies the small compact law at every sufficiently
deep collar, with the prescribed start gate and the resulting mean exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem RecursiveCodeLaw.eventually_gated_collar_mean
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea) (hcollar : SmoothRegularJordanCollars)
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    (L : RecursiveCodeLaw base π Flags ω)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (hp : L.data.target ≠ π OnePoint.infty)
    {g : ℂ → ℝ≥0∞}
    (D : ℕ → WeightedCollar base.physicalDomain π base.dust L.data.target g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 L.data.target, ∃ k : ℕ,
      ∀ n ≥ k, closure (D n).region ⊆ V)
    (hanchor : Disjoint base.anchor (closure (D 0).region))
    (hfinite : OnePoint.infty ∉ closure (D 0).region)
    (hcontours : ∀ n, L.data.gateContours n = frontier (D n).region)
    (f : base.quotientDomain → Sphere) (hf : Continuous f) (W : Set Sphere)
    (hgate : ∀ n, L.data.gateSets n = Subtype.val '' (f ⁻¹' closure W))
    (F₀ : ℂ → ℂ)
    (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain))
    (hF₀m : Measurable F₀)
    (hF₀smooth : ContDiffOn ℝ (⊤ : ℕ∞) F₀
      (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain))
    (hF : ∀ x : base.quotientDomain, f x ∈ closure W →
      f x = (F₀ (finiteCoord (physicalValue base.domainEquiv base.basePoint x.val)) : Sphere))
    (c : ℂ) (r : ℝ≥0)
    (houtside : ∀ z : ℂ, (z : Sphere) ∈ base.physicalDomain → (r : ℝ) < dist (F₀ z) c)
    {R d₀ : ℝ} (hR : 0 ≤ R) (hd₀ : 0 < d₀)
    (hgap : ∀ z : ℂ, (z : Sphere) ∈ closure W →
      d₀ ≤ Metric.infDist z (Metric.closedBall c (r : ℝ))) :
    ∃ B : ℝ≥0, ∀ᶠ n in atTop,
      ∃ J : ℂ ≃ₜ ℂ, (D n).region = ((↑) : ℂ → Sphere) '' jordanInterior J ∧
      ∃ Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J)
        (meanBudgetTolerance B R (d₀ / 4)),
        Nonempty (RecursiveMeanOutput hsch Q F₀ hF₀ c r R (d₀ / 4)) := by
  have hanti : Antitone (fun n => (D n).region) :=
    antitone_nat_of_succ_le (fun n => subset_closure.trans (hnest n))
  have hintersection : (⋂ n, closure (D n).region) ⊆ {L.data.target} := by
    intro x hx
    by_contra hxp
    have hpx : L.data.target ≠ x := fun h => hxp h.symm
    obtain ⟨k, hk⟩ := hshrink {x}ᶜ (isClosed_singleton.isOpen_compl.mem_nhds hpx)
    exact hk k le_rfl (mem_iInter.mp hx k) rfl
  have hdisj : Disjoint base.quotientDomain base.dust := by
    rw [hdust]
    exact disjoint_compl_right
  obtain ⟨B, hB⟩ := finiteCoord_lipschitz_quotient_neighborhood π hπ base.physicalDomain
    (D 0).region ((D 0).infty_notMem_closure_region hπ hsurj hr)
  refine ⟨B, ?_⟩
  have hε : 0 < meanBudgetTolerance B R (d₀ / 4) :=
    meanBudgetTolerance_pos B hR (by positivity)
  filter_upwards [L.eventually_compact_reduction hselect harcs hU hG hπ hdisj
    (fun n => (D n).region) (fun n => (D n).isOpen_region hπ hclosed hsurj hr)
    (fun n => hanchor.mono_right ((hanti (Nat.zero_le n)).trans subset_closure))
    (fun n => (D n).point_mem_region hsurj hp) hanti hintersection hε] with n hn
  have hboundary : ∀ z ∈ frontier (jordanInterior (D n).disk),
      (z : Sphere) ∈ base.physicalDomain :=
    fun z hz => ((D n).level_good z ((D n).frontier_level hz)).1
  obtain ⟨J, hJ⟩ := exists_jordan_quotient_collar hsch base.physicalDomain π hπ hclosed
    hsurj hr (D n).disk hboundary
    (fun hx => hfinite (closure_mono (hanti (Nat.zero_le n)) hx))
  obtain ⟨C⟩ := (D n).exists_regular_inward_collar hcollar
  have hbJ : L.data.target ∈ ((↑) : ℂ → Sphere) '' jordanInterior J :=
    hJ ▸ (D n).point_mem_region hsurj hp
  have hinfty : π OnePoint.infty ∉ closure (((↑) : ℂ → Sphere) '' jordanInterior J) := by
    rw [← hJ]
    exact (D n).infty_notMem_closure_region hπ hsurj hr
  obtain ⟨Q⟩ := hn
  let Q' : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J)
      (meanBudgetTolerance B R (d₀ / 4)) := hJ ▸ Q
  have hBn : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹'
          ((((↑) : ℂ → Sphere) '' jordanInterior J) \ {L.data.target}))) := by
    apply hB.mono
    apply image_mono
    intro z hz
    have hzn : π (z : Sphere) ∈ (D n).region := by
      change π (z : Sphere) ∈ π '' (((↑) : ℂ → Sphere) '' jordanInterior (D n).disk)
      rw [hJ]
      exact hz.2.1
    exact ⟨hz.1, hanti (Nat.zero_le n) hzn⟩
  have hCclosed : ∀ k, IsClosed (L.data.gateContours k) := by
    intro k
    rw [hcontours]
    exact isClosed_frontier
  have hCK : ∀ k, IsClosed (L.data.gateContours k ∩ L.data.gateSets k) := by
    intro k
    rw [hcontours, hgate]
    apply isClosed_contour_gate isClosed_frontier ?_ hf isClosed_closure
    intro x hx
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ :=
      (D k).frontier_region_subset hπ ((D k).isOpen_region hπ hclosed hsurj hr) hx
    rw [← he ⟨(z : Sphere), ((D k).level_good z hz).1⟩]
    exact (base.domainEquiv _).property
  have hstart := Q'.physical_start_distance_of_inter_closed hCclosed hCK n
    (by rw [← hJ, hcontours]; exact Subset.rfl) f W (hgate n) F₀ hF c r d₀ hgap
  refine ⟨J, hJ, Q', ?_⟩
  exact Q'.exists_mean_exclusion hsch hsep hcoarea hG hU hdense hdust hπ hclosed hsurj hr he
    hbad C hJ hbJ hinfty B hBn hR hd₀
    (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain) (hG.preimage OnePoint.continuous_coe)
    hboundary (fun _ hz => hz) F₀ hF₀ hF₀m hF₀smooth c r houtside hstart

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionMeanExclusion
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual marked-component protrusion and its recursive law produce
an inner mean exclusion. All map regularity and distance hypotheses are
derived from the conformal limit and the separated protrusion balls. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem RecursiveCodeLaw.eventually_protrusion_mean_oai
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea) (hcollar : SmoothRegularJordanCollars)
    (hselect : BorelPathRelationSelection)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    (L : RecursiveCodeLaw base π Flags ω)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (hp : L.data.target ≠ π OnePoint.infty)
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
    (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
    (s : S) (hqs : π q = σ s)
    (hseparated : Disjoint (Metric.closedBall T.center (2 * T.radius))
      (Metric.closedBall (A.center s) (A.radius s)))
    {R : ℝ} (hR : 0 ≤ R)
    {g : ℂ → ℝ≥0∞}
    (D : ℕ → WeightedCollar base.physicalDomain π base.dust L.data.target g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 L.data.target, ∃ k : ℕ,
      ∀ n ≥ k, closure (D n).region ⊆ V)
    (hanchor : Disjoint base.anchor (closure (D 0).region))
    (hfinite : OnePoint.infty ∉ closure (D 0).region)
    (hcontours : ∀ n, L.data.gateContours n = frontier (D n).region)
    (hgates : ∀ n, L.data.gateSets n = Subtype.val ''
      ((quotientNormalizedMap base.domainEquiv A.function) ⁻¹' closure T.openGate)) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∃ (F₀ : ℂ → ℂ) (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)),
        EqOn F₀ A.function (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain) ∧
        ∃ B : ℝ≥0, ∀ᶠ n in atTop,
          ∃ J : ℂ ≃ₜ ℂ, (D n).region = ((↑) : ℂ → Sphere) '' jordanInterior J ∧
          ∃ Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J)
            (meanBudgetTolerance B R (δ / 4)),
            Nonempty (RecursiveMeanOutput hsch Q F₀ hF₀ (A.center s)
              ⟨A.radius s, (A.bounds s).2.1⟩ R (δ / 4)) := by
  obtain ⟨δ, hδ, hgap⟩ := T.uniform_gate_gap hseparated
  obtain ⟨F₀, hF₀m, hF₀s, hEq⟩ := exists_normalized_source_representative hG A.function A.conformal.1
  have hf := quotientNormalizedMap_continuous base.domainEquiv A.function A.conformal.1
  have hmap := quotientNormalizedMap_eq_of_eqOn base.domainEquiv hEq
  have hgate : ∀ x : base.quotientDomain,
      quotientNormalizedMap base.domainEquiv A.function x ∈ closure T.openGate →
      quotientNormalizedMap base.domainEquiv A.function x =
        (F₀ (finiteCoord (physicalValue base.domainEquiv base.basePoint x.val)) : Sphere) := by
    rw [← hmap]
    exact quotientNormalizedMap_finite_gate base.domainEquiv F₀ base.basePoint
      T.infinity_notMem_closure_openGate
  have hout : ∀ z : ℂ, (z : Sphere) ∈ base.physicalDomain →
      A.radius s < dist (F₀ z) (A.center s) := by
    intro z hz
    rw [hEq hz]
    exact E.source_outside_marked_disk hr hq hqs z hz
  refine ⟨δ, hδ, F₀, hF₀s.continuousOn, hEq, ?_⟩
  exact L.eventually_gated_collar_mean hsch hsep hcoarea hcollar hselect harcs hG hU
    hdense hdust hπ hclosed hsurj hr he hbad hp D hnest hshrink hanchor hfinite hcontours
    (quotientNormalizedMap base.domainEquiv A.function) hf T.openGate hgates F₀
    hF₀s.continuousOn hF₀m hF₀s hgate (A.center s) ⟨A.radius s, (A.bounds s).2.1⟩
    hout hR hδ hgap

end CircleDomainRigidity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CircleDomainRigidity.RecursiveCodeLaw.eventually_protrusion_mean_oai.{u_1} := @OAI.CircleDomainRigidity.RecursiveCodeLaw.eventually_protrusion_mean_oai.{u_1}
