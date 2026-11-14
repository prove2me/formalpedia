-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_compact_equal_leaf_shearing_sequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:50:33.113646+00:00
-- url     : https://prove2.me/submissions/2bcef8af-2943-4ef6-9079-ec049a89f1a1

import Mathlib
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke044

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafPairSelection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous compact returns on equal root leaves

The all-radius good-set estimate controls both exceptional time sets
with the same leaf measure. A third small forbidden set can be removed
while retaining a common return time.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma exists_common_point_outside_forbidden
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (W L R F : Set Y)
    (hbudget : ν (W \ L) + ν (W \ R) + ν (W ∩ F) < ν W) :
    ∃ t ∈ W, t ∈ L ∧ t ∈ R ∧ t ∉ F := by
  by_contra h
  have hcover : W ⊆ ((W \ L) ∪ (W \ R)) ∪ (W ∩ F) := by
    intro t ht
    by_cases hL : t ∈ L
    · by_cases hR : t ∈ R
      · exact Or.inr ⟨ht, by_contra fun hF => h ⟨t, ht, hL, hR, hF⟩⟩
      · exact Or.inl (Or.inr ⟨ht, hR⟩)
    · exact Or.inl (Or.inl ⟨ht, hL⟩)
  have hle : ν W ≤ ν (W \ L) + ν (W \ R) + ν (W ∩ F) :=
    (measure_mono hcover).trans ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl))
  exact hbudget.not_ge hle

theorem exists_simultaneous_root_return
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (K G : Set (X n)) (c : ℝ≥0∞)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (closedBall 0 r))
    (x y : X n) (hx : x ∈ G) (hy : y ∈ G)
    (heq : intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ y)
    (r : ℝ) (hr : 0 < r) (F : Set ℝ)
    (hbudget : (c + c) * intrinsicRootLeaf hij μ x (closedBall 0 r) +
      intrinsicRootLeaf hij μ x (closedBall 0 r ∩ F) <
        intrinsicRootLeaf hij μ x (closedBall 0 r)) :
    ∃ t ∈ closedBall (0 : ℝ) r,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∈ K ∧
      rightAction y (Matrix.SpecialLinearGroup.transvection hij t) ∈ K ∧ t ∉ F := by
  let ν := intrinsicRootLeaf hij μ x
  let W := closedBall (0 : ℝ) r
  have hleft : ν (W \ rootHitTimes hij K x) ≤ c * ν W := by
    have he : W \ rootHitTimes hij K x = rootHitTimes hij Kᶜ x ∩ W := by
      ext t
      simp only [Set.mem_sdiff, mem_inter_iff, rootHitTimes, mem_ofPred_eq, mem_compl_iff]
      tauto
    rw [he]
    exact hgood x hx r hr
  have hright : ν (W \ rootHitTimes hij K y) ≤ c * ν W := by
    have he : W \ rootHitTimes hij K y = rootHitTimes hij Kᶜ y ∩ W := by
      ext t
      simp only [Set.mem_sdiff, mem_inter_iff, rootHitTimes, mem_ofPred_eq, mem_compl_iff]
      tauto
    rw [he]
    change intrinsicRootLeaf hij μ x _ ≤ c * intrinsicRootLeaf hij μ x _
    rw [heq]
    exact hgood y hy r hr
  apply exists_common_point_outside_forbidden ν W (rootHitTimes hij K x)
    (rootHitTimes hij K y) F
  calc
    ν (W \ rootHitTimes hij K x) + ν (W \ rootHitTimes hij K y) + ν (W ∩ F)
        ≤ c * ν W + c * ν W + ν (W ∩ F) :=
      add_le_add (add_le_add hleft hright) le_rfl
    _ = (c + c) * ν W + ν (W ∩ F) := by rw [add_mul]
    _ < ν W := hbudget

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingAnnulus
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Annular simultaneous returns

Small mass near the root origin excludes the central portion of a
shearing interval. The relative maximal bound then supplies simultaneous
compact returns in the remaining annulus, as in EKL Section 4.5.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma scaling_preimage_closedBall (s r : ℝ) (hs : 0 < s) :
    (Homeomorph.mulLeft₀ s hs.ne') ⁻¹' closedBall 0 r = closedBall 0 (r / s) := by
  ext t
  simp only [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero,
    Homeomorph.coe_mulLeft₀, abs_mul, abs_of_pos hs]
  rw [le_div_iff₀ hs, mul_comm]

lemma normalized_scaling_closedBall (ν : Measure ℝ) (s r : ℝ) (hs : 0 < s) :
    anchorNormalize (ν.map (Homeomorph.mulLeft₀ s hs.ne')) (ball 0 1)
      (closedBall 0 r) = (ν (ball 0 (1 / s)))⁻¹ * ν (closedBall 0 (r / s)) := by
  change (ν.map (Homeomorph.mulLeft₀ s hs.ne') (ball 0 1))⁻¹ *
    ν.map (Homeomorph.mulLeft₀ s hs.ne') (closedBall 0 r) = _
  rw [Measure.map_apply (Homeomorph.mulLeft₀ s hs.ne').measurable isOpen_ball.measurableSet,
    Measure.map_apply (Homeomorph.mulLeft₀ s hs.ne').measurable isClosed_closedBall.measurableSet,
    realScaling_preimage_ball s 1 hs, scaling_preimage_closedBall s r hs]

theorem normalized_small_ball_gives_annulus
    (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (s ρ : ℝ) (hs : 0 < s)
    (hpos : ν (ball 0 (1 / s)) ≠ 0) (a : ℝ≥0∞)
    (hsmall : anchorNormalize (ν.map (Homeomorph.mulLeft₀ s hs.ne')) (ball 0 1)
      (closedBall 0 ρ) < a) :
    ν (closedBall 0 (ρ / s)) < a * ν (closedBall 0 (1 / s)) := by
  rw [normalized_scaling_closedBall ν s ρ hs] at hsmall
  have hfinite : ν (ball 0 (1 / s)) ≠ ∞ := measure_ball_lt_top.ne
  have h := ENNReal.mul_lt_mul_left hpos hfinite hsmall
  rw [mul_right_comm (ν (ball 0 (1 / s)))⁻¹, ENNReal.inv_mul_cancel hpos hfinite, one_mul] at h
  exact h.trans_le (mul_le_mul' le_rfl (measure_mono ball_subset_closedBall))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_AffineTimeSelection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Synchronizing the shearing time windows

Affine changes of time with slope at least one half at most double
Lebesgue measure. This yields the loss of eight in EKL (2006), Lemma 4.5.
A finite family of bad windows can then be avoided simultaneously.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal BigOperators

namespace DukePrimeDegree

lemma volume_real_affine_preimage (a b : ℝ) (ha : 0 < a) (E : Set ℝ) :
    volume.real ((fun t => b + a * t) ⁻¹' E) = a⁻¹ * volume.real E := by
  have he : (fun t => b + a * t) ⁻¹' E =
      (fun t => a * t) ⁻¹' ((fun t => b + t) ⁻¹' E) := rfl
  rw [measureReal_def, he, Real.volume_preimage_mul_left ha.ne', measure_preimage_add,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr ha)]
  rfl

lemma affine_bad_time_bound (a b T : ℝ) (ha : 1 / 2 ≤ a)
    (E : Set ℝ) (hfinite : volume E ≠ ∞) :
    volume.real (Ioc 0 T ∩ ((fun t => b + a * t) ⁻¹' E)) ≤ 2 * volume.real E := by
  have hapos : 0 < a := by linarith
  have hpre : volume ((fun t => b + a * t) ⁻¹' E) ≠ ∞ := by
    change volume ((fun t => a * t) ⁻¹' ((fun t => b + t) ⁻¹' E)) ≠ ∞
    rw [Real.volume_preimage_mul_left hapos.ne', measure_preimage_add]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
  calc
    volume.real (Ioc 0 T ∩ ((fun t => b + a * t) ⁻¹' E))
        ≤ volume.real ((fun t => b + a * t) ⁻¹' E) := measureReal_mono inter_subset_right hpre
    _ = a⁻¹ * volume.real E := volume_real_affine_preimage a b hapos E
    _ ≤ 2 * volume.real E := by
      apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
      apply (inv_le_comm₀ hapos (by norm_num : (0 : ℝ) < 2)).mpr
      norm_num
      exact ha

lemma ekl_affine_time_mem (T θ η τ : ℝ) (hT : 0 < T)
    (hθlo : 4 * T ≤ θ) (hθhi : θ ≤ 6 * T) (hη : η = 0 ∨ η = 1)
    (hτ : τ ∈ Ioc 0 T) : (θ + (2 - η) * τ) / 2 ∈ Ioc 0 (4 * T) := by
  rcases hη with rfl | rfl <;> constructor <;> nlinarith [hτ.1, hτ.2]

/-- The precise affine-time loss used to transfer the small-ball set
from the interval of length `4*T` to the shearing interval of length `T`. -/
theorem ekl_pullback_bad_time_bound (T θ η ε : ℝ)
    (hη : η = 0 ∨ η = 1) (E : Set ℝ) (hE : E ⊆ Ioc 0 (4 * T))
    (hbad : volume.real E ≤ ε * (4 * T)) :
    volume.real (Ioc 0 T ∩
      ((fun τ => (θ + (2 - η) * τ) / 2) ⁻¹' E)) ≤ 8 * ε * T := by
  have ha : (1 : ℝ) / 2 ≤ (2 - η) / 2 := by
    rcases hη with rfl | rfl <;> norm_num
  have hfinite : volume E ≠ ∞ :=
    measure_ne_top_of_subset hE (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have heq : (fun τ => (θ + (2 - η) * τ) / 2) =
      (fun τ => θ / 2 + ((2 - η) / 2) * τ) := by
    funext τ
    ring
  rw [heq]
  have h := affine_bad_time_bound ((2 - η) / 2) (θ / 2) T ha E hfinite
  nlinarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingDiagonal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two-coordinate shearing diagonal

In the row-lattice convention the weights are `-1` at the root's row,
`+1` at its column, and zero elsewhere. Backward right translation
contracts root time by `exp (-2*t)`. The corresponding relative return
matrix has a fixed diagonal difference, quadratic coefficient growing
by `exp (2*t)`, and other shearing coefficients growing by `exp t`.
These are the rates in EKL (2006), Lemma 4.6.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootPairWeights_row {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    rootPairWeights i j i = -1 := by simp [rootPairWeights, hij]

lemma rootPairWeights_col {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    rootPairWeights i j j = 1 := by simp [rootPairWeights, hij.symm]

lemma rootPairWeights_other {n : ℕ} {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    rootPairWeights i j k = 0 := by simp [rootPairWeights, hki, hkj]

lemma rootPairConjugate_diagonal {n : ℕ} (i j r : Fin n) (t : ℝ) (g : G n) :
    (rootPairConjugate i j t g).val r r = g.val r r := by
  simp [rootPairConjugate, rootPairFlow, conjugation_entry]

lemma rootPairConjugate_quadratic {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (t : ℝ) (g : G n) :
    (rootPairConjugate i j t g).val j i = Real.exp (2 * t) * g.val j i := by
  simp only [rootPairConjugate, rootPairFlow, conjugation_entry,
    rootPairWeights_row hij, rootPairWeights_col hij]
  norm_num

lemma rootPairConjugate_row {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (t : ℝ) (g : G n) :
    (rootPairConjugate i j t g).val j k = Real.exp t * g.val j k := by
  simp [rootPairConjugate, rootPairFlow, conjugation_entry,
    rootPairWeights_col hij, rootPairWeights_other hki hkj]

lemma rootPairConjugate_col {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (t : ℝ) (g : G n) :
    (rootPairConjugate i j t g).val k i = Real.exp t * g.val k i := by
  simp [rootPairConjugate, rootPairFlow, conjugation_entry,
    rootPairWeights_row hij, rootPairWeights_other hki hkj]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingReturnGeometry
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Relative matrices after diagonal and root translation

These identities track the right-action convention in the return-pair
argument. After simultaneous root translation by `t`, the relative
matrix is conjugated by the root element at `-t`.
-/

noncomputable section
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootPairConjugate_rightAction {n : ℕ} (i j : Fin n)
    (x : X n) (g : G n) (τ : ℝ) :
    rightAction (rightAction x (rootPairFlow i j (-τ))) (rootPairConjugate i j τ g) =
      rightAction (rightAction x g) (rootPairFlow i j (-τ)) := by
  simp only [rootPairConjugate, rootPairFlow, diagonalOneParameter_neg,
    rightAction_mul, ← mul_assoc, inv_mul_cancel, one_mul]

lemma rootConjugate_rightAction {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x : X n) (g : G n) (t : ℝ) :
    rightAction (rightAction x (Matrix.SpecialLinearGroup.transvection hij t))
      (Matrix.SpecialLinearGroup.transvection hij (-t) * g *
        Matrix.SpecialLinearGroup.transvection hij t) =
      rightAction (rightAction x g) (Matrix.SpecialLinearGroup.transvection hij t) := by
  have hcancel : Matrix.SpecialLinearGroup.transvection hij t *
      Matrix.SpecialLinearGroup.transvection hij (-t) = 1 := by
    rw [← Matrix.SpecialLinearGroup.transvection_add, add_neg_cancel]
    simp
  simp only [rightAction_mul, ← mul_assoc, hcancel, one_mul]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootShearing
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Polynomial shearing along a root subgroup

The exact matrix formula is the algebraic part of the low-entropy
argument: conjugation by a root unipotent is quadratic in its parameter.
The exceptional case is precisely the centralizer, and commuting with a
single nonzero root element already characterizes that case.
-/

open scoped BigOperators Classical
open Filter

namespace DukePrimeDegree

open PrimeDegreePackets

/-- The centralizer of a root element at parameter one is the
centralizer of the full real root subgroup. -/
theorem commutes_root_one_iff_all {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g ↔
      ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
        Matrix.SpecialLinearGroup.transvection hij t * g := by
  constructor
  · intro h t
    obtain ⟨hcol, hrow, hdiag⟩ := (commutes_root_one_iff hij g).mp h
    ext r s
    simp only [root_mul_entry, root_left_mul_entry]
    by_cases hr : r = i <;> by_cases hs : s = j
    · subst r
      subst s
      simp only [ite_true, if_true, hdiag, mul_comm]
    · subst r
      simp [hs, hrow s hs]
    · subst s
      simp [hr, hcol r hr]
    · simp [hr, hs]
  · exact fun h => h 1

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingKappa
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A scale for noncentral return matrices

The scale is the maximum of the diagonal difference and a homogeneous
off-diagonal size. The latter uses the square root of the quadratic
coefficient and a finite sum of the other linear coefficients. This
equivalent choice of norm gives exactly the two scaling regimes used in
EKL (2006), Lemma 4.6.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootShearingOffDiagonalSize_nonneg {n : ℕ} (i j : Fin n) (g : G n) :
    0 ≤ rootShearingOffDiagonalSize i j g := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> positivity

lemma rootShearingOffDiagonalSize_row_bound {n : ℕ} {i j k : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (g : G n) :
    |g.val j k| ≤ rootShearingOffDiagonalSize i j g := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun k => if k = i ∨ k = j then (0 : ℝ) else |g.val j k| + |g.val k i|)
    (fun k _ => by split_ifs <;> positivity) (Finset.mem_univ k)
  simp only [hki, hkj, false_or, ite_false, if_false] at h
  exact (le_add_of_nonneg_right (abs_nonneg _)).trans h

lemma rootShearingOffDiagonalSize_col_bound {n : ℕ} {i j k : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (g : G n) :
    |g.val k i| ≤ rootShearingOffDiagonalSize i j g := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun k => if k = i ∨ k = j then (0 : ℝ) else |g.val j k| + |g.val k i|)
    (fun k _ => by split_ifs <;> positivity) (Finset.mem_univ k)
  simp only [hki, hkj, false_or, ite_false, if_false] at h
  exact (le_add_of_nonneg_left (abs_nonneg _)).trans h

lemma rootShearingMovingSize_nonneg {n : ℕ} (i j : Fin n) (g : G n) :
    0 ≤ rootShearingMovingSize i j g :=
  add_nonneg (Real.sqrt_nonneg _) (rootShearingOffDiagonalSize_nonneg i j g)

lemma rootShearingKappa_nonneg {n : ℕ} (i j : Fin n) (g : G n) :
    0 ≤ rootShearingKappa i j g :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem rootShearingKappa_pos_of_noncentral {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g) :
    0 < rootShearingKappa i j g := by
  by_contra hn
  have hk : rootShearingKappa i j g ≤ 0 := le_of_not_gt hn
  have ha : |g.val j j - g.val i i| ≤ 0 := (le_max_left _ _).trans hk
  have hb : rootShearingMovingSize i j g ≤ 0 := (le_max_right _ _).trans hk
  have hoff := rootShearingOffDiagonalSize_nonneg i j g
  have hsqrt := Real.sqrt_nonneg |g.val j i|
  have hsqrtzero : Real.sqrt |g.val j i| = 0 := by
    dsimp [rootShearingMovingSize] at hb
    linarith
  have hji : g.val j i = 0 := abs_eq_zero.mp ((Real.sqrt_eq_zero (abs_nonneg _)).mp hsqrtzero)
  have hoffzero : rootShearingOffDiagonalSize i j g = 0 := by
    dsimp [rootShearingMovingSize] at hb
    linarith
  have hdiag : g.val i i = g.val j j := by
    have hz := abs_eq_zero.mp (le_antisymm ha (abs_nonneg _))
    linarith
  apply hnot
  apply (commutes_root_one_iff_all hij g).mp
  apply (commutes_root_one_iff hij g).mpr
  refine ⟨?_, ?_, hdiag⟩
  · intro k hki
    by_cases hkj : k = j
    · simpa only [hkj] using hji
    · exact abs_eq_zero.mp (le_antisymm
        (hoffzero ▸ rootShearingOffDiagonalSize_col_bound hki hkj g) (abs_nonneg _))
  · intro k hkj
    by_cases hki : k = i
    · simpa only [hki] using hji
    · exact abs_eq_zero.mp (le_antisymm
        (hoffzero ▸ rootShearingOffDiagonalSize_row_bound hki hkj g) (abs_nonneg _))

theorem rootShearingMovingSize_conjugate {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (t : ℝ) (g : G n) :
    rootShearingMovingSize i j (rootPairConjugate i j t g) =
      Real.exp t * rootShearingMovingSize i j g := by
  have hquad : Real.sqrt |(rootPairConjugate i j t g).val j i| =
      Real.exp t * Real.sqrt |g.val j i| := by
    rw [rootPairConjugate_quadratic hij, abs_mul, abs_of_pos (Real.exp_pos _),
      Real.sqrt_mul (Real.exp_pos _).le]
    have he : Real.exp (2 * t) = (Real.exp t) ^ 2 := by
      rw [show 2 * t = t + t by ring, Real.exp_add, pow_two]
    rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos t)]
  have hoff : rootShearingOffDiagonalSize i j (rootPairConjugate i j t g) =
      Real.exp t * rootShearingOffDiagonalSize i j g := by
    unfold rootShearingOffDiagonalSize
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = i ∨ k = j
    · simp only [hk, ite_true, if_true, mul_zero]
    · have hki : k ≠ i := fun h => hk (Or.inl h)
      have hkj : k ≠ j := fun h => hk (Or.inr h)
      simp only [hk, ite_false, if_false, rootPairConjugate_row hij hki hkj,
        rootPairConjugate_col hij hki hkj, abs_mul, abs_of_pos (Real.exp_pos t), mul_add]
  simp only [rootShearingMovingSize, hquad, hoff, mul_add]

theorem rootShearingKappa_conjugate {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (t : ℝ) (g : G n) :
    rootShearingKappa i j (rootPairConjugate i j t g) =
      max |g.val j j - g.val i i| (Real.exp t * rootShearingMovingSize i j g) := by
  simp only [rootShearingKappa, rootPairConjugate_diagonal,
    rootShearingMovingSize_conjugate hij]

theorem continuous_rootShearingKappa {n : ℕ} (i j : Fin n) :
    Continuous (rootShearingKappa i j) := by
  have hc (r s : Fin n) : Continuous (fun g : G n => g.val r s) := by fun_prop
  unfold rootShearingKappa rootShearingMovingSize rootShearingOffDiagonalSize
  apply Continuous.max ((hc j j).sub (hc i i)).abs
  apply Continuous.add ((hc j i).abs.sqrt)
  apply continuous_finsetSum
  intro k _
  split_ifs
  · exact continuous_const
  · exact (hc j k).abs.add (hc k i).abs

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingCoefficientBounds
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bounds on the selected shearing interval

The logarithmic scale controls every coefficient of the quadratic
conjugation formula. A bound on `|t| * κ` therefore gives a uniform
matrix-displacement bound on the whole symmetric interval.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootShearingKappa_diagonal_bound {n : ℕ} (i j : Fin n) (g : G n) :
    |g.val j j - g.val i i| ≤ rootShearingKappa i j g := le_max_left _ _

lemma rootShearingKappa_quadratic_bound {n : ℕ} (i j : Fin n) (g : G n) :
    |g.val j i| ≤ (rootShearingKappa i j g) ^ 2 := by
  have hs : Real.sqrt |g.val j i| ≤ rootShearingKappa i j g :=
    (le_add_of_nonneg_right (rootShearingOffDiagonalSize_nonneg i j g)).trans (le_max_right _ _)
  nlinarith [Real.sq_sqrt (abs_nonneg (g.val j i)), Real.sqrt_nonneg |g.val j i|,
    rootShearingKappa_nonneg i j g]

lemma rootShearingKappa_offDiagonal_bound {n : ℕ} (i j : Fin n) (g : G n) :
    rootShearingOffDiagonalSize i j g ≤ rootShearingKappa i j g :=
  (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans (le_max_right _ _)

lemma rootShearingKappa_row_bound {n : ℕ} {i j k : Fin n} (g : G n)
    (hkj : k ≠ j) (hsmall : rootShearingKappa i j g ≤ 1) :
    |g.val j k| ≤ rootShearingKappa i j g := by
  by_cases hki : k = i
  · subst k
    have hb := rootShearingKappa_quadratic_bound i j g
    nlinarith [rootShearingKappa_nonneg i j g]
  · exact (rootShearingOffDiagonalSize_row_bound hki hkj g).trans
      (rootShearingKappa_offDiagonal_bound i j g)

lemma rootShearingKappa_col_bound {n : ℕ} {i j k : Fin n} (g : G n)
    (hki : k ≠ i) (hsmall : rootShearingKappa i j g ≤ 1) :
    |g.val k i| ≤ rootShearingKappa i j g := by
  by_cases hkj : k = j
  · subst k
    have hb := rootShearingKappa_quadratic_bound i j g
    nlinarith [rootShearingKappa_nonneg i j g]
  · exact (rootShearingOffDiagonalSize_col_bound hki hkj g).trans
      (rootShearingKappa_offDiagonal_bound i j g)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingRegimes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two exponential shearing regimes

Over the logarithmic window, the inverse shearing scale is either fixed
or decreases exponentially. Clamping the moving coefficient below its
inactive threshold gives a single logarithmic parameter in `[4*T,5*T]`,
including when the original moving coefficient vanishes.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree

lemma max_fixed_moving_clamp (A U T τ : ℝ) (hA : 0 ≤ A) (hU : 0 ≤ U)
    (hτ : τ ∈ Icc 0 T) :
    max A (Real.exp τ * U) =
      max (max A U) (Real.exp τ * max U (max A U * Real.exp (-T))) := by
  let κ := max A U
  have he : 1 ≤ Real.exp τ := Real.one_le_exp_iff.mpr hτ.1
  have hκ : 0 ≤ κ := hA.trans (le_max_left _ _)
  have hκle : κ ≤ max A (Real.exp τ * U) := by
    apply max_le (le_max_left _ _)
    exact (by nlinarith : U ≤ Real.exp τ * U).trans (le_max_right _ _)
  have hscaled : Real.exp τ * (κ * Real.exp (-T)) ≤ κ := by
    have he' : Real.exp (τ - T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hτ.2])
    calc
      Real.exp τ * (κ * Real.exp (-T)) = κ * Real.exp (τ - T) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
      _ ≤ κ := by nlinarith [Real.exp_pos (τ - T)]
  apply le_antisymm
  · apply max_le
    · exact (le_max_left A U).trans (le_max_left _ _)
    · exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos τ).le).trans
        (le_max_right _ _)
  · apply max_le hκle
    rw [mul_max_of_nonneg _ _ (Real.exp_pos τ).le]
    exact max_le (le_max_right _ _) (hscaled.trans hκle)

theorem exists_two_exponential_shearing_regimes
    (A U T : ℝ) (hA : 0 ≤ A) (hU : 0 ≤ U) (hT : 0 ≤ T)
    (hnorm : max A U = Real.exp (-4 * T)) :
    ∃ θ : ℝ, 4 * T ≤ θ ∧ θ ≤ 5 * T ∧ ∀ τ ∈ Icc 0 T,
      (max A (Real.exp τ * U))⁻¹ = Real.exp (4 * T) ∨
      (max A (Real.exp τ * U))⁻¹ = Real.exp (θ - τ) := by
  let κ := Real.exp (-4 * T)
  let v := max U (κ * Real.exp (-T))
  have hκ : 0 < κ := Real.exp_pos _
  have hv : 0 < v := (mul_pos hκ (Real.exp_pos _)).trans_le (le_max_right _ _)
  have hvle : v ≤ κ := by
    apply max_le
    · exact (le_max_right A U).trans_eq hnorm
    · have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT)
      nlinarith [Real.exp_pos (-T)]
  have hvlo : Real.exp (-5 * T) ≤ v := by
    have he : κ * Real.exp (-T) = Real.exp (-5 * T) := by
      dsimp only [κ]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← he]
    exact le_max_right _ _
  let θ := -Real.log v
  have hθlo : 4 * T ≤ θ := by
    have h := Real.log_le_log hv hvle
    change Real.log v ≤ Real.log (Real.exp (-4 * T)) at h
    rw [Real.log_exp] at h
    dsimp [θ]
    linarith
  have hθhi : θ ≤ 5 * T := by
    have h := Real.log_le_log (Real.exp_pos (-5 * T)) hvlo
    rw [Real.log_exp] at h
    dsimp [θ]
    linarith
  refine ⟨θ, hθlo, hθhi, ?_⟩
  intro τ hτ
  have heq := max_fixed_moving_clamp A U T τ hA hU hτ
  rw [hnorm] at heq
  change max A (Real.exp τ * U) = max κ (Real.exp τ * v) at heq
  rw [heq]
  by_cases h : Real.exp τ * v ≤ κ
  · left
    rw [max_eq_left h]
    change (Real.exp (-4 * T))⁻¹ = Real.exp (4 * T)
    rw [← Real.exp_neg]
    congr 1
    ring
  · right
    rw [max_eq_right (le_of_not_ge h)]
    simp [θ, Real.exp_sub, Real.exp_neg, Real.exp_log hv, div_eq_mul_inv, mul_inv_rev]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingLogTime
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Divergence of the logarithmic shearing window

Noncentral return matrices approaching the identity have positive scale
tending to zero. Their logarithmic time window tends to infinity, and
the two exponential regimes have exactly the bounds needed for the
common-time selection theorem.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootShearingKappa_one {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    rootShearingKappa i j (1 : G n) = 0 := by
  have hoff : rootShearingOffDiagonalSize i j (1 : G n) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = i ∨ k = j
    · simp only [hk, ite_true, if_true]
    · have hki : k ≠ i := fun h => hk (Or.inl h)
      have hkj : k ≠ j := fun h => hk (Or.inr h)
      simp [Matrix.SpecialLinearGroup.coe_one, hki, hkj, hkj.symm]
  simp [rootShearingKappa, rootShearingMovingSize, hoff,
    Matrix.SpecialLinearGroup.coe_one, hij.symm]

theorem rootShearingLogTime_normalizes {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g) :
    rootShearingKappa i j g = Real.exp (-4 * rootShearingLogTime i j g) := by
  have hk := rootShearingKappa_pos_of_noncentral hij g hnot
  have he : -4 * rootShearingLogTime i j g = Real.log (rootShearingKappa i j g) := by
    unfold rootShearingLogTime
    ring
  rw [he, Real.exp_log hk]

theorem rootShearingLogTime_nonneg {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    (hsmall : rootShearingKappa i j g ≤ 1) : 0 ≤ rootShearingLogTime i j g := by
  have hk := rootShearingKappa_pos_of_noncentral hij g hnot
  have hl := Real.log_nonpos hk.le hsmall
  exact div_nonneg (neg_nonneg.mpr hl) (by norm_num)

theorem rootShearingLogTime_tendsto {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hnot : ∀ m, ¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g m) :
    Tendsto (fun m => rootShearingLogTime i j (g m)) atTop atTop := by
  have hk : Tendsto (fun m => rootShearingKappa i j (g m)) atTop (𝓝 0) := by
    change Tendsto (rootShearingKappa i j ∘ g) atTop (𝓝 0)
    simpa only [rootShearingKappa_one hij] using
      ((continuous_rootShearingKappa i j).tendsto 1).comp hg
  have hkgt : Tendsto (fun m => rootShearingKappa i j (g m)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hk, Eventually.of_forall fun m =>
      rootShearingKappa_pos_of_noncentral hij (g m) (hnot m)⟩
  have hl := Real.tendsto_log_nhdsGT_zero.comp hkgt
  have hn : Tendsto (fun m => -Real.log (rootShearingKappa i j (g m))) atTop atTop :=
    tendsto_neg_atBot_atTop.comp hl
  exact (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 4)).mpr hn

theorem rootShearingKappa_two_regimes {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    (hsmall : rootShearingKappa i j g ≤ 1) :
    ∃ θ : ℝ, 4 * rootShearingLogTime i j g ≤ θ ∧
      θ ≤ 5 * rootShearingLogTime i j g ∧
      ∀ τ ∈ Icc 0 (rootShearingLogTime i j g),
        (rootShearingKappa i j (rootPairConjugate i j τ g))⁻¹ =
          Real.exp (4 * rootShearingLogTime i j g) ∨
        (rootShearingKappa i j (rootPairConjugate i j τ g))⁻¹ = Real.exp (θ - τ) := by
  obtain ⟨θ, hlo, hhi, hθ⟩ := exists_two_exponential_shearing_regimes
    |g.val j j - g.val i i| (rootShearingMovingSize i j g) (rootShearingLogTime i j g)
    (abs_nonneg _) (rootShearingMovingSize_nonneg i j g)
    (rootShearingLogTime_nonneg hij g hnot hsmall)
    (rootShearingLogTime_normalizes hij g hnot)
  refine ⟨θ, hlo, hhi, ?_⟩
  intro τ hτ
  simpa only [rootShearingKappa_conjugate hij] using hθ τ hτ

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingWindowControl
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform control during the logarithmic recurrence window

The shearing scale remains small throughout the chosen diagonal window.
The growing matrix entries are bounded by that scale; all other
off-diagonal entries contract. Thus moving to the selected recurrence
time preserves convergence of the relative return matrices to identity.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootShearingKappa_window_bound
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n)
    (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    (hsmall : rootShearingKappa i j g ≤ 1)
    (τ : ℝ) (hτ : τ ∈ Icc 0 (rootShearingLogTime i j g)) :
    rootShearingKappa i j (rootPairConjugate i j τ g) ≤
      Real.exp (-3 * rootShearingLogTime i j g) := by
  let T := rootShearingLogTime i j g
  have hT : 0 ≤ T := rootShearingLogTime_nonneg hij g hnot hsmall
  have hk := rootShearingLogTime_normalizes hij g hnot
  have hA := rootShearingKappa_diagonal_bound i j g
  have hU : rootShearingMovingSize i j g ≤ rootShearingKappa i j g := le_max_right _ _
  rw [rootShearingKappa_conjugate hij]
  apply max_le
  · apply hA.trans
    rw [hk]
    exact Real.exp_le_exp.mpr (by dsimp only [T] at hT ⊢ <;> linarith)
  · calc
      Real.exp τ * rootShearingMovingSize i j g ≤
          Real.exp T * rootShearingKappa i j g :=
        mul_le_mul (Real.exp_le_exp.mpr hτ.2) hU
          (rootShearingMovingSize_nonneg i j g) (Real.exp_pos _).le
      _ = Real.exp (-3 * rootShearingLogTime i j g) := by
        rw [hk, ← Real.exp_add]
        congr 1
        dsimp only [T]
        ring

theorem rootPairConjugate_entry_difference_bound
    {n : ℕ} {i j : Fin n} (g : G n)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hsmall : rootShearingKappa i j (rootPairConjugate i j τ g) ≤ 1)
    (r s : Fin n) :
    |(rootPairConjugate i j τ g).val r s - (1 : G n).val r s| ≤
      |g.val r s - (1 : G n).val r s| +
        rootShearingKappa i j (rootPairConjugate i j τ g) := by
  have hk := rootShearingKappa_nonneg i j (rootPairConjugate i j τ g)
  by_cases hrs : r = s
  · subst s
    rw [rootPairConjugate_diagonal]
    linarith
  have hzero : (1 : G n).val r s = 0 := by
    simp [Matrix.SpecialLinearGroup.coe_one, hrs]
  rw [hzero, sub_zero, sub_zero]
  by_cases hrj : r = j
  · subst r
    have hb := rootShearingKappa_row_bound (rootPairConjugate i j τ g) (Ne.symm hrs) hsmall
    linarith [abs_nonneg (g.val j s)]
  by_cases hsi : s = i
  · subst s
    have hb := rootShearingKappa_col_bound (rootPairConjugate i j τ g) hrs hsmall
    linarith [abs_nonneg (g.val r i)]
  have hwr : rootPairWeights i j r ≤ 0 := by
    simp only [rootPairWeights, hrj, ite_false, if_false, zero_sub]
    split_ifs <;> norm_num
  have hws : 0 ≤ rootPairWeights i j s := by
    simp only [rootPairWeights, hsi, ite_false, if_false, sub_zero]
    split_ifs <;> norm_num
  have he : Real.exp ((rootPairWeights i j r - rootPairWeights i j s) * τ) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hτ)
  have hentry : (rootPairConjugate i j τ g).val r s =
      Real.exp ((rootPairWeights i j r - rootPairWeights i j s) * τ) * g.val r s := by
    simp only [rootPairConjugate, rootPairFlow, conjugation_entry]
  rw [hentry, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans (by linarith)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingSelectedConvergence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergence of the relative matrices at selected recurrence times

Any selection inside the logarithmic window preserves convergence to
the identity. This justifies applying the signed shearing compactness
argument after the recurrence time has been chosen.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootPairConjugate_selected_tendsto_one
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hnot : ∀ m, ¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g m)
    (hsmall : ∀ m, rootShearingKappa i j (g m) ≤ 1)
    (τ : ℕ → ℝ) (hτ : ∀ m, τ m ∈ Icc 0 (rootShearingLogTime i j (g m))) :
    Tendsto (fun m => rootPairConjugate i j (τ m) (g m)) atTop (𝓝 1) := by
  have hT := rootShearingLogTime_tendsto hij g hg hnot
  have hrate : Tendsto (fun m => Real.exp (-3 * rootShearingLogTime i j (g m)))
      atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3) hT)
    simpa only [Function.comp_def, neg_mul] using h
  have hbound (m : ℕ) := rootShearingKappa_window_bound hij (g m) (hnot m)
    (hsmall m) (τ m) (hτ m)
  have hk : Tendsto (fun m => rootShearingKappa i j (rootPairConjugate i j (τ m) (g m)))
      atTop (𝓝 0) :=
    squeeze_zero (fun m => rootShearingKappa_nonneg _ _ _) hbound hrate
  have hsmall' (m : ℕ) : rootShearingKappa i j (rootPairConjugate i j (τ m) (g m)) ≤ 1 :=
    (hbound m).trans (Real.exp_le_one_iff.mpr (by
      have hT0 := rootShearingLogTime_nonneg hij (g m) (hnot m) (hsmall m)
      linarith))
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro s
  have hentry : Tendsto (fun m => (g m).val r s) atTop (𝓝 ((1 : G n).val r s)) :=
    ((show Continuous (fun h : G n => h.val r s) from by fun_prop).tendsto 1).comp hg
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  apply squeeze_zero (fun m => abs_nonneg _)
    (fun m => rootPairConjugate_entry_difference_bound (g m) (τ m) (hτ m).1 (hsmall' m) r s)
  simpa only [sub_self, abs_zero, zero_add] using
    (hentry.sub_const ((1 : G n).val r s)).abs.add hk

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_LeafReturnCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Annular compact returns avoiding leafwise null exceptions

The simultaneous-return argument can also enforce any property holding
almost everywhere on the common leaf. In particular both rebasing laws
can be enforced, so equal initial leaves give equal terminal leaves at
the chosen compact return.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_annular_simultaneous_root_return_ae
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (K G : Set (X n)) (c a : ℝ≥0∞)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (x y : X n) (hx : x ∈ G) (hy : y ∈ G)
    (heq : intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ y)
    (r ρ : ℝ) (hr : 0 < r)
    (hpos : intrinsicRootLeaf hij μ x (Metric.closedBall 0 r) ≠ 0)
    (hfinite : intrinsicRootLeaf hij μ x (Metric.closedBall 0 r) ≠ ∞)
    (hsmall : intrinsicRootLeaf hij μ x (Metric.closedBall 0 (ρ * r)) ≤
      a * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (hcoeff : c + c + a < 1)
    (P : ℝ → Prop) (hP : ∀ᵐ t ∂intrinsicRootLeaf hij μ x, P t) :
    ∃ t : ℝ, ρ * r < |t| ∧ |t| ≤ r ∧ P t ∧
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∈ K ∧
      rightAction y (Matrix.SpecialLinearGroup.transvection hij t) ∈ K := by
  let ν := intrinsicRootLeaf hij μ x
  let F := Metric.closedBall (0 : ℝ) (ρ * r) ∪ {t | ¬ P t}
  have hF : ν (Metric.closedBall (0 : ℝ) r ∩ F) ≤ ν (Metric.closedBall (0 : ℝ) (ρ * r)) := by
    calc
      _ ≤ ν F := measure_mono inter_subset_right
      _ ≤ ν (Metric.closedBall (0 : ℝ) (ρ * r)) + ν {t | ¬ P t} := measure_union_le _ _
      _ = _ := by rw [ae_iff.mp hP, add_zero]
  have hbudget : (c + c) * ν (Metric.closedBall 0 r) +
      ν (Metric.closedBall 0 r ∩ F) < ν (Metric.closedBall 0 r) := by
    calc
      _ ≤ (c + c) * ν (Metric.closedBall 0 r) + a * ν (Metric.closedBall 0 r) :=
        add_le_add le_rfl (hF.trans hsmall)
      _ = (c + c + a) * ν (Metric.closedBall 0 r) := (add_mul _ _ _).symm
      _ < 1 * ν (Metric.closedBall 0 r) := ENNReal.mul_lt_mul_left hpos hfinite hcoeff
      _ = _ := one_mul _
  obtain ⟨t, ht, hxK, hyK, hout⟩ := exists_simultaneous_root_return hij μ K G c hgood
    x y hx hy heq r hr F hbudget
  have hinner : t ∉ Metric.closedBall (0 : ℝ) (ρ * r) := fun h => hout (Or.inl h)
  have hp : P t := by
    by_contra h
    exact hout (Or.inr h)
  exact ⟨t, by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] using hinner,
    by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using ht, hp, hxK, hyK⟩

theorem exists_annular_return_with_equal_leaves
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (K G : Set (X n)) (c a : ℝ≥0∞)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (x y : X n) (hx : x ∈ G) (hy : y ∈ G)
    (heq : intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ y)
    (hrebasex : ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ x) t)
    (hrebasey : ∀ᵐ t ∂intrinsicRootLeaf hij μ y,
      intrinsicRootLeaf hij μ (rightAction y (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ y) t)
    (r ρ : ℝ) (hr : 0 < r)
    (hpos : intrinsicRootLeaf hij μ x (Metric.closedBall 0 r) ≠ 0)
    (hfinite : intrinsicRootLeaf hij μ x (Metric.closedBall 0 r) ≠ ∞)
    (hsmall : intrinsicRootLeaf hij μ x (Metric.closedBall 0 (ρ * r)) ≤
      a * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (hcoeff : c + c + a < 1) :
    ∃ t : ℝ, ρ * r < |t| ∧ |t| ≤ r ∧
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∈ K ∧
      rightAction y (Matrix.SpecialLinearGroup.transvection hij t) ∈ K ∧
      intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        intrinsicRootLeaf hij μ (rightAction y (Matrix.SpecialLinearGroup.transvection hij t)) := by
  rw [← heq] at hrebasey
  obtain ⟨t, hlo, hhi, he, hxK, hyK⟩ := exists_annular_simultaneous_root_return_ae
    hij μ K G c a hgood x y hx hy heq r ρ hr hpos hfinite hsmall hcoeff
    (fun t => intrinsicRootLeaf hij μ
      (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        intrinsicRootLeaf hij μ (rightAction y (Matrix.SpecialLinearGroup.transvection hij t)))
    (by
      filter_upwards [hrebasex, hrebasey] with t hx hy
      exact hx.trans hy.symm)
  exact ⟨t, hlo, hhi, hxK, hyK, he⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_TwoAnnularEqualReturns
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact returns in both normalized annuli

The synchronized small central portions and the intrinsic maximal
estimate give simultaneous compact returns with equal terminal leaves at both radii. Multiplying
the chosen times by the shearing scale places them in the two annuli
required by the polynomial noncancellation estimate.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_two_normalized_annular_equal_leaf_returns
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (K G : Set (X n)) (c a : ℝ≥0∞)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (x y : X n) (hx : x ∈ G) (hy : y ∈ G)
    (heq : intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ y)
    (hrebasex : ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ x) t)
    (hrebasey : ∀ᵐ t ∂intrinsicRootLeaf hij μ y,
      intrinsicRootLeaf hij μ (rightAction y (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ y) t)
    (hloc : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x))
    (κ ρ C : ℝ) (hκ : 0 < κ) (hC : 1 ≤ C)
    (hsecond : 16 / ρ ≤ ρ * C)
    (hsmall : ∀ b : Fin 2, intrinsicRootLeaf hij μ x
        (Metric.closedBall 0 (ρ * ((if b = 0 then 1 else C) / κ))) <
      a * intrinsicRootLeaf hij μ x (Metric.closedBall 0 ((if b = 0 then 1 else C) / κ)))
    (hcoeff : c + c + a < 1) :
    ∃ t : Fin 2 → ℝ,
      (∀ b, rightAction x (Matrix.SpecialLinearGroup.transvection hij (t b)) ∈ K ∧
        rightAction y (Matrix.SpecialLinearGroup.transvection hij (t b)) ∈ K ∧
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij (t b))) =
          intrinsicRootLeaf hij μ (rightAction y (Matrix.SpecialLinearGroup.transvection hij (t b)))) ∧
      ρ ≤ |κ * t 0| ∧ |κ * t 0| ≤ 1 ∧
      16 / ρ ≤ |κ * t 1| ∧ |κ * t 1| ≤ C := by
  let := hloc
  let r : Fin 2 → ℝ := fun b => (if b = 0 then 1 else C) / κ
  have hr (b : Fin 2) : 0 < r b := by
    apply div_pos _ hκ
    split_ifs
    · norm_num
    · exact zero_lt_one.trans_le hC
  have hmass (b : Fin 2) :
      intrinsicRootLeaf hij μ x (Metric.closedBall 0 (r b)) ≠ 0 := by
    intro he
    have h := hsmall b
    change intrinsicRootLeaf hij μ x (Metric.closedBall 0 (ρ * r b)) <
      a * intrinsicRootLeaf hij μ x (Metric.closedBall 0 (r b)) at h
    rw [he, mul_zero] at h
    exact (not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ _) h)
  have hfin (b : Fin 2) : intrinsicRootLeaf hij μ x (Metric.closedBall 0 (r b)) ≠ ∞ :=
    (isCompact_closedBall (0 : ℝ) (r b)).measure_lt_top.ne
  have hex (b : Fin 2) := exists_annular_return_with_equal_leaves hij μ K G c a hgood
    x y hx hy heq hrebasex hrebasey (r b) ρ (hr b) (hmass b) (hfin b) (hsmall b).le hcoeff
  choose t hlo hhi hxK hyK heqK using hex
  have hκr (b : Fin 2) : κ * r b = if b = 0 then 1 else C := by
    dsimp only [r]
    field_simp [hκ.ne']
  have hnorm (b : Fin 2) :
      ρ * (if b = 0 then 1 else C) < |κ * t b| ∧
        |κ * t b| ≤ (if b = 0 then 1 else C) := by
    have hl := mul_lt_mul_of_pos_left (hlo b) hκ
    have hu := mul_le_mul_of_nonneg_left (hhi b) hκ.le
    rw [abs_mul, abs_of_pos hκ]
    constructor
    · have hp := congrArg (fun u : ℝ => ρ * u) (hκr b)
      nlinarith
    · linarith [hκr b]
  have hzero : ρ < |κ * t 0| ∧ |κ * t 0| ≤ 1 := by
    simpa only [ite_true, if_true, mul_one] using hnorm 0
  have hone : ρ * C < |κ * t 1| ∧ |κ * t 1| ≤ C := by
    simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false, if_false] using hnorm 1
  exact ⟨t, fun b => ⟨hxK b, hyK b, heqK b⟩, hzero.1.le, hzero.2,
    hsecond.trans hone.1.le, hone.2⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_LeafFlowCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Joint almost-everywhere leaf covariance for the shearing flow

The fixed-time covariance theorem alone does not justify using a time
selected from a recurrence argument. Measurable kernels and a countable
determining family of leaf tests allow Fubini to put the time quantifier
inside: almost every initial point has covariance at almost every real
time. This is sufficient for selection after finitely many affine time
changes, without asserting an unproved pointwise equivariant version.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootPairCovarianceKernel_apply
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (x : X n) (t : ℝ) :
    rootPairCovarianceKernel hij μ hfree (x, t) =
      anchorNormalize ((intrinsicRootKernel hij μ hfree x).map
        (fun u => Real.exp (-2 * t) * u)) (Metric.ball 0 1) := rfl

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingTimeCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Choosing recurrence times with leaf covariance

Finitely many affine pullbacks of a Lebesgue null exceptional set are
null. Thus the two-point, two-scale recurrence selection can enforce
the actual leaf covariance identities at every selected time.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma ae_affine_precompose {P : ℝ → Prop} (hP : ∀ᵐ t ∂volume, P t)
    (a b : ℝ) (ha : a ≠ 0) : ∀ᵐ t ∂volume, P (b + a * t) := by
  apply ae_iff.mpr
  have he : {t | ¬ P (b + a * t)} =
      (fun t => a * t) ⁻¹' ((fun t => b + t) ⁻¹' {t | ¬ P t}) := rfl
  rw [he, Real.volume_preimage_mul_left ha, measure_preimage_add, ae_iff.mp hP, mul_zero]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingFourWindows
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Four candidate windows for the two annular radii

EKL Lemma 4.6 needs both possible scale regimes at each of two annular
radii. The four windows have total density loss at most `72 * ε` for
two initial points. Null-time exceptions for covariance can be avoided
at all four windows simultaneously.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal

namespace DukePrimeDegree

theorem exists_common_four_window_time
    {Y : Type*} (Φ : ℝ → Y → Y) (G H : Set Y) (z : Fin 2 → Y)
    (T ε : ℝ) (hT : 0 < T) (hε : 72 * ε < 1)
    (θ η : Fin 2 × Fin 2 → ℝ)
    (hθlo : ∀ q, 4 * T ≤ θ q) (hθhi : ∀ q, θ q ≤ 6 * T)
    (hη : ∀ q, η q = 0 ∨ η q = 1)
    (hG : ∀ k, volume.real (Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}) ≤ ε * T)
    (hH : ∀ k, volume.real (Ioc 0 (4 * T) ∩ {τ | Φ τ (z k) ∉ H}) ≤ ε * (4 * T)) :
    ∃ τ ∈ Ioc 0 T, (∀ k, Φ τ (z k) ∈ G) ∧
      ∀ k q, Φ ((θ q + (2 - η q) * τ) / 2) (z k) ∈ H := by
  let A : Fin 2 → Set ℝ := fun k => Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}
  let E : Fin 2 → Set ℝ := fun k => Ioc 0 (4 * T) ∩ {τ | Φ τ (z k) ∉ H}
  let B : Fin 2 × (Fin 2 × Fin 2) → Set ℝ := fun p => A p.1 ∪
    (Ioc 0 T ∩ ((fun τ => (θ p.2 + (2 - η p.2) * τ) / 2) ⁻¹' E p.1))
  have hB : ∀ p, B p ⊆ Ioc 0 T := by
    intro p τ hτ
    rcases hτ with hτ | hτ <;> exact hτ.1
  have hbad (p : Fin 2 × (Fin 2 × Fin 2)) : volume.real (B p) ≤ (9 * ε) * T := by
    have hpull := ekl_pullback_bad_time_bound T (θ p.2) (η p.2) ε (hη p.2)
      (E p.1) inter_subset_left (hH p.1)
    have hu := measureReal_union_le (μ := volume) (A p.1)
      (Ioc 0 T ∩ ((fun τ => (θ p.2 + (2 - η p.2) * τ) / 2) ⁻¹' E p.1))
    change volume.real (B p) ≤ volume.real (A p.1) + _ at hu
    have hg : volume.real (A p.1) ≤ ε * T := hG p.1
    linarith
  have hsum : ∑ _p : Fin 2 × (Fin 2 × Fin 2), (9 * ε) < 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have havoid : ∃ τ ∈ Ioc 0 T, ∀ p : Fin 2 × (Fin 2 × Fin 2), τ ∉ B p := by
    by_contra h
    have hcover : Ioc 0 T ⊆ ⋃ p, B p := by
      intro τ hτ
      by_contra hn
      apply h
      exact ⟨τ, hτ, fun p hp => hn (mem_iUnion.mpr ⟨p, hp⟩)⟩
    have hsub : (⋃ p, B p) ⊆ Ioc 0 T := iUnion_subset hB
    have hfinite : volume (⋃ p, B p) ≠ ∞ :=
      measure_ne_top_of_subset hsub (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hle := measureReal_mono hcover hfinite
    have hu := measureReal_iUnion_fintype_le (μ := volume) B
    have hb : ∑ p, volume.real (B p) ≤ (∑ _p : Fin 2 × (Fin 2 × Fin 2), 9 * ε) * T := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun p _ => hbad p
    have hstrict : (∑ _p : Fin 2 × (Fin 2 × Fin 2), 9 * ε) * T < T := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hsum hT
    rw [Real.volume_real_Ioc_of_le hT.le, sub_zero] at hle
    linarith
  obtain ⟨τ, hτ, hτB⟩ := havoid
  refine ⟨τ, hτ, ?_, ?_⟩
  · intro k
    by_contra hk
    exact hτB (k, (0, 0)) (Or.inl ⟨hτ, hk⟩)
  · intro k q
    by_contra hk
    have ht := ekl_affine_time_mem T (θ q) (η q) τ hT (hθlo q) (hθhi q) (hη q) hτ
    exact hτB (k, q) (Or.inr ⟨hτ, ht, hk⟩)


theorem exists_common_four_window_time_ae
    {Y : Type*} (Φ : ℝ → Y → Y) (G H : Set Y) (z : Fin 2 → Y)
    (T ε : ℝ) (hT : 0 < T) (hε : 72 * ε < 1)
    (θ η : Fin 2 × Fin 2 → ℝ)
    (hθlo : ∀ q, 4 * T ≤ θ q) (hθhi : ∀ q, θ q ≤ 6 * T)
    (hη : ∀ q, η q = 0 ∨ η q = 1)
    (hG : ∀ k, volume.real (Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}) ≤ ε * T)
    (hH : ∀ k, volume.real (Ioc 0 (4 * T) ∩ {τ | Φ τ (z k) ∉ H}) ≤ ε * (4 * T))
    (P : ℝ → Prop) (hP : ∀ᵐ τ ∂volume, P τ) :
    ∃ τ ∈ Ioc 0 T, P τ ∧ (∀ k, Φ τ (z k) ∈ G) ∧
      ∀ k q, Φ ((θ q + (2 - η q) * τ) / 2) (z k) ∈ H := by
  let Ψ : ℝ → Y × ℝ → Y × ℝ := fun t y => (Φ t y.1, t)
  let G' : Set (Y × ℝ) := {y | y.1 ∈ G ∧ P y.2}
  let H' : Set (Y × ℝ) := {y | y.1 ∈ H}
  have hG' (k : Fin 2) :
      volume.real (Ioc 0 T ∩ {τ | Ψ τ (z k, 0) ∉ G'}) ≤ ε * T := by
    have he : ((Ioc 0 T ∩ {τ | Ψ τ (z k, 0) ∉ G'} : Set ℝ)) =ᵐ[volume]
        ((Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G} : Set ℝ)) := by
      filter_upwards [hP] with τ hτ
      show (_ ∈ (_ : Set _)) = (_ ∈ (_ : Set _))
      simp only [mem_inter_iff, mem_ofPred_eq, Ψ, G', hτ, and_true]
    have hm := measure_congr he
    simpa only [measureReal_def, hm] using hG k
  obtain ⟨τ, hτ, hg, hh⟩ := exists_common_four_window_time Ψ G' H'
    (fun k => (z k, 0)) T ε hT hε θ η hθlo hθhi hη hG' hH
  exact ⟨τ, hτ, (hg 0).2, fun k => (hg k).1, hh⟩

theorem exists_common_four_window_time_with_covariance
    {Y : Type*} (Φ : ℝ → Y → Y) (G H : Set Y) (z : Fin 2 → Y)
    (T ε : ℝ) (hT : 0 < T) (hε : 72 * ε < 1)
    (θ η : Fin 2 × Fin 2 → ℝ)
    (hθlo : ∀ q, 4 * T ≤ θ q) (hθhi : ∀ q, θ q ≤ 6 * T)
    (hη : ∀ q, η q = 0 ∨ η q = 1)
    (hG : ∀ k, volume.real (Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}) ≤ ε * T)
    (hH : ∀ k, volume.real (Ioc 0 (4 * T) ∩ {τ | Φ τ (z k) ∉ H}) ≤ ε * (4 * T))
    (Q : Y → ℝ → Prop) (hQ : ∀ k, ∀ᵐ t ∂volume, Q (z k) t) :
    ∃ τ ∈ Ioc 0 T,
      (∀ k, Φ τ (z k) ∈ G ∧ Q (z k) τ) ∧
      ∀ k q, Φ ((θ q + (2 - η q) * τ) / 2) (z k) ∈ H ∧
        Q (z k) ((θ q + (2 - η q) * τ) / 2) := by
  have hfirst : ∀ᵐ τ ∂volume, ∀ k, Q (z k) τ := ae_all_iff.mpr hQ
  have hsecond : ∀ᵐ τ ∂volume, ∀ k q,
      Q (z k) ((θ q + (2 - η q) * τ) / 2) := by
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro q
    have ha : (2 - η q) / 2 ≠ 0 := by
      rcases hη q with h | h <;> rw [h] <;> norm_num
    have he (τ : ℝ) : (θ q + (2 - η q) * τ) / 2 =
        θ q / 2 + ((2 - η q) / 2) * τ := by ring
    simp_rw [he]
    exact ae_affine_precompose (hQ k) _ _ ha
  obtain ⟨τ, hτ, hq, hg, hh⟩ := exists_common_four_window_time_ae
    Φ G H z T ε hT hε θ η hθlo hθhi hη hG hH
    (fun τ => (∀ k, Q (z k) τ) ∧
      ∀ k q, Q (z k) ((θ q + (2 - η q) * τ) / 2)) (hfirst.and hsecond)
  exact ⟨τ, hτ, fun k => ⟨hg k, hq.1 k⟩, fun k q => ⟨hh k q, hq.2 k q⟩⟩


end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingCandidateWindows
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Four fixed candidate windows for two moving annuli

The inverse scale at a selected time is in one of two exponential
regimes. Adding the logarithm of a fixed enlargement to both candidate
exponents supplies the second annulus, while keeping all four exponents
in the recurrence range once the logarithmic time window is large.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootShearing_four_candidate_windows
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n)
    (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    (hsmall : rootShearingKappa i j g ≤ 1)
    (C : ℝ) (hC : 1 ≤ C) (hlog : Real.log C ≤ rootShearingLogTime i j g) :
    ∃ θ η : Fin 2 × Fin 2 → ℝ,
      (∀ q, 4 * rootShearingLogTime i j g ≤ θ q) ∧
      (∀ q, θ q ≤ 6 * rootShearingLogTime i j g) ∧
      (∀ q, η q = 0 ∨ η q = 1) ∧
      ∀ τ ∈ Icc 0 (rootShearingLogTime i j g), ∃ mode : Fin 2, ∀ b : Fin 2,
        (if b = 0 then 1 else C) *
          (rootShearingKappa i j (rootPairConjugate i j τ g))⁻¹ =
            Real.exp (θ (mode, b) - η (mode, b) * τ) := by
  obtain ⟨v, hvlo, hvhi, hreg⟩ := rootShearingKappa_two_regimes hij g hnot hsmall
  let T := rootShearingLogTime i j g
  have hT : 0 ≤ T := rootShearingLogTime_nonneg hij g hnot hsmall
  have hl : 0 ≤ Real.log C := Real.log_nonneg hC
  have hCp : 0 < C := zero_lt_one.trans_le hC
  let θ : Fin 2 × Fin 2 → ℝ := fun q =>
    (if q.1 = 0 then 4 * T else v) + (if q.2 = 0 then 0 else Real.log C)
  let η : Fin 2 × Fin 2 → ℝ := fun q => if q.1 = 0 then 0 else 1
  refine ⟨θ, η, ?_, ?_, ?_, ?_⟩
  · intro q
    dsimp only [θ]
    split_ifs <;> dsimp only [T] at * <;> linarith
  · intro q
    dsimp only [θ]
    split_ifs <;> dsimp only [T] at * <;> linarith
  · intro q
    dsimp only [η]
    split_ifs <;> tauto
  · intro τ hτ
    rcases hreg τ hτ with h | h
    · refine ⟨0, ?_⟩
      intro b
      rw [h]
      fin_cases b
      · simp [θ, η, T]
      · simp [θ, η, T, Real.exp_add, Real.exp_log hCp, mul_comm]
    · refine ⟨1, ?_⟩
      intro b
      rw [h]
      fin_cases b
      · simp [θ, η]
      · norm_num [θ, η]
        rw [show v + Real.log C - τ = Real.log C + (v - τ) by ring,
          Real.exp_add, Real.exp_log hCp]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafScaleComposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Comparing leaves at two selected diagonal times

Normalized scaling composes exactly when the leaf gives positive mass
to every neighborhood of the origin. This transfers the small-ball
bound at the second recurrence time to the annulus at the first time,
the measure comparison in EKL Lemma 4.5.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem normalized_scaling_comp (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c e : ℝ) (hc : 0 < c) :
    anchorNormalize
      ((anchorNormalize (ν.map (fun u => c * u)) (Metric.ball 0 1)).map (fun u => e * u))
      (Metric.ball 0 1) =
    anchorNormalize (ν.map (fun u => (e * c) * u)) (Metric.ball 0 1) := by
  have hm : ν.map (fun u => c * u) (Metric.ball 0 1) = ν (Metric.ball 0 (1 / c)) := by
    rw [Measure.map_apply (show Measurable (fun u : ℝ => c * u) from by fun_prop)
      Metric.isOpen_ball.measurableSet]
    exact congrArg ν (realScaling_preimage_ball c 1 hc)
  change anchorNormalize (((ν.map (fun u => c * u) (Metric.ball 0 1))⁻¹ •
    ν.map (fun u => c * u)).map (fun u => e * u)) (Metric.ball 0 1) = _
  rw [Measure.map_smul]
  rw [anchorNormalize_smul _ _ _ (by rw [hm]; exact ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    (by rw [hm]; exact ENNReal.inv_ne_top.mpr (hp _ (by positivity)).ne')]
  rw [Measure.map_map (show Measurable (fun u : ℝ => e * u) from by fun_prop)
    (show Measurable (fun u : ℝ => c * u) from by fun_prop)]
  congr 2
  funext u
  exact (mul_assoc e c u).symm

theorem normalized_scaling_ball_pos (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    0 < anchorNormalize (ν.map (fun u => c * u)) (Metric.ball 0 1) (Metric.ball 0 r) := by
  change 0 < anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne'))
    (Metric.ball 0 1) (Metric.ball 0 r)
  rw [normalized_realScaling_ball ν c r hc]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    (hp _ (div_pos hr hc)).ne'

theorem rootPair_leaf_covariance_between_times
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ a : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij a) = x → a = 0)
    (z : X n) (τ v : ℝ)
    (hp : ∀ r : ℝ, 0 < r → 0 < intrinsicRootKernel hij μ hfree z (Metric.ball 0 r))
    (hτ : RootPairLeafCovariance hij μ hfree z τ)
    (hv : RootPairLeafCovariance hij μ hfree z v) :
    intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-v))) =
      anchorNormalize ((intrinsicRootKernel hij μ hfree
        (rightAction z (rootPairFlow i j (-τ)))).map
          (fun u => Real.exp (-2 * (v - τ)) * u)) (Metric.ball 0 1) := by
  change intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-τ))) =
    anchorNormalize ((intrinsicRootKernel hij μ hfree z).map
      (fun u => Real.exp (-2 * τ) * u)) (Metric.ball 0 1) at hτ
  change intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-v))) =
    anchorNormalize ((intrinsicRootKernel hij μ hfree z).map
      (fun u => Real.exp (-2 * v) * u)) (Metric.ball 0 1) at hv
  rw [hv, hτ, normalized_scaling_comp _ hp _ _ (Real.exp_pos _)]
  congr 2
  funext u
  rw [← Real.exp_add]
  congr 2
  ring

theorem rootPair_small_ball_gives_annulus
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ a : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij a) = x → a = 0)
    (z : X n) (τ v ρ : ℝ) (a : ℝ≥0∞)
    (hp : ∀ r : ℝ, 0 < r → 0 < intrinsicRootKernel hij μ hfree z (Metric.ball 0 r))
    (hτ : RootPairLeafCovariance hij μ hfree z τ)
    (hv : RootPairLeafCovariance hij μ hfree z v)
    (hsmall : intrinsicRootKernel hij μ hfree
      (rightAction z (rootPairFlow i j (-v))) (Metric.closedBall 0 ρ) < a) :
    intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-τ)))
        (Metric.closedBall 0 (ρ * Real.exp (2 * (v - τ)))) <
      a * intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-τ)))
        (Metric.closedBall 0 (Real.exp (2 * (v - τ)))) := by
  let ν := intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-τ)))
  have hνpos : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r) := by
    change intrinsicRootKernel hij μ hfree (rightAction z (rootPairFlow i j (-τ))) =
      anchorNormalize ((intrinsicRootKernel hij μ hfree z).map
        (fun u => Real.exp (-2 * τ) * u)) (Metric.ball 0 1) at hτ
    intro r hr
    dsimp only [ν]
    rw [hτ]
    exact normalized_scaling_ball_pos _ hp _ r (Real.exp_pos _) hr
  have he := rootPair_leaf_covariance_between_times hij μ hfree z τ v hp hτ hv
  rw [he] at hsmall
  have h := normalized_small_ball_gives_annulus ν (Real.exp (-2 * (v - τ))) ρ
    (Real.exp_pos _) (hνpos _ (by positivity)).ne' a hsmall
  have hinv : (Real.exp (-2 * (v - τ)))⁻¹ = Real.exp (2 * (v - τ)) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  simpa only [div_eq_mul_inv, hinv, one_mul] using h

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SynchronizedAnnuli
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous small central portions at both shearing radii

This combines the two exponential regimes, all four candidate windows,
and the actual leaf scaling law. It proves the leaf-mass conclusion of
EKL Lemma 4.6 at the inverse shearing scale and at a fixed enlargement,
for both initial points, at one common recurrence time.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_synchronized_leaf_annuli
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ a : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij a) = x → a = 0)
    (g : G (d + 1))
    (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    (hsmall : rootShearingKappa i j g ≤ 1)
    (hT : 1 ≤ rootShearingLogTime i j g)
    (C : ℝ) (hC : 1 ≤ C) (hlog : Real.log C ≤ rootShearingLogTime i j g)
    (G H : Set (X (d + 1))) (z : Fin 2 → X (d + 1))
    (ρ ε : ℝ) (a : ℝ≥0∞) (hε : 72 * ε < 1)
    (hHsmall : ∀ y ∈ H, intrinsicRootKernel hij μ hfree y (Metric.closedBall 0 ρ) < a)
    (hpos : ∀ k, ∀ r : ℝ, 0 < r →
      0 < intrinsicRootKernel hij μ hfree (z k) (Metric.ball 0 r))
    (heq : intrinsicRootKernel hij μ hfree (z 0) = intrinsicRootKernel hij μ hfree (z 1))
    (hcov : ∀ k, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree (z k) t)
    (hcontrol : ∀ k, ∀ S : ℝ, 1 ≤ S →
      volume.real (Ioc 0 S ∩ {t | rightAction (z k) (rootPairFlow i j (-t)) ∉ G}) ≤ ε * S ∧
      volume.real (Ioc 0 S ∩ {t | rightAction (z k) (rootPairFlow i j (-t)) ∉ H}) ≤ ε * S) :
    ∃ τ ∈ Ioc 0 (rootShearingLogTime i j g),
      let x := fun k => rightAction (z k) (rootPairFlow i j (-τ))
      let r := fun b : Fin 2 => (if b = 0 then 1 else C) *
        (rootShearingKappa i j (rootPairConjugate i j τ g))⁻¹
      (∀ k, x k ∈ G) ∧
      intrinsicRootKernel hij μ hfree (x 0) = intrinsicRootKernel hij μ hfree (x 1) ∧
      (∀ b, 0 < r b) ∧
      ∀ k b, intrinsicRootKernel hij μ hfree (x k) (Metric.closedBall 0 (ρ * r b)) <
        a * intrinsicRootKernel hij μ hfree (x k) (Metric.closedBall 0 (r b)) := by
  obtain ⟨θ, η, hθlo, hθhi, hη, hreg⟩ :=
    rootShearing_four_candidate_windows hij g hnot hsmall C hC hlog
  obtain ⟨τ, hτ, hg, hh⟩ := exists_common_four_window_time_with_covariance
    (fun t x => rightAction x (rootPairFlow i j (-t))) G H z
    (rootShearingLogTime i j g) ε (by linarith) hε θ η hθlo hθhi hη
    (fun k => (hcontrol k _ hT).1)
    (fun k => (hcontrol k _ (by linarith)).2)
    (RootPairLeafCovariance hij μ hfree) hcov
  obtain ⟨mode, hmode⟩ := hreg τ ⟨hτ.1.le, hτ.2⟩
  refine ⟨τ, hτ, fun k => (hg k).1, ?_, ?_, ?_⟩
  · have h0 := (hg 0).2
    have h1 := (hg 1).2
    change intrinsicRootKernel hij μ hfree _ = rootPairCovarianceKernel hij μ hfree _ at h0 h1
    rw [h0, h1, rootPairCovarianceKernel_apply, rootPairCovarianceKernel_apply, heq]
  · intro b
    dsimp only
    rw [hmode b]
    exact Real.exp_pos _
  · intro k b
    let v := (θ (mode, b) + (2 - η (mode, b)) * τ) / 2
    have hv := (hh k (mode, b)).2
    have hsmall' := hHsmall _ (hh k (mode, b)).1
    have h := rootPair_small_ball_gives_annulus hij μ hfree (z k) τ v ρ a
      (hpos k) (hg k).2 hv hsmall'
    have hr : Real.exp (2 * (v - τ)) =
        (if b = 0 then 1 else C) *
          (rootShearingKappa i j (rootPairConjugate i j τ g))⁻¹ := by
      rw [hmode b]
      congr 1
      dsimp only [v]
      ring
    simpa only [hr] using h

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SynchronizedReturns
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Synchronized compact shearing pairs with equal leaves

The four recurrence windows produce the small central portions of both
leaf annuli at one common diagonal time. On the regular set, the
measurable kernel is the intrinsic leaf. The annular selection then
avoids the leafwise exceptional sets for rebasing, so both compact
return pairs have equal intrinsic leaves.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_synchronized_annular_equal_leaf_returns
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ u : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij u) = x → u = 0)
    (g : G (d + 1))
    (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    (hsmall : rootShearingKappa i j g ≤ 1)
    (hT : 1 ≤ rootShearingLogTime i j g)
    (C : ℝ) (hC : 1 ≤ C) (hlog : Real.log C ≤ rootShearingLogTime i j g)
    (K G H : Set (X (d + 1))) (z : Fin 2 → X (d + 1))
    (ρ ε : ℝ) (c a : ℝ≥0∞) (hε : 72 * ε < 1)
    (hsecond : 16 / ρ ≤ ρ * C) (hcoeff : c + c + a < 1)
    (hregular : ∀ x ∈ G,
      intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x ∧
      IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          basedRealMeasure (intrinsicRootLeaf hij μ x) t)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (hHsmall : ∀ y ∈ H, intrinsicRootKernel hij μ hfree y (Metric.closedBall 0 ρ) < a)
    (hpos : ∀ k, ∀ r : ℝ, 0 < r →
      0 < intrinsicRootKernel hij μ hfree (z k) (Metric.ball 0 r))
    (heq : intrinsicRootKernel hij μ hfree (z 0) = intrinsicRootKernel hij μ hfree (z 1))
    (hcov : ∀ k, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree (z k) t)
    (hcontrol : ∀ k, ∀ S : ℝ, 1 ≤ S →
      volume.real (Ioc 0 S ∩ {t | rightAction (z k) (rootPairFlow i j (-t)) ∉ G}) ≤ ε * S ∧
      volume.real (Ioc 0 S ∩ {t | rightAction (z k) (rootPairFlow i j (-t)) ∉ H}) ≤ ε * S) :
    ∃ τ ∈ Ioc 0 (rootShearingLogTime i j g), ∃ t : Fin 2 → ℝ,
      let x := fun k => rightAction (z k) (rootPairFlow i j (-τ))
      let κ := rootShearingKappa i j (rootPairConjugate i j τ g)
      (∀ b, rightAction (x 0) (Matrix.SpecialLinearGroup.transvection hij (t b)) ∈ K ∧
        rightAction (x 1) (Matrix.SpecialLinearGroup.transvection hij (t b)) ∈ K ∧
        intrinsicRootLeaf hij μ (rightAction (x 0)
          (Matrix.SpecialLinearGroup.transvection hij (t b))) =
        intrinsicRootLeaf hij μ (rightAction (x 1)
          (Matrix.SpecialLinearGroup.transvection hij (t b)))) ∧
      0 < κ ∧ ρ ≤ |κ * t 0| ∧ |κ * t 0| ≤ 1 ∧
      16 / ρ ≤ |κ * t 1| ∧ |κ * t 1| ≤ C := by
  obtain ⟨τ, hτ, hxG, heqτ, hr, hmass⟩ := exists_synchronized_leaf_annuli
    d hij μ hfree g hnot hsmall hT C hC hlog G H z ρ ε a hε hHsmall hpos heq hcov hcontrol
  let x := fun k => rightAction (z k) (rootPairFlow i j (-τ))
  let κ := rootShearingKappa i j (rootPairConjugate i j τ g)
  have hκ : 0 < κ := by
    have h := hr 0
    change 0 < (if (0 : Fin 2) = 0 then 1 else C) * κ⁻¹ at h
    simpa only [ite_true, if_true, one_mul, inv_pos] using h
  have hxreg := hregular (x 0) (hxG 0)
  have hyreg := hregular (x 1) (hxG 1)
  have hleaf : intrinsicRootLeaf hij μ (x 0) = intrinsicRootLeaf hij μ (x 1) :=
    hxreg.1.symm.trans (heqτ.trans hyreg.1)
  have hmass' (b : Fin 2) : intrinsicRootLeaf hij μ (x 0)
      (Metric.closedBall 0 (ρ * ((if b = 0 then 1 else C) / κ))) <
        a * intrinsicRootLeaf hij μ (x 0)
          (Metric.closedBall 0 ((if b = 0 then 1 else C) / κ)) := by
    have hm := hmass 0 b
    change intrinsicRootKernel hij μ hfree (x 0)
      (Metric.closedBall 0 (ρ * ((if b = 0 then 1 else C) * κ⁻¹))) <
        a * intrinsicRootKernel hij μ hfree (x 0)
          (Metric.closedBall 0 ((if b = 0 then 1 else C) * κ⁻¹)) at hm
    rw [hxreg.1] at hm
    simpa only [div_eq_mul_inv] using hm
  obtain ⟨t, hret, hlo, hfirst, hsecond', hupp⟩ :=
    exists_two_normalized_annular_equal_leaf_returns hij μ K G c a hgood
      (x 0) (x 1) (hxG 0) (hxG 1) hleaf hxreg.2.2 hyreg.2.2 hxreg.2.1
      κ ρ C hκ hC hsecond hmass' hcoeff
  exact ⟨τ, hτ, t, hret, hκ, hlo, hfirst, hsecond', hupp⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CompactShearingSequence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact equal-leaf shearing sequences

The synchronized annular return theorem applies to every member of an
initial noncentral sequence. The selected diagonal conjugates still
tend to identity, and the two compact return pairs have equal leaves
and the signed conjugation convention required by shearing compactness.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_compact_equal_leaf_shearing_sequence_oai
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ u : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij u) = x → u = 0)
    (g : ℕ → G (d + 1)) (hg : Tendsto g atTop (𝓝 1))
    (hnot : ∀ m, ¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g m)
    (hsmall : ∀ m, rootShearingKappa i j (g m) ≤ 1)
    (hT : ∀ m, 1 ≤ rootShearingLogTime i j (g m))
    (C : ℝ) (hC : 1 ≤ C) (hlog : ∀ m, Real.log C ≤ rootShearingLogTime i j (g m))
    (K G H : Set (X (d + 1))) (z : ℕ → Fin 2 → X (d + 1))
    (hpair : ∀ m, rightAction (z m 0) (g m) = z m 1)
    (ρ ε : ℝ) (c a : ℝ≥0∞) (hε : 72 * ε < 1)
    (hsecond : 16 / ρ ≤ ρ * C) (hcoeff : c + c + a < 1)
    (hregular : ∀ x ∈ G,
      intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x ∧
      IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          basedRealMeasure (intrinsicRootLeaf hij μ x) t)
    (hgood : ∀ x ∈ G, ∀ r : ℝ, 0 < r →
      intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
        c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r))
    (hHsmall : ∀ y ∈ H, intrinsicRootKernel hij μ hfree y (Metric.closedBall 0 ρ) < a)
    (hpos : ∀ m k, ∀ r : ℝ, 0 < r →
      0 < intrinsicRootKernel hij μ hfree (z m k) (Metric.ball 0 r))
    (heq : ∀ m, intrinsicRootKernel hij μ hfree (z m 0) =
      intrinsicRootKernel hij μ hfree (z m 1))
    (hcov : ∀ m k, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree (z m k) t)
    (hcontrol : ∀ m k, ∀ S : ℝ, 1 ≤ S →
      volume.real (Ioc 0 S ∩ {t | rightAction (z m k) (rootPairFlow i j (-t)) ∉ G}) ≤ ε * S ∧
      volume.real (Ioc 0 S ∩ {t | rightAction (z m k) (rootPairFlow i j (-t)) ∉ H}) ≤ ε * S) :
    ∃ (γ : ℕ → PrimeDegreePackets.G (d + 1))
      (p : ℕ → Fin 2 → X (d + 1)) (t : ℕ → Fin 2 → ℝ),
      Tendsto γ atTop (𝓝 1) ∧ ∀ m,
        0 < rootShearingKappa i j (γ m) ∧ rootShearingKappa i j (γ m) ≤ 1 ∧
        (∀ b, p m b ∈ K ∧
          rightAction (p m b) (Matrix.SpecialLinearGroup.transvection hij (t m b) * γ m *
            Matrix.SpecialLinearGroup.transvection hij (-t m b)) ∈ K ∧
          intrinsicRootLeaf hij μ (p m b) = intrinsicRootLeaf hij μ
            (rightAction (p m b) (Matrix.SpecialLinearGroup.transvection hij (t m b) * γ m *
              Matrix.SpecialLinearGroup.transvection hij (-t m b)))) ∧
        ρ ≤ |rootShearingKappa i j (γ m) * t m 0| ∧
        |rootShearingKappa i j (γ m) * t m 0| ≤ 1 ∧
        16 / ρ ≤ |rootShearingKappa i j (γ m) * t m 1| ∧
        |rootShearingKappa i j (γ m) * t m 1| ≤ C := by
  have hex (m : ℕ) := exists_synchronized_annular_equal_leaf_returns d hij μ hfree
    (g m) (hnot m) (hsmall m) (hT m) C hC (hlog m) K G H (z m) ρ ε c a hε hsecond
    hcoeff hregular hgood hHsmall (hpos m) (heq m) (hcov m) (hcontrol m)
  choose τ hτ r hr using hex
  let γ := fun m => rootPairConjugate i j (τ m) (g m)
  let x := fun m k => rightAction (z m k) (rootPairFlow i j (-τ m))
  let p := fun m b => rightAction (x m 0) (Matrix.SpecialLinearGroup.transvection hij (r m b))
  have hxpair (m : ℕ) : rightAction (x m 0) (γ m) = x m 1 := by
    change rightAction (rightAction (z m 0) (rootPairFlow i j (-τ m)))
      (rootPairConjugate i j (τ m) (g m)) = _
    rw [rootPairConjugate_rightAction, hpair]
  have hp (m : ℕ) (b : Fin 2) : rightAction (p m b)
      (Matrix.SpecialLinearGroup.transvection hij (-(r m b)) * γ m *
        Matrix.SpecialLinearGroup.transvection hij (r m b)) =
      rightAction (x m 1) (Matrix.SpecialLinearGroup.transvection hij (r m b)) := by
    exact (rootConjugate_rightAction hij (x m 0) (γ m) (r m b)).trans
      (congrArg (fun y => rightAction y (Matrix.SpecialLinearGroup.transvection hij (r m b)))
        (hxpair m))
  refine ⟨γ, p, fun m b => -(r m b),
    rootPairConjugate_selected_tendsto_one hij g hg hnot hsmall τ
      (fun m => ⟨(hτ m).1.le, (hτ m).2⟩), ?_⟩
  intro m
  have hκ : rootShearingKappa i j (γ m) ≤ 1 :=
    (rootShearingKappa_window_bound hij (g m) (hnot m) (hsmall m) (τ m)
      ⟨(hτ m).1.le, (hτ m).2⟩).trans
        (Real.exp_le_one_iff.mpr (by linarith [hT m]))
  refine ⟨(hr m).2.1, hκ, ?_, ?_⟩
  · intro b
    simp only [neg_neg, hp]
    exact (hr m).1 b
  · simpa only [mul_neg, abs_neg] using (hr m).2.2

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_compact_equal_leaf_shearing_sequence_oai := @OAI.DukePrimeDegree.exists_compact_equal_leaf_shearing_sequence_oai
