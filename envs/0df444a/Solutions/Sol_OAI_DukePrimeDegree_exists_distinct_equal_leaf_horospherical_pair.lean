-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_distinct_equal_leaf_horospherical_pair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:52:14.344852+00:00
-- url     : https://prove2.me/submissions/088b64a6-993c-4a3d-9527-06e17cc37bbe

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke044
import Theorems.Thm_OAI_DukePrimeDegree_exists_compact_equal_leaf_shearing_sequence
import Theorems.Thm_OAI_DukePrimeDegree_exists_equal_leaf_return_sequence_with_windows
import Theorems.Thm_OAI_DukePrimeDegree_nonempty_rootPairSelectionData
import Theorems.Thm_OAI_DukePrimeDegree_rootShearSize_two_scales_lower
import Theorems.Thm_OAI_DukePrimeDegree_signed_shearing_forces_horospherical_collision

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafPeriods
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported


namespace PrimeDegreePackets

lemma leafTest_apply (N k : ℕ) (x : ℝ) :
    leafTest N k x = (denseSeq (leafTestSpace N) k).val x := rfl

lemma continuous_leafTestSpace_integral (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (N : ℕ) (a : ℝ) : Continuous
      (fun f : leafTestSpace N => ∫ x, f.val (x+a) ∂ν) := by
  rw [←continuousOn_univ]
  apply continuousOn_integral_of_compact_support
    ((Homeomorph.addRight a).isCompact_preimage.mpr (isCompact_Icc (a := -(N:ℝ)) (b := N)))
  · have H : Continuous (fun p : leafTestSpace N × ℝ => p.1.val (p.2+a)) := by
      exact continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_snd.add_const a))
    exact H.continuousOn
  · intro f x _ hx
    exact f.prop (x+a) hx


end PrimeDegreePackets


open MeasureTheory Set Filter TopologicalSpace
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootInvariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace


namespace PrimeDegreePackets

lemma realMeasures_eq_iff_leafTests (ν ρ : Measure ℝ)
    [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ρ] :
    ν = ρ ↔ ∀ N k : ℕ, (∫ x, leafTest N k x ∂ν) = ∫ x, leafTest N k x ∂ρ := by
  constructor
  · rintro rfl N k
    rfl
  · intro h
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    obtain ⟨R,hR⟩ := f.hasCompactSupport.isBounded.subset_closedBall 0
    obtain ⟨N,hN⟩ := exists_nat_gt R
    have hs : ∀ x : ℝ, x ∉ Icc (-(N:ℝ)) N → f x = 0 := by
      intro x hx
      by_contra hf
      have hb := hR (subset_closure hf)
      rw [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hb
      exact hx (abs_le.mp (hb.trans hN.le))
    let f' : leafTestSpace N := ⟨f.toContinuousMap,hs⟩
    have hh : (fun g : leafTestSpace N => ∫ x, g.val (x+0) ∂ν) =
        (fun g : leafTestSpace N => ∫ x, g.val (x+0) ∂ρ) := by
      apply (denseRange_denseSeq (leafTestSpace N)).equalizer
        (continuous_leafTestSpace_integral ν N 0) (continuous_leafTestSpace_integral ρ N 0)
      funext k
      simpa only [Function.comp_apply,add_zero,leafTest_apply] using h N k
    have H := congrFun hh f'
    simpa only [f',add_zero,CompactlySupportedContinuousMap.coe_toContinuousMap] using H


end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootShearing
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

/-- The quadratic root-shearing formula, for arbitrary matrix indices. -/
theorem root_conjugation_entry {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (r s : Fin n) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s =
      g.1 r s + (if r = i then t * g.1 j s else 0) -
        (if s = j then t * g.1 r i else 0) -
        (if r = i ∧ s = j then t ^ 2 * g.1 j i else 0) := by
  rw [root_mul_entry, root_left_mul_entry, root_left_mul_entry]
  by_cases hr : r = i <;> by_cases hs : s = j
  all_goals simp only [hr, hs, ite_true, if_true, ite_false, if_false, true_and, false_and]
  all_goals ring

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafLusin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact sets with continuous root-leaf data

The Lusin step in EKL (2006), Section 4.3, is applied to a countable
family of compactly supported tests determining locally finite real
measures. A finer Polish topology and inner regularity provide a compact
set in the original topology, outside any specified null set.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology Classical ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma intrinsicLeafData_eq_iff {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (x y : X n) :
    intrinsicLeafData hij μ hfree x = intrinsicLeafData hij μ hfree y ↔
      intrinsicRootKernel hij μ hfree x = intrinsicRootKernel hij μ hfree y := by
  constructor
  · intro h
    apply (realMeasures_eq_iff_leafTests _ _).mpr
    intro a b
    exact congrFun h (a, b)
  · intro h
    funext q
    exact congrArg (fun ν : Measure ℝ => ∫ t, leafTest q.1 q.2 t ∂ν) h

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingKappa
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

lemma rootShearingKappa_nonneg {n : ℕ} (i j : Fin n) (g : G n) :
    0 ≤ rootShearingKappa i j g :=
  (abs_nonneg _).trans (le_max_left _ _)

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingLogTime
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingCoefficientBounds
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
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

lemma rootShearingKappa_linear_bound {n : ℕ} (i j r s : Fin n) (g : G n)
    (hsmall : rootShearingKappa i j g ≤ 1) :
    |(if r = i then g.val j s else 0) - (if s = j then g.val r i else 0)| ≤
      2 * rootShearingKappa i j g := by
  have hk := rootShearingKappa_nonneg i j g
  by_cases hr : r = i <;> by_cases hs : s = j
  · subst r; subst s
    simpa only [ite_true, if_true] using (rootShearingKappa_diagonal_bound i j g).trans
      (by linarith : rootShearingKappa i j g ≤ 2 * rootShearingKappa i j g)
  · subst r
    simp only [ite_true, if_true, hs, ite_false, if_false, sub_zero]
    exact (rootShearingKappa_row_bound g hs hsmall).trans (by linarith)
  · subst s
    simp only [hr, ite_false, if_false, ite_true, if_true, zero_sub, abs_neg]
    exact (rootShearingKappa_col_bound g hr hsmall).trans (by linarith)
  · simp only [hr, hs, ite_false, if_false, sub_zero, abs_zero]
    linarith

theorem rootShear_entry_bound_of_scale {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hsmall : rootShearingKappa i j g ≤ 1)
    (u C : ℝ) (hu : |u| * rootShearingKappa i j g ≤ C) (r s : Fin n) :
    |(Matrix.SpecialLinearGroup.transvection hij u * g *
      Matrix.SpecialLinearGroup.transvection hij (-u)).val r s - g.val r s| ≤ 2 * C + C ^ 2 := by
  let L := (if r = i then g.val j s else 0) - (if s = j then g.val r i else 0)
  let Q := if r = i ∧ s = j then g.val j i else 0
  have hL : |L| ≤ 2 * rootShearingKappa i j g := rootShearingKappa_linear_bound i j r s g hsmall
  have hQ : |Q| ≤ (rootShearingKappa i j g) ^ 2 := by
    dsimp [Q]
    split_ifs
    · exact rootShearingKappa_quadratic_bound i j g
    · simpa only [abs_zero] using sq_nonneg (rootShearingKappa i j g)
  have he : (Matrix.SpecialLinearGroup.transvection hij u * g *
      Matrix.SpecialLinearGroup.transvection hij (-u)).val r s - g.val r s = u * L - u ^ 2 * Q := by
    rw [root_conjugation_entry]
    dsimp [L, Q]
    split_ifs <;> ring
  have hk := rootShearingKappa_nonneg i j g
  have hC : 0 ≤ C := (mul_nonneg (abs_nonneg u) hk).trans hu
  have hlinear : |u| * |L| ≤ 2 * C := by
    have h := mul_le_mul_of_nonneg_left hL (abs_nonneg u)
    nlinarith
  have hquadratic : |u| ^ 2 * |Q| ≤ C ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hQ (sq_nonneg |u|)
    have hsq : (|u| * rootShearingKappa i j g) ^ 2 ≤ C ^ 2 := by
      nlinarith [mul_nonneg (abs_nonneg u) hk]
    nlinarith
  rw [he]
  have h := abs_sub_le (u * L) 0 (u ^ 2 * Q)
  simp only [sub_zero, zero_sub, abs_neg, abs_mul, abs_pow] at h
  linarith

theorem rootShearSize_bound_of_scale {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hsmall : rootShearingKappa i j g ≤ 1)
    (u C : ℝ) (hu : |u| * rootShearingKappa i j g ≤ C) :
    rootShearSize hij g u ≤ (n : ℝ) * n * (2 * C + C ^ 2) := by
  unfold rootShearSize
  calc
    _ ≤ ∑ _r : Fin n, ∑ _s : Fin n, (2 * C + C ^ 2) :=
      Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ =>
        rootShear_entry_bound_of_scale hij g hsmall u C hu r s
    _ = _ := by simp <;> ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingTwoAnnuli
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform positive displacement at one of two annular returns

The normalized profile is the actual matrix profile. Consequently the
two-scale cancellation estimate gives a positive lower bound independent
of the return matrix, while the scale bound controls every intervening
shearing parameter.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootShearSize_bound_on_symmetric_interval {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hsmall : rootShearingKappa i j g ≤ 1)
    (t C : ℝ) (ht : |t| * rootShearingKappa i j g ≤ C) :
    ∀ u : ℝ, |u| ≤ |t| →
      rootShearSize hij g u ≤ (n : ℝ) * n * (2 * C + C ^ 2) := by
  intro u hu
  apply rootShearSize_bound_of_scale hij g hsmall u C
  exact (mul_le_mul_of_nonneg_right hu (rootShearingKappa_nonneg i j g)).trans ht

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_HorosphereFreeness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Freeness of the shearing horosphere

A lattice with no nonzero vector on a coordinate hyperplane has no
nonidentity stabilizer fixing a coordinate column. Root-horospherical
matrices fix such a column. Full diagonal invariance gives the required
lattice property almost everywhere, removing any small-size restriction
from the compact shearing contradiction.
-/

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma vecMul_fixed_column {n : ℕ} (h : G n) (i : Fin n)
    (hcol : ∀ r, h.val r i = (1 : Matrix (Fin n) (Fin n) ℝ) r i)
    (v : Fin n → ℝ) : (v ᵥ* h.val) i = v i := by
  calc
    (v ᵥ* h.val) i = (v ᵥ* (1 : Matrix (Fin n) (Fin n) ℝ)) i := by
      change (∑ k, v k * h.val k i) = ∑ k, v k * (1 : Matrix (Fin n) (Fin n) ℝ) k i
      apply Finset.sum_congr rfl
      intro k _
      rw [hcol k]
    _ = v i := congrFun (Matrix.vecMul_one v) i

theorem stabilizer_eq_one_of_fixed_column {n : ℕ} (x : X n)
    (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ i, v i ≠ 0)
    (h : G n) (i : Fin n)
    (hcol : ∀ r, h.val r i = (1 : Matrix (Fin n) (Fin n) ℝ) r i)
    (hfix : rightAction x h = x) : h = 1 := by
  have hvec (v : Fin n → ℝ) (hv : v ∈ pointLattice x) : v ᵥ* h.val = v := by
    let w := v ᵥ* h.val - v
    have hw : w ∈ pointLattice x := by
      apply Submodule.sub_mem _ _ hv
      have hmem := vecMul_mem_pointLattice_rightAction x h v hv
      simpa only [hfix] using hmem
    have hwi : w i = 0 := by
      change (v ᵥ* h.val) i - v i = 0
      rw [vecMul_fixed_column h i hcol, sub_self]
    have hwzero : w = 0 := by
      by_contra hn
      exact hx w hw hn i hwi
    exact sub_eq_zero.mp hwzero
  induction x using Quotient.inductionOn with
  | h g =>
    have hmul : g * h = g := by
      apply Subtype.ext
      ext r s
      have hmem : g.val r ∈ pointLattice (Quotient.mk'' g) := by
        rw [pointLattice_mk]
        exact Submodule.subset_span (mem_range_self r)
      exact congrFun (hvec (g.val r) hmem) s
    exact mul_left_cancel (hmul.trans (mul_one g).symm)

theorem rootHorosphere_stabilizer_eq_one {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x : X n) (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ k, v k ≠ 0)
    (h : G n) (hshape : RootHorosphereShape i j h) (hfix : rightAction x h = x) : h = 1 := by
  apply stabilizer_eq_one_of_fixed_column x hx h i _ hfix
  intro r
  by_cases hr : r = i
  · exact hshape r i (Or.inr hr)
  · exact hshape r i (Or.inl ⟨hr, hij⟩)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingSelection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting a nontrivial shearing sequence from two annuli

This is the last compactness step in the two-scale argument of EKL,
Section 4.5. A scale tending to zero makes every annular return diverge.
The two-scale estimate selects a return with uniformly positive
displacement; the common upper scale controls its entire trajectory.
On a compact set with the stated horospherical separation property this
contradicts arithmetic freeness. The separation property is a separate
input here, not a claim that the low-entropy product theorem is proved.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma abs_tendsto_atTop_of_vanishing_scale
    (k t : ℕ → ℝ) (hk : Tendsto k atTop (𝓝 0))
    (hk0 : ∀ m, 0 ≤ k m) (ρ : ℝ) (hρ : 0 < ρ)
    (hlo : ∀ m, ρ ≤ k m * |t m|) :
    Tendsto (fun m => |t m|) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  by_cases hb : b ≤ 0
  · exact Eventually.of_forall fun m => hb.trans (abs_nonneg _)
  · have hbpos : 0 < b := lt_of_not_ge hb
    have he : ∀ᶠ m in atTop, k m < ρ / b :=
      (tendsto_order.1 hk).2 _ (div_pos hρ hbpos)
    filter_upwards [he] with m hm
    by_contra h
    have htb : |t m| ≤ b := (lt_of_not_ge h).le
    have hprod := mul_le_mul_of_nonneg_left htb (hk0 m)
    have hkb : k m * b < ρ := (lt_div_iff₀ hbpos).mp hm
    linarith [hlo m]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_IntrinsicShearingCollision
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Two annular equal-leaf sequences force a horospherical collision

The compactness argument is expressed directly in terms of the actual
intrinsic leaves. Countable determining data allow passage to the
limit on a Lusin compact set. Arithmetic freeness ensures that the
nonidentity limiting matrix moves the limiting point.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem two_annular_equal_leaves_force_collision
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ u : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij u) = x → u = 0)
    (K : Set (X n)) (hK : IsCompact K)
    (hF : ContinuousOn (intrinsicLeafData hij μ hfree) K)
    (hkernel : ∀ x ∈ K, intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x)
    (hcoords : ∀ z ∈ K, ∀ v ∈ pointLattice z, v ≠ 0 → ∀ k, v k ≠ 0)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hkpos : ∀ m, 0 < rootShearingKappa i j (g m))
    (hksmall : ∀ m, rootShearingKappa i j (g m) ≤ 1)
    (x : ℕ → Fin 2 → X n) (t : ℕ → Fin 2 → ℝ)
    (ρ C : ℝ) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hlo : ∀ m q, ρ ≤ |rootShearingKappa i j (g m) * t m q|)
    (hfirst : ∀ m, |rootShearingKappa i j (g m) * t m 0| ≤ 1)
    (hsecond : ∀ m, 16 / ρ ≤ |rootShearingKappa i j (g m) * t m 1|)
    (hupp : ∀ m q, |rootShearingKappa i j (g m) * t m q| ≤ C)
    (hx : ∀ m q, x m q ∈ K)
    (hy : ∀ m q, rightAction (x m q)
      (Matrix.SpecialLinearGroup.transvection hij (t m q) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m q)) ∈ K)
    (heq : ∀ m q, intrinsicRootLeaf hij μ (x m q) = intrinsicRootLeaf hij μ
      (rightAction (x m q) (Matrix.SpecialLinearGroup.transvection hij (t m q) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m q)))) :
    ∃ z ∈ K, ∃ h : G n, RootHorosphereShape i j h ∧ rightAction z h ∈ K ∧
      rightAction z h ≠ z ∧ intrinsicRootLeaf hij μ z =
        intrinsicRootLeaf hij μ (rightAction z h) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Fin.pos i
  let a : ℝ := ρ / (16 * (n : ℝ))
  have ha : 0 < a := div_pos hρ (by positivity)
  have hchoice (m : ℕ) : ∃ q : Fin 2, a ≤ rootShearSize hij (g m) (t m q) := by
    rcases rootShearSize_two_scales_lower hij (g m) (hkpos m)
      (t m 0) (t m 1) ρ hρ hρone (hlo m 0) (hfirst m) (hsecond m) with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  choose q hq using hchoice
  have hk : Tendsto (fun m => rootShearingKappa i j (g m)) atTop (𝓝 0) := by
    change Tendsto (rootShearingKappa i j ∘ g) atTop (𝓝 0)
    simpa only [rootShearingKappa_one hij] using
      ((continuous_rootShearingKappa i j).tendsto 1).comp hg
  have hnorm (m : ℕ) : ρ ≤ rootShearingKappa i j (g m) * |t m (q m)| := by
    simpa only [abs_mul, abs_of_pos (hkpos m)] using hlo m (q m)
  have ht (m : ℕ) : t m (q m) ≠ 0 := by
    intro he
    have h := hnorm m
    rw [he, abs_zero, mul_zero] at h
    exact hρ.not_ge h
  have hdata (m : ℕ) : intrinsicLeafData hij μ hfree (x m (q m)) =
      intrinsicLeafData hij μ hfree (rightAction (x m (q m))
        (Matrix.SpecialLinearGroup.transvection hij (t m (q m)) * g m *
          Matrix.SpecialLinearGroup.transvection hij (-t m (q m)))) := by
    apply (intrinsicLeafData_eq_iff hij μ hfree _ _).mpr
    rw [hkernel _ (hx m (q m)), hkernel _ (hy m (q m)), heq m (q m)]
  obtain ⟨h, hne, hshape, _, _, z, hz, hzh, he⟩ :=
    signed_shearing_forces_horospherical_collision hij K hK (intrinsicLeafData hij μ hfree) hF
      (fun m => x m (q m)) g hg (fun m => t m (q m)) ht
      (abs_tendsto_atTop_of_vanishing_scale _ _ hk (fun m => (hkpos m).le) ρ hρ hnorm)
      a ((n : ℝ) * n * (2 * C + C ^ 2)) ha hq
      (fun m u hu => rootShearSize_bound_on_symmetric_interval hij (g m) (hksmall m)
        (t m (q m)) C (by
          simpa only [abs_mul, abs_of_pos (hkpos m), mul_comm] using hupp m (q m)) u hu)
      (fun m => hx m (q m)) (fun m => hy m (q m)) hdata
  refine ⟨z, hz, h, hshape, hzh, ?_, ?_⟩
  · exact fun hfix => hne (rootHorosphere_stabilizer_eq_one hij z (hcoords z hz) h hshape hfix)
  · have he' := (intrinsicLeafData_eq_iff hij μ hfree _ _).mp he
    rwa [hkernel z hz, hkernel _ hzh] at he'

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LowEntropyCollision
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual equal-leaf horospherical collisions

All sets, return pairs, recurrence times and annular translations are
constructed from diagonal invariance and nontrivial root leaves. No
horospherical separation premise is used here. The resulting distinct
points avoid any prescribed null set.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem RootPairSelectionData.exists_equal_leaf_collision
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (N : Set (X (d + 1))) (S : RootPairSelectionData d hij μ hfree N) :
    ∃ x ∈ S.K, ∃ h : PrimeDegreePackets.G (d + 1),
      RootHorosphereShape i j h ∧ rightAction x h ∈ S.K ∧
      rightAction x h ≠ x ∧ intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ (rightAction x h) := by
  let C : ℝ := 16 / S.ρ ^ 2
  have hρ := S.rho_pos
  have hρone : S.ρ ≤ 1 := by linarith [S.rho_small]
  have hC : 1 ≤ C := by
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    nlinarith [S.rho_small]
  have hsecond : 16 / S.ρ ≤ S.ρ * C := by
    have he : S.ρ * C = 16 / S.ρ := by
      dsimp only [C]
      field_simp [hρ.ne']
    exact he.ge
  obtain ⟨x, y, g, hg, hp⟩ := exists_equal_leaf_return_sequence_with_windows
    d hd hij μ hA S.Z S.source_measurable S.source_positive (max 1 (Real.log C))
  let z : ℕ → Fin 2 → X (d + 1) := fun m => ![x m, y m]
  have hz (m : ℕ) (k : Fin 2) : z m k ∈ S.Z := by
    fin_cases k
    · exact (hp m).1
    · exact (hp m).2.1
  have hreg (m : ℕ) (k : Fin 2) := S.source_regular (z m k) (hz m k)
  have hinit (m : ℕ) : intrinsicRootKernel hij μ hfree (z m 0) =
      intrinsicRootKernel hij μ hfree (z m 1) := by
    rw [(hreg m 0).1, (hreg m 1).1]
    exact (hp m).2.2.2.2.1
  obtain ⟨γ, p, t, hγ, hret⟩ := exists_compact_equal_leaf_shearing_sequence d hij μ hfree g hg
    (fun m => (hp m).2.2.2.1) (fun m => (hp m).2.2.2.2.2.1)
    (fun m => (le_max_left _ _).trans (hp m).2.2.2.2.2.2) C hC
    (fun m => (le_max_right _ _).trans (hp m).2.2.2.2.2.2)
    S.K S.G S.H z (fun m => (hp m).2.2.1) S.ρ (1 / 100)
    (ENNReal.ofReal (1 / 8)) (1 / 2) (by norm_num) hsecond
    (by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num)
    (fun x hx => ⟨(S.good_regular x hx).1, (S.good_regular x hx).2.1,
      (S.good_regular x hx).2.2.2⟩)
    S.good_returns S.small_ball
    (fun m k r hr => by rw [(hreg m k).1]; exact (hreg m k).2.2.1 r hr)
    hinit (fun m k => S.source_covariance (z m k) (hz m k))
    (fun m k => S.source_returns (z m k) (hz m k))
  have hlo (m : ℕ) (b : Fin 2) : S.ρ ≤ |rootShearingKappa i j (γ m) * t m b| := by
    rcases hret m with ⟨_, _, _, hlo, _, hsecond', _⟩
    fin_cases b
    · exact hlo
    · have hr : S.ρ ≤ 16 / S.ρ := (le_div_iff₀ hρ).mpr (by nlinarith)
      exact hr.trans hsecond'
  have hupp (m : ℕ) (b : Fin 2) : |rootShearingKappa i j (γ m) * t m b| ≤ C := by
    rcases hret m with ⟨_, _, _, _, hfirst, _, hsecond'⟩
    fin_cases b
    · exact hfirst.trans hC
    · exact hsecond'
  exact two_annular_equal_leaves_force_collision hij μ hfree S.K S.compact S.continuous
    (fun x hx => (S.compact_regular x hx).1) S.coordinates γ hγ
    (fun m => (hret m).1) (fun m => (hret m).2.1) p t S.ρ C hρ hρone hlo
    (fun m => (hret m).2.2.2.2.1) (fun m => (hret m).2.2.2.2.2.1) hupp
    (fun m b => ((hret m).2.2.1 b).1)
    (fun m b => ((hret m).2.2.1 b).2.1)
    (fun m b => ((hret m).2.2.1 b).2.2)

theorem exists_distinct_equal_leaf_horospherical_pair_oai
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hnontrivial : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    ∃ x ∉ N, ∃ h : G (d + 1), RootHorosphereShape i j h ∧ rightAction x h ∉ N ∧
      rightAction x h ≠ x ∧ intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ (rightAction x h) := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  obtain ⟨S⟩ := nonempty_rootPairSelectionData d hij μ hA hfree hnontrivial N hN hNzero
  obtain ⟨x, hx, h, hshape, hy, hne, heq⟩ :=
    S.exists_equal_leaf_collision d hd hij μ hA hfree N
  exact ⟨x, S.outside hx, h, hshape, S.outside hy, hne, heq⟩

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_distinct_equal_leaf_horospherical_pair_oai := @OAI.DukePrimeDegree.exists_distinct_equal_leaf_horospherical_pair_oai
