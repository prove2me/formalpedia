-- Prove2me | solution 1 for OAI.DukePrimeDegree.EliminationChain.wholeFuture_conditionalInformation_integrable_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:44.325228+00:00
-- url     : https://prove2.me/submissions/8e9078f5-00fe-4b8a-8833-b7465c96e29e

import Mathlib
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Pairing
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Logic.Encodable.Lattice
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.PartialSups
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
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

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_EntropyMixtures
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets

variable {Z Y ι : Type*} [MeasurableSpace Z] [MeasurableSpace Y]



lemma measurable_kernel_real (κ : Kernel Z Y) {S : Set Y} (hS : MeasurableSet S) :
    Measurable (fun z => (κ z).real S) := (κ.measurable_coe hS).ennreal_toReal

lemma integrable_kernel_real (τ : Measure Z) [IsFiniteMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] {S : Set Y} (hS : MeasurableSet S) :
    Integrable (fun z => (κ z).real S) τ := by
  refine Integrable.mono' (integrable_const (1:ℝ)) (measurable_kernel_real κ hS).aestronglyMeasurable ?_
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntrinsicLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets
variable {n : ℕ} {i j : Fin n} (hij : i ≠ j)



lemma ae_intrinsicRootKernel_eq (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x := by
  let κ : Kernel (X n) ℝ :=
    ⟨(aemeasurable_intrinsicRootLeaf hij μ hfree).mk (intrinsicRootLeaf hij μ),
      (aemeasurable_intrinsicRootLeaf hij μ hfree).measurable_mk⟩
  have he : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x :=
    (aemeasurable_intrinsicRootLeaf hij μ hfree).ae_eq_mk.symm
  filter_upwards [he,ae_intrinsicRootLeaf_spec hij μ hfree] with x hx hs
  have : IsLocallyFiniteMeasure (κ x) := hx.symm ▸ hs.1
  exact (locallyFiniteRealVersion_eq κ x).trans hx

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_HopfMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite maximal ergodic inequality

The maximal recurrence estimate used in EKL (2006), Section 4.3, follows
from this elementary finite Hopf inequality. The running maximum is built
recursively, so its integrability and its coboundary bound require no
pointwise ergodic theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

lemma positiveRunningSum_nonneg {Y : Type*} (T : Y → Y) (f : Y → ℝ)
    (n : ℕ) (x : Y) : 0 ≤ positiveRunningSum T f n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

lemma positiveRunningSum_mono {Y : Type*} (T : Y → Y) (f : Y → ℝ)
    (x : Y) : Monotone (fun n => positiveRunningSum T f n x) := by
  suffices h : ∀ n x, positiveRunningSum T f n x ≤ positiveRunningSum T f (n + 1) x
    from monotone_nat_of_le_succ (fun n => h n x)
  intro n
  induction n with
  | zero => exact fun x => positiveRunningSum_nonneg T f 1 x
  | succ n ih =>
    intro x
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

lemma birkhoffSum_le_positiveRunningSum {Y : Type*} (T : Y → Y) (f : Y → ℝ)
    (n : ℕ) (x : Y) : birkhoffSum T f n x ≤ positiveRunningSum T f n x := by
  induction n generalizing x with
  | zero => simp [positiveRunningSum]
  | succ n ih =>
    rw [birkhoffSum_succ']
    exact (add_le_add le_rfl (ih (T x))).trans (le_max_right _ _)

lemma measurable_positiveRunningSum {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} {f : Y → ℝ} (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (positiveRunningSum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

lemma integrable_positiveRunningSum {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {T : Y → Y} {f : Y → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (positiveRunningSum T f n) μ := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih =>
    exact (integrable_zero _ _ _).sup (hf.add (hT.integrable_comp_of_integrable ih))

/-- A finite running maximum has nonnegative signed mass on its positive set. -/
theorem finite_hopf_maximal {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {T : Y → Y} {f : Y → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    (hfmeas : Measurable f) (n : ℕ) :
    0 ≤ ∫ x in {x | 0 < positiveRunningSum T f n x}, f x ∂μ := by
  let m := positiveRunningSum T f n
  let E := {x | 0 < m x}
  have hm : Integrable m μ := integrable_positiveRunningSum hT hf n
  have hmmeas : Measurable m := measurable_positiveRunningSum hT.measurable hfmeas n
  have hE : MeasurableSet E := measurableSet_lt measurable_const hmmeas
  have hpoint (x : Y) : m x - m (T x) ≤ E.indicator f x := by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      have hle := positiveRunningSum_mono T f x (Nat.le_succ n)
      change m x ≤ max 0 (f x + m (T x)) at hle
      have hpos : 0 < m x := hx
      have hle' := (le_max_iff.mp hle).resolve_left (not_le_of_gt hpos)
      linarith
    · rw [indicator_of_notMem hx]
      have hz : m x = 0 := le_antisymm (le_of_not_gt hx)
        (positiveRunningSum_nonneg T f n x)
      rw [hz]
      linarith [positiveRunningSum_nonneg T f n (T x)]
  have hcomp : ∫ x, m (T x) ∂μ = ∫ x, m x ∂μ := by
    have hmap : AEStronglyMeasurable m (μ.map T) := by
      simpa only [hT.map_eq] using hm.aestronglyMeasurable
    exact (integral_map hT.measurable.aemeasurable hmap).symm.trans
      (by rw [hT.map_eq])
  have hle := integral_mono (hm.sub (hT.integrable_comp_of_integrable hm))
    (hf.indicator hE) hpoint
  simp only [Pi.sub_apply, Function.comp_apply] at hle
  have hmt : Integrable (fun x => m (T x)) μ := hT.integrable_comp_of_integrable hm
  rw [integral_sub hm hmt, hcomp, sub_self,
    integral_indicator hE] at hle
  exact hle

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_HopfMeanBound
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean bounds from eventual orbit excursions

A conull union of positive finite excursions has nonnegative mean by the
finite Hopf inequality. This avoids assuming integrability of an unbounded
information function before truncating it.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree

/-- Positive partial sums somewhere along almost every orbit force a
nonnegative integral. -/
theorem integral_nonneg_of_ae_positive_birkhoffSum
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
    {T : Y → Y} {f : Y → ℝ} (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) (hfm : Measurable f)
    (hexc : ∀ᵐ x ∂μ, ∃ n : ℕ, 0 < birkhoffSum T f n x) :
    0 ≤ ∫ x, f x ∂μ := by
  let E : ℕ → Set Y := fun n => {x | 0 < positiveRunningSum T f n x}
  have hEm (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfm n)
  have hmono : Monotone E := by
    intro a b hab x hx
    exact hx.trans_le (positiveRunningSum_mono T f x hab)
  have hconull : ∀ᵐ x ∂μ, x ∈ ⋃ n, E n := by
    filter_upwards [hexc] with x hx
    obtain ⟨n, hn⟩ := hx
    exact mem_iUnion.mpr ⟨n, hn.trans_le (birkhoffSum_le_positiveRunningSum T f n x)⟩
  have hlim := tendsto_setIntegral_of_monotone hEm hmono hf.integrableOn
  have heq : (∫ x in ⋃ n, E n, f x ∂μ) = ∫ x, f x ∂μ := by
    rw [Measure.restrict_congr_set (show (⋃ n, E n) =ᵐ[μ] (univ : Set Y) from
      hconull.mono (fun x hx => by
        show (x ∈ ⋃ n, E n) = (x ∈ (univ : Set Y))
        simp [hx]))]
    simp
  rw [heq] at hlim
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun n => finite_hopf_maximal hT hf hfm n

/-- A bounded observable whose orbit average is eventually below `c`
has mean at most `c`. -/
theorem integral_le_of_ae_birkhoffSum_lt
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
    {T : Y → Y} {g : Y → ℝ} (hT : MeasurePreserving T μ μ)
    (hg : Integrable g μ) (hgm : Measurable g) (c : ℝ)
    (hexc : ∀ᵐ x ∂μ, ∃ n : ℕ, birkhoffSum T g n x < c * n) :
    (∫ x, g x ∂μ) ≤ c := by
  have h := integral_nonneg_of_ae_positive_birkhoffSum hT
    ((integrable_const c).sub hg) (measurable_const.sub hgm) ?_
  · change 0 ≤ ∫ x, c - g x ∂μ at h
    rw [integral_sub (integrable_const c) hg] at h
    simpa using (sub_nonneg.mp h)
  · filter_upwards [hexc] with x hx
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    change 0 < ∑ k ∈ Finset.range n, (c - g (T^[k] x))
    rw [Finset.sum_sub_distrib]
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm,
      birkhoffSum]
      using sub_pos.mpr hn

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_IntegrableCoboundary
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrable coboundaries have zero mean

Only the difference is assumed integrable. Truncating the transfer
function by one-Lipschitz clamps and applying dominated convergence
avoids any integrability assumption on the logarithmic normalization.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace DukePrimeDegree

lemma realClamp_lipschitz (M : ℝ) : LipschitzWith 1 (realClamp M) :=
  (LipschitzWith.id.const_min M).const_max (-M)

lemma realClamp_eq {M x : ℝ} (hx : |x| ≤ M) : realClamp M x=x := by
  have h := abs_le.mp hx
  simp only [realClamp,min_eq_right h.2,max_eq_right h.1]

lemma realClamp_abs_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |realClamp M x| ≤ M := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma realClamp_difference_le (M x y : ℝ) :
    |realClamp M x-realClamp M y| ≤ |x-y| := by
  have H := (realClamp_lipschitz M).dist_le_mul x y
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using H

theorem integral_coboundary_eq_zero {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) {f : Y → ℝ} (hf : StronglyMeasurable f)
    (hdf : Integrable (fun y => f y-f (T y)) μ) :
    (∫ y, f y-f (T y) ∂μ)=0 := by
  let F : ℕ → Y → ℝ := fun n y => realClamp n (f y)
  have hFm n : StronglyMeasurable (F n) :=
    (realClamp_lipschitz n).continuous.comp_stronglyMeasurable hf
  have hFi n : Integrable (F n) μ := by
    apply (integrable_const (n:ℝ)).mono' (hFm n).aestronglyMeasurable
    exact ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs] using realClamp_abs_le (Nat.cast_nonneg n) (f y)
  have hFTi n : Integrable (fun y => F n (T y)) μ := hT.integrable_comp_of_integrable (hFi n)
  have hInt n : (∫ y, F n (T y) ∂μ) = ∫ y, F n y ∂μ := by
    rw [←integral_map hT.measurable.aemeasurable (hFm n).aestronglyMeasurable,hT.map_eq]
  have hzero n : (∫ y, F n y-F n (T y) ∂μ)=0 := by
    rw [integral_sub (hFi n) (hFTi n),hInt n,sub_self]
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun n => F n y-F n (T y)) atTop (𝓝 (f y-f (T y))) := by
    apply ae_of_all
    intro y
    obtain ⟨N,hN⟩ := exists_nat_gt (max |f y| |f (T y)|)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N:ℝ) ≤ n := Nat.cast_le.mpr hn
    have hy : |f y| ≤ (n:ℝ) := (le_max_left _ _).trans (le_of_lt hN) |>.trans hn'
    have hTy : |f (T y)| ≤ (n:ℝ) := (le_max_right _ _).trans (le_of_lt hN) |>.trans hn'
    simp only [F,realClamp_eq hy,realClamp_eq hTy]
  have hbound n : ∀ᵐ y ∂μ, ‖F n y-F n (T y)‖ ≤ ‖f y-f (T y)‖ :=
    ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs] using realClamp_difference_le n (f y) (f (T y))
  have H := tendsto_integral_of_dominated_convergence
    (fun y => ‖f y-f (T y)‖) (fun n => ((hFi n).sub (hFTi n)).aestronglyMeasurable)
    hdf.norm hbound hlim
  have H0 : Tendsto (fun n => ∫ y, F n y-F n (T y) ∂μ) atTop (𝓝 (0:ℝ)) := by
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique H H0

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OneSidedCoboundary
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-sided integrable bounds for measurable coboundaries

The normalization transfer in the leaf-information identity need not be
integrable. A one-sided integrable bound on its difference is sufficient.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

lemma realClamp_monotone (M : ℝ) : Monotone (realClamp M) := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

theorem integrable_coboundary_of_lower_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) {f b : Y → ℝ}
    (hf : StronglyMeasurable f) (hb : Integrable b μ)
    (hlower : ∀ᵐ y ∂μ, -|b y| ≤ f y-f (T y)) :
    Integrable (fun y => f y-f (T y)) μ := by
  let F : ℕ → Y → ℝ := fun n y => realClamp n (f y)
  let D : ℕ → Y → ℝ := fun n y => F n y-F n (T y)
  have hFm (n : ℕ) : StronglyMeasurable (F n) :=
    (realClamp_lipschitz n).continuous.comp_stronglyMeasurable hf
  have hFi (n : ℕ) : Integrable (F n) μ := by
    apply (integrable_const (n:ℝ)).mono' (hFm n).aestronglyMeasurable
    exact ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs] using realClamp_abs_le (Nat.cast_nonneg n) (f y)
  have hDi (n : ℕ) : Integrable (D n) μ :=
    (hFi n).sub (hT.integrable_comp_of_integrable (hFi n))
  have hzero (n : ℕ) : (∫ y, D n y ∂μ)=0 :=
    integral_coboundary_eq_zero μ hT (hFm n) (hDi n)
  have hnegative (n : ℕ) : ∀ᵐ y ∂μ, (D n y)⁻ ≤ |b y| := by
    filter_upwards [hlower] with y hy
    change max (-(D n y)) 0 ≤ |b y|
    apply max_le _ (abs_nonneg _)
    by_cases h : f (T y) ≤ f y
    · have hm := realClamp_monotone (n:ℝ) h
      change -(realClamp n (f y)-realClamp n (f (T y))) ≤ _
      exact (neg_nonpos.mpr (sub_nonneg.mpr hm)).trans (abs_nonneg _)
    · have hd := realClamp_difference_le n (f y) (f (T y))
      rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))] at hd
      change -(realClamp n (f y)-realClamp n (f (T y))) ≤ _
      exact (neg_le_abs _).trans (hd.trans (by linarith))
  have hL1 (n : ℕ) : (∫ y, ‖D n y‖ ∂μ) ≤ 2 * ∫ y, |b y| ∂μ := by
    simp only [Real.norm_eq_abs]
    rw [integral_abs_eq_two_mul_integral_negPart_add_integral (hDi n), hzero, add_zero]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact integral_mono_ae ((hDi n).neg.sup (integrable_const 0)) hb.abs (hnegative n)
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun n => D n y) atTop (𝓝 (f y-f (T y))) := by
    apply ae_of_all
    intro y
    obtain ⟨N,hN⟩ := exists_nat_gt (max |f y| |f (T y)|)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N:ℝ) ≤ n := Nat.cast_le.mpr hn
    have hy : |f y| ≤ (n:ℝ) := (le_max_left _ _).trans hN.le |>.trans hn'
    have hTy : |f (T y)| ≤ (n:ℝ) := (le_max_right _ _).trans hN.le |>.trans hn'
    simp only [D,F,realClamp_eq hy,realClamp_eq hTy]
  have hFatou : (∫⁻ y, ‖f y-f (T y)‖ₑ ∂μ) ≤
      liminf (fun n => ∫⁻ y, ‖D n y‖ₑ ∂μ) atTop := by
    calc
      _ = ∫⁻ y, liminf (fun n => ‖D n y‖ₑ) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono fun _ hy => hy.enorm.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' fun n => (hDi n).aestronglyMeasurable.aemeasurable.enorm
  have hbound : liminf (fun n => ∫⁻ y, ‖D n y‖ₑ ∂μ) atTop ≤
      ENNReal.ofReal (2 * ∫ y, |b y| ∂μ) := by
    apply le_trans (liminf_le_liminf (Eventually.of_forall (fun n => ?_)))
      (le_of_eq (liminf_const _))
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hDi n)]
    exact ENNReal.ofReal_le_ofReal (hL1 n)
  refine ⟨(hf.sub (hf.comp_measurable hT.measurable)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (hFatou.trans hbound).trans_lt ENNReal.ofReal_lt_top

/-- A nonnegative information function differing from an integrable
reference by a measurable coboundary has the same integral. -/
theorem information_integrable_integral_of_coboundary {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) {f J I : Y → ℝ}
    (hf : StronglyMeasurable f) (hJ : Integrable J μ)
    (hI : ∀ᵐ y ∂μ, 0 ≤ I y)
    (heq : I =ᵐ[μ] fun y => J y + (f y-f (T y))) :
    Integrable I μ ∧ (∫ y, I y ∂μ) = ∫ y, J y ∂μ := by
  have hd := integrable_coboundary_of_lower_bound μ hT hf hJ (by
    filter_upwards [hI, heq] with y hy he
    have hj := le_abs_self (J y)
    linarith)
  refine ⟨(hJ.add hd).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_add hJ hd,
    integral_coboundary_eq_zero μ hT hf hd, add_zero]

/-- Null-set changes in the transfer do not affect the information identity. -/
theorem information_integrable_integral_of_ae_coboundary {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) {f J I : Y → ℝ}
    (hf : AEStronglyMeasurable f μ) (hJ : Integrable J μ)
    (hI : ∀ᵐ y ∂μ, 0 ≤ I y)
    (heq : I =ᵐ[μ] fun y => J y + (f y-f (T y))) :
    Integrable I μ ∧ (∫ y, I y ∂μ) = ∫ y, J y ∂μ := by
  apply information_integrable_integral_of_coboundary μ hT
    hf.stronglyMeasurable_mk hJ hI
  filter_upwards [heq, hf.ae_eq_mk, hT.quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk]
    with y hy hf₀ hf₁
  change f (T y) = hf.mk f (T y) at hf₁
  rwa [hf₀, hf₁] at hy

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootEuclideanCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One real coordinate for each positive root

The elimination time space is canonically a finite product of real
lines, indexed without repetition by the positive roots. Diagonal
conjugation scales each coordinate by its own root character.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma timeVectorHomeomorph_cube (c : EliminationChain P D) (R : ℝ) (t : c.Time) :
    t ∈ c.cube R ↔ ∀ k, |c.timeVectorHomeomorph t k| < R := by
  induction c with
  | done => simp [cube, roots]
  | step a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      change t.1 ∈ tail.cube R ∧ t.2 ∈ Ioo (-R) R ↔
        ∀ k : Fin (tail.roots.length + 1),
          |Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ) t.2 (tail.timeVectorHomeomorph t.1) k| < R
      rw [ih, Set.mem_Ioo, ←abs_lt]
      constructor
      · rintro ⟨h₁, h₂⟩ k
        refine Fin.cases ?_ (fun j => ?_) k
        · simpa only [Fin.cons_zero] using h₂
        · simpa only [Fin.cons_succ] using h₁ j
      · intro h
        exact ⟨fun j => by simpa only [Fin.cons_succ] using h j.succ,
          by simpa only [Fin.cons_zero] using h 0⟩

lemma timeVectorHomeomorph_dilation (c : EliminationChain P D) (ell : Fin n → ℝ)
    (r : ℝ) (t : c.Time) (k : Fin c.roots.length) :
    c.timeVectorHomeomorph (c.rootDilation ell r t) k =
      Real.exp ((ell (c.roots.get k).1 - ell (c.roots.get k).2) * r) *
        c.timeVectorHomeomorph t k := by
  induction c with
  | done => exact Fin.elim0 k
  | step a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      change Fin (tail.roots.length + 1) at k
      change Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ)
        (Real.exp ((ell a - ell b) * r) * t.2)
          (tail.timeVectorHomeomorph (tail.rootDilation ell r t.1)) k =
        Real.exp ((ell (((a, b) :: tail.roots).get k).1 -
          ell (((a, b) :: tail.roots).get k).2) * r) *
            Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ)
              t.2 (tail.timeVectorHomeomorph t.1) k
      refine Fin.cases ?_ (fun j => ?_) k
      · rfl
      · exact ih t.1 j

end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingProductMass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mass of actual remaining-root cubes under the intrinsic product -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma remainingEuclideanCoordinates_cube (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) (R : ℝ) (t : c.Time) :
    t ∈ c.cube R ↔ ∀ p, |c.remainingEuclideanCoordinates hfinal t p| < R := by
  rw [c.timeVectorHomeomorph_cube]
  change (∀ k, |c.timeVectorHomeomorph t k| < R) ↔
    ∀ p, |c.timeVectorHomeomorph t ((c.remainingIndexEquiv hfinal).symm p)| < R
  constructor
  · exact fun h p => h _
  · intro h k
    simpa only [Equiv.symm_apply_apply] using h (c.remainingIndexEquiv hfinal k)

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NormalizedPiMeasures
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalization of finite products on rectangles -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {ι : Type*} [Fintype ι] {A : ι → Type*}
  [∀ i, MeasurableSpace (A i)]

lemma pi_smul_measures (ν : (i : ι) → Measure (A i)) [∀ i, SigmaFinite (ν i)]
    (c : ι → ℝ≥0∞) [∀ i, SigmaFinite (c i • ν i)] :
    Measure.pi (fun i => c i • ν i) = (∏ i, c i) • Measure.pi ν := by
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

lemma sigmaFinite_anchorNormalize {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [SigmaFinite ν] (V : Set B) (hV : ν V ≠ 0) :
    SigmaFinite (anchorNormalize ν V) := by
  have h : (((ν V)⁻¹).toNNReal : ℝ≥0∞) = (ν V)⁻¹ :=
    ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hV)
  unfold anchorNormalize
  rw [←h, Measure.coe_nnreal_smul]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem pi_anchorNormalize (ν : (i : ι) → Measure (A i)) [∀ i, SigmaFinite (ν i)]
    (V : (i : ι) → Set (A i)) (h0 : ∀ i, ν i (V i) ≠ 0) :
    Measure.pi (fun i => anchorNormalize (ν i) (V i)) =
      anchorNormalize (Measure.pi ν) (Set.univ.pi V) := by
  let : ∀ i, SigmaFinite ((ν i (V i))⁻¹ • ν i) :=
    fun i => sigmaFinite_anchorNormalize (ν i) (V i) (h0 i)
  unfold anchorNormalize
  rw [pi_smul_measures, Measure.pi_pi,
    ENNReal.prod_inv_distrib (fun i _ _ _ _ => Or.inl (h0 i))]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootProductCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal covariance of the actual product of root leaves

The normalization is on the unit rectangle. No independence or
conditional-entropy identification is assumed in this calculation.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

private lemma locallyFinite_map_real (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (E : ℝ ≃ₜ ℝ) : IsLocallyFiniteMeasure (ν.map E) := by
  constructor
  intro x
  obtain ⟨U, hx, hU, hfin⟩ := Measure.exists_isOpen_measure_lt_top ν (E.symm x)
  refine ⟨E '' U, (E.isOpenMap _ hU).mem_nhds ⟨E.symm x, hx, E.apply_symm_apply x⟩, ?_⟩
  rw [Measure.map_apply E.measurable (E.isOpenMap _ hU).measurableSet,
    E.injective.preimage_image]
  exact hfin

theorem ae_rootProduct_diagonal {ι : Type*} [Fintype ι]
    (d : ℕ) (i j : ι → Fin (d+1)) (hij : ∀ a, i a ≠ j a)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k = 0) (t : ℝ) :
    ∀ᵐ x ∂μ,
      (Measure.pi fun a => intrinsicRootLeaf (hij a) μ
        (rightAction x (diagonalOneParameter ell hell t))) =
      anchorNormalize
        ((Measure.pi fun a => intrinsicRootLeaf (hij a) μ x).map
          (fun v a => rootTimeScaling ell (i a) (j a) t (v a)))
        (Set.univ.pi fun _ : ι => Metric.ball 0 1) := by
  have hfree (a : ι) : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection (hij a) v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx (i a) (j a) (hij a)
  have hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ := by
    rw [diagonalOneParameter_eq_diagonalFlow ell hell t]
    exact hA _
  have hcov := ae_all_iff.mpr (fun a =>
    ae_intrinsicRootLeaf_diagonal (hij a) ell hell t μ (hfree a) hinv)
  have hspec := ae_all_iff.mpr (fun a => ae_intrinsicRootLeaf_spec (hij a) μ (hfree a))
  have hpos := ae_all_iff.mpr (fun a => ae_intrinsicRootLeaf_ball_pos (hij a) μ (hfree a))
  filter_upwards [hcov, hspec, hpos] with x hx hs hp
  let ν : ι → Measure ℝ := fun a => intrinsicRootLeaf (hij a) μ x
  let F (a : ι) := rootTimeScaling ell (i a) (j a) t
  let : ∀ a, IsLocallyFiniteMeasure (ν a) := fun a => (hs a).1
  let : ∀ a, IsLocallyFiniteMeasure ((ν a).map (F a)) :=
    fun a => locallyFinite_map_real (ν a) (F a)
  have hmass (a : ι) : (ν a).map (F a) (Metric.ball 0 1) ≠ 0 := by
    rw [Measure.map_apply (F a).measurable isOpen_ball.measurableSet]
    change ν a ((Homeomorph.mulLeft₀ _ _) ⁻¹' Metric.ball 0 1) ≠ 0
    rw [realScaling_preimage_ball _ _ (Real.exp_pos _)]
    exact (hp a _ (by positivity)).ne'
  calc
    _ = Measure.pi (fun a => anchorNormalize ((ν a).map (F a)) (Metric.ball 0 1)) := by
      congr 1
      funext a
      exact hx a
    _ = anchorNormalize (Measure.pi fun a => (ν a).map (F a))
        (Set.univ.pi fun _ : ι => Metric.ball 0 1) :=
      pi_anchorNormalize _ _ hmass
    _ = _ := by
      rw [Measure.pi_map_pi (fun a => (F a).measurable.aemeasurable)]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingProductDiagonal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal covariance in actual remaining-root time coordinates -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma remainingEuclideanCoordinates_dilation (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n) (ell : Fin n → ℝ) (r : ℝ)
    (u : c.Time) (p : ↥(allPositiveRoots n \ P)) :
    c.remainingEuclideanCoordinates hf (c.rootDilation ell r u) p =
      Real.exp ((ell p.val.1 - ell p.val.2) * r) *
        c.remainingEuclideanCoordinates hf u p := by
  have h := c.timeVectorHomeomorph_dilation ell r u ((c.remainingIndexEquiv hf).symm p)
  have he : c.roots.get ((c.remainingIndexEquiv hf).symm p) = p.val :=
    congrArg Subtype.val ((c.remainingIndexEquiv hf).apply_symm_apply p)
  change c.timeVectorHomeomorph (c.rootDilation ell r u) ((c.remainingIndexEquiv hf).symm p) =
    Real.exp ((ell p.val.1 - ell p.val.2) * r) *
      c.timeVectorHomeomorph u ((c.remainingIndexEquiv hf).symm p)
  simpa only [he] using h

lemma remainingTimeProduct_eq_map (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) :
    c.remainingTimeProduct hP hf μ x =
      (Measure.pi fun p : ↥(allPositiveRoots n \ P) =>
        intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x).map
          (c.remainingEuclideanCoordinates hf).symm := by
  unfold remainingTimeProduct remainingIntrinsicProduct
  rw [Measure.map_map (c.remainingWordHomeomorph hP hf).symm.measurable
    (c.remainingGroupCoordinates hP hf).symm.measurable]
  congr 1
  funext v
  simp [remainingGroupCoordinates]

lemma remainingCoordinates_unit_cube (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n) :
    (c.remainingEuclideanCoordinates hf).symm ''
      (Set.univ.pi fun _ : ↥(allPositiveRoots n \ P) => Metric.ball 0 1) = c.cube 1 := by
  let E := c.remainingEuclideanCoordinates hf
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    apply (c.remainingEuclideanCoordinates_cube hf 1 _).mpr
    intro p
    have hp := hv p (mem_univ p)
    change |E (E.symm v) p| < 1
    rw [E.apply_symm_apply]
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hp
  · intro hu
    refine ⟨E u, ?_, E.symm_apply_apply u⟩
    intro p _
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      (c.remainingEuclideanCoordinates_cube hf 1 u).mp hu p

theorem ae_remainingTimeProduct_diagonal (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k = 0) (t : ℝ) :
    ∀ᵐ x ∂μ,
      c.remainingTimeProduct hP hf μ (rightAction x (diagonalOneParameter ell hell t)) =
        anchorNormalize ((c.remainingTimeProduct hP hf μ x).map (c.rootDilation ell (-t)))
          (c.cube 1) := by
  let I := ↥(allPositiveRoots (d+1) \ P)
  let E := c.remainingEuclideanCoordinates hf
  let S : (I → ℝ) → (I → ℝ) := fun v p => rootTimeScaling ell p.val.1 p.val.2 t (v p)
  let ν := fun x => Measure.pi fun p : I =>
    intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x
  let R : Set (I → ℝ) := Set.univ.pi fun _ : I => Metric.ball 0 1
  have hcov := ae_rootProduct_diagonal d (fun p : I => p.val.1) (fun p : I => p.val.2)
    (fun p => ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2)
    μ hA ell hell t
  filter_upwards [hcov] with x hx
  change ν (rightAction x (diagonalOneParameter ell hell t)) =
    anchorNormalize ((ν x).map S) R at hx
  have hS : Measurable S := measurable_pi_iff.mpr fun p =>
    (rootTimeScaling ell p.val.1 p.val.2 t).measurable.comp (measurable_pi_apply p)
  have he : E.symm ∘ S = c.rootDilation ell (-t) ∘ E.symm := by
    funext v
    apply E.injective
    change E (E.symm (S v)) = E (c.rootDilation ell (-t) (E.symm v))
    rw [E.apply_symm_apply]
    funext p
    rw [c.remainingEuclideanCoordinates_dilation hf]
    change Real.exp ((ell p.val.2 - ell p.val.1) * t) * v p =
      Real.exp ((ell p.val.1 - ell p.val.2) * (-t)) * E (E.symm v) p
    rw [E.apply_symm_apply]
    congr 2
    ring
  rw [c.remainingTimeProduct_eq_map hP hf, c.remainingTimeProduct_eq_map hP hf]
  change (ν (rightAction x (diagonalOneParameter ell hell t))).map E.symm =
    anchorNormalize (((ν x).map E.symm).map (c.rootDilation ell (-t))) (c.cube 1)
  have hnorm : (anchorNormalize ((ν x).map S) R).map E.symm =
      anchorNormalize (((ν x).map S).map E.symm) (E.symm '' R) := by
    simpa only [Homeomorph.toMeasurableEquiv_coe] using
      (anchorNormalize_map_equiv ((ν x).map S) E.symm.toMeasurableEquiv R).symm
  rw [hx, hnorm, c.remainingCoordinates_unit_cube hf]
  congr 1
  rw [Measure.map_map E.symm.measurable hS,
    Measure.map_map (c.rootDilation ell (-t)).measurable E.symm.measurable, he]

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RemainingFutureShift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact shift of future atoms along remaining-root leaves -/

noncomputable section
open Set
open MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma measurableSet_remainingFutureAtom (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) (x : X n) :
    MeasurableSet (c.remainingFutureAtom ell hell Q m x) := by
  let T : X n → X n := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry n).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  change MeasurableSet {u | ∀ k : ℕ, Q (T^[k+m] (rightAction x (c.word u))) = _}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (hQ.comp ((hT.iterate (k+m)).comp hF)) (measurableSet_singleton _)

lemma remainingFutureAtom_zero_subset_one (c : EliminationChain P D)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (Q : X n → ℕ) (x : X n) :
    c.remainingFutureAtom ell hell Q 0 x ⊆ c.remainingFutureAtom ell hell Q 1 x := by
  intro u hu k
  simpa only [Nat.add_zero] using hu (k+1)

lemma remaining_orbit_diagonal (c : EliminationChain P D)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (x : X n) (u : c.Time) :
    rightAction (rightAction x (diagonalOneParameter ell hell (-1)))
        (c.word (c.rootDilation ell 1 u)) =
      rightAction (rightAction x (c.word u)) (diagonalOneParameter ell hell (-1)) := by
  rw [rightAction_mul, rightAction_mul, c.word_rootDilation ell hell 1,
    diagonalOneParameter_neg]
  congr 1
  group

theorem remainingFutureAtom_shift (c : EliminationChain P D)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (Q : X n → ℕ) (x : X n) :
    (c.rootDilation ell 1) ⁻¹'
      c.remainingFutureAtom ell hell Q 0
        (rightAction x (diagonalOneParameter ell hell (-1))) =
      c.remainingFutureAtom ell hell Q 1 x := by
  ext u
  simp only [mem_preimage, remainingFutureAtom, Set.mem_ofPred_eq, Nat.add_zero,
    c.remaining_orbit_diagonal ell hell, Function.iterate_succ_apply]

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureAtomCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact covariance of actual whole-future leaf masses -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_mass_log_identity {a b c d : ℝ≥0∞}
    (ha0 : a ≠ 0) (haT : a ≠ ∞) (hb0 : b ≠ 0) (hbT : b ≠ ∞)
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) (hd : d = c⁻¹ * b) :
    -Real.log (a / b).toReal =
      Real.log c.toReal + (-Real.log a.toReal) - (-Real.log d.toReal) := by
  have ha : a.toReal ≠ 0 := (ENNReal.toReal_pos ha0 haT).ne'
  have hb : b.toReal ≠ 0 := (ENNReal.toReal_pos hb0 hbT).ne'
  have hc : c.toReal ≠ 0 := (ENNReal.toReal_pos hc0 hcT).ne'
  rw [ENNReal.toReal_div, Real.log_div ha hb, hd,
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    Real.log_mul (inv_ne_zero hc) hb, Real.log_inv]
  ring

namespace EliminationChain

theorem ae_remainingTimeProduct_futureAtom (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k = 0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q) :
    ∀ᵐ x ∂μ,
      c.remainingTimeProduct hP hf μ (rightAction x (diagonalOneParameter ell hell (-1)))
          (c.remainingFutureAtom ell hell Q 0
            (rightAction x (diagonalOneParameter ell hell (-1)))) =
        (c.remainingTimeProduct hP hf μ x
          ((c.rootDilation ell 1) ⁻¹' c.cube 1))⁻¹ *
        c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 1 x) := by
  filter_upwards [ae_remainingTimeProduct_diagonal d c hP hf μ hA ell hell (-1)] with x hx
  rw [hx]
  simp only [neg_neg]
  rw [anchorNormalize, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (c.rootDilation ell 1).measurable
      (c.measurableSet_remainingFutureAtom hf ell hell Q hQ 0 _),
    c.remainingFutureAtom_shift ell hell Q x,
    Measure.map_apply (c.rootDilation ell 1).measurable (c.cube_open 1).measurableSet]

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootInformationScale
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact scaling of the mean root information

The actual normalized leaf information is additive under the canonical
flow. Monotonicity and rational approximation promote its integer-time
scaling law to every nonnegative real time, including infinite means.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
  (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

lemma rootInformationMean_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    rootInformationMean hij μ s ≤ rootInformationMean hij μ t := by
  have he := rootInformationMean_add d hij μ hA hs (sub_nonneg.mpr hst)
  rw [add_sub_cancel] at he
  rw [he]
  exact le_add_right le_rfl

lemma rootInformationMean_rat (m n : ℕ) :
    rootInformationMean hij μ ((m : ℝ) / n) =
      ENNReal.ofReal ((m : ℝ) / n) * rootInformationMean hij μ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [rootInformationMean_zero_time d hij μ hA]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  let f := rootInformationHom d hij μ hA
  have hdiv : ((m : ℝ≥0) / n) = (n⁻¹ : ℝ≥0) • (m : ℝ≥0) := by
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hm : f (m : ℝ≥0) = (m : ℝ≥0∞) * f 1 := by
    simpa only [nsmul_eq_mul, mul_one] using f.map_nsmul m (1 : ℝ≥0)
  have h := map_inv_natCast_smul f ℝ≥0 ℝ≥0 n (m : ℝ≥0)
  rw [← hdiv, hm, ENNReal.smul_def, smul_eq_mul] at h
  change rootInformationMean hij μ (↑((m : ℝ≥0) / n)) =
    (↑((n : ℝ≥0)⁻¹) : ℝ≥0∞) * ((m : ℝ≥0∞) * rootInformationMean hij μ 1) at h
  rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast,
    ENNReal.coe_inv (by exact_mod_cast hn), ENNReal.coe_natCast] at h
  rw [ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, div_eq_mul_inv]
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- The mean at time one is the exact coefficient at every positive scale. -/
theorem rootInformationMean_real {t : ℝ} (ht : 0 ≤ t) :
    rootInformationMean hij μ t =
      ENNReal.ofReal t * rootInformationMean hij μ 1 := by
  by_cases ht0 : t = 0
  · subst t
    simp [rootInformationMean_zero_time d hij μ hA]
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let lo (n : ℕ) : ℝ := (⌊t * (n + 1 : ℝ)⌋₊ : ℝ) / (n + 1 : ℝ)
  let hi (n : ℕ) : ℝ := (⌈t * (n + 1 : ℝ)⌉₊ : ℝ) / (n + 1 : ℝ)
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hlo : Tendsto lo atTop (𝓝 t) := (tendsto_nat_floor_mul_div_atTop ht).comp hn
  have hhi : Tendsto hi atTop (𝓝 t) := (tendsto_nat_ceil_mul_div_atTop ht).comp hn
  have hlo_le (n : ℕ) : lo n ≤ t := by
    dsimp only [lo]
    rw [div_le_iff₀ (by positivity)]
    exact Nat.floor_le (by positivity)
  have hle_hi (n : ℕ) : t ≤ hi n := by
    dsimp only [hi]
    rw [le_div_iff₀ (by positivity)]
    exact Nat.le_ceil _
  have hlo0 (n : ℕ) : 0 ≤ lo n := by dsimp [lo] <;> positivity
  have hlot := ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.tendsto t |>.comp hlo)
    (b := rootInformationMean hij μ 1) (Or.inl (ENNReal.ofReal_pos.mpr htp).ne')
  have hhit := ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.tendsto t |>.comp hhi)
    (b := rootInformationMean hij μ 1) (Or.inl (ENNReal.ofReal_pos.mpr htp).ne')
  apply le_antisymm
  · apply ge_of_tendsto hhit
    apply Eventually.of_forall
    intro n
    have hm := rootInformationMean_mono d hij μ hA ht (hle_hi n)
    have hr := rootInformationMean_rat d hij μ hA ⌈t * (n + 1 : ℝ)⌉₊ (n + 1)
    have hr' : rootInformationMean hij μ (hi n) =
        ENNReal.ofReal (hi n) * rootInformationMean hij μ 1 := by
      simpa only [hi, Nat.cast_add, Nat.cast_one] using hr
    exact hm.trans_eq hr'
  · apply le_of_tendsto hlot
    apply Eventually.of_forall
    intro n
    have hm := rootInformationMean_mono d hij μ hA (hlo0 n) (hlo_le n)
    have hr := rootInformationMean_rat d hij μ hA ⌊t * (n + 1 : ℝ)⌋₊ (n + 1)
    have hr' : rootInformationMean hij μ (lo n) =
        ENNReal.ofReal (lo n) * rootInformationMean hij μ 1 := by
      simpa only [lo, Nat.cast_add, Nat.cast_one] using hr
    exact hr'.symm.trans_le hm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RealLeafDensity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Linear lower bounds at typical centers of real leaf measures

Differentiation of Lebesgue measure relative to an arbitrary locally
finite real measure bounds their small-ball ratio at almost every center.
This supplies the dimension-one bound for actual root information.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree

/-- A locally finite measure has at least linear mass in small balls
around almost every one of its own typical points. -/
theorem ae_real_ball_linear_lower_bound (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    ∀ᵐ x ∂ν, ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ᶠ r : ℝ in 𝓝[>] 0, ENNReal.ofReal r ≤ C * ν (ball x r) := by
  have hhalf : Tendsto (fun r : ℝ => r / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun r : ℝ => r / 2) := continuous_id.div_const 2
      simpa only [zero_div] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < r / 2
      exact div_pos (show 0 < r from hr) (by norm_num)
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv (volume : Measure ℝ) ν,
    Measure.rnDeriv_lt_top (volume : Measure ℝ) ν] with x hx hfin
  let C := (volume : Measure ℝ).rnDeriv ν x + 1
  have hC : C ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hfin.ne, ENNReal.one_ne_top⟩
  have hC0 : C ≠ 0 := by dsimp [C] <;> positivity
  have hless : (volume : Measure ℝ).rnDeriv ν x < C := ENNReal.lt_add_right hfin.ne one_ne_zero
  have hbound := (hx.comp hhalf).eventually (gt_mem_nhds hless)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, self_mem_nhdsWithin] with r hr hr0
  change 0 < r at hr0
  have h := (ENNReal.div_le_iff_le_mul (Or.inr hC) (Or.inr hC0)).mp hr.le
  have hs : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  have hvol : (volume : Measure ℝ) (closedBall x (r / 2)) = ENNReal.ofReal r := by
    rw [Real.volume_closedBall]
    congr 1
    ring
  rw [hvol] at h
  exact h.trans (by simpa only [mul_comm] using
    (mul_le_mul_left (measure_mono hs : ν (closedBall x (r / 2)) ≤ ν (ball x r)) C))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootLeafLowerBound
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Typical root leaves have a linear lower mass bound

The property is expressed at countably many exponential radii. This makes
it measurable and allows transfer through the actual root-box disintegration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma measurableSet_hasDiscreteLinearLowerBound :
    MeasurableSet {ν : Measure ℝ | HasDiscreteLinearLowerBound ν} := by
  simp only [HasDiscreteLinearLowerBound, Set.ofPred_exists, Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro C
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le measurable_const
    (measurable_const.mul (Measure.measurable_coe
      (isOpen_ball (x := (0 : ℝ)) (ε := Real.exp (-(n : ℝ)))).measurableSet))

lemma ae_basedRealMeasure_discrete_lower_bound (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    ∀ᵐ x ∂ν, HasDiscreteLinearLowerBound (basedRealMeasure ν x) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop),
      Eventually.of_forall fun n => Real.exp_pos _⟩
  filter_upwards [ae_real_ball_linear_lower_bound ν, ν.support_mem_ae] with x hx hs
  obtain ⟨C, hC, hbound⟩ := hx
  have hm : 0 < ν (ball x 1) :=
    (ν.mem_support_iff_forall x).mp hs _ (ball_mem_nhds _ zero_lt_one)
  have hmT : ν (ball x 1) ≠ ∞ := measure_ball_lt_top.ne
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt (ENNReal.mul_ne_top hC hmT)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hexp.eventually hbound)
  refine ⟨K, N, ?_⟩
  intro n hn
  have hmass : basedRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) =
      (ν (ball x 1))⁻¹ * ν (ball x (Real.exp (-(n : ℝ)))) := by
    change (centerRealMeasure ν x (ball 0 1))⁻¹ *
      centerRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) = _
    rw [centerRealMeasure_ball, centerRealMeasure_ball]
  have heq : (C * ν (ball x 1)) *
      basedRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) =
      C * ν (ball x (Real.exp (-(n : ℝ)))) := by
    rw [hmass, mul_assoc, ← mul_assoc (ν (ball x 1)),
      ENNReal.mul_inv_cancel hm.ne' hmT, one_mul]
  calc
    ENNReal.ofReal (Real.exp (-(n : ℝ))) ≤
        C * ν (ball x (Real.exp (-(n : ℝ)))) := hN n hn
    _ = (C * ν (ball x 1)) *
        basedRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) := heq.symm
    _ ≤ (K : ℝ≥0∞) * basedRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) :=
      mul_le_mul_left hK.le _

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma ae_basedLeaf_discrete_lower_bound (A : PrimeDegreePackets.RootBox hij k)
    (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, HasDiscreteLinearLowerBound (A.basedLeaf R μ z) := by
  let κ := A.regularLeafKernel R hAR μ hfree
  have hmeas : MeasurableSet {z : RootSlice i j k × ℝ |
      HasDiscreteLinearLowerBound (basedRealMeasure (κ z.1) z.2)} :=
    measurableSet_hasDiscreteLinearLowerBound.preimage (basedRealKernel κ).measurable
  have hbase : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.conditionalKernel μ s,
      HasDiscreteLinearLowerBound (basedRealMeasure (κ s) t) := by
    filter_upwards [A.ae_regularLeafKernel_eq R hAR μ hfree,
      A.ae_leafMeasure_spec R hAR μ hfree] with s hs hspec
    have hle : A.conditionalKernel μ s ≤ κ s := by
      rw [hs, ← hspec.2.2.1]
      exact Measure.restrict_le_self
    exact (ae_basedRealMeasure_discrete_lower_bound (κ s)).filter_mono
      (ae_mono hle)
  have H := Measure.ae_compProd_of_ae_ae hmeas hbase
  have H' : ∀ᵐ z ∂A.coordinateMeasure μ,
      HasDiscreteLinearLowerBound (basedRealMeasure (κ z.1) z.2) := by
    simpa only [PrimeDegreePackets.RootBox.conditionalKernel, Measure.disintegrate] using H
  have he : ∀ᵐ z ∂A.coordinateMeasure μ, κ z.1 = A.leafMeasure R μ z.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_regularLeafKernel_eq R hAR μ hfree)
  filter_upwards [H', he] with z hz hez
  simpa only [PrimeDegreePackets.RootBox.basedLeaf, ← hez] using hz

lemma ae_intrinsicRootLeaf_discrete_lower_bound_restrict
    (A : PrimeDegreePackets.RootBox hij k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ.restrict A.range, HasDiscreteLinearLowerBound (intrinsicRootLeaf hij μ x) := by
  apply A.ae_of_coordinate μ
  filter_upwards [A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
    ae_basedLeaf_discrete_lower_bound A R hAR μ hfree] with z he hz
  rwa [he]

end RootBox

/-- The actual intrinsic root leaf has a linear lower mass bound at almost
all base points. No entropy input is assumed. -/
theorem ae_intrinsicRootLeaf_discrete_lower_bound {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, HasDiscreteLinearLowerBound (intrinsicRootLeaf hij μ x) := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := (ae_restrict_iUnion_iff (μ := μ)
    (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr
    (fun B => RootBox.ae_intrinsicRootLeaf_discrete_lower_bound_restrict
      B.val.box B.val.radius B.val.time_bound μ hfree)
  simpa only [boundedRootAtlas_iUnion, Measure.restrict_univ] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootInformationGrowth
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Linear growth of actual root information

Small-ball differentiation bounds the information along integer scales.
The actual scaling cocycle identifies these scales with Birkhoff sums.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
  (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

/-- The information at integer time is the corresponding finite orbit sum. -/
lemma ae_rootInformation_nat_sum (n : ℕ) :
    ∀ᵐ x ∂μ, rootInformation hij μ n x =
      birkhoffSum (fun y => rightAction y (rootCanonicalFlow d j 1))
        (rootInformation hij μ 1) n x := by
  induction n with
  | zero =>
    have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
        rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
      (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
    filter_upwards [ae_intrinsicRootLeaf_spec hij μ hfree] with x hx
    simp [rootInformation, hx.2]
  | succ n ih =>
    have hT := rootCanonicalFlow_preserving d j 1 μ hA
    have him : ∀ᵐ y ∂μ.map (fun y => rightAction y (rootCanonicalFlow d j 1)),
        rootInformation hij μ n y =
          birkhoffSum (fun y => rightAction y (rootCanonicalFlow d j 1))
            (rootInformation hij μ 1) n y := by
      rw [hT.map_eq]
      exact ih
    have hip := ae_of_ae_map hT.measurable.aemeasurable him
    filter_upwards [hip, ae_rootInformation_cocycle d hij μ hA n 1] with x hi hc
    simpa only [Nat.cast_succ, hi, birkhoffSum_succ'] using hc

/-- Root information grows at most linearly, with slope one and a
point-dependent additive constant. -/
lemma ae_rootInformation_linear_bound :
    ∀ᵐ x ∂μ, ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      rootInformation hij μ n x ≤ n + B := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [ae_intrinsicRootLeaf_discrete_lower_bound hij μ hfree,
    ae_intrinsicRootLeaf_spec hij μ hfree,
    ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx hs hp
  let ν := intrinsicRootLeaf hij μ x
  let : IsLocallyFiniteMeasure ν := hs.1
  obtain ⟨C, N, hCN⟩ := hx
  refine ⟨Real.log (C + 1 : ℝ), N, ?_⟩
  intro n hn
  have hr := Real.exp_pos (-(n : ℝ))
  have hm : 0 < ν (ball 0 (Real.exp (-(n : ℝ)))) := hp _ hr
  have hfin : ν (ball 0 (Real.exp (-(n : ℝ)))) ≠ ∞ := measure_ball_lt_top.ne
  have hbig : ENNReal.ofReal (Real.exp (-(n : ℝ))) ≤
      ((C + 1 : ℕ) : ℝ≥0∞) * ν (ball 0 (Real.exp (-(n : ℝ)))) :=
    (hCN n hn).trans (mul_le_mul_left (by exact_mod_cast Nat.le_succ C) _)
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) hfin) hbig
  rw [ENNReal.toReal_ofReal hr.le, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  simp only [Nat.cast_add, Nat.cast_one] at hreal
  have hmreal : 0 < (ν (ball 0 (Real.exp (-(n : ℝ))))).toReal :=
    ENNReal.toReal_pos hm.ne' hfin
  have hlog := Real.log_le_log hr hreal
  rw [Real.log_exp, Real.log_mul (by positivity) hmreal.ne'] at hlog
  change -Real.log (ν (ball 0 (Real.exp (-(n : ℝ))))).toReal ≤ _
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootInformationBound
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual root information coefficient lies in the unit interval

Truncation, finite Hopf bounds and monotone convergence turn the almost
sure linear small-ball bound into a finite mean bound. No entropy formula
or ergodic theorem is assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
  (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

/-- The coefficient defined by the actual root leaf information is finite
and at most one. -/
theorem rootInformationMean_le_one : rootInformationMean hij μ 1 ≤ 1 := by
  let T : X (d + 1) → X (d + 1) := fun x => rightAction x (rootCanonicalFlow d j 1)
  have hT : MeasurePreserving T μ μ := rootCanonicalFlow_preserving d j 1 μ hA
  have hmeas := aemeasurable_rootInformation d hij μ hA 1
  let f : X (d + 1) → ℝ := fun x => max (hmeas.mk (rootInformation hij μ 1) x) 0
  have hfm : Measurable f := hmeas.measurable_mk.max measurable_const
  have hfnonneg (x) : 0 ≤ f x := le_max_right _ _
  have hfeq : f =ᵐ[μ] rootInformation hij μ 1 := by
    filter_upwards [hmeas.ae_eq_mk, ae_rootInformation_nonneg d hij μ hA zero_le_one] with x hx hn
    exact (congrArg (max · 0) hx).symm.trans (max_eq_left hn)
  let g (M : ℕ) (x : X (d + 1)) : ℝ := min (f x) M
  have hgm (M : ℕ) : Measurable (g M) := hfm.min measurable_const
  have hg0 (M : ℕ) (x) : 0 ≤ g M x := le_min (hfnonneg x) (Nat.cast_nonneg M)
  have hgint (M : ℕ) : Integrable (g M) μ :=
    integrable_of_le_of_le (hgm M).aestronglyMeasurable
      (Eventually.of_forall (hg0 M)) (Eventually.of_forall fun x => min_le_right (f x) (M : ℝ))
      (integrable_const 0) (integrable_const (M : ℝ))
  have hsum : ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffSum T f n x = rootInformation hij μ n x := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [hT.quasiMeasurePreserving.birkhoffSum_ae_eq_of_ae_eq hfeq n,
      ae_rootInformation_nat_sum d hij μ hA n] with x he hs
    exact he.trans hs.symm
  have hgmean (M : ℕ) : (∫ x, g M x ∂μ) ≤ 1 := by
    have hbound (c : ℝ) (hc : 1 < c) : (∫ x, g M x ∂μ) ≤ c := by
      apply integral_le_of_ae_birkhoffSum_lt hT (hgint M) (hgm M) c
      filter_upwards [hsum, ae_rootInformation_linear_bound d hij μ hA] with x hx hb
      obtain ⟨B, N, hN⟩ := hb
      obtain ⟨n, hn⟩ := exists_nat_gt (max (N : ℝ) (B / (c - 1)))
      have hnN : N ≤ n := by exact_mod_cast (le_max_left (N : ℝ) _).trans hn.le
      have hBn : B < (n : ℝ) * (c - 1) :=
        (div_lt_iff₀ (by linarith : 0 < c - 1)).mp ((le_max_right _ _).trans_lt hn)
      refine ⟨n, ?_⟩
      have hle : birkhoffSum T (g M) n x ≤ birkhoffSum T f n x := by
        apply Finset.sum_le_sum
        intro k _
        exact min_le_left _ _
      rw [hx n] at hle
      have hfin := (hle.trans (hN n hnN))
      nlinarith
    by_contra! h
    have hh := hbound (((∫ x, g M x ∂μ) + 1) / 2) (by linarith)
    linarith
  have hlin (M : ℕ) : (∫⁻ x, ENNReal.ofReal (g M x) ∂μ) ≤ 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hgint M) (Eventually.of_forall (hg0 M))]
    exact ENNReal.ofReal_le_one.mpr (hgmean M)
  have hlim : Tendsto (fun M : ℕ => ∫⁻ x, ENNReal.ofReal (g M x) ∂μ)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂μ)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone (fun M => (hgm M).ennreal_ofReal.aemeasurable)
    · exact Eventually.of_forall fun x a b hab => ENNReal.ofReal_le_ofReal
        (min_le_min_left (f x) (Nat.cast_le.mpr hab))
    · apply Eventually.of_forall
      intro x
      have heq : ∀ᶠ M : ℕ in atTop, g M x = f x := by
        obtain ⟨N, hN⟩ := exists_nat_gt (f x)
        filter_upwards [eventually_ge_atTop N] with M hM
        exact min_eq_left (hN.le.trans (Nat.cast_le.mpr hM))
      exact tendsto_const_nhds.congr' (heq.mono fun M hM => congrArg ENNReal.ofReal hM.symm)
  have hbound := le_of_tendsto hlim (Eventually.of_forall hlin)
  have he : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = rootInformationMean hij μ 1 :=
    lintegral_congr_ae (hfeq.mono fun x hx => congrArg ENNReal.ofReal hx)
  rwa [he] at hbound

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CanonicalRootBasic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mean root coefficients and their elementary properties

The coefficient is the mean leaf information at unit scale. Diagonal
covariance makes real-time mean information linear in time.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

lemma canonicalRootCoefficient_nonneg (i j : Fin (d + 1)) :
    0 ≤ canonicalRootCoefficient d μ i j := by
  unfold canonicalRootCoefficient
  split_ifs
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

include hA

/-- Actual real-time mean information is the root coefficient times time. -/
lemma rootInformationMean_eq_coefficient (i j : Fin (d + 1)) (hij : i ≠ j)
    {t : ℝ} (ht : 0 ≤ t) :
    rootInformationMean hij μ t =
      ENNReal.ofReal (t * canonicalRootCoefficient d μ i j) := by
  have hfin : rootInformationMean hij μ 1 ≠ ∞ :=
    ne_of_lt ((rootInformationMean_le_one d hij μ hA).trans_lt ENNReal.one_lt_top)
  rw [rootInformationMean_real d hij μ hA ht, canonicalRootCoefficient, dite_eq_right hij,
    ENNReal.ofReal_mul ht, ENNReal.ofReal_toReal hfin]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootInformationIntegral
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Signed mean information at every real time

Finite coefficients imply integrability. The actual leaf cocycle extends
the mean identity to negative times as well as positive times.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
  (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

lemma integrable_rootInformation_nonneg {t : ℝ} (ht : 0 ≤ t) :
    Integrable (rootInformation hij μ t) μ := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (aemeasurable_rootInformation d hij μ hA t).aestronglyMeasurable
    (ae_rootInformation_nonneg d hij μ hA ht)).mp
  change rootInformationMean hij μ t ≠ ∞
  rw [rootInformationMean_eq_coefficient d μ hA i j hij ht]
  exact ENNReal.ofReal_ne_top

lemma integral_rootInformation_nonneg {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, rootInformation hij μ t x ∂μ) = t * canonicalRootCoefficient d μ i j := by
  have he := ofReal_integral_eq_lintegral_ofReal
    (integrable_rootInformation_nonneg d hij μ hA ht)
    (ae_rootInformation_nonneg d hij μ hA ht)
  change ENNReal.ofReal (∫ x, rootInformation hij μ t x ∂μ) = rootInformationMean hij μ t at he
  rw [rootInformationMean_eq_coefficient d μ hA i j hij ht] at he
  have hi := integral_nonneg_of_ae (ae_rootInformation_nonneg d hij μ hA ht)
  have hh := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal hi,
    ENNReal.toReal_ofReal (mul_nonneg ht (canonicalRootCoefficient_nonneg d μ i j))] using hh

lemma ae_rootInformation_time_reversal (t : ℝ) :
    ∀ᵐ x ∂μ, rootInformation hij μ t x =
      -rootInformation hij μ (-t) (rightAction x (rootCanonicalFlow d j t)) := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [ae_rootInformation_cocycle d hij μ hA (-t) t,
    ae_intrinsicRootLeaf_spec hij μ hfree] with x hc hs
  have hz : rootInformation hij μ 0 x = 0 := by simp [rootInformation, hs.2]
  rw [neg_add_cancel, hz] at hc
  linarith

/-- Root information is integrable even for negative times. -/
theorem integrable_rootInformation (t : ℝ) : Integrable (rootInformation hij μ t) μ := by
  by_cases ht : 0 ≤ t
  · exact integrable_rootInformation_nonneg d hij μ hA ht
  have hm := integrable_rootInformation_nonneg d hij μ hA (neg_nonneg.mpr (le_of_not_ge ht))
  have hT := rootCanonicalFlow_preserving d j t μ hA
  apply (hT.integrable_comp_of_integrable hm).neg.congr
  filter_upwards [ae_rootInformation_time_reversal d hij μ hA t] with x hx
  exact hx.symm

/-- The signed integral is exactly linear at every real time. -/
theorem integral_rootInformation (t : ℝ) :
    (∫ x, rootInformation hij μ t x ∂μ) = t * canonicalRootCoefficient d μ i j := by
  by_cases ht : 0 ≤ t
  · exact integral_rootInformation_nonneg d hij μ hA ht
  have hT := rootCanonicalFlow_preserving d j t μ hA
  rw [integral_congr_ae (ae_rootInformation_time_reversal d hij μ hA t), integral_neg]
  have hmap : (∫ x, rootInformation hij μ (-t)
      (rightAction x (rootCanonicalFlow d j t)) ∂μ) =
      ∫ x, rootInformation hij μ (-t) x ∂μ := by
    have hf : AEStronglyMeasurable (rootInformation hij μ (-t))
        (μ.map (fun x => rightAction x (rootCanonicalFlow d j t))) := by
      rw [hT.map_eq]
      exact (aemeasurable_rootInformation d hij μ hA (-t)).aestronglyMeasurable
    exact (integral_map hT.measurable.aemeasurable hf).symm.trans (by rw [hT.map_eq])
  rw [hmap, integral_rootInformation_nonneg d hij μ hA (by linarith)]
  ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootProductInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Information of products of the actual root leaf measures

Rectangular information of a finite product is the sum of its root
information. Its integral is the coefficient-weighted sum of root
information integrals.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

variable {ι : Type*} [Fintype ι] (d : ℕ)
  (i j : ι → Fin (d + 1)) (hij : ∀ a, i a ≠ j a)
  (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

lemma ae_rootProductInformation_eq_sum (t : ι → ℝ) :
    ∀ᵐ x ∂μ, rootProductInformation d i j hij μ t x =
      ∑ a, rootInformation (hij a) μ (t a) x := by
  have hfree (a : ι) : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection (hij a) v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx (i a) (j a) (hij a)
  have hs := ae_all_iff.mpr (fun a => ae_intrinsicRootLeaf_spec (hij a) μ (hfree a))
  have hp := ae_all_iff.mpr (fun a => ae_intrinsicRootLeaf_ball_pos (hij a) μ (hfree a))
  filter_upwards [hs, hp] with x hx hpx
  let ν : ι → Measure ℝ := fun a => intrinsicRootLeaf (hij a) μ x
  let (a : ι) : IsLocallyFiniteMeasure (ν a) := (hx a).1
  change -Real.log ((Measure.pi ν) (Set.pi univ (fun a => ball 0 (Real.exp (-t a))))).toReal = _
  rw [Measure.pi_pi, ENNReal.toReal_prod, Real.log_prod]
  · simp only [rootInformation, Finset.sum_neg_distrib, ν]
  · intro a _
    exact (ENNReal.toReal_pos (hpx a _ (Real.exp_pos _)).ne' measure_ball_lt_top.ne).ne'

lemma integrable_rootProductInformation (t : ι → ℝ) :
    Integrable (rootProductInformation d i j hij μ t) μ := by
  have hi : Integrable (fun x => ∑ a, rootInformation (hij a) μ (t a) x) μ := by
    exact integrable_finsetSum _ fun a _ => integrable_rootInformation d (hij a) μ hA (t a)
  apply hi.congr
  filter_upwards [ae_rootProductInformation_eq_sum d i j hij μ hA t] with x hx
  exact hx.symm

/-- The product leaf information has precisely the coefficient-weighted
mean occurring in the entropy formula. -/
theorem integral_rootProductInformation (t : ι → ℝ) :
    (∫ x, rootProductInformation d i j hij μ t x ∂μ) =
      ∑ a, t a * canonicalRootCoefficient d μ (i a) (j a) := by
  rw [integral_congr_ae (ae_rootProductInformation_eq_sum d i j hij μ hA t),
    integral_finsetSum _ (fun a _ => integrable_rootInformation d (hij a) μ hA (t a))]
  exact Finset.sum_congr rfl fun a _ => integral_rootInformation d (hij a) μ hA (t a)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DiagonalRootTubes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite diagonal orbit tubes in a remaining root group

These are actual conjugation tubes, not assumed entropy partitions.
Their information is computed exactly; the passage from these tubes to
metric entropy is a separate step.
-/

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma exp_scaled_abs_lt_iff (a ρ x : ℝ) :
    |Real.exp a * x| < Real.exp (-ρ) ↔ |x| < Real.exp (-(ρ+a)) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos a), mul_comm (Real.exp a),
    ←lt_div_iff₀ (Real.exp_pos a), ←Real.exp_sub,
    show -ρ-a = -(ρ+a) by ring]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RemainingExpansionInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mean normalization in the actual remaining-root covariance -/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}

lemma remainingDilationCube_preimage (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots (d+1)) (ell : Fin (d+1) → ℝ) :
    (c.remainingEuclideanCoordinates hf).symm ⁻¹'
        ((c.rootDilation ell 1) ⁻¹' c.cube 1) =
      Set.univ.pi (fun p : ↥(allPositiveRoots (d+1) \ P) =>
        Metric.ball 0 (Real.exp (-(ell p.val.1-ell p.val.2)))) := by
  ext v
  simp only [Set.mem_preimage, c.remainingEuclideanCoordinates_cube hf,
    Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_ball, Real.dist_eq, sub_zero]
  apply forall_congr'
  intro p
  rw [c.remainingEuclideanCoordinates_dilation hf]
  simp only [Homeomorph.apply_symm_apply, mul_one]
  simpa only [neg_zero, Real.exp_zero, zero_add] using
    exp_scaled_abs_lt_iff (ell p.val.1-ell p.val.2) 0 (v p)

/-- Every expanding normalization rectangle has positive finite mass. -/
theorem ae_remainingExpansionMass_pos_ne_top (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots (d+1))
    (ell : Fin (d+1) → ℝ) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1) ∧
      c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1) ≠ ∞ := by
  let I := ↥(allPositiveRoots (d+1) \ P)
  let hij (p : I) := ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2
  have hfree (p : I) : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection (hij p) v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _
  have hs := ae_all_iff.mpr (fun p : I => ae_intrinsicRootLeaf_spec (hij p) μ (hfree p))
  have hp := ae_all_iff.mpr (fun p : I => ae_intrinsicRootLeaf_ball_pos (hij p) μ (hfree p))
  filter_upwards [hs, hp] with x hxs hxp
  let : ∀ p : I, IsLocallyFiniteMeasure (intrinsicRootLeaf (hij p) μ x) :=
    fun p => (hxs p).1
  rw [c.remainingTimeProduct_eq_map hP hf μ x,
    Measure.map_apply (c.remainingEuclideanCoordinates hf).symm.measurable
      ((c.cube_open 1).preimage (c.rootDilation ell 1).continuous).measurableSet,
    c.remainingDilationCube_preimage hf, Measure.pi_pi]
  constructor
  · exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
      (fun p _ => (hxp p _ (Real.exp_pos _)).ne'))
  · exact ENNReal.prod_ne_top (fun p _ => measure_ball_lt_top.ne)

/-- Logarithm of the covariance normalizing mass. It is integrable, and
its mean is the signed root-character sum, for arbitrary weights. -/
theorem remainingExpansionInformation_integrable_integral (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots (d+1))
    (ell : Fin (d+1) → ℝ) (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    let J := fun x => Real.log
      (c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1)).toReal
    Integrable J μ ∧ (∫ x, J x ∂μ) =
      ∑ p : ↥(allPositiveRoots (d+1) \ P),
        (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  dsimp only
  let i := fun p : ↥(allPositiveRoots (d+1) \ P) => p.val.1
  let j := fun p : ↥(allPositiveRoots (d+1) \ P) => p.val.2
  let hij := fun p : ↥(allPositiveRoots (d+1) \ P) =>
    ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2
  let t := fun p : ↥(allPositiveRoots (d+1) \ P) => ell p.val.1-ell p.val.2
  have he (x : X (d+1)) : Real.log
      (c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1)).toReal =
      -rootProductInformation d i j hij μ t x := by
    rw [c.remainingTimeProduct_eq_map hP hf μ x,
      Measure.map_apply (c.remainingEuclideanCoordinates hf).symm.measurable
        ((c.cube_open 1).preimage (c.rootDilation ell 1).continuous).measurableSet,
      c.remainingDilationCube_preimage hf]
    simp only [rootProductInformation, neg_neg]
    rfl
  simp_rw [he]
  refine ⟨(integrable_rootProductInformation d i j hij μ hA t).neg, ?_⟩
  rw [integral_neg, integral_rootProductInformation d i j hij μ hA t,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  dsimp [t, i, j]
  ring

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FiniteRealProductKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable finite products of locally finite real kernels

Only finite products of real kernels are needed for the root coordinates.
The construction uses binary kernel products and the standard finite
coordinate equivalences.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace DukePrimeDegree

private theorem exists_finRealProductKernel {A : Type*} [MeasurableSpace A] (m : ℕ) :
    ∀ (κ : Fin m → Kernel A ℝ) [∀ i, IsSFiniteKernel (κ i)]
      [∀ i x, SigmaFinite (κ i x)],
    ∃ η : Kernel A (Fin m → ℝ), IsSFiniteKernel η ∧
      ∀ x, η x = Measure.pi (fun i => κ i x) := by
  induction m with
  | zero =>
      intro κ _ _
      refine ⟨Kernel.const A (Measure.dirac 0), inferInstance, ?_⟩
      intro x
      exact (Measure.pi_of_empty (fun i => κ i x) 0).symm
  | succ m ih =>
      intro κ _ _
      obtain ⟨η, hη, heq⟩ := ih (fun i => κ ((0 : Fin (m+1)).succAbove i))
      let := hη
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0
      refine ⟨((κ 0).prod η).map e.symm, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), ?_⟩
      intro x
      rw [Kernel.map_apply _ e.symm.measurable, Kernel.prod_apply, heq]
      exact (MeasurePreserving.symm e
        (measurePreserving_piFinSuccAbove (fun i => κ i x) 0)).map_eq

/-- A finite product of s-finite real kernels with sigma-finite values
is again a kernel, with the expected product measure at every point. -/
theorem exists_realProductKernel {A I : Type*} [MeasurableSpace A] [Fintype I]
    (κ : I → Kernel A ℝ) [∀ i, IsSFiniteKernel (κ i)]
    [∀ i x, SigmaFinite (κ i x)] :
    ∃ η : Kernel A (I → ℝ), IsSFiniteKernel η ∧
      ∀ x, η x = Measure.pi (fun i => κ i x) := by
  let e := (Fintype.equivFin I).symm
  obtain ⟨η, hη, heq⟩ := exists_finRealProductKernel (Fintype.card I) (fun i => κ (e i))
  let := hη
  let E := MeasurableEquiv.piCongrLeft (fun _ : I => ℝ) e
  refine ⟨η.map E, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), ?_⟩
  intro x
  rw [Kernel.map_apply _ E.measurable, heq]
  exact Measure.pi_map_piCongrLeft e (fun i => κ i x)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingProductKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A measurable version of the actual remaining-root product

This supplies measurability of the mass of a whole future atom, rather
than imposing measurability as an additional dynamical hypothesis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

/-- The intrinsic product has an s-finite kernel version. -/
theorem exists_remainingTimeKernel (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ κ : Kernel (X (d+1)) c.Time, IsSFiniteKernel κ ∧
      ∀ᵐ x ∂μ, κ x = c.remainingTimeProduct hP hf μ x := by
  let I := ↥(allPositiveRoots (d+1) \ P)
  let hij (p : I) := ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2
  have hfree (p : I) : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection (hij p) v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _
  let κ (p : I) := intrinsicRootKernel (hij p) μ (hfree p)
  obtain ⟨η, hη, heq⟩ := exists_realProductKernel κ
  let := hη
  let E := c.remainingEuclideanCoordinates hf
  refine ⟨η.map E.symm, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), ?_⟩
  have hleaf := ae_all_iff.mpr (fun p : I => ae_intrinsicRootKernel_eq (hij p) μ (hfree p))
  filter_upwards [hleaf] with x hx
  rw [Kernel.map_apply _ E.symm.measurable, heq, c.remainingTimeProduct_eq_map hP hf μ x]
  congr 2
  funext p
  exact hx p

/-- The mass of the entire future fiber is measurable up to the ambient
null set on which intrinsic leaf measures may be chosen arbitrarily. -/
theorem aemeasurable_remainingFutureMass (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k = 0) (Q : X (d+1) → ℕ)
    (hQ : Measurable Q) (m : ℕ) :
    AEMeasurable (fun x => c.remainingTimeProduct hP hf μ x
      (c.remainingFutureAtom ell hell Q m x)) μ := by
  obtain ⟨κ, hκ, heq⟩ := c.exists_remainingTimeKernel d hP hf μ hA
  let := hκ
  have hm := Kernel.measurable_kernel_prodMk_left (κ := κ)
    (c.measurableSet_remainingFutureRelation hf ell hell Q hQ m)
  apply hm.aemeasurable.congr
  filter_upwards [heq] with x hx
  rw [hx]
  rfl

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RemainingFutureInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mean information of the actual whole-future root atom -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

/-- Positive finite whole-future mass converts exact leaf covariance into
an integrable information function with the canonical root mean. -/
theorem remainingFutureInformation_integrable_integral (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k = 0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1) :
    let I := fun x => -Real.log
      (c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) /
        c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 1 x)).toReal
    Integrable I μ ∧ (∫ x, I x ∂μ) =
      ∑ p : ↥(allPositiveRoots (d+1) \ P),
        (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  let T : X (d+1) → X (d+1) :=
    fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let M (k : ℕ) (x : X (d+1)) :=
    c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q k x)
  let C (x : X (d+1)) :=
    c.remainingTimeProduct hP hf μ x ((c.rootDilation ell 1) ⁻¹' c.cube 1)
  let J (x : X (d+1)) := Real.log (C x).toReal
  let f (x : X (d+1)) := -Real.log (M 0 x).toReal
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    dsimp [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hM : AEMeasurable (M 0) μ :=
    c.aemeasurable_remainingFutureMass d hP hf μ hA ell hell Q hQ 0
  have hfmeas : AEStronglyMeasurable f μ :=
    hM.ennreal_toReal.log.neg.aestronglyMeasurable
  have hJ := c.remainingExpansionInformation_integrable_integral hP hf ell μ hA
  have hcov := c.ae_remainingTimeProduct_futureAtom d hP hf μ hA ell hell Q hQ
  have hC := c.ae_remainingExpansionMass_pos_ne_top hP hf ell μ hA
  have hboth : ∀ᵐ x ∂μ, M 0 x ≠ 0 ∧ M 0 x ≠ ∞ ∧
      M 1 x ≠ 0 ∧ M 1 x ≠ ∞ ∧ C x ≠ 0 ∧ C x ≠ ∞ ∧
      M 0 (T x) = (C x)⁻¹ * M 1 x := by
    filter_upwards [hmass, hT.quasiMeasurePreserving.ae hmass, hcov, hC]
      with x hx hTx hcx hc
    have hmono : M 0 x ≤ M 1 x :=
      measure_mono (c.remainingFutureAtom_zero_subset_one ell hell Q x)
    have hfactor : M 1 x = C x * M 0 (T x) := by
      change M 0 (T x) = (C x)⁻¹ * M 1 x at hcx
      rw [hcx, ← mul_assoc, ENNReal.mul_inv_cancel hc.1.ne' hc.2, one_mul]
    refine ⟨hx.1.ne', ne_of_lt (hx.2.trans_lt ENNReal.one_lt_top),
      (hx.1.trans_le hmono).ne', ?_, hc.1.ne', hc.2, hcx⟩
    rw [hfactor]
    exact ENNReal.mul_ne_top hc.2 (ne_of_lt (hTx.2.trans_lt ENNReal.one_lt_top))
  have hI : ∀ᵐ x ∂μ, 0 ≤ -Real.log (M 0 x / M 1 x).toReal := by
    filter_upwards [hboth] with x hx
    rw [ENNReal.toReal_div]
    apply neg_nonneg.mpr
    apply Real.log_nonpos (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    apply (div_le_one (ENNReal.toReal_pos hx.2.2.1 hx.2.2.2.1)).mpr
    exact ENNReal.toReal_mono hx.2.2.2.1
      (measure_mono (c.remainingFutureAtom_zero_subset_one ell hell Q x))
  have heq : (fun x => -Real.log (M 0 x / M 1 x).toReal) =ᵐ[μ]
      fun x => J x + (f x-f (T x)) := by
    filter_upwards [hboth] with x hx
    have he := normalized_mass_log_identity hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
      hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2
    simpa only [sub_eq_add_neg, add_assoc] using he
  have H := information_integrable_integral_of_ae_coboundary μ hT hfmeas hJ.1 hI heq
  exact ⟨H.1, H.2.trans hJ.2⟩

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NormalizedRestrictionLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy limits for decreasing positive-mass conditioning cells -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_restriction_real {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (A B : Set Y) (hB : MeasurableSet B) :
    ((anchorNormalize ν A).restrict A).real B = ν.real (B ∩ A) / ν.real A := by
  rw [measureReal_def,Measure.restrict_apply hB,anchorNormalize,Measure.smul_apply]
  simp only [smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,measureReal_def,
    div_eq_mul_inv,mul_comm]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_StationaryRestrictions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gluing stationary restrictions over a countable cover

For a Markov kernel, stationary restrictions of one finite measure are
closed under intersections and unions. Thus local stationarity on a
countable almost-everywhere cover implies global stationarity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

theorem bind_kernel_real (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) (A : Set Y) (hA : MeasurableSet A) :
    (μ.bind κ).real A = ∫ y, (κ y).real A ∂μ := by
  rw [Measure.real, Measure.bind_apply hA κ.measurable.aemeasurable]
  exact (integral_toReal (κ.measurable_coe hA).aemeasurable
    (Filter.Eventually.of_forall fun y => measure_lt_top (κ y) A)).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_SelfConditionalKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional distributions from a stationary fiber kernel

A stationary kernel which is constant almost everywhere on each of its
own probability fibers is the conditional distribution for the sigma
algebra generated by that kernel. This is the precise extra condition
needed beyond stationarity in the whole-future application.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y : Type*} [mY : MeasurableSpace Y]

theorem setIntegral_selfConstant_kernel
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (hstat : μ.bind κ = μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y = κ x)
    {S : Set Y} (hS : MeasurableSet[MeasurableSpace.comap κ inferInstance] S)
    {A : Set Y} (hA : MeasurableSet A) :
    (∫ x in S, (κ x).real A ∂μ) = μ.real (A ∩ S) := by
  have hSm : MeasurableSet S := κ.measurable.comap_le S hS
  obtain ⟨B,hB,rfl⟩ := hS
  have he : ∀ᵐ x ∂μ,
      (κ x).real (A ∩ (κ ⁻¹' B)) =
        (κ ⁻¹' B).indicator (fun x => (κ x).real A) x := by
    filter_upwards [hself] with x hx
    by_cases hb : κ x ∈ B
    · rw [Set.indicator_of_mem (show x ∈ κ ⁻¹' B from hb)]
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [hx] with y hy
      show (_ ∈ (_ : Set _)) = (_ ∈ (_ : Set _))
      simp only [Set.mem_setOf_eq,mem_inter_iff,mem_preimage,hy,hb,and_true]
    · rw [Set.indicator_of_notMem (show x ∉ κ ⁻¹' B from hb)]
      have hz : (κ x) (A ∩ (κ ⁻¹' B)) = 0 := by
        rw [←measure_empty (μ := κ x)]
        apply measure_congr
        filter_upwards [hx] with y hy
        show (y ∈ (A ∩ κ ⁻¹' B : Set Y)) = (y ∈ (∅ : Set Y))
        simp only [Set.mem_setOf_eq,mem_inter_iff,mem_preimage,hy,hb,and_false,mem_empty_iff_false]
      rw [Measure.real,hz,ENNReal.toReal_zero]
  calc
    _ = ∫ x, (κ ⁻¹' B).indicator (fun x => (κ x).real A) x ∂μ :=
      (integral_indicator hSm).symm
    _ = ∫ x, (κ x).real (A ∩ (κ ⁻¹' B)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      exact hx.symm
    _ = (μ.bind κ).real (A ∩ (κ ⁻¹' B)) :=
      (bind_kernel_real κ μ _ (hA.inter hSm)).symm
    _ = _ := by rw [hstat]

/-- The kernel evaluations are actual conditional probabilities. -/
theorem selfConstant_kernel_ae_eq_condExp
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (hstat : μ.bind κ = μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y = κ x)
    {A : Set Y} (hA : MeasurableSet A) :
    (fun x => (κ x).real A) =ᵐ[μ]
      μ[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap κ inferInstance] := by
  have hm : MeasurableSpace.comap (fun x => κ x)
      (inferInstance : MeasurableSpace (Measure Y)) ≤ mY := κ.measurable.comap_le
  apply ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) hm
    ((integrable_const (μ := μ) (1 : ℝ)).indicator hA)
  · exact fun _ _ _ => (integrable_kernel_real μ κ hA).integrableOn
  · intro S hS _
    rw [setIntegral_selfConstant_kernel μ κ hstat hself hS hA,
      integral_indicator_const (1 : ℝ) hA]
    simp only [smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply hA]
  · have h : @Measurable Y ℝ (MeasurableSpace.comap κ inferInstance)
        inferInstance (fun x => (κ x).real A) :=
      (Measure.measurable_coe hA).ennreal_toReal.comp (comap_measurable κ)
    exact h.stronglyMeasurable.aestronglyMeasurable

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WholeFutureConditionalInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual conditional information of the whole-future root kernel -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem selfConstant_kernel_conditionalInformation
    {Y α : Type*} [MeasurableSpace Y] [Countable α]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) :
    conditionalInformation μ P (MeasurableSpace.comap κ inferInstance) =ᵐ[μ]
      fun x => -Real.log ((κ x).real {y | P y=P x}) := by
  filter_upwards [ae_all_iff.mpr (fun a =>
    selfConstant_kernel_ae_eq_condExp μ κ hstat hself (hP a))] with x hx
  exact congrArg (-Real.log ·) (hx (P x)).symm

namespace EliminationChain

lemma remainingFutureAtom_present_inter_one
    {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (x : X n) :
    {u | Q (rightAction x (c.word u))=Q x} ∩ c.remainingFutureAtom ell hell Q 1 x =
      c.remainingFutureAtom ell hell Q 0 x := by
  ext u
  constructor
  · rintro ⟨hzero,hpos⟩ k
    cases k with
    | zero => simpa only [Set.mem_ofPred_eq,Nat.zero_add,Function.iterate_zero,Function.id_def] using hzero
    | succ k => simpa only [Nat.add_zero,Nat.succ_eq_add_one] using hpos k
  · intro h
    refine ⟨?_,c.remainingFutureAtom_zero_subset_one ell hell Q x h⟩
    simpa only [Set.mem_ofPred_eq,Nat.zero_add,Function.iterate_zero,Function.id_def] using h 0

theorem wholeFuture_conditionalInformation
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hversion : ∀ᵐ x ∂μ, κ x=
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))) :
    conditionalInformation μ Q (MeasurableSpace.comap κ inferInstance) =ᵐ[μ]
      fun x => -Real.log
        (c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) /
          c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 1 x)).toReal := by
  have H := selfConstant_kernel_conditionalInformation μ κ hstat hself Q
    (fun a => hQ (measurableSet_singleton a))
  filter_upwards [H,hversion] with x hx hv
  rw [hx,hv]
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry (d+1)).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  have hA : MeasurableSet {y : X (d+1) | Q y=Q x} := hQ (measurableSet_singleton _)
  apply congrArg (-Real.log ·)
  rw [Measure.real,Measure.map_apply hF hA]
  change ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
      (c.remainingFutureAtom ell hell Q 1 x)).restrict
      (c.remainingFutureAtom ell hell Q 1 x)).real
      {u | Q (rightAction x (c.word u))=Q x} = _
  rw [normalized_restriction_real _ _ {u | Q (rightAction x (c.word u))=Q x} (hA.preimage hF),
    c.remainingFutureAtom_present_inter_one ell hell Q x,ENNReal.toReal_div]
  rfl

theorem wholeFuture_conditionalInformation_integrable_integral_oai
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hversion : ∀ᵐ x ∂μ, κ x=
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u)))
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1) :
    Integrable (conditionalInformation μ Q (MeasurableSpace.comap κ inferInstance)) μ ∧
      (∫ x, conditionalInformation μ Q (MeasurableSpace.comap κ inferInstance) x ∂μ) =
        ∑ p : ↥(allPositiveRoots (d+1) \ P),
          (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  have he := c.wholeFuture_conditionalInformation d hP hf μ ell hell Q hQ κ hstat hself hversion
  have H := c.remainingFutureInformation_integrable_integral d hP hf μ hA ell hell Q hQ hmass
  exact ⟨H.1.congr he.symm,(integral_congr_ae he).trans H.2⟩

end EliminationChain
end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.EliminationChain.wholeFuture_conditionalInformation_integrable_integral_oai := @OAI.DukePrimeDegree.EliminationChain.wholeFuture_conditionalInformation_integrable_integral_oai
