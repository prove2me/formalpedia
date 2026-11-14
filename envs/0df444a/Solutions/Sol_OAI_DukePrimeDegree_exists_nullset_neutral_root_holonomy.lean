-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_nullset_neutral_root_holonomy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:54.096472+00:00
-- url     : https://prove2.me/submissions/d6e58479-e83c-4296-8d95-1f2e51827ace

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
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
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
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

section
-- module Solutions.OAIQ244_DUKE.Compat
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


namespace PrimeDegreePackets

lemma centerRealMeasure_center (ν : Measure ℝ) (t u : ℝ) :
    centerRealMeasure (centerRealMeasure ν t) u = centerRealMeasure ν (t+u) := by
  unfold centerRealMeasure
  rw [Measure.map_map (Homeomorph.subRight u).measurable (Homeomorph.subRight t).measurable]
  congr 1
  funext x
  change (x-t)-u=x-(t+u)
  ring

lemma basedRealMeasure_center (ν : Measure ℝ) (t u : ℝ) :
    basedRealMeasure (centerRealMeasure ν t) u = basedRealMeasure ν (t+u) := by
  unfold basedRealMeasure
  rw [centerRealMeasure_center]

 

lemma basedRealMeasure_rebase (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (t u : ℝ) (ht : 0 < ν (Metric.ball t 1)) :
    basedRealMeasure (basedRealMeasure ν t) u = basedRealMeasure ν (t+u) := by
  change basedRealMeasure ((centerRealMeasure ν t (Metric.ball 0 1))⁻¹ • centerRealMeasure ν t) u = _
  rw [basedRealMeasure_smul]
  · exact basedRealMeasure_center ν t u
  · rw [centerRealMeasure_ball]
    exact ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne
  · rw [centerRealMeasure_ball]
    exact ENNReal.inv_ne_top.mpr ht.ne'

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafLusin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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

lemma continuousOn_of_finer_compact {Y Z : Type*}
    {t t' : TopologicalSpace Y} {tZ : TopologicalSpace Z} [@T2Space Y t]
    (hle : t' ≤ t) {K : Set Y} (hK : @IsCompact Y t' K)
    {f : Y → Z} (hf : @Continuous Y Z t' tZ f) :
    @ContinuousOn Y Z t tZ f K := by
  let : TopologicalSpace Y := t
  apply continuousOn_iff_isClosed.mpr
  intro C hC
  have hc : @IsCompact Y t' (f ⁻¹' C ∩ K) := by
    let : TopologicalSpace Y := t'
    exact hK.inter_left (hC.preimage hf)
  have hid : @Continuous Y Y t' t id := continuous_id_of_le hle
  have hcold : @IsCompact Y t (f ⁻¹' C ∩ K) := by
    simpa only [image_id] using @IsCompact.image Y Y t' t _ id hc hid
  exact ⟨f ⁻¹' C ∩ K, hcold.isClosed, by simp only [inter_assoc, inter_self]⟩

/-- A compact Lusin set avoiding a prescribed measurable null set. -/
theorem exists_compact_continuousOn_outside_null
    {Y Z : Type*} [tY : TopologicalSpace Y] [PolishSpace Y]
    [mY : MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (f : Y → Z) (hf : Measurable f)
    (N : Set Y) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ K : Set Y, IsCompact K ∧ K ⊆ Nᶜ ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  have hB : mY = @borel Y tY := BorelSpace.measurable_eq
  obtain ⟨t', hle, hf', hp⟩ := hf.exists_continuous
  have hBt : mY = @borel Y t' :=
    hB.trans (borel_eq_borel_of_le hp (inferInstance : @PolishSpace Y tY) hle).symm
  let : TopologicalSpace Y := t'
  let : PolishSpace Y := hp
  let : BorelSpace Y := ⟨hBt⟩
  obtain ⟨K, hKN, hK, hsmall⟩ := hN.compl.exists_isCompact_sdiff_lt
    (measure_ne_top μ Nᶜ) hε
  have hsmall' : μ Kᶜ < ε := by
    have heq : Nᶜ \ K = Kᶜ \ N := by ext x; simp only [Set.mem_sdiff, mem_compl_iff, and_comm]
    rwa [heq, measure_sdiff_null hNzero] at hsmall
  refine ⟨K, ?_, hKN, hsmall', continuousOn_of_finer_compact hle hK hf'⟩
  simpa only [image_id] using @IsCompact.image Y Y t' tY K id hK (continuous_id_of_le hle)

/-- The compact-set version only needs a metrizable source and inner
regularity; the source need not be equipped with a complete metric. -/
theorem exists_compact_continuousOn_metrizable
    {Y Z : Type*} [TopologicalSpace Y] [MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Y) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]
    (f : Y → Z) (hf : Measurable f)
    (N : Set Y) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ K : Set Y, IsCompact K ∧ K ⊆ Nᶜ ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  obtain ⟨δ, hδ, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε (Fin 2)
  have hsum : δ 0 + δ 1 < ε := by simpa only [tsum_fintype, Fin.sum_univ_two] using hδsum
  obtain ⟨C, hCN, hC, hCsmall⟩ := hN.compl.exists_isCompact_sdiff_lt
    (measure_ne_top μ Nᶜ) (hδ 0).ne'
  have hCsmall' : μ Cᶜ < δ 0 := by
    have heq : Nᶜ \ C = Cᶜ \ N := by ext x; simp only [Set.mem_sdiff, mem_compl_iff, and_comm]
    rwa [heq, measure_sdiff_null hNzero] at hCsmall
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : MetricSpace C := TopologicalSpace.metrizableSpaceMetric C
  let : PolishSpace C := inferInstance
  let ν : Measure C := μ.comap Subtype.val
  have he : MeasurableEmbedding (Subtype.val : C → Y) :=
    (hC.isClosed.isClosedEmbedding_subtypeVal).measurableEmbedding
  let : IsFiniteMeasure ν := ⟨by
    change μ.comap Subtype.val univ < ∞
    rw [he.comap_apply]
    exact measure_lt_top μ _⟩
  obtain ⟨L, hL, _, hLsmall, hLcont⟩ := exists_compact_continuousOn_outside_null
    ν (f ∘ Subtype.val) (hf.comp measurable_subtype_coe) ∅ MeasurableSet.empty
    (by simp) (δ 1) (hδ 1).ne'
  let K : Set Y := Subtype.val '' L
  have hK : IsCompact K := hL.image continuous_subtype_val
  have hKsmall : μ (C \ K) < δ 1 := by
    have heq : Subtype.val '' Lᶜ = C \ K := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, fun ⟨z, hz, hez⟩ => hy (Subtype.ext hez ▸ hz)⟩
      · rintro ⟨hxC, hxK⟩
        exact ⟨⟨x, hxC⟩, fun h => hxK ⟨⟨x, hxC⟩, h, rfl⟩, rfl⟩
    change μ.comap Subtype.val Lᶜ < δ 1 at hLsmall
    rw [he.comap_apply, heq] at hLsmall
    exact hLsmall
  refine ⟨K, hK, ?_, ?_, ?_⟩
  · rintro x ⟨y, _, rfl⟩
    exact hCN y.property
  · have hsub : Kᶜ ⊆ Cᶜ ∪ (C \ K) := by intro x hx; by_cases h : x ∈ C <;> tauto
    exact (((measure_mono hsub).trans (measure_union_le _ _)).trans
      (add_le_add hCsmall'.le hKsmall.le)).trans_lt hsum
  · exact Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_image_iff.mpr hLcont

lemma measurable_intrinsicLeafData {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    Measurable (intrinsicLeafData hij μ hfree) := by
  apply Measurable.of_eval
  intro q
  exact (leafTest q.1 q.2).continuous.stronglyMeasurable.integral_kernel.measurable

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DiscreteMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform discrete orbit averages

The finite Hopf inequality bounds the union over all averaging lengths.
The resulting measurable good set controls every positive integer time,
as needed before passing to the continuous diagonal flow.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

theorem positiveRunningSum_measure_bound
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {g : Y → ℝ} (hg : Integrable g μ) (hgmeas : Measurable g)
    (hgnonneg : ∀ x, 0 ≤ g x) (c : ℝ) (hc : 0 < c) :
    μ (⋃ n : ℕ, {x | 0 < positiveRunningSum T (fun y => g y - c) n x}) ≤
      ENNReal.ofReal ((∫ x, g x ∂μ) / c) := by
  let f : Y → ℝ := fun x => g x - c
  let E : ℕ → Set Y := fun n => {x | 0 < positiveRunningSum T f n x}
  have hf : Integrable f μ := hg.sub (integrable_const c)
  have hfmeas : Measurable f := hgmeas.sub measurable_const
  have hEmeas (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfmeas n)
  have hEmono : Monotone E := by
    intro a b hab x hx
    exact hx.trans_le (positiveRunningSum_mono T f x hab)
  have hbound (n : ℕ) : μ (E n) ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / c) := by
    have hhopf := finite_hopf_maximal hT hf hfmeas n
    change 0 ≤ ∫ x in E n, g x - c ∂μ at hhopf
    rw [integral_sub hg.restrict (integrable_const c), setIntegral_const, smul_eq_mul] at hhopf
    have hsub : ∫ x in E n, g x ∂μ ≤ ∫ x, g x ∂μ :=
      setIntegral_le_integral hg (Eventually.of_forall hgnonneg)
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _)
      (div_nonneg (integral_nonneg hgnonneg) hc.le)).mpr
    apply (le_div_iff₀ hc).mpr
    change μ.real (E n) * c ≤ _
    linarith
  rw [hEmono.measure_iUnion]
  exact iSup_le hbound

/-- The complement of one measurable exceptional set controls all finite
averages, with the sharp Hopf bound on its measure. -/
theorem exists_discrete_average_good_set
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {g : Y → ℝ} (hg : Integrable g μ) (hgmeas : Measurable g)
    (hgnonneg : ∀ x, 0 ≤ g x) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set Y, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / c) ∧
      ∀ x ∈ G, ∀ n : ℕ, birkhoffSum T g n x ≤ c * n := by
  let f : Y → ℝ := fun x => g x - c
  let B := ⋃ n : ℕ, {x | 0 < positiveRunningSum T f n x}
  have hfmeas : Measurable f := hgmeas.sub measurable_const
  have hB : MeasurableSet B := MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfmeas n)
  refine ⟨Bᶜ, hB.compl, ?_, ?_⟩
  · simpa only [compl_compl] using positiveRunningSum_measure_bound μ hT hg hgmeas hgnonneg c hc
  · intro x hx n
    have hnot : ¬ 0 < positiveRunningSum T f n x := by
      intro h
      exact hx (mem_iUnion.mpr ⟨n, h⟩)
    have hs := (birkhoffSum_le_positiveRunningSum T f n x).trans (le_of_not_gt hnot)
    have heq : birkhoffSum T f n x = birkhoffSum T g n x - (n : ℝ) * c := by
      change (∑ k ∈ Finset.range n, (g (T^[k] x) - c)) = _
      rw [Finset.sum_sub_distrib]
      simp [birkhoffSum]
    rw [heq] at hs
    linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FlowOccupation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One-unit occupation observables

For a measurable measure-preserving flow, the time spent in a measurable
set during one unit interval is a measurable integrable observable. Its
space integral is exactly the measure of that set. Its discrete sums
are the occupation integrals on the corresponding integer intervals.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

lemma integrable_one_indicator_comp
    {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] {F : Z → Y} (hF : Measurable F)
    {E : Set Y} (hE : MeasurableSet E) :
    Integrable (fun z => E.indicator (fun _ => (1 : ℝ)) (F z)) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_const.indicator hE).comp hF).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : F z ∈ E <;> simp [hz]

lemma measurable_unitFlowOccupation
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) : Measurable (unitFlowOccupation Φ E) := by
  have hχ : Measurable (fun p : Y × ℝ =>
      E.indicator (fun _ => (1 : ℝ)) (Φ p.2 p.1)) :=
    (measurable_const.indicator hE).comp hΦ
  exact hχ.stronglyMeasurable.integral_prod_right'.measurable

lemma unitFlowOccupation_nonneg
    {Y : Type*} (Φ : ℝ → Y → Y) (E : Set Y) (x : Y) :
    0 ≤ unitFlowOccupation Φ E x := by
  apply integral_nonneg
  intro t
  exact indicator_nonneg (fun _ _ => zero_le_one) (Φ t x)

lemma unitFlowOccupation_le_one
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) (x : Y) : unitFlowOccupation Φ E x ≤ 1 := by
  have hF : Measurable (fun t => Φ t x) := hΦ.comp (measurable_const.prodMk measurable_id)
  have hi := integrable_one_indicator_comp (volume.restrict (Ioc (0 : ℝ) 1)) hF hE
  have h := integral_mono hi (integrable_const (1 : ℝ))
    (fun t => show E.indicator (fun _ => (1 : ℝ)) (Φ t x) ≤ 1 from by
      by_cases ht : Φ t x ∈ E <;> simp [ht])
  simpa [unitFlowOccupation, measureReal_def] using h

lemma integrable_unitFlowOccupation
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) : Integrable (unitFlowOccupation Φ E) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_unitFlowOccupation hΦ hE).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (unitFlowOccupation_nonneg Φ E x)]
    exact unitFlowOccupation_le_one hΦ hE x

theorem integral_unitFlowOccupation
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    {E : Set Y} (hE : MeasurableSet E) :
    ∫ x, unitFlowOccupation Φ E x ∂μ = μ.real E := by
  have hi := integrable_one_indicator_comp
    (μ.prod (volume.restrict (Ioc (0 : ℝ) 1))) hΦ hE
  change (∫ x, (∫ t in Ioc (0 : ℝ) 1,
    E.indicator (fun _ => (1 : ℝ)) (Φ t x)) ∂μ) = _
  rw [integral_integral_swap hi]
  have heq (t : ℝ) : (∫ x, E.indicator (fun _ => (1 : ℝ)) (Φ t x) ∂μ) = μ.real E := by
    have hm : AEStronglyMeasurable (E.indicator (fun _ => (1 : ℝ))) (μ.map (Φ t)) := by
      rw [(hpres t).map_eq]
      exact (measurable_const.indicator hE).aestronglyMeasurable
    rw [← integral_map (hpres t).measurable.aemeasurable hm, (hpres t).map_eq,
      integral_indicator_const (1 : ℝ) hE]
    simp
  simp_rw [heq]
  simp [measureReal_def]

lemma intervalIntegrable_flow_indicator
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) (x : Y) (a b : ℝ) :
    IntervalIntegrable (fun t => E.indicator (fun _ => (1 : ℝ)) (Φ t x)) volume a b := by
  let : IsFiniteMeasure (volume.restrict (uIcc a b)) :=
    isFiniteMeasure_restrict.mpr (isCompact_uIcc.measure_lt_top.ne)
  apply (intervalIntegrable_iff').mpr
  exact integrable_one_indicator_comp (volume.restrict (uIcc a b))
    (hΦ.comp (measurable_const.prodMk measurable_id)) hE

lemma flow_nat_iterate {Y : Type*} {Φ : ℝ → Y → Y}
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (n : ℕ) (x : Y) : (Φ 1)^[n] x = Φ n x := by
  induction n generalizing x with
  | zero => simpa using (hzero x).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Nat.cast_add, Nat.cast_one,
      add_comm (n : ℝ) 1, hadd]

theorem birkhoffSum_unitFlowOccupation
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    {E : Set Y} (hE : MeasurableSet E) (n : ℕ) (x : Y) :
    birkhoffSum (Φ 1) (unitFlowOccupation Φ E) n x =
      ∫ t in (0 : ℝ)..(n : ℝ), E.indicator (fun _ => (1 : ℝ)) (Φ t x) := by
  have hterm (k : ℕ) : unitFlowOccupation Φ E ((Φ 1)^[k] x) =
      ∫ t in (k : ℝ)..(k + 1 : ℕ), E.indicator (fun _ => (1 : ℝ)) (Φ t x) := by
    rw [flow_nat_iterate hzero hadd]
    change (∫ t in Ioc (0 : ℝ) 1, E.indicator (fun _ => (1 : ℝ)) (Φ t (Φ k x))) = _
    simp_rw [← hadd]
    rw [← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    have hs := intervalIntegral.integral_comp_add_right
      (fun t => E.indicator (fun _ => (1 : ℝ)) (Φ t x)) (a := 0) (b := 1) (k : ℝ)
    simpa [Nat.cast_add, Nat.cast_one, add_comm] using hs
  simp_rw [birkhoffSum, hterm]
  simpa only [Nat.cast_zero] using
    intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ))
      (fun k _ => by
        simpa only [Nat.cast_add, Nat.cast_one] using
          intervalIntegrable_flow_indicator hΦ hE x k (k + 1))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FlowMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Maximal occupation control for long flow intervals

The discrete Hopf inequality, applied to one-unit occupation, controls
every real interval of length at least one. This is sufficient for the
large logarithmic time windows in EKL (2006), Lemmas 4.5 and 4.6.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

theorem exists_flow_average_good_set
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    {E : Set Y} (hE : MeasurableSet E) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal (2 * μ.real E / c) ∧
      ∀ x ∈ G, ∀ T : ℝ, 1 ≤ T →
        (∫ t in (0 : ℝ)..T, E.indicator (fun _ => (1 : ℝ)) (Φ t x)) ≤ c * T := by
  obtain ⟨G, hG, hmass, hgood⟩ := exists_discrete_average_good_set μ (hpres 1)
    (integrable_unitFlowOccupation μ hΦ hE) (measurable_unitFlowOccupation hΦ hE)
    (unitFlowOccupation_nonneg Φ E) (c / 2) (by linarith)
  refine ⟨G, hG, ?_, ?_⟩
  · rw [integral_unitFlowOccupation μ hΦ hpres hE] at hmass
    convert hmass using 2
    all_goals try with_reducible_and_instances rfl
    ring
  · intro x hx T hT
    let n := Nat.ceil T
    have hTn : T ≤ (n : ℝ) := Nat.le_ceil T
    have hn : (n : ℝ) ≤ 2 * T := by
      have hnlt : (n : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
      linarith
    have hmono := intervalIntegral.integral_mono_interval
      (f := fun t => E.indicator (fun _ => (1 : ℝ)) (Φ t x))
      (le_refl (0 : ℝ)) (by linarith : (0 : ℝ) ≤ T) hTn
      (Eventually.of_forall fun t => indicator_nonneg (fun _ _ => zero_le_one) (Φ t x))
      (intervalIntegrable_flow_indicator hΦ hE x 0 n)
    rw [← birkhoffSum_unitFlowOccupation hΦ hzero hadd hE n x] at hmono
    have hdiscrete := hgood x hx n
    have hfinal : c / 2 * (n : ℝ) ≤ c * T := by nlinarith
    exact hmono.trans (hdiscrete.trans hfinal)

lemma flow_occupation_eq_time_measure
    {Y : Type*} [MeasurableSpace Y] {Φ : ℝ → Y → Y}
    (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    {E : Set Y} (hE : MeasurableSet E) (x : Y) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, E.indicator (fun _ => (1 : ℝ)) (Φ t x)) =
      volume.real (Ioc 0 T ∩ {t | Φ t x ∈ E}) := by
  let S := {t | Φ t x ∈ E}
  have hS : MeasurableSet S := hE.preimage (hΦ.comp (measurable_const.prodMk measurable_id))
  have heq : (fun t => E.indicator (fun _ => (1 : ℝ)) (Φ t x)) =
      S.indicator (fun _ => (1 : ℝ)) := by
    funext t
    by_cases ht : Φ t x ∈ E <;> simp [S, ht]
  rw [intervalIntegral.integral_of_le hT, heq, integral_indicator_const (1 : ℝ) hS,
    measureReal_restrict_apply hS, inter_comm]
  simp only [smul_eq_mul, mul_one]
  rfl

/-- Every long interval has a uniformly small fraction of bad visits
outside one set with the explicit maximal-inequality bound. -/
theorem exists_flow_return_good_set
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    {E : Set Y} (hE : MeasurableSet E) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal (2 * μ.real E / c) ∧
      ∀ x ∈ G, ∀ T : ℝ, 1 ≤ T →
        volume.real (Ioc 0 T ∩ {t | Φ t x ∈ E}) ≤ c * T := by
  obtain ⟨G, hG, hmass, hgood⟩ :=
    exists_flow_average_good_set μ hΦ hzero hadd hpres hE c hc
  refine ⟨G, hG, hmass, ?_⟩
  intro x hx T hT
  rw [← flow_occupation_eq_time_measure hΦ hE x T (by linarith)]
  exact hgood x hx T hT

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CompactFlowReturns
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact simultaneous returns outside a prescribed null set

A summable sequence of maximal-inequality exceptional sets gives one
conull set on which any two points return to a common compact set with
uniformly positive overlap. No ergodicity of the individual flow is used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree

theorem exists_eventual_flow_good_sets
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    (K : ℕ → Set Y) (hK : ∀ m, MeasurableSet (K m))
    (hsmall : ∀ m, μ (K m)ᶜ < ENNReal.ofReal (((1 / 2 : ℝ) ^ m) / 8)) :
    ∃ G : ℕ → Set Y, (∀ m, MeasurableSet (G m)) ∧
      (∀ᵐ x ∂μ, ∀ᶠ m in atTop, x ∈ G m) ∧
      ∀ m x, x ∈ G m → ∀ T : ℝ, 1 ≤ T →
        volume.real (Ioc 0 T ∩ {t | Φ t x ∉ K m}) ≤ T / 4 := by
  have hG (m : ℕ) := exists_flow_return_good_set μ hΦ hzero hadd hpres
    (hK m).compl (1 / 4) (by norm_num)
  choose G hGmeas hGmass hgood using hG
  have hmass (m : ℕ) : μ (G m)ᶜ ≤ (2⁻¹ : ℝ≥0∞) ^ m := by
    have hr : μ.real (K m)ᶜ ≤ ((1 / 2 : ℝ) ^ m) / 8 := by
      have h := (ENNReal.toReal_le_toReal (measure_ne_top μ _)
        ENNReal.ofReal_ne_top).mpr (hsmall m).le
      rw [ENNReal.toReal_ofReal (by positivity)] at h
      exact h
    calc
      μ (G m)ᶜ ≤ ENNReal.ofReal (2 * μ.real (K m)ᶜ / (1 / 4)) := hGmass m
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = (2⁻¹ : ℝ≥0∞) ^ m := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        congr 1
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
  have hs : (∑' m, μ (G m)ᶜ) ≠ ∞ := by
    apply ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    calc
      (∑' m, μ (G m)ᶜ) ≤ ∑' m, (2⁻¹ : ℝ≥0∞) ^ m := ENNReal.tsum_le_tsum hmass
      _ = 2 := ENNReal.tsum_geometric_two
  refine ⟨G, hGmeas, ?_, ?_⟩
  · simpa only [notMem_compl_iff] using (ae_eventually_notMem hs)
  · intro m x hx T hT
    simpa only [mem_compl_iff, one_div, div_eq_mul_inv, one_mul, mul_comm] using hgood m x hx T hT

theorem exists_late_simultaneous_compact_return
    {Y : Type*} (Φ : ℝ → Y → Y) (K : Set Y) (x y : Y)
    (hx : ∀ T : ℝ, 1 ≤ T →
      volume.real (Ioc 0 T ∩ {t | Φ t x ∉ K}) ≤ T / 4)
    (hy : ∀ T : ℝ, 1 ≤ T →
      volume.real (Ioc 0 T ∩ {t | Φ t y ∉ K}) ≤ T / 4)
    (R : ℝ) : ∃ t : ℝ, R < t ∧ Φ t x ∈ K ∧ Φ t y ∈ K := by
  let T : ℝ := 4 * (max R 1 + 1)
  have hT : 1 ≤ T := by dsimp [T] <;> linarith [le_max_right R 1]
  have hTpos : 0 < T := by linarith
  let A : Set ℝ := Ioc 0 T ∩ {t | Φ t x ∉ K}
  let B : Set ℝ := Ioc 0 T ∩ {t | Φ t y ∉ K}
  by_contra h
  have hcover : Ioc (T / 4) T ⊆ A ∪ B := by
    intro t ht
    have ht0 : t ∈ Ioc 0 T := ⟨by linarith [ht.1], ht.2⟩
    by_cases htx : Φ t x ∈ K
    · apply Or.inr
      refine ⟨ht0, ?_⟩
      intro hty
      apply h ⟨t, ?_, htx, hty⟩
      dsimp [T] at ht
      linarith [ht.1, le_max_left R 1]
    · exact Or.inl ⟨ht0, htx⟩
  have hsub : A ∪ B ⊆ Ioc 0 T := union_subset inter_subset_left inter_subset_left
  have hfinite : volume (A ∪ B) ≠ ∞ :=
    measure_ne_top_of_subset hsub (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hle := measureReal_mono hcover hfinite
  have hu := measureReal_union_le (μ := volume) A B
  have hAx : volume.real A ≤ T / 4 := hx T hT
  have hBy : volume.real B ≤ T / 4 := hy T hT
  rw [Real.volume_real_Ioc_of_le (by linarith : T / 4 ≤ T)] at hle
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_DiagonalFlowMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform long-time returns for the diagonal flow

This specializes the proved maximal occupation bound to the actual
canonical diagonal flow on the arithmetic quotient.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma continuous_diagonalOneParameter {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) : Continuous (diagonalOneParameter ell hell) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun t : ℝ => Matrix.diagonal (fun k => Real.exp (ell k * t)) i j)
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    fun_prop
  · simp only [Matrix.diagonal_apply_ne _ hij]
    exact continuous_const

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_InvariantVersion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A strictly invariant version of an almost-everywhere invariant observable

For a measurable group action, use the essential constant value of the
observable along the orbit with respect to a nonzero translation-invariant
measure on the acting group. Fubini gives agreement almost everywhere;
translation invariance makes the new version invariant at every point.
This supplies the pointwise neutral invariance needed for selecting
noncentral return pairs.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree

theorem exists_strictly_invariant_version
    {H X Y : Type*} [Group H] [MeasurableSpace H]
    [MeasurableSpace X] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] [Inhabited Y]
    (σ : Measure H) [SigmaFinite σ] [NeZero σ]
    (μ : Measure X) [SigmaFinite μ]
    (R : H → X → X) (hR : Measurable (fun p : H × X => R p.1 p.2))
    (hone : ∀ x, R 1 x = x) (hmul : ∀ a b x, R a (R b x) = R (a * b) x)
    (hσ : ∀ b : H, MeasurePreserving (fun a => a * b) σ σ)
    (F : X → Y) (hF : Measurable F)
    (hinv : ∀ a : H, ∀ᵐ x ∂μ, F (R a x) = F x) :
    ∃ V : X → Y, V =ᵐ[μ] F ∧ AEMeasurable V μ ∧
      ∀ a x, V (R a x) = V x := by
  let E : X → Prop := fun x => ∃ y : Y, ∀ᵐ a ∂σ, F (R a x) = y
  let V : X → Y := fun x => if h : E x then h.choose else default
  have hvalue (x : X) (hx : E x) : ∀ᵐ a ∂σ, F (R a x) = V x := by
    simpa only [V, dite_eq_left hx] using hx.choose_spec
  have hpull (x : X) (b : H) (y : Y) (hy : ∀ᵐ a ∂σ, F (R a x) = y) :
      ∀ᵐ a ∂σ, F (R a (R b x)) = y := by
    have hmap : ∀ᵐ a ∂σ.map (fun a => a * b), F (R a x) = y := by
      simpa only [(hσ b).map_eq] using hy
    have h := ae_of_ae_map (hσ b).measurable.aemeasurable hmap
    simpa only [hmul] using h
  have hE (x : X) (b : H) : E (R b x) ↔ E x := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      have h := hpull (R b x) b⁻¹ y hy
      simpa only [hmul, inv_mul_cancel, hone] using h
    · rintro ⟨y, hy⟩
      exact ⟨y, hpull x b y hy⟩
  have hstrict (b : H) (x : X) : V (R b x) = V x := by
    by_cases hx : E x
    · have hy := (hE x b).mpr hx
      obtain ⟨a, ha, hb⟩ := ((hvalue (R b x) hy).and (hpull x b (V x) (hvalue x hx))).exists
      exact ha.symm.trans hb
    · have hy : ¬ E (R b x) := fun h => hx ((hE x b).mp h)
      simp only [V, dite_eq_right hx, dite_eq_right hy]
  have hmeas : MeasurableSet {p : H × X | F (R p.1 p.2) = F p.2} :=
    measurableSet_eq_fun (hF.comp hR) (hF.comp measurable_snd)
  have horbit : ∀ᵐ x ∂μ, ∀ᵐ a ∂σ, F (R a x) = F x :=
    (Measure.ae_ae_comm hmeas).mp (Eventually.of_forall hinv)
  have heq : V =ᵐ[μ] F := by
    filter_upwards [horbit] with x hx
    have hEx : E x := ⟨F x, hx⟩
    obtain ⟨a, ha, hb⟩ := ((hvalue x hEx).and hx).exists
    exact ha.symm.trans hb
  exact ⟨V, heq, hF.aemeasurable.congr heq.symm, hstrict⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_LusinFlowReturns
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous returns to compact Lusin sets

The compact recurrence construction retains continuity of a measurable
observable. This supplies one conull set for all pairs in the pointwise
stable-holonomy argument.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace DukePrimeDegree

theorem exists_conull_lusin_flow_returns
    {Y Z : Type*} [TopologicalSpace Y] [MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Y) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]
    {Φ : ℝ → Y → Y} (hΦ : Measurable (fun p : Y × ℝ => Φ p.2 p.1))
    (hzero : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hpres : ∀ t, MeasurePreserving (Φ t) μ μ)
    (F : Y → Z) (hF : Measurable F)
    (N : Set Y) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    ∃ M : Set Y, MeasurableSet M ∧ μ M = 0 ∧
      ∀ x ∉ M, ∀ y ∉ M, ∃ K : Set Y, IsCompact K ∧ K ⊆ Nᶜ ∧ ContinuousOn F K ∧
        ∀ R : ℝ, ∃ t : ℝ, R < t ∧ Φ t x ∈ K ∧ Φ t y ∈ K := by
  have hK (m : ℕ) := exists_compact_continuousOn_metrizable μ F hF N hN hNzero
    (ENNReal.ofReal (((1 / 2 : ℝ) ^ m) / 8))
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  choose K hcompact hKN hsmall hcont using hK
  obtain ⟨G, hGmeas, hae, hgood⟩ := exists_eventual_flow_good_sets μ hΦ hzero hadd hpres
    K (fun m => (hcompact m).isClosed.measurableSet) hsmall
  obtain ⟨M, hbad, hM, hMzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  refine ⟨M, hM, hMzero, ?_⟩
  intro x hx y hy
  have hxG : ∀ᶠ m in atTop, x ∈ G m := by
    by_contra h
    exact hx (hbad h)
  have hyG : ∀ᶠ m in atTop, y ∈ G m := by
    by_contra h
    exact hy (hbad h)
  obtain ⟨m, hxm, hym⟩ := (hxG.and hyG).exists
  exact ⟨K m, hcompact m, hKN m, hcont m,
    exists_late_simultaneous_compact_return Φ (K m) x y
      (hgood m x hxm) (hgood m y hym)⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralWeightSpace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite-dimensional neutral weight space

Real scalar closure of the trace-zero neutral weights supplies a
locally compact abelian group with Haar measure. Its diagonal action
is the same neutral action used in the exceptional-return argument.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem continuous_neutralSpaceDiagonal {n : ℕ} (i j : Fin n) :
    Continuous (neutralSpaceDiagonal i j) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  change Continuous (fun u : Multiplicative (neutralWeightSpace i j) =>
    Matrix.diagonal (fun r => Real.exp (u.toAdd.val r * 1)) a b)
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq, mul_one]
    exact Real.continuous_exp.comp ((continuous_apply a).comp
      (continuous_subtype_val.comp (show Continuous (fun u : Multiplicative
        (neutralWeightSpace i j) => u.toAdd) from continuous_id)))
  · simp only [Matrix.diagonal_apply_ne _ hab]
    exact continuous_const

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralLeafVersion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A pointwise neutral-invariant version of the intrinsic leaf data

Neutral diagonal translations have root scaling factor one, so their
actual leaf kernels agree almost everywhere. Haar orbit constants give
a version of the countable determining data invariant under every
neutral translation at every point.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_neutralSpace_rootKernel_eq
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ a : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow a)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (u : Multiplicative (neutralWeightSpace i j)) :
    ∀ᵐ x ∂μ, intrinsicRootKernel hij μ hfree (rightAction x (neutralSpaceDiagonal i j u)) =
      intrinsicRootKernel hij μ hfree x := by
  have hpres : MeasurePreserving (fun x => rightAction x (neutralSpaceDiagonal i j u)) μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    change μ.map (fun x => rightAction x (diagonalOneParameter u.toAdd.val u.toAdd.property.1 1)) = μ
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hmap : ∀ᵐ y ∂μ.map (fun x => rightAction x (neutralSpaceDiagonal i j u)),
      intrinsicRootKernel hij μ hfree y = intrinsicRootLeaf hij μ y := by
    rw [hpres.map_eq]
    exact ae_intrinsicRootKernel_eq hij μ hfree
  have htarget := ae_of_ae_map hpres.measurable.aemeasurable hmap
  have hcov := ae_intrinsicRootLeaf_diagonal hij u.toAdd.val u.toAdd.property.1 1 μ hfree hpres.map_eq
  have hdiff : u.toAdd.val j - u.toAdd.val i = 0 := sub_eq_zero.mpr u.toAdd.property.2.symm
  have hscale : rootTimeScaling u.toAdd.val i j 1 = Homeomorph.refl ℝ := by
    ext t
    simp [rootTimeScaling, hdiff]
  filter_upwards [ae_intrinsicRootKernel_eq hij μ hfree, htarget, hcov,
    ae_intrinsicRootLeaf_spec hij μ hfree] with x hx ht hc hs
  rw [ht, hx]
  change intrinsicRootLeaf hij μ
    (rightAction x (diagonalOneParameter u.toAdd.val u.toAdd.property.1 1)) = _
  rw [hc, hscale]
  change anchorNormalize ((intrinsicRootLeaf hij μ x).map id) (Metric.ball 0 1) = _
  rw [Measure.map_id]
  simp only [anchorNormalize, hs.2, inv_one, one_smul]

theorem exists_strictly_neutral_invariant_leafData
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ a : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow a)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∃ V : X (d + 1) → (ℕ × ℕ → ℝ),
      V =ᵐ[μ] intrinsicLeafData hij μ hfree ∧ AEMeasurable V μ ∧
      ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
        ∀ x, V (rightAction x (diagonalOneParameter ell hell 1)) = V x := by
  let H := Multiplicative (neutralWeightSpace i j)
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let σ : Measure H := Measure.haar
  let R : H → X (d + 1) → X (d + 1) :=
    fun u x => rightAction x (neutralSpaceDiagonal i j u)
  have hR : Measurable (fun p : H × X (d + 1) => R p.1 p.2) := by
    exact ((continuous_rightAction_uncurry (d + 1)).comp
      (continuous_snd.prodMk ((continuous_neutralSpaceDiagonal i j).comp continuous_fst))).measurable
  have hone (x : X (d + 1)) : R 1 x = x := by simp [R]
  have hmul (a b : H) (x : X (d + 1)) : R a (R b x) = R (a * b) x := by
    dsimp only [R]
    rw [rightAction_mul, ← map_mul, mul_comm b a]
  have hinv (a : H) : ∀ᵐ x ∂μ,
      intrinsicLeafData hij μ hfree (R a x) = intrinsicLeafData hij μ hfree x := by
    filter_upwards [ae_neutralSpace_rootKernel_eq d hij μ hA hfree a] with x hx
    exact (intrinsicLeafData_eq_iff hij μ hfree (R a x) x).mpr hx
  obtain ⟨V, heq, hm, hv⟩ := exists_strictly_invariant_version σ μ R hR hone hmul
    (fun b => measurePreserving_mul_right σ b)
    (intrinsicLeafData hij μ hfree) (measurable_intrinsicLeafData hij μ hfree) hinv
  refine ⟨V, heq, hm, ?_⟩
  intro ell hell hn x
  exact hv (Multiplicative.ofAdd (⟨ell, hell, hn⟩ : neutralWeightSpace i j)) x

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_NeutralLeafFlow
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Strict neutral invariance at arbitrary real times
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma diagonalOneParameter_rescale_weights
    {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (t : ℝ) :
    diagonalOneParameter (fun r => ell r * t)
      (by rw [← Finset.sum_mul, hell, zero_mul]) 1 = diagonalOneParameter ell hell t := by
  apply Subtype.ext
  simp [diagonalOneParameter]

theorem exists_strictly_neutral_flow_invariant_leafData
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ a : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow a)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∃ V : X (d + 1) → (ℕ × ℕ → ℝ),
      V =ᵐ[μ] intrinsicLeafData hij μ hfree ∧ AEMeasurable V μ ∧
      ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
        ∀ t x, V (rightAction x (diagonalOneParameter ell hell t)) = V x := by
  obtain ⟨V, heq, hm, hv⟩ := exists_strictly_neutral_invariant_leafData d hij μ hA hfree
  refine ⟨V, heq, hm, ?_⟩
  intro ell hell hn t x
  have hsum : ∑ r, ell r * t = 0 := by rw [← Finset.sum_mul, hell, zero_mul]
  have he := hv (fun r => ell r * t) hsum (congrArg (· * t) hn) x
  rwa [diagonalOneParameter_rescale_weights] at he

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafBoxSeparation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Pointwise separation of root fibers on a conull set

Coordinate disintegration gives one ambient null set outside which the
intrinsic leaf agrees with the chart leaf at every remaining point.
Within a fixed root box, equal leaves at points in one fiber then force
equal points in the noninvariant ergodic case. This strengthens the
conditional-almost-everywhere form needed in EKL (2006), Lemma 4.4(2).
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootBox_exists_nullset_for_coordinates
    {n : ℕ} {i j k : Fin n} {hij : i ≠ j}
    (A : RootBox hij k) (μ : Measure (X n))
    (Q : RootSlice i j k × ℝ → Prop)
    (hQ : ∀ᵐ z ∂A.coordinateMeasure μ, Q z) :
    ∃ N : Set (X n), MeasurableSet N ∧ μ N = 0 ∧
      ∀ z ∈ A.domain, rootQuotientParametrization hij z ∉ N → Q z := by
  have hchart : ∀ᵐ x ∂μ.restrict A.range,
      ∀ z ∈ A.domain, rootQuotientParametrization hij z = x → Q z := by
    apply A.ae_of_coordinate μ
    filter_upwards [hQ, A.coordinateMeasure_ae_domain μ] with z hz hzd
    intro w hw heq
    have he : (⟨w, hw⟩ : A.domain) = ⟨z, hzd⟩ := A.embedding.injective heq
    have he' : w = z := congrArg Subtype.val he
    simpa only [he'] using hz
  have hall := (ae_restrict_iff' A.range_open.measurableSet).mp hchart
  obtain ⟨N, hbad, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hall)
  refine ⟨N, hN, hzero, ?_⟩
  intro z hz hx
  by_contra h
  apply hx
  apply hbad
  intro H
  exact h (H ⟨⟨z, hz⟩, rfl⟩ z hz rfl)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootOrbitRebase
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rebasing at every pair outside a single null set

Countably many long root boxes turn coordinate disintegration into a
pointwise rebasing law along all root orbits. In particular, if a root
conditional is Dirac almost everywhere, one conull set meets each root
orbit at most once. This is the atomic case needed by the support argument.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootBox_rebase_outside_nullset
    {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (A : RootBox hij k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) :
    ∃ N : Set (X n), MeasurableSet N ∧ μ N = 0 ∧
      ∀ z ∈ A.domain, ∀ w ∈ A.domain,
        rootQuotientParametrization hij z ∉ N →
        rootQuotientParametrization hij w ∉ N → z.1 = w.1 →
        intrinsicRootLeaf hij μ (rootQuotientParametrization hij w) =
          basedRealMeasure (intrinsicRootLeaf hij μ (rootQuotientParametrization hij z))
            (w.2 - z.2) := by
  let Q := fun z : RootSlice i j k × ℝ =>
    intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) = A.basedLeaf R μ z ∧
    IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) ∧
    0 < A.leafMeasure R μ z.1 (Metric.ball z.2 1)
  have hQ : ∀ᵐ z ∂A.coordinateMeasure μ, Q z := by
    have hloc := ae_of_ae_map measurable_fst.aemeasurable
      ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun _ h => h.1)
    filter_upwards [A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree, hloc,
      A.ae_leafMeasure_ball_pos R hAR μ hfree] with z hz hl hp
    exact ⟨hz, hl, hp 1 zero_lt_one⟩
  obtain ⟨N, hN, hzero, hgood⟩ := rootBox_exists_nullset_for_coordinates A μ Q hQ
  refine ⟨N, hN, hzero, ?_⟩
  intro z hz w hw hzN hwN hbase
  have hgz := hgood z hz hzN
  have hgw := hgood w hw hwN
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hgz.2.1
  rw [hgz.1, hgw.1]
  change basedRealMeasure (A.leafMeasure R μ w.1) w.2 =
    basedRealMeasure (basedRealMeasure (A.leafMeasure R μ z.1) z.2) (w.2 - z.2)
  rw [← hbase, basedRealMeasure_rebase _ _ _ hgz.2.2]
  congr 1
  ring

theorem exists_nullset_root_orbit_rebase
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧ ∀ x ∉ N, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∉ N →
      intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ x) t := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let C := fun (k : Fin (d + 1)) (m : ℕ) => rootLongBoxFamily hij k 1 m
  let (k : Fin (d + 1)) (m : ℕ) : Countable (C k m) :=
    (rootLongBoxFamily_countable hij k 1 m).to_subtype
  let I := Σ k : Fin (d + 1), Σ m : ℕ, C k m
  let box := fun q : I => q.2.2.val
  have htime (q : I) : (box q).time ⊆ rootLeafWindow (1 + (q.2.1 : ℝ)) 0 := by
    rw [rootLongBoxFamily_time hij q.1 1 q.2.1 (box q) q.2.2.property]
    simp only [rootLeafWindow, Nat.cast_zero, add_zero, subset_refl]
  have hlocal (q : I) := rootBox_rebase_outside_nullset hij μ hfree (box q)
    (1 + (q.2.1 : ℝ)) (htime q)
  choose N hN hzero hrebase using hlocal
  obtain ⟨M, hbad, hM, hMzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hfree)
  let E := M ∪ ⋃ q : I, N q
  have hEzero : μ E = 0 := measure_union_null hMzero (measure_iUnion_null hzero)
  refine ⟨E, hM.union (MeasurableSet.iUnion hN), hEzero, ?_⟩
  intro x hx t hy
  have hxfree : ∀ u : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij u) = x → u = 0 := by
    by_contra h
    exact hx (Or.inl (hbad h))
  obtain ⟨k, B, z, hz⟩ := exists_rootBox_at hij x
  let s := z.val.1
  let v := z.val.2
  have hxparam : rootQuotientParametrization hij (s, v) = x := hz
  have hyparam : rootQuotientParametrization hij (s, v + t) =
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) := by
    rw [rootQuotientParametrization_add, hxparam]
  have hsfree := root_time_injective_of_free hij s v (by rwa [hxparam])
  obtain ⟨m, hm⟩ := exists_nat_gt (max |v| |v + t|)
  have hv : v ∈ rootLeafWindow 1 m := by
    apply abs_lt.mp
    exact (lt_of_le_of_lt (le_max_left _ _) hm).trans (by linarith)
  have hvt : v + t ∈ rootLeafWindow 1 m := by
    apply abs_lt.mp
    exact (lt_of_le_of_lt (le_max_right _ _) hm).trans (by linarith)
  obtain ⟨D, hD, hsD⟩ := rootLongBoxFamily_covers hij k 1 m s hsfree
  let q : I := ⟨k, m, ⟨D, hD⟩⟩
  have htD : D.time = rootLeafWindow 1 m := rootLongBoxFamily_time hij k 1 m D hD
  have hzD : (s, v) ∈ (box q).domain := ⟨hsD, htD.symm ▸ hv⟩
  have hwD : (s, v + t) ∈ (box q).domain := ⟨hsD, htD.symm ▸ hvt⟩
  have hNx : rootQuotientParametrization hij (s, v) ∉ N q := by
    rw [hxparam]
    exact fun h => hx (Or.inr (mem_iUnion.mpr ⟨q, h⟩))
  have hNy : rootQuotientParametrization hij (s, v + t) ∉ N q := by
    rw [hyparam]
    exact fun h => hy (Or.inr (mem_iUnion.mpr ⟨q, h⟩))
  have h := hrebase q (s, v) hzD (s, v + t) hwD hNx hNy rfl
  simpa only [hxparam, hyparam, add_sub_cancel_left] using h

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CompactLimitData
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed observable values at compact orbit limits
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem compact_orbit_limit_with_data
    {n : ℕ} {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (p : ℕ → X n) (H : ℕ → G n) (h : G n)
    (hp : ∀ m, p m ∈ K) (hq : ∀ m, rightAction (p m) (H m) ∈ K)
    (a b : Z) (ha : ∀ m, F (p m) = a) (hb : ∀ m, F (rightAction (p m) (H m)) = b)
    (hH : Tendsto H atTop (𝓝 h)) :
    ∃ z ∈ K, rightAction z h ∈ K ∧ F z = a ∧ F (rightAction z h) = b := by
  obtain ⟨z, hz, φ, hφ, hlim⟩ := hK.isSeqCompact hp
  have hpLim : Tendsto (p ∘ φ) atTop (𝓝 z) := hlim
  have hqLim : Tendsto (fun m => rightAction (p (φ m)) (H (φ m)))
      atTop (𝓝 (rightAction z h)) :=
    (continuous_rightAction_uncurry n).continuousAt.tendsto.comp
      (hpLim.prodMk_nhds (hH.comp hφ.tendsto_atTop))
  have hz' : rightAction z h ∈ K := hK.isClosed.mem_of_tendsto hqLim
    (Eventually.of_forall fun m => hq (φ m))
  have haLim : Tendsto (fun m => F (p (φ m))) atTop (𝓝 (F z)) :=
    (hF z hz).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hpLim, Eventually.of_forall fun m => hp (φ m)⟩)
  have hbLim : Tendsto (fun m => F (rightAction (p (φ m)) (H (φ m))))
      atTop (𝓝 (F (rightAction z h))) :=
    (hF _ hz').tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hqLim, Eventually.of_forall fun m => hq (φ m)⟩)
  refine ⟨z, hz, hz', ?_, ?_⟩
  · have hc : Tendsto (fun m => F (p (φ m))) atTop (𝓝 a) := by
      simpa only [ha] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
    exact tendsto_nhds_unique haLim hc
  · have hc : Tendsto (fun m => F (rightAction (p (φ m)) (H (φ m)))) atTop (𝓝 b) := by
      simpa only [hb] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b))
    exact tendsto_nhds_unique hbLim hc

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootHolonomy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Pointwise root holonomy under a neutral diagonal flow

This is the consequence of Einsiedler–Katok (2003), Proposition 5.1,
needed by the high-entropy commutator argument. One null set works for
all pairs and all relative matrices whose conjugates approach a root
translation. Lusin compactness and strict neutral invariance identify
both limiting root conditionals; pointwise rebasing supplies holonomy.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_neutral_root_holonomy_oai
    (d : ℕ) {a b : Fin (d + 1)} (hab : a ≠ b)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell a = ell b) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ x ∉ N, ∀ y ∉ N, ∀ g : G (d + 1), rightAction x g = y → ∀ c : ℝ,
        Tendsto (fun t : ℝ => diagonalOneParameter ell hell t * g *
          diagonalOneParameter ell hell (-t)) atTop
          (𝓝 (Matrix.SpecialLinearGroup.transvection hab c)) →
        intrinsicRootLeaf hab μ y = basedRealMeasure (intrinsicRootLeaf hab μ x) c := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hab t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx a b hab
  let F := intrinsicLeafData hab μ hfree
  obtain ⟨V, hVF, _, hV⟩ := exists_strictly_neutral_flow_invariant_leafData d hab μ hA hfree
  obtain ⟨R, hR, hRzero, hrebase⟩ := exists_nullset_root_orbit_rebase d hab μ hA
  have hspec : ∀ᵐ x ∂μ, intrinsicRootKernel hab μ hfree x = intrinsicRootLeaf hab μ x ∧ V x = F x :=
    (ae_intrinsicRootKernel_eq hab μ hfree).and hVF
  obtain ⟨S, hbad, hS, hSzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hspec)
  let E := R ∪ S
  have hE : MeasurableSet E := hR.union hS
  have hEzero : μ E = 0 := measure_union_null hRzero hSzero
  have hgood (x : X (d + 1)) (hx : x ∉ E) :
      intrinsicRootKernel hab μ hfree x = intrinsicRootLeaf hab μ x ∧ V x = F x := by
    by_contra h
    exact hx (Or.inr (hbad h))
  let Φ : ℝ → X (d + 1) → X (d + 1) :=
    fun t x => rightAction x (diagonalOneParameter ell hell (-t))
  have hcont : Continuous (fun p : X (d + 1) × ℝ => Φ p.2 p.1) :=
    (continuous_rightAction_uncurry (d + 1)).comp
      (continuous_fst.prodMk ((continuous_diagonalOneParameter ell hell).comp continuous_snd.neg))
  have hzero (x : X (d + 1)) : Φ 0 x = x := by simp [Φ, diagonalOneParameter_zero]
  have hadd (s t : ℝ) (x : X (d + 1)) : Φ (s + t) x = Φ s (Φ t x) := by
    dsimp [Φ]
    rw [rightAction_mul, ← diagonalOneParameter_add]
    congr 2
    ring
  have hpres (t : ℝ) : MeasurePreserving (Φ t) μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    dsimp only [Φ]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨M, hM, hMzero, hreturns⟩ := exists_conull_lusin_flow_returns μ hcont.measurable
    hzero hadd hpres F (measurable_intrinsicLeafData hab μ hfree) E hE hEzero
  refine ⟨E ∪ M, hE.union hM, measure_union_null hEzero hMzero, ?_⟩
  intro x hx y hy g hxy c hlim
  have hxE : x ∉ E := fun h => hx (Or.inl h)
  have hyE : y ∉ E := fun h => hy (Or.inl h)
  obtain ⟨K, hK, hKE, hFK, hret⟩ := hreturns x (fun h => hx (Or.inr h)) y (fun h => hy (Or.inr h))
  have hseq (m : ℕ) : ∃ t : ℝ, (m : ℝ) < t ∧ Φ t x ∈ K ∧ Φ t y ∈ K := hret m
  choose t ht htx hty using hseq
  have htop : Tendsto t atTop atTop :=
    tendsto_atTop_mono (fun m => (ht m).le) tendsto_natCast_atTop_atTop
  let H : ℕ → G (d + 1) := fun m => diagonalOneParameter ell hell (t m) * g *
    diagonalOneParameter ell hell (-t m)
  have hpair (m : ℕ) : rightAction (Φ (t m) x) (H m) = Φ (t m) y := by
    rw [← hxy]
    dsimp only [Φ, H]
    rw [rightAction_mul, rightAction_mul]
    congr 1
    rw [diagonalOneParameter_neg]
    group
  have hdata (w : X (d + 1)) (m : ℕ) (hw : Φ (t m) w ∈ K) : F (Φ (t m) w) = V w :=
    (hgood _ (hKE hw)).2.symm.trans (hV ell hell hneut (-t m) w)
  obtain ⟨z, hz, hzc, hFz, hFzc⟩ := compact_orbit_limit_with_data K hK F hFK
    (fun m => Φ (t m) x) H (Matrix.SpecialLinearGroup.transvection hab c) htx
    (fun m => by rw [hpair]; exact hty m) (V x) (V y)
    (fun m => hdata x m (htx m))
    (fun m => by rw [hpair]; exact hdata y m (hty m)) (hlim.comp htop)
  have hleaf (w u : X (d + 1)) (hw : w ∉ E) (hu : u ∉ E) (hFwu : F w = V u) :
      intrinsicRootLeaf hab μ w = intrinsicRootLeaf hab μ u := by
    have he : F w = F u := hFwu.trans (hgood u hu).2
    have hk := (intrinsicLeafData_eq_iff hab μ hfree w u).mp he
    exact (hgood w hw).1.symm.trans (hk.trans (hgood u hu).1)
  have hxz := hleaf z x (hKE hz) hxE hFz
  have hyz := hleaf _ y (hKE hzc) hyE hFzc
  have hr := hrebase z (fun h => hKE hz (Or.inl h)) c (fun h => hKE hzc (Or.inl h))
  rw [hxz, hyz] at hr
  exact hr

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_nullset_neutral_root_holonomy_oai := @OAI.DukePrimeDegree.exists_nullset_neutral_root_holonomy_oai
