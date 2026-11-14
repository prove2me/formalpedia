-- Prove2me | solution 1 for OAI.DukePrimeDegree.nonempty_rootPairSelectionData
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:52:15.602799+00:00
-- url     : https://prove2.me/submissions/bab4b34e-9d1b-40f0-89c5-2363673a8825

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootCharts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_locallyFinite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_locallyFinite _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}



theorem disintegrate (B : RootBox hij k) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    Measure.map (rootQuotientParametrization hij)
      ((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ) = μ.restrict B.range := by
  rw [conditionalKernel,Measure.disintegrate]
  exact B.map_coordinateMeasure μ

end RootBox

end PrimeDegreePackets


open scoped ENNReal ProbabilityTheory
end
end

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafAnchors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_locallyFinite _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_leafMeasure_change_anchor (A B : RootBox hij k) (R S : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (hAB : A.time ⊆ B.time) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse →
      A.leafMeasure R μ s = anchorNormalize (B.leafMeasure S μ s) A.time := by
  let C := rootLongBoxFamily hij k S
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k S m).to_subtype
  have hT (m : ℕ) (D : C m) : D.val.time = rootLeafWindow S m :=
    rootLongBoxFamily_time hij k S m D.val D.prop
  have hinc (m : ℕ) (D : C m) : B.time ⊆ D.val.time := by
    rw [hT m D]
    exact hBS.trans (rootLeafWindow_mono S (Nat.zero_le m))
  have hA : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (D : C m),
      s ∈ D.val.transverse → D.val.conditionalKernel μ s A.time ≠ 0 ∧
      (A.leafMeasure R μ s).restrict D.val.time =
        (anchorNormalize (D.val.conditionalKernel μ s) A.time).restrict D.val.time := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro D
    exact A.ae_leafMeasure_restrict R hAR μ hfree D.val (hAB.trans (hinc m D))
  have hB := base_ae_of_ae A B hAB μ (B.ae_leafMeasure_spec S hBS μ hfree)
  filter_upwards [hA,hB,A.ae_injective_root_slice_of_ae_free μ hfree] with s hsA hsB hi
  intro hsBt
  have hsB' := hsB hsBt
  apply measure_eq_of_restrictionChain (rootLeafWindow S) (rootLeafWindow_mono S)
    (rootLeafWindow_cover S)
  intro m
  obtain ⟨D,hDC,hsD⟩ := rootLongBoxFamily_covers hij k S m s hi
  let D' : C m := ⟨D,hDC⟩
  have ha := hsA m D' hsD
  have hb := hsB'.2.2.2 m D hDC hsD
  have hBD : B.time ⊆ rootLeafWindow S m := hBS.trans (rootLeafWindow_mono S (Nat.zero_le m))
  have hAD : A.time ⊆ rootLeafWindow S m := hAB.trans hBD
  have hmB : D.conditionalKernel μ s B.time ≠ 0 :=
    (lt_of_lt_of_le (pos_iff_ne_zero.mpr ha.1) (measure_mono hAB)).ne'
  have he := congrArg (fun ν : Measure ℝ => anchorNormalize ν A.time) hb
  rw [anchorNormalize_restrict_comm _ A.time_open.measurableSet hAD,
    anchorNormalize_restrict_comm _ A.time_open.measurableSet hAD,
    anchorNormalize_twice _ _ _ hmB (measure_ne_top _ _)] at he
  rw [he]
  simpa only [hT m D'] using ha.2

 

theorem ae_change_anchor_mass (A B : RootBox hij k) (R S : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (hAB : A.time ⊆ B.time) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse →
      B.leafMeasure S μ s A.time ≠ 0 ∧ B.leafMeasure S μ s A.time ≠ ∞ := by
  filter_upwards [A.ae_leafMeasure_change_anchor B R S hAR hBS hAB μ hfree,
    A.ae_leafMeasure_spec R hAR μ hfree] with s hs hspec
  intro hsB
  have H : anchorNormalize (B.leafMeasure S μ s) A.time A.time = 1 := by
    rw [←hs hsB]
    exact hspec.2.1
  constructor
  · intro hz
    simp only [anchorNormalize,Measure.smul_apply,smul_eq_mul,hz,mul_zero] at H
    exact zero_ne_one H
  · intro hz
    simp only [anchorNormalize,Measure.smul_apply,smul_eq_mul,hz,ENNReal.inv_top,zero_mul] at H
    exact zero_ne_one H



end PrimeDegreePackets.RootBox


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntrinsicLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
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


namespace PrimeDegreePackets

lemma ae_eq_of_measurePreserving_ennreal_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1)
    (hmono : ∀ᵐ x ∂μ, f x ≤ f (T x)) : f =ᵐ[μ] f ∘ T := by
  have hint : ∫⁻ x, f x ∂μ < ∞ :=
    (lintegral_mono_ae hf1).trans_lt (by simp)
  have he : ∫⁻ x, f (T x) ∂μ = ∫⁻ x, f x ∂μ := by
    have hf' : AEMeasurable f (μ.map T) := hT.map_eq.symm ▸ hf
    exact ((lintegral_map' hf' hT.measurable.aemeasurable).symm).trans
      (congrArg (fun ν : Measure α => ∫⁻ x, f x ∂ν) hT.map_eq)
  exact ae_eq_of_ae_le_of_lintegral_le hmono hint.ne
    (hf.comp_quasiMeasurePreserving hT.quasiMeasurePreserving) he.le

lemma ae_eq_of_measurePreserving_ennreal_ge {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1)
    (hmono : ∀ᵐ x ∂μ, f (T x) ≤ f x) : f =ᵐ[μ] f ∘ T := by
  have hfT := hf.comp_quasiMeasurePreserving hT.quasiMeasurePreserving
  have he : ∫⁻ x, f (T x) ∂μ = ∫⁻ x, f x ∂μ := by
    have hf' : AEMeasurable f (μ.map T) := hT.map_eq.symm ▸ hf
    exact ((lintegral_map' hf' hT.measurable.aemeasurable).symm).trans
      (congrArg (fun ν : Measure α => ∫⁻ x, f x ∂ν) hT.map_eq)
  have hint : ∫⁻ x, f (T x) ∂μ < ∞ := by
    rw [he]
    exact (lintegral_mono_ae hf1).trans_lt (by simp)
  exact (ae_eq_of_ae_le_of_lintegral_le hmono hint.ne hf he.ge).symm

lemma realScaling_preimage_singleton (c : ℝ) (hc : c ≠ 0) :
    (Homeomorph.mulLeft₀ c hc) ⁻¹' ({0} : Set ℝ) = {0} := by
  ext x
  change c*x=0 ↔ x=0
  exact mul_eq_zero.trans (or_iff_right hc)

lemma realScaling_preimage_unitBall_subset (c : ℝ) (hc : 1 ≤ c) :
    (Homeomorph.mulLeft₀ c (ne_of_gt (zero_lt_one.trans_le hc))) ⁻¹' Metric.ball (0:ℝ) 1 ⊆
      Metric.ball 0 1 := by
  intro x hx
  simp only [Set.mem_preimage,Metric.mem_ball,Homeomorph.coe_mulLeft₀,Real.dist_eq,sub_zero] at hx ⊢
  rw [abs_mul,abs_of_nonneg (zero_le_one.trans hc)] at hx
  nlinarith [abs_nonneg x]

lemma realScaling_unitBall_subset_preimage (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    Metric.ball (0:ℝ) 1 ⊆ (Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1 := by
  intro x hx
  simp only [Set.mem_preimage,Metric.mem_ball,Homeomorph.coe_mulLeft₀,Real.dist_eq,sub_zero] at hx ⊢
  rw [abs_mul,abs_of_pos hc]
  nlinarith [abs_nonneg x]

lemma normalized_realScaling_atom (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0) :
    anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc)) (Metric.ball 0 1) {0} =
      (ν ((Homeomorph.mulLeft₀ c hc) ⁻¹' Metric.ball 0 1))⁻¹ * ν {0} := by
  change (ν.map (Homeomorph.mulLeft₀ c hc) (Metric.ball 0 1))⁻¹ *
    ν.map (Homeomorph.mulLeft₀ c hc) {0} = _
  rw [Measure.map_apply (Homeomorph.mulLeft₀ c hc).measurable Metric.isOpen_ball.measurableSet,
    Measure.map_apply (Homeomorph.mulLeft₀ c hc).measurable (measurableSet_singleton 0),
    realScaling_preimage_singleton]

 

theorem ae_atom_eq_of_scaling_covariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (ν : α → Measure ℝ) (hν : AEMeasurable ν μ)
    (hball : ∀ᵐ x ∂μ, ν x (Metric.ball 0 1) = 1)
    (c : ℝ) (hc : 0 < c)
    (hcov : ∀ᵐ x ∂μ, ν (T x) =
      anchorNormalize ((ν x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, ν x {0} = ν (T x) {0} := by
  have hm : AEMeasurable (fun x => ν x {0}) μ :=
    (Measure.measurable_coe (measurableSet_singleton 0)).comp_aemeasurable hν
  have hle : ∀ᵐ x ∂μ, ν x {0} ≤ 1 := by
    filter_upwards [hball] with x hx
    rw [←hx]
    exact measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self zero_lt_one))
  rcases le_total 1 c with h | h
  · apply ae_eq_of_measurePreserving_ennreal_le μ hT hm hle
    filter_upwards [hball,hcov] with x hx he
    rw [he,normalized_realScaling_atom]
    have hb : ν x ((Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1) ≤ 1 := by
      rw [←hx]
      exact measure_mono (realScaling_preimage_unitBall_subset c h)
    calc
      ν x {0} = 1 * ν x {0} := (one_mul _).symm
      _ ≤ _ := mul_le_mul' (ENNReal.one_le_inv.mpr hb) le_rfl
  · apply ae_eq_of_measurePreserving_ennreal_ge μ hT hm hle
    filter_upwards [hball,hcov] with x hx he
    rw [he,normalized_realScaling_atom]
    have hb : 1 ≤ ν x ((Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1) := by
      rw [←hx]
      exact measure_mono (realScaling_unitBall_subset_preimage c hc h)
    calc
      _ ≤ 1 * ν x {0} := mul_le_mul' (ENNReal.inv_le_one.mpr hb) le_rfl
      _ = ν x {0} := one_mul _

lemma scaling_ball_mass_of_atom_eq (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0)
    (h0 : ν {0} ≠ 0) (hT : ν {0} ≠ ∞)
    (he : anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc)) (Metric.ball 0 1) {0} = ν {0}) :
    ν ((Homeomorph.mulLeft₀ c hc) ⁻¹' Metric.ball 0 1) = 1 := by
  rw [normalized_realScaling_atom] at he
  have H := congrArg (fun a : ℝ≥0∞ => a*(ν {0})⁻¹) he
  rw [ENNReal.mul_inv_cancel_right h0 hT,ENNReal.mul_inv_cancel h0 hT] at H
  exact ENNReal.inv_eq_one.mp H

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma real_iInter_ball_inv_nat :
    (⋂ m : ℕ, Metric.ball (0:ℝ) ((m+1:ℝ)⁻¹)) = {0} := by
  ext x
  simp only [mem_iInter,mem_singleton_iff,Metric.mem_ball,Real.dist_eq,sub_zero]
  constructor
  · intro h
    by_contra hx
    have hx0 : 0 < |x| := abs_pos.mpr hx
    obtain ⟨m,hm⟩ := exists_nat_gt (|x|⁻¹)
    have hm0 : (0:ℝ) < m+1 := by positivity
    have hh := h m
    have hl : (m+1:ℝ)⁻¹ < |x| := by
      rw [←one_div]
      apply (one_div_lt hm0 hx0).mpr
      simpa only [one_div] using hm.trans (by linarith : (m:ℝ) < m+1)
    exact (not_lt_of_ge hl.le) hh
  · rintro rfl m
    simp only [abs_zero]
    positivity

lemma realMeasure_eq_dirac_of_ball_masses (ν : Measure ℝ)
    (hsmall : ∀ m : ℕ, ν (Metric.ball 0 ((m+1:ℝ)⁻¹)) = 1)
    (hlarge : ∀ m : ℕ, ν (Metric.ball 0 (m+1:ℝ)) = 1) : ν = Measure.dirac 0 := by
  have hmono : Monotone (fun m : ℕ => Metric.ball (0:ℝ) (m+1:ℝ)) := by
    intro a b hab
    exact Metric.ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hab 1)
  have hu : ν univ = 1 := by
    rw [← Metric.iUnion_ball_nat_succ (0:ℝ),hmono.measure_iUnion]
    simp only [hlarge,iSup_const]
  have hanti : Antitone (fun m : ℕ => Metric.ball (0:ℝ) ((m+1:ℝ)⁻¹)) := by
    intro a b hab
    apply Metric.ball_subset_ball
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  have h0 : ν {0} = 1 := by
    rw [←real_iInter_ball_inv_nat,hanti.measure_iInter
      (fun _ => Metric.isOpen_ball.measurableSet.nullMeasurableSet) ⟨0,by rw [hsmall]; exact ENNReal.one_ne_top⟩]
    simp only [hsmall,iInf_const]
  let : IsFiniteMeasure ν := ⟨by rw [hu]; exact ENNReal.one_lt_top⟩
  have hc : ν ({0} : Set ℝ)ᶜ = 0 := by
    rw [measure_compl (measurableSet_singleton _) (by finiteness),hu,h0,tsub_self]
  ext s hs
  by_cases hx : (0:ℝ) ∈ s
  · rw [Measure.dirac_apply_of_mem hx]
    apply le_antisymm
    · simpa only [hu] using measure_mono (subset_univ s) (μ := ν)
    · rw [←h0]
      exact measure_mono (singleton_subset_iff.mpr hx)
  · simp only [Measure.dirac_apply,indicator_of_notMem hx]
    apply le_antisymm _ bot_le
    exact (measure_mono (subset_compl_singleton_iff.mpr hx)).trans hc.le

 

theorem ae_dirac_of_scaling_covariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (ν : α → Measure ℝ)
    (hν : AEMeasurable ν μ) (hball : ∀ᵐ x ∂μ, ν x (Metric.ball 0 1) = 1)
    (hscale : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α,
      MeasurePreserving T μ μ ∧ ∀ᵐ x ∂μ, ν (T x) =
        anchorNormalize ((ν x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, ν x {0} ≠ 0 → ν x = Measure.dirac 0 := by
  have H (c : ℝ) (hc : 0 < c) : ∀ᵐ x ∂μ, ν x {0} ≠ 0 → ν x (Metric.ball 0 (1/c)) = 1 := by
    obtain ⟨T,hT,hcov⟩ := hscale c hc
    have he := ae_atom_eq_of_scaling_covariance μ hT ν hν hball c hc hcov
    filter_upwards [hball,hcov,he] with x hx hc' he' h0
    have hT' : ν x {0} ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (by
      rw [←hx]
      exact measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self zero_lt_one)))
    have hh := scaling_ball_mass_of_atom_eq (ν x) c hc.ne' h0 hT' (by rw [←hc']; exact he'.symm)
    rwa [realScaling_preimage_ball c 1 hc] at hh
  have HS := ae_all_iff.mpr (fun m : ℕ => H (m+1) (by positivity))
  have HL := ae_all_iff.mpr (fun m : ℕ => H ((m+1:ℝ)⁻¹) (by positivity))
  filter_upwards [HS,HL] with x hs hl h0
  apply realMeasure_eq_dirac_of_ball_masses (ν x)
  · intro m
    simpa only [one_div] using hs m h0
  · intro m
    simpa only [one_div,inv_inv] using hl m h0

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem ae_intrinsicRootLeaf_atom_dirac (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x {0} ≠ 0 →
      intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  apply ae_dirac_of_scaling_covariance μ (intrinsicRootLeaf hij μ)
    (aemeasurable_intrinsicRootLeaf hij μ hfree)
    ((ae_intrinsicRootLeaf_spec hij μ hfree).mono fun x hx => hx.2)
  intro c hc
  let ell := coordinateContractionWeights d j
  have hell : ∑ k, ell k = 0 := coordinateContractionWeights_sum d j
  let t := Real.log c / (d+1:ℝ)
  let a := diagonalOneParameter ell hell t
  have hinv : μ.map (fun x => rightAction x a) = μ := by
    rw [show a = diagonalFlow (fun k : Fin d => ell k.castSucc*t) from
      diagonalOneParameter_eq_diagonalFlow ell hell t]
    exact hA _
  refine ⟨(fun x => rightAction x a),⟨(continuous_rightAction a).measurable,hinv⟩,?_⟩
  have hrate : ell j-ell i = (d+1:ℝ) := by
    simp [ell,coordinateContractionWeights,hij]
  have he : Real.exp ((ell j-ell i)*t) = c := by
    rw [hrate]
    dsimp [t]
    rw [mul_comm,div_mul_cancel₀ _ (by positivity),Real.exp_log hc]
  have hs : rootTimeScaling ell i j t = Homeomorph.mulLeft₀ c hc.ne' := by
    apply Homeomorph.ext
    intro v
    simp only [rootTimeScaling,Homeomorph.coe_mulLeft₀,he]
  have H := ae_intrinsicRootLeaf_diagonal hij ell hell t μ hfree hinv
  simpa only [hs] using H

 

theorem ae_intrinsicRootLeaf_zero_atom_or_trivial (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x {0} = 0 ∨ intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  filter_upwards [ae_intrinsicRootLeaf_atom_dirac d hij μ hA] with x hx
  exact eq_or_ne _ _ |>.imp_right hx

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_AmbientLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_leafMeasure_intrinsic (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.leafMeasure R μ s,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (A.leafMeasure R μ s) t := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hbound (m : ℕ) (B : C m) : B.val.time ⊆ rootLeafWindow (R+m) 0 := by
    rw [hT m B]
    simp only [rootLeafWindow,Nat.cast_zero,add_zero,subset_refl]
  have HD (m : ℕ) (B : C m) : ∀ᵐ s ∂(B.val.coordinateMeasure μ).fst,
      ∀ᵐ t ∂B.val.conditionalKernel μ s,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (B.val.leafMeasure (R+m) μ s) t := by
    have H : ∀ᵐ z ∂(B.val.coordinateMeasure μ).fst ⊗ₘ B.val.conditionalKernel μ,
        intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) = B.val.basedLeaf (R+m) μ z := by
      simpa only [conditionalKernel,Measure.disintegrate] using
        B.val.ae_intrinsicRootLeaf_coordinates (R+m) (hbound m B) μ hfree
    exact Measure.ae_ae_of_ae_compProd H
  have H (m : ℕ) (B : C m) : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      s ∈ B.val.transverse → ∀ᵐ t ∂(A.leafMeasure R μ s).restrict (rootLeafWindow R m),
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (A.leafMeasure R μ s) t := by
    filter_upwards [A.ae_leafMeasure_restrict R hAR μ hfree B.val (hinc m B),
      A.base_ae_of_ae B.val (hinc m B) μ (HD m B),
      A.ae_leafMeasure_change_anchor B.val R (R+m) hAR (hbound m B) (hinc m B) μ hfree,
      A.ae_change_anchor_mass B.val R (R+m) hAR (hbound m B) (hinc m B) μ hfree]
      with s hs hd he hm hsb
    have he' (t : ℝ) : basedRealMeasure (A.leafMeasure R μ s) t =
        basedRealMeasure (B.val.leafMeasure (R+m) μ s) t := by
      rw [he hsb]
      exact basedRealMeasure_smul _ _ (ENNReal.inv_ne_zero.mpr (hm hsb).2)
        (ENNReal.inv_ne_top.mpr (hm hsb).1) _
    have hh := ae_restrict_of_ae (s := B.val.time) (Measure.ae_smul_measure (hd hsb)
      ((B.val.conditionalKernel μ s A.time)⁻¹))
    change ∀ᵐ t ∂(anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict B.val.time,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (B.val.leafMeasure (R+m) μ s) t at hh
    rw [←(hs hsb).2,hT m B] at hh
    simpa only [he'] using hh
  have Hall := ae_all_iff.mpr (fun m => ae_all_iff.mpr (H m))
  filter_upwards [Hall,A.ae_injective_root_slice_of_ae_free μ hfree] with s hs hi
  have HW (m : ℕ) : ∀ᵐ t ∂(A.leafMeasure R μ s).restrict (rootLeafWindow R m),
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (A.leafMeasure R μ s) t := by
    obtain ⟨B,hBC,hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
    exact hs m ⟨B,hBC⟩ hsB
  have HH := (ae_restrict_iUnion_iff (μ := A.leafMeasure R μ s) (rootLeafWindow R) _).mpr HW
  simpa only [rootLeafWindow_cover,Measure.restrict_univ] using HH

lemma ae_basedLeaf_rebase (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ᵐ t ∂A.basedLeaf R μ z,
      intrinsicRootLeaf hij μ (rightAction (rootQuotientParametrization hij z)
        (Matrix.SpecialLinearGroup.transvection hij t)) = basedRealMeasure (A.basedLeaf R μ z) t := by
  have H := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_intrinsic R hAR μ hfree)
  have HL := ae_of_ae_map measurable_fst.aemeasurable
    ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun _ h => h.1)
  filter_upwards [H,HL,A.ae_leafMeasure_ball_pos R hAR μ hfree] with z hz hlf hp
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hlf
  apply Measure.ae_smul_measure
  apply (Homeomorph.subRight z.2).measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hz] with t ht
  change intrinsicRootLeaf hij μ (rightAction (rootQuotientParametrization hij z)
    (Matrix.SpecialLinearGroup.transvection hij (t-z.2))) =
      basedRealMeasure (basedRealMeasure (A.leafMeasure R μ z.1) z.2) (t-z.2)
  rw [←rootQuotientParametrization_add,basedRealMeasure_rebase _ _ _ (hp 1 zero_lt_one),←add_sub_assoc,add_sub_cancel_left]
  exact ht

end RootBox

 

theorem ae_intrinsicRootLeaf_rebase {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ x) t := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H (B : boundedRootAtlas hij) : ∀ᵐ x ∂μ.restrict B.val.box.range,
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          basedRealMeasure (intrinsicRootLeaf hij μ x) t := by
    apply B.val.box.ae_of_coordinate μ
    filter_upwards [B.val.box.ae_intrinsicRootLeaf_coordinates B.val.radius B.val.time_bound μ hfree,
      B.val.box.ae_basedLeaf_rebase B.val.radius B.val.time_bound μ hfree] with z he hz
    rwa [he]
  have HH := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr H
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using HH

end PrimeDegreePackets

open scoped Topology ENNReal

open scoped Matrix Topology ENNReal ProbabilityTheory
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space
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

theorem exists_compact_continuous_rootLeafData
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (N : Set (X n)) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ K : Set (X n), IsCompact K ∧ K ⊆ Nᶜ ∧ μ Kᶜ < ε ∧
      ContinuousOn (intrinsicLeafData hij μ hfree) K ∧
      ∀ x ∈ K, intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x := by
  obtain ⟨E, hbad, hE, hEzero⟩ := exists_measurable_superset_of_null
    (ae_iff.mp (ae_intrinsicRootKernel_eq hij μ hfree))
  obtain ⟨K, hK, hKN, hsmall, hcont⟩ := exists_compact_continuousOn_metrizable
    μ (intrinsicLeafData hij μ hfree) (measurable_intrinsicLeafData hij μ hfree)
    (N ∪ E) (hN.union hE) (measure_union_null hNzero hEzero) ε hε
  refine ⟨K, hK, fun x hx => fun h => hKN hx (Or.inl h), hsmall, hcont, ?_⟩
  intro x hx
  by_contra h
  exact hKN hx (Or.inr (hbad h))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafSmallRadius
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform small-radius control of nonatomic root leaves

The set denoted `X_ρ` in EKL (2006), Section 4.3, can have arbitrarily
large measure. The proof uses continuity from above twice: first on each
locally finite leaf, and then on the decreasing sets of bad base points.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma exists_small_ball_mass_of_zero_atom (ν : Measure ℝ)
    (hfinite : ν (Metric.ball 0 1) ≠ ∞) (hzero : ν {0} = 0)
    (c : ℝ≥0∞) (hc : 0 < c) :
    ∃ m : ℕ, ν (Metric.ball 0 ((m + 1 : ℝ)⁻¹)) < c := by
  have hanti : Antitone (fun m : ℕ => Metric.ball (0 : ℝ) ((m + 1 : ℝ)⁻¹)) := by
    intro a b hab
    apply Metric.ball_subset_ball
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  have hmass : (⨅ m : ℕ, ν (Metric.ball 0 ((m + 1 : ℝ)⁻¹))) = 0 := by
    rw [← hanti.measure_iInter
      (fun _ => Metric.isOpen_ball.measurableSet.nullMeasurableSet)
      ⟨0, by simpa using hfinite⟩, real_iInter_ball_inv_nat, hzero]
  by_contra h
  push Not at h
  have : c ≤ 0 := hmass ▸ le_iInf h
  exact hc.not_ge this

/-- One radius works outside an arbitrarily small set of base points. -/
theorem exists_uniform_small_kernel_ball
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y ℝ)
    (hfinite : ∀ᵐ x ∂μ, κ x (Metric.ball 0 1) ≠ ∞)
    (hzero : ∀ᵐ x ∂μ, κ x {0} = 0)
    (c ε : ℝ≥0∞) (hc : 0 < c) (hε : ε ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 2 ∧
      μ {x | c ≤ κ x (Metric.ball 0 ρ)} < ε := by
  let B : ℕ → Set Y := fun m => {x | c ≤ κ x (Metric.ball 0 ((m + 1 : ℝ)⁻¹))}
  have hBmeas (m : ℕ) : MeasurableSet (B m) :=
    measurableSet_le measurable_const (κ.measurable_coe Metric.isOpen_ball.measurableSet)
  have hBanti : Antitone B := by
    intro a b hab x hx
    exact hx.trans (measure_mono (Metric.ball_subset_ball
      (inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1))))
  have hnull : μ (⋂ m, B m) = 0 := by
    have hae : ∀ᵐ x ∂μ, x ∉ ⋂ m, B m := by
      filter_upwards [hfinite, hzero] with x hxfinite hxzero
      obtain ⟨m, hm⟩ := exists_small_ball_mass_of_zero_atom (κ x) hxfinite hxzero c hc
      intro hx
      exact hm.not_ge (mem_iInter.mp hx m)
    simpa only [not_not, ofPred_mem_eq] using ae_iff.mp hae
  have hmass : (⨅ m, μ (B m)) = 0 := by
    rw [← hBanti.measure_iInter (fun m => (hBmeas m).nullMeasurableSet)
      ⟨0, measure_ne_top μ _⟩, hnull]
  have hex : ∃ m, μ (B m) < ε := by
    by_contra h
    push Not at h
    have : ε ≤ 0 := hmass ▸ le_iInf h
    exact hε (le_antisymm this bot_le)
  obtain ⟨m, hm⟩ := hex
  refine ⟨(m + 3 : ℝ)⁻¹, by positivity, ?_, ?_⟩
  · rw [inv_lt_comm₀ (by positivity) (by positivity)]
    norm_num
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · apply lt_of_le_of_lt (measure_mono ?_) hm
    intro x hx
    change c ≤ κ x (Metric.ball 0 ((m + 1 : ℝ)⁻¹))
    change c ≤ κ x (Metric.ball 0 ((m + 3 : ℝ)⁻¹)) at hx
    apply hx.trans
    apply measure_mono
    apply Metric.ball_subset_ball
    exact inv_anti₀ (by positivity) (by linarith)

/-- The uniform-radius set for the actual intrinsic root leaves. -/
theorem exists_uniform_small_rootLeaf_ball
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hnontrivial : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0)
    (c ε : ℝ≥0∞) (hc : 0 < c) (hε : ε ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 2 ∧
      μ {x | c ≤ intrinsicRootLeaf hij μ x (Metric.ball 0 ρ)} < ε := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  have heq : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x :=
    ae_intrinsicRootKernel_eq hij μ hfree
  have hzero : ∀ᵐ x ∂μ, κ x {0} = 0 := by
    filter_upwards [heq, hnontrivial,
      ae_intrinsicRootLeaf_zero_atom_or_trivial d hij μ hA] with x hx hn hz
    rw [hx]
    exact hz.resolve_right hn
  obtain ⟨ρ, hρ, hρhalf, hsmall⟩ := exists_uniform_small_kernel_ball μ κ
    (Filter.Eventually.of_forall fun x => measure_ball_lt_top.ne) hzero c ε hc hε
  refine ⟨ρ, hρ, hρhalf, ?_⟩
  have hcongr : {x | c ≤ intrinsicRootLeaf hij μ x (Metric.ball 0 ρ)} =ᵐ[μ]
      {x | c ≤ κ x (Metric.ball 0 ρ)} := by
    filter_upwards [heq] with x hx
    change (c ≤ intrinsicRootLeaf hij μ x (Metric.ball 0 ρ)) = (c ≤ κ x (Metric.ball 0 ρ))
    simp only [hx]
  rwa [measure_congr hcongr]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A covering estimate for leafwise bad sets

The relative maximal estimate used in EKL (2006), Section 4.3, rests on
the one-dimensional Besicovitch covering theorem. We first prove the
estimate for an arbitrary bounded family of witnessing radii. The measure
on the line is arbitrary; no doubling property is used.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree

theorem real_ball_covering_estimate
    {N : ℕ} {τ : ℝ} (hτ : 1 < τ)
    (hN : IsEmpty (Besicovitch.SatelliteConfig ℝ N τ))
    (ν : Measure ℝ) (E : Set ℝ) (hE : MeasurableSet E)
    (c : ℝ≥0∞) (S : Set ℝ) (r : S → ℝ) (R : ℝ)
    (hrpos : ∀ x, 0 < r x) (hrle : ∀ x, r x ≤ R)
    (hbad : ∀ x : S, c * ν (closedBall x (r x)) ≤ ν (E ∩ closedBall x (r x))) :
    c * ν S ≤ (N : ℝ≥0∞) * ν E := by
  let q : Besicovitch.BallPackage S ℝ :=
    ⟨Subtype.val, r, hrpos, R, hrle⟩
  obtain ⟨F, hdisj, hcover⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
  have hcount (i : Fin N) : (F i).Countable := by
    apply (hdisj i).countable_of_nonempty_interior
    intro x hx
    exact ⟨x, (ball_subset_interior_closedBall (ε := r x)) (mem_ball_self (hrpos x))⟩
  have hcover' : S ⊆ ⋃ i : Fin N, ⋃ x ∈ F i, closedBall (x : ℝ) (r x) := by
    intro x hx
    have h := hcover ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    obtain ⟨y, hy⟩ := mem_iUnion.mp hi
    obtain ⟨hyF, hyball⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨y,
      mem_iUnion.mpr ⟨hyF, ball_subset_closedBall hyball⟩⟩⟩
  have hfamily (i : Fin N) :
      c * ν (⋃ x ∈ F i, closedBall (x : ℝ) (r x)) ≤ ν E := by
    calc
      c * ν (⋃ x ∈ F i, closedBall (x : ℝ) (r x))
          ≤ c * ∑' x : F i, ν (closedBall ((x : S) : ℝ) (r x)) :=
        mul_le_mul' le_rfl (measure_biUnion_le ν (hcount i) _)
      _ = ∑' x : F i, c * ν (closedBall ((x : S) : ℝ) (r x)) :=
        (ENNReal.tsum_mul_left).symm
      _ ≤ ∑' x : F i, ν (E ∩ closedBall ((x : S) : ℝ) (r x)) :=
        ENNReal.tsum_le_tsum fun x => hbad x
      _ = ν (⋃ x ∈ F i, E ∩ closedBall (x : ℝ) (r x)) := by
        symm
        apply measure_biUnion (hcount i)
        · exact (hdisj i).mono fun _ => inter_subset_right
        · intro x hx
          exact hE.inter isClosed_closedBall.measurableSet
      _ ≤ ν E := measure_mono (by
        intro x hx
        obtain ⟨y, hy⟩ := mem_iUnion.mp hx
        obtain ⟨_, hxy⟩ := mem_iUnion.mp hy
        exact hxy.1)
  calc
    c * ν S ≤ c * ν (⋃ i : Fin N, ⋃ x ∈ F i, closedBall (x : ℝ) (r x)) :=
      mul_le_mul' le_rfl (measure_mono hcover')
    _ ≤ c * ∑ i : Fin N, ν (⋃ x ∈ F i, closedBall (x : ℝ) (r x)) :=
      mul_le_mul' le_rfl (measure_iUnion_fintype_le ν _)
    _ = ∑ i : Fin N, c * ν (⋃ x ∈ F i, closedBall (x : ℝ) (r x)) :=
      Finset.mul_sum ..
    _ ≤ ∑ _i : Fin N, ν E := Finset.sum_le_sum fun i _ => hfamily i
    _ = (N : ℝ≥0∞) * ν E := by simp

/-- A single finite constant controls every bounded-radius relative
maximal set on a real leaf, uniformly in the leaf measure. -/
theorem exists_real_relative_maximal_constant :
    ∃ N : ℕ, ∀ (ν : Measure ℝ) (E : Set ℝ), MeasurableSet E →
      ∀ (c : ℝ≥0∞) (R : ℝ),
      c * ν {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
        c * ν (closedBall x r) ≤ ν (E ∩ closedBall x r)} ≤ (N : ℝ≥0∞) * ν E := by
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := ℝ)
  refine ⟨N, ?_⟩
  intro ν E hE c R
  let S := {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
    c * ν (closedBall x r) ≤ ν (E ∩ closedBall x r)}
  choose r hr using fun x : S => x.property
  exact real_ball_covering_estimate hτ hN ν E hE c S r R
    (fun x => (hr x).1) (fun x => (hr x).2.1) (fun x => (hr x).2.2)

/-- The same constant controls all radii. Continuity from below holds
for arbitrary increasing sets, so no measurability of the supremum over
the radius parameter has to be assumed. -/
theorem exists_real_relative_maximal_constant_all_radii :
    ∃ N : ℕ, ∀ (ν : Measure ℝ) (E : Set ℝ), MeasurableSet E →
      ∀ c : ℝ≥0∞,
      c * ν {x | ∃ r : ℝ, 0 < r ∧
        c * ν (closedBall x r) ≤ ν (E ∩ closedBall x r)} ≤ (N : ℝ≥0∞) * ν E := by
  obtain ⟨N, hN⟩ := exists_real_relative_maximal_constant
  refine ⟨N, ?_⟩
  intro ν E hE c
  let B : ℕ → Set ℝ := fun m => {x | ∃ r : ℝ, 0 < r ∧ r ≤ (m + 1 : ℝ) ∧
    c * ν (closedBall x r) ≤ ν (E ∩ closedBall x r)}
  have hmono : Monotone B := by
    intro a b hab x hx
    obtain ⟨r, hr, hra, hmass⟩ := hx
    exact ⟨r, hr, hra.trans (by exact_mod_cast Nat.add_le_add_right hab 1), hmass⟩
  have hunion : {x | ∃ r : ℝ, 0 < r ∧
      c * ν (closedBall x r) ≤ ν (E ∩ closedBall x r)} = ⋃ m, B m := by
    ext x
    constructor
    · rintro ⟨r, hr, hmass⟩
      obtain ⟨m, hm⟩ := exists_nat_gt r
      exact mem_iUnion.mpr ⟨m, r, hr, by linarith, hmass⟩
    · intro hx
      obtain ⟨m, r, hr, _, hmass⟩ := mem_iUnion.mp hx
      exact ⟨r, hr, hmass⟩
  rw [hunion, hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun m => hN ν E hE c (m + 1)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafMaximalDisintegration
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Disintegrating the relative leaf maximal estimate

The real-line estimate is integrated against the transverse measure.
This gives the relative maximal bound in an actual root box, using its
conditional kernel and the original ambient measure.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem relative_maximal_compProd_bound
    {Y : Type*} [MeasurableSpace Y] (N : ℕ)
    (hN : ∀ (ν : Measure ℝ) (E : Set ℝ), MeasurableSet E → ∀ c : ℝ≥0∞,
      c * ν {x | ∃ r : ℝ, 0 < r ∧
        c * ν (closedBall x r) ≤ ν (E ∩ closedBall x r)} ≤ (N : ℝ≥0∞) * ν E)
    (μ : Measure Y) [SFinite μ] (κ : Kernel Y ℝ) [IsSFiniteKernel κ]
    (B E : Set (Y × ℝ)) (hB : MeasurableSet B) (hE : MeasurableSet E)
    (c : ℝ≥0∞)
    (hbad : ∀ᵐ y ∂μ, ∀ᵐ t ∂κ y, (y, t) ∈ B → ∃ r : ℝ, 0 < r ∧
      c * κ y (closedBall t r) ≤ κ y ((Prod.mk y ⁻¹' E) ∩ closedBall t r)) :
    c * (μ ⊗ₘ κ) B ≤ (N : ℝ≥0∞) * (μ ⊗ₘ κ) E := by
  rw [Measure.compProd_apply hB, Measure.compProd_apply hE,
    ← lintegral_const_mul c (Kernel.measurable_kernel_prodMk_left hB),
    ← lintegral_const_mul (N : ℝ≥0∞) (Kernel.measurable_kernel_prodMk_left hE)]
  apply lintegral_mono_ae
  filter_upwards [hbad] with y hy
  exact (mul_le_mul' le_rfl (measure_mono_ae hy)).trans
    (hN (κ y) (Prod.mk y ⁻¹' E) (hE.preimage (measurable_const.prodMk measurable_id)) c)

/-- The Besicovitch constant remains uniform after integrating along
the actual conditional distributions in any root box. -/
theorem exists_rootBox_relative_maximal_constant :
    ∃ N : ℕ, ∀ {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
      (A : RootBox hij k) (μ : Measure (X n)) [IsFiniteMeasure μ]
      (B E : Set (X n)), MeasurableSet B → MeasurableSet E → ∀ c : ℝ≥0∞,
      (∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.conditionalKernel μ s,
        rootQuotientParametrization hij (s, t) ∈ B → ∃ r : ℝ, 0 < r ∧
        c * A.conditionalKernel μ s (closedBall t r) ≤
          A.conditionalKernel μ s
            ({u | rootQuotientParametrization hij (s, u) ∈ E} ∩ closedBall t r)) →
      c * (μ.restrict A.range) B ≤ (N : ℝ≥0∞) * (μ.restrict A.range) E := by
  obtain ⟨N, hN⟩ := exists_real_relative_maximal_constant_all_radii
  refine ⟨N, ?_⟩
  intro n i j k hij A μ _ B E hB hE c hbad
  have hparam : Measurable (rootQuotientParametrization (k := k) hij) :=
    (rootQuotientParametrization_localHomeomorph hij).continuous.measurable
  have hbound := relative_maximal_compProd_bound N hN (A.coordinateMeasure μ).fst
    (A.conditionalKernel μ)
    (rootQuotientParametrization hij ⁻¹' B) (rootQuotientParametrization hij ⁻¹' E)
    (hB.preimage hparam) (hE.preimage hparam) c hbad
  rw [← Measure.map_apply hparam hB, ← Measure.map_apply hparam hE,
    A.disintegrate μ] at hbound
  exact hbound

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafMaximalIntrinsic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Relative maximal estimates for intrinsic leaves in a root box

Normalization does not change a relative mass inequality. On an interval
contained in a root box, the intrinsic leaf therefore gives the same
relative bound as the box's conditional probability measure.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma basedRealMeasure_translate_apply (ν : Measure ℝ) (t : ℝ)
    (S : Set ℝ) (hS : MeasurableSet S) :
    basedRealMeasure ν t ((fun u : ℝ => t + u) ⁻¹' S) =
      (ν (ball t 1))⁻¹ * ν S := by
  change (centerRealMeasure ν t (ball 0 1))⁻¹ *
    centerRealMeasure ν t ((fun u : ℝ => t + u) ⁻¹' S) = _
  have hpre : MeasurableSet ((fun u : ℝ => t + u) ⁻¹' S) :=
    hS.preimage (show Measurable (fun u : ℝ => t + u) by fun_prop)
  rw [centerRealMeasure_ball, centerRealMeasure,
    Measure.map_apply (Homeomorph.subRight t).measurable hpre]
  have he : (Homeomorph.subRight t) ⁻¹' ((fun u : ℝ => t + u) ⁻¹' S) = S := by
    ext u
    change (t + (u - t) ∈ S ↔ u ∈ S)
    rw [show t + (u - t) = u by ring]
  rw [he]

lemma smul_relative_mass_iff (ν : Measure ℝ) (a c : ℝ≥0∞)
    (ha : a ≠ 0) (haTop : a ≠ ∞) (S T : Set ℝ) :
    c * (a * ν S) ≤ a * ν T ↔ c * ν S ≤ ν T := by
  constructor
  · intro h
    have hh := mul_le_mul' (le_refl a⁻¹) h
    simpa only [mul_left_comm a⁻¹ c, ← mul_assoc a⁻¹ a,
      ENNReal.inv_mul_cancel ha haTop, one_mul] using hh
  · intro h
    have hh := mul_le_mul' (le_refl a) h
    simpa only [mul_left_comm a c] using hh

lemma basedRealMeasure_relative_mass_iff (ν : Measure ℝ)
    [IsLocallyFiniteMeasure ν] (t : ℝ) (ht : 0 < ν (ball t 1))
    (c : ℝ≥0∞) (S T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    c * basedRealMeasure ν t ((fun u : ℝ => t + u) ⁻¹' S) ≤
      basedRealMeasure ν t ((fun u : ℝ => t + u) ⁻¹' T) ↔ c * ν S ≤ ν T := by
  rw [basedRealMeasure_translate_apply ν t S hS,
    basedRealMeasure_translate_apply ν t T hT]
  exact smul_relative_mass_iff ν _ c (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    (ENNReal.inv_ne_top.mpr ht.ne') S T

lemma preimage_add_closedBall (t r : ℝ) :
    (fun u : ℝ => t + u) ⁻¹' closedBall t r = closedBall 0 r := by
  ext u
  simp only [mem_preimage, mem_closedBall, Real.dist_eq, add_sub_cancel_left, sub_zero]

/-- If an intrinsic bad interval stays inside the root box, its
relative mass inequality passes to the actual conditional kernel. -/
lemma intrinsic_bad_interval_to_conditional
    {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (A : RootBox hij k) (R : ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : RootSlice i j k) (t r : ℝ) (E : Set (X n)) (hE : MeasurableSet E)
    (hs : A.IsNormalizedRootLeaf R μ s (A.leafMeasure R μ s))
    (ht : 0 < A.leafMeasure R μ s (ball t 1))
    (heq : intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s, t)) =
      A.basedLeaf R μ (s, t))
    (hr : closedBall t r ⊆ A.time) (c : ℝ≥0∞)
    (hbad : c * intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s, t))
        (closedBall 0 r) ≤
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s, t))
        ({u | rightAction (rootQuotientParametrization hij (s, t))
          (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩ closedBall 0 r)) :
    c * A.conditionalKernel μ s (closedBall t r) ≤
      A.conditionalKernel μ s
        ({u | rootQuotientParametrization hij (s, u) ∈ E} ∩ closedBall t r) := by
  let ν := A.leafMeasure R μ s
  let : IsLocallyFiniteMeasure ν := hs.1
  let F : Set ℝ := {u | rootQuotientParametrization hij (s, u) ∈ E}
  have hF : MeasurableSet F := hE.preimage
    ((rootQuotientParametrization_localHomeomorph hij).continuous.measurable.comp
      (measurable_const.prodMk measurable_id))
  have htranslate : (fun u : ℝ => t + u) ⁻¹' (F ∩ closedBall t r) =
      {u | rightAction (rootQuotientParametrization hij (s, t))
        (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩ closedBall 0 r := by
    rw [preimage_inter, preimage_add_closedBall]
    congr 1
    ext u
    simp only [mem_preimage, mem_ofPred_eq, F, rootQuotientParametrization_add]
  have hmass : c * ν (closedBall t r) ≤ ν (F ∩ closedBall t r) := by
    apply (basedRealMeasure_relative_mass_iff ν t ht c _ _
      isClosed_closedBall.measurableSet (hF.inter isClosed_closedBall.measurableSet)).mp
    rw [preimage_add_closedBall, htranslate]
    simpa only [heq, RootBox.basedLeaf] using hbad
  have hcond := hs.2.2.1
  rw [← hcond, Measure.restrict_apply isClosed_closedBall.measurableSet,
    Measure.restrict_apply (hF.inter isClosed_closedBall.measurableSet),
    inter_eq_left.mpr hr, inter_eq_left.mpr (inter_subset_right.trans hr)]
  exact hmass

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafBoxMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Intrinsic leaf maximal inequality inside root boxes

A measurable set of points witnessing a bad intrinsic leaf interval has
small ambient measure, provided the witnessing interval stays in the
root box. The constant is independent of the box and ambient measure.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_intrinsic_rootBox_maximal_constant :
    ∃ N : ℕ, ∀ {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
      (A : RootBox hij k) (R : ℝ), A.time ⊆ rootLeafWindow R 0 →
      ∀ (μ : Measure (X n)) [IsFiniteMeasure μ],
      (∀ᵐ x ∂μ, ∀ v : ℝ,
        rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) →
      ∀ (B E : Set (X n)), MeasurableSet B → MeasurableSet E → ∀ c : ℝ≥0∞,
      (∀ᵐ z ∂A.coordinateMeasure μ,
        rootQuotientParametrization hij z ∈ B → ∃ r : ℝ, 0 < r ∧
        closedBall z.2 r ⊆ A.time ∧
        c * intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) (closedBall 0 r) ≤
          intrinsicRootLeaf hij μ (rootQuotientParametrization hij z)
            ({u | rightAction (rootQuotientParametrization hij z)
              (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩ closedBall 0 r)) →
      c * (μ.restrict A.range) B ≤ (N : ℝ≥0∞) * (μ.restrict A.range) E := by
  obtain ⟨N, hN⟩ := exists_rootBox_relative_maximal_constant
  refine ⟨N, ?_⟩
  intro n i j k hij A R hAR μ _ hfree B E hB hE c hbad
  apply hN hij A μ B E hB hE c
  have hspec : ∀ᵐ z ∂A.coordinateMeasure μ,
      A.IsNormalizedRootLeaf R μ z.1 (A.leafMeasure R μ z.1) :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_spec R hAR μ hfree)
  have hall : ∀ᵐ z ∂A.coordinateMeasure μ,
      rootQuotientParametrization hij z ∈ B → ∃ r : ℝ, 0 < r ∧
      c * A.conditionalKernel μ z.1 (closedBall z.2 r) ≤
        A.conditionalKernel μ z.1
          ({u | rootQuotientParametrization hij (z.1, u) ∈ E} ∩ closedBall z.2 r) := by
    filter_upwards [hbad, hspec, A.ae_leafMeasure_ball_pos R hAR μ hfree,
      A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree] with z hz hs hp he
    intro hx
    obtain ⟨r, hr, hinside, hmass⟩ := hz hx
    exact ⟨r, hr, intrinsic_bad_interval_to_conditional hij A R μ z.1 z.2 r E hE
      hs (hp 1 zero_lt_one) he hinside c hmass⟩
  have hh : (A.coordinateMeasure μ).fst ⊗ₘ A.conditionalKernel μ = A.coordinateMeasure μ := by
    change (A.coordinateMeasure μ).fst ⊗ₘ (A.coordinateMeasure μ).condKernel = _
    exact Measure.disintegrate _ _
  rw [← hh] at hall
  exact Measure.ae_ae_of_ae_compProd hall

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootBoxMargins
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root boxes with a uniform interval margin

Every point has a smaller open root box for which a fixed positive time
interval stays inside a larger root box. Compactness makes these margins
uniform on any prescribed compact set.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_bufferedRootBox_at {n : ℕ} {i j : Fin n} (hij : i ≠ j) (x : X n) :
    ∃ A : BufferedRootBox hij, x ∈ A.core := by
  obtain ⟨A, hx⟩ := exists_boundedRootBox_at hij x
  obtain ⟨z, hz⟩ := hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp A.box.time_open z.val.2 z.property.2
  have hsmall : ball z.val.2 (ε / 2) ⊆ A.box.time := by
    apply (ball_subset_ball (by linarith : ε / 2 ≤ ε)).trans hball
  let B := A.box.shrink A.box.transverse (ball z.val.2 (ε / 2))
    A.box.transverse_open isOpen_ball subset_rfl hsmall
  have hsub : B.range ⊆ A.box.range := by
    rintro y ⟨w, rfl⟩
    exact ⟨⟨w.val, w.property.1, hsmall w.property.2⟩, rfl⟩
  refine ⟨⟨A.pivot, A.box, A.radius, A.time_bound, B.range, B.range_open,
    hsub, ε / 4, by positivity, ?_⟩, ?_⟩
  · intro w hw hwB v hv
    obtain ⟨u, hu⟩ := hwB
    have he : (⟨u.val, u.property.1, hsmall u.property.2⟩ : A.box.domain) = ⟨w, hw⟩ :=
      A.box.embedding.injective hu
    have huw : u.val = w := congrArg Subtype.val he
    have hwclose : dist w.2 z.val.2 < ε / 2 := by
      simpa only [huw] using (show dist u.val.2 z.val.2 < ε / 2 from u.property.2)
    apply hball
    have hvclose : dist v w.2 ≤ ε / 4 := hv
    have hd := dist_triangle v w.2 z.val.2
    change dist v z.val.2 < ε
    linarith
  · exact ⟨⟨z.val, z.property.1, mem_ball_self (by positivity)⟩, hz⟩

theorem compact_bufferedRootBox_cover {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (K : Set (X n)) (hK : IsCompact K) :
    ∃ (F : Finset (BufferedRootBox hij)) (δ : ℝ), 0 < δ ∧
      K ⊆ ⋃ A ∈ F, A.core ∧ ∀ A ∈ F, δ ≤ A.margin := by
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun A : BufferedRootBox hij => A.core)
    (fun A => A.core_open) (by
      intro x _
      obtain ⟨A, hx⟩ := exists_bufferedRootBox_at hij x
      exact mem_iUnion.mpr ⟨A, hx⟩)
  by_cases hne : F.Nonempty
  · refine ⟨F, F.inf' hne BufferedRootBox.margin, ?_, hF, ?_⟩
    · exact (Finset.lt_inf'_iff hne).mpr fun A _ => A.margin_pos
    · intro A hA
      exact Finset.inf'_le _ hA
  · refine ⟨F, 1, zero_lt_one, hF, ?_⟩
    intro A hA
    exact (hne ⟨A, hA⟩).elim

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafCompactMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform short-interval maximal estimates on compact sets

The root-box estimate and a finite cover of a compact set give one
positive radius and one finite constant, uniformly over all finite
ambient measures with essentially free root action.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem compact_intrinsic_maximal_bound
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (K : Set (X n)) (hK : IsCompact K) :
    ∃ (M : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ (μ : Measure (X n)) [IsFiniteMeasure μ],
      (∀ᵐ x ∂μ, ∀ v : ℝ,
        rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) →
      ∀ (B E : Set (X n)), MeasurableSet B → MeasurableSet E → B ⊆ K →
      ∀ c : ℝ≥0∞,
      (∀ᵐ x ∂μ, x ∈ B → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
        c * intrinsicRootLeaf hij μ x (closedBall 0 r) ≤
          intrinsicRootLeaf hij μ x
            ({u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩
              closedBall 0 r)) →
      c * μ B ≤ (M : ℝ≥0∞) * μ E := by
  obtain ⟨N, hN⟩ := exists_intrinsic_rootBox_maximal_constant
  obtain ⟨F, δ, hδ, hcover, hmargin⟩ := compact_bufferedRootBox_cover hij K hK
  refine ⟨F.card * N, δ, hδ, ?_⟩
  intro μ _ hfree B E hB hE hBK c hbad
  have hlocal (A : BufferedRootBox hij) (hAF : A ∈ F) :
      c * μ (B ∩ A.core) ≤ (N : ℝ≥0∞) * μ E := by
    have hBC := hB.inter A.core_open.measurableSet
    have hparam : Measurable (rootQuotientParametrization (k := A.pivot) hij) :=
      (rootQuotientParametrization_localHomeomorph hij).continuous.measurable
    have hbadcoord : ∀ᵐ z ∂A.box.coordinateMeasure μ,
        rootQuotientParametrization hij z ∈ B → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
        c * intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) (closedBall 0 r) ≤
          intrinsicRootLeaf hij μ (rootQuotientParametrization hij z)
            ({u | rightAction (rootQuotientParametrization hij z)
              (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩ closedBall 0 r) := by
      have hmap := ae_restrict_of_ae (s := A.box.range) hbad
      rw [← A.box.map_coordinateMeasure μ] at hmap
      exact ae_of_ae_map hparam.aemeasurable hmap
    have hbound := hN hij A.box A.radius A.time_bound μ hfree (B ∩ A.core) E hBC hE c (by
      filter_upwards [hbadcoord, A.box.coordinateMeasure_ae_domain μ] with z hz hzd
      intro hx
      obtain ⟨r, hr, hrδ, hmass⟩ := hz hx.1
      exact ⟨r, hr, (closedBall_subset_closedBall (hrδ.trans (hmargin A hAF))).trans
        (A.time_margin z hzd hx.2), hmass⟩)
    rw [Measure.restrict_apply hBC,
      inter_eq_left.mpr (inter_subset_right.trans A.core_subset), Measure.restrict_apply hE] at hbound
    exact hbound.trans (mul_le_mul' le_rfl (measure_mono inter_subset_left))
  have hBcover : B ⊆ ⋃ A ∈ F, B ∩ A.core := by
    intro x hx
    obtain ⟨A, hA⟩ := mem_iUnion.mp (hcover (hBK hx))
    obtain ⟨hAF, hxA⟩ := mem_iUnion.mp hA
    exact mem_iUnion.mpr ⟨A, mem_iUnion.mpr ⟨hAF, hx, hxA⟩⟩
  calc
    c * μ B ≤ c * μ (⋃ A ∈ F, B ∩ A.core) := mul_le_mul' le_rfl (measure_mono hBcover)
    _ ≤ c * ∑ A ∈ F, μ (B ∩ A.core) :=
      mul_le_mul' le_rfl (measure_biUnion_finset_le F _)
    _ = ∑ A ∈ F, c * μ (B ∩ A.core) := Finset.mul_sum ..
    _ ≤ ∑ _A ∈ F, (N : ℝ≥0∞) * μ E := Finset.sum_le_sum fun A hAF => hlocal A hAF
    _ = (↑(F.card * N) : ℝ≥0∞) * μ E := by simp [nsmul_eq_mul, mul_assoc]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafShortMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Short-interval maximal control with a small exceptional set

Inner regularity and the compact-set estimate give uniform relative
maximal control at sufficiently short times. The error is the measure
of the complement of a large compact set.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem short_interval_intrinsic_maximal_bound
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ (M : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ (B E : Set (X n)), MeasurableSet B → MeasurableSet E → ∀ c : ℝ≥0∞,
      (∀ᵐ x ∂μ, x ∈ B → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
        c * intrinsicRootLeaf hij μ x (closedBall 0 r) ≤
          intrinsicRootLeaf hij μ x
            ({u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩
              closedBall 0 r)) →
      c * μ B ≤ (M : ℝ≥0∞) * μ E + c * ε := by
  obtain ⟨K, _, hK, hsmall⟩ := MeasurableSet.univ.exists_isCompact_sdiff_lt
    (μ := μ) (measure_ne_top μ univ) hε
  have hKsmall : μ Kᶜ < ε := by simpa only [← compl_eq_univ_sdiff] using hsmall
  obtain ⟨M, δ, hδ, hbound⟩ := compact_intrinsic_maximal_bound hij K hK
  refine ⟨M, δ, hδ, ?_⟩
  intro B E hB hE c hbad
  have hbadK : ∀ᵐ x ∂μ, x ∈ B ∩ K → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
      c * intrinsicRootLeaf hij μ x (closedBall 0 r) ≤
        intrinsicRootLeaf hij μ x
          ({u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩
            closedBall 0 r) := hbad.mono fun _ hx h => hx h.1
  have hBK := hbound μ hfree (B ∩ K) E (hB.inter hK.measurableSet) hE
    inter_subset_right c hbadK
  calc
    c * μ B ≤ c * (μ (B ∩ K) + μ Kᶜ) := mul_le_mul' le_rfl
      ((measure_mono (show B ⊆ (B ∩ K) ∪ Kᶜ by intro x hx; by_cases h : x ∈ K <;> tauto)).trans
        (measure_union_le _ _))
    _ = c * μ (B ∩ K) + c * μ Kᶜ := mul_add ..
    _ ≤ (M : ℝ≥0∞) * μ E + c * ε :=
      add_le_add hBK (mul_le_mul' le_rfl hKsmall.le)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafMaximalScaling
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scaling relative bad intervals by the diagonal action

The actual canonical diagonal flow rescales root time by its exponential.
Transport and projective normalization preserve every relative mass
inequality used in the leafwise maximal argument.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_map_image_relative_bound (ν : Measure ℝ) (e : ℝ ≃ₜ ℝ)
    (J S T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (c : ℝ≥0∞) (h : c * ν S ≤ ν T) :
    c * anchorNormalize (ν.map e) J (e '' S) ≤
      anchorNormalize (ν.map e) J (e '' T) := by
  have hmap (U : Set ℝ) (hU : MeasurableSet U) : (ν.map e) (e '' U) = ν U := by
    rw [Measure.map_apply e.measurable
      (e.isOpenEmbedding.measurableEmbedding.measurableSet_image.mpr hU),
      e.injective.preimage_image]
  change c * ((ν.map e J)⁻¹ * ν.map e (e '' S)) ≤
    (ν.map e J)⁻¹ * ν.map e (e '' T)
  rw [hmap S hS, hmap T hT, mul_left_comm]
  exact mul_le_mul' le_rfl h

lemma scaling_image_closedBall_zero (a : ℝ) (ha : 0 < a) (r : ℝ) :
    (Homeomorph.mulLeft₀ a ha.ne') '' closedBall 0 r = closedBall 0 (a * r) := by
  let e := Homeomorph.mulLeft₀ a ha.ne'
  have hpre : e ⁻¹' closedBall 0 (a * r) = closedBall 0 r := by
    ext u
    simp only [mem_preimage, mem_closedBall, Real.dist_eq, sub_zero,
      e, Homeomorph.coe_mulLeft₀, abs_mul, abs_of_pos ha]
    exact mul_le_mul_iff_right₀ ha
  rw [← hpre]
  exact e.image_preimage _

lemma rootCanonicalFlow_rescales_time
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j) (t u : ℝ) (x : X (d + 1)) :
    rightAction (rightAction x (Matrix.SpecialLinearGroup.transvection hij u))
      (rootCanonicalFlow d j t) =
    rightAction (rightAction x (rootCanonicalFlow d j t))
      (Matrix.SpecialLinearGroup.transvection hij (Real.exp t * u)) := by
  let D := rootCanonicalFlow d j t
  have he : (rootCanonicalWeights d j i - rootCanonicalWeights d j j) * (-t) = t := by
    have hd := rootCanonicalWeights_difference d hij
    rw [show rootCanonicalWeights d j i - rootCanonicalWeights d j j = -1 by linarith]
    ring
  have hc : D⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * D =
      Matrix.SpecialLinearGroup.transvection hij (Real.exp t * u) := by
    simpa only [D, rootCanonicalFlow, diagonalOneParameter_neg, neg_neg, he] using
      diagonal_conjugation_transvection (rootCanonicalWeights d j)
        (rootCanonicalWeights_sum d j) hij u (-t)
  rw [rightAction_mul, rightAction_mul]
  congr 1
  calc
    Matrix.SpecialLinearGroup.transvection hij u * D =
        D * (D⁻¹ * Matrix.SpecialLinearGroup.transvection hij u * D) := by group
    _ = _ := by rw [hc]

/-- A bad interval is sent to a bad interval of exponentially rescaled
radius for the image set under the canonical diagonal flow. -/
theorem intrinsic_bad_interval_scale
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (x : X (d + 1)) (t r : ℝ) (E : Set (X (d + 1))) (hE : MeasurableSet E)
    (heq : intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t)) =
      anchorNormalize ((intrinsicRootLeaf hij μ x).map
        (Homeomorph.mulLeft₀ (Real.exp t) (Real.exp_ne_zero t))) (ball 0 1))
    (c : ℝ≥0∞)
    (hbad : c * intrinsicRootLeaf hij μ x (closedBall 0 r) ≤
      intrinsicRootLeaf hij μ x
        ({u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩
          closedBall 0 r)) :
    c * intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t))
        (closedBall 0 (Real.exp t * r)) ≤
      intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t))
        ({u | rightAction (rightAction x (rootCanonicalFlow d j t))
          (Matrix.SpecialLinearGroup.transvection hij u) ∈
            (rightActionHomeomorph (rootCanonicalFlow d j t)) '' E} ∩
          closedBall 0 (Real.exp t * r)) := by
  let e := Homeomorph.mulLeft₀ (Real.exp t) (Real.exp_ne_zero t)
  let f := rightActionHomeomorph (rootCanonicalFlow d j t)
  let S : Set ℝ := {u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E}
  let T : Set ℝ := {u | rightAction (f x) (Matrix.SpecialLinearGroup.transvection hij u) ∈ f '' E}
  have hS : MeasurableSet S := hE.preimage (by
    exact ((continuous_rightAction_uncurry (d + 1)).comp
      (continuous_const.prodMk (continuous_rootTransvection hij))).measurable)
  have hpre : e ⁻¹' T = S := by
    ext u
    change (rightAction (rightAction x (rootCanonicalFlow d j t))
      (Matrix.SpecialLinearGroup.transvection hij (Real.exp t * u)) ∈ f '' E) ↔ _
    rw [← rootCanonicalFlow_rescales_time]
    exact f.injective.mem_set_image
  have himage : e '' S = T := by rw [← hpre]; exact e.image_preimage _
  have h := normalized_map_image_relative_bound (intrinsicRootLeaf hij μ x) e (ball 0 1)
    (closedBall 0 r) (S ∩ closedBall 0 r) isClosed_closedBall.measurableSet
    (hS.inter isClosed_closedBall.measurableSet) c hbad
  rw [image_inter e.injective, himage,
    scaling_image_closedBall_zero (Real.exp t) (Real.exp_pos t) r] at h
  dsimp only [T] at h
  rw [show f x = rightAction x (rootCanonicalFlow d j t) from rfl] at h
  simpa only [e, ← heq] using h

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafBoundedMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A maximal bound uniform in the time window

Diagonal invariance rescales any bounded family of witnessing intervals
into the short-time estimate. Its constant is independent of the bound
on those intervals.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem bounded_interval_intrinsic_maximal_bound
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ M : ℕ, ∀ (R : ℝ) (B E : Set (X (d + 1))),
      MeasurableSet B → MeasurableSet E → ∀ c : ℝ≥0∞,
      (∀ᵐ x ∂μ, x ∈ B → ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
        c * intrinsicRootLeaf hij μ x (closedBall 0 r) ≤
          intrinsicRootLeaf hij μ x
            ({u | rightAction x (Matrix.SpecialLinearGroup.transvection hij u) ∈ E} ∩
              closedBall 0 r)) →
      c * μ B ≤ (M : ℝ≥0∞) * μ E + c * ε := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  obtain ⟨M, δ, hδ, hbound⟩ := short_interval_intrinsic_maximal_bound hij μ hfree ε hε
  refine ⟨M, ?_⟩
  intro R B E hB hE c hbad
  let q : ℝ := δ / (|R| + 1)
  have hq : 0 < q := div_pos hδ (by positivity)
  have hqR : q * R ≤ δ := by
    calc
      q * R ≤ q * (|R| + 1) := mul_le_mul_of_nonneg_left (by linarith [le_abs_self R]) hq.le
      _ = δ := div_mul_cancel₀ _ (by positivity)
  let t := Real.log q
  let f := rightActionHomeomorph (rootCanonicalFlow d j t)
  have hexp : Real.exp t = q := Real.exp_log hq
  have hfμ : MeasurePreserving f μ μ := rootCanonicalFlow_preserving d j t μ hA
  have hB' : MeasurableSet (f '' B) := f.isOpenEmbedding.measurableEmbedding.measurableSet_image.mpr hB
  have hE' : MeasurableSet (f '' E) := f.isOpenEmbedding.measurableEmbedding.measurableSet_image.mpr hE
  have hbase : ∀ᵐ x ∂μ, f x ∈ f '' B → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
      c * intrinsicRootLeaf hij μ (f x) (closedBall 0 r) ≤
        intrinsicRootLeaf hij μ (f x)
          ({u | rightAction (f x) (Matrix.SpecialLinearGroup.transvection hij u) ∈ f '' E} ∩
            closedBall 0 r) := by
    filter_upwards [hbad, ae_intrinsicRootLeaf_canonical d hij μ hA t] with x hx hcov
    intro hxB
    obtain ⟨r, hr, hrR, hmass⟩ := hx (f.injective.mem_set_image.mp hxB)
    refine ⟨q * r, mul_pos hq hr,
      (mul_le_mul_of_nonneg_left hrR hq.le).trans hqR, ?_⟩
    have H := intrinsic_bad_interval_scale d hij μ x t r E hE hcov c hmass
    rw [hexp, show rightAction x (rootCanonicalFlow d j t) = f x from rfl] at H
    exact H
  have hnew : ∀ᵐ y ∂μ, y ∈ f '' B → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
      c * intrinsicRootLeaf hij μ y (closedBall 0 r) ≤
        intrinsicRootLeaf hij μ y
          ({u | rightAction y (Matrix.SpecialLinearGroup.transvection hij u) ∈ f '' E} ∩
            closedBall 0 r) := by
    let P : X (d + 1) → Prop := fun y => y ∈ f '' B → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
      c * intrinsicRootLeaf hij μ y (closedBall 0 r) ≤
        intrinsicRootLeaf hij μ y
          ({u | rightAction y (Matrix.SpecialLinearGroup.transvection hij u) ∈ f '' E} ∩
            closedBall 0 r)
    have hb : ∀ᵐ x ∂μ, P (f x) := hbase
    have hmap : ∀ᵐ y ∂μ.map f, P y := f.isOpenEmbedding.measurableEmbedding.ae_map_iff.mpr hb
    simpa only [hfμ.map_eq] using hmap
  have hmeasure (S : Set (X (d + 1))) (hS : MeasurableSet S) : μ (f '' S) = μ S := by
    calc
      μ (f '' S) = (μ.map f) (f '' S) := by rw [hfμ.map_eq]
      _ = μ S := by
        rw [Measure.map_apply f.measurable
          (f.isOpenEmbedding.measurableEmbedding.measurableSet_image.mpr hS),
          f.injective.preimage_image]
  have H := hbound (f '' B) (f '' E) hB' hE' c hnew
  rwa [hmeasure B hB, hmeasure E hE] at H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafRationalRadii
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational radii determine relative leaf bounds

Continuity from above for locally finite real measures lets the
measurable, countable family of rational-radius inequalities control
every positive real radius.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree

lemma iInter_closedBall_of_antitone_tendsto (a : ℝ) (r : ℕ → ℝ)
    (hr : Antitone r) (hlim : Tendsto r atTop (𝓝 a)) :
    (⋂ m, closedBall (0 : ℝ) (r m)) = closedBall 0 a := by
  ext u
  simp only [mem_iInter, mem_closedBall]
  constructor
  · intro h
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall h)
  · intro h m
    exact h.trans (le_of_tendsto hlim (Filter.eventually_atTop.mpr
      ⟨m, fun n hn => hr hn⟩))

theorem relative_closedBall_bound_of_rational
    (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (E : Set ℝ) (hE : MeasurableSet E)
    (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hbound : ∀ q : ℚ, 0 < (q : ℝ) →
      ν (E ∩ closedBall 0 (q : ℝ)) ≤ c * ν (closedBall 0 (q : ℝ)))
    (r : ℝ) (hr : 0 < r) :
    ν (E ∩ closedBall 0 r) ≤ c * ν (closedBall 0 r) := by
  obtain ⟨q, hqanti, hqabove, hqlim⟩ := Rat.denseRange_cast.exists_seq_strictAnti_tendsto
    (show Monotone (fun q : ℚ => (q : ℝ)) from fun a b h => by
      change (a : ℝ) ≤ (b : ℝ)
      exact_mod_cast h) r
  let R : ℕ → ℝ := fun m => q m
  have hanti : Antitone R := fun a b hab => by
    change (q b : ℝ) ≤ (q a : ℝ)
    exact_mod_cast hqanti.antitone hab
  have hi : (⋂ m, closedBall (0 : ℝ) (R m)) = closedBall 0 r :=
    iInter_closedBall_of_antitone_tendsto r R hanti hqlim
  have hlim : Tendsto (fun m => ν (closedBall 0 (R m))) atTop (𝓝 (ν (closedBall 0 r))) := by
    simpa only [hi, Function.comp_def] using tendsto_measure_iInter_atTop
      (μ := ν) (fun _ => isClosed_closedBall.measurableSet.nullMeasurableSet)
      (fun a b hab => closedBall_subset_closedBall (hanti hab))
      ⟨0, (isCompact_closedBall (0 : ℝ) (R 0)).measure_lt_top.ne⟩
  have hEi : (⋂ m, E ∩ closedBall (0 : ℝ) (R m)) = E ∩ closedBall 0 r := by
    rw [← inter_iInter, hi]
  have hElim : Tendsto (fun m => ν (E ∩ closedBall 0 (R m))) atTop
      (𝓝 (ν (E ∩ closedBall 0 r))) := by
    simpa only [hEi, Function.comp_def] using tendsto_measure_iInter_atTop
      (μ := ν) (fun _ => (hE.inter isClosed_closedBall.measurableSet).nullMeasurableSet)
      (fun a b hab => inter_subset_inter_right E (closedBall_subset_closedBall (hanti hab)))
      ⟨0, ne_top_of_le_ne_top (isCompact_closedBall (0 : ℝ) (R 0)).measure_lt_top.ne
        (measure_mono inter_subset_right)⟩
  apply le_of_tendsto_of_tendsto hElim ((ENNReal.continuous_const_mul hc).tendsto _ |>.comp hlim)
  exact Filter.Eventually.of_forall fun m => hbound (q m) (hr.trans (hqabove m))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafMeasurableBad
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable bad sets for intrinsic leaf averages

Strict bad inequalities at rational radii define a measurable set.
Its complement controls every real radius, by continuity from above.
The diagonal scaling estimate bounds this set uniformly over all radii.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma measurableSet_rootHitTimes {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {E : Set (X n)} (hE : MeasurableSet E) (x : X n) : MeasurableSet (rootHitTimes hij E x) :=
  hE.preimage (((continuous_rightAction_uncurry n).comp
    (continuous_const.prodMk (continuous_rootTransvection hij))).measurable)

lemma measurable_rootHitMass {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (κ : Kernel (X n) ℝ) [IsSFiniteKernel κ]
    {E : Set (X n)} (hE : MeasurableSet E) (r : ℝ) :
    Measurable (fun x => κ x (rootHitTimes hij E x ∩ closedBall 0 r)) := by
  have hcont : Continuous (fun z : X n × ℝ =>
      rightAction z.1 (Matrix.SpecialLinearGroup.transvection hij z.2)) :=
    (continuous_rightAction_uncurry n).comp
      (continuous_fst.prodMk ((continuous_rootTransvection hij).comp continuous_snd))
  exact Kernel.measurable_kernel_prodMk_left
    ((hE.preimage hcont.measurable).inter (measurable_snd isClosed_closedBall.measurableSet))

lemma measurableSet_rootRationalBad {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (κ : Kernel (X n) ℝ) [IsSFiniteKernel κ]
    {E : Set (X n)} (hE : MeasurableSet E) (c : ℝ≥0∞) (R : ℝ) :
    MeasurableSet (rootRationalBad hij κ E c R) := by
  classical
  unfold rootRationalBad
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) ≤ R
  · simpa only [hq, true_and] using measurableSet_lt
      ((κ.measurable_coe isClosed_closedBall.measurableSet).const_mul c)
      (measurable_rootHitMass hij κ hE (q : ℝ))
  · simp only [hq, false_and, Set.ofPred_false]
    exact MeasurableSet.empty

theorem all_radii_rootRationalBad_bound
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ M : ℕ, ∀ (E : Set (X (d + 1))), MeasurableSet E → ∀ c : ℝ≥0∞,
      c * μ (⋃ m : ℕ, rootRationalBad hij (intrinsicRootKernel hij μ hfree) E c (m + 1)) ≤
        (M : ℝ≥0∞) * μ E + c * ε := by
  obtain ⟨M, hM⟩ := bounded_interval_intrinsic_maximal_bound d hij μ hA ε hε
  refine ⟨M, ?_⟩
  intro E hE c
  let κ := intrinsicRootKernel hij μ hfree
  have hmono : Monotone (fun m : ℕ => rootRationalBad hij κ E c (m + 1)) := by
    intro a b hab x hx
    obtain ⟨q, hq, hm⟩ := hx
    exact ⟨q, ⟨hq.1, hq.2.trans (by exact_mod_cast Nat.add_le_add_right hab 1)⟩, hm⟩
  rw [hmono.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro m
  apply hM (m + 1) _ E (measurableSet_rootRationalBad hij κ hE c _) hE c
  filter_upwards [ae_intrinsicRootKernel_eq hij μ hfree] with x hx hbad
  obtain ⟨q, hq, hm⟩ := hbad
  refine ⟨(q : ℝ), hq.1, hq.2, ?_⟩
  change c * κ x _ < κ x _ at hm
  rw [hx] at hm
  exact hm.le

theorem rootRationalBad_compl_all_radii
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (κ : Kernel (X n) ℝ) (x : X n) [IsLocallyFiniteMeasure (κ x)]
    {E : Set (X n)} (hE : MeasurableSet E) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hx : x ∉ ⋃ m : ℕ, rootRationalBad hij κ E c (m + 1)) :
    ∀ r : ℝ, 0 < r → κ x (rootHitTimes hij E x ∩ closedBall 0 r) ≤
      c * κ x (closedBall 0 r) := by
  apply relative_closedBall_bound_of_rational (κ x) (rootHitTimes hij E x)
    (measurableSet_rootHitTimes hij hE x) c hc
  intro q hq
  apply le_of_not_gt
  intro h
  obtain ⟨m, hm⟩ := exists_nat_gt (q : ℝ)
  apply hx
  exact mem_iUnion.mpr ⟨m, q, ⟨hq, by linarith⟩, h⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafGoodSet
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Large good sets for all leafwise radii

For a sufficiently small exceptional ambient set, almost every base
point sees only a prescribed small fraction of that set in every
centered root interval. This is the maximal-inequality good set used
in EKL (2006), Section 4.3.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_large_rootLeaf_good_set
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ E : Set (X (d + 1)), MeasurableSet E →
      μ E < ENNReal.ofReal δ → ∃ G : Set (X (d + 1)), MeasurableSet G ∧
      μ Gᶜ < ENNReal.ofReal η ∧ ∀ x ∈ G, ∀ r : ℝ, 0 < r →
        intrinsicRootLeaf hij μ x (rootHitTimes hij E x ∩ closedBall 0 r) ≤
          ENNReal.ofReal c * intrinsicRootLeaf hij μ x (closedBall 0 r) := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  have heq : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x := ae_intrinsicRootKernel_eq hij μ hfree
  obtain ⟨N, hNbad, hN, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp heq)
  obtain ⟨M, hM⟩ := all_radii_rootRationalBad_bound d hij μ hA hfree
    (ENNReal.ofReal (η / 2)) (by positivity)
  let δ : ℝ := c * η / (2 * ((M : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  refine ⟨δ, hδ, ?_⟩
  intro E hE hsmall
  let B : Set (X (d + 1)) := ⋃ m : ℕ, rootRationalBad hij κ E (ENNReal.ofReal c) (m + 1)
  have hB : MeasurableSet B := MeasurableSet.iUnion fun m =>
    measurableSet_rootRationalBad hij κ hE (ENNReal.ofReal c) (m + 1)
  have hb : ENNReal.ofReal c * μ B ≤
      (M : ℝ≥0∞) * μ E + ENNReal.ofReal c * ENNReal.ofReal (η / 2) := hM E hE _
  have hreal := ENNReal.toReal_mono (by finiteness) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_add (by finiteness) (by finiteness)] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hc.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ η / 2)] at hreal
  have hsmallR : (μ E).toReal < δ := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ E) ENNReal.ofReal_ne_top).mpr hsmall
    simpa only [ENNReal.toReal_ofReal hδ.le] using h
  have hterm : (M : ℝ) * (μ E).toReal < c * η / 2 := by
    calc
      (M : ℝ) * (μ E).toReal ≤ ((M : ℝ) + 1) * (μ E).toReal :=
        mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg
      _ < ((M : ℝ) + 1) * δ := mul_lt_mul_of_pos_left hsmallR (by positivity)
      _ = c * η / 2 := by dsimp [δ]; field_simp
  have hbadsmall : μ B < ENNReal.ofReal η := by
    apply (ENNReal.toReal_lt_toReal (measure_ne_top μ B) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hη.le]
    nlinarith
  refine ⟨(B ∪ N)ᶜ, (hB.union hN).compl, ?_, ?_⟩
  · rw [compl_compl]
    have hle : μ (B ∪ N) ≤ μ B := by
      simpa only [hNzero, add_zero] using (measure_union_le (μ := μ) B N)
    exact hle.trans_lt hbadsmall
  · intro x hx r hr
    have hxB : x ∉ B := fun h => hx (Or.inl h)
    have hxN : x ∉ N := fun h => hx (Or.inr h)
    have hxeq : κ x = intrinsicRootLeaf hij μ x := by
      by_contra h
      exact hxN (hNbad h)
    have h := rootRationalBad_compl_all_radii hij κ x hE (ENNReal.ofReal c)
      ENNReal.ofReal_ne_top hxB r hr
    simpa only [hxeq] using h

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafLusinGoodSet
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Lusin sets with uniform leafwise return control

The compact Lusin set and the maximal-inequality good set can be chosen
together. This supplies the two large sets used to select shearing
returns in EKL (2006), Section 4.3.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_compact_lusin_and_rootLeaf_good_set
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ K G : Set (X (d + 1)), IsCompact K ∧ K ⊆ Nᶜ ∧
      μ Kᶜ < ENNReal.ofReal η ∧ ContinuousOn (intrinsicLeafData hij μ hfree) K ∧
      (∀ x ∈ K, intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x) ∧
      MeasurableSet G ∧ μ Gᶜ < ENNReal.ofReal η ∧
      ∀ x ∈ G, ∀ r : ℝ, 0 < r →
        intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ closedBall 0 r) ≤
          ENNReal.ofReal c * intrinsicRootLeaf hij μ x (closedBall 0 r) := by
  obtain ⟨δ, hδ, hgood⟩ := exists_large_rootLeaf_good_set d hij μ hA c η hc hη
  let ε : ℝ≥0∞ := min (ENNReal.ofReal δ) (ENNReal.ofReal η)
  have hε : ε ≠ 0 := by
    apply ne_of_gt
    exact lt_min (ENNReal.ofReal_pos.mpr hδ) (ENNReal.ofReal_pos.mpr hη)
  obtain ⟨K, hK, hKN, hKsmall, hcont, hkernel⟩ :=
    exists_compact_continuous_rootLeafData hij μ hfree N hN hNzero ε hε
  have hKδ : μ Kᶜ < ENNReal.ofReal δ := hKsmall.trans_le (min_le_left _ _)
  obtain ⟨G, hG, hGsmall, hreturn⟩ := hgood Kᶜ hK.measurableSet.compl hKδ
  exact ⟨K, G, hK, hKN, hKsmall.trans_le (min_le_right _ _), hcont, hkernel,
    hG, hGsmall, hreturn⟩

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafClosedRadius
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable small-ball good sets

Nonatomic root leaves admit a common small closed-ball radius outside a
measurable set of arbitrarily small measure. Pointwise agreement with the
intrinsic leaves is obtained by removing one measurable null set.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_rootLeaf_closedBall_good_set
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hnontrivial : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0)
    (c ε : ℝ≥0∞) (hc : 0 < c) (hε : ε ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 2 ∧ ∃ G : Set (X (d + 1)),
      MeasurableSet G ∧ μ Gᶜ < ε ∧
      ∀ x ∈ G, intrinsicRootLeaf hij μ x (closedBall 0 ρ) < c := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  have heq : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x :=
    ae_intrinsicRootKernel_eq hij μ hfree
  obtain ⟨N, hNbad, hN, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp heq)
  obtain ⟨r, hr, hrhalf, hsmall⟩ :=
    exists_uniform_small_rootLeaf_ball d hij μ hA hnontrivial c ε hc hε
  let B := {x | c ≤ κ x (ball 0 r)}
  have hB : MeasurableSet B :=
    measurableSet_le measurable_const (κ.measurable_coe isOpen_ball.measurableSet)
  have hBmass : μ B < ε := by
    have hcongr : B =ᵐ[μ] {x | c ≤ intrinsicRootLeaf hij μ x (ball 0 r)} := by
      filter_upwards [heq] with x hx
      change (c ≤ κ x (ball 0 r)) = (c ≤ intrinsicRootLeaf hij μ x (ball 0 r))
      rw [hx]
    rwa [measure_congr hcongr]
  refine ⟨r / 2, by linarith, by linarith, (B ∪ N)ᶜ, (hB.union hN).compl, ?_, ?_⟩
  · rw [compl_compl]
    exact (measure_union_le B N).trans_lt (by simpa only [hNzero, add_zero] using hBmass)
  · intro x hx
    have hxB : x ∉ B := fun h => hx (Or.inl h)
    have hxN : x ∉ N := fun h => hx (Or.inr h)
    have hxeq : κ x = intrinsicRootLeaf hij μ x := by
      by_contra h
      exact hxN (hNbad h)
    have hmass : intrinsicRootLeaf hij μ x (ball 0 r) < c := by
      rw [← hxeq]
      exact lt_of_not_ge hxB
    exact (measure_mono (closedBall_subset_ball (by linarith : r / 2 < r))).trans_lt hmass

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingDiagonal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

theorem rootPairFlow_preserving
    (d : ℕ) (i j : Fin (d + 1)) (t : ℝ) (μ : Measure (X (d + 1)))
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    MeasurePreserving (fun x => rightAction x (rootPairFlow i j t)) μ μ := by
  refine ⟨(continuous_rightAction _).measurable, ?_⟩
  rw [rootPairFlow, diagonalOneParameter_eq_diagonalFlow]
  exact hA _

theorem exists_rootPairFlow_return_good_set
    (d : ℕ) (i j : Fin (d + 1)) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (E : Set (X (d + 1))) (hE : MeasurableSet E) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set (X (d + 1)), MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal (2 * μ.real E / c) ∧
      ∀ x ∈ G, ∀ T : ℝ, 1 ≤ T →
        volume.real (Ioc 0 T ∩ {t | rightAction x (rootPairFlow i j (-t)) ∈ E}) ≤ c * T := by
  let Φ : ℝ → X (d + 1) → X (d + 1) := fun t x => rightAction x (rootPairFlow i j (-t))
  have hcont : Continuous (fun p : X (d + 1) × ℝ => Φ p.2 p.1) := by
    have hD : Continuous (fun p : X (d + 1) × ℝ => rootPairFlow i j (-p.2)) :=
      (continuous_diagonalOneParameter (rootPairWeights i j) (rootPairWeights_sum i j)).comp
        continuous_snd.neg
    exact (continuous_rightAction_uncurry (d + 1)).comp (continuous_fst.prodMk hD)
  have hzero (x : X (d + 1)) : Φ 0 x = x := by
    simp [Φ, rootPairFlow, diagonalOneParameter_zero]
  have hadd (s t : ℝ) (x : X (d + 1)) : Φ (s + t) x = Φ s (Φ t x) := by
    dsimp [Φ, rootPairFlow]
    rw [rightAction_mul, ← diagonalOneParameter_add]
    congr 2
    ring
  exact exists_flow_return_good_set μ hcont.measurable hzero hadd
    (fun t => rootPairFlow_preserving d i j (-t) μ hA) hE c hc

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_LeafFlowCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
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

lemma normalized_scaling_locallyFinite (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r)) (c : ℝ) (hc : 0 < c) :
    IsLocallyFiniteMeasure
      (anchorNormalize (ν.map (fun u => c * u)) (Metric.ball 0 1)) := by
  have hm : ν.map (fun u => c * u) (Metric.ball 0 1) = ν (Metric.ball 0 (1 / c)) := by
    rw [Measure.map_apply (show Measurable (fun u : ℝ => c * u) from by fun_prop)
      Metric.isOpen_ball.measurableSet]
    exact congrArg ν (realScaling_preimage_ball c 1 hc)
  apply locallyFinite_of_finite_real_windows
  intro m
  change (ν.map (fun u => c * u) (Metric.ball 0 1))⁻¹ *
    ν.map (fun u => c * u) (Icc (-(m : ℝ)) m) < ∞
  rw [hm, Measure.map_apply (show Measurable (fun u : ℝ => c * u) from by fun_prop)
    measurableSet_Icc]
  apply ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (hp _ (by positivity)))
  exact ((Homeomorph.mulLeft₀ c hc.ne').isCompact_preimage.mpr isCompact_Icc).measure_lt_top

lemma rootPairCovarianceKernel_apply
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (x : X n) (t : ℝ) :
    rootPairCovarianceKernel hij μ hfree (x, t) =
      anchorNormalize ((intrinsicRootKernel hij μ hfree x).map
        (fun u => Real.exp (-2 * t) * u)) (Metric.ball 0 1) := rfl

theorem ae_rootPairKernel_covariance_fixed
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (t : ℝ) :
    ∀ᵐ x ∂μ, intrinsicRootKernel hij μ hfree (rightAction x (rootPairFlow i j (-t))) =
      rootPairCovarianceKernel hij μ hfree (x, t) := by
  have hpres := rootPairFlow_preserving d i j (-t) μ hA
  have hmap : ∀ᵐ y ∂μ.map (fun x => rightAction x (rootPairFlow i j (-t))),
      intrinsicRootKernel hij μ hfree y = intrinsicRootLeaf hij μ y := by
    rw [hpres.map_eq]
    exact ae_intrinsicRootKernel_eq hij μ hfree
  have htarget := ae_of_ae_map hpres.measurable.aemeasurable hmap
  have hcov := ae_intrinsicRootLeaf_diagonal hij (rootPairWeights i j)
    (rootPairWeights_sum i j) (-t) μ hfree hpres.map_eq
  have hs : rootTimeScaling (rootPairWeights i j) i j (-t) =
      Homeomorph.mulLeft₀ (Real.exp (-2 * t)) (Real.exp_ne_zero _) := by
    ext u
    simp only [rootTimeScaling, Homeomorph.coe_mulLeft₀,
      rootPairWeights_row hij, rootPairWeights_col hij]
    congr 2
    ring
  filter_upwards [ae_intrinsicRootKernel_eq hij μ hfree, htarget, hcov] with x hx ht hc
  rw [ht, rootPairCovarianceKernel_apply, hx]
  simpa only [rootPairFlow, hs, Homeomorph.coe_mulLeft₀] using hc

theorem ae_rootPairKernel_covariance_time
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, ∀ᵐ t : ℝ ∂volume,
      intrinsicRootKernel hij μ hfree (rightAction x (rootPairFlow i j (-t))) =
        rootPairCovarianceKernel hij μ hfree (x, t) := by
  let κ := intrinsicRootKernel hij μ hfree
  let η := rootPairCovarianceKernel hij μ hfree
  let η' := locallyFiniteRealVersion η
  have hflow : Measurable (fun p : X (d + 1) × ℝ =>
      rightAction p.1 (rootPairFlow i j (-p.2))) := by
    apply Continuous.measurable
    exact (continuous_rightAction_uncurry (d + 1)).comp
      (continuous_fst.prodMk ((continuous_diagonalOneParameter
        (rootPairWeights i j) (rootPairWeights_sum i j)).comp continuous_snd.neg))
  have hmeas : MeasurableSet {p : X (d + 1) × ℝ |
      κ (rightAction p.1 (rootPairFlow i j (-p.2))) = η' p} := by
    simp_rw [realMeasures_eq_iff_leafTests]
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    apply MeasurableSet.iInter
    intro b
    exact measurableSet_eq_fun
      (((leafTest a b).continuous.stronglyMeasurable.integral_kernel.measurable).comp hflow)
      (leafTest a b).continuous.stronglyMeasurable.integral_kernel.measurable
  have hfixed (t : ℝ) : ∀ᵐ x ∂μ,
      κ (rightAction x (rootPairFlow i j (-t))) = η' (x, t) := by
    filter_upwards [ae_rootPairKernel_covariance_fixed d hij μ hA hfree t] with x hx
    have hloc : IsLocallyFiniteMeasure (η (x, t)) := hx ▸ inferInstance
    rw [show η' (x, t) = η (x, t) from locallyFiniteRealVersion_eq η (x, t)]
    exact hx
  have htime : ∀ᵐ x ∂μ, ∀ᵐ t : ℝ ∂volume,
      κ (rightAction x (rootPairFlow i j (-t))) = η' (x, t) :=
    (MeasureTheory.Measure.ae_ae_comm hmeas).mpr (Eventually.of_forall hfixed)
  filter_upwards [htime, ae_intrinsicRootKernel_eq hij μ hfree,
    ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx he hp
  have hpos : ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r) := by
    simpa only [κ, he] using hp
  filter_upwards [hx] with t ht
  have hloc : IsLocallyFiniteMeasure (η (x, t)) :=
    normalized_scaling_locallyFinite (κ x) hpos (Real.exp (-2 * t)) (Real.exp_pos _)
  exact ht.trans (locallyFiniteRealVersion_eq η (x, t))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafRegularSet
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One conull set for leaf regularity and rebasing

The measurable kernel agrees with the intrinsic leaf, is locally finite,
has positive mass in every neighborhood of the origin, and satisfies
the leafwise rebasing law outside a single measurable null set.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_rootLeaf_regular_nullset
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∃ N : Set (X n), MeasurableSet N ∧ μ N = 0 ∧ ∀ x ∉ N,
      intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x ∧
      IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      (∀ r : ℝ, 0 < r → 0 < intrinsicRootLeaf hij μ x (Metric.ball 0 r)) ∧
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          basedRealMeasure (intrinsicRootLeaf hij μ x) t := by
  have h : ∀ᵐ x ∂μ,
      intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x ∧
      IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      (∀ r : ℝ, 0 < r → 0 < intrinsicRootLeaf hij μ x (Metric.ball 0 r)) ∧
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          basedRealMeasure (intrinsicRootLeaf hij μ x) t := by
    filter_upwards [ae_intrinsicRootKernel_eq hij μ hfree, ae_intrinsicRootLeaf_spec hij μ hfree,
      ae_intrinsicRootLeaf_ball_pos hij μ hfree, ae_intrinsicRootLeaf_rebase hij μ hfree]
      with x hx hs hp hr
    exact ⟨hx, hs.1, hp, hr⟩
  obtain ⟨N, hbad, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  refine ⟨N, hN, hzero, ?_⟩
  intro x hx
  by_contra h
  exact hx (hbad h)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RegularLusinSets
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regular Lusin sets and regular maximal-inequality base points

Removing the single regularity null set from the base-point good set
does not change its measure bound. The compact Lusin set can avoid that
null set and any additional prescribed null set at the same time.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_regular_lusin_rootLeaf_good_set
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ K G : Set (X (d + 1)), IsCompact K ∧ K ⊆ Nᶜ ∧
      μ Kᶜ < ENNReal.ofReal η ∧ ContinuousOn (intrinsicLeafData hij μ hfree) K ∧
      (∀ x ∈ K, RootLeafRegular hij μ hfree x) ∧
      MeasurableSet G ∧ μ Gᶜ < ENNReal.ofReal η ∧
      (∀ x ∈ G, RootLeafRegular hij μ hfree x) ∧
      ∀ x ∈ G, ∀ r : ℝ, 0 < r →
        intrinsicRootLeaf hij μ x (rootHitTimes hij Kᶜ x ∩ Metric.closedBall 0 r) ≤
          ENNReal.ofReal c * intrinsicRootLeaf hij μ x (Metric.closedBall 0 r) := by
  obtain ⟨M, hM, hMzero, hregular⟩ := exists_rootLeaf_regular_nullset hij μ hfree
  obtain ⟨K, G, hK, hKN, hKsmall, hcont, _, hG, hGsmall, hreturn⟩ :=
    exists_compact_lusin_and_rootLeaf_good_set d hij μ hA hfree
      (N ∪ M) (hN.union hM) (measure_union_null hNzero hMzero) c η hc hη
  have hKreg (x : X (d + 1)) (hx : x ∈ K) : RootLeafRegular hij μ hfree x :=
    hregular x (fun hm => hKN hx (Or.inr hm))
  have hGsmall' : μ (G \ M)ᶜ < ENNReal.ofReal η := by
    rw [compl_sdiff]
    have hle : μ (Gᶜ ∪ M) ≤ μ Gᶜ := by
      simpa only [hMzero, add_zero] using measure_union_le (μ := μ) Gᶜ M
    simpa only [union_comm] using hle.trans_lt hGsmall
  exact ⟨K, G \ M, hK, fun _ hx hn => hKN hx (Or.inl hn), hKsmall, hcont,
    hKreg, hG.diff hM, hGsmall', fun x hx => hregular x hx.2,
    fun x hx => hreturn x hx.1⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPairTimeSelection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual diagonal recurrence with simultaneous leaf covariance

The correct two-coordinate shearing flow has a large measurable set on
which both recurrence estimates hold on every long interval. Removing
one null set also gives leaf covariance at almost every time. The common
time can therefore satisfy all six recurrence conditions and all six
covariance identities used in the two-scale argument.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_rootPair_two_target_covariance_set
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (G H : Set (X (d + 1))) (hG : MeasurableSet G) (hH : MeasurableSet H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Z : Set (X (d + 1)), MeasurableSet Z ∧
      μ Zᶜ ≤ ENNReal.ofReal (2 * μ.real Gᶜ / ε) + ENNReal.ofReal (2 * μ.real Hᶜ / ε) ∧
      ∀ z ∈ Z,
        (∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree z t) ∧
        ∀ T : ℝ, 1 ≤ T →
          volume.real (Ioc 0 T ∩ {t | rightAction z (rootPairFlow i j (-t)) ∉ G}) ≤ ε * T ∧
          volume.real (Ioc 0 T ∩ {t | rightAction z (rootPairFlow i j (-t)) ∉ H}) ≤ ε * T := by
  obtain ⟨ZG, hZG, hmG, htG⟩ :=
    exists_rootPairFlow_return_good_set d i j μ hA Gᶜ hG.compl ε hε
  obtain ⟨ZH, hZH, hmH, htH⟩ :=
    exists_rootPairFlow_return_good_set d i j μ hA Hᶜ hH.compl ε hε
  have hcov : ∀ᵐ x ∂μ, ∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree x t :=
    ae_rootPairKernel_covariance_time d hij μ hA hfree
  obtain ⟨N, hbad, hN, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hcov)
  refine ⟨(ZG ∩ ZH) \ N, (hZG.inter hZH).diff hN, ?_, ?_⟩
  · rw [compl_sdiff, compl_inter, union_comm N]
    calc
      μ (ZGᶜ ∪ ZHᶜ ∪ N) ≤ μ (ZGᶜ ∪ ZHᶜ) + μ N := measure_union_le _ _
      _ = μ (ZGᶜ ∪ ZHᶜ) := by rw [hNzero, add_zero]
      _ ≤ μ ZGᶜ + μ ZHᶜ := measure_union_le _ _
      _ ≤ _ := add_le_add hmG hmH
  · intro z hz
    refine ⟨?_, fun T hT => ⟨htG z hz.1.1 T hT, htH z hz.1.2 T hT⟩⟩
    by_contra h
    exact hz.2 (hbad h)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPairSourceSet
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A positive-measure source for synchronized recurrence

The maximal estimates leave positive measure whenever their explicit
error budget is below one. Any prescribed null set can be removed
without losing positivity or the simultaneous recurrence and covariance
properties.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_positive_rootPair_source_set
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (G H N : Set (X (d + 1))) (hG : MeasurableSet G) (hH : MeasurableSet H)
    (hN : MeasurableSet N) (hNzero : μ N = 0)
    (ε : ℝ) (hε : 0 < ε)
    (hbudget : ENNReal.ofReal (2 * μ.real Gᶜ / ε) +
      ENNReal.ofReal (2 * μ.real Hᶜ / ε) < 1) :
    ∃ Z : Set (X (d + 1)), MeasurableSet Z ∧ μ Z ≠ 0 ∧ Z ⊆ Nᶜ ∧
      ∀ z ∈ Z,
        (∀ᵐ t : ℝ ∂volume, RootPairLeafCovariance hij μ hfree z t) ∧
        ∀ T : ℝ, 1 ≤ T →
          volume.real (Ioc 0 T ∩ {t | rightAction z (rootPairFlow i j (-t)) ∉ G}) ≤ ε * T ∧
          volume.real (Ioc 0 T ∩ {t | rightAction z (rootPairFlow i j (-t)) ∉ H}) ≤ ε * T := by
  obtain ⟨Z, hZ, hZsmall, hgood⟩ := exists_rootPair_two_target_covariance_set
    d hij μ hA hfree G H hG hH ε hε
  have hZpos : μ Z ≠ 0 := by
    intro hzero
    have htotal := prob_add_prob_compl (μ := μ) hZ
    rw [hzero, zero_add] at htotal
    exact (hZsmall.trans_lt hbudget).ne htotal
  refine ⟨Z \ N, hZ.diff hN, ?_, fun _ hx => hx.2, ?_⟩
  · rwa [measure_sdiff_null hNzero]
  · exact fun z hz => hgood z hz.1

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingSelectionData
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual sets used for the low-entropy shearing argument

The constants are fixed for this application. The two maximal estimates,
Lusin continuity, small central leaf mass, arithmetic freeness and leaf
regularity are all supplied by proved results. In particular the source
set has positive measure, so the neutral return theorem applies to it.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem nonempty_rootPairSelectionData_oai
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (hnontrivial : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    Nonempty (RootPairSelectionData d hij μ hfree N) := by
  obtain ⟨L, hbadL, hL, hLzero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp (ae_no_coordinate_zero d μ hA))
  have hcoords (x : X (d + 1)) (hx : x ∉ L) :
      ∀ v ∈ pointLattice x, v ≠ 0 → ∀ k, v k ≠ 0 := by
    by_contra h
    exact hx (hbadL h)
  obtain ⟨K, G, hK, hKN, _, hcont, hKreg, hG, hGsmall, hGreg, hreturn⟩ :=
    exists_regular_lusin_rootLeaf_good_set d hij μ hA hfree
      (N ∪ L) (hN.union hL) (measure_union_null hNzero hLzero)
      (1 / 8) (1 / 10000) (by norm_num) (by norm_num)
  obtain ⟨M, hM, hMzero, hMreg⟩ := exists_rootLeaf_regular_nullset hij μ hfree
  obtain ⟨ρ, hρ, hρsmall, H₀, hH₀, hH₀small, hsmall⟩ :=
    exists_rootLeaf_closedBall_good_set d hij μ hA hnontrivial (1 / 2)
      (ENNReal.ofReal (1 / 10000)) (by norm_num) (by norm_num)
  let H := H₀ \ M
  have hH : MeasurableSet H := hH₀.diff hM
  have hHsmall : μ Hᶜ < ENNReal.ofReal (1 / 10000) := by
    rw [show Hᶜ = M ∪ H₀ᶜ from compl_sdiff]
    have hle : μ (M ∪ H₀ᶜ) ≤ μ H₀ᶜ := by
      simpa only [hMzero, zero_add] using measure_union_le (μ := μ) M H₀ᶜ
    exact hle.trans_lt hH₀small
  have hGreal : μ.real Gᶜ < (1 / 10000 : ℝ) := by
    simpa only [Measure.real, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 10000)] using
      (ENNReal.toReal_lt_toReal (measure_ne_top μ Gᶜ) ENNReal.ofReal_ne_top).mpr hGsmall
  have hHreal : μ.real Hᶜ < (1 / 10000 : ℝ) := by
    simpa only [Measure.real, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 10000)] using
      (ENNReal.toReal_lt_toReal (measure_ne_top μ Hᶜ) ENNReal.ofReal_ne_top).mpr hHsmall
  have hbudget : ENNReal.ofReal (2 * μ.real Gᶜ / (1 / 100)) +
      ENNReal.ofReal (2 * μ.real Hᶜ / (1 / 100)) < 1 := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_lt_one]
    norm_num [div_eq_mul_inv] at ⊢
    linarith
  obtain ⟨Z, hZ, hZpos, hZM, hZgood⟩ := exists_positive_rootPair_source_set d hij μ hA hfree
    G H M hG hH hM hMzero (1 / 100) (by norm_num) hbudget
  refine ⟨{
    K := K, G := G, H := H, Z := Z, ρ := ρ
    rho_pos := hρ, rho_small := hρsmall
    compact := hK
    outside := fun x hx hn => hKN hx (Or.inl hn)
    continuous := hcont
    compact_regular := hKreg
    coordinates := fun x hx => hcoords x (fun hl => hKN hx (Or.inr hl))
    good_regular := hGreg
    good_returns := hreturn
    small_ball := ?_
    source_measurable := hZ
    source_positive := hZpos
    source_regular := fun z hz => hMreg z (hZM hz)
    source_covariance := fun z hz => (hZgood z hz).1
    source_returns := fun z hz => (hZgood z hz).2
  }⟩
  intro x hx
  rw [(hMreg x hx.2).1]
  exact hsmall x hx.1

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.nonempty_rootPairSelectionData_oai := @OAI.DukePrimeDegree.nonempty_rootPairSelectionData_oai
