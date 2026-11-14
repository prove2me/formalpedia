-- Prove2me | solution 1 for OAI.DukePrimeDegree.canonicalRootCoefficient_one_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:48.098205+00:00
-- url     : https://prove2.me/submissions/5a829fba-f8b2-4761-acfa-c9b46ff61778

import Mathlib
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

 

lemma normalized_translation_invariant_measure (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (J : Set ℝ) (hJ : ν J = 1)
    (hinv : ∀ a : ℝ, Measure.map (fun t : ℝ => t+a) ν = ν) :
    ∃ c : ℝ≥0, ν = c • (volume : Measure ℝ) ∧ (c : ℝ≥0∞) = (volume J)⁻¹ := by
  let : ν.IsAddLeftInvariant := ⟨fun a => by simpa only [add_comm] using hinv a⟩
  let c := addHaarScalarFactor ν (volume : Measure ℝ)
  have he : ν = c • (volume : Measure ℝ) := isAddLeftInvariant_eq_smul ν volume
  refine ⟨c,he,?_⟩
  apply ENNReal.eq_inv_of_mul_eq_one_left
  have H := hJ
  rw [he,Measure.smul_apply] at H
  simpa only [ENNReal.smul_def,smul_eq_mul] using H

end PrimeDegreePackets


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
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntrinsicLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafPeriods
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceBaseNontriviallyNormedField _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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


lemma continuous_integral_translate (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (f : C_c(ℝ,ℝ)) : Continuous (fun a : ℝ => ∫ x, f (x+a) ∂ν) := by
  have H := ((f.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)).continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) (locallyIntegrable_const (μ := ν) (1:ℝ))
    (f.continuous.comp continuous_neg)).comp continuous_neg
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  simp only [Function.comp_apply,convolution_def,ContinuousLinearMap.mul_apply',one_mul]
  congr 1
  funext x
  congr 1
  simp

lemma realLeafPeriods_eq_tests (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    (realLeafPeriods ν : Set ℝ) =
      ⋂ f : C_c(ℝ,ℝ), {a | (∫ x, f (x+a) ∂ν) = ∫ x, f x ∂ν} := by
  ext a
  simp only [mem_iInter,mem_ofPred_eq]
  constructor
  · intro ha f
    change ν.map (fun x => x+a) = ν at ha
    have H := integral_map (μ := ν) («φ» := fun x : ℝ => x+a)
      (f := fun x => f x) (by fun_prop) f.continuous.aestronglyMeasurable
    rw [ha] at H
    exact H.symm
  · intro ha
    have : (ν.map (fun x : ℝ => x+a)).Regular :=
      Measure.Regular.map (Homeomorph.addRight a)
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := ν) («φ» := fun x : ℝ => x+a)
      (f := fun x => f x) (by fun_prop) f.continuous.aestronglyMeasurable]
    exact ha f

 

theorem isClosed_realLeafPeriods (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    IsClosed (realLeafPeriods ν : Set ℝ) := by
  rw [realLeafPeriods_eq_tests]
  exact isClosed_iInter fun f => isClosed_eq (continuous_integral_translate ν f) continuous_const

lemma realLeafPeriods_eq_top_of_dense (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hd : Dense (realLeafPeriods ν : Set ℝ)) : realLeafPeriods ν = ⊤ := by
  apply SetLike.coe_injective
  change (realLeafPeriods ν : Set ℝ) = univ
  rw [←(isClosed_realLeafPeriods ν).closure_eq,hd.closure_eq]

 

theorem realLeaf_invariant_of_small_periods (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hs : ∀ ε > 0, ∃ a ∈ realLeafPeriods ν, a ∈ Set.Ioo 0 ε) (a : ℝ) :
    ν.map (fun x => x+a) = ν := by
  have H := realLeafPeriods_eq_top_of_dense ν ((realLeafPeriods ν).dense_of_not_isolated_zero hs)
  change a ∈ realLeafPeriods ν
  rw [H]
  trivial



end PrimeDegreePackets


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
namespace PrimeDegreePackets

lemma exists_compact_zero_iff_dense_tests {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [SeparableSpace T] [Nonempty T]
    (F : ℕ → T → ℝ) (hF : ∀ n, Continuous (F n)) :
    (∃ t : T, ∀ n, F n t = 0) ↔
      ∀ k : ℕ, ∃ j : ℕ, ∀ i : Fin (k+1),
        |F i (denseSeq T j)| < 1/((k:ℝ)+1) := by
  constructor
  · rintro ⟨t,ht⟩ k
    let U := ⋂ i : Fin (k+1), {t : T | |F i t| < 1/((k:ℝ)+1)}
    have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
      isOpen_lt (hF i).abs continuous_const
    have htU : t ∈ U := by
      simp only [U,mem_iInter,mem_ofPred_eq,ht,abs_zero]
      intro _
      positivity
    obtain ⟨j,hj⟩ := (denseRange_denseSeq T).exists_mem_open hU ⟨t,htU⟩
    exact ⟨j,fun i => mem_iInter.mp hj i⟩
  · intro h
    let C (k : ℕ) := ⋂ i : Fin (k+1), {t : T | |F i t| ≤ 1/((k:ℝ)+1)}
    have hclosed (k : ℕ) : IsClosed (C k) := isClosed_iInter fun i =>
      isClosed_le (hF i).abs continuous_const
    have hnonempty (k : ℕ) : (C k).Nonempty := by
      obtain ⟨j,hj⟩ := h k
      exact ⟨denseSeq T j,mem_iInter.mpr fun i => (hj i).le⟩
    have hanti (k : ℕ) : C (k+1) ⊆ C k := by
      intro t ht
      apply mem_iInter.mpr
      intro i
      have H : |F i t| ≤ 1/(((k+1:ℕ):ℝ)+1) :=
        mem_iInter.mp ht ⟨i.val,by omega⟩
      exact H.trans (Nat.one_div_le_one_div (Nat.le_succ k))
    obtain ⟨t,ht⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      hanti hnonempty (hclosed 0).isCompact hclosed
    refine ⟨t,fun i => ?_⟩
    have H : ∀ᶠ k : ℕ in atTop, |F i t| ≤ 1/((k:ℝ)+1) := by
      filter_upwards [eventually_ge_atTop i] with k hk
      exact mem_iInter.mp (mem_iInter.mp ht k) ⟨i,by omega⟩
    have hz : |F i t| ≤ 0 := ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat H
    exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

 

theorem measurableSet_exists_compact_zero {α T : Type*} [MeasurableSpace α]
    [TopologicalSpace T] [CompactSpace T] [SeparableSpace T] [Nonempty T]
    (F : ℕ → α → T → ℝ)
    (hm : ∀ n t, Measurable (fun x => F n x t))
    (hc : ∀ n x, Continuous (F n x)) :
    MeasurableSet {x : α | ∃ t : T, ∀ n, F n x t = 0} := by
  simp_rw [exists_compact_zero_iff_dense_tests (fun n => F n _) (fun n => hc n _)]
  simp_rw [Set.ofPred_forall,Set.ofPred_exists]
  exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun j =>
    by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i : Fin (k+1) =>
        measurableSet_lt (hm i (denseSeq T j)).abs measurable_const

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootInvariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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


lemma projectiveLeafPeriod_iff_tests (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (p : ℝ × ℝ) :
    projectiveLeafPeriod ν p ↔ ∀ N k : ℕ,
      (∫ x, leafTest N k (x+p.1) ∂ν) = Real.exp p.2 * ∫ x, leafTest N k x ∂ν := by
  let : (ν.map (fun x : ℝ => x+p.1)).Regular := Measure.Regular.map (Homeomorph.addRight p.1)
  let : IsFiniteMeasureOnCompacts (ENNReal.ofReal (Real.exp p.2) • ν) :=
    IsFiniteMeasureOnCompacts.smul ν ENNReal.ofReal_ne_top
  unfold projectiveLeafPeriod
  rw [realMeasures_eq_iff_leafTests]
  congr! 2
  rename_i N k
  rw [integral_map (μ := ν) («φ» := fun x : ℝ => x+p.1)
    (f := fun x => leafTest N k x) (by fun_prop)
    (leafTest N k).continuous.aestronglyMeasurable,
    integral_smul_measure,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]

lemma continuous_projectiveLeaf_discrepancy (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (N k : ℕ) : Continuous (fun p : ℝ × ℝ =>
      (∫ x, leafTest N k (x+p.1) ∂ν) - Real.exp p.2 * ∫ x, leafTest N k x ∂ν) :=
  ((continuous_integral_translate ν (leafTest N k)).comp continuous_fst).sub
    ((Real.continuous_exp.comp continuous_snd).mul continuous_const)

lemma measurable_projectiveLeaf_discrepancy {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) (N k : ℕ) (p : ℝ × ℝ) : Measurable (fun z =>
      (∫ x, leafTest N k (x+p.1) ∂κ z) - Real.exp p.2 * ∫ x, leafTest N k x ∂κ z) := by
  exact (((leafTest N k).continuous.comp (continuous_id.add_const p.1)).stronglyMeasurable.integral_kernel).measurable.sub
    (measurable_const.mul ((leafTest N k).continuous.stronglyMeasurable.integral_kernel).measurable)

lemma isClosed_projectiveLeafPeriods (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    IsClosed {p | projectiveLeafPeriod ν p} := by
  have he : {p | projectiveLeafPeriod ν p} =
      ⋂ N : ℕ, ⋂ k : ℕ, {p : ℝ × ℝ |
        (∫ x, leafTest N k (x+p.1) ∂ν) - Real.exp p.2 * ∫ x, leafTest N k x ∂ν = 0} := by
    ext p
    simp only [Set.mem_ofPred_eq,mem_iInter,sub_eq_zero,projectiveLeafPeriod_iff_tests]
  rw [he]
  exact isClosed_iInter fun N => isClosed_iInter fun k =>
    isClosed_eq (continuous_projectiveLeaf_discrepancy ν N k) continuous_const

 

lemma projectiveLeafPeriod_zero_time (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : 0 < ν (Metric.ball 0 1)) (b : ℝ) (h : projectiveLeafPeriod ν (0,b)) : b = 0 := by
  have he : ν = ENNReal.ofReal (Real.exp b) • ν := by
    simpa [projectiveLeafPeriod] using h
  have H := congrArg (fun ρ : Measure ℝ => ρ (Metric.ball 0 1)) he
  rw [Measure.smul_apply,smul_eq_mul] at H
  have HH : (1:ℝ≥0∞) = ENNReal.ofReal (Real.exp b) :=
    (ENNReal.mul_left_inj hp.ne' measure_ball_lt_top.ne).mp (by simpa only [one_mul] using H)
  exact (Real.exp_eq_one_iff b).mp (ENNReal.ofReal_eq_one.mp HH.symm)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma projectiveLeafPeriod_smul (ν : Measure ℝ) (q : ℝ≥0∞) (hq0 : q ≠ 0) (hqT : q ≠ ∞)
    (p : ℝ × ℝ) : projectiveLeafPeriod (q • ν) p ↔ projectiveLeafPeriod ν p := by
  unfold projectiveLeafPeriod
  rw [Measure.map_smul (f := fun value : ℝ => value+p.1),
    smul_comm (ENNReal.ofReal (Real.exp p.2)) q ν]
  constructor
  · intro he
    have H := congrArg (fun ρ : Measure ℝ => q⁻¹ • ρ) he
    simpa only [smul_smul,←mul_assoc,ENNReal.inv_mul_cancel hq0 hqT,one_mul,one_smul] using H
  · exact congrArg (fun ρ : Measure ℝ => q • ρ)

lemma projectiveLeafPeriod_scaling (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0) (p : ℝ × ℝ) :
    projectiveLeafPeriod (ν.map (Homeomorph.mulLeft₀ c hc)) (c*p.1,p.2) ↔
      projectiveLeafPeriod ν p := by
  have H : (ν.map (Homeomorph.mulLeft₀ c hc)).map (fun x => x+c*p.1) =
      (ν.map (fun x => x+p.1)).map (Homeomorph.mulLeft₀ c hc) := by
    rw [Measure.map_map (by fun_prop) (Homeomorph.mulLeft₀ c hc).measurable,
      Measure.map_map (Homeomorph.mulLeft₀ c hc).measurable (by fun_prop)]
    congr 1
    ext x
    change c*x+c*p.1 = c*(x+p.1)
    ring
  unfold projectiveLeafPeriod
  rw [H,←Measure.map_smul]
  exact (Homeomorph.mulLeft₀ c hc).measurableEmbedding.map_injective.eq_iff

lemma projectiveLeafPeriod_normalized_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c : ℝ) (hc : 0 < c) (p : ℝ × ℝ) :
    projectiveLeafPeriod
      (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) (c*p.1,p.2) ↔
        projectiveLeafPeriod ν p := by
  have hm : ν.map (Homeomorph.mulLeft₀ c hc.ne') (Metric.ball 0 1) =
      ν (Metric.ball 0 (1/c)) := by
    rw [Measure.map_apply (Homeomorph.mulLeft₀ c hc.ne').measurable
      Metric.isOpen_ball.measurableSet,realScaling_preimage_ball c 1 hc]
  unfold anchorNormalize
  rw [projectiveLeafPeriod_smul _ _ (by rw [hm]; exact ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    (by rw [hm]; exact ENNReal.inv_ne_top.mpr (hp _ (by positivity)).ne')]
  exact projectiveLeafPeriod_scaling ν c hc.ne' p



lemma boundedProjectiveLeafPeriod_mono (ν : Measure ℝ) {r R l u : ℝ} (hr : r ≤ R) :
    boundedProjectiveLeafPeriod ν r l u → boundedProjectiveLeafPeriod ν R l u := by
  rintro ⟨p,hp,hrp,hs⟩
  exact ⟨p,hp,hrp.trans hr,hs⟩

lemma boundedProjectiveLeafPeriod_normalized_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (c : ℝ) (hc : 0 < c) (R l u : ℝ) :
    boundedProjectiveLeafPeriod
      (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) R l u ↔
      boundedProjectiveLeafPeriod ν (R/c) l u := by
  constructor
  · rintro ⟨p,hp',hpa,hpb⟩
    refine ⟨(p.1/c,p.2),?_,?_,hpb⟩
    · apply (projectiveLeafPeriod_normalized_scaling ν hp c hc (p.1/c,p.2)).mp
      simpa only [mul_div_cancel₀ _ hc.ne'] using hp'
    · change |p.1/c| ≤ R/c
      rw [abs_div,abs_of_pos hc]
      exact (div_le_div_iff_of_pos_right hc).mpr hpa
  · rintro ⟨p,hp',hpa,hpb⟩
    refine ⟨(c*p.1,p.2),(projectiveLeafPeriod_normalized_scaling ν hp c hc p).mpr hp',?_,hpb⟩
    change |c*p.1| ≤ R
    rw [abs_mul,abs_of_pos hc,mul_comm]
    exact (le_div_iff₀ hc).mp hpa

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma measurableSet_exists_projectiveLeafPeriod_mem {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [∀ x, IsLocallyFiniteMeasure (κ x)]
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    MeasurableSet {x : α | ∃ p ∈ K, projectiveLeafPeriod (κ x) p} := by
  by_cases he : K.Nonempty
  · let T := ↥K
    let : Nonempty T := he.to_subtype
    let : CompactSpace T := isCompact_iff_compactSpace.mp hK
    let : SecondCountableTopology T := Subtype.secondCountableTopology _
    let F (n : ℕ) (x : α) (p : T) : ℝ :=
      (∫ y, leafTest n.unpair.1 n.unpair.2 (y+p.val.1) ∂κ x) -
        Real.exp p.val.2 * ∫ y, leafTest n.unpair.1 n.unpair.2 y ∂κ x
    have H := measurableSet_exists_compact_zero F
      (fun n p => measurable_projectiveLeaf_discrepancy κ _ _ p.val)
      (fun n x => (continuous_projectiveLeaf_discrepancy (κ x) _ _).comp continuous_subtype_val)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    constructor
    · rintro ⟨p,hp,hper⟩
      exact ⟨⟨p,hp⟩,fun n => sub_eq_zero.mpr
        ((projectiveLeafPeriod_iff_tests (κ x) p).mp hper _ _)⟩
    · rintro ⟨p,hp⟩
      refine ⟨p.val,p.prop,(projectiveLeafPeriod_iff_tests (κ x) p.val).mpr ?_⟩
      intro N k
      have H := hp (Nat.pair N k)
      simpa only [F,Nat.unpair_pair,sub_eq_zero] using H
  · simp only [Set.not_nonempty_iff_eq_empty.mp he,mem_empty_iff_false,false_and,exists_false,
      Set.ofPred_false,MeasurableSet.empty]

lemma measurableSet_boundedProjectiveLeafPeriod {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [∀ x, IsLocallyFiniteMeasure (κ x)] (R l u : ℝ) :
    MeasurableSet {x : α | boundedProjectiveLeafPeriod (κ x) R l u} := by
  have he : {x : α | boundedProjectiveLeafPeriod (κ x) R l u} =
      {x : α | ∃ p ∈ (Icc (-R) R ×ˢ Icc l u), projectiveLeafPeriod (κ x) p} := by
    ext x
    simp only [Set.mem_ofPred_eq,boundedProjectiveLeafPeriod,mem_prod]
    constructor
    · rintro ⟨p,hp,ha,hb⟩
      exact ⟨p,⟨abs_le.mp ha,hb⟩,hp⟩
    · rintro ⟨p,⟨ha,hb⟩,hp⟩
      exact ⟨p,hp,abs_le.mpr ha,hb⟩
  rw [he]
  exact measurableSet_exists_projectiveLeafPeriod_mem κ _ (isCompact_Icc.prod isCompact_Icc)

 

lemma not_forall_boundedProjectiveLeafPeriod (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hp : 0 < ν (Metric.ball 0 1)) (l u : ℝ) (hzero : (0:ℝ) ∉ Icc l u) :
    ¬ ∀ k : ℕ, boundedProjectiveLeafPeriod ν (1/((k:ℝ)+1)) l u := by
  intro H
  let C (k : ℕ) : Set (ℝ × ℝ) := {p | projectiveLeafPeriod ν p} ∩
    (Icc (-(1/((k:ℝ)+1))) (1/((k:ℝ)+1)) ×ˢ Icc l u)
  have hc (k : ℕ) : IsClosed (C k) :=
    (isClosed_projectiveLeafPeriods ν).inter (isClosed_Icc.prod isClosed_Icc)
  have hne (k : ℕ) : (C k).Nonempty := by
    obtain ⟨p,hp,ha,hb⟩ := H k
    exact ⟨p,hp,abs_le.mp ha,hb⟩
  have ha (k : ℕ) : C (k+1) ⊆ C k := by
    rintro p ⟨hp,ha,hb⟩
    refine ⟨hp,?_,hb⟩
    exact abs_le.mp ((abs_le.mpr ha).trans (Nat.one_div_le_one_div (Nat.le_succ k)))
  have hcomp : IsCompact (C 0) :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (hc 0) (fun _ h => h.2)
  obtain ⟨p,hpC⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C ha hne hcomp hc
  have hpa : ∀ᶠ k : ℕ in atTop, |p.1| ≤ 1/((k:ℝ)+1) :=
    Eventually.of_forall fun k => abs_le.mpr (mem_iInter.mp hpC k).2.1
  have hp0 : p.1 = 0 := abs_eq_zero.mp (le_antisymm
    (ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat hpa) (abs_nonneg _))
  have hper := (mem_iInter.mp hpC 0).1
  have hrect := (mem_iInter.mp hpC 0).2.2
  have he : p = (0,p.2) := Prod.ext hp0 rfl
  rw [he] at hper
  have hp2 : p.2 = 0 := projectiveLeafPeriod_zero_time ν hp p.2 hper
  exact hzero (hp2 ▸ hrect)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma ae_boundedProjectiveLeafPeriod_scaling {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    {T : α → α} (hT : MeasurePreserving T μ μ) (c : ℝ) (hc : 1 ≤ c)
    (hcov : ∀ᵐ x ∂μ, κ (T x) =
      anchorNormalize ((κ x).map (Homeomorph.mulLeft₀ c (by linarith))) (Metric.ball 0 1))
    (R l u : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ x ∂μ, boundedProjectiveLeafPeriod (κ x) R l u ↔
      boundedProjectiveLeafPeriod (κ x) (R/c) l u := by
  classical
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  let E : Set α := {x | boundedProjectiveLeafPeriod (κ x) R l u}
  let f : α → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator (measurableSet_boundedProjectiveLeafPeriod κ R l u)
  have he : ∀ᵐ x ∂μ, T x ∈ E ↔ boundedProjectiveLeafPeriod (κ x) (R/c) l u := by
    filter_upwards [hp,hcov] with x hx hcovx
    change boundedProjectiveLeafPeriod (κ (T x)) R l u ↔ _
    rw [hcovx]
    exact boundedProjectiveLeafPeriod_normalized_scaling (κ x) hx c hc0 R l u
  have hmono : ∀ᵐ x ∂μ, f (T x) ≤ f x := by
    filter_upwards [he] with x hx
    by_cases h : T x ∈ E
    · have hxE : x ∈ E := boundedProjectiveLeafPeriod_mono (κ x)
        (div_le_self hR hc) (hx.mp h)
      simp only [f,indicator_of_mem h,indicator_of_mem hxE,le_refl]
    · simp only [f,indicator_of_notMem h]
      exact bot_le
  have heq := ae_eq_of_measurePreserving_ennreal_ge μ hT hf.aemeasurable
    (Eventually.of_forall fun x => show f x ≤ 1 from by
      by_cases hx : x ∈ E <;> simp [f,hx]) hmono
  filter_upwards [he,heq] with x hx heqx
  have hiff : x ∈ E ↔ T x ∈ E := by
    by_cases hxE : x ∈ E <;> by_cases hTE : T x ∈ E <;>
      simp_all [f,Function.comp_apply]
  exact hiff.trans hx

lemma ae_projectiveLeafPeriod_avoids_interval {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    (hscaling : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α, MeasurePreserving T μ μ ∧
      ∀ᵐ x ∂μ, κ (T x) = anchorNormalize
        ((κ x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1))
    (l u : ℝ) (hzero : (0:ℝ) ∉ Icc l u) :
    ∀ᵐ x ∂μ, ∀ p : ℝ × ℝ, projectiveLeafPeriod (κ x) p → p.2 ∉ Icc l u := by
  have H (m k : ℕ) : ∀ᵐ x ∂μ, boundedProjectiveLeafPeriod (κ x) ((m:ℝ)+1) l u ↔
      boundedProjectiveLeafPeriod (κ x) (1/((k:ℝ)+1)) l u := by
    let c : ℝ := ((m:ℝ)+1)*((k:ℝ)+1)
    have hc : 1 ≤ c := by
      dsimp [c]
      nlinarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨T,hT,hcov⟩ := hscaling c (zero_lt_one.trans_le hc)
    have he := ae_boundedProjectiveLeafPeriod_scaling μ κ hp hT c hc hcov ((m:ℝ)+1) l u (by positivity)
    have hdiv : ((m:ℝ)+1)/c = 1/((k:ℝ)+1) := by
      dsimp [c]
      field_simp
    simpa only [hdiv] using he
  have HH : ∀ᵐ x ∂μ, ∀ m k : ℕ, boundedProjectiveLeafPeriod (κ x) ((m:ℝ)+1) l u ↔
      boundedProjectiveLeafPeriod (κ x) (1/((k:ℝ)+1)) l u :=
    ae_all_iff.mpr fun m => ae_all_iff.mpr fun k => H m k
  filter_upwards [hp,HH] with x hx hxx
  intro p hper hmem
  obtain ⟨m,hm⟩ := exists_nat_gt |p.1|
  have hlarge : boundedProjectiveLeafPeriod (κ x) ((m:ℝ)+1) l u := ⟨p,hper,by linarith,hmem⟩
  exact not_forall_boundedProjectiveLeafPeriod (κ x) (hx 1 zero_lt_one) l u hzero
    (fun k => (hxx m k).mp hlarge)

lemma exists_nat_mem_Icc_inv_succ {b : ℝ} (hb : 0 < b) :
    ∃ n : ℕ, b ∈ Icc (1/((n:ℝ)+1)) ((n:ℝ)+1) := by
  obtain ⟨m,hm⟩ := exists_nat_gt b
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hb
  refine ⟨max m k,?_,?_⟩
  · exact (Nat.one_div_le_one_div (Nat.le_max_right m k)).trans hk.le
  · have H : (m:ℝ) ≤ ((max m k:ℕ):ℝ) := Nat.cast_le.mpr (Nat.le_max_left m k)
    linarith

 

theorem ae_projectiveLeafPeriod_multiplier_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α ℝ)
    [∀ x, IsLocallyFiniteMeasure (κ x)]
    (hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r))
    (hscaling : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α, MeasurePreserving T μ μ ∧
      ∀ᵐ x ∂μ, κ (T x) = anchorNormalize
        ((κ x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, ∀ p : ℝ × ℝ, projectiveLeafPeriod (κ x) p → p.2 = 0 := by
  have Hpos (n : ℕ) := ae_projectiveLeafPeriod_avoids_interval μ κ hp hscaling
    (1/((n:ℝ)+1)) ((n:ℝ)+1) (by
      intro h
      have : 0 < 1/((n:ℝ)+1) := by positivity
      linarith [h.1])
  have Hneg (n : ℕ) := ae_projectiveLeafPeriod_avoids_interval μ κ hp hscaling
    (-((n:ℝ)+1)) (-(1/((n:ℝ)+1))) (by
      intro h
      have : 0 < 1/((n:ℝ)+1) := by positivity
      linarith [h.2])
  filter_upwards [ae_all_iff.mpr Hpos,ae_all_iff.mpr Hneg] with x hx hy
  intro p hp
  rcases lt_trichotomy (0:ℝ) p.2 with h | h | h
  · obtain ⟨n,hn⟩ := exists_nat_mem_Icc_inv_succ h
    exact (hx n p hp hn).elim
  · exact h.symm
  · obtain ⟨n,hn⟩ := exists_nat_mem_Icc_inv_succ (neg_pos.mpr h)
    exact (hy n p hp ⟨by linarith [hn.2],by linarith [hn.1]⟩).elim

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_PublishedEKL
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Haar rigidity from root-leaf symmetries

Projective normalization can be removed from root-leaf symmetries, and
nontrivial root periods yield invariance under the corresponding
unipotent group. Haar measure follows from all root periods, or from
a single root and a transitive prime-degree symmetry group.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree

open PrimeDegreePackets

/-- A projective period of a leaf with zero logarithmic multiplier is an
ordinary period. -/
lemma leaf_period_of_projective_multiplier_zero
    (ν : Measure ℝ) (p : ℝ × ℝ) (hp : projectiveLeafPeriod ν p) (hzero : p.2 = 0) :
    p.1 ∈ realLeafPeriods ν := by
  change ν.map (fun x => x + p.1) = ν
  simpa only [projectiveLeafPeriod, hzero, Real.exp_zero, ENNReal.ofReal_one, one_smul] using hp

/-- Equality with a rebased normalized leaf yields a projective period.
The normalizing scalar is recovered from the unit-ball mass. -/
lemma projectivePeriod_of_based_fixed
    (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (hunit : ν (Metric.ball 0 1) = 1)
    (t : ℝ) (hfixed : basedRealMeasure ν t = ν) :
    projectiveLeafPeriod ν (-t, Real.log (ν (Metric.ball t 1)).toReal) := by
  let m := ν (Metric.ball t 1)
  have hmul : m⁻¹ * m = 1 := by
    have he := congrArg (fun ρ : Measure ℝ => ρ (Metric.ball 0 1)) hfixed
    simpa only [basedRealMeasure, anchorNormalize, Measure.smul_apply,
      smul_eq_mul, centerRealMeasure_ball, hunit] using he
  have hm0 : m ≠ 0 := by
    intro hm
    simp [hm] at hmul
  have hmT : m ≠ ∞ := measure_ball_lt_top.ne
  have hcenter : centerRealMeasure ν t = m • ν := by
    have hs := congrArg (fun ρ : Measure ℝ => m • ρ) hfixed
    simp only [basedRealMeasure, anchorNormalize, centerRealMeasure_ball] at hs
    change m • (m⁻¹ • centerRealMeasure ν t) = m • ν at hs
    rw [smul_smul, ENNReal.mul_inv_cancel hm0 hmT, one_smul] at hs
    exact hs
  change ν.map (fun x => x + -t) = ENNReal.ofReal (Real.exp (Real.log m.toReal)) • ν
  rw [Real.exp_log (ENNReal.toReal_pos hm0 hmT), ENNReal.ofReal_toReal hmT]
  simpa only [centerRealMeasure, Homeomorph.coe_subRight, sub_eq_add_neg] using hcenter

/-- For a finite invariant ambient measure, the full diagonal scaling
covariance forces every projective root-leaf period to have multiplier
one. This is the normalization step needed by the low-entropy argument. -/
theorem ae_intrinsic_projective_multiplier_zero
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ p : ℝ × ℝ,
      projectiveLeafPeriod (intrinsicRootLeaf hij μ x) p → p.2 = 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let κ := intrinsicRootKernel hij μ hfree
  have heq : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x :=
    ae_intrinsicRootKernel_eq hij μ hfree
  have hp : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < κ x (Metric.ball 0 r) := by
    filter_upwards [heq, ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx hp
    rwa [hx]
  have H := ae_projectiveLeafPeriod_multiplier_zero μ κ hp (by
    intro c hc
    let T : X (d + 1) → X (d + 1) :=
      fun x => rightAction x (rootCanonicalFlow d j (Real.log c))
    have hT : MeasurePreserving T μ μ :=
      rootCanonicalFlow_preserving d j (Real.log c) μ hA
    refine ⟨T, hT, ?_⟩
    have heqmap : ∀ᵐ x ∂μ.map T, κ x = intrinsicRootLeaf hij μ x := by
      rw [hT.map_eq]
      exact heq
    have heqT : ∀ᵐ x ∂μ, κ (T x) = intrinsicRootLeaf hij μ (T x) :=
      ae_of_ae_map hT.measurable.aemeasurable heqmap
    filter_upwards [heq, heqT,
      ae_intrinsicRootLeaf_canonical d hij μ hA (Real.log c)] with x hx hTx hcq
    rw [hTx, hx]
    simpa only [Real.exp_log hc, T] using hcq)
  filter_upwards [heq, H] with x hx h
  simpa only [hx] using h

end DukePrimeDegree

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootTranslateBox
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Translation covariance of root boxes

A measure-preserving root translation transports the actual coordinate
measure and its disintegration. This is the local input for identifying
invariant root conditionals with Lebesgue measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets
open PrimeDegreePackets.RootBox
namespace RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma translate_domain (B : PrimeDegreePackets.RootBox hij k) (a : ℝ) :
    (translate B a).domain = timeTranslation a '' B.domain := by
  ext z
  constructor
  · rintro ⟨hs, t, ht, he⟩
    exact ⟨(z.1, t), ⟨hs, ht⟩, Prod.ext rfl he⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz.1, z.2, hz.2, rfl⟩

theorem translate_coordinateMeasure (B : PrimeDegreePackets.RootBox hij k)
    (a : ℝ) (μ : Measure (X n))
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    (translate B a).coordinateMeasure μ = (B.coordinateMeasure μ).map (timeTranslation a) := by
  let E := timeTranslation (i := i) (j := j) (k := k) a
  let H := rightActionHomeomorph (Matrix.SpecialLinearGroup.transvection hij a)
  have hμ (S : Set (X n)) : μ (H '' S) = μ S := by
    calc
      μ (H '' S) = (μ.map H) (H '' S) := congrArg (fun ν => ν (H '' S)) hinv.symm
      _ = μ S := by
        rw [H.isOpenEmbedding.measurableEmbedding.map_apply, H.injective.preimage_image]
  ext S hS
  rw [Measure.map_apply E.continuous.measurable hS,
    PrimeDegreePackets.RootBox.coordinateMeasure_apply _ μ hS,
    PrimeDegreePackets.RootBox.coordinateMeasure_apply _ μ (E.continuous.measurable hS),
    translate_domain]
  rw [← hμ (rootQuotientParametrization hij '' (E ⁻¹' S ∩ B.domain))]
  congr 1
  ext x
  constructor
  · rintro ⟨z, ⟨hzS, w, hw, rfl⟩, rfl⟩
    exact ⟨rootQuotientParametrization hij w, ⟨w, ⟨hzS, hw⟩, rfl⟩,
      (rootQuotientParametrization_add hij w.1 w.2 a).symm⟩
  · rintro ⟨_, ⟨w, ⟨hwS, hw⟩, rfl⟩, rfl⟩
    exact ⟨E w, ⟨hwS, ⟨w, hw, rfl⟩⟩, rootQuotientParametrization_add hij w.1 w.2 a⟩

theorem translate_marginal (B : PrimeDegreePackets.RootBox hij k)
    (a : ℝ) (μ : Measure (X n))
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ((translate B a).coordinateMeasure μ).fst = (B.coordinateMeasure μ).fst := by
  rw [translate_coordinateMeasure B a μ hinv]
  have h := fst_map_measurableEquiv (B.coordinateMeasure μ)
    (MeasurableEquiv.refl (RootSlice i j k)) (Homeomorph.addRight a).toMeasurableEquiv
  change ((B.coordinateMeasure μ).map (timeTranslation a)).fst =
    ((B.coordinateMeasure μ).fst).map id at h
  simpa only [Measure.map_id] using h

theorem translate_conditionalKernel (B : PrimeDegreePackets.RootBox hij k)
    (a : ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      (translate B a).conditionalKernel μ s =
        (B.conditionalKernel μ s).map (Homeomorph.addRight a) := by
  simp only [PrimeDegreePackets.RootBox.conditionalKernel, translate_coordinateMeasure B a μ hinv]
  exact condKernel_map_measurableEquiv (B.coordinateMeasure μ)
    (MeasurableEquiv.refl (RootSlice i j k)) (Homeomorph.addRight a).toMeasurableEquiv

end RootBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootTranslateLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Translation covariance of the global normalized root leaf

Long root boxes extend the local disintegration identity to the whole
real root line. Centering cancels the translation, so a preserving root
translation fixes the intrinsic normalized leaf almost everywhere.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
open PrimeDegreePackets.RootBox
namespace RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

theorem ae_leafMeasure_translate (A : PrimeDegreePackets.RootBox hij k)
    (R S a : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (hAS : (translate A a).time ⊆ rootLeafWindow S 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      (translate A a).leafMeasure S μ s =
        (A.leafMeasure R μ s).map (Homeomorph.addRight a) := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  let f := Homeomorph.addRight a
  let AT := translate A a
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hincT (m : ℕ) (B : C m) : AT.time ⊆ (translate B.val a).time :=
    image_mono (hinc m B)
  have hcov : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse → (translate B.val a).conditionalKernel μ s =
        (B.val.conditionalKernel μ s).map f := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    exact PrimeDegreePackets.RootBox.base_ae_of_ae A B.val (hinc m B) μ
      (translate_conditionalKernel B.val a μ hinv)
  have htrans : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
      (AT.leafMeasure S μ s).restrict (f '' B.val.time) =
        (anchorNormalize ((translate B.val a).conditionalKernel μ s)
          (f '' A.time)).restrict (f '' B.val.time) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    have H := AT.ae_leafMeasure_restrict S hAS μ hfree (translate B.val a) (hincT m B)
    rw [translate_marginal A a μ hinv] at H
    exact H.mono fun s hs hsB => (hs hsB).2
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,
    A.ae_injective_root_slice_of_ae_free μ hfree, hcov, htrans] with s hs hi hc ht
  apply measure_eq_of_restrictionChain (fun m => f '' rootLeafWindow R m)
    (fun p q hpq => image_mono (rootLeafWindow_mono R hpq))
    (by rw [← image_iUnion, rootLeafWindow_cover, image_univ, f.surjective.range_eq])
  intro m
  obtain ⟨B, hBC, hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
  let B' : C m := ⟨B, hBC⟩
  have H := ht m B' hsB
  rw [hc m B' hsB] at H
  have ha : anchorNormalize ((B.conditionalKernel μ s).map f) (f '' A.time) =
      (anchorNormalize (B.conditionalKernel μ s) A.time).map f :=
    anchorNormalize_map_equiv (B.conditionalKernel μ s) f.toMeasurableEquiv A.time
  change (AT.leafMeasure S μ s).restrict (f '' B.time) =
    (anchorNormalize ((B.conditionalKernel μ s).map f) (f '' A.time)).restrict (f '' B.time) at H
  rw [ha] at H
  change (AT.leafMeasure S μ s).restrict (f '' rootLeafWindow R m) =
    ((A.leafMeasure R μ s).map f).restrict (f '' rootLeafWindow R m)
  have hmap (ν : Measure ℝ) (J : Set ℝ) :
      (ν.map f).restrict (f '' J) = (ν.restrict J).map f := by
    exact (f.toMeasurableEquiv.restrict_map ν (f '' J)).trans
      (congrArg (fun T : Set ℝ => (ν.restrict T).map f) (f.injective.preimage_image J))
  rw [hmap, hs.2.2.2 m B hBC hsB]
  rw [hmap] at H
  simpa only [rootLongBoxFamily_time hij k R m B hBC] using H

lemma translate_time_bound (A : PrimeDegreePackets.RootBox hij k) (R a : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0) :
    (translate A a).time ⊆ rootLeafWindow (R + |a|) 0 := by
  rintro _ ⟨t, ht, rfl⟩
  have hh := hAR ht
  simp only [rootLeafWindow, Nat.cast_zero, add_zero, mem_Ioo] at hh ⊢
  change -(R + |a|) < t + a ∧ t + a < R + |a|
  constructor <;> linarith [neg_abs_le a, le_abs_self a]

lemma ae_basedLeaf_translate (A : PrimeDegreePackets.RootBox hij k) (R a : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      (translate A a).basedLeaf (R + |a|) μ (timeTranslation a z) = A.basedLeaf R μ z := by
  have H := ae_of_ae_map measurable_fst.aemeasurable
    (ae_leafMeasure_translate A R (R + |a|) a hAR (translate_time_bound A R a hAR) μ hfree hinv)
  filter_upwards [H] with z hz
  change basedRealMeasure ((translate A a).leafMeasure _ μ z.1) (z.2 + a) = _
  rw [hz]
  exact basedRealMeasure_translate _ _ _

lemma ae_intrinsicRootLeaf_translate_restrict (A : PrimeDegreePackets.RootBox hij k)
    (R a : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ.restrict A.range, intrinsicRootLeaf hij μ
      (rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = intrinsicRootLeaf hij μ x := by
  apply A.ae_of_coordinate μ
  have HT := (translate A a).ae_intrinsicRootLeaf_coordinates
    (R + |a|) (translate_time_bound A R a hAR) μ hfree
  rw [translate_coordinateMeasure A a μ hinv] at HT
  have HT' := ae_of_ae_map (timeTranslation a).measurable.aemeasurable HT
  filter_upwards [HT', A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
    ae_basedLeaf_translate A R a hAR μ hfree hinv] with z ht ha hc
  change intrinsicRootLeaf hij μ (rootQuotientParametrization hij (z.1, z.2 + a)) = _ at ht
  rw [rootQuotientParametrization_add] at ht
  exact ht.trans (hc.trans ha.symm)

end RootBox

/-- A preserving root translation fixes the normalized intrinsic leaf. -/
theorem ae_intrinsicRootLeaf_translate {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a : ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ
      (rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = intrinsicRootLeaf hij μ x := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr
    (fun B => RootBox.ae_intrinsicRootLeaf_translate_restrict B.val.box B.val.radius a
      B.val.time_bound μ hfree hinv)
  simpa only [boundedRootAtlas_iUnion, Measure.restrict_univ] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootInvariantLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Lebesgue normalization for invariant roots

A preserving root action fixes its intrinsic leaf. The pointwise rebasing
law turns this into projective translation periods; diagonal covariance
removes their multipliers. Arbitrarily small periods identify Lebesgue
measure, giving the exact mean information coefficient one.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA in
lemma ae_based_fixed_of_root_invariant (a : ℝ)
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ, basedRealMeasure (intrinsicRootLeaf hij μ x) a = intrinsicRootLeaf hij μ x := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  obtain ⟨N, hN, hz, hrebase⟩ := exists_nullset_root_orbit_rebase d hij μ hA
  have hn : ∀ᵐ x ∂μ, x ∉ N := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hz
  have hpre : ∀ᵐ x ∂μ, rightAction x (Matrix.SpecialLinearGroup.transvection hij a) ∉ N := by
    have hm : ∀ᵐ y ∂μ.map (fun x => rightAction x
        (Matrix.SpecialLinearGroup.transvection hij a)), y ∉ N := by rwa [hinv]
    exact ae_of_ae_map (continuous_rightAction
      (Matrix.SpecialLinearGroup.transvection hij a)).measurable.aemeasurable hm
  filter_upwards [hn, hpre, ae_intrinsicRootLeaf_translate hij a μ hfree hinv] with x hx htx he
  exact (hrebase x hx a htx).symm.trans he

include hA in
/-- Every invariant root has translation-invariant intrinsic conditionals. -/
theorem ae_rootLeaf_invariant_of_root_invariant
    (hinv : ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ, ∀ a : ℝ,
      (intrinsicRootLeaf hij μ x).map (fun t => t + a) = intrinsicRootLeaf hij μ x := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have hfixed : ∀ᵐ x ∂μ, ∀ k : ℕ,
      basedRealMeasure (intrinsicRootLeaf hij μ x) (-(1 / ((k : ℝ) + 1))) =
        intrinsicRootLeaf hij μ x :=
    ae_all_iff.mpr fun k => ae_based_fixed_of_root_invariant d hij μ hA _ (hinv _)
  filter_upwards [hfixed, ae_intrinsicRootLeaf_spec hij μ hfree,
    ae_intrinsic_projective_multiplier_zero d hij μ hA] with x hx hs hm
  let ν := intrinsicRootLeaf hij μ x
  let : IsLocallyFiniteMeasure ν := hs.1
  apply realLeaf_invariant_of_small_periods ν
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  let a : ℝ := 1 / ((k : ℝ) + 1)
  have hp := projectivePeriod_of_based_fixed ν hs.2 (-a) (hx k)
  have hz := hm _ hp
  have hper := leaf_period_of_projective_multiplier_zero ν _ hp hz
  refine ⟨a, ?_, by dsimp [a] <;> positivity, hk⟩
  simpa only [neg_neg] using hper

include hA in
/-- Unit mass on the unit ball fixes the Haar scalar to one half. -/
theorem ae_rootLeaf_eq_half_volume
    (hinv : ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = (2 : ℝ≥0∞)⁻¹ • (volume : Measure ℝ) := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [ae_intrinsicRootLeaf_spec hij μ hfree,
    ae_rootLeaf_invariant_of_root_invariant d hij μ hA hinv] with x hs hi
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) := hs.1
  obtain ⟨c, hc, hcV⟩ := normalized_translation_invariant_measure
    (intrinsicRootLeaf hij μ x) (Metric.ball 0 1) hs.2 hi
  rw [hc, ENNReal.smul_def, hcV, Real.volume_ball]
  norm_num

include hA in
theorem ae_rootInformation_of_invariant
    (hinv : ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) (t : ℝ) :
    ∀ᵐ x ∂μ, rootInformation hij μ t x = t := by
  filter_upwards [ae_rootLeaf_eq_half_volume d hij μ hA hinv] with x hx
  change -Real.log ((intrinsicRootLeaf hij μ x) (Metric.ball 0 (Real.exp (-t)))).toReal = t
  rw [hx, Measure.smul_apply, smul_eq_mul, Real.volume_ball,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have he : (2 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp (-t))) =
      ENNReal.ofReal (Real.exp (-t)) := by
    rw [ENNReal.ofReal_ofNat, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul]
  rw [he, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp, neg_neg]

include hA in
/-- Haar root conditionals give coefficient one in the actual leaf information. -/
theorem rootInformationMean_of_invariant [IsProbabilityMeasure μ]
    (hinv : ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) (t : ℝ) :
    rootInformationMean hij μ t = ENNReal.ofReal t := by
  unfold rootInformationMean
  have he : (fun x => ENNReal.ofReal (rootInformation hij μ t x)) =ᵐ[μ]
      fun _ => ENNReal.ofReal t :=
    (ae_rootInformation_of_invariant d hij μ hA hinv t).mono fun _ h => congrArg ENNReal.ofReal h
  rw [lintegral_congr_ae he]
  simp

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CanonicalRootBasic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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

include hA

lemma canonicalRootCoefficient_one_of_invariant_oai (i j : Fin (d + 1)) (hij : i ≠ j)
    (hinv : ∀ t : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij t)) = μ) :
    canonicalRootCoefficient d μ i j = 1 := by
  rw [canonicalRootCoefficient, dite_eq_right hij, rootInformationMean_of_invariant d hij μ hA hinv]
  norm_num

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.canonicalRootCoefficient_one_of_invariant_oai := @OAI.DukePrimeDegree.canonicalRootCoefficient_one_of_invariant_oai
