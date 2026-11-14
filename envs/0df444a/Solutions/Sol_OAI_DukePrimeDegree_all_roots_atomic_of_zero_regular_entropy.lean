-- Prove2me | solution 1 for OAI.DukePrimeDegree.all_roots_atomic_of_zero_regular_entropy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:45.384601+00:00
-- url     : https://prove2.me/submissions/6f6d45c9-23f7-4a10-a7e9-0324e54eea3b

import Mathlib
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Basic
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
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.PartialSups
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke044
import Theorems.Thm_OAI_DukePrimeDegree_atomic_positive_root_of_zero_entropy

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ShannonEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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
namespace PrimeDegreePackets

lemma observationEntropy_equiv {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) (P : Y → α) (e : α ≃ β) :
    observationEntropy μ (fun y => e (P y)) = observationEntropy μ P := by
  classical
  unfold observationEntropy finiteShannon
  rw [← e.sum_comp]
  simp only [Equiv.apply_eq_iff_eq]

lemma observationEntropy_comp_preserving {Y α : Type*} [MeasurableSpace Y]
    [Fintype α] (μ : Measure Y) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) {S : Y → Y} (hS : MeasurePreserving S μ μ) :
    observationEntropy μ (fun y => P (S y)) = observationEntropy μ P := by
  unfold observationEntropy finiteShannon
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (μ (S ⁻¹' {y | P y = a})).toReal = (μ {y | P y = a}).toReal
  rw [hS.measure_preimage (hP a).nullMeasurableSet]


lemma orbitName_measurable_fiber {Y α : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {P : Y → α}
    (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) (a : Fin N → α) :
    MeasurableSet {y | orbitName T P N y = a} := by
  have heq : {y | orbitName T P N y = a} = ⋂ j : Fin N, {y | P (T^[j] y) = a j} := by
    ext y
    simp [orbitName,funext_iff]
  rw [heq]
  exact MeasurableSet.iInter fun j => (hP (a j)).preimage (hT.iterate j)

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootRelations
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets

lemma observationEntropy_map {Y Z α : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [Fintype α] (μ : Measure Y) (f : Y → Z) (hf : Measurable f)
    (P : Z → α) (hP : ∀ a, MeasurableSet {z | P z = a}) :
    observationEntropy (Measure.map f μ) P = observationEntropy μ (P ∘ f) := by
  unfold observationEntropy finiteShannon
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (Measure.map f μ {z | P z = a}).toReal = _
  rw [Measure.map_apply hf (hP a)]
  rfl

lemma orbitName_semiconj {Y Z α : Type*} (f : Y → Z) (S : Y → Y) (T : Z → Z)
    (h : ∀ y, f (S y) = T (f y)) (P : Z → α) (N : ℕ) :
    orbitName T P N ∘ f = orbitName S (P ∘ f) N := by
  have H (n : ℕ) (y : Y) : f (S^[n] y) = T^[n] (f y) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply',h,ih]
  ext y j
  exact congrArg P (H j.val y).symm

lemma observationEntropyRate_map_semiconj {Y Z α : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z] [Fintype α]
    (μ : Measure Y) (f : Y → Z) (hf : Measurable f)
    (S : Y → Y) (T : Z → Z) (hT : Measurable T)
    (h : ∀ y, f (S y) = T (f y))
    (P : Z → α) (hP : ∀ a, MeasurableSet {z | P z = a}) :
    observationEntropyRate (Measure.map f μ) T P =
      observationEntropyRate μ S (P ∘ f) := by
  unfold observationEntropyRate
  congr 3
  funext N
  rw [observationEntropy_map μ f hf _ (orbitName_measurable_fiber hT hP N),
    orbitName_semiconj f S T h P N]

 
theorem measureEntropy_map_semiconj_le {Y Z : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure Y) (f : Y → Z) (hf : Measurable f)
    (S : Y → Y) (T : Z → Z) (hT : Measurable T)
    (h : ∀ y, f (S y) = T (f y)) :
    measureEntropy (Measure.map f μ) T ≤ measureEntropy μ S := by
  unfold measureEntropy
  refine iSup_le fun k => iSup_le fun P => iSup_le fun hP => ?_
  rw [observationEntropyRate_map_semiconj μ f hf S T hT h P hP]
  apply le_iSup_of_le k
  apply le_iSup_of_le (P ∘ f)
  exact le_iSup_of_le (fun a => (hP a).preimage hf) le_rfl

end PrimeDegreePackets


open scoped Topology Classical ENNReal

open scoped Matrix Topology Classical
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeDuality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets
open ThetaConstruction

lemma restoredLogCoordinates_sum {d : ℕ} (u : LogCoordinates d) :
    ∑ i, restoredLogCoordinates u i = 0 := by
  simp [restoredLogCoordinates,Fin.sum_univ_castSucc]

end PrimeDegreePackets


open MeasureTheory Module WithLp

open scoped BigOperators NumberField nonZeroDivisors ENNReal
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

lemma ae_coordinate_of_ambient (A : RootBox hij k) (μ : Measure (X n))
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂A.coordinateMeasure μ, P (rootQuotientParametrization hij z) := by
  have H : ∀ᵐ x ∂μ.restrict A.range, P x := ae_restrict_of_ae hp
  rw [←A.map_coordinateMeasure μ] at H
  exact ae_of_ae_map (rootQuotientParametrization_localHomeomorph hij).continuous.measurable.aemeasurable H

 

theorem ae_leafMeasure_of_ambient (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.leafMeasure R μ s,
      P (rootQuotientParametrization hij (s,t)) := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have HD (D : RootBox hij k) : ∀ᵐ s ∂(D.coordinateMeasure μ).fst,
      ∀ᵐ t ∂D.conditionalKernel μ s, P (rootQuotientParametrization hij (s,t)) := by
    have H : ∀ᵐ z ∂(D.coordinateMeasure μ).fst ⊗ₘ D.conditionalKernel μ,
        P (rootQuotientParametrization hij z) := by
      simpa only [conditionalKernel,Measure.disintegrate] using D.ae_coordinate_of_ambient μ hp
    exact Measure.ae_ae_of_ae_compProd H
  have H (m : ℕ) (B : C m) : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      s ∈ B.val.transverse → ∀ᵐ t ∂(A.leafMeasure R μ s).restrict (rootLeafWindow R m),
        P (rootQuotientParametrization hij (s,t)) := by
    filter_upwards [A.ae_leafMeasure_restrict R hAR μ hfree B.val (hinc m B),
      A.base_ae_of_ae B.val (hinc m B) μ (HD B.val)] with s hs hd hsb
    have hh := ae_restrict_of_ae (s := B.val.time) (Measure.ae_smul_measure (hd hsb)
      ((B.val.conditionalKernel μ s A.time)⁻¹))
    change ∀ᵐ t ∂(anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict B.val.time,
      P (rootQuotientParametrization hij (s,t)) at hh
    rw [←(hs hsb).2,hT m B] at hh
    exact hh
  have Hall := ae_all_iff.mpr (fun m => ae_all_iff.mpr (H m))
  filter_upwards [Hall,A.ae_injective_root_slice_of_ae_free μ hfree] with s hs hi
  have HW (m : ℕ) : ∀ᵐ t ∂(A.leafMeasure R μ s).restrict (rootLeafWindow R m),
      P (rootQuotientParametrization hij (s,t)) := by
    obtain ⟨B,hBC,hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
    exact hs m ⟨B,hBC⟩ hsB
  have HH := (ae_restrict_iUnion_iff (μ := A.leafMeasure R μ s) (rootLeafWindow R) _).mpr HW
  simpa only [rootLeafWindow_cover,Measure.restrict_univ] using HH

lemma ae_basedLeaf_of_ambient (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ᵐ t ∂A.basedLeaf R μ z,
      P (rightAction (rootQuotientParametrization hij z)
        (Matrix.SpecialLinearGroup.transvection hij t)) := by
  have H := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_of_ambient R hAR μ hfree hp)
  filter_upwards [H] with z hz
  apply Measure.ae_smul_measure
  apply (Homeomorph.subRight z.2).measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hz] with t ht
  change P (rightAction (rootQuotientParametrization hij z)
    (Matrix.SpecialLinearGroup.transvection hij (t-z.2)))
  rw [←rootQuotientParametrization_add]
  simpa only [←add_sub_assoc,add_sub_cancel_left] using ht

end RootBox

 

theorem ae_intrinsicRootLeaf_of_ambient {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂μ, ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      P (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H (B : boundedRootAtlas hij) : ∀ᵐ x ∂μ.restrict B.val.box.range,
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        P (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) := by
    apply B.val.box.ae_of_coordinate μ
    filter_upwards [B.val.box.ae_intrinsicRootLeaf_coordinates B.val.radius B.val.time_bound μ hfree,
      B.val.box.ae_basedLeaf_of_ambient B.val.radius B.val.time_bound μ hfree hp] with z he hz
    rwa [he]
  have HH := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr H
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using HH

end PrimeDegreePackets


open scoped Topology ENNReal
namespace PrimeDegreePackets

lemma centerRealMeasure_singleton (ν : Measure ℝ) (t u : ℝ) :
    centerRealMeasure ν t {u} = ν {u+t} := by
  rw [centerRealMeasure,Measure.map_apply (Homeomorph.subRight t).measurable (measurableSet_singleton u)]
  congr 1
  ext v
  simp only [Set.mem_preimage,mem_singleton_iff,Homeomorph.coe_subRight]
  exact sub_eq_iff_eq_add

end PrimeDegreePackets

open scoped Matrix Topology ENNReal ProbabilityTheory
end
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
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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

lemma based_dirac_eq_self_only_at_zero (t : ℝ)
    (h : basedRealMeasure (Measure.dirac 0) t = Measure.dirac 0) : t = 0 := by
  by_contra ht
  have he := congrArg (fun ν : Measure ℝ => ν {0}) h
  change (centerRealMeasure (Measure.dirac 0) t (Metric.ball 0 1))⁻¹ *
    centerRealMeasure (Measure.dirac 0) t {0} = (Measure.dirac 0) {0} at he
  rw [centerRealMeasure_singleton, zero_add] at he
  simp [Ne.symm ht] at he

theorem exists_nullset_atomic_root_transversal
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hatom : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧ ∀ x ∉ N, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∉ N → t = 0 := by
  obtain ⟨N, hN, hNzero, hrebase⟩ := exists_nullset_root_orbit_rebase d hij μ hA
  obtain ⟨M, hbad, hM, hMzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hatom)
  refine ⟨N ∪ M, hN.union hM, measure_union_null hNzero hMzero, ?_⟩
  intro x hx t hy
  have hxatom : intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
    by_contra h
    exact hx (Or.inr (hbad h))
  have hyatom : intrinsicRootLeaf hij μ
      (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) = Measure.dirac 0 := by
    by_contra h
    exact hy (Or.inr (hbad h))
  apply based_dirac_eq_self_only_at_zero
  simpa only [hxatom, hyatom] using
    (hrebase x (fun h => hx (Or.inl h)) t (fun h => hy (Or.inl h))).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_EntropyInverse
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Time reversal of entropy

Reversing a finite orbit name and shifting its starting point does not
change its Shannon entropy. This proves equality of
Kolmogorov--Sinai entropy for mutually inverse measure-preserving maps,
as used in EKL (2006), equation (3.2).
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma inverse_orbitName {Y α : Type*} (T S : Y → Y)
    (hST : Function.LeftInverse S T) (P : Y → α) (N : ℕ) (y : Y) :
    orbitName S P N (T^[N - 1] y) =
      reverseWordEquiv α N (orbitName T P N y) := by
  funext j
  change P (S^[j.val] (T^[N - 1] y)) = P (T^[j.rev.val] y)
  congr 1
  have hN : N - 1 = j.val + (N - 1 - j.val) := by omega
  rw [hN, Function.iterate_add_apply]
  rw [(hST.iterate j.val) _]
  rw [Fin.val_rev]
  exact congrArg (fun m : ℕ => T^[m] y) (by omega)

/-- Finite block entropies agree exactly under time reversal. -/
theorem orbitEntropy_inverse {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (T S : Y → Y)
    (hT : MeasurePreserving T μ μ) (hS : Measurable S)
    (hST : Function.LeftInverse S T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) :
    observationEntropy μ (orbitName S P N) =
      observationEntropy μ (orbitName T P N) := by
  calc
    observationEntropy μ (orbitName S P N) =
        observationEntropy μ (fun y => orbitName S P N (T^[N - 1] y)) :=
      (observationEntropy_comp_preserving μ _
        (orbitName_measurable_fiber hS hP N) (hT.iterate (N - 1))).symm
    _ = observationEntropy μ (fun y => reverseWordEquiv α N (orbitName T P N y)) := by
      congr 1
      funext y
      exact inverse_orbitName T S hST P N y
    _ = _ := observationEntropy_equiv μ _ _

/-- Equality holds for every finite observation, before taking the supremum. -/
theorem observationEntropyRate_inverse {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (T S : Y → Y)
    (hT : MeasurePreserving T μ μ) (hS : Measurable S)
    (hST : Function.LeftInverse S T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    observationEntropyRate μ S P = observationEntropyRate μ T P := by
  unfold observationEntropyRate
  congr 2
  funext N
  rw [orbitEntropy_inverse μ T S hT hS hST P hP]

/-- Entropy is invariant under reversing an invertible measure-preserving map. -/
theorem measureEntropy_inverse {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (T S : Y → Y)
    (hT : MeasurePreserving T μ μ) (hS : Measurable S)
    (hST : Function.LeftInverse S T) :
    measureEntropy μ S = measureEntropy μ T := by
  unfold measureEntropy
  congr 1
  funext k
  congr 1
  funext P
  congr 1
  funext hP
  rw [observationEntropyRate_inverse μ T S hT hS hST P hP]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_DiagonalEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entropy symmetry for the actual diagonal action

The time-reversal theorem applies to right translations by diagonal
matrices. The final lemma combines it with the precise positive-root
entropy formula of EKL (2006), Proposition 3.1(3). That formula remains
an explicit hypothesis here; time reversal and the coefficient balance
are proved.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Time reversal for the diagonal action on the arithmetic quotient. -/
theorem diagonal_entropy_neg (d : ℕ)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0)
    (μ : Measure (X (d + 1)))
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (t : ℝ) :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-t))) =
      measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell t)) := by
  apply measureEntropy_inverse
  · refine ⟨(continuous_rightAction _).measurable, ?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  · exact (continuous_rightAction _).measurable
  · intro x
    change rightAction (rightAction x (diagonalOneParameter ell hell t))
      (diagonalOneParameter ell hell (-t)) = x
    rw [rightAction_mul, diagonalOneParameter_neg]
    simp

lemma diagonalOneParameter_neg_weights {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ) :
    diagonalOneParameter (fun i => -ell i)
      (by simp only [Finset.sum_neg_distrib, hell, neg_zero]) t =
      diagonalOneParameter ell hell (-t) := by
  apply Subtype.ext
  change Matrix.diagonal (fun i => Real.exp (-ell i * t)) =
    Matrix.diagonal (fun i => Real.exp (ell i * -t))
  congr 1
  funext i
  congr 1
  ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeylReindex
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Permuting coordinates on the arithmetic quotient

Coordinate reversal transfers the increasing regular weight construction
to its decreasing counterpart. Reindexing preserves determinant one and
the integral lattice, so it acts on the actual quotient.
-/

noncomputable section
open Matrix MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

lemma quotientReindex_rightAction {n : ℕ} (e : Equiv.Perm (Fin n))
    (x : X n) (g : G n) :
    quotientReindex e (rightAction x g) =
      rightAction (quotientReindex e x) (reindexSpecialLinear ℝ e g) := by
  induction x using Quotient.inductionOn with
  | h a => exact congrArg (Quotient.mk _) ((reindexSpecialLinear ℝ e).map_mul a g)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WeylEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy under coordinate permutations of the quotient -/

noncomputable section
open MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem measureEntropy_map_measurableEquiv {Y Z : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure Y) (e : Y ≃ᵐ Z) (S : Y → Y) (T : Z → Z)
    (hS : Measurable S) (hT : Measurable T)
    (h : ∀ y, e (S y) = T (e y)) :
    measureEntropy (μ.map e) T = measureEntropy μ S := by
  apply le_antisymm
  · exact measureEntropy_map_semiconj_le μ e e.measurable S T hT h
  · have hi (z : Z) : e.symm (T z) = S (e.symm z) := by
      apply e.injective
      simpa only [e.apply_symm_apply] using (h (e.symm z)).symm
    have H := measureEntropy_map_semiconj_le (μ.map e) e.symm e.symm.measurable T S hS hi
    have hmap : (μ.map e).map e.symm = μ := by
      rw [Measure.map_map e.symm.measurable e.measurable]
      have he : e.symm ∘ e = id := by funext y; exact e.symm_apply_apply y
      rw [he, Measure.map_id]
    rwa [hmap] at H

lemma reindex_diagonalOneParameter {n : ℕ} (e : Equiv.Perm (Fin n))
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ) :
    reindexSpecialLinear ℝ e (diagonalOneParameter ell hell t) =
      diagonalOneParameter (fun i => ell (e.symm i)) (permutedWeight_sum e ell hell) t := by
  apply Subtype.ext
  ext i j
  change (Matrix.diagonal (fun k => Real.exp (ell k * t))) (e.symm i) (e.symm j) =
    (Matrix.diagonal (fun k => Real.exp (ell (e.symm k) * t))) i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ (fun h => hij (e.symm.injective h)),
      Matrix.diagonal_apply_ne _ hij]

theorem diagonal_entropy_reindex (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (μ : Measure (X (d+1))) (ell : Fin (d+1) → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) :
    measureEntropy (μ.map (quotientReindex e))
      (fun x => rightAction x (diagonalOneParameter
        (fun i => ell (e.symm i)) (permutedWeight_sum e ell hell) t)) =
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell t)) := by
  exact measureEntropy_map_measurableEquiv μ (quotientReindexHomeomorph e).toMeasurableEquiv
    _ _ (continuous_rightAction _).measurable (continuous_rightAction _).measurable
    (fun x => by
      change quotientReindex e (rightAction x _) = rightAction (quotientReindex e x) _
      rw [quotientReindex_rightAction, reindex_diagonalOneParameter])

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootAtomicTransversal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intrinsic atomicity characterized by a full-measure root transversal -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem intrinsicRootLeaf_dirac_of_nullset_transversal {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t)=x → t=0)
    (N : Set (X n)) (hNzero : μ N=0)
    (htrans : ∀ x ∉ N, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∉ N → t=0) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x=Measure.dirac 0 := by
  have hN : ∀ᵐ x ∂μ, x ∉ N := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hNzero
  have hleaf := ae_intrinsicRootLeaf_of_ambient hij μ hfree hN
  filter_upwards [hN,hleaf,ae_intrinsicRootLeaf_spec hij μ hfree] with x hx hl hs
  let ν := intrinsicRootLeaf hij μ x
  have hz : ∀ᵐ t ∂ν, t=0 := hl.mono (fun t ht => htrans x hx t ht)
  have hunit : ν {0}=1 := by
    calc
      ν {0}=ν (Metric.ball 0 1) := measure_congr (hz.mono (by
        intro t ht
        subst t
        show ((0:ℝ) ∈ ({0} : Set ℝ)) = ((0:ℝ) ∈ Metric.ball (0:ℝ) 1)
        simp))
      _=1 := hs.2
  apply Measure.ext
  intro S hS
  by_cases hzero : (0:ℝ) ∈ S
  · have he : ν S=ν {0} := measure_congr (hz.mono (by
      intro t ht
      subst t
      show ((0:ℝ) ∈ S) = ((0:ℝ) ∈ ({0} : Set ℝ))
      simp only [hzero,mem_singleton_iff]))
    simp only [ν,he,hunit,Measure.dirac_apply_of_mem hzero]
  · have he : ν S=ν ∅ := measure_congr (hz.mono (by
      intro t ht
      subst t
      show ((0:ℝ) ∈ S) = ((0:ℝ) ∈ (∅ : Set ℝ))
      simp only [hzero,mem_empty_iff_false]))
    simp only [ν,he,measure_empty,Measure.dirac_apply' _ hS,indicator_of_notMem hzero]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_WeylAtomicRoots
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate permutations transport atomic intrinsic root leaves -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

/-- Only the geometric characterization of an atomic leaf is needed;
there is no assumed covariance formula for arbitrary intrinsic leaves. -/
theorem atomic_root_reindex (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (hatom : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x=Measure.dirac 0) :
    ∀ᵐ x ∂μ.map (quotientReindex e),
      intrinsicRootLeaf (e.injective.ne hij) (μ.map (quotientReindex e)) x=Measure.dirac 0 := by
  let E := (quotientReindexHomeomorph e).toMeasurableEquiv
  obtain ⟨N,hN,hN0,htrans⟩ := exists_nullset_atomic_root_transversal d hij μ hA hatom
  have hfree : ∀ᵐ y ∂μ.map E, ∀ t : ℝ,
      rightAction y (Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) t)=y → t=0 := by
    rw [←E.map_ae μ]
    change ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction (E x) (Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) t)=E x → t=0
    filter_upwards [(ae_root_stabilizer_trivial d μ hA).mono
      (fun x hx => hx i j hij)] with x hx
    intro t ht
    apply hx t
    apply E.injective
    change quotientReindex e (rightAction x _) = quotientReindex e x
    rw [quotientReindex_rightAction,reindex_transvection]
    exact ht
  have hN' : (μ.map E) (E '' N)=0 := by
    rw [E.map_apply,E.injective.preimage_image,hN0]
  apply intrinsicRootLeaf_dirac_of_nullset_transversal (e.injective.ne hij) (μ.map E)
    hfree (E '' N) hN'
  intro y hy t ht
  obtain ⟨x,rfl⟩ := E.surjective y
  apply htrans x
  · exact fun hx => hy ⟨x,hx,rfl⟩
  · intro hx
    apply ht
    refine ⟨rightAction x (Matrix.SpecialLinearGroup.transvection hij t),hx,?_⟩
    exact (quotientReindex_rightAction e x _).trans
      (congrArg (rightAction (quotientReindex e x)) (reindex_transvection e hij t))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeylDiagonalAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal invariance and ergodicity under coordinate permutations -/

noncomputable section
open MeasureTheory Set Filter
namespace DukePrimeDegree
open PrimeDegreePackets

lemma reindex_diagonalFlow (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (u : LogCoordinates d) :
    reindexSpecialLinear ℝ e (diagonalFlow u) = diagonalFlow (reindexLogCoordinates d e u) := by
  have hs := restoredLogCoordinates_sum u
  have he : diagonalOneParameter (restoredLogCoordinates u) hs 1=diagonalFlow u := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    congr 1
    funext i
    simp only [restoredLogCoordinates,Fin.snoc_castSucc,mul_one]
  rw [←he,reindex_diagonalOneParameter,diagonalOneParameter_eq_diagonalFlow]
  congr 1
  funext i
  simp only [reindexLogCoordinates,mul_one]

lemma reindex_diagonalFlow_conjugacy (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (u : LogCoordinates d) (x : X (d+1)) :
    quotientReindex e (rightAction x (diagonalFlow u)) =
      rightAction (quotientReindex e x) (diagonalFlow (reindexLogCoordinates d e u)) := by
  rw [quotientReindex_rightAction,reindex_diagonalFlow]

lemma reindex_diagonalFlow_reverse (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (u : LogCoordinates d) (x : X (d+1)) :
    quotientReindex e (rightAction x (diagonalFlow (reindexLogCoordinates d e.symm u))) =
      rightAction (quotientReindex e x) (diagonalFlow u) := by
  apply (quotientReindexHomeomorph e.symm).injective
  change quotientReindex e.symm (quotientReindex e
    (rightAction x (diagonalFlow (reindexLogCoordinates d e.symm u)))) =
      quotientReindex e.symm (rightAction (quotientReindex e x) (diagonalFlow u))
  rw [quotientReindex_symm_apply,reindex_diagonalFlow_conjugacy,
    quotientReindex_symm_apply]

/-- The full diagonal action remains invariant after reindexing. -/
theorem diagonal_invariant_reindex (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (μ : Measure (X (d+1)))
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (u : LogCoordinates d) :
    (μ.map (quotientReindex e)).map (fun x => rightAction x (diagonalFlow u)) =
      μ.map (quotientReindex e) := by
  rw [Measure.map_map (continuous_rightAction _).measurable
    (continuous_quotientReindex e).measurable]
  have he : (fun x => rightAction x (diagonalFlow u)) ∘ quotientReindex e =
      quotientReindex e ∘ (fun x => rightAction x
        (diagonalFlow (reindexLogCoordinates d e.symm u))) := by
    funext x
    exact (reindex_diagonalFlow_reverse d e u x).symm
  rw [he,←Measure.map_map (continuous_quotientReindex e).measurable
    (continuous_rightAction _).measurable,hA]

/-- Ergodicity uses the full diagonal group, whose parameters are permuted
along with the coordinates. -/
theorem diagonal_ergodic_reindex (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (μ : Measure (X (d+1)))
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1))
      (μ.map (quotientReindex e)) := by
  let E := (quotientReindexHomeomorph e).toMeasurableEquiv
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  refine { measure_preimage_smul := ?_, aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  · intro u S hS
    exact (show MeasurePreserving (fun x => rightAction x (diagonalFlow u.toAdd))
      (μ.map (quotientReindex e)) (μ.map (quotientReindex e)) from
      ⟨(continuous_rightAction _).measurable,diagonal_invariant_reindex d e μ hA _⟩).measure_preimage
        hS.nullMeasurableSet
  · intro S hS hfix
    change EventuallyConst S (ae (μ.map E))
    rw [←E.map_ae μ,←eventuallyConst_preimage]
    apply ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq
      (G := Multiplicative (LogCoordinates d)) (hS.preimage E.measurable)
    intro u
    have h := ae_of_ae_map E.measurable.aemeasurable
      (hfix (Multiplicative.ofAdd (reindexLogCoordinates d e u.toAdd))).mem_iff
    filter_upwards [h] with x hx
    apply propext
    change rightAction x (diagonalFlow u.toAdd) ∈ E ⁻¹' S ↔ x ∈ E ⁻¹' S
    change rightAction (quotientReindex e x)
      (diagonalFlow (reindexLogCoordinates d e u.toAdd)) ∈ S ↔ quotientReindex e x ∈ S at hx
    change quotientReindex e (rightAction x (diagonalFlow u.toAdd)) ∈ S ↔
      quotientReindex e x ∈ S
    rw [reindex_diagonalFlow_conjugacy]
    exact hx

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ZeroEntropyAllRoots
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A zero-entropy regular element has atomic leaves in both root directions -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

/-- Time reversal gives zero entropy in the opposite chamber. Reindexing
that chamber lets the same proved positive-root lower bound apply there. -/
theorem all_roots_atomic_of_zero_regular_entropy_oai (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hz : measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1)))=0) :
    ∀ (i j : Fin (d+1)) (hij : i ≠ j), ∀ᵐ x ∂μ,
      intrinsicRootLeaf hij μ x=Measure.dirac 0 := by
  let e : Equiv.Perm (Fin (d+1)) := Fin.revPerm
  let ν := μ.map (quotientReindex e)
  haveI : IsProbabilityMeasure (μ.map (quotientReindex e)) :=
    Measure.isProbabilityMeasure_map (continuous_quotientReindex e).measurable.aemeasurable
  let ellR := fun i => -ell (e.symm i)
  have hsum : ∑ i, ellR i=0 := by
    simp only [ellR,Finset.sum_neg_distrib,Equiv.sum_comp,hell,neg_zero]
  have hgapR (p : allPositiveRoots (d+1)) :
      Real.log 4 ≤ ellR p.val.2-ellR p.val.1 := by
    have hrev : p.val.2.rev < p.val.1.rev :=
      Fin.rev_lt_rev.mpr (Finset.mem_filter.mp p.prop).2
    have hh := hgap ⟨(p.val.2.rev,p.val.1.rev),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hrev⟩⟩
    simpa only [ellR,e,Fin.revPerm_symm,Fin.revPerm_apply,neg_sub_neg] using hh
  let : ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) ν :=
    diagonal_ergodic_reindex d e μ
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hAν (u : LogCoordinates d) : ν.map (fun x => rightAction x (diagonalFlow u))=ν :=
    diagonal_invariant_reindex d e μ hA u
  have hp0 : measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell 1))=0 :=
    (diagonal_entropy_neg d ell hell μ hA 1).symm.trans hz
  have he : diagonalOneParameter ellR hsum (-1) =
      diagonalOneParameter (fun i => ell (e.symm i)) (permutedWeight_sum e ell hell) 1 := by
    simpa only [neg_neg] using
      diagonalOneParameter_neg_weights (fun i => ell (e.symm i))
        (permutedWeight_sum e ell hell) (-1)
  have hzν : measureEntropy ν (fun x => rightAction x (diagonalOneParameter ellR hsum (-1)))=0 := by
    rw [he]
    exact (diagonal_entropy_reindex d e μ ell hell 1).trans hp0
  have hm : ν.map (quotientReindex e.symm)=μ := by
    change (μ.map (quotientReindex e)).map (quotientReindex e.symm)=μ
    rw [Measure.map_map (continuous_quotientReindex e.symm).measurable
      (continuous_quotientReindex e).measurable]
    have hid : quotientReindex e.symm ∘ quotientReindex e=id := by
      funext x
      exact quotientReindex_symm_apply e x
    rw [hid,Measure.map_id]
  intro i j hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact atomic_positive_root_of_zero_entropy d ell hell hgap μ hz hijlt
  · have hrev : e i < e j := by
      change i.rev < j.rev
      exact Fin.rev_lt_rev.mpr hjilt
    have ha := atomic_positive_root_of_zero_entropy d ellR hsum hgapR ν hzν hrev
    have ht := atomic_root_reindex d e.symm (e.injective.ne hij) ν hAν ha
    simpa only [hm,Equiv.symm_apply_apply] using ht

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.all_roots_atomic_of_zero_regular_entropy_oai := @OAI.DukePrimeDegree.all_roots_atomic_of_zero_regular_entropy_oai
