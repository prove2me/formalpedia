-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_atomic_neutral_future_cover
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:50:32.005219+00:00
-- url     : https://prove2.me/submissions/7510bd41-4f31-4e10-a889-63192d09471c

import Mathlib
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
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Composition.MapComap
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
import Theorems.Thm_OAI_DukePrimeDegree_RootPrefixBox_ae_conditionalKernel_eq_dirac_of_atomic_roots

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.conditionalKernel_markov _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_locallyFinite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma matrixBall_isOpen (n : ℕ) (r : ℝ) : IsOpen (matrixBall n r) := by
  simp only [matrixBall, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt _ continuous_const
  exact ((continuous_apply j).comp ((continuous_apply i).comp Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous)).sub
    continuous_const |>.abs

open scoped Matrix
open Matrix

open TopologicalSpace
open scoped Topology

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_InverseEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.conditionalKernel_markov _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_locallyFinite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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
namespace PrimeDegreePackets

lemma matrixBall_mono {n : ℕ} {r s : ℝ} (hrs : r ≤ s) :
    matrixBall n r ⊆ matrixBall n s := by
  intro g hg i j
  exact (hg i j).trans_le hrs



end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
namespace PrimeDegreePackets

lemma one_mem_matrixBall (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (1 : G n) ∈ matrixBall n r := by
  intro i j
  simpa using hr

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_KernelStabilizerMeasurable
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable invariance events for the actual component measures

Equality of finite kernel values is detected by countably many half-line
tests after a measurable embedding in the real line. Consequently both
invariance under one lattice translation and invariance under an entire
root flow are measurable events in the component parameter. The latter
uses rational times and the closedness of the actual measure stabilizer.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma measurableSet_finite_kernel_eq
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [StandardBorelSpace Y] (κ η : Kernel Z Y)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {z | κ z = η z} := by
  let f := embeddingReal Y
  have hf : MeasurableEmbedding f := measurableEmbedding_embeddingReal Y
  let K := κ.map f
  let E := η.map f
  have he (z : Z) : κ z = η z ↔
      K z univ = E z univ ∧ ∀ q : ℚ, K z (Iic (q : ℝ)) = E z (Iic (q : ℝ)) := by
    constructor
    · intro hz
      have hz' : K z = E z := by
        simp only [K, E, Kernel.map_apply _ hf.measurable, hz]
      rw [hz']
      exact ⟨rfl, fun _ => rfl⟩
    · rintro ⟨huniv, hq⟩
      apply hf.map_injective
      rw [← Kernel.map_apply κ hf.measurable, ← Kernel.map_apply η hf.measurable]
      change K z = E z
      apply ext_of_generate_finite _ Real.borel_eq_generateFrom_Iic_rat
        Real.isPiSystem_Iic_rat
      · intro s hs
        simp only [mem_iUnion, mem_singleton_iff] at hs
        obtain ⟨q, rfl⟩ := hs
        exact hq q
      · exact huniv
  have huniv : MeasurableSet {z | K z univ = E z univ} :=
    measurableSet_eq_fun (Kernel.measurable_coe K MeasurableSet.univ)
      (Kernel.measurable_coe E MeasurableSet.univ)
  have hhalf : MeasurableSet {z | ∀ q : ℚ, K z (Iic (q : ℝ)) = E z (Iic (q : ℝ))} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter (fun q : ℚ =>
      measurableSet_eq_fun (Kernel.measurable_coe K (measurableSet_Iic (a := (q : ℝ))))
        (Kernel.measurable_coe E (measurableSet_Iic (a := (q : ℝ)))))
  have hset : {z | κ z = η z} =
      {z | K z univ = E z univ} ∩
        {z | ∀ q : ℚ, K z (Iic (q : ℝ)) = E z (Iic (q : ℝ))} := by
    ext z
    exact he z
  rw [hset]
  exact huniv.inter hhalf

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_TranslationInvariantSlices
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar slices of a measure invariant in its second coordinate

Only relatively compact transverse sets are needed for local product charts.
The transverse measure itself is allowed to be singular.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DukePrimeDegree

variable {Z V : Type*} [MeasurableSpace Z] [MeasurableSpace V]

lemma secondCoordinateSlice_apply (ρ : Measure (Z × V)) (A : Set Z)
    {B : Set V} (hB : MeasurableSet B) :
    secondCoordinateSlice ρ A B=ρ (A ×ˢ B) := by
  rw [secondCoordinateSlice,Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (hB.preimage measurable_snd)]
  congr 1
  ext z
  simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,and_true]
  exact and_comm

theorem secondCoordinateSlice_invariant [Add V] [MeasurableAdd₂ V]
    (ρ : Measure (Z × V)) (A : Set Z) (hA : MeasurableSet A)
    (hinv : ∀ v : V, ρ.map (fun z => (z.1,v+z.2))=ρ) :
    Measure.IsAddLeftInvariant (secondCoordinateSlice ρ A) := by
  constructor
  intro v
  ext B hB
  have hm : Measurable (fun w : V => v+w) := measurable_const.add measurable_id
  have hM : Measurable (fun z : Z × V => (z.1,v+z.2)) :=
    measurable_fst.prodMk (measurable_const.add measurable_snd)
  rw [Measure.map_apply hm hB,secondCoordinateSlice_apply ρ A (hB.preimage hm),
    secondCoordinateSlice_apply ρ A hB]
  have he : A ×ˢ ((fun w : V => v+w) ⁻¹' B)=
      (fun z : Z × V => (z.1,v+z.2)) ⁻¹' (A ×ˢ B) := rfl
  rw [he,←Measure.map_apply hM (hA.prod hB),hinv]

variable [TopologicalSpace Z] [TopologicalSpace V] [BorelSpace Z] [BorelSpace V]
  [T2Space V]

omit [BorelSpace Z] in
theorem secondCoordinateSlice_finiteOnCompacts (ρ : Measure (Z × V))
    [IsFiniteMeasureOnCompacts ρ] {A : Set Z} (hA : IsCompact (closure A)) :
    IsFiniteMeasureOnCompacts (secondCoordinateSlice ρ A) := by
  constructor
  intro B hB
  rw [secondCoordinateSlice_apply ρ A hB.measurableSet]
  exact (measure_mono (Set.prod_mono subset_closure Subset.rfl)).trans_lt
    (hA.prod hB).measure_lt_top

omit [BorelSpace Z] in
theorem secondCoordinateSlice_eq_haar [AddGroup V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V]
    (ρ : Measure (Z × V)) [IsFiniteMeasureOnCompacts ρ]
    {A : Set Z} (hA : MeasurableSet A) (hAc : IsCompact (closure A))
    (hinv : ∀ v : V, ρ.map (fun z => (z.1,v+z.2))=ρ)
    (η : Measure V) [η.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, secondCoordinateSlice ρ A=c • η := by
  let := secondCoordinateSlice_finiteOnCompacts ρ hAc
  let := secondCoordinateSlice_invariant ρ A hA hinv
  exact ⟨_,Measure.isAddLeftInvariant_eq_smul _ _⟩

omit [BorelSpace Z] in
theorem translationInvariant_rectangle [AddGroup V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V]
    (ρ : Measure (Z × V)) [IsFiniteMeasureOnCompacts ρ]
    {A : Set Z} (hA : MeasurableSet A) (hAc : IsCompact (closure A))
    (hinv : ∀ v : V, ρ.map (fun z => (z.1,v+z.2))=ρ)
    (η : Measure V) [η.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, ∀ B : Set V, MeasurableSet B →
      ρ (A ×ˢ B)=(c : ℝ≥0∞)*η B := by
  obtain ⟨c,hc⟩ := secondCoordinateSlice_eq_haar ρ hA hAc hinv η
  refine ⟨c,fun B hB => ?_⟩
  rw [←secondCoordinateSlice_apply ρ A hB,hc,Measure.smul_apply]
  rfl

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_TranslationInvariantProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting off a translation-invariant neutral factor -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DukePrimeDegree

variable {Z V : Type*} [MeasurableSpace Z] [MeasurableSpace V]

lemma firstCoordinateSlice_apply (ρ : Measure (Z × V)) (K : Set V)
    {A : Set Z} (hA : MeasurableSet A) :
    firstCoordinateSlice ρ K A=ρ (A ×ˢ K) := by
  rw [firstCoordinateSlice,Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (hA.preimage measurable_fst)]
  congr 1
  ext z
  simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,true_and]

variable [TopologicalSpace Z] [TopologicalSpace V] [BorelSpace Z] [BorelSpace V]
  [T2Space Z] [T2Space V]

omit [BorelSpace V] [T2Space V] in
theorem firstCoordinateSlice_finiteOnCompacts (ρ : Measure (Z × V))
    [IsFiniteMeasureOnCompacts ρ] {K : Set V} (hK : IsCompact K) :
    IsFiniteMeasureOnCompacts (firstCoordinateSlice ρ K) := by
  constructor
  intro A hA
  rw [firstCoordinateSlice_apply ρ K hA.measurableSet]
  exact (hA.prod hK).measure_lt_top

theorem translationInvariant_eq_product
    [AddGroup V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [SigmaCompactSpace Z]
    (ρ : Measure (Z × V)) [IsFiniteMeasureOnCompacts ρ]
    (hinv : ∀ v : V, ρ.map (fun z => (z.1,v+z.2))=ρ)
    (η : Measure V) [η.IsAddHaarMeasure]
    (K : Set V) (hK : IsCompact K) (hηK : η K=1) :
    ρ=(firstCoordinateSlice ρ K).prod η := by
  let τ := firstCoordinateSlice ρ K
  let := firstCoordinateSlice_finiteOnCompacts ρ hK
  apply Eq.symm
  apply Measure.prod_eq
  intro A B hA hB
  let An : ℕ → Set Z := fun k => A ∩ compactCovering Z k
  have hAn (k : ℕ) : MeasurableSet (An k) :=
    hA.inter (isCompact_compactCovering Z k).measurableSet
  have hAnc (k : ℕ) : IsCompact (closure (An k)) :=
    (isCompact_compactCovering Z k).of_isClosed_subset isClosed_closure
      (closure_minimal inter_subset_right (isCompact_compactCovering Z k).isClosed)
  have hrect (k : ℕ) : ρ (An k ×ˢ B)=τ (An k)*η B := by
    obtain ⟨c,hc⟩ := translationInvariant_rectangle ρ (hAn k) (hAnc k) hinv η
    have ht : τ (An k)=(c : ℝ≥0∞) := by
      rw [firstCoordinateSlice_apply ρ K (hAn k),hc K hK.measurableSet,hηK,mul_one]
    rw [hc B hB,ht]
  have hmono : Monotone An := fun i j hij =>
    inter_subset_inter Subset.rfl (compactCovering_subset Z hij)
  have hunion : (⋃ k, An k)=A := by
    simp only [An,←inter_iUnion,iUnion_compactCovering,inter_univ]
  have hprodmono : Monotone (fun k => An k ×ˢ B) := fun i j hij =>
    Set.prod_mono (hmono hij) Subset.rfl
  have hprodunion : (⋃ k, An k ×ˢ B)=A ×ˢ B := by
    rw [←iUnion_prod_const,hunion]
  calc
    ρ (A ×ˢ B)=⨆ k, ρ (An k ×ˢ B) := by
      rw [←hprodunion,hprodmono.measure_iUnion]
    _ = ⨆ k, τ (An k)*η B := iSup_congr hrect
    _ = (⨆ k, τ (An k))*η B := (ENNReal.iSup_mul _ _).symm
    _ = τ A*η B := by rw [←hmono.measure_iUnion,hunion]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DiracFiberGraph
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common full-measure graph for Dirac fiber conditionals -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree

variable {Z U : Type*} [MeasurableSpace Z] [MeasurableSpace U]
  [StandardBorelSpace U]

lemma measurableSet_kernelDiracGraph (κ : Kernel Z U) [IsFiniteKernel κ] :
    MeasurableSet (kernelDiracGraph κ) := by
  have h := measurableSet_finite_kernel_eq (κ.comap Prod.fst measurable_fst)
    (Kernel.deterministic Prod.snd measurable_snd)
  simpa only [kernelDiracGraph,Kernel.comap_apply,Kernel.deterministic_apply] using h

lemma kernelDiracGraph_fiber_unique (κ : Kernel Z U)
    {x y : Z × U} (hx : x ∈ kernelDiracGraph κ)
    (hy : y ∈ kernelDiracGraph κ) (hbase : x.1=y.1) : x.2=y.2 := by
  apply MeasureTheory.injective_dirac
  exact hx.symm.trans ((congrArg κ hbase).trans hy)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_IndependentGraphSlice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Remove the independent neutral coordinate from a full-measure graph -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree

variable {Z U V : Type*} [MeasurableSpace Z] [MeasurableSpace U] [MeasurableSpace V]

theorem independent_graph_slice
    (ρ : Measure (Z × U)) [SFinite ρ] (η : Measure V) [SFinite η] [NeZero η]
    (E : Set ((Z × U) × V)) (hE : MeasurableSet E)
    (hfull : ∀ᵐ x ∂ρ.prod η, x ∈ E)
    (hunique : ∀ x ∈ E, ∀ y ∈ E,
      x.1.1=y.1.1 → x.2=y.2 → x.1.2=y.1.2) :
    ∃ F : Set (Z × U), MeasurableSet F ∧ (∀ᵐ z ∂ρ, z ∈ F) ∧
      (∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2) ∧
      (∀ᵐ z ∂ρ.prod η, z.1 ∈ F) := by
  have hv : ∀ᵐ v ∂η, ∀ᵐ z ∂ρ, (z,v) ∈ E :=
    (Measure.ae_ae_comm (p := fun z v => (z,v) ∈ E) hE).mp
      (Measure.ae_ae_of_ae_prod hfull)
  obtain ⟨v,hv⟩ := hv.exists
  let F : Set (Z × U) := (fun z => (z,v)) ⁻¹' E
  have hF : MeasurableSet F := hE.preimage measurable_prodMk_right
  refine ⟨F,hF,hv,?_,?_⟩
  · intro x hx y hy hxy
    exact hunique (x,v) hx (y,v) hy hxy rfl
  · apply (Measure.ae_prod_iff_ae_ae (hF.preimage measurable_fst)).mpr
    filter_upwards [hv] with z hz
    exact Filter.Eventually.of_forall fun _ => hz

theorem independent_graph_of_fiber_map
    {S W : Type*} [MeasurableSpace S] [MeasurableSpace W] [StandardBorelSpace W]
    (ρ : Measure (Z × U)) [SFinite ρ] (η : Measure V) [SFinite η] [NeZero η]
    (θ : Measure (S × W)) (κ : Kernel S W) [IsFiniteKernel κ]
    (hatom : ∀ᵐ z ∂θ, κ z.1=Measure.dirac z.2)
    (Φ : (Z × U) × V → S × W) (hΦ : Measurable Φ)
    (hac : (ρ.prod η).map Φ ≪ θ)
    (hbase : ∀ x y, x.1.1=y.1.1 → x.2=y.2 → (Φ x).1=(Φ y).1)
    (hinj : ∀ x y, x.1.1=y.1.1 → x.2=y.2 →
      (Φ x).2=(Φ y).2 → x.1.2=y.1.2) :
    ∃ F : Set (Z × U), MeasurableSet F ∧ (∀ᵐ z ∂ρ, z ∈ F) ∧
      (∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2) ∧
      (∀ᵐ z ∂ρ.prod η, z.1 ∈ F) := by
  let E := Φ ⁻¹' kernelDiracGraph κ
  have hE : MeasurableSet E := (measurableSet_kernelDiracGraph κ).preimage hΦ
  have hfull : ∀ᵐ z ∂ρ.prod η, z ∈ E :=
    ae_of_ae_map hΦ.aemeasurable (hac.ae_le hatom)
  apply independent_graph_slice ρ η E hE hfull
  intro x hx y hy hN hv
  apply hinj x y hN hv
  exact kernelDiracGraph_fiber_unique κ hx hy (hbase x y hN hv)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralUpperRootChart
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Move the neutral coordinate to the right of the root coordinate

The parametrization is now lower-unitriangular, upper-unipotent, diagonal.
Consequently right translation by the diagonal group is translation in the
last coordinate, with the other two coordinates fixed.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma neutralUpperRootParam_eq (n : ℕ)
    (z : UnitDiagonalTransverse n × (UpperRootTime n × transverseNeutralSpace n)) :
    neutralUpperRootParam n z =
      upperRootParam n ((transverseNeutralReconstruct (z.1,z.2.2)).val,
        (completeRootChain n).rootDilation z.2.2.val (-1) z.2.1) := by
  rw [upperRootParam_eq_mul,(completeRootChain n).word_rootDilation _ z.2.2.prop]
  change z.1.val.val*(completeRootChain n).word z.2.1*
    diagonalOneParameter z.2.2.val z.2.2.prop 1 =
    (z.1.val.val*diagonalOneParameter z.2.2.val z.2.2.prop 1)*
      (diagonalOneParameter z.2.2.val z.2.2.prop (-1)*
        (completeRootChain n).word z.2.1*
          diagonalOneParameter z.2.2.val z.2.2.prop (-(-1)))
  rw [neg_neg,diagonalOneParameter_neg]
  group

lemma neutralUpperRootParam_translate (n : ℕ)
    (z : UnitDiagonalTransverse n × (UpperRootTime n × transverseNeutralSpace n))
    (v : transverseNeutralSpace n) :
    neutralUpperRootParam n (z.1,(z.2.1,z.2.2+v)) =
      neutralUpperRootParam n z*diagonalOneParameter v.val v.prop 1 := by
  change z.1.val.val*(completeRootChain n).word z.2.1*
    diagonalOneParameter (z.2.2.val+v.val) _ 1 = _
  rw [diagonalOneParameter_add_weights]
  exact (mul_assoc _ _ _).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralUpperRootHomeomorph
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An actual product chart with neutral translation as its final factor -/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma isOpen_positiveTransverse (n : ℕ) :
    IsOpen {s : UpperRootTransverse n | ∀ i, 0 < s.val.val i i} := by
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (by fun_prop)

lemma neutralUpperRootParam_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (neutralUpperRootParam n) := by
  have hi : Topology.IsOpenEmbedding (fun z : PositiveTransverse n × UpperRootTime n =>
      (z.1.val,z.2)) :=
    (isOpen_positiveTransverse n).isOpenEmbedding_subtypeVal.prodMap
      (Topology.IsOpenEmbedding.id (X := UpperRootTime n))
  have H := (upperRootParam_isOpenEmbedding n).comp
    (hi.comp (neutralUpperRootHomeomorph n).isOpenEmbedding)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact neutralUpperRootParam_eq n z

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientLiftMeasure
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_locallyFinite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_locallyFinite _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.SUnitGroup.instDiscreteTopology_fullLogLattice _root_.SUnitGroup.instDiscreteTopology_reducedLogLattice _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting an arbitrary finite measure through the arithmetic covering

The countable sum over deck transformations restricts on every injective
chart to the original quotient measure. In particular this construction
applies also to singular invariant measures.
-/

noncomputable section
open MeasureTheory Set Function TopologicalSpace
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

lemma quotient_left_integral (n : ℕ) (γ : integralGroup n) (g : G n) :
    Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (γ.val*g)=
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g := by
  apply Quotient.sound
  change QuotientGroup.rightRel (integralGroup n) (γ.val*g) g
  rw [QuotientGroup.rightRel_apply]
  simpa only [mul_inv_rev,←mul_assoc,mul_inv_cancel,one_mul] using
    (integralGroup n).inv_mem γ.prop

lemma quotient_fiber_representative (n : ℕ) (s : X n → G n)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (g : G n) : ∃ γ : integralGroup n,
      γ.val*s (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g)=g := by
  let x : X n := Quotient.mk _ g
  have he : Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g=
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x) := (hs x).symm
  have hmem := Quotient.exact he
  change QuotientGroup.rightRel (integralGroup n) g (s x) at hmem
  rw [QuotientGroup.rightRel_apply] at hmem
  have hmem' : g*(s x)⁻¹ ∈ integralGroup n := by
    simpa only [mul_inv_rev,inv_inv] using (integralGroup n).inv_mem hmem
  refine ⟨⟨g*(s x)⁻¹,hmem'⟩,?_⟩
  exact inv_mul_cancel_right _ _

theorem quotientLiftMeasure_injective_chart (n : ℕ)
    (μ : Measure (X n)) (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (E : Set (G n)) (hE : MeasurableSet E)
    (hinj : Set.InjOn (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) E) :
    quotientLiftMeasure n μ s E =
      μ ((Quotient.mk (QuotientGroup.rightRel (integralGroup n))) '' E) := by
  let : Countable (integralGroup n) := separableSpace_iff_countable.mp inferInstance
  let q : G n → X n := Quotient.mk (QuotientGroup.rightRel (integralGroup n))
  let A : integralGroup n → Set (X n) := fun γ => (fun x => γ.val*s x) ⁻¹' E
  have hA (γ : integralGroup n) : MeasurableSet (A γ) :=
    hE.preimage (measurable_const.mul hsm)
  have hd : Pairwise (Disjoint on A) := by
    intro γ δ hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    have he : γ.val*s x=δ.val*s x := hinj hx hy (by
      change q (γ.val*s x)=q (δ.val*s x)
      dsimp only [q]
      rw [quotient_left_integral,quotient_left_integral])
    exact hne (Subtype.ext (mul_right_cancel he))
  have hu : (⋃ γ, A γ)=q '' E := by
    ext x
    constructor
    · intro hx
      obtain ⟨γ,hγ⟩ := mem_iUnion.mp hx
      refine ⟨γ.val*s x,hγ,?_⟩
      exact (quotient_left_integral n γ (s x)).trans (hs x)
    · rintro ⟨g,hg,rfl⟩
      obtain ⟨γ,hγ⟩ := quotient_fiber_representative n s hs g
      exact mem_iUnion.mpr ⟨γ,by change γ.val*s (q g) ∈ E; rwa [hγ]⟩
  rw [quotientLiftMeasure,Measure.sum_apply _ hE]
  calc
    _ = ∑' γ : integralGroup n, μ (A γ) := by
      apply tsum_congr
      intro γ
      exact Measure.map_apply (measurable_const.mul hsm) hE
    _ = _ := by rw [←measure_iUnion hd hA,hu]

theorem quotient_measure_ext_on_injective_charts (n : ℕ)
    (ν ν' : Measure (G n))
    (heq : ∀ E : Set (G n), MeasurableSet E →
      Set.InjOn (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) E → ν E=ν' E) :
    ν=ν' := by
  let q : G n → X n := Quotient.mk (QuotientGroup.rightRel (integralGroup n))
  choose e he hqe using (quotient_covering n).isLocalHomeomorph
  obtain ⟨S,hSuniv,hSc,hS⟩ := isOpen_biUnion_countable (univ : Set (G n))
    (fun g => (e g).source) (fun g _ => (e g).open_source)
  have hcover : (⋃ g ∈ S, (e g).source)=univ := by
    rw [hS]
    apply eq_univ_of_forall
    intro g
    exact mem_iUnion₂.mpr ⟨g,mem_univ _,he g⟩
  apply Measure.ext_of_biUnion_eq_univ hSc hcover
  intro g hg
  ext E hE
  rw [Measure.restrict_apply hE,Measure.restrict_apply hE]
  apply heq _ (hE.inter (e g).open_source.measurableSet)
  intro a ha b hb hab
  apply (e g).injOn ha.2 hb.2
  rwa [←hqe g]

theorem quotientLiftMeasure_section_independent (n : ℕ)
    (μ : Measure (X n)) (s t : X n → G n) (hsm : Measurable s) (htm : Measurable t)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (ht : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (t x)=x) :
    quotientLiftMeasure n μ s=quotientLiftMeasure n μ t := by
  apply quotient_measure_ext_on_injective_charts
  intro E hE hEinj
  rw [quotientLiftMeasure_injective_chart n μ s hsm hs E hE hEinj,
    quotientLiftMeasure_injective_chart n μ t htm ht E hE hEinj]

theorem quotientLiftMeasure_locallyFinite (n : ℕ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x) :
    IsLocallyFiniteMeasure (quotientLiftMeasure n μ s) := by
  constructor
  intro g
  obtain ⟨e,hg,hqe⟩ := (quotient_covering n).isLocalHomeomorph g
  refine ⟨e.source,e.open_source.mem_nhds hg,?_⟩
  rw [quotientLiftMeasure_injective_chart n μ s hsm hs e.source e.open_source.measurableSet]
  · exact measure_lt_top μ _
  · intro a ha b hb hab
    apply e.injOn ha hb
    rwa [←hqe]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientLiftInvariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_locallyFinite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_locallyFinite _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariance of the covering lift

Changing the section after a quotient translation is harmless because the
lift is section-independent. Thus every actual right invariance of the
quotient measure lifts to the corresponding right invariance on the group.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem quotientLiftMeasure_right_invariant (n : ℕ)
    (μ : Measure (X n)) (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (a : G n) (ha : μ.map (fun x => rightAction x a)=μ) :
    (quotientLiftMeasure n μ s).map (fun g => g*a)=quotientLiftMeasure n μ s := by
  let T : X n → X n := fun x => rightAction x a
  have hT : MeasurePreserving T μ μ := ⟨(continuous_rightAction a).measurable,ha⟩
  let t : X n → G n := fun x => s (T x)*a⁻¹
  have htm : Measurable t := (hsm.comp hT.measurable).mul_const _
  have ht : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (t x)=x := by
    intro x
    change rightAction (Quotient.mk _ (s (T x))) a⁻¹=x
    rw [hs]
    change rightAction (rightAction x a) a⁻¹=x
    rw [rightAction_mul,mul_inv_cancel,rightAction_one]
  conv_lhs => rw [quotientLiftMeasure_section_independent n μ s t hsm htm hs ht]
  ext E hE
  have hR : Measurable (fun g : G n => g*a) := continuous_mul_const a |>.measurable
  rw [Measure.map_apply hR hE,quotientLiftMeasure,Measure.sum_apply _ (hE.preimage hR),
    quotientLiftMeasure,Measure.sum_apply _ hE]
  apply tsum_congr
  intro γ
  have hγt : Measurable (fun x => γ.val*t x) := measurable_const.mul htm
  have hγs : Measurable (fun x => γ.val*s x) := measurable_const.mul hsm
  rw [Measure.map_apply hγt (hE.preimage hR),Measure.map_apply hγs hE]
  have he : (fun x => γ.val*t x) ⁻¹' ((fun g : G n => g*a) ⁻¹' E) =
      T ⁻¹' ((fun x => γ.val*s x) ⁻¹' E) := by
    ext x
    change (γ.val*(s (T x)*a⁻¹))*a ∈ E ↔ γ.val*s (T x) ∈ E
    simp only [mul_assoc,inv_mul_cancel,mul_one]
  rw [he]
  exact hT.measure_preimage (hE.preimage hγs).nullMeasurableSet

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralCoordinateMeasure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translation invariance in the actual neutral product chart -/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem comap_map_eq_of_equivariant
    {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Z) (f : Y → Z) (hf : MeasurableEmbedding f)
    (e : Y ≃ᵐ Y) (g : Z ≃ᵐ Z)
    (heq : ∀ y, f (e y)=g (f y)) (hinv : ν.map g=ν) :
    (ν.comap f).map e=ν.comap f := by
  ext E hE
  have himage : f '' (e ⁻¹' E)=g ⁻¹' (f '' E) := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨e y,hy,heq y⟩
    · rintro ⟨y,hy,hyz⟩
      refine ⟨e.symm y,?_,?_⟩
      · change e (e.symm y) ∈ E
        simpa only [e.apply_symm_apply] using hy
      · apply g.injective
        rw [←heq,e.apply_symm_apply,hyz]
  rw [Measure.map_apply e.measurable hE,
    Measure.comap_apply f hf.injective (fun _ => hf.measurableSet_image.mpr) _
      (hE.preimage e.measurable),himage,
    ←Measure.map_apply g.measurable (hf.measurableSet_image.mpr hE),hinv,
    Measure.comap_apply f hf.injective (fun _ => hf.measurableSet_image.mpr) _ hE]

lemma neutralProductParam_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (neutralProductParam n) :=
  (neutralUpperRootParam_isOpenEmbedding n).comp
    (Homeomorph.prodAssoc _ _ _).isOpenEmbedding

lemma neutralProductParam_add (n : ℕ)
    (z : NeutralCoordinateBase n × transverseNeutralSpace n) (v : transverseNeutralSpace n) :
    neutralProductParam n (z.1,z.2+v)=
      neutralProductParam n z*diagonalOneParameter v.val v.prop 1 :=
  neutralUpperRootParam_translate n (z.1.1,(z.1.2,z.2)) v

lemma neutralCoordinateBase_locallyCompact (n : ℕ) :
    LocallyCompactSpace (NeutralCoordinateBase n) := by
  let : LocallyCompactSpace (NeutralCoordinateBase n × transverseNeutralSpace n) :=
    (neutralProductParam_isOpenEmbedding n).locallyCompactSpace
  exact (isOpenQuotientMap_fst (X := NeutralCoordinateBase n)
    (Y := transverseNeutralSpace n)).locallyCompactSpace

lemma neutralCoordinateBase_secondCountable (n : ℕ) :
    SecondCountableTopology (NeutralCoordinateBase n) := by
  let : SecondCountableTopology (NeutralCoordinateBase n × transverseNeutralSpace n) :=
    (neutralProductParam_isOpenEmbedding n).isEmbedding.secondCountableTopology
  have hq := isOpenQuotientMap_fst (X := NeutralCoordinateBase n) (Y := transverseNeutralSpace n)
  exact Topology.IsQuotientMap.secondCountableTopology hq.isQuotientMap hq.isOpenMap

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RestrictedCoordinateMap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting an embedded coordinate measure inside a second chart -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

theorem map_restrict_comap_le
    {Y Z W : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]
    (ν : Measure W) (f : Z → W) (hf : MeasurableEmbedding f)
    (g : Y → Z) (hg : MeasurableEmbedding g)
    (A : Set Y) (B : Set Z)
    (hsub : ∀ y ∈ A, g y ∈ B) :
    (((ν.comap (f ∘ g)).restrict A).map g) ≤ (ν.comap f).restrict B := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.map_apply hg.measurable hE,
    Measure.restrict_apply (hE.preimage hg.measurable),
    (hf.comp hg).comap_apply,
    Measure.restrict_apply hE,hf.comap_apply]
  apply measure_mono
  rintro _ ⟨y,⟨hyE,hyA⟩,rfl⟩
  exact ⟨g y,⟨hyE,hsub y hyA⟩,rfl⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual quotient boxes for every remaining root subgroup -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_rootPrefixBox_at_coordinates {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n)
    (z : (UpperRootTransverse n × T) × c.Time) :
    ∃ B : RootPrefixBox C c hP hfinal g, z ∈ B.transverse ×ˢ B.time := by
  obtain ⟨U,hUz,hU⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp
    (C.timeParam_localHomeomorph c hP hfinal g) z
  obtain ⟨V,W,hVo,hVz,hWo,hWz,hsub⟩ := mem_nhds_prod_iff'.mp hUz
  have he := hU.comp (Topology.IsOpenEmbedding.inclusion hsub
    ((hVo.prod hWo).preimage continuous_subtype_val))
  exact ⟨⟨V,W,hVo,hWo,he⟩,hVz,hWz⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixLift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root-prefix box measures agree with the actual covering lift -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {T : Type*} [TopologicalSpace T]

theorem timeGroupParam_isOpenEmbedding
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries=allPositiveRoots n) (g : G n) :
    Topology.IsOpenEmbedding (C.timeGroupParam c hP hf g) := by
  let E := (Homeomorph.prodAssoc (UpperRootTransverse n) T c.Time).trans
    ((Homeomorph.refl (UpperRootTransverse n)).prodCongr
      ((Homeomorph.refl T).prodCongr (c.remainingWordHomeomorph hP hf)))
  exact (Homeomorph.mulLeft g).isOpenEmbedding.comp
    (C.groupParam_isOpenEmbedding.comp E.isOpenEmbedding)

end RootPrefixCoordinates

namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
  {C : RootPrefixCoordinates n P T} {c : EliminationChain P D}
  {hP : InitialRootPattern P} {hf : c.finalEntries=allPositiveRoots n} {g : G n}

theorem coordinateMeasure_eq_lift_restrict
    (B : RootPrefixBox C c hP hf g) (μ : Measure (X n))
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x) :
    B.coordinateMeasure μ=
      ((quotientLiftMeasure n μ s).comap (C.timeGroupParam c hP hf g)).restrict B.domain := by
  let F := C.timeGroupParam c hP hf g
  have hF : MeasurableEmbedding F := (C.timeGroupParam_isOpenEmbedding c hP hf g).measurableEmbedding
  ext A hA
  rw [B.coordinateMeasure_apply μ hA,Measure.restrict_apply hA,
    hF.comap_apply]
  have hinj : Set.InjOn
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) (F '' (A ∩ B.domain)) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hxy
    have he : B.param ⟨x,hx.2⟩=B.param ⟨y,hy.2⟩ := hxy
    have hz := congrArg Subtype.val (B.embedding.injective he)
    exact congrArg F hz
  rw [quotientLiftMeasure_injective_chart n μ s hsm hs _
    (hF.measurableSet_image.mpr (hA.inter (B.transverse_open.prod B.time_open).measurableSet)) hinj]
  rw [Set.image_image]
  rfl

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralPrefixMap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual change from neutral coordinates to full-root prefix coordinates -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma neutralToPrefix_param (n : ℕ) (g : G n)
    (z : NeutralCoordinateBase n × transverseNeutralSpace n) :
    (neutralEmptyPrefix n).timeGroupParam (completeRootChain n)
        (emptyRootPattern n) (completeRootChain_final n) g (neutralToPrefix n z)=
      g*neutralProductParam n z := by
  unfold RootPrefixCoordinates.timeGroupParam
  rw [RootPrefixCoordinates.groupParam_eq_mul]
  change g*((transverseNeutralReconstruct (z.1.1,z.2)).val.val *
      (1*(completeRootChain n).word
        ((completeRootChain n).rootDilation z.2.val (-1) z.1.2))) = _
  rw [one_mul]
  have he := (neutralUpperRootParam_eq n (z.1.1,(z.1.2,z.2))).symm
  rw [upperRootParam_eq_mul] at he
  exact congrArg (g*·) he

theorem neutralToPrefix_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (neutralToPrefix n) := by
  have hf := (neutralEmptyPrefix n).timeGroupParam_isOpenEmbedding
    (completeRootChain n) (emptyRootPattern n) (completeRootChain_final n) (1 : G n)
  apply Topology.IsOpenEmbedding.of_comp (neutralToPrefix n) hf
  convert neutralProductParam_isOpenEmbedding n using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact (neutralToPrefix_param n 1 z).trans (one_mul _)

lemma neutralToPrefix_base (n : ℕ)
    (x y : NeutralCoordinateBase n × transverseNeutralSpace n)
    (hN : x.1.1=y.1.1) (hv : x.2=y.2) :
    (neutralToPrefix n x).1=(neutralToPrefix n y).1 := by
  change (Subtype.val (transverseNeutralReconstruct (x.1.1,x.2)),PUnit.unit)=
    (Subtype.val (transverseNeutralReconstruct (y.1.1,y.2)),PUnit.unit)
  rw [hN,hv]

lemma neutralToPrefix_fiber_injective (n : ℕ)
    (x y : NeutralCoordinateBase n × transverseNeutralSpace n)
    (hv : x.2=y.2) (hu : (neutralToPrefix n x).2=(neutralToPrefix n y).2) :
    x.1.2=y.1.2 := by
  change (completeRootChain n).rootDilation x.2.val (-1) x.1.2=
    (completeRootChain n).rootDilation y.2.val (-1) y.1.2 at hu
  rw [←hv] at hu
  have H := congrArg ((completeRootChain n).rootDilation x.2.val 1) hu
  have hx := upperRootDilation_opposite_cancel n x.2 (-1) x.1.2
  have hy := upperRootDilation_opposite_cancel n x.2 (-1) y.1.2
  simp only [neg_neg] at hx hy
  exact hx.symm.trans (H.trans hy)

theorem neutralToPrefix_restrict_le (n : ℕ) (g : G n)
    (B : RootPrefixBox (neutralEmptyPrefix n) (completeRootChain n)
      (emptyRootPattern n) (completeRootChain_final n) g)
    (μ : Measure (X n)) (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (R : Set (NeutralCoordinateBase n × transverseNeutralSpace n))
    (hRB : ∀ z ∈ R, neutralToPrefix n z ∈ B.domain) :
    (((quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z)).restrict R).map
        (neutralToPrefix n) ≤ B.coordinateMeasure μ := by
  have H := map_restrict_comap_le (quotientLiftMeasure n μ s)
    ((neutralEmptyPrefix n).timeGroupParam (completeRootChain n)
      (emptyRootPattern n) (completeRootChain_final n) g)
    ((neutralEmptyPrefix n).timeGroupParam_isOpenEmbedding (completeRootChain n)
      (emptyRootPattern n) (completeRootChain_final n) g).measurableEmbedding
    (neutralToPrefix n) (neutralToPrefix_isOpenEmbedding n).measurableEmbedding
    R B.domain hRB
  have he : (neutralEmptyPrefix n).timeGroupParam (completeRootChain n)
        (emptyRootPattern n) (completeRootChain_final n) g ∘ neutralToPrefix n=
      fun z => g*neutralProductParam n z := funext (neutralToPrefix_param n g)
  rw [he,←B.coordinateMeasure_eq_lift_restrict μ s hsm hs] at H
  exact H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_TranslatedNeutralProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Neutral Haar products in every left-translated chart -/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem translated_neutral_product (n : ℕ) (g : G n)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (hA : ∀ v : transverseNeutralSpace n,
      μ.map (fun x => rightAction x (diagonalOneParameter v.val v.prop 1))=μ)
    (η : Measure (transverseNeutralSpace n)) [η.IsAddHaarMeasure]
    (K : Set (transverseNeutralSpace n)) (hK : IsCompact K) (hηK : η K=1) :
    (quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z)=
      (firstCoordinateSlice
        ((quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z)) K).prod η := by
  let F := fun z : NeutralCoordinateBase n × transverseNeutralSpace n =>
    g*neutralProductParam n z
  have hF : Topology.IsOpenEmbedding F :=
    (Homeomorph.mulLeft g).isOpenEmbedding.comp (neutralProductParam_isOpenEmbedding n)
  let := quotientLiftMeasure_locallyFinite n μ s hsm hs
  let := neutralCoordinateBase_locallyCompact n
  let := neutralCoordinateBase_secondCountable n
  let : IsFiniteMeasureOnCompacts ((quotientLiftMeasure n μ s).comap F) :=
    IsFiniteMeasureOnCompacts.comap' _ hF.continuous hF.measurableEmbedding
  apply translationInvariant_eq_product _ _ η K hK hηK
  intro v
  let e := ((Homeomorph.refl (NeutralCoordinateBase n)).prodCongr
    (Homeomorph.addRight v)).toMeasurableEquiv
  let a := (Homeomorph.mulRight (diagonalOneParameter v.val v.prop 1)).toMeasurableEquiv
  have H := comap_map_eq_of_equivariant (quotientLiftMeasure n μ s) F
    hF.measurableEmbedding e a (fun z => by
      change g*neutralProductParam n (z.1,z.2+v)=
        (g*neutralProductParam n z)*diagonalOneParameter v.val v.prop 1
      rw [neutralProductParam_add,mul_assoc])
    (quotientLiftMeasure_right_invariant n μ s hsm hs _ (hA v))
  have he : ⇑e = (fun z => (z.1,v+z.2)) := by
    funext z
    rcases z with ⟨z,w⟩
    change (z,w+v)=(z,v+w)
    rw [add_comm]
  rw [he] at H
  exact H

theorem translated_neutral_transverse_finiteOnCompacts (n : ℕ) (g : G n)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (K : Set (transverseNeutralSpace n)) (hK : IsCompact K) :
    IsFiniteMeasureOnCompacts (firstCoordinateSlice
      ((quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z)) K) := by
  let := quotientLiftMeasure_locallyFinite n μ s hsm hs
  have hF : Topology.IsOpenEmbedding
      (fun z : NeutralCoordinateBase n × transverseNeutralSpace n =>
        g*neutralProductParam n z) :=
    (Homeomorph.mulLeft g).isOpenEmbedding.comp (neutralProductParam_isOpenEmbedding n)
  let : IsFiniteMeasureOnCompacts ((quotientLiftMeasure n μ s).comap
      (fun z => g*neutralProductParam n z)) :=
    IsFiniteMeasureOnCompacts.comap' _ hF.continuous hF.measurableEmbedding
  exact firstCoordinateSlice_finiteOnCompacts _ hK

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralAtomicPatch
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Atomic root kernels give a neutral-independent support graph in each patch -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem neutral_patch_graph_of_atomic_kernel (n : ℕ) (g : G n)
    (B : RootPrefixBox (neutralEmptyPrefix n) (completeRootChain n)
      (emptyRootPattern n) (completeRootChain_final n) g)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (τ : Measure (NeutralCoordinateBase n)) [SFinite τ]
    (η : Measure (transverseNeutralSpace n)) [SFinite η]
    (hprod : (quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z)=τ.prod η)
    (A : Set (NeutralCoordinateBase n))
    (K : Set (transverseNeutralSpace n)) (hηK : η K ≠ 0)
    (hAB : ∀ z ∈ A ×ˢ K, neutralToPrefix n z ∈ B.domain)
    (hatom : ∀ᵐ z ∂B.coordinateMeasure μ, B.conditionalKernel μ z.1=Measure.dirac z.2) :
    ∃ F : Set (NeutralCoordinateBase n), MeasurableSet F ∧
      (∀ᵐ z ∂τ.restrict A, z ∈ F) ∧
      (∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2) ∧
      (∀ᵐ z ∂(τ.restrict A).prod (η.restrict K), z.1 ∈ F) := by
  let : NeZero (η.restrict K) := ⟨by
    intro he
    have H := congrArg (fun m : Measure (transverseNeutralSpace n) => m univ) he
    simp only [Measure.restrict_apply_univ,Measure.coe_zero,Pi.zero_apply] at H
    exact hηK H⟩
  have hle := neutralToPrefix_restrict_le n g B μ s hsm hs (A ×ˢ K) hAB
  rw [hprod,←Measure.prod_restrict] at hle
  apply independent_graph_of_fiber_map (τ.restrict A) (η.restrict K)
    (B.coordinateMeasure μ) (B.conditionalKernel μ) hatom (neutralToPrefix n)
    (neutralToPrefix_isOpenEmbedding n).continuous.measurable
    (Measure.absolutelyContinuous_of_le hle)
  · exact neutralToPrefix_base n
  · intro x y _ hv hu
    exact neutralToPrefix_fiber_injective n x y hv hu

theorem neutral_patch_graph_of_atomic_roots (d : ℕ) (g : G (d+1))
    (B : RootPrefixBox (neutralEmptyPrefix (d+1)) (completeRootChain (d+1))
      (emptyRootPattern (d+1)) (completeRootChain_final (d+1)) g)
    (R : ℝ) (hBR : B.time ⊆ (completeRootChain (d+1)).remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (s : X (d+1) → G (d+1)) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup (d+1))) (s x)=x)
    (τ : Measure (NeutralCoordinateBase (d+1))) [SFinite τ]
    (η : Measure (transverseNeutralSpace (d+1))) [SFinite η]
    (hprod : (quotientLiftMeasure (d+1) μ s).comap
      (fun z => g*neutralProductParam (d+1) z)=τ.prod η)
    (A : Set (NeutralCoordinateBase (d+1)))
    (K : Set (transverseNeutralSpace (d+1))) (hηK : η K ≠ 0)
    (hAB : ∀ z ∈ A ×ˢ K, neutralToPrefix (d+1) z ∈ B.domain)
    (hatom : ∀ p : ↥(allPositiveRoots (d+1) \ ∅), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0) :
    ∃ F : Set (NeutralCoordinateBase (d+1)), MeasurableSet F ∧
      (∀ᵐ z ∂τ.restrict A, z ∈ F) ∧
      (∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2) ∧
      (∀ᵐ z ∂(τ.restrict A).prod (η.restrict K), z.1 ∈ F) :=
  neutral_patch_graph_of_atomic_kernel (d+1) g B μ s hsm hs τ η hprod A K hηK hAB
    (B.ae_conditionalKernel_eq_dirac_of_atomic_roots R hBR μ hatom)

theorem actual_neutral_patch_graph_of_atomic_roots (d : ℕ) (g : G (d+1))
    (B : RootPrefixBox (neutralEmptyPrefix (d+1)) (completeRootChain (d+1))
      (emptyRootPattern (d+1)) (completeRootChain_final (d+1)) g)
    (R : ℝ) (hBR : B.time ⊆ (completeRootChain (d+1)).remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (s : X (d+1) → G (d+1)) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup (d+1))) (s x)=x)
    (hA : ∀ v : transverseNeutralSpace (d+1),
      μ.map (fun x => rightAction x (diagonalOneParameter v.val v.prop 1))=μ)
    (η : Measure (transverseNeutralSpace (d+1))) [η.IsAddHaarMeasure]
    (K₀ : Set (transverseNeutralSpace (d+1))) (hK₀ : IsCompact K₀) (hηK₀ : η K₀=1)
    (A : Set (NeutralCoordinateBase (d+1)))
    (K : Set (transverseNeutralSpace (d+1))) (hηK : η K ≠ 0)
    (hAB : ∀ z ∈ A ×ˢ K, neutralToPrefix (d+1) z ∈ B.domain)
    (hatom : ∀ p : ↥(allPositiveRoots (d+1) \ ∅), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0) :
    let τ := firstCoordinateSlice
      ((quotientLiftMeasure (d+1) μ s).comap (fun z => g*neutralProductParam (d+1) z)) K₀
    ∃ F : Set (NeutralCoordinateBase (d+1)), MeasurableSet F ∧
      (∀ᵐ z ∂τ.restrict A, z ∈ F) ∧
      (∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2) ∧
      (∀ᵐ z ∂(τ.restrict A).prod (η.restrict K), z.1 ∈ F) := by
  let := neutralCoordinateBase_locallyCompact (d+1)
  let := neutralCoordinateBase_secondCountable (d+1)
  let := translated_neutral_transverse_finiteOnCompacts (d+1) g μ s hsm hs K₀ hK₀
  exact neutral_patch_graph_of_atomic_roots d g B R hBR μ s hsm hs _ η
    (translated_neutral_product (d+1) g μ s hsm hs hA η K₀ hK₀ hηK₀)
    A K hηK hAB hatom

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RadialFutureLifts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponentially shrinking radial cells give triangular future lifts -/

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma LocalInjectivityAt.injOn {n : ℕ} {r : ℝ} {x : X n}
    (h : LocalInjectivityAt r x) :
    Set.InjOn (fun g => rightAction x g) (matrixBall n r) := by
  obtain ⟨U,_,hx,hi⟩ := h
  exact hi x hx

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_BilateralNeutralLifts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bilateral observation fibers have neutral relative displacement

The same small radial cells are used in both time directions. Uniqueness
of the small lift identifies the two triangular lifts; their common lift
commutes with the diagonal flow. This supplies the geometry needed to
bound the entropy left over after the complete observation itinerary.
-/

noncomputable section
open Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma commute_diagonalOneParameter_of_weight_support {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (g : G n)
    (hg : ∀ i j, ell i ≠ ell j → g.val i j=0) (t : ℝ) :
    Commute g (diagonalOneParameter ell hell t) := by
  change g * diagonalOneParameter ell hell t = diagonalOneParameter ell hell t * g
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (g.val * Matrix.diagonal (fun k => Real.exp (ell k*t))) i j =
    (Matrix.diagonal (fun k => Real.exp (ell k*t)) * g.val) i j
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases h : ell i=ell j
  · rw [h,mul_comm]
  · rw [hg i j h]
    simp

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeakStableFactorization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal and unipotent coordinates of a weak stable displacement -/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

/-- Positive upper triangular matrices split into a positive diagonal
matrix and an actual ordered upper-root word. -/
theorem upper_triangular_positive_diagonal_factorization {n : ℕ} (g : G n)
    (htri : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i) :
    ∃ (v : Fin n → ℝ) (hv : ∑ i, v i=0) (u : UpperRootTime n),
      g=diagonalOneParameter v hv 1 * (completeRootChain n).word u := by
  let v : Fin n → ℝ := fun i => Real.log (g.val i i)
  have hprod : ∏ i, g.val i i=1 := (Matrix.det_of_isUpperTriangular htri).symm.trans g.prop
  have hv : ∑ i, v i=0 := by
    dsimp [v]
    rw [←Real.log_prod (fun i _ => (hpos i).ne'),hprod,Real.log_one]
  let a := diagonalOneParameter v hv 1
  let u : G n := a⁻¹*g
  have hu : PositiveRootPattern (allPositiveRoots n) u := by
    intro i j hij
    have hij' : ¬ i < j := by simpa [allPositiveRoots] using hij
    have he : u.val i j=Real.exp (-v i)*g.val i j := by
      change ((diagonalOneParameter v hv 1)⁻¹*g).val i j = _
      rw [←diagonalOneParameter_neg]
      change (Matrix.diagonal (fun i => Real.exp (v i*(-1))) * g.val) i j = _
      rw [Matrix.diagonal_mul]
      congr 2
      ring
    rw [he]
    by_cases heq : i=j
    · subst j
      rw [Matrix.one_apply_eq]
      dsimp [v]
      rw [Real.exp_neg,Real.exp_log (hpos i),inv_mul_cancel₀ (hpos i).ne']
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij') (Ne.symm heq)
      rw [htri hji,Matrix.one_apply_ne heq,mul_zero]
  have hum : u ∈ positiveRootGeneratedGroup (allPositiveRoots n) :=
    positiveRootPattern_mem_generated (allPositiveRoots n)
      (fun p hp => (Finset.mem_filter.mp hp).2) (allPositiveRoots_closed n) hu
  obtain ⟨t,ht⟩ := upperRootWord_surjective n ⟨u,hum⟩
  refine ⟨v,hv,t,?_⟩
  rw [ht]
  change g=a*(a⁻¹*g)
  group

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_NeutralFutureCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weak stable displacements preserve the lower unitriangular coordinate -/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem neutralProductParam_mul_upper (n : ℕ)
    (z : NeutralCoordinateBase n × transverseNeutralSpace n)
    (g : G n) (hg : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i) :
    ∃ (u : UpperRootTime n) (v : transverseNeutralSpace n),
      neutralProductParam n ((z.1.1,u),v)=neutralProductParam n z*g := by
  obtain ⟨w,hw,t,ht⟩ := upper_triangular_positive_diagonal_factorization g hg hpos
  let v : transverseNeutralSpace n := z.2+⟨w,hw⟩
  let t' := (completeRootChain n).rootDilation v.val 1 t
  have hm : (completeRootChain n).word z.1.2*(completeRootChain n).word t' ∈
      positiveRootGeneratedGroup (allPositiveRoots n) :=
    (positiveRootGeneratedGroup _).mul_mem (upperRootWord_mem n _) (upperRootWord_mem n _)
  obtain ⟨u,hu⟩ := upperRootWord_surjective n ⟨_,hm⟩
  refine ⟨u,v,?_⟩
  change z.1.1.val.val*(completeRootChain n).word u*diagonalOneParameter v.val v.prop 1=
    (z.1.1.val.val*(completeRootChain n).word z.1.2*
      diagonalOneParameter z.2.val z.2.prop 1)*g
  rw [hu]
  dsimp only [t']
  rw [(completeRootChain n).word_rootDilation v.val v.prop,
    diagonalOneParameter_neg,ht]
  have hd : diagonalOneParameter v.val v.prop 1=
      diagonalOneParameter z.2.val z.2.prop 1*diagonalOneParameter w hw 1 :=
    diagonalOneParameter_add_weights _ _ _ _ _
  rw [hd]
  group

theorem neutral_unit_coordinate_of_upper_displacement (n : ℕ)
    (z w : NeutralCoordinateBase n × transverseNeutralSpace n)
    (g : G n) (hg : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i)
    (heq : neutralProductParam n w=neutralProductParam n z*g) :
    z.1.1=w.1.1 := by
  obtain ⟨u,v,huv⟩ := neutralProductParam_mul_upper n z g hg hpos
  have hz := (neutralProductParam_isOpenEmbedding n).injective (huv.trans heq.symm)
  simpa only using
    congrArg (fun q : NeutralCoordinateBase n × transverseNeutralSpace n => q.1.1) hz

theorem neutral_graph_upper_displacement (n : ℕ)
    (E : Set (NeutralCoordinateBase n))
    (hE : ∀ x ∈ E, ∀ y ∈ E, x.1=y.1 → x.2=y.2)
    (z w : NeutralCoordinateBase n × transverseNeutralSpace n)
    (hz : z.1 ∈ E) (hw : w.1 ∈ E)
    (g : G n) (hg : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i)
    (heq : neutralProductParam n w=neutralProductParam n z*g) :
    ∃ v : transverseNeutralSpace n, g=diagonalOneParameter v.val v.prop 1 := by
  have hN := neutral_unit_coordinate_of_upper_displacement n z w g hg hpos heq
  have hu := hE z.1 hz w.1 hw hN
  have hb : z.1=w.1 := Prod.ext hN hu
  have hc : (z.1,z.2+(w.2-z.2))=w := by
    refine Prod.ext ?_ ?_
    · exact hb
    · change z.2+(w.2-z.2)=w.2
      abel
  have ht := neutralProductParam_add n z (w.2-z.2)
  rw [hc] at ht
  exact ⟨w.2-z.2,mul_left_cancel (heq.symm.trans ht)⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralGraphLifts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identify small future lifts inside a neutral graph patch -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem neutral_graph_quotient_lift {n : ℕ} (g₀ : G n)
    (E : Set (NeutralCoordinateBase n))
    (hE : ∀ x ∈ E, ∀ y ∈ E, x.1=y.1 → x.2=y.2)
    (z w : NeutralCoordinateBase n × transverseNeutralSpace n)
    (hz : z.1 ∈ E) (hw : w.1 ∈ E) (r : ℝ)
    (hinj : LocalInjectivityAt r
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n z)))
    (hchart : (neutralProductParam n z)⁻¹*neutralProductParam n w ∈ matrixBall n r)
    (g : G n) (hg : g ∈ matrixBall n r)
    (htri : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i)
    (hlift : rightAction
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n z)) g =
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n w)) :
    ∃ v : transverseNeutralSpace n, g=diagonalOneParameter v.val v.prop 1 := by
  have haction : rightAction
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n z))
      ((neutralProductParam n z)⁻¹*neutralProductParam n w) =
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n w) := by
    change Quotient.mk _ ((g₀*neutralProductParam n z)*
      ((neutralProductParam n z)⁻¹*neutralProductParam n w)) = _
    congr 1
    group
  have he : g=(neutralProductParam n z)⁻¹*neutralProductParam n w :=
    hinj.injOn hg hchart (hlift.trans haction.symm)
  apply neutral_graph_upper_displacement n E hE z w hz hw g htri hpos
  rw [he]
  group

theorem neutral_graph_small_future_lift {n : ℕ}
    (ell : Fin n → ℝ) (hord : StrictMono ell) (g₀ : G n)
    (E : Set (NeutralCoordinateBase n))
    (hE : ∀ x ∈ E, ∀ y ∈ E, x.1=y.1 → x.2=y.2)
    (z w : NeutralCoordinateBase n × transverseNeutralSpace n)
    (hz : z.1 ∈ E) (hw : w.1 ∈ E) (r : ℝ) (hr : r ≤ 1)
    (hinj : LocalInjectivityAt r
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n z)))
    (hchart : (neutralProductParam n z)⁻¹*neutralProductParam n w ∈ matrixBall n r)
    (g : G n) (hg : g ∈ matrixBall n r)
    (hzero : ∀ i j, ell j < ell i → g.val i j=0)
    (hlift : rightAction
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n z)) g =
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g₀*neutralProductParam n w)) :
    ∃ v : transverseNeutralSpace n, g=diagonalOneParameter v.val v.prop 1 := by
  apply neutral_graph_quotient_lift g₀ E hE z w hz hw r hinj hchart g hg
    (fun i j hji => hzero i j (hord hji)) _ hlift
  intro i
  have h := matrixBall_mono hr hg i i
  rw [Matrix.one_apply_eq] at h
  have hh := (abs_lt.mp h).1
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralPatchNull
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer the neutral graph's full measure to the quotient patch -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma neutralQuotientParam_injOn (n : ℕ) (g : G n)
    (B : RootPrefixBox (neutralEmptyPrefix n) (completeRootChain n)
      (emptyRootPattern n) (completeRootChain_final n) g)
    (R : Set (NeutralCoordinateBase n × transverseNeutralSpace n))
    (hRB : ∀ z ∈ R, neutralToPrefix n z ∈ B.domain) :
    InjOn (neutralQuotientParam n g) R := by
  intro z hz w hw hzw
  have he : B.param ⟨neutralToPrefix n z,hRB z hz⟩ =
      B.param ⟨neutralToPrefix n w,hRB w hw⟩ := by
    change Quotient.mk _ ((neutralEmptyPrefix n).timeGroupParam
      (completeRootChain n) (emptyRootPattern n) (completeRootChain_final n) g
      (neutralToPrefix n z)) = Quotient.mk _ ((neutralEmptyPrefix n).timeGroupParam
      (completeRootChain n) (emptyRootPattern n) (completeRootChain_final n) g
      (neutralToPrefix n w))
    simpa only [neutralToPrefix_param,neutralQuotientParam] using hzw
  exact (neutralToPrefix_isOpenEmbedding n).injective
    (congrArg Subtype.val (B.embedding.injective he))

theorem neutralQuotientParam_image_measure (n : ℕ) (g : G n)
    (μ : Measure (X n))
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (E : Set (NeutralCoordinateBase n × transverseNeutralSpace n)) (hE : MeasurableSet E)
    (hinj : InjOn (neutralQuotientParam n g) E) :
    μ (neutralQuotientParam n g '' E)=
      (quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z) E := by
  let f := fun z => g*neutralProductParam n z
  have hf : MeasurableEmbedding f :=
    ((Homeomorph.mulLeft g).isOpenEmbedding.comp
      (neutralProductParam_isOpenEmbedding n)).measurableEmbedding
  rw [hf.comap_apply,quotientLiftMeasure_injective_chart n μ s hsm hs (f '' E)
    (hf.measurableSet_image.mpr hE)]
  · rw [Set.image_image]
  · rintro _ ⟨z,hz,rfl⟩ _ ⟨w,hw,rfl⟩ hzw
    exact congrArg f (hinj hz hw hzw)

theorem neutralQuotientParam_measurable_image (n : ℕ) (g : G n)
    (E : Set (NeutralCoordinateBase n × transverseNeutralSpace n)) (hE : MeasurableSet E)
    (hinj : InjOn (neutralQuotientParam n g) E) :
    MeasurableSet (neutralQuotientParam n g '' E) := by
  let f := fun z => g*neutralProductParam n z
  have hf : MeasurableEmbedding f :=
    ((Homeomorph.mulLeft g).isOpenEmbedding.comp
      (neutralProductParam_isOpenEmbedding n)).measurableEmbedding
  have hq : InjOn (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) (f '' E) := by
    rintro _ ⟨z,hz,rfl⟩ _ ⟨w,hw,rfl⟩ hzw
    exact congrArg f (hinj hz hw hzw)
  have H := (hf.measurableSet_image.mpr hE).image_of_measurable_injOn
    continuous_quotient_mk'.measurable hq
  rw [Set.image_image] at H
  change MeasurableSet (neutralQuotientParam n g '' E) at H
  exact H

theorem neutral_patch_image_ae_graph (n : ℕ) (g : G n)
    (μ : Measure (X n))
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (τ : Measure (NeutralCoordinateBase n)) [SFinite τ]
    (η : Measure (transverseNeutralSpace n)) [SFinite η]
    (hprod : (quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z)=τ.prod η)
    (A : Set (NeutralCoordinateBase n)) (hA : MeasurableSet A)
    (K : Set (transverseNeutralSpace n)) (hK : MeasurableSet K)
    (hinj : InjOn (neutralQuotientParam n g) (A ×ˢ K))
    (F : Set (NeutralCoordinateBase n)) (hF : MeasurableSet F)
    (hfull : ∀ᵐ z ∂(τ.restrict A).prod (η.restrict K), z.1 ∈ F) :
    ∀ᵐ x ∂μ, x ∈ neutralQuotientParam n g '' (A ×ˢ K) →
      x ∈ neutralQuotientParam n g '' ((A ×ˢ K) ∩ Prod.fst ⁻¹' F) := by
  let E := (A ×ˢ K) ∩ Prod.fst ⁻¹' Fᶜ
  have hE : MeasurableSet E := (hA.prod hK).inter (hF.compl.preimage measurable_fst)
  have he0 : μ (neutralQuotientParam n g '' E)=0 := by
    rw [neutralQuotientParam_image_measure n g μ s hsm hs E hE
      (hinj.mono inter_subset_left),hprod]
    have he := ae_iff.mp hfull
    rw [Measure.prod_restrict] at he
    change ((τ.prod η).restrict (A ×ˢ K)) (Prod.fst ⁻¹' Fᶜ)=0 at he
    rw [Measure.restrict_apply (hF.compl.preimage measurable_fst)] at he
    change (τ.prod η) ((A ×ˢ K) ∩ Prod.fst ⁻¹' Fᶜ)=0
    rw [Set.inter_comm]
    exact he
  have hn : ∀ᵐ x ∂μ, x ∉ neutralQuotientParam n g '' E := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using he0
  filter_upwards [hn] with x hx hmem
  obtain ⟨z,hz,rfl⟩ := hmem
  by_cases hf : z.1 ∈ F
  · exact ⟨z,⟨hz,hf⟩,rfl⟩
  · exact (hx ⟨z,⟨hz,hf⟩,rfl⟩).elim

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralSmallRectangles
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arbitrarily small neutral rectangles inside bounded root boxes -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

attribute [local irreducible] completeRootChain

theorem exists_small_neutral_rectangle (n : ℕ) (g : G n)
    (z₀ : NeutralCoordinateBase n × transverseNeutralSpace n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (B : RootPrefixBox (neutralEmptyPrefix n) (completeRootChain n)
        (emptyRootPattern n) (completeRootChain_final n) g)
      (R : ℝ) (A : Set (NeutralCoordinateBase n)) (K : Set (transverseNeutralSpace n)),
      IsOpen A ∧ IsOpen K ∧ z₀ ∈ A ×ˢ K ∧
      B.time ⊆ (completeRootChain n).remainingWindow R 0 ∧
      (∀ z ∈ A ×ˢ K, neutralToPrefix n z ∈ B.domain) ∧
      ∀ z ∈ A ×ˢ K, ∀ w ∈ A ×ˢ K,
        (neutralProductParam n z)⁻¹*neutralProductParam n w ∈ matrixBall n ε := by
  obtain ⟨B₀,hB₀⟩ := exists_rootPrefixBox_at_coordinates (neutralEmptyPrefix n)
    (completeRootChain n) (emptyRootPattern n) (completeRootChain_final n) g
    (neutralToPrefix n z₀)
  have hcover : (neutralToPrefix n z₀).2 ∈
      ⋃ m, (completeRootChain n).remainingWindow 1 m := by
    rw [(completeRootChain n).remainingWindow_cover]
    trivial
  obtain ⟨m,hm⟩ := mem_iUnion.mp hcover
  let B := B₀.shrink B₀.transverse
    (B₀.time ∩ (completeRootChain n).remainingWindow 1 m)
    B₀.transverse_open (B₀.time_open.inter ((completeRootChain n).remainingWindow_open 1 m))
    subset_rfl inter_subset_left
  have hzB : neutralToPrefix n z₀ ∈ B.domain := ⟨hB₀.1,hB₀.2,hm⟩
  let f := fun q : (NeutralCoordinateBase n × transverseNeutralSpace n) ×
      (NeutralCoordinateBase n × transverseNeutralSpace n) =>
    (neutralProductParam n q.1)⁻¹*neutralProductParam n q.2
  have hf : Continuous f :=
    (((neutralProductParam_isOpenEmbedding n).continuous.comp continuous_fst).inv).mul
      ((neutralProductParam_isOpenEmbedding n).continuous.comp continuous_snd)
  have hneigh : f ⁻¹' matrixBall n ε ∈ 𝓝 (z₀,z₀) := by
    apply (hf.isOpen_preimage _ (matrixBall_isOpen n ε)).mem_nhds
    change (neutralProductParam n z₀)⁻¹*neutralProductParam n z₀ ∈ matrixBall n ε
    rw [inv_mul_cancel]
    exact one_mem_matrixBall n hε
  obtain ⟨U,V,hU,hzU,hV,hzV,hUV⟩ := mem_nhds_prod_iff'.mp hneigh
  let W := (U ∩ V) ∩ (neutralToPrefix n) ⁻¹' B.domain
  have hW : IsOpen W := (hU.inter hV).inter
    ((B.transverse_open.prod B.time_open).preimage
      (neutralToPrefix_isOpenEmbedding n).continuous)
  have hzW : z₀ ∈ W := ⟨⟨hzU,hzV⟩,hzB⟩
  obtain ⟨A,K,hA,hzA,hK,hzK,hAK⟩ := mem_nhds_prod_iff'.mp (hW.mem_nhds hzW)
  refine ⟨B,1+m,A,K,hA,hK,⟨hzA,hzK⟩,?_,?_,?_⟩
  · intro t ht
    simpa only [EliminationChain.remainingWindow,Nat.cast_zero,add_zero] using ht.2
  · intro z hz
    exact (hAK hz).2
  · intro z hz w hw
    change f (z,w) ∈ matrixBall n ε
    exact hUV ⟨(hAK hz).1.1,(hAK hw).1.2⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralPatchCover
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A countable cover by actual small neutral rectangles -/

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma neutralQuotientParam_localHomeomorph (n : ℕ) (g : G n) :
    IsLocalHomeomorph (neutralQuotientParam n g) :=
  (quotient_covering n).isLocalHomeomorph.comp
    ((Homeomorph.mulLeft g).isLocalHomeomorph.comp
      (neutralProductParam_isOpenEmbedding n).isLocalHomeomorph)

lemma SmallNeutralPatch.raw_open {n : ℕ} {ε : ℝ} (P : SmallNeutralPatch n ε) :
    IsOpen P.raw :=
  (neutralQuotientParam_localHomeomorph n P.center).isOpenMap _
    (P.base_open.prod P.neutral_open)

theorem exists_countable_small_neutral_patches (n : ℕ)
    (z₀ : NeutralCoordinateBase n × transverseNeutralSpace n) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℕ → SmallNeutralPatch n ε, (⋃ i, (P i).raw)=univ := by
  classical
  have hx (x : X n) : ∃ P : SmallNeutralPatch n ε, x ∈ P.raw := by
    induction x using Quotient.inductionOn with
    | h g =>
      let g₀ := g*(neutralProductParam n z₀)⁻¹
      obtain ⟨B,R,A,K,hA,hK,hz,hBR,hAB,hsmall⟩ :=
        exists_small_neutral_rectangle n g₀ z₀ hε
      let P : SmallNeutralPatch n ε :=
        ⟨g₀,B,R,A,K,hA,hK,⟨z₀.2,hz.2⟩,hBR,hAB,hsmall⟩
      refine ⟨P,z₀,hz,?_⟩
      change Quotient.mk _ ((g*(neutralProductParam n z₀)⁻¹)*neutralProductParam n z₀)=
        Quotient.mk _ g
      rw [inv_mul_cancel_right]
  obtain ⟨S,_,hS,hcover⟩ := isOpen_biUnion_countable
    (univ : Set (SmallNeutralPatch n ε)) SmallNeutralPatch.raw
    (fun P _ => P.raw_open)
  have hfull : (⋃ P ∈ S, P.raw)=univ := by
    rw [hcover]
    apply eq_univ_of_forall
    intro x
    obtain ⟨P,hP⟩ := hx x
    exact mem_iUnion₂.mpr ⟨P,mem_univ _,hP⟩
  have hSne : S.Nonempty := by
    have hz : (Quotient.mk _ (1 : G n)) ∈ ⋃ P ∈ S, P.raw := by rw [hfull]; trivial
    obtain ⟨P,hP,_⟩ := mem_iUnion₂.mp hz
    exact ⟨P,hP⟩
  obtain ⟨P,hP⟩ := hS.exists_eq_range hSne
  refine ⟨P,?_⟩
  rw [hP] at hfull
  simpa only [biUnion_range] using hfull

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_AtomicNeutralPatch
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual atomic roots give full-measure graphs in every small neutral patch -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem SmallNeutralPatch.exists_atomic_graph {d : ℕ} {ε : ℝ}
    (P : SmallNeutralPatch (d+1) ε)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (s : X (d+1) → G (d+1)) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup (d+1))) (s x)=x)
    (hA : ∀ v : transverseNeutralSpace (d+1),
      μ.map (fun x => rightAction x (diagonalOneParameter v.val v.prop 1))=μ)
    (η : Measure (transverseNeutralSpace (d+1))) [η.IsAddHaarMeasure]
    (K₀ : Set (transverseNeutralSpace (d+1))) (hK₀ : IsCompact K₀) (hηK₀ : η K₀=1)
    (hatom : ∀ p : ↥(allPositiveRoots (d+1) \ ∅), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0) :
    ∃ F : Set (NeutralCoordinateBase (d+1)), MeasurableSet F ∧
      (∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2) ∧
      (∀ᵐ x ∂μ, x ∈ P.raw → x ∈ neutralQuotientParam (d+1) P.center ''
        ((P.base ×ˢ P.neutral) ∩ Prod.fst ⁻¹' F)) := by
  let τ := firstCoordinateSlice ((quotientLiftMeasure (d+1) μ s).comap
    (fun z => P.center*neutralProductParam (d+1) z)) K₀
  let := neutralCoordinateBase_locallyCompact (d+1)
  let := neutralCoordinateBase_secondCountable (d+1)
  let : IsFiniteMeasureOnCompacts τ :=
    translated_neutral_transverse_finiteOnCompacts (d+1) P.center μ s hsm hs K₀ hK₀
  obtain ⟨F,hF,_,hunique,hfull⟩ := actual_neutral_patch_graph_of_atomic_roots
    d P.center P.box P.bound P.time_bound μ s hsm hs hA η K₀ hK₀ hηK₀
    P.base P.neutral (P.neutral_open.measure_pos η P.neutral_nonempty).ne'
    P.in_box hatom
  refine ⟨F,hF,hunique,?_⟩
  exact neutral_patch_image_ae_graph (d+1) P.center μ s hsm hs τ η
    (translated_neutral_product (d+1) P.center μ s hsm hs hA η K₀ hK₀ hηK₀)
    P.base P.base_open.measurableSet P.neutral P.neutral_open.measurableSet
    (neutralQuotientParam_injOn (d+1) P.center P.box _ P.in_box) F hF hfull

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_NeutralPatchFuturePair
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-future pairs inside a graph patch differ by a neutral displacement -/

noncomputable section
open MeasureTheory Set Matrix
namespace DukePrimeDegree
open PrimeDegreePackets

theorem SmallNeutralPatch.graph_future_pair {n : ℕ} {ε : ℝ}
    (P : SmallNeutralPatch n ε)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
    (Q : X n → ℕ) (ρ : X n → ℝ)
    (hρ : ∀ x, ρ x ≤ 1) (hinj : ∀ x, LocalInjectivityAt (ρ x) x)
    (hlift : ∀ x y, (∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      ∃ g ∈ matrixBall n (ρ x), rightAction x g=y ∧
        ∀ i j, ell j < ell i → g.val i j=0)
    (F : Set (NeutralCoordinateBase n))
    (hF : ∀ x ∈ F, ∀ y ∈ F, x.1=y.1 → x.2=y.2)
    (x y : X n)
    (hx : x ∈ neutralQuotientParam n P.center ''
      ((P.base ×ˢ P.neutral) ∩ Prod.fst ⁻¹' F))
    (hy : y ∈ neutralQuotientParam n P.center ''
      ((P.base ×ˢ P.neutral) ∩ Prod.fst ⁻¹' F))
    (hε : ε ≤ ρ x)
    (hobs : fullFutureObservation
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 x =
      fullFutureObservation
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 y) :
    ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
      ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t) := by
  obtain ⟨z,⟨hz,hzF⟩,rfl⟩ := hx
  obtain ⟨w,⟨hw,hwF⟩,rfl⟩ := hy
  obtain ⟨g,hg,hgxy,hzero⟩ := hlift _ _ (fun k => by
    simpa only [fullFutureObservation,zero_add] using (congrFun hobs k).symm)
  have hchart := matrixBall_mono hε (P.small z hz w hw)
  obtain ⟨v,hv⟩ := neutral_graph_small_future_lift ell hord P.center F hF z w
    hzF hwF _ (hρ _) (hinj _) hchart g hg hzero hgxy
  refine ⟨g,matrixBall_mono (hρ _) hg,hgxy,?_⟩
  rw [hv]
  intro t
  apply commute_diagonalOneParameter_of_weight_support ell hell
  intro i j hij
  change (Matrix.diagonal (fun i => Real.exp (v.val i*1))) i j=0
  exact Matrix.diagonal_apply_ne _ (fun he => hij (congrArg ell he))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_AtomicFutureCover
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A full-measure countable neutral future cover from atomic intrinsic roots -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_atomic_neutral_future_cover_oai (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) (hord : StrictMono ell)
    (Q H : X (d+1) → ℕ) (hH : Measurable H)
    (r : ℕ → ℝ) (hanti : Antitone r) (hr : ∀ m, 0 < r m ∧ r m ≤ 1)
    (hinj : ∀ x, LocalInjectivityAt (r (H x)) x)
    (hlift : ∀ x y, (∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      ∃ g ∈ matrixBall (d+1) (r (H x)), rightAction x g=y ∧
        ∀ i j, ell j < ell i → g.val i j=0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (s : X (d+1) → G (d+1)) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup (d+1))) (s x)=x)
    (hA : ∀ v : transverseNeutralSpace (d+1),
      μ.map (fun x => rightAction x (diagonalOneParameter v.val v.prop 1))=μ)
    (η : Measure (transverseNeutralSpace (d+1))) [η.IsAddHaarMeasure]
    (K₀ : Set (transverseNeutralSpace (d+1))) (hK₀ : IsCompact K₀) (hηK₀ : η K₀=1)
    (z₀ : NeutralCoordinateBase (d+1) × transverseNeutralSpace (d+1))
    (hatom : ∀ p : ↥(allPositiveRoots (d+1) \ ∅), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0) :
    ∃ E : ℕ → Set (X (d+1)), (∀ i, MeasurableSet (E i)) ∧
      (∀ᵐ x ∂μ, x ∈ ⋃ i, E i) ∧
      ∀ i, ∀ x ∈ E i, ∀ y ∈ E i,
        fullFutureObservation
          (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 x =
        fullFutureObservation
          (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 y →
        ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
          ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t) := by
  classical
  choose P hP using fun m => exists_countable_small_neutral_patches (d+1) z₀ (hr m).1
  choose F hF hunique hfull using fun m j =>
    (P m j).exists_atomic_graph μ s hsm hs hA η K₀ hK₀ hηK₀ hatom
  let G (m j : ℕ) := neutralQuotientParam (d+1) (P m j).center ''
    (((P m j).base ×ˢ (P m j).neutral) ∩ Prod.fst ⁻¹' F m j)
  have hG (m j : ℕ) : MeasurableSet (G m j) := by
    apply neutralQuotientParam_measurable_image
    · exact ((P m j).base_open.measurableSet.prod
        (P m j).neutral_open.measurableSet).inter ((hF m j).preimage measurable_fst)
    · exact (neutralQuotientParam_injOn (d+1) (P m j).center (P m j).box _
        (P m j).in_box).mono inter_subset_left
  let E (k : ℕ) := G k.unpair.1 k.unpair.2 ∩ {x | H x ≤ k.unpair.1}
  have hgood : ∀ᵐ x ∂μ, ∀ m j, x ∈ (P m j).raw → x ∈ G m j :=
    ae_all_iff.mpr fun m => ae_all_iff.mpr fun j => hfull m j
  refine ⟨E,?_,?_,?_⟩
  · intro k
    exact (hG _ _).inter (hH measurableSet_Iic)
  · filter_upwards [hgood] with x hx
    have hxP : x ∈ ⋃ j, (P (H x) j).raw := by rw [hP]; trivial
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxP
    apply mem_iUnion.mpr
    refine ⟨Nat.pair (H x) j,?_⟩
    simpa only [E,Nat.unpair_pair,Set.mem_inter_iff,Set.mem_ofPred_eq] using And.intro (hx (H x) j hj) (le_refl (H x))
  · intro k x hx y hy hobs
    exact (P k.unpair.1 k.unpair.2).graph_future_pair ell hell hord Q
      (fun x => r (H x)) (fun x => (hr (H x)).2) hinj hlift
      (F k.unpair.1 k.unpair.2) (hunique _ _) x y hx.1 hy.1
      (hanti hx.2) hobs

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_atomic_neutral_future_cover_oai := @OAI.DukePrimeDegree.exists_atomic_neutral_future_cover_oai
