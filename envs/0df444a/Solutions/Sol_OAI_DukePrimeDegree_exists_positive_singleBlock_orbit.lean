-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_positive_singleBlock_orbit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:50:34.481948+00:00
-- url     : https://prove2.me/submissions/dd5e19db-7ab3-4c6d-af01-629a66b217f5

import Mathlib
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_DukePrimeDegree_exists_singleBlock_terminal_generic_set

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockDiagonalAlgebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The algebra of scalars on root blocks

For a partition of the coordinate indices, the block-scalar algebra is
the actual diagonal matrix algebra whose diagonal is constant on each
block. Its dimension is the number of blocks. It is also the common
centralizer of the full diagonal algebra and the elementary root
matrices within the blocks. These are algebraic statements, without
any homogeneous-measure classification assumption.
-/

noncomputable section
open Matrix
open scoped Classical

namespace DukePrimeDegree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mem_blockScalarAlgebra_iff (r : Setoid ι) (M : Matrix ι ι ℝ) :
    M ∈ blockScalarAlgebra r ↔
      M = Matrix.diagonal (fun i => M i i) ∧ ∀ i j, r i j → M i i = M j j := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨?_, ?_⟩
    · change Matrix.diagonal (fun i => c (Quotient.mk r i)) =
        Matrix.diagonal (fun i => Matrix.diagonal (fun k => c (Quotient.mk r k)) i i)
      simp only [Matrix.diagonal_apply_eq]
    · intro i j hij
      change Matrix.diagonal (fun k => c (Quotient.mk r k)) i i =
        Matrix.diagonal (fun k => c (Quotient.mk r k)) j j
      simpa only [Matrix.diagonal_apply_eq] using congrArg c (Quotient.sound hij)
  · rintro ⟨hd, hr⟩
    let c : Quotient r → ℝ := Quotient.lift (fun i => M i i) (fun i j hij => hr i j hij)
    refine ⟨c, ?_⟩
    change Matrix.diagonal (fun i => M i i) = M
    exact hd.symm

/-- A matrix commuting with every block scalar has no entries between
different coordinate blocks. -/
theorem commute_blockScalars_iff (r : Setoid ι) (M : Matrix ι ι ℝ) :
    (∀ A ∈ blockScalarAlgebra r, Commute M A) ↔
      ∀ i j, ¬ r i j → M i j = 0 := by
  constructor
  · intro h i j hij
    let c : Quotient r → ℝ := fun q => if q = Quotient.mk r i then 1 else 0
    have hq : Quotient.mk r j ≠ Quotient.mk r i := by
      intro he
      exact hij (r.symm (Quotient.exact he))
    have he := congrArg (fun A : Matrix ι ι ℝ => A i j)
      (h (blockScalarAlgHom r c) ⟨c, rfl⟩).eq
    change (M * Matrix.diagonal (fun k => c (Quotient.mk r k))) i j =
      (Matrix.diagonal (fun k => c (Quotient.mk r k)) * M) i j at he
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, c, hq] using he.symm
  · intro h A hA
    obtain ⟨c, rfl⟩ := hA
    change M * blockScalarAlgHom r c = blockScalarAlgHom r c * M
    ext i j
    change (M * Matrix.diagonal (fun k => c (Quotient.mk r k))) i j =
      (Matrix.diagonal (fun k => c (Quotient.mk r k)) * M) i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : r i j
    · rw [Quotient.sound hij, mul_comm]
    · rw [h i j hij, zero_mul, mul_zero]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_InverseEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets

lemma matrixBall_nhds_basis {n : ℕ} {U : Set (G n)} (hU : U ∈ 𝓝 (1 : G n)) :
    ∃ r : ℝ, 0 < r ∧ matrixBall n r ⊆ U := by
  have hv : Topology.IsInducing (fun g : G n => g.1) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.isInducing
  rw [hv.nhds_eq_comap] at hU
  obtain ⟨V,hV,hVU⟩ := Filter.mem_comap.mp hU
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r,hr,fun g hg => hVU (hsub ?_)⟩
  change dist g.1 (1 : G n).1 < r
  rw [dist_eq_norm]
  exact (Matrix.norm_lt_iff hr).mpr hg



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockNormalizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The connected normalizer of the block algebra

Conjugation permutes the primitive block projections. In a connected
family starting at the identity these projections cannot move, since
their diagonal coordinates remain idempotents. Consequently the identity
component of the block-algebra normalizer preserves every block.
-/

noncomputable section
open Matrix Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixConjugation_eq_self_iff {n : ℕ} (g : G n)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    slMatrixConjugation g M = M ↔ Commute M g.val := by
  constructor
  · intro h
    have he := congrArg (fun A => g.val * A) h
    have hg : g.val * g⁻¹.val = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    change M * g.val = g.val * M
    simpa only [slMatrixConjugation, ← mul_assoc, hg, one_mul] using he
  · exact slMatrixConjugation_eq_self g M

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockNormalizerFiniteIndex
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite quotient of the block normalizer

Conjugation acts on the finite set of idempotents in the block-scalar
algebra. The kernel is precisely the block matrix group. Thus the latter
has finite index in the full normalizer, including its disconnected part.
-/

noncomputable section
open Matrix Set
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixConjugation_eq_self_of_mem_blockMatrixGroup {n : ℕ}
    (r : Setoid (Fin n)) (g : G n) (hg : g ∈ blockMatrixGroup r)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ blockScalarAlgebra r) :
    slMatrixConjugation g M = M := by
  obtain ⟨hD, hc⟩ := (mem_blockScalarAlgebra_iff r M).mp hM
  rw [hD]
  exact hg _ hc

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockRootGroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The group generated by the roots within each block

The finite-orbit fixed-vector obstruction excludes singleton blocks.
Without singleton blocks, the full matrix commutant of the root-generated
group is exactly the block-scalar algebra. Its full normalizer therefore
lies in the scalar-algebra normalizer used in orbit reduction.
-/

noncomputable section
open Matrix Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma root_mem_blockRootGroup {n : ℕ} (r : Setoid (Fin n))
    (i j : Fin n) (hij : i ≠ j) (hr : r i j) (t : ℝ) :
    Matrix.SpecialLinearGroup.transvection hij t ∈ blockRootGroup r :=
  Subgroup.subset_closure ⟨i, j, hij, t, hr, rfl⟩

private lemma diagonal_commute_transvection_of_eq {n : ℕ}
    (c : Fin n → ℝ) (i j : Fin n) (t : ℝ) (hc : c i = c j) :
    Commute (Matrix.diagonal c) (Matrix.transvection i j t) := by
  change Matrix.diagonal c * Matrix.transvection i j t =
    Matrix.transvection i j t * Matrix.diagonal c
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hab : a = b
  · subst b
    rw [mul_comm]
  · by_cases hai : a = i
    · subst a
      by_cases hbj : b = j
      · subst b
        rw [hc, mul_comm]
      · simp [Matrix.transvection, hab, Ne.symm hbj]
    · simp [Matrix.transvection, hab, Ne.symm hai]

lemma blockRootGroup_le_blockMatrixGroup {n : ℕ} (r : Setoid (Fin n)) :
    blockRootGroup r ≤ blockMatrixGroup r := by
  rw [blockRootGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, t, hr, rfl⟩
  intro c hc
  apply slMatrixConjugation_eq_self
  exact diagonal_commute_transvection_of_eq c i j t (hc i j hr)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OrbitMeasureTransfer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Invariant measures on actual lattice orbits

The quotient by the actual point stabilizer injects into the lattice space.
For a closed matrix subgroup this injection is a Borel embedding, even when
the orbit is not closed. A finite invariant measure concentrated on that
orbit therefore pulls back to a finite invariant measure on the quotient.

This discharges the measure-transfer part of the homogeneous-orbit argument;
it does not assert the existence of a homogeneous orbit supporting a given
measure.
-/

noncomputable section
open MeasureTheory Set Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma isClosed_blockMatrixGroup {n : ℕ} (r : Setoid (Fin n)) :
    IsClosed (blockMatrixGroup r : Set (G n)) := by
  have he : (blockMatrixGroup r : Set (G n)) =
      ⋂ c : Fin n → ℝ, ⋂ (_hc : c ∈ blockCoordinateAlgebra r),
        {g : G n | slMatrixConjugation g (Matrix.diagonal c) = Matrix.diagonal c} := by
    ext g
    simp only [mem_iInter, mem_ofPred_eq]
    rfl
  rw [he]
  apply isClosed_iInter
  intro c
  apply isClosed_iInter
  intro _
  apply isClosed_eq _ continuous_const
  unfold slMatrixConjugation
  fun_prop

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockTransverseElimination
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing block directions by actual invariant roots

This is a sequence-level Gaussian elimination. No Lie-subgroup
classification or membership of the entire block group is assumed.
Every correction is a product of the specified within-block roots.
Pivots are eventually nonzero because the matrices tend to the identity.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma blockZeroPattern_translate {n : ℕ} (P : Finset (Fin n × Fin n))
    {a b : Fin n} (hab : a ≠ b)
    (hP : ∀ j, (j, b) ∈ P → (j, a) ∈ P)
    {g : G n} (hg : BlockZeroPattern P g) (t : ℝ) :
    BlockZeroPattern P (g * Matrix.SpecialLinearGroup.transvection hab t) := by
  intro p hp
  rw [root_mul_entry, hg p hp]
  by_cases hb : p.2 = b
  · have hz := hg (p.1, a) (hP p.1 (by simpa only [← hb, Prod.mk.eta] using hp))
    simp only [hb, ite_true, if_true, hz, zero_mul, add_zero]
  · simp only [hb, ite_false, if_false, add_zero]

namespace BlockEliminationChain

variable {n : ℕ} {r : Setoid (Fin n)} {P : Finset (Fin n × Fin n)}

/-- The correction converges to one, belongs to the actual root-generated
subgroup at every index, and eventually clears the entire schedule. -/
theorem normalize_sequence (c : BlockEliminationChain r P)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hzero : ∀ᶠ k in atTop, BlockZeroPattern P (g k)) :
    ∃ s b : ℕ → G n,
      Tendsto s atTop (𝓝 1) ∧ Tendsto b atTop (𝓝 1) ∧
      (∀ k, s k = g k * b k) ∧
      (∀ k, b k ∈ blockRootGroup r) ∧
      ∀ᶠ k in atTop, BlockZeroPattern c.finalEntries (s k) := by
  induction c generalizing g with
  | done =>
      exact ⟨g, fun _ => 1, hg, tendsto_const_nhds, fun _ => (mul_one _).symm,
        fun _ => (blockRootGroup r).one_mem, hzero⟩
  | @step P a b hab hr hP tail ih =>
      let t : ℕ → ℝ := fun k => -(g k).val a b / (g k).val a a
      let u : ℕ → G n := fun k => Matrix.SpecialLinearGroup.transvection hab (t k)
      have hentry (i j : Fin n) : Tendsto (fun k => (g k).val i j) atTop
          (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j)) := by
        have hc : Continuous (fun h : G n => h.val i j) := by fun_prop
        exact hc.continuousAt.tendsto.comp hg
      have hdiag : Tendsto (fun k => (g k).val a a) atTop (𝓝 1) := by
        simpa only [Matrix.one_apply_eq] using hentry a a
      have hoff : Tendsto (fun k => (g k).val a b) atTop (𝓝 0) := by
        simpa only [Matrix.one_apply_ne hab] using hentry a b
      have ht : Tendsto t atTop (𝓝 0) := by
        simpa only [t, Pi.div_def, Pi.neg_def, neg_zero, zero_div] using
          hoff.neg.div hdiag one_ne_zero
      have hu : Tendsto u atTop (𝓝 1) := by
        simpa only [u, Function.comp_def, Matrix.SpecialLinearGroup.transvection_coeff_zero] using
          (continuous_rootTransvection hab).continuousAt.tendsto.comp ht
      have hq : Tendsto (fun k => g k * u k) atTop (𝓝 1) := by
        simpa only [mul_one] using hg.mul hu
      have hnonzero : ∀ᶠ k in atTop, (g k).val a a ≠ 0 :=
        hdiag.eventually_ne one_ne_zero
      have hqzero : ∀ᶠ k in atTop,
          BlockZeroPattern (insert (a, b) P) (g k * u k) := by
        filter_upwards [hzero, hnonzero] with k hk hn
        intro p hp
        rcases Finset.mem_insert.mp hp with hp | hp
        · subst p
          dsimp only [u]
          rw [root_mul_entry]
          simp only [ite_true, if_true]
          dsimp only [t]
          field_simp
          ring
        · exact blockZeroPattern_translate P hab hP hk (t k) p hp
      obtain ⟨s, b', hs, hb', he, hmem, hz⟩ := ih _ hq hqzero
      refine ⟨s, fun k => u k * b' k, hs, ?_, ?_, ?_, hz⟩
      · simpa only [mul_one] using hu.mul hb'
      · intro k
        rw [he k, mul_assoc]
      · intro k
        exact (blockRootGroup r).mul_mem (root_mem_blockRootGroup r a b hab hr (t k)) (hmem k)

end BlockEliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockEliminationSchedule
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A full within-block elimination schedule

Upper entries are cleared in increasing row order, and lower entries
in decreasing row order. Transitivity of the block relation ensures
that each affected earlier entry has an earlier zero source entry.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

private theorem exists_upper_schedule {n : ℕ} (r : Setoid (Fin n))
    (P : Finset (Fin n × Fin n)) (hP : UpperInitial r P) :
    ∃ c : BlockEliminationChain r P, c.finalEntries = blockUpperEntries r := by
  suffices ∀ m : ℕ, ∀ P : Finset (Fin n × Fin n),
      (blockUpperEntries r \ P).card = m → UpperInitial r P →
      ∃ c : BlockEliminationChain r P, c.finalEntries = blockUpperEntries r by
    exact this _ P rfl hP
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro P hcard hP
    by_cases he : blockUpperEntries r \ P = ∅
    · refine ⟨.done, ?_⟩
      exact Finset.Subset.antisymm hP.1 (Finset.sdiff_eq_empty_iff_subset.mp he)
    · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (blockUpperEntries r \ P)
        (fun q => q.1) (Finset.nonempty_iff_ne_empty.mpr he)
      have hpU := (Finset.mem_sdiff.mp hp).1
      have hpnot := (Finset.mem_sdiff.mp hp).2
      obtain ⟨hab, hr⟩ := (mem_blockUpperEntries r p).mp hpU
      have hsmall (q : Fin n × Fin n) (hq : q ∈ blockUpperEntries r)
          (hlt : q.1 < p.1) : q ∈ P := by
        by_contra hnot
        exact (not_le_of_gt hlt) (hmin q (Finset.mem_sdiff.mpr ⟨hq, hnot⟩))
      have hstable : ∀ j, (j, p.2) ∈ P → (j, p.1) ∈ P := by
        intro j hj
        have hjU := (mem_blockUpperEntries r (j, p.2)).mp (hP.1 hj)
        have hjlt : j < p.1 := by
          by_contra h
          have hle : p.1 ≤ j := le_of_not_gt h
          rcases eq_or_lt_of_le hle with heq | hlt
          · apply hpnot
            simpa only [← heq, Prod.eta] using hj
          · exact hpnot (hP.2 (j, p.2) hj p hpU hlt)
        exact hsmall (j, p.1) ((mem_blockUpperEntries r _).mpr
          ⟨hjlt, r.trans hjU.2 (r.symm hr)⟩) hjlt
      have hnew : UpperInitial r (insert p P) := by
        constructor
        · intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hpU
          · exact hP.1 hq
        · intro q hq z hz hlt
          apply Finset.mem_insert_of_mem
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hsmall z hz hlt
          · exact hP.2 q hq z hz hlt
      have hless : (blockUpperEntries r \ insert p P).card < m := by
        rw [Finset.sdiff_insert, ← hcard]
        exact Finset.card_erase_lt_of_mem hp
      obtain ⟨tail, ht⟩ := ih _ hless (insert p P) rfl hnew
      exact ⟨.step p.1 p.2 (ne_of_lt hab) hr hstable tail, ht⟩

private theorem exists_lower_schedule {n : ℕ} (r : Setoid (Fin n))
    (Q : Finset (Fin n × Fin n)) (hQ : LowerInitial r Q) :
    ∃ c : BlockEliminationChain r (blockUpperEntries r ∪ Q),
      c.finalEntries = blockOffDiagonalEntries r := by
  suffices ∀ m : ℕ, ∀ Q : Finset (Fin n × Fin n),
      (blockLowerEntries r \ Q).card = m → LowerInitial r Q →
      ∃ c : BlockEliminationChain r (blockUpperEntries r ∪ Q),
        c.finalEntries = blockOffDiagonalEntries r by
    exact this _ Q rfl hQ
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro Q hcard hQ
    by_cases he : blockLowerEntries r \ Q = ∅
    · have heq : Q = blockLowerEntries r :=
        Finset.Subset.antisymm hQ.1 (Finset.sdiff_eq_empty_iff_subset.mp he)
      exact ⟨.done, by simp only [BlockEliminationChain.finalEntries, heq,
        blockOffDiagonalEntries]⟩
    · obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (blockLowerEntries r \ Q)
        (fun q => q.1) (Finset.nonempty_iff_ne_empty.mpr he)
      have hpL := (Finset.mem_sdiff.mp hp).1
      have hpnot := (Finset.mem_sdiff.mp hp).2
      obtain ⟨hba, hr⟩ := (mem_blockLowerEntries r p).mp hpL
      have hlarge (q : Fin n × Fin n) (hq : q ∈ blockLowerEntries r)
          (hlt : p.1 < q.1) : q ∈ Q := by
        by_contra hnot
        exact (not_le_of_gt hlt) (hmax q (Finset.mem_sdiff.mpr ⟨hq, hnot⟩))
      have hstable : ∀ j, (j, p.2) ∈ blockUpperEntries r ∪ Q →
          (j, p.1) ∈ blockUpperEntries r ∪ Q := by
        intro j hj
        rcases Finset.mem_union.mp hj with hj | hj
        · have hjU := (mem_blockUpperEntries r _).mp hj
          exact Finset.mem_union_left _ ((mem_blockUpperEntries r _).mpr
            ⟨hjU.1.trans hba, r.trans hjU.2 (r.symm hr)⟩)
        · have hjL := (mem_blockLowerEntries r _).mp (hQ.1 hj)
          have hjgt : p.1 < j := by
            by_contra h
            have hle : j ≤ p.1 := le_of_not_gt h
            rcases eq_or_lt_of_le hle with heq | hlt
            · apply hpnot
              simpa only [heq, Prod.eta] using hj
            · exact hpnot (hQ.2 (j, p.2) hj p hpL hlt)
          exact Finset.mem_union_right _ (hlarge (j, p.1)
            ((mem_blockLowerEntries r _).mpr
              ⟨hjgt, r.trans hjL.2 (r.symm hr)⟩) hjgt)
      have hnew : LowerInitial r (insert p Q) := by
        constructor
        · intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hpL
          · exact hQ.1 hq
        · intro q hq z hz hlt
          apply Finset.mem_insert_of_mem
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hlarge z hz hlt
          · exact hQ.2 q hq z hz hlt
      have hless : (blockLowerEntries r \ insert p Q).card < m := by
        rw [Finset.sdiff_insert, ← hcard]
        exact Finset.card_erase_lt_of_mem hp
      obtain ⟨tail, ht⟩ := ih _ hless (insert p Q) rfl hnew
      have heq : blockUpperEntries r ∪ insert p Q =
          insert p (blockUpperEntries r ∪ Q) := by ext q; simp
      have htail : ∃ c : BlockEliminationChain r (insert p (blockUpperEntries r ∪ Q)),
          c.finalEntries = blockOffDiagonalEntries r := by
        rw [← heq]
        exact ⟨tail, ht⟩
      obtain ⟨tail', ht'⟩ := htail
      exact ⟨.step p.1 p.2 (ne_of_lt hba).symm hr hstable tail', ht'⟩

/-- Every off-diagonal entry inside a block can be eliminated using
only roots from that block, with every earlier zero retained. -/
theorem exists_block_elimination_schedule {n : ℕ} (r : Setoid (Fin n)) :
    ∃ c : BlockEliminationChain r ∅, c.finalEntries = blockOffDiagonalEntries r := by
  obtain ⟨upper, hu⟩ := exists_upper_schedule r ∅ ⟨by simp, by simp⟩
  have hlower : ∃ c : BlockEliminationChain r upper.finalEntries,
      c.finalEntries = blockOffDiagonalEntries r := by
    rw [hu]
    have h := exists_lower_schedule r ∅ ⟨by simp, by simp⟩
    rw [Finset.union_empty] at h
    exact h
  obtain ⟨lower, hl⟩ := hlower
  exact ⟨upper.append lower, (BlockEliminationChain.finalEntries_append upper lower).trans hl⟩

/-- A near-identity sequence has an actual within-block root correction
which kills all its within-block off-diagonal entries. -/
theorem exists_block_transverse_sequence {n : ℕ} (r : Setoid (Fin n))
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1)) :
    ∃ s b : ℕ → G n,
      Tendsto s atTop (𝓝 1) ∧ Tendsto b atTop (𝓝 1) ∧
      (∀ k, s k = g k * b k) ∧ (∀ k, b k ∈ blockRootGroup r) ∧
      ∀ᶠ k in atTop, ∀ i j, i ≠ j → r i j → (s k).val i j = 0 := by
  obtain ⟨c, hc⟩ := exists_block_elimination_schedule r
  obtain ⟨s, b, hs, hb, he, hm, hz⟩ := c.normalize_sequence g hg
    (Filter.Eventually.of_forall (by intro k p hp; simp at hp))
  refine ⟨s, b, hs, hb, he, hm, ?_⟩
  filter_upwards [hz] with k hk i j hij hr
  apply hk (i, j)
  simpa only [hc] using (mem_blockOffDiagonalEntries r _).mpr ⟨hij, hr⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CompactAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact observables under small group translations

A compactly supported continuous observable changes uniformly little
under a group element tending to the identity. This remains true along
arbitrary moving base points, including points leaving compact sets.
It supplies the topological contraction step in the Hopf argument on a
noncompact homogeneous space.
-/

open Filter Set
open scoped Topology

namespace DukePrimeDegree

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [TopologicalSpace X] [MulAction G X]
  [ContinuousSMul G X]

/-- Small translations act uniformly continuously on a compactly
supported continuous real observable. -/
theorem compact_observable_smul_tendstoUniformly
    (f : X → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    TendstoUniformly (fun a : G => fun x : X => f (a • x)) f (𝓝 1) := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  let C : Set X := tsupport f ∪
    (fun z : G × X => z.1⁻¹ • z.2) '' (V ×ˢ tsupport f)
  have hCc : IsCompact C := hc.union
    ((hVc.prod hc).image (continuous_fst.inv.smul continuous_snd))
  have hcont : Continuous (fun z : G × X => f (z.1 • z.2)) := by
    fun_prop
  obtain ⟨W, hW, hsmallW⟩ := hCc.mem_uniformity_of_prod
    (f := fun a : G => fun x : X => f (a • x))
    (s := Set.univ) hcont.continuousOn (show (1 : G) ∈ Set.univ from Set.mem_univ _)
    (Metric.dist_mem_uniformity hε)
  have hsmall : ∀ᶠ a : G in 𝓝 1,
      ∀ x : C, dist (f (a • (x : X))) (f x) < ε := by
    have hW' : W ∈ 𝓝 (1 : G) := by simpa only [nhdsWithin_univ] using hW
    filter_upwards [hW'] with a ha x
    simpa only [one_smul, Set.mem_ofPred_eq] using hsmallW a ha x x.property
  filter_upwards [hV, hsmall] with a ha hs x
  by_cases hx : x ∈ C
  · simpa only [dist_comm] using hs ⟨x, hx⟩
  · have hx0 : f x = 0 := by
      by_contra hne
      exact hx (Or.inl (subset_tsupport f hne))
    have hax0 : f (a • x) = 0 := by
      by_contra hne
      apply hx
      exact Or.inr ⟨(a, a • x), ⟨ha, subset_tsupport f hne⟩, inv_smul_smul a x⟩
    simpa only [hx0, hax0, dist_self] using hε

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootShearing
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

/-- A quadratic polynomial bounded on the positive half-line is
constant. This version keeps the exact coefficients used in shearing. -/
lemma bounded_quadratic_constant (a b c B : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → |a + b * t + c * t ^ 2| ≤ B) :
    ∀ t : ℝ, a + b * t + c * t ^ 2 = a := by
  let P : Polynomial ℝ := Polynomial.C a + Polynomial.C b * Polynomial.X +
    Polynomial.C c * Polynomial.X ^ 2
  have heval (t : ℝ) : P.eval t = a + b * t + c * t ^ 2 := by simp [P]
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun t : ℝ => |P.eval t|) := by
    refine ⟨B, eventually_map.mpr ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa only [heval] using hbound t ht
  have hdeg : P.degree ≤ 0 := (Polynomial.isBoundedUnder_abs_atTop_iff P).mp hb
  have hc := Polynomial.eq_C_of_degree_le_zero hdeg
  have hconst (t : ℝ) : P.eval t = P.eval 0 := by rw [hc]; simp
  intro t
  simpa only [heval, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using hconst t

/-- A root-conjugation trajectory stays bounded for all positive times
only in the exceptional, centralizing case. -/
theorem commutes_root_of_bounded_conjugation {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (g : G n) (B : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → ∀ r s : Fin n,
      |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s| ≤ B) :
    ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g := by
  apply (commutes_root_one_iff_all hij g).mp
  have hconstant (t : ℝ) : Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t) = g := by
    ext r s
    let b : ℝ := (if r = i then g.1 j s else 0) -
      (if s = j then g.1 r i else 0)
    let c : ℝ := if r = i ∧ s = j then -g.1 j i else 0
    have hpoly (u : ℝ) :
        (Matrix.SpecialLinearGroup.transvection hij u * g *
          Matrix.SpecialLinearGroup.transvection hij (-u)).1 r s =
          g.1 r s + b * u + c * u ^ 2 := by
      rw [root_conjugation_entry]
      dsimp [b, c]
      split_ifs <;> ring
    rw [hpoly]
    apply bounded_quadratic_constant _ _ _ B ?_ t
    intro u hu
    rw [← hpoly]
    exact hbound u hu r s
  have hm := congrArg (fun h : G n => h * Matrix.SpecialLinearGroup.transvection hij 1)
    (hconstant 1)
  have hi : Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) *
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) = 1 := by
    simpa only [neg_neg] using Matrix.SpecialLinearGroup.transvection_mul_neg hij (-1 : ℝ)
  rw [mul_assoc, hi, mul_one] at hm
  exact hm.symm

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingScale
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A first scale for noncentral root shearing

Every matrix outside a root centralizer has a finite positive first time
at which its conjugation displacement reaches a prescribed size. Before
that time all matrix entries remain uniformly controlled. This is the
stopping-time normalization used for the polynomial shearing argument.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma continuous_first_level {f : ℝ → ℝ} (hf : Continuous f)
    {a T : ℝ} (hzero : f 0 < a) (hT : 0 ≤ T) (hlarge : a ≤ f T) :
    ∃ t : ℝ, 0 < t ∧ t ≤ T ∧ f t = a ∧ ∀ u ∈ Icc 0 t, f u ≤ a := by
  let S : Set ℝ := Icc 0 T ∩ {t | a ≤ f t}
  have hSc : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const hf)
  have hSne : S.Nonempty := ⟨T, ⟨⟨hT, le_rfl⟩, hlarge⟩⟩
  obtain ⟨t, ht, hmin⟩ := hSc.exists_isLeast hSne
  have ht0 : 0 < t := lt_of_le_of_ne ht.1.1 (by
    intro he
    have h := ht.2
    rw [← he] at h
    exact hzero.not_ge h)
  obtain ⟨u, hu, hue⟩ := intermediate_value_Icc ht.1.1 hf.continuousOn
    ⟨hzero.le, ht.2⟩
  have htu : t ≤ u := hmin ⟨⟨hu.1, hu.2.trans ht.1.2⟩, hue.symm.le⟩
  have hut : u = t := le_antisymm hu.2 htu
  have hteq : f t = a := hut ▸ hue
  refine ⟨t, ht0, ht.1.2, hteq, ?_⟩
  intro u hu
  by_contra h
  have hau : a < f u := lt_of_not_ge h
  have htu : t ≤ u := hmin ⟨⟨hu.1, hu.2.trans ht.1.2⟩, hau.le⟩
  have hut : u = t := le_antisymm hu.2 htu
  simp only [hut, hteq, lt_self_iff_false] at hau

lemma rootShearSize_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    rootShearSize hij g 0 = 0 := by
  simp [rootShearSize]

lemma continuous_rootShearSize {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    Continuous (rootShearSize hij g) := by
  have hroot := continuous_rootTransvection hij
  have hconj : Continuous (fun t : ℝ =>
      Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)) :=
    (hroot.mul continuous_const).mul (hroot.comp continuous_neg)
  unfold rootShearSize
  apply continuous_finsetSum
  intro r _
  apply continuous_finsetSum
  intro s _
  exact ((((continuous_apply s).comp (continuous_apply r)).comp
    (continuous_subtype_val.comp hconj)).sub continuous_const).abs

lemma entry_sub_le_rootShearSize {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t : ℝ) (r s : Fin n) :
    |(Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s| ≤
      rootShearSize hij g t := by
  have hs : |(Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s| ≤
      ∑ u : Fin n, |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r u - g.1 r u| :=
    Finset.single_le_sum (f := fun u : Fin n =>
      |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r u - g.1 r u|)
      (fun u _ => abs_nonneg _) (Finset.mem_univ s)
  apply hs.trans
  exact Finset.single_le_sum (f := fun u : Fin n => ∑ v : Fin n,
    |(Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 u v - g.1 u v|)
    (fun u _ => Finset.sum_nonneg (fun v _ => abs_nonneg _))
    (Finset.mem_univ r)

/-- There is no bounded positive root-conjugation trajectory outside
the root centralizer. -/
theorem exists_large_rootShearSize {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n)
    (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g) (a : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ a ≤ rootShearSize hij g t := by
  by_contra h
  push Not at h
  let B : ℝ := ∑ r, ∑ s, |g.1 r s|
  have hentry (r s : Fin n) : |g.1 r s| ≤ B := by
    have hs : |g.1 r s| ≤ ∑ v : Fin n, |g.1 r v| :=
      Finset.single_le_sum (f := fun v : Fin n => |g.1 r v|)
        (fun v _ => abs_nonneg _) (Finset.mem_univ s)
    apply hs.trans
    exact Finset.single_le_sum (f := fun u : Fin n => ∑ v : Fin n, |g.1 u v|)
      (fun u _ => Finset.sum_nonneg (fun v _ => abs_nonneg _))
      (Finset.mem_univ r)
  apply hnot
  apply commutes_root_of_bounded_conjugation hij g (a + B)
  intro t ht r s
  calc
    |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s| =
      |((Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s) + g.1 r s| :=
          by rw [sub_add_cancel]
    _ ≤ |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s| + |g.1 r s| :=
      abs_add_le _ _
    _ ≤ a + B := add_le_add ((entry_sub_le_rootShearSize hij g t r s).trans (h t ht).le)
      (hentry r s)

/-- A normalized finite shearing interval exists at every positive
displacement scale for any noncentral matrix. -/
theorem exists_first_rootShearScale {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n)
    (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    {a : ℝ} (ha : 0 < a) :
    ∃ t : ℝ, 0 < t ∧ rootShearSize hij g t = a ∧
      ∀ u ∈ Icc 0 t, rootShearSize hij g u ≤ a := by
  obtain ⟨T, hT, hlarge⟩ := exists_large_rootShearSize hij g hnot a
  obtain ⟨t, ht, _, heq, hsmall⟩ := continuous_first_level
    (continuous_rootShearSize hij g) (by simpa only [rootShearSize_zero] using ha) hT hlarge
  exact ⟨t, ht, heq, hsmall⟩

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingLimits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Divergence of the normalized shearing time

For matrices approaching the identity, every time at which root
conjugation has a fixed nonzero displacement tends to infinity. This
places the stopping-time normalization on the scale required for the
recurrence and leafwise comparison argument.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma rootShearSize_one {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : ℝ) :
    rootShearSize hij 1 t = 0 := by
  simp only [rootShearSize, mul_one, Matrix.SpecialLinearGroup.transvection_mul_neg,
    sub_self, abs_zero, Finset.sum_const_zero]

lemma continuous_rootShearSize_pair {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Continuous (fun z : G n × ℝ => rootShearSize hij z.1 z.2) := by
  have hroot := continuous_rootTransvection hij
  have hconj : Continuous (fun z : G n × ℝ =>
      Matrix.SpecialLinearGroup.transvection hij z.2 * z.1 *
        Matrix.SpecialLinearGroup.transvection hij (-z.2)) :=
    ((hroot.comp continuous_snd).mul continuous_fst).mul
      (hroot.comp continuous_snd.neg)
  unfold rootShearSize
  apply continuous_finsetSum
  intro r _
  apply continuous_finsetSum
  intro s _
  exact ((((continuous_apply s).comp (continuous_apply r)).comp
    (continuous_subtype_val.comp hconj)).sub
      (((continuous_apply s).comp (continuous_apply r)).comp
        (continuous_subtype_val.comp continuous_fst))).abs

theorem rootShearScale_tendsto_atTop {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, 0 ≤ t m) {a : ℝ} (ha : a ≠ 0)
    (hsize : ∀ m, rootShearSize hij (g m) (t m) = a) :
    Tendsto t atTop atTop := by
  by_contra h
  rw [tendsto_atTop] at h
  push Not at h
  obtain ⟨R, hR⟩ := h
  have hbounded : ∃ᶠ m : ℕ in atTop, t m ∈ Icc 0 R :=
    hR.mono fun m hm => ⟨ht m, hm.le⟩
  obtain ⟨v, _, φ, hφ, hv⟩ := isCompact_Icc.isSeqCompact.subseq_of_frequently_in hbounded
  have hgp : Tendsto (g ∘ φ) atTop (𝓝 1) := hg.comp hφ.tendsto_atTop
  have hlim := (continuous_rootShearSize_pair hij).continuousAt.tendsto.comp
    (hgp.prodMk_nhds hv)
  have hlim0 : Tendsto (fun m => rootShearSize hij (g (φ m)) (t (φ m)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, rootShearSize_one] using hlim
  have hconst : Tendsto (fun m => rootShearSize hij (g (φ m)) (t (φ m)))
      atTop (𝓝 a) := by
    simpa only [hsize] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
  exact ha (tendsto_nhds_unique hconst hlim0)

/-- Noncentral return matrices approaching the identity admit first
shearing intervals whose lengths diverge. -/
theorem exists_diverging_first_rootShearScale {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hnot : ∀ m, ¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g m)
    {a : ℝ} (ha : 0 < a) :
    ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧ ∀ m,
      0 < t m ∧ rootShearSize hij (g m) (t m) = a ∧
        ∀ u ∈ Icc 0 (t m), rootShearSize hij (g m) u ≤ a := by
  choose t ht heq hsmall using fun m => exists_first_rootShearScale hij (g m) (hnot m) ha
  exact ⟨t, rootShearScale_tendsto_atTop hij g hg t (fun m => (ht m).le) ha.ne' heq,
    fun m => ⟨ht m, heq m, hsmall m⟩⟩

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingCentralizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Centralizer limits of normalized shearing trajectories

Uniform control before the first shearing time bounds the quadratic
coefficient. Since the shearing times diverge, the diagonal disturbance
vanishes. Every convergent terminal matrix therefore lies in the root
centralizer. These conclusions use actual special-linear matrices.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma root_conjugation_pivot {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 i j - g.1 i j =
      t * (g.1 j j - g.1 i i) - t ^ 2 * g.1 j i := by
  rw [root_conjugation_entry]
  simp only [ite_true, if_true, and_self]
  ring

lemma root_shearing_quadratic_bound {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) {t a : ℝ} (ht : 0 ≤ t)
    (hsmall : ∀ u ∈ Icc 0 t, rootShearSize hij g u ≤ a) :
    |t ^ 2 * g.1 j i| ≤ 6 * a := by
  let f : ℝ → ℝ := fun u =>
    (Matrix.SpecialLinearGroup.transvection hij u * g *
      Matrix.SpecialLinearGroup.transvection hij (-u)).1 i j - g.1 i j
  have h1 : |f t| ≤ a :=
    (entry_sub_le_rootShearSize hij g t i j).trans (hsmall t ⟨ht, le_rfl⟩)
  have h2 : |f (t / 2)| ≤ a :=
    (entry_sub_le_rootShearSize hij g (t / 2) i j).trans
      (hsmall (t / 2) ⟨by linarith, by linarith⟩)
  have he : t ^ 2 * g.1 j i = 4 * f (t / 2) - 2 * f t := by
    have hf (u : ℝ) : f u = u * (g.1 j j - g.1 i i) - u ^ 2 * g.1 j i :=
      root_conjugation_pivot hij g u
    rw [hf, hf]
    ring
  rw [he]
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma root_shearing_linear_bound {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) {t a : ℝ} (ht : 0 < t)
    (hsmall : ∀ u ∈ Icc 0 t, rootShearSize hij g u ≤ a) :
    |t * g.1 j i| ≤ 6 * a / t := by
  apply (le_div_iff₀ ht).mpr
  have he : |t * g.1 j i| * t = |t ^ 2 * g.1 j i| := by
    simp only [abs_mul, abs_pow, abs_of_pos ht]
    ring
  rw [he]
  exact root_shearing_quadratic_bound hij g ht.le hsmall

/-- The diagonal perturbation tends to zero on a diverging normalized
shearing interval. -/
lemma tendsto_root_shearing_linear_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (t : ℕ → ℝ) (ht : ∀ m, 0 < t m)
    (htop : Tendsto t atTop atTop) (a : ℝ)
    (hsmall : ∀ m, ∀ u ∈ Icc 0 (t m), rootShearSize hij (g m) u ≤ a) :
    Tendsto (fun m => t m * (g m).1 j i) atTop (𝓝 0) := by
  apply squeeze_zero_norm
  · intro m
    simpa only [Real.norm_eq_abs] using
      root_shearing_linear_bound hij (g m) (ht m) (hsmall m)
  · exact tendsto_const_nhds.div_atTop htop

/-- Every terminal limit of a uniformly bounded normalized shearing
interval centralizes the original root subgroup. -/
theorem rootShearLimit_centralizes {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, 0 < t m) (htop : Tendsto t atTop atTop)
    (a : ℝ) (hsmall : ∀ m, ∀ u ∈ Icc 0 (t m), rootShearSize hij (g m) u ≤ a)
    (h : G n)
    (hlim : Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
      Matrix.SpecialLinearGroup.transvection hij (-t m)) atTop (𝓝 h)) :
    ∀ u : ℝ, h * Matrix.SpecialLinearGroup.transvection hij u =
      Matrix.SpecialLinearGroup.transvection hij u * h := by
  have hcont (r s : Fin n) : Continuous (fun g : G n => g.1 r s) := by fun_prop
  have hgentry (r s : Fin n) : Tendsto (fun m => (g m).1 r s) atTop
      (𝓝 ((1 : G n).1 r s)) :=
    (hcont r s).tendsto _ |>.comp hg
  have hhentry (r s : Fin n) : Tendsto (fun m =>
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).1 r s) atTop (𝓝 (h.1 r s)) :=
    (hcont r s).tendsto _ |>.comp hlim
  have hlinear := tendsto_root_shearing_linear_zero hij g t ht htop a hsmall
  apply (commutes_root_one_iff_all hij h).mp
  apply (commutes_root_one_iff hij h).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).1 r i) =
        (fun m => (g m).1 r i) := by
      funext m
      simp [root_conjugation_entry, hr, hij]
    have hzero : Tendsto (fun m => (g m).1 r i) atTop (𝓝 0) := by
      simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hr] using hgentry r i
    exact tendsto_nhds_unique (he ▸ hhentry r i) hzero
  · intro s hs
    have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).1 j s) =
        (fun m => (g m).1 j s) := by
      funext m
      simp [root_conjugation_entry, hs, hij.symm]
    have hzero : Tendsto (fun m => (g m).1 j s) atTop (𝓝 0) := by
      simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne (Ne.symm hs)] using hgentry j s
    exact tendsto_nhds_unique (he ▸ hhentry j s) hzero
  · have hdiag_i : h.1 i i = 1 := by
      have hconv := (hgentry i i).add hlinear
      have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
          Matrix.SpecialLinearGroup.transvection hij (-t m)).1 i i) =
          (fun m => (g m).1 i i + t m * (g m).1 j i) := by
        funext m
        simp [root_conjugation_entry, hij]
      have hone : Tendsto (fun m => (g m).1 i i + t m * (g m).1 j i) atTop (𝓝 1) := by
        simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, add_zero] using hconv
      exact tendsto_nhds_unique (he ▸ hhentry i i) hone
    have hdiag_j : h.1 j j = 1 := by
      have hconv := (hgentry j j).sub hlinear
      have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
          Matrix.SpecialLinearGroup.transvection hij (-t m)).1 j j) =
          (fun m => (g m).1 j j - t m * (g m).1 j i) := by
        funext m
        simp [root_conjugation_entry, hij.symm]
      have hone : Tendsto (fun m => (g m).1 j j - t m * (g m).1 j i) atTop (𝓝 1) := by
        simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, sub_zero] using hconv
      exact tendsto_nhds_unique (he ▸ hhentry j j) hone
    exact hdiag_i.trans hdiag_j.symm

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientNeighborhoods
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small relative lifts on the arithmetic quotient

Open quotient charts provide a neighborhood in which any two points are
related by a matrix in a prescribed identity neighborhood. This is the
local lifting step used with compactly controlled centralizer returns.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rightOrbitMap_isOpen {n : ℕ} (x : X n) :
    IsOpenMap (fun g : G n => rightAction x g) := by
  induction x using Quotient.inductionOn with
  | h q =>
    intro U hU
    change IsOpen ((fun g => Quotient.mk _ (q * g)) '' U)
    rw [← Set.image_image]
    exact (quotient_covering n).isOpenMap _ ((Homeomorph.mulLeft q).isOpenMap _ hU)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingCompactness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A nontrivial limit of normalized shearing

The normalized first shearing intervals provide bounded terminal
matrices. Finite-dimensional compactness supplies a convergent
subsequence, whose limit is nontrivial and centralizes the root group.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma continuous_slMatrixDifference {n : ℕ} :
    Continuous (fun z : G n × G n => slMatrixDifference z.1 z.2) := by
  unfold slMatrixDifference
  apply continuous_finsetSum
  intro r _
  apply continuous_finsetSum
  intro s _
  have hentry : Continuous (fun g : G n => g.1 r s) := by fun_prop
  exact ((hentry.comp continuous_fst).sub (hentry.comp continuous_snd)).abs

lemma slMatrixDifference_self {n : ℕ} (g : G n) : slMatrixDifference g g = 0 := by
  simp [slMatrixDifference]

/-- A normalized, bounded shearing sequence has a nonidentity
subsequential limit in the root centralizer. -/
theorem exists_nontrivial_rootShearLimit {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, 0 < t m) (htop : Tendsto t atTop atTop)
    {a : ℝ} (ha : 0 < a)
    (hsize : ∀ m, rootShearSize hij (g m) (t m) = a)
    (hsmall : ∀ m, ∀ u ∈ Icc 0 (t m), rootShearSize hij (g m) u ≤ a) :
    ∃ h : G n, h ≠ 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (t (φ m)) * g (φ m) *
        Matrix.SpecialLinearGroup.transvection hij (-t (φ m))) atTop (𝓝 h) ∧
      ∀ u : ℝ, h * Matrix.SpecialLinearGroup.transvection hij u =
        Matrix.SpecialLinearGroup.transvection hij u * h := by
  let H : ℕ → G n := fun m => Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
    Matrix.SpecialLinearGroup.transvection hij (-t m)
  have hcont (r s : Fin n) : Continuous (fun g : G n => g.1 r s) := by fun_prop
  have hgentry (r s : Fin n) : Tendsto (fun m => (g m).1 r s) atTop
      (𝓝 ((1 : G n).1 r s)) :=
    (hcont r s).tendsto _ |>.comp hg
  have hgsmall : ∀ᶠ m : ℕ in atTop, ∀ r s : Fin n, |(g m).1 r s| ≤ 2 := by
    apply Filter.eventually_all.mpr
    intro r
    apply Filter.eventually_all.mpr
    intro s
    have hval : |(1 : G n).1 r s| < (2 : ℝ) := by
      simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
      split_ifs <;> norm_num
    exact ((hgentry r s).abs.eventually (gt_mem_nhds hval)).mono fun _ hm => hm.le
  let K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {M | ∀ r s, |M r s| ≤ a + 2}
  have hK : IsCompact K := by
    have hbox : IsCompact {M : Matrix (Fin n) (Fin n) ℝ |
        ∀ r s, M r s ∈ Icc (-(a + 2)) (a + 2)} :=
      isCompact_pi_infinite fun _ : Fin n =>
      isCompact_pi_infinite fun _ : Fin n =>
        (isCompact_Icc : IsCompact (Icc (-(a + 2)) (a + 2)))
    simpa only [K, mem_Icc, abs_le] using hbox
  have hHK : ∀ᶠ m : ℕ in atTop, (H m).1 ∈ K := by
    filter_upwards [hgsmall] with m hm
    intro r s
    calc
      |(H m).1 r s| = |((H m).1 r s - (g m).1 r s) + (g m).1 r s| :=
        by rw [sub_add_cancel]
      _ ≤ |(H m).1 r s - (g m).1 r s| + |(g m).1 r s| := abs_add_le _ _
      _ ≤ a + 2 := add_le_add
        ((entry_sub_le_rootShearSize hij (g m) (t m) r s).trans_eq (hsize m)) (hm r s)
  obtain ⟨M, _, φ, hφ, hM⟩ := hK.tendsto_subseq' hHK.frequently
  have hdet : M.det = 1 := by
    apply (isClosed_eq continuous_id.matrix_det continuous_const).mem_of_tendsto hM
    exact Filter.Eventually.of_forall fun m => (H (φ m)).property
  let h : G n := ⟨M, hdet⟩
  have hH : Tendsto (H ∘ φ) atTop (𝓝 h) := by
    apply tendsto_subtype_rng.mpr
    exact hM
  have hgp : Tendsto (g ∘ φ) atTop (𝓝 1) := hg.comp hφ.tendsto_atTop
  have hD := continuous_slMatrixDifference.continuousAt.tendsto.comp (hH.prodMk_nhds hgp)
  have hD' : Tendsto (fun m => slMatrixDifference (H (φ m)) (g (φ m)))
      atTop (𝓝 (slMatrixDifference h 1)) := by
    simpa only [Function.comp_def] using hD
  have hDc : Tendsto (fun m => slMatrixDifference (H (φ m)) (g (φ m)))
      atTop (𝓝 a) := by
    have he (m : ℕ) : slMatrixDifference (H (φ m)) (g (φ m)) = a := hsize (φ m)
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
  have hne : h ≠ 1 := by
    intro he
    have hdiff := tendsto_nhds_unique hD' hDc
    rw [he, slMatrixDifference_self] at hdiff
    exact ha.ne' hdiff.symm
  refine ⟨h, hne, φ, hφ, hH, ?_⟩
  exact rootShearLimit_centralizes hij (g ∘ φ) hgp (t ∘ φ) (fun m => ht (φ m))
    (htop.comp hφ.tendsto_atTop) a (fun m => hsmall (φ m)) h hH

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_InvariantMeasureGroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The closed group preserving a finite measure

The ambient measure stabilizer is closed. Consequently the topological
closure of the invariant root-generated group still preserves the measure.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace PrimeDegreePackets

lemma continuous_integral_rightAction {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ]
    (f : CompactlySupportedContinuousMap (X n) ℝ) : Continuous (fun g : G n => ∫ x, f (rightAction x g) ∂μ) := by
  apply continuous_of_dominated
    (bound := fun _ => ‖f.toBoundedContinuousFunction‖)
  · intro g
    exact (f.continuous.comp (continuous_rightAction g)).aestronglyMeasurable
  · intro g
    exact Eventually.of_forall fun x => f.toBoundedContinuousFunction.norm_coe_le_norm _
  · exact integrable_const _
  · apply Eventually.of_forall
    intro x
    apply f.continuous.comp
    induction x using Quotient.inductionOn with
    | h g =>
      exact continuous_quotient_mk'.comp (continuous_const.mul continuous_id)

lemma invariantRightSubgroup_eq_tests {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ] :
    (invariantRightSubgroup μ : Set (G n)) =
      ⋂ f : CompactlySupportedContinuousMap (X n) ℝ, {g | (∫ x, f (rightAction x g) ∂μ) = ∫ x, f x ∂μ} := by
  ext g
  simp only [mem_iInter, mem_ofPred_eq]
  constructor
  · intro hg f
    change μ.map (fun x => rightAction x g) = μ at hg
    have he := integral_map (μ := μ) (φ := fun x => rightAction x g)
      (f := fun x => f x) (continuous_rightAction g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable
    rw [hg] at he
    exact he.symm
  · intro hg
    change μ.map (fun x => rightAction x g) = μ
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := μ) (f := fun x => f x)
      (continuous_rightAction g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
    exact hg f

/-- The stabilizer of a finite measure is a closed subgroup of the real
special linear group. -/
theorem isClosed_invariantRightSubgroup {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ] :
    IsClosed (invariantRightSubgroup μ : Set (G n)) := by
  rw [invariantRightSubgroup_eq_tests]
  exact isClosed_iInter fun f => isClosed_eq (continuous_integral_rightAction μ f) continuous_const

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_TransverseStabilizerLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A transverse diagonal limit lies outside the stabilizer

The previously proved commutator identities give a global statement:
an element of L with nonzero diagonal preserves the maximal root blocks.
Consequently a nonidentity diagonal-conjugation limit with zero
within-block off-diagonal entries cannot belong to L. No additional
"limit outside L" assumption or connectedness assumption is used.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma mem_blockMatrixGroup_of_cross_zero {n : ℕ} (r : Setoid (Fin n))
    (g : G n) (hzero : ∀ i j, ¬ r i j → g.val i j = 0) :
    g ∈ blockMatrixGroup r := by
  have hcomm := (commute_blockScalars_iff r g.val).mpr hzero
  intro c hc
  apply slMatrixConjugation_eq_self
  apply Commute.symm
  apply hcomm
  refine (mem_blockScalarAlgebra_iff r _).mpr ⟨by simp, ?_⟩
  intro i j hij
  simpa only [Matrix.diagonal_apply_eq] using hc i j hij

lemma cross_zero_of_mem_blockMatrixGroup {n : ℕ} (r : Setoid (Fin n))
    (g : G n) (hg : g ∈ blockMatrixGroup r) :
    ∀ i j, ¬ r i j → g.val i j = 0 := by
  apply (commute_blockScalars_iff r g.val).mp
  intro M hM
  exact ((slMatrixConjugation_eq_self_iff g M).mp
    (slMatrixConjugation_eq_self_of_mem_blockMatrixGroup r g hg M hM)).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockMatrixProjection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The within-block matrix projection

The projection onto the within-block entries commutes with multiplication
by block-diagonal matrices on either side. Hence a scalar within-block
part stays scalar under every within-block conjugation, including the
unipotent shears used in the stopping-time argument.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma withinBlockPart_mul_left {n : ℕ} (r : Setoid (Fin n))
    (A M : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, ¬ r i j → A i j = 0) :
    withinBlockPart r (A * M) = A * withinBlockPart r M := by
  ext i j
  by_cases hij : r i j
  · simp only [withinBlockPart, hij, ite_true, if_true, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : r i k
    · have hkj : r k j := r.trans (r.symm hik) hij
      simp only [hkj, ite_true, if_true]
    · simp only [hA i k hik, zero_mul]
  · simp only [withinBlockPart, hij, ite_false, if_false, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hkj : r k j
    · have hik : ¬ r i k := fun hik => hij (r.trans hik hkj)
      simp only [hA i k hik, zero_mul]
    · simp only [hkj, ite_false, if_false, mul_zero]

lemma withinBlockPart_mul_right {n : ℕ} (r : Setoid (Fin n))
    (M B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i j, ¬ r i j → B i j = 0) :
    withinBlockPart r (M * B) = withinBlockPart r M * B := by
  ext i j
  by_cases hij : r i j
  · simp only [withinBlockPart, hij, ite_true, if_true, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkj : r k j
    · have hik : r i k := r.trans hij (r.symm hkj)
      simp only [hik, ite_true, if_true]
    · simp only [hB k j hkj, mul_zero]
  · simp only [withinBlockPart, hij, ite_false, if_false, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : r i k
    · have hkj : ¬ r k j := fun hkj => hij (r.trans hik hkj)
      simp only [hB k j hkj, mul_zero]
    · simp only [hik, ite_false, if_false, zero_mul]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingMeasureLimits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A limiting shear preserves the limiting measure

This is the measure step in the unipotent shearing argument. If two
families of probability measures have the same weak limit, and one is
the translate of the other by converging group elements, the limiting
element preserves that measure. Compact observables give uniform control
even when the sampled points leave every compact set.
-/

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology BoundedContinuousFunction

namespace DukePrimeDegree

variable {G X I : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [TopologicalSpace X] [LocallyCompactSpace X]
  [T2Space X] [MetrizableSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]
  {l : Filter I} [NeBot l]

omit [LocallyCompactSpace X] [T2Space X] [MetrizableSpace X] [SigmaCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [NeBot l] in
/-- Moving translations of a compact observable converge uniformly. -/
lemma compact_observable_varying_smul
    (f : X → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (a : I → G) (g : G) (ha : Tendsto a l (𝓝 g)) :
    ∀ ε > 0, ∀ᶠ i in l, ∀ x,
      |f (a i • x) - f (g • x)| < ε := by
  have hid : Tendsto (fun i => a i * g⁻¹) l (𝓝 1) := by
    simpa only [mul_inv_cancel] using ha.mul_const g⁻¹
  intro ε hε
  have hu := Metric.tendstoUniformly_iff.mp
    (compact_observable_smul_tendstoUniformly (G := G) f hf hc) ε hε
  filter_upwards [hid.eventually hu] with i hi x
  simpa only [mul_smul, inv_smul_smul, Real.dist_eq, abs_sub_comm] using hi (g • x)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CompactFamilyGeneric
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A fixed generic set for a compact family of observables

The limiting shear is selected after the generic set. Compactness of the
possible shears gives a compact family of translated observables in the
uniform norm. A finite approximation therefore suffices for one common
generic set and time threshold. No commutation of the translating group
with the averaging flow is required.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree

theorem continuous_compactObservableTranslate
    {H Y : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [WeaklyLocallyCompactSpace H] [TopologicalSpace Y]
    [MulAction H Y] [ContinuousSMul H Y]
    (f : CompactlySupportedContinuousMap Y ℝ) :
    Continuous (compactObservableTranslate (H := H) f) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [compact_observable_varying_smul f f.continuous f.hasCompactSupport
    (id : H → H) a tendsto_id ε hε] with b hb x
  simpa only [compactObservableTranslate, BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk, CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
    id_eq, Real.dist_eq, abs_sub_comm] using hb x

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CompactStabilizerSeparation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finitely many observables separate a compact set from the stabilizer

The eventual shearing contradiction only needs a fixed finite family
of generic observables. Continuity and compactness produce that family
and a uniform positive separation, directly from the actual measure
stabilizer. No empirical-convergence or homogeneous-orbit premise is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma continuous_invarianceDefect {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ]
    (f : CompactlySupportedContinuousMap (X n) ℝ) :
    Continuous (invarianceDefect μ f) :=
  (continuous_integral_rightAction μ f).sub continuous_const

lemma exists_nonzero_invarianceDefect {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ]
    (g : G n) (hg : g ∉ invariantRightSubgroup μ) :
    ∃ f : CompactlySupportedContinuousMap (X n) ℝ, invarianceDefect μ f g ≠ 0 := by
  by_contra h
  push Not at h
  apply hg
  change g ∈ (invariantRightSubgroup μ : Set (G n))
  rw [invariantRightSubgroup_eq_tests]
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  intro f
  exact sub_eq_zero.mp (h f)

/-- A fixed finite family distinguishes every possible limiting shear
in a compact set disjoint from the actual stabilizer. -/
theorem exists_finite_compact_stabilizer_separators {n : ℕ}
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (K : Set (G n)) (hK : IsCompact K)
    (hout : ∀ g ∈ K, g ∉ invariantRightSubgroup μ) :
    ∃ (F : Finset (CompactlySupportedContinuousMap (X n) ℝ)) (ε : ℝ),
      0 < ε ∧ ∀ g ∈ K, ∃ f ∈ F, ε < |invarianceDefect μ f g| := by
  by_cases hne : K.Nonempty
  · choose f hf using fun g : K => exists_nonzero_invarianceDefect μ g.val (hout g.val g.property)
    let e : K → ℝ := fun g => |invarianceDefect μ (f g) g.val| / 2
    have he (g : K) : 0 < e g := half_pos (abs_pos.mpr (hf g))
    let U : K → Set (G n) := fun g => {a | e g < |invarianceDefect μ (f g) a|}
    have hopen (g : K) : IsOpen (U g) :=
      isOpen_lt continuous_const (continuous_invarianceDefect μ (f g)).abs
    have hself (g : K) : g.val ∈ U g := by
      change |invarianceDefect μ (f g) g.val| / 2 < |invarianceDefect μ (f g) g.val|
      linarith [abs_pos.mpr (hf g)]
    have hcover : K ⊆ ⋃ g : K, U g := by
      intro g hg
      exact mem_iUnion.mpr ⟨⟨g, hg⟩, hself ⟨g, hg⟩⟩
    obtain ⟨J, hJ⟩ := hK.elim_finite_subcover U hopen hcover
    have hJne : J.Nonempty := by
      obtain ⟨g, hg⟩ := hne
      obtain ⟨a, ha, _⟩ := mem_iUnion₂.mp (hJ hg)
      exact ⟨a, ha⟩
    obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image J e hJne
    refine ⟨J.image f, e a, he a, ?_⟩
    intro g hg
    obtain ⟨b, hb, hgb⟩ := mem_iUnion₂.mp (hJ hg)
    exact ⟨f b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, (hmin b hb).trans_lt hgb⟩
  · refine ⟨∅, 1, zero_lt_one, ?_⟩
    intro g hg
    exact (hne ⟨g, hg⟩).elim

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_GoodSetFiberCorrection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correcting a pair inside a large generic set

The two initial points may be corrected by a changing element of the
measure stabilizer.  Averaging the bad set along a fixed group patch
gives a larger good set.  For two points in that larger set, a common
group translation restores membership in the original generic set.
No commutation with the averaging flow is needed for this selection.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree

section FiberMass

variable {H Y : Type*} [MeasurableSpace H] [MeasurableSpace Y]

lemma badOrbitFiberMass_eq_measure (ρ : Measure H) (R : Y → H → Y)
    (K : Set H) (G : Set Y) (hG : MeasurableSet G)
    (x : Y) (hR : Measurable (R x)) :
    badOrbitFiberMass ρ R K G x = ρ (K ∩ {h | R x h ∉ G}) := by
  unfold badOrbitFiberMass
  change (∫⁻ h in K, ((R x) ⁻¹' Gᶜ).indicator (1 : H → ℝ≥0∞) h ∂ρ) = _
  rw [lintegral_indicator_one (hG.compl.preimage hR),
    Measure.restrict_apply (hG.compl.preimage hR)]
  congr 1
  ext h
  simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_ofPred_eq]
  exact and_comm

lemma measurable_badOrbitFiberMass (ρ : Measure H) [SFinite ρ]
    (R : Y → H → Y) (hR : Measurable (Function.uncurry R))
    (K : Set H) (G : Set Y) (hG : MeasurableSet G) :
    Measurable (badOrbitFiberMass ρ R K G) := by
  exact ((measurable_const.indicator hG.compl).comp hR).lintegral_prod_right'

/-- Invariance gives the exact average bad-fiber mass. -/
lemma lintegral_badOrbitFiberMass
    (μ : Measure Y) [SFinite μ] (ρ : Measure H) [SFinite ρ]
    (R : Y → H → Y) (hR : Measurable (Function.uncurry R))
    (hinv : ∀ h, MeasurePreserving (fun x => R x h) μ μ)
    (K : Set H) (G : Set Y) (hG : MeasurableSet G) :
    (∫⁻ x, badOrbitFiberMass ρ R K G x ∂μ) = ρ K * μ Gᶜ := by
  unfold badOrbitFiberMass
  have hm : AEMeasurable (Function.uncurry
      (fun x h => Gᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (R x h)))
      (μ.prod (ρ.restrict K)) :=
    ((measurable_const.indicator hG.compl).comp hR).aemeasurable
  rw [lintegral_lintegral_swap hm]
  have hinner (h : H) :
      (∫⁻ x, Gᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (R x h) ∂μ) = μ Gᶜ := by
    change (∫⁻ x, ((fun x => R x h) ⁻¹' Gᶜ).indicator
      (1 : Y → ℝ≥0∞) x ∂μ) = _
    rw [lintegral_indicator_one (hG.compl.preimage (hinv h).measurable)]
    rw [← Measure.map_apply (hinv h).measurable hG.compl, (hinv h).map_eq]
  simp_rw [hinner]
  rw [setLIntegral_const, mul_comm]

/-- The enlarged good set has an explicit complement bound and a
pointwise fiber estimate, rather than only an almost-everywhere one. -/
theorem exists_goodOrbitFiber_set
    (μ : Measure Y) [SFinite μ] (ρ : Measure H) [SFinite ρ]
    (R : Y → H → Y) (hR : Measurable (Function.uncurry R))
    (hinv : ∀ h, MeasurePreserving (fun x => R x h) μ μ)
    (K : Set H) (G : Set Y) (hG : MeasurableSet G)
    (a : ℝ≥0∞) (ha : a ≠ 0) (hatop : a ≠ ⊤) :
    ∃ E : Set Y, MeasurableSet E ∧
      μ Eᶜ ≤ (ρ K * μ Gᶜ) / a ∧
      ∀ x ∈ E, badOrbitFiberMass ρ R K G x < a := by
  let E := {x | badOrbitFiberMass ρ R K G x < a}
  have hm := measurable_badOrbitFiberMass ρ R hR K G hG
  refine ⟨E, measurableSet_lt hm measurable_const, ?_, fun _ hx => hx⟩
  have heq : Eᶜ = {x | a ≤ badOrbitFiberMass ρ R K G x} := by
    ext x
    simp only [E, mem_compl_iff, mem_ofPred_eq, not_lt]
  rw [heq]
  simpa only [lintegral_badOrbitFiberMass μ ρ R hR hinv K G hG] using
    meas_ge_le_lintegral_div (hm.aemeasurable (μ := μ)) ha hatop

/-- A small original exceptional set leaves a genuinely positive-mass
set of points with uniformly small bad fibers. -/
theorem exists_positive_goodOrbitFiber_set
    (μ : Measure Y) [IsProbabilityMeasure μ] (ρ : Measure H) [SFinite ρ]
    (R : Y → H → Y) (hR : Measurable (Function.uncurry R))
    (hinv : ∀ h, MeasurePreserving (fun x => R x h) μ μ)
    (K : Set H) (G : Set Y) (hG : MeasurableSet G)
    (a : ℝ≥0∞) (ha : a ≠ 0) (hatop : a ≠ ⊤)
    (hbudget : (ρ K * μ Gᶜ) / a < 1) :
    ∃ E : Set Y, MeasurableSet E ∧ μ E ≠ 0 ∧
      ∀ x ∈ E, badOrbitFiberMass ρ R K G x < a := by
  obtain ⟨E, hE, hbound, hsmall⟩ :=
    exists_goodOrbitFiber_set μ ρ R hR hinv K G hG a ha hatop
  refine ⟨E, hE, ?_, hsmall⟩
  intro hzero
  have hcompl : μ Eᶜ = 1 := by
    simpa only [hzero, zero_add, measure_univ] using measure_add_measure_compl (μ := μ) hE
  have hlt := hbound.trans_lt hbudget
  rw [hcompl] at hlt
  exact lt_irrefl _ hlt

end FiberMass

section CommonCorrection

variable {H Y : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
  [MeasurableSpace Y]

/-- A common bounded translation corrects both points.  The first
correction is allowed to vary and need not commute with any flow. -/
theorem exists_common_goodOrbit_correction
    (ρ : Measure H) [ρ.IsMulLeftInvariant]
    (R : Y → H → Y) (hR : ∀ x, Measurable (R x))
    (K₀ K₁ : Set H) (hK : K₀ ⊆ K₁)
    (G : Set Y) (hG : MeasurableSet G) (x y : Y) (b : H)
    (hb : ∀ h ∈ K₀, b * h ∈ K₁)
    (hsmall : badOrbitFiberMass ρ R K₁ G x +
      badOrbitFiberMass ρ R K₁ G y < ρ K₀) :
    ∃ h ∈ K₀, R x h ∈ G ∧ R y (b * h) ∈ G := by
  classical
  let Dₓ := K₁ ∩ {h | R x h ∉ G}
  let Dᵧ := K₁ ∩ {h | R y h ∉ G}
  have hxmass : ρ Dₓ = badOrbitFiberMass ρ R K₁ G x :=
    (badOrbitFiberMass_eq_measure ρ R K₁ G hG x (hR x)).symm
  have hymass : ρ Dᵧ = badOrbitFiberMass ρ R K₁ G y :=
    (badOrbitFiberMass_eq_measure ρ R K₁ G hG y (hR y)).symm
  by_contra hn
  have hcover : K₀ ⊆ Dₓ ∪ (fun h => b * h) ⁻¹' Dᵧ := by
    intro h hh
    by_cases hx : R x h ∈ G
    · right
      refine ⟨hb h hh, ?_⟩
      intro hy
      exact hn ⟨h, hh, hx, hy⟩
    · exact Or.inl ⟨hK hh, hx⟩
  have hle : ρ K₀ ≤ badOrbitFiberMass ρ R K₁ G x +
      badOrbitFiberMass ρ R K₁ G y := by
    calc
      ρ K₀ ≤ ρ (Dₓ ∪ (fun h => b * h) ⁻¹' Dᵧ) := measure_mono hcover
      _ ≤ ρ Dₓ + ρ ((fun h => b * h) ⁻¹' Dᵧ) := measure_union_le _ _
      _ = _ := by rw [measure_preimage_mul, hxmass, hymass]
  exact (not_le_of_gt hsmall) hle

end CommonCorrection

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CorrectedGenericPairs
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous generic representatives of a transverse pair

A correction in a block-preserving subgroup may depend on the pair.
The Haar-fiber selection puts both corrected points back in the same
generic set, and simultaneous block conjugation preserves the scalar
within-block normalization.  The subgroup is contained in the actual
measure stabilizer in the application; that inclusion is explicit here.
-/

noncomputable section
open MeasureTheory Set Matrix
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma measurable_rightAction_subgroup_uncurry {n : ℕ} (H : Subgroup (G n)) :
    Measurable (fun p : X n × H => rightAction p.1 (p.2 : G n)) := by
  exact ((continuous_rightAction_uncurry n).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).measurable

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingWindow
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform control on a terminal shearing window

A quadratic displacement bounded up to its stopping time changes by at
most a fixed multiple of the relative window length near that time. This
is the quantitative algebra needed to replace a short orbit window by a
single terminal shear in the measure argument.
-/

noncomputable section
open Set Matrix Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma quadratic_sample_coefficient_bounds (B C a : ℝ)
    (hfull : |B + C| ≤ a) (hhalf : |B / 2 + C / 4| ≤ a) :
    |B| ≤ 5 * a ∧ |C| ≤ 6 * a := by
  have h1 := abs_le.mp hfull
  have h2 := abs_le.mp hhalf
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

lemma quadratic_terminal_window_bound (B C a s : ℝ)
    (hfull : |B + C| ≤ a) (hhalf : |B / 2 + C / 4| ≤ a)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    |B * s + C * s ^ 2 - (B + C)| ≤ 17 * a * (1 - s) := by
  obtain ⟨hB, hC⟩ := quadratic_sample_coefficient_bounds B C a hfull hhalf
  have ha : 0 ≤ a := (abs_nonneg (B + C)).trans hfull
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have he : B * s + C * s ^ 2 - (B + C) = (s - 1) * (B + (s + 1) * C) := by ring
  rw [he, abs_mul, abs_of_nonpos (sub_nonpos.mpr hs.2), neg_sub]
  calc
    (1 - s) * |B + (s + 1) * C| ≤
        (1 - s) * (|B| + |s + 1| * |C|) := by
      apply mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr hs1)
      simpa only [abs_mul] using abs_add_le B ((s + 1) * C)
    _ ≤ (1 - s) * (5 * a + 2 * (6 * a)) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ s + 1)]
      apply mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr hs1)
      apply add_le_add hB
      exact (mul_le_mul_of_nonneg_right (by linarith : s + 1 ≤ 2) (abs_nonneg C)).trans
        (mul_le_mul_of_nonneg_left hC (by norm_num))
    _ = 17 * a * (1 - s) := by ring

/-- Every matrix entry stays close to its terminal value on a short
relative window, uniformly over all stopping times and nearby matrices. -/
theorem root_conjugation_terminal_window {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) {T a : ℝ} (hT : 0 < T)
    (hbound : ∀ t ∈ Icc 0 T, rootShearSize hij g t ≤ a)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (r q : Fin n) :
    |(Matrix.SpecialLinearGroup.transvection hij (s * T) * g *
        Matrix.SpecialLinearGroup.transvection hij (-(s * T))).val r q -
      (Matrix.SpecialLinearGroup.transvection hij T * g *
        Matrix.SpecialLinearGroup.transvection hij (-T)).val r q| ≤
      17 * a * (1 - s) := by
  let b : ℝ := (if r = i then g.val j q else 0) -
    (if q = j then g.val r i else 0)
  let c : ℝ := if r = i ∧ q = j then -g.val j i else 0
  have hpoly (t : ℝ) :
      (Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).val r q =
        g.val r q + b * t + c * t ^ 2 := by
    rw [root_conjugation_entry]
    dsimp only [b, c]
    split_ifs <;> ring
  have hfull : |b * T + c * T ^ 2| ≤ a := by
    have hh := (entry_sub_le_rootShearSize hij g T r q).trans
      (hbound T ⟨hT.le, le_rfl⟩)
    rw [hpoly] at hh
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)
  have hhalf : |(b * T) / 2 + (c * T ^ 2) / 4| ≤ a := by
    have hh := (entry_sub_le_rootShearSize hij g (T / 2) r q).trans
      (hbound (T / 2) ⟨by linarith, by linarith⟩)
    rw [hpoly] at hh
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)
  have hh := quadratic_terminal_window_bound (b * T) (c * T ^ 2) a s hfull hhalf hs
  rw [hpoly, hpoly]
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootPairErgodicity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ergodicity of a root inside its actual two-root group

The chosen root is ergodic on an ergodic component of the group generated
by it and its opposite. This follows from the concrete Mautner argument,
not from an implication from diagonal ergodicity. Only the two-root group
is required to preserve the measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Pointwise

namespace DukePrimeDegree
open PrimeDegreePackets

lemma subgroup_le_invariantRightSubgroup_of_invariant_action {n : ℕ}
    (H : Subgroup (G n)) (μ : Measure (X n)) [SMulInvariantMeasure H (X n) μ] :
    H ≤ invariantRightSubgroup μ := by
  intro g hg
  have hp := (measurePreserving_smul (⟨g, hg⟩ : H)⁻¹ μ).map_eq
  change μ.map (fun x => rightAction x ((g⁻¹)⁻¹)) = μ at hp
  change μ.map (fun x => rightAction x g) = μ
  simpa only [inv_inv] using hp

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockErgodicity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An actual ergodic root flow on a single block component

For a fixed coordinate block, the group generated by its root groups has
the same invariant measurable sets as any one of its nontrivial root
flows.  The Mautner argument proves this for the actual lattice action.
The coordinate block is not required to be the whole ambient space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Pointwise

namespace DukePrimeDegree
open PrimeDegreePackets

lemma root_mem_singleBlockRootGroup {n : ℕ} (S : Set (Fin n))
    (p : Fin n) (hp : p ∈ S) (q : Fin n) (hq : q ∈ S) (hpq : p ≠ q) (t : ℝ) :
    Matrix.SpecialLinearGroup.transvection hpq t ∈ singleBlockRootGroup S :=
  Subgroup.subset_closure ⟨p, q, hpq, t, hp, hq, rfl⟩

lemma singleBlockRootGroup_le_of_roots {n : ℕ} (S : Set (Fin n))
    (H : Subgroup (G n))
    (hroot : ∀ p ∈ S, ∀ q ∈ S, ∀ (hpq : p ≠ q) (t : ℝ),
      Matrix.SpecialLinearGroup.transvection hpq t ∈ H) :
    singleBlockRootGroup S ≤ H := by
  rw [singleBlockRootGroup, Subgroup.closure_le]
  rintro g ⟨p, q, hpq, t, hp, hq, rfl⟩
  exact hroot p hp q hq hpq t

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockNormalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transverse representatives using only a single root block

On an ergodic component for a single root block, an arbitrary ambient
diagonal correction need not preserve the component measure.  Here the
correction is a product of roots in that block.  It clears the entries
inside the block and equalizes its diagonal, leaving the complementary
coordinates unrestricted.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

attribute [local irreducible] singleBlockRootGroup

lemma singleBlockSetoid_off_diagonal {n : ℕ} (S : Set (Fin n))
    {i j : Fin n} (hij : i ≠ j) :
    singleBlockSetoid S i j ↔ i ∈ S ∧ j ∈ S := by
  change (i = j ∨ (i ∈ S ∧ j ∈ S)) ↔ _
  simp only [hij, false_or]

lemma blockRootGroup_singleBlockSetoid {n : ℕ} (S : Set (Fin n)) :
    blockRootGroup (singleBlockSetoid S) = singleBlockRootGroup S := by
  apply le_antisymm
  · rw [blockRootGroup, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, t, hr, rfl⟩
    obtain ⟨hi, hj⟩ := (singleBlockSetoid_off_diagonal S hij).mp hr
    exact root_mem_singleBlockRootGroup S i hi j hj hij t
  · apply singleBlockRootGroup_le_of_roots
    intro i hi j hj hij t
    exact root_mem_blockRootGroup (singleBlockSetoid S) i j hij (Or.inr ⟨hi, hj⟩) t

/-- A diagonal supported on one coordinate block belongs to its actual
root-generated group, provided its determinant is one. -/
theorem supported_diagonal_mem_singleBlockRootGroup {n : ℕ}
    (S : Set (Fin n)) (i₀ : Fin n) (hi₀ : i₀ ∈ S)
    (D : Fin n → ℝ) (hdet : Matrix.det (Matrix.diagonal D) = 1)
    (hsupport : ∀ i, i ∉ S → D i = 1) :
    (⟨Matrix.diagonal D, hdet⟩ : G n) ∈ singleBlockRootGroup S := by
  rw [Matrix.SpecialLinearGroup.diag_eq_diag2n_prod i₀ D hdet]
  apply (singleBlockRootGroup S).noncommProd_mem
  intro i hi
  split_ifs with hii
  · by_cases hiS : i ∈ S
    · exact diag2n_mem_of_opposite_roots hii (singleBlockRootGroup S)
        (root_mem_singleBlockRootGroup S i hiS i₀ hi₀ hii)
        (root_mem_singleBlockRootGroup S i₀ hi₀ i hiS hii.symm)
        (D i) (Matrix.SpecialLinearGroup.diagonal_neZero D hdet i)
    · have he : Matrix.SpecialLinearGroup.diag2n hii (D i)
          (Matrix.SpecialLinearGroup.diagonal_neZero D hdet i) = 1 := by
        apply Subtype.ext
        ext a b
        simp [Matrix.SpecialLinearGroup.diag2n_coe, hsupport i hiS]
      rw [he]
      exact (singleBlockRootGroup S).one_mem
  · exact (singleBlockRootGroup S).one_mem

theorem supported_diagonalOneParameter_mem_singleBlockRootGroup {n : ℕ}
    (S : Set (Fin n)) (i₀ : Fin n) (hi₀ : i₀ ∈ S)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (hsupport : ∀ i, i ∉ S → ell i = 0) (t : ℝ) :
    diagonalOneParameter ell hell t ∈ singleBlockRootGroup S := by
  apply supported_diagonal_mem_singleBlockRootGroup S i₀ hi₀
  intro i hi
  simp only [hsupport i hi, zero_mul, Real.exp_zero]

lemma singleBlockDiagonalCorrection_mem {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (g : G n) :
    singleBlockDiagonalCorrection S hS g ∈ singleBlockRootGroup (↑S) := by
  unfold singleBlockDiagonalCorrection
  obtain ⟨i₀, hi₀⟩ := hS
  apply supported_diagonalOneParameter_mem_singleBlockRootGroup (↑S) i₀ hi₀
  intro i hi
  exact ite_eq_right hi

lemma mul_singleBlockDiagonalCorrection_mem {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) (b u : G n)
    (hb : b ∈ blockRootGroup (singleBlockSetoid (↑S))) :
    b * singleBlockDiagonalCorrection S hS u ∈ singleBlockRootGroup (↑S) := by
  have hbk : b ∈ singleBlockRootGroup (↑S) := by
    rw [← blockRootGroup_singleBlockSetoid]
    exact hb
  exact (singleBlockRootGroup (↑S)).mul_mem
    (x := b) (y := singleBlockDiagonalCorrection S hS u)
    hbk (singleBlockDiagonalCorrection_mem S hS u)

lemma singleBlockDiagonalCorrection_entry {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (g : G n) (i j : Fin n) :
    (g * singleBlockDiagonalCorrection S hS g).val i j =
      g.val i j * Real.exp (singleBlockDiagonalWeights S g j) := by
  unfold singleBlockDiagonalCorrection
  change (g.val * Matrix.diagonal (fun k =>
    Real.exp (singleBlockDiagonalWeights S g k * 1))) i j = _
  simp only [Matrix.mul_diagonal, mul_one]

lemma singleBlockDiagonalCorrection_diagonal {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (g : G n) (hpos : ∀ i ∈ S, 0 < g.val i i)
    (i : Fin n) (hi : i ∈ S) :
    (g * singleBlockDiagonalCorrection S hS g).val i i =
      Real.exp (singleBlockDiagonalMean S g) := by
  rw [singleBlockDiagonalCorrection_entry, singleBlockDiagonalWeights, ite_eq_left hi,
    Real.exp_sub, Real.exp_log (hpos i hi)]
  field_simp [ne_of_gt (hpos i hi)]

lemma singleBlockDiagonalCorrection_tendsto {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) (g : ℕ → G n)
    (hg : Tendsto g atTop (𝓝 1)) :
    Tendsto (fun k => singleBlockDiagonalCorrection S hS (g k)) atTop (𝓝 1) := by
  have hi (i : Fin n) : Tendsto (fun k => Real.log ((g k).val i i)) atTop (𝓝 0) := by
    have hc : Continuous (fun a : G n => a.val i i) := by fun_prop
    have he : Tendsto (fun k => (g k).val i i) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_apply_eq] using hc.continuousAt.tendsto.comp hg
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp he
  have hmean : Tendsto (fun k => singleBlockDiagonalMean S (g k)) atTop (𝓝 0) := by
    simpa only [singleBlockDiagonalMean, Finset.sum_const_zero, zero_div] using
      (tendsto_finsetSum S (fun i _ => hi i)).div_const (S.card : ℝ)
  have hw (i : Fin n) : Tendsto (fun k => singleBlockDiagonalWeights S (g k) i)
      atTop (𝓝 0) := by
    by_cases hiS : i ∈ S
    · simpa only [singleBlockDiagonalWeights, ite_eq_left hiS, sub_zero] using hmean.sub (hi i)
    · simpa only [singleBlockDiagonalWeights, ite_eq_right hiS] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases hij : i = j
  · subst j
    simp only [singleBlockDiagonalCorrection, diagonalOneParameter,
      Matrix.diagonal_apply_eq, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq, mul_one]
    simpa only [Function.comp_def, mul_one, Real.exp_zero] using
      (Real.continuous_exp.tendsto 0).comp (hw i)
  · unfold singleBlockDiagonalCorrection
    change Tendsto (fun k => (Matrix.diagonal (fun a =>
        Real.exp (singleBlockDiagonalWeights S (g k) a * 1))) i j)
      atTop (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j))
    simpa only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Both corrections remain in the single-block group. This is the
normalization available on its actual ergodic components. -/
theorem exists_singleBlock_transverse_sequence {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1)) :
    ∃ s b : ℕ → G n, ∃ c : ℕ → ℝ,
      Tendsto s atTop (𝓝 1) ∧ Tendsto b atTop (𝓝 1) ∧
      (∀ k, s k = g k * b k) ∧ (∀ k, b k ∈ singleBlockRootGroup (↑S)) ∧
      (∀ k, 0 < c k) ∧
      ∀ᶠ k in atTop, (∀ i ∈ S, (s k).val i i = c k) ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (s k).val i j = 0 := by
  obtain ⟨u, b, hu, hb, he, hmem, hz⟩ :=
    exists_block_transverse_sequence (singleBlockSetoid (↑S)) g hg
  let a : ℕ → G n := fun k => singleBlockDiagonalCorrection S hS (u k)
  let s : ℕ → G n := fun k => u k * a k
  let b' : ℕ → G n := fun k => b k * a k
  let c : ℕ → ℝ := fun k => Real.exp (singleBlockDiagonalMean S (u k))
  have ha : Tendsto a atTop (𝓝 1) := singleBlockDiagonalCorrection_tendsto S hS u hu
  have hpos : ∀ᶠ k in atTop, ∀ i, 0 < (u k).val i i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun a : G n => a.val i i) := by fun_prop
    have hlim : Tendsto (fun k => (u k).val i i) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_apply_eq] using hc.continuousAt.tendsto.comp hu
    exact hlim.eventually (lt_mem_nhds zero_lt_one)
  refine ⟨s, b', c, ?_, ?_, ?_, ?_, fun k => Real.exp_pos _, ?_⟩
  · simpa only [s, mul_one] using hu.mul ha
  · simpa only [b', mul_one] using hb.mul ha
  · intro k
    dsimp only [s, b']
    rw [he k, mul_assoc]
  · intro k
    change b k * singleBlockDiagonalCorrection S hS (u k) ∈ singleBlockRootGroup (↑S)
    exact mul_singleBlockDiagonalCorrection_mem S hS (b k) (u k) (hmem k)
  · filter_upwards [hpos, hz] with k hk hkz
    constructor
    · intro i hi
      exact singleBlockDiagonalCorrection_diagonal S hS (u k) (fun j _ => hk j) i hi
    · intro i hi j hj hij
      change (u k * singleBlockDiagonalCorrection S hS (u k)).val i j = 0
      rw [singleBlockDiagonalCorrection_entry, hkz i j hij (Or.inr ⟨hi, hj⟩), zero_mul]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockTransverse
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A single-block correction retains a transverse limiting shear

Only the selected block is normalized to a scalar. Its complement may
have arbitrary entries. Conjugation by the selected root group fixes
the entire block-diagonal part, so every nonidentity limiting shear is
outside the two-block preserving group.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma singleBlockRootGroup_le_blockComplement {n : ℕ} (S : Set (Fin n)) :
    singleBlockRootGroup S ≤ blockMatrixGroup (blockComplementSetoid S) := by
  apply singleBlockRootGroup_le_of_roots
  intro i hi j hj hij t
  exact blockRootGroup_le_blockMatrixGroup (blockComplementSetoid S)
    (root_mem_blockRootGroup (blockComplementSetoid S) i j hij
      ⟨fun _ => hj, fun _ => hi⟩ t)

lemma matrix_commute_transvection_of_row_column {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (t : ℝ)
    (hcol : ∀ a, a ≠ i → M a i = 0)
    (hrow : ∀ b, b ≠ j → M j b = 0)
    (hdiag : M i i = M j j) :
    Commute M (Matrix.transvection i j t) := by
  change M * Matrix.transvection i j t = Matrix.transvection i j t * M
  ext a b
  by_cases ha : a = i <;> by_cases hb : b = j
  · subst a
    subst b
    simp only [Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same,
      hdiag]
  · subst a
    rw [Matrix.mul_transvection_apply_of_ne i j i b hb t M,
      Matrix.transvection_mul_apply_same, hrow b hb, mul_zero, add_zero]
  · subst b
    rw [Matrix.mul_transvection_apply_same,
      Matrix.transvection_mul_apply_of_ne i j a j ha t M,
      hcol a ha, mul_zero, add_zero]
  · rw [Matrix.mul_transvection_apply_of_ne i j a b hb t M,
      Matrix.transvection_mul_apply_of_ne i j a b ha t M]

lemma withinBlockPart_singleBlock_commutes {n : ℕ}
    (S : Set (Fin n)) (g : G n) (c : ℝ)
    (hdiag : ∀ i ∈ S, g.val i i = c)
    (hzero : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → g.val i j = 0)
    (u : G n) (hu : u ∈ singleBlockRootGroup S) :
    slMatrixConjugation u (withinBlockPart (blockComplementSetoid S) g.val) =
      withinBlockPart (blockComplementSetoid S) g.val := by
  let M := withinBlockPart (blockComplementSetoid S) g.val
  have hroot (i : Fin n) (hi : i ∈ S) (j : Fin n) (hj : j ∈ S)
      (hij : i ≠ j) (t : ℝ) :
      slMatrixConjugation (Matrix.SpecialLinearGroup.transvection hij t) M = M := by
    apply slMatrixConjugation_eq_self
    apply matrix_commute_transvection_of_row_column
    · intro a hai
      by_cases haS : a ∈ S
      · simp only [M, withinBlockPart, blockComplementSetoid,
          show (a ∈ S ↔ i ∈ S) from ⟨fun _ => hi, fun _ => haS⟩,
          ite_true, if_true, hzero a haS i hi hai]
      · simp only [M, withinBlockPart, blockComplementSetoid,
          show ¬ (a ∈ S ↔ i ∈ S) from fun h => haS (h.mpr hi), ite_false, if_false]
    · intro b hbj
      by_cases hbS : b ∈ S
      · simp only [M, withinBlockPart, blockComplementSetoid,
          show (j ∈ S ↔ b ∈ S) from ⟨fun _ => hbS, fun _ => hj⟩,
          ite_true, if_true, hzero j hj b hbS hbj.symm]
      · simp only [M, withinBlockPart, blockComplementSetoid,
          show ¬ (j ∈ S ↔ b ∈ S) from fun h => hbS (h.mp hj), ite_false, if_false]
    · simp only [M, withinBlockPart, Setoid.refl, ite_true, if_true, hdiag i hi, hdiag j hj]
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
      obtain ⟨i, j, hij, t, hi, hj, rfl⟩ := hu
      exact hroot i hi j hj hij t
  | one => exact slMatrixConjugation_one M
  | mul u v _ _ hu hv => rw [slMatrixConjugation_mul, hu, hv]
  | inv u _ hu =>
      have he := congrArg (slMatrixConjugation u⁻¹) hu
      have hinv := slMatrixConjugation_inverse u⁻¹ M
      rw [inv_inv] at hinv
      exact he.symm.trans hinv

theorem withinBlockPart_singleBlock_conjugation {n : ℕ}
    (S : Set (Fin n)) (g : G n) (c : ℝ)
    (hdiag : ∀ i ∈ S, g.val i i = c)
    (hzero : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → g.val i j = 0)
    (u : G n) (hu : u ∈ singleBlockRootGroup S) :
    withinBlockPart (blockComplementSetoid S) (u * g * u⁻¹).val =
      withinBlockPart (blockComplementSetoid S) g.val := by
  let r := blockComplementSetoid S
  have hb : u ∈ blockMatrixGroup r := singleBlockRootGroup_le_blockComplement S hu
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
    withinBlockPart_mul_left r u.val _ (cross_zero_of_mem_blockMatrixGroup r u hb),
    withinBlockPart_mul_right r g.val u⁻¹.val
      (cross_zero_of_mem_blockMatrixGroup r u⁻¹ ((blockMatrixGroup r).inv_mem hb))]
  simpa only [slMatrixConjugation, inv_inv, Matrix.mul_assoc] using
    withinBlockPart_singleBlock_commutes S g c hdiag hzero u⁻¹
      ((singleBlockRootGroup S).inv_mem hu)

theorem singleBlock_conjugation_limit_outside_blocks {n : ℕ}
    (S : Set (Fin n)) (g u : ℕ → G n) (c : ℕ → ℝ)
    (hg : Tendsto g atTop (𝓝 1))
    (hu : ∀ k, u k ∈ singleBlockRootGroup S)
    (hpart : ∀ᶠ k in atTop,
      (∀ i ∈ S, (g k).val i i = c k) ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (g k).val i j = 0)
    (h : G n) (hne : h ≠ 1)
    (hlim : Tendsto (fun k => u k * g k * (u k)⁻¹) atTop (𝓝 h)) :
    h ∉ blockMatrixGroup (blockComplementSetoid S) := by
  intro hh
  apply hne
  apply Subtype.ext
  ext i j
  by_cases hij : blockComplementSetoid S i j
  · have he : ∀ᶠ k in atTop,
        (u k * g k * (u k)⁻¹).val i j = (g k).val i j := by
      filter_upwards [hpart] with k hk
      have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
        (withinBlockPart_singleBlock_conjugation S (g k) (c k) hk.1 hk.2 (u k) (hu k))
      simpa only [withinBlockPart, hij, ite_true, if_true] using he
    have hc : Continuous (fun a : G n => a.val i j) := by fun_prop
    have hx := hc.continuousAt.tendsto.comp hg
    have hy := hc.continuousAt.tendsto.comp hlim
    exact tendsto_nhds_unique hy (hx.congr' (he.mono fun _ h => h.symm))
  · rw [cross_zero_of_mem_blockMatrixGroup (blockComplementSetoid S) h hh i j hij]
    have hneij : i ≠ j := by
      intro he
      subst j
      exact hij Iff.rfl
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hneij]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockNoncentral
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A fixed root detects a transverse sequence

Every matrix outside the two-block preserving group fails to commute
with a root in the selected nontrivial block. There are only finitely
many such roots, so one root detects an entire subsequence. This chooses
the shearing direction from the actual return matrices.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_noncentral_singleBlock_root {n : ℕ}
    (S : Set (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (g : G n) (hg : g ∉ blockMatrixGroup (blockComplementSetoid S)) :
    ∃ (i j : Fin n) (hij : i ≠ j), i ∈ S ∧ j ∈ S ∧
      ¬∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
        Matrix.SpecialLinearGroup.transvection hij t * g := by
  by_contra hn
  have hcomm (i : Fin n) (hi : i ∈ S) (j : Fin n) (hj : j ∈ S) (hij : i ≠ j) :
      g * Matrix.SpecialLinearGroup.transvection hij 1 =
        Matrix.SpecialLinearGroup.transvection hij 1 * g := by
    by_contra hh
    exact hn ⟨i, j, hij, hi, hj, fun hall => hh (hall 1)⟩
  have hpartner (i : Fin n) (hi : i ∈ S) : ∃ j, j ∈ S ∧ i ≠ j := by
    by_cases hik : i = k
    · subst i
      exact ⟨l, hl, hkl⟩
    · exact ⟨k, hk, hik⟩
  apply hg
  apply mem_blockMatrixGroup_of_cross_zero
  intro i j hij
  change ¬(i ∈ S ↔ j ∈ S) at hij
  by_cases hi : i ∈ S
  · have hj : j ∉ S := fun hj => hij ⟨fun _ => hj, fun _ => hi⟩
    obtain ⟨p, hp, hip⟩ := hpartner i hi
    have he := ((commutes_root_one_iff hip.symm g).mp (hcomm p hp i hi hip.symm)).2.1
    exact he j (fun hji => hj (hji.symm ▸ hi))
  · have hj : j ∈ S := by
      by_contra hj
      exact hij ⟨fun h => (hi h).elim, fun h => (hj h).elim⟩
    obtain ⟨p, hp, hjp⟩ := hpartner j hj
    have he := ((commutes_root_one_iff hjp g).mp (hcomm j hj p hp hjp)).1
    exact he i (fun hij => hi (hij.symm ▸ hj))

lemma exists_constant_subsequence_of_finite {A : Type*} [Finite A] (f : ℕ → A) :
    ∃ a : A, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m, f (φ m) = a := by
  have hf : ∃ a : A, ∃ᶠ m in atTop, f m = a := by
    by_contra hn
    have hnone (a : A) : ∀ᶠ m in atTop, f m ≠ a :=
      not_frequently.mp (fun ha => hn ⟨a, ha⟩)
    obtain ⟨m, hm⟩ := (Filter.eventually_all.mpr hnone).exists
    exact hm (f m) rfl
  obtain ⟨a, ha⟩ := hf
  obtain ⟨φ, hφ, hfφ⟩ := extraction_of_frequently_atTop ha
  exact ⟨a, φ, hφ, hfφ⟩

theorem exists_fixed_noncentral_root_subsequence {n : ℕ}
    (S : Set (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (g : ℕ → G n)
    (hg : ∀ m, g m ∉ blockMatrixGroup (blockComplementSetoid S)) :
    ∃ (i j : Fin n) (hij : i ≠ j), i ∈ S ∧ j ∈ S ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m,
        ¬∀ t : ℝ, g (φ m) * Matrix.SpecialLinearGroup.transvection hij t =
          Matrix.SpecialLinearGroup.transvection hij t * g (φ m) := by
  let A := {p : Fin n × Fin n // p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2}
  have hex (m : ℕ) : ∃ p : A,
      ¬∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection p.property.2.2 t =
        Matrix.SpecialLinearGroup.transvection p.property.2.2 t * g m := by
    obtain ⟨i, j, hij, hi, hj, hnot⟩ :=
      exists_noncentral_singleBlock_root S k l hkl hk hl (g m) (hg m)
    exact ⟨⟨(i, j), hi, hj, hij⟩, hnot⟩
  choose p hp using hex
  obtain ⟨a, φ, hφ, ha⟩ := exists_constant_subsequence_of_finite p
  refine ⟨a.val.1, a.val.2, a.property.2.2, a.property.1, a.property.2.1, φ, hφ, ?_⟩
  intro m
  simpa only [ha m] using hp (φ m)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockShearingLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A transverse limit from actual normalized return matrices

The shearing root, diverging first stopping times and transverse limit
are all constructed. In particular, being outside the block group is
a conclusion about the limit, not an additional hypothesis imposed on
a subsequence.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixDifference_of_rootShearLimit {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (T : ℕ → ℝ) (a : ℝ)
    (hsize : ∀ m, rootShearSize hij (g m) (T m) = a)
    (h : G n)
    (hlim : Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (T m) * g m *
      Matrix.SpecialLinearGroup.transvection hij (-(T m))) atTop (𝓝 h)) :
    slMatrixDifference h 1 = a := by
  have he := continuous_slMatrixDifference.continuousAt.tendsto.comp (hlim.prodMk_nhds hg)
  have hc : Tendsto (fun m => slMatrixDifference
      (Matrix.SpecialLinearGroup.transvection hij (T m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-(T m))) (g m)) atTop (𝓝 a) := by
    simpa only [show ∀ m, slMatrixDifference
      (Matrix.SpecialLinearGroup.transvection hij (T m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-(T m))) (g m) = a from hsize] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
  exact tendsto_nhds_unique he hc

theorem exists_singleBlock_transverse_shearing_limit {n : ℕ}
    (S : Set (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hout : ∀ m, g m ∉ blockMatrixGroup (blockComplementSetoid S))
    (c : ℕ → ℝ)
    (hpart : ∀ᶠ m in atTop,
      (∀ i ∈ S, (g m).val i i = c m) ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (g m).val i j = 0)
    (a : ℝ) (ha : 0 < a) :
    ∃ (i j : Fin n) (hij : i ≠ j), i ∈ S ∧ j ∈ S ∧
      ∃ (φ : ℕ → ℕ) (T : ℕ → ℝ) (h : G n),
        StrictMono φ ∧ Tendsto T atTop atTop ∧ h ≠ 1 ∧
        h ∉ blockMatrixGroup (blockComplementSetoid S) ∧
        slMatrixDifference h 1 = a ∧
        Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (T m) * g (φ m) *
          Matrix.SpecialLinearGroup.transvection hij (-(T m))) atTop (𝓝 h) ∧
        (∀ m, 0 < T m ∧ rootShearSize hij (g (φ m)) (T m) = a ∧
          ∀ t ∈ Icc 0 (T m), rootShearSize hij (g (φ m)) t ≤ a) ∧
        ∀ t : ℝ, h * Matrix.SpecialLinearGroup.transvection hij t =
          Matrix.SpecialLinearGroup.transvection hij t * h := by
  obtain ⟨i, j, hij, hi, hj, σ, hσ, hnoncentral⟩ :=
    exists_fixed_noncentral_root_subsequence S k l hkl hk hl g hout
  have hgσ : Tendsto (g ∘ σ) atTop (𝓝 1) := hg.comp hσ.tendsto_atTop
  obtain ⟨T, hTtop, hT⟩ := exists_diverging_first_rootShearScale hij (g ∘ σ)
    hgσ hnoncentral ha
  obtain ⟨h, hne, ψ, hψ, hlim, hcentral⟩ := exists_nontrivial_rootShearLimit hij
    (g ∘ σ) hgσ T (fun m => (hT m).1) hTtop ha (fun m => (hT m).2.1)
    (fun m => (hT m).2.2)
  have hdiff : slMatrixDifference h 1 = a := slMatrixDifference_of_rootShearLimit hij
    (g ∘ (σ ∘ ψ)) (hg.comp (hσ.comp hψ).tendsto_atTop) (T ∘ ψ) a
    (fun m => (hT (ψ m)).2.1) h hlim
  refine ⟨i, j, hij, hi, hj, σ ∘ ψ, T ∘ ψ, h, hσ.comp hψ,
    hTtop.comp hψ.tendsto_atTop, hne, ?_, hdiff, hlim, ?_, hcentral⟩
  · apply singleBlock_conjugation_limit_outside_blocks S
      (g ∘ (σ ∘ ψ)) (fun m => Matrix.SpecialLinearGroup.transvection hij (T (ψ m)))
      (c ∘ (σ ∘ ψ)) (hg.comp (hσ.comp hψ).tendsto_atTop)
      (fun m => root_mem_singleBlockRootGroup S i hi j hj hij (T (ψ m)))
      ((hσ.comp hψ).tendsto_atTop.eventually hpart) h hne
    simpa only [Function.comp_apply, Matrix.SpecialLinearGroup.transvection_inv] using hlim
  · intro m
    exact hT (ψ m)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockShell
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A fixed compact set of transverse shearing limits

Normalizing the selected block makes the within-block part of every
limiting conjugate equal to the identity. A fixed positive displacement
therefore gives a compact set disjoint from the block group. Local
containment of the actual stabilizer in that group supplies a sufficiently
small displacement, before the generic points or the limiting shear are
chosen.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma entry_sub_le_slMatrixDifference {n : ℕ} (g h : G n) (i j : Fin n) :
    |g.val i j - h.val i j| ≤ slMatrixDifference g h := by
  apply (Finset.single_le_sum (f := fun k : Fin n => |g.val i k - h.val i k|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
  exact Finset.single_le_sum
    (f := fun k : Fin n => ∑ l : Fin n, |g.val k l - h.val k l|)
    (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)

lemma continuous_withinBlockPart {n : ℕ} (r : Setoid (Fin n)) :
    Continuous (withinBlockPart r) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : r i j
  · simpa only [withinBlockPart, hij, ite_true, if_true, Function.comp_def] using
      ((continuous_apply j).comp (continuous_apply i))
  · simpa only [withinBlockPart, hij, ite_false, if_false] using
      (continuous_const : Continuous (fun _ : Matrix (Fin n) (Fin n) ℝ => (0 : ℝ)))

lemma transverseMatrixShell_isClosed {n : ℕ} (r : Setoid (Fin n)) (a : ℝ) :
    IsClosed (transverseMatrixShell r a) := by
  exact (isClosed_eq ((continuous_withinBlockPart r).comp continuous_subtype_val)
    continuous_const).inter
      (isClosed_eq (continuous_slMatrixDifference.comp
        (continuous_id.prodMk continuous_const)) continuous_const)

lemma transverseMatrixShell_isCompact {n : ℕ} (r : Setoid (Fin n)) (a : ℝ) :
    IsCompact (transverseMatrixShell r a) := by
  let K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {M | ∀ i j, M i j ∈ Icc (-(|a| + 1)) (|a| + 1)}
  have hK : IsCompact K :=
    isCompact_pi_infinite fun _ : Fin n =>
      isCompact_pi_infinite fun _ : Fin n => isCompact_Icc
  apply (Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hK).of_isClosed_subset
    (transverseMatrixShell_isClosed r a)
  intro g hg i j
  have hb : |g.val i j - (1 : G n).val i j| ≤ |a| :=
    ((entry_sub_le_slMatrixDifference g 1 i j).trans_eq hg.2).trans (le_abs_self a)
  have hone : |(1 : G n).val i j| ≤ (1 : ℝ) := by
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
    split_ifs <;> norm_num
  apply abs_le.mp
  calc
    |g.val i j| = |(g.val i j - (1 : G n).val i j) + (1 : G n).val i j| := by
      rw [sub_add_cancel]
    _ ≤ |g.val i j - (1 : G n).val i j| + |(1 : G n).val i j| := abs_add_le _ _
    _ ≤ |a| + 1 := add_le_add hb hone

lemma transverseMatrixShell_not_mem_block {n : ℕ} (r : Setoid (Fin n))
    {a : ℝ} (ha : 0 < a) {g : G n} (hg : g ∈ transverseMatrixShell r a) :
    g ∉ blockMatrixGroup r := by
  intro hblock
  have heq : g = 1 := by
    apply Subtype.ext
    ext i j
    by_cases hij : r i j
    · have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hg.1
      simpa only [withinBlockPart, hij, ite_true, if_true, Matrix.SpecialLinearGroup.coe_one] using he
    · rw [cross_zero_of_mem_blockMatrixGroup r g hblock i j hij]
      have hne : i ≠ j := fun h => hij (h ▸ r.refl i)
      simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hne]
  have hz := hg.2
  rw [heq, slMatrixDifference_self] at hz
  exact ha.ne' hz.symm

section LocalShell

attribute [local irreducible] blockMatrixGroup

/-- Local block preservation gives a displacement scale whose entire
transverse shell is disjoint from the actual subgroup. -/
theorem exists_small_transverse_shell {n : ℕ}
    (L : Subgroup (G n)) (r : Setoid (Fin n))
    (hlocal : {g : L | g.val ∈ blockMatrixGroup r} ∈ 𝓝 (1 : L)) :
    ∃ a : ℝ, 0 < a ∧ ∀ g ∈ transverseMatrixShell r a, g ∉ L := by
  obtain ⟨V, hV, hVL⟩ :=
    (mem_nhds_subtype (L : Set (G n)) (1 : L)
      {g : L | g.val ∈ blockMatrixGroup r}).mp hlocal
  obtain ⟨δ, hδ, hδV⟩ := matrixBall_nhds_basis hV
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro g hg hgL
  have hgδ : g ∈ matrixBall n δ := by
    intro i j
    have he := (entry_sub_le_slMatrixDifference g 1 i j).trans_eq hg.2
    exact he.trans_lt (by linarith)
  exact transverseMatrixShell_not_mem_block r (half_pos hδ) hg
    (hVL (show (⟨g, hgL⟩ : L) ∈ (Subtype.val : L → G n) ⁻¹' V from hδV hgδ))

end LocalShell

theorem singleBlock_conjugation_limit_withinPart {n : ℕ}
    (S : Set (Fin n)) (g u : ℕ → G n) (c : ℕ → ℝ)
    (hg : Tendsto g atTop (𝓝 1))
    (hu : ∀ k, u k ∈ singleBlockRootGroup S)
    (hpart : ∀ᶠ k in atTop,
      (∀ i ∈ S, (g k).val i i = c k) ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (g k).val i j = 0)
    (h : G n)
    (hlim : Tendsto (fun k => u k * g k * (u k)⁻¹) atTop (𝓝 h)) :
    withinBlockPart (blockComplementSetoid S) h.val = 1 := by
  ext i j
  by_cases hij : blockComplementSetoid S i j
  · have he : ∀ᶠ k in atTop,
        (u k * g k * (u k)⁻¹).val i j = (g k).val i j := by
      filter_upwards [hpart] with k hk
      have ht := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
        (withinBlockPart_singleBlock_conjugation S (g k) (c k) hk.1 hk.2 (u k) (hu k))
      simpa only [withinBlockPart, hij, ite_true, if_true] using ht
    have hc : Continuous (fun a : G n => a.val i j) := by fun_prop
    have hentry := tendsto_nhds_unique (hc.continuousAt.tendsto.comp hlim)
      ((hc.continuousAt.tendsto.comp hg).congr' (he.mono fun _ h => h.symm))
    simpa only [withinBlockPart, hij, ite_true, if_true, Matrix.SpecialLinearGroup.coe_one] using hentry
  · have hne : i ≠ j := fun he => hij (he ▸ Iff.rfl)
    simp only [withinBlockPart, hij, ite_false, if_false, Matrix.one_apply_ne hne]

/-- The finitely many tests are fixed using the local stabilizer before
the normalized pairs and their subsequences are selected. -/
theorem exists_finite_small_transverse_separators {n : ℕ}
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (r : Setoid (Fin n))
    (hlocal : {g : invariantRightSubgroup μ | g.val ∈ blockMatrixGroup r} ∈
      𝓝 (1 : invariantRightSubgroup μ)) :
    ∃ a : ℝ, 0 < a ∧
      ∃ (F : Finset (CompactlySupportedContinuousMap (X n) ℝ)) (ε : ℝ),
        0 < ε ∧ ∀ g ∈ transverseMatrixShell r a,
          ∃ f ∈ F, ε < |invarianceDefect μ f g| := by
  obtain ⟨a, ha, hout⟩ := exists_small_transverse_shell (invariantRightSubgroup μ) r hlocal
  obtain ⟨F, ε, hε, hF⟩ := exists_finite_compact_stabilizer_separators μ
    (transverseMatrixShell r a) (transverseMatrixShell_isCompact r a) hout
  exact ⟨a, ha, F, ε, hε, hF⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RightObservableUniformity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform observables near a compact family of right translations

The tolerance is selected before the eventual shearing limit. Matrix
entry control then bounds a compact observable at every base point,
including points outside compact subsets of the lattice space.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction Matrix.Norms.Elementwise

namespace DukePrimeDegree
open PrimeDegreePackets

section OppositeAction

attribute [local instance] OAI.DukePrimeDegree.rightLatticeOppositeAction
local instance rightLatticeOppositeAction_continuous (n : ℕ) :
    ContinuousSMul (G n)ᵐᵒᵖ (X n) where
  continuous_smul := (continuous_rightAction_uncurry n).comp
    (continuous_snd.prodMk (MulOpposite.continuous_unop.comp continuous_fst))

lemma continuous_rightCompactObservable {n : ℕ}
    (f : CompactlySupportedContinuousMap (X n) ℝ) :
    Continuous (rightCompactObservable f) := by
  exact (continuous_compactObservableTranslate (H := (G n)ᵐᵒᵖ) f).comp MulOpposite.continuous_op

end OppositeAction

/-- A single matrix tolerance works around the whole compact set and
for every lattice base point. -/
theorem exists_uniform_right_observable_tolerance {n : ℕ}
    (f : CompactlySupportedContinuousMap (X n) ℝ)
    (K : Set (G n)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g h : G n, h ∈ K → slMatrixDifference g h < δ →
      ∀ x : X n, |f (rightAction x g) - f (rightAction x h)| < ε := by
  let : MetricSpace (G n) := MetricSpace.induced
    (fun g : G n => g.val) Subtype.val_injective inferInstance
  have hu := hK.uniformContinuousAt_of_continuousAt (rightCompactObservable f)
    (fun _ _ => (continuous_rightCompactObservable f).continuousAt)
    (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hclose⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨δ, hδ, ?_⟩
  intro g h hh hgh x
  have hdist : dist h g < δ := by
    change dist h.val g.val < δ
    rw [dist_eq_norm]
    apply (Matrix.norm_lt_iff hδ).mpr
    intro i j
    change |h.val i j - g.val i j| < δ
    rw [abs_sub_comm]
    exact (entry_sub_le_slMatrixDifference g h i j).trans_lt hgh
  have ht : dist (rightCompactObservable f h) (rightCompactObservable f g) < ε :=
    hclose hdist hh
  have hp := (BoundedContinuousFunction.dist_coe_le_dist
    (f := rightCompactObservable f h) (g := rightCompactObservable f g) x).trans_lt ht
  simpa only [rightCompactObservable, BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk, CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
    Real.dist_eq, abs_sub_comm] using hp

/-- Finitely many separating tests share one tolerance, with no choice
of a limiting shear involved. -/
theorem exists_finite_uniform_right_observable_tolerance {n : ℕ}
    (F : Finset (CompactlySupportedContinuousMap (X n) ℝ))
    (K : Set (G n)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ F, ∀ g h : G n, h ∈ K →
      slMatrixDifference g h < δ →
        ∀ x : X n, |f (rightAction x g) - f (rightAction x h)| < ε := by
  classical
  choose δ hδ hsmall using fun f : F =>
    exists_uniform_right_observable_tolerance f.val K hK ε hε
  by_cases hF : F.Nonempty
  · obtain ⟨f, hf, hmin⟩ := Finset.exists_min_image F
      (fun f => if h : f ∈ F then δ ⟨f, h⟩ else 1) hF
    refine ⟨δ ⟨f, hf⟩, hδ ⟨f, hf⟩, ?_⟩
    intro q hq g h hh hgh x
    apply hsmall ⟨q, hq⟩ g h hh _ x
    apply hgh.trans_le
    simpa only [dite_eq_left hf, dite_eq_left hq] using hmin q hq
  · refine ⟨1, zero_lt_one, ?_⟩
    intro f hf
    exact (hF ⟨f, hf⟩).elim

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FixedTerminalShearing
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A fixed terminal fraction for every eventual shearing limit

The fraction is chosen using only the fixed displacement scale, the
compact set of possible limits and the finite test family. It does not
shrink along the sequence. Hence a previously chosen generic set gives
valid control at the pair-dependent stopping times.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixDifference_triangle {n : ℕ} (g h k : G n) :
    slMatrixDifference g k ≤ slMatrixDifference g h + slMatrixDifference h k := by
  simp only [slMatrixDifference, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact abs_sub_le (g.val i j) (h.val i j) (k.val i j)

lemma slMatrixDifference_le_of_entries {n : ℕ} (g h : G n) (C : ℝ)
    (hC : ∀ i j, |g.val i j - h.val i j| ≤ C) :
    slMatrixDifference g h ≤ (n : ℝ) * n * C := by
  calc
    slMatrixDifference g h ≤ ∑ _i : Fin n, ∑ _j : Fin n, C := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun j _ => hC i j)
    _ = (n : ℝ) * n * C := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The same fixed fraction works for all roots and every sequence with
the specified bounded stopping intervals. -/
theorem exists_fixed_terminal_observable_fraction {n : ℕ}
    (F : Finset (CompactlySupportedContinuousMap (X n) ℝ))
    (K : Set (G n)) (hK : IsCompact K)
    (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (i j : Fin n) (hij : i ≠ j)
        (g : ℕ → G n) (T : ℕ → ℝ),
        (∀ k, 0 < T k) →
        (∀ k, ∀ t ∈ Icc 0 (T k), rootShearSize hij (g k) t ≤ a) →
        ∀ h ∈ K,
          Tendsto (fun k => Matrix.SpecialLinearGroup.transvection hij (T k) * g k *
            Matrix.SpecialLinearGroup.transvection hij (-(T k))) atTop (𝓝 h) →
          ∀ᶠ k in atTop, ∀ s ∈ Icc (1 - δ) 1, ∀ f ∈ F, ∀ x : X n,
            |f (rightAction x (Matrix.SpecialLinearGroup.transvection hij (s * T k) *
                g k * Matrix.SpecialLinearGroup.transvection hij (-(s * T k)))) -
              f (rightAction x h)| < ε := by
  obtain ⟨η, hη, hηtest⟩ :=
    exists_finite_uniform_right_observable_tolerance F K hK ε hε
  let C : ℝ := (n : ℝ) * n * (17 * a)
  have hC : 0 ≤ C := by dsimp only [C] <;> positivity
  let δ := min (1 / 2 : ℝ) (η / (4 * (C + 1)))
  have hden : 0 < 4 * (C + 1) := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hη hden)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hCδ : C * δ < η / 2 := by
    have hb : δ * (4 * (C + 1)) ≤ η :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro i j hij g T hT hbound h hh hlim
  let A (k : ℕ) := Matrix.SpecialLinearGroup.transvection hij (T k) * g k *
    Matrix.SpecialLinearGroup.transvection hij (-(T k))
  have hdist : Tendsto (fun k => slMatrixDifference (A k) h) atTop (𝓝 0) := by
    simpa only [A, Function.comp_def, slMatrixDifference_self] using
      continuous_slMatrixDifference.continuousAt.tendsto.comp
        (hlim.prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℕ => h) atTop (𝓝 h)))
  filter_upwards [hdist.eventually (gt_mem_nhds (half_pos hη))] with k hk
  intro s hs f hf x
  let B := Matrix.SpecialLinearGroup.transvection hij (s * T k) * g k *
    Matrix.SpecialLinearGroup.transvection hij (-(s * T k))
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
  have hBA : slMatrixDifference B (A k) ≤ C * δ := by
    have hentry := slMatrixDifference_le_of_entries B (A k) (17 * a * (1 - s))
      (root_conjugation_terminal_window hij (g k) (hT k) (hbound k) s hs01)
    have heq : (n : ℝ) * n * (17 * a * (1 - s)) = C * (1 - s) := by
      dsimp only [C]
      ring
    rw [heq] at hentry
    exact hentry.trans (mul_le_mul_of_nonneg_left (by linarith [hs.1]) hC)
  apply hηtest f hf B h hh _ x
  exact (slMatrixDifference_triangle B (A k) h).trans_lt (by linarith)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_LocalOrbitIsolation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local orbit isolation gives a positive-mass orbit

The topological conclusion needed from the shearing argument is local
isolation of the invariant-group orbits inside one positive-mass good
set. Second countability then produces a countable orbit cover, so one
actual orbit has positive mass. No finite-orbit existence is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

/-- A positive-mass set locally covered by single members of a family
has positive mass in one family member. The family members need not be
open, measurable, or countable. -/
theorem exists_positive_member_of_local_cover
    {Y I : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    (μ : Measure Y) (E : Set Y) (hE : μ E ≠ 0) (O : I → Set Y)
    (hlocal : ∀ x ∈ E, ∃ (i : I) (U : Set Y),
      IsOpen U ∧ x ∈ U ∧ E ∩ U ⊆ O i) :
    ∃ i : I, μ (O i) ≠ 0 := by
  classical
  choose i U hUopen hUx hUsub using fun x : E => hlocal x.val x.property
  have hcover : E ⊆ ⋃ x : E, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hUx ⟨x, hx⟩⟩
  obtain ⟨J, hJcount, hJcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof E).elim_countable_subcover U hUopen hcover
  by_contra hnone
  push Not at hnone
  have hzero : μ (⋃ x ∈ J, E ∩ U x) = 0 :=
    (measure_biUnion_null_iff hJcount).mpr fun x _ =>
      measure_mono_null (hUsub x) (hnone (i x))
  apply hE
  apply measure_mono_null _ hzero
  intro x hx
  obtain ⟨y, hyJ, hyU⟩ := mem_iUnion₂.mp (hJcover hx)
  exact mem_iUnion₂.mpr ⟨y, hyJ, hx, hyU⟩

/-- If every orbit is null, every positive-mass good set contains a
point approached by good points from outside its orbit. -/
theorem exists_good_point_in_closure_outside_orbit
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    (μ : Measure Y) (E : Set Y) (hE : μ E ≠ 0) (O : Y → Set Y)
    (hnull : ∀ x, μ (O x) = 0) :
    ∃ x ∈ E, x ∈ closure (E \ O x) := by
  classical
  by_contra hnone
  push Not at hnone
  have hlocal : ∀ x ∈ E, ∃ (i : Y) (U : Set Y),
      IsOpen U ∧ x ∈ U ∧ E ∩ U ⊆ O i := by
    intro x hx
    refine ⟨x, (closure (E \ O x))ᶜ, isClosed_closure.isOpen_compl, hnone x hx, ?_⟩
    rintro y ⟨hyE, hyU⟩
    by_contra hyO
    exact hyU (subset_closure ⟨hyE, hyO⟩)
  obtain ⟨x, hx⟩ := exists_positive_member_of_local_cover μ E hE O hlocal
  exact hx (hnull x)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_GenericMatrixPairs
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small matrix lifts of generic pairs outside a subgroup orbit

If all subgroup orbits are null, a positive-mass generic set contains
arbitrarily close pairs from different orbits. Openness of the actual
quotient orbit map lifts these pairs to matrices tending to identity,
all outside the subgroup. This is a concrete input to polynomial
shearing, without a homogeneous-orbit assumption.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rightSubgroupOrbit_mk {n : ℕ} (L : Subgroup (G n)) (g : G n) :
    rightSubgroupOrbit L (Quotient.mk _ g) = range (latticeOrbitPoint g L) := by
  ext y
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨Quotient.mk _ h, rfl⟩
  · rintro ⟨a, ha⟩
    induction a using Quotient.inductionOn with
    | h h => exact ⟨h, ha⟩

/-- An actual sequence of small matrices transports one good point to
other good points and never belongs to the given subgroup. -/
theorem exists_small_matrix_generic_pairs {n : ℕ}
    (L : Subgroup (G n)) (μ : Measure (X n)) (E : Set (X n)) (hE : μ E ≠ 0)
    (hnull : ∀ g : G n, μ (range (latticeOrbitPoint g L)) = 0) :
    ∃ x ∈ E, ∃ a : ℕ → G n,
      Tendsto a atTop (𝓝 1) ∧ ∀ k, a k ∉ L ∧ rightAction x (a k) ∈ E := by
  have horbits : ∀ x : X n, μ (rightSubgroupOrbit L x) = 0 := by
    intro x
    induction x using Quotient.inductionOn with
    | h g => rw [rightSubgroupOrbit_mk]; exact hnull g
  obtain ⟨x, hx, hcl⟩ := exists_good_point_in_closure_outside_orbit μ E hE
    (rightSubgroupOrbit L) horbits
  let S : Set (G n) := {g | g ∉ L ∧ rightAction x g ∈ E}
  have hS : (1 : G n) ∈ closure S := by
    apply mem_closure_iff.mpr
    intro U hU h1
    have hUx : x ∈ (fun g => rightAction x g) '' U :=
      ⟨1, h1, rightAction_one x⟩
    obtain ⟨y, ⟨hyU, hyE, hyO⟩⟩ := mem_closure_iff.mp hcl
      ((fun g => rightAction x g) '' U) (rightOrbitMap_isOpen x U hU) hUx
    obtain ⟨g, hgU, rfl⟩ := hyU
    refine ⟨g, hgU, ?_, hyE⟩
    intro hgL
    exact hyO ⟨⟨g, hgL⟩, rfl⟩
  obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.mp hS
  exact ⟨x, hx, a, hlim, ha⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ReverseRootFlow
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The reverse root flow used by a right-action shearing pair

For points separated on the right by g, sampling both at U(-t) gives
relative displacement U(t) g U(-t). This action has exactly the same
invariant sets as the original root flow, so its ergodicity follows
from full real-root ergodicity, without selecting a discrete time.
-/

noncomputable section
open MeasureTheory Filter Set

namespace DukePrimeDegree
open PrimeDegreePackets

lemma reverse_root_pair_displacement {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (x : X n) (g : G n) (t : ℝ) :
    rightAction (rightAction x g) (Matrix.SpecialLinearGroup.transvection hij (-t)) =
      rightAction (rightAction x (Matrix.SpecialLinearGroup.transvection hij (-t)))
        (Matrix.SpecialLinearGroup.transvection hij t * g *
          Matrix.SpecialLinearGroup.transvection hij (-t)) := by
  simp only [rightAction_mul]
  congr 1
  rw [← Matrix.SpecialLinearGroup.transvection_inv hij t]
  group

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact corrections from the closure of one root block

Haar patches are taken in the closed root-generated subgroup. This
closure still preserves the same finite measure. Continuity preserves
the exact normalization of the within-block matrix part, so no abstract
Lie-subgroup or homogeneous-orbit statement is needed for these patches.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma singleBlock_closure_le_stabilizer {n : ℕ}
    (S : Set (Fin n)) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hH : singleBlockRootGroup S ≤ invariantRightSubgroup μ) :
    (singleBlockRootGroup S).topologicalClosure ≤ invariantRightSubgroup μ :=
  (singleBlockRootGroup S).topologicalClosure_minimal hH (isClosed_invariantRightSubgroup μ)

lemma singleBlock_closure_le_blockComplement {n : ℕ} (S : Set (Fin n)) :
    (singleBlockRootGroup S).topologicalClosure ≤ blockMatrixGroup (blockComplementSetoid S) :=
  (singleBlockRootGroup S).topologicalClosure_minimal
    (singleBlockRootGroup_le_blockComplement S)
    (isClosed_blockMatrixGroup (blockComplementSetoid S))

lemma withinBlockPart_singleBlock_closure_commutes {n : ℕ}
    (S : Set (Fin n)) (g : G n) (c : ℝ)
    (hdiag : ∀ i ∈ S, g.val i i = c)
    (hzero : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → g.val i j = 0)
    (u : G n) (hu : u ∈ (singleBlockRootGroup S).topologicalClosure) :
    slMatrixConjugation u (withinBlockPart (blockComplementSetoid S) g.val) =
      withinBlockPart (blockComplementSetoid S) g.val := by
  let M := withinBlockPart (blockComplementSetoid S) g.val
  have hclosed : IsClosed {v : G n | slMatrixConjugation v M = M} :=
    isClosed_eq (by unfold slMatrixConjugation; fun_prop) continuous_const
  exact closure_minimal
    (fun v hv => withinBlockPart_singleBlock_commutes S g c hdiag hzero v hv) hclosed hu

theorem withinBlockPart_singleBlock_closure_conjugation {n : ℕ}
    (S : Set (Fin n)) (g : G n) (c : ℝ)
    (hdiag : ∀ i ∈ S, g.val i i = c)
    (hzero : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → g.val i j = 0)
    (u : G n) (hu : u ∈ (singleBlockRootGroup S).topologicalClosure) :
    withinBlockPart (blockComplementSetoid S) (u * g * u⁻¹).val =
      withinBlockPart (blockComplementSetoid S) g.val := by
  let r := blockComplementSetoid S
  have hb : u ∈ blockMatrixGroup r := singleBlock_closure_le_blockComplement S hu
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
    withinBlockPart_mul_left r u.val _ (cross_zero_of_mem_blockMatrixGroup r u hb),
    withinBlockPart_mul_right r g.val u⁻¹.val
      (cross_zero_of_mem_blockMatrixGroup r u⁻¹ ((blockMatrixGroup r).inv_mem hb))]
  simpa only [slMatrixConjugation, inv_inv, Matrix.mul_assoc] using
    withinBlockPart_singleBlock_closure_commutes S g c hdiag hzero u⁻¹
      ((singleBlockRootGroup S).topologicalClosure.inv_mem hu)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CompactCorrectionPatches
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed compact patches for varying stabilizer corrections

The pair correction tends to identity. Two fixed compact patches then
suffice: small corrections send the smaller patch into the larger one.
Positive Haar mass and finite larger-patch mass give the two constants
used in the fiber-good-set estimate.
-/

noncomputable section
open MeasureTheory Set Filter
open MeasureTheory.Measure
open scoped Topology Pointwise ENNReal

namespace DukePrimeDegree

theorem exists_compact_correction_patches
    {H : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
    [WeaklyLocallyCompactSpace H] [MeasurableSpace H] [OpensMeasurableSpace H]
    (ρ : Measure H) [IsOpenPosMeasure ρ] [IsFiniteMeasureOnCompacts ρ] :
    ∃ W K₀ K₁ : Set H, IsOpen W ∧ 1 ∈ W ∧
      IsCompact K₀ ∧ IsCompact K₁ ∧ K₀ ⊆ K₁ ∧
      0 < ρ K₀ ∧ ρ K₁ < ⊤ ∧
      ∀ b ∈ W, ∀ h ∈ K₀, b * h ∈ K₁ := by
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds (1 : H)
  have h1 : (1 : H) ∈ K := mem_of_mem_nhds hK
  refine ⟨interior K, K, K * K, isOpen_interior,
    mem_interior_iff_mem_nhds.mpr hK, hKc, hKc.mul hKc, ?_,
    measure_pos_of_mem_nhds ρ hK, (hKc.mul hKc).measure_lt_top, ?_⟩
  · intro h hh
    exact ⟨1, h1, h, hh, one_mul h⟩
  · intro b hb h hh
    exact ⟨b, interior_subset hb, h, hh, rfl⟩

/-- A fixed patch works eventually for an arbitrary sequence of
identity-converging corrections. No rate is compared with the orbit
window length. -/
theorem eventually_maps_compact_correction_patch
    {H I : Type*} [Group H] [TopologicalSpace H]
    {l : Filter I} (b : I → H) (hb : Tendsto b l (𝓝 1))
    (W K₀ K₁ : Set H) (hW : IsOpen W) (h1 : 1 ∈ W)
    (hpatch : ∀ a ∈ W, ∀ h ∈ K₀, a * h ∈ K₁) :
    ∀ᶠ i in l, ∀ h ∈ K₀, b i * h ∈ K₁ := by
  exact (hb.eventually (hW.mem_nhds h1)).mono fun i hi => hpatch (b i) hi

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CorrectedPairLimits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactly corrected generic pairs approach the same point

The common correcting parameters lie in one compact stabilizer patch.
After a subsequence, both corrected starting points approach the same
quotient point.  Their actual invariant means can consequently be
compared using a fixed finite continuous approximation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_common_corrected_pair_limit {n : ℕ}
    (H : Subgroup (G n)) (K : Set H) (hK : IsCompact K)
    (u : ℕ → H) (hu : ∀ k, u k ∈ K)
    (a b : ℕ → G n) (ha : Tendsto a atTop (𝓝 1)) (hb : Tendsto b atTop (𝓝 1))
    (x : X n) :
    ∃ u₀ ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => rightAction x (u (φ k) : G n))
        atTop (𝓝 (rightAction x (u₀ : G n))) ∧
      Tendsto (fun k => rightAction x (a (φ k) * b (φ k) * (u (φ k) : G n)))
        atTop (𝓝 (rightAction x (u₀ : G n))) ∧
      Tendsto (fun k => (u (φ k) : G n)⁻¹ *
        (a (φ k) * b (φ k)) * (u (φ k) : G n)) atTop (𝓝 1) := by
  let : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨u₀, hu₀, φ, hφ, hlim⟩ := hK.tendsto_subseq hu
  have hulim : Tendsto (fun k => (u (φ k) : G n)) atTop (𝓝 (u₀ : G n)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hlim
  have hablim : Tendsto (fun k => a (φ k) * b (φ k)) atTop (𝓝 (1 : G n)) := by
    simpa only [one_mul, Function.comp_def] using
      (ha.comp hφ.tendsto_atTop).mul (hb.comp hφ.tendsto_atTop)
  have hfulllim : Tendsto (fun k => a (φ k) * b (φ k) * (u (φ k) : G n))
      atTop (𝓝 (u₀ : G n)) := by
    simpa only [one_mul] using hablim.mul hulim
  have hact : Continuous (fun g : G n => rightAction x g) := by
    exact (continuous_rightAction_uncurry n).comp (continuous_const.prodMk continuous_id)
  refine ⟨u₀, hu₀, φ, hφ, hact.continuousAt.tendsto.comp hulim,
    hact.continuousAt.tendsto.comp hfulllim, ?_⟩
  simpa only [mul_one, inv_mul_cancel] using (hulim.inv.mul hablim).mul hulim

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockCorrectedPairs
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized generic pairs from null block orbits

The small return matrices, their within-block normalizations and the
common compact corrections are selected in this proof. The correction
group is the closure of the single root block, so it preserves the same
component measure. The conclusion does not assume genericity of the
normalized points or a transverse limiting element.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

attribute [local irreducible] singleBlockRootGroup blockMatrixGroup singleBlockClosureGroup

theorem exists_singleBlock_corrected_generic_pairs {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hH : singleBlockRootGroup (↑S) ≤ invariantRightSubgroup μ)
    (ρ : Measure (singleBlockClosureGroup (n := n) (↑S))) [SFinite ρ] [ρ.IsMulLeftInvariant]
    (K₀ K₁ : Set (singleBlockClosureGroup (n := n) (↑S))) (hK₀ : IsCompact K₀) (hK : K₀ ⊆ K₁)
    (W : Set (singleBlockClosureGroup (n := n) (↑S))) (hW : IsOpen W) (h1W : 1 ∈ W)
    (hpatch : ∀ b ∈ W, ∀ u ∈ K₀, b * u ∈ K₁)
    (G₀ : Set (X n)) (hG₀ : MeasurableSet G₀)
    (t : ℝ≥0∞) (ht : t ≠ 0) (httop : t ≠ ⊤)
    (hsize : t + t < ρ K₀) (hbudget : (ρ K₁ * μ G₀ᶜ) / t < 1)
    (hnull : ∀ g : G n,
      μ (range (latticeOrbitPoint g (blockMatrixGroup (blockComplementSetoid (↑S))))) = 0) :
    ∃ (p q : ℕ → X n) (g : ℕ → G n) (c : ℕ → ℝ),
      Tendsto g atTop (𝓝 1) ∧
      (∀ k, q k = rightAction (p k) (g k) ∧
        g k ∉ blockMatrixGroup (blockComplementSetoid (↑S))) ∧
      (∀ᶠ k in atTop, p k ∈ G₀ ∧ q k ∈ G₀) ∧
      ∀ᶠ k in atTop,
        (∀ i ∈ S, (g k).val i i = c k) ∧
          ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (g k).val i j = 0 := by
  classical
  let H : Subgroup (G n) := singleBlockClosureGroup (n := n) (↑S)
  let B : Subgroup (G n) := blockMatrixGroup (blockComplementSetoid (↑S))
  have hHμ : H ≤ invariantRightSubgroup μ := by
    simpa only [H, singleBlockClosureGroup] using
      singleBlock_closure_le_stabilizer (S : Set (Fin n)) μ hH
  have hHB : H ≤ B := by
    simpa only [H, B, singleBlockClosureGroup] using
      singleBlock_closure_le_blockComplement (S : Set (Fin n))
  obtain ⟨E, _hE, hEpos, hEfiber⟩ := exists_positive_goodOrbitFiber_set μ ρ
    (fun x u => rightAction x (u : G n))
    (measurable_rightAction_subgroup_uncurry H)
    (fun u => ⟨(continuous_rightAction u.val).measurable, hHμ u.property⟩)
    K₁ G₀ hG₀ t ht httop hbudget
  obtain ⟨x, hx, a, ha, haE⟩ := exists_small_matrix_generic_pairs B μ E hEpos hnull
  obtain ⟨s, b, c, _hs, hb, he, hbH, _hc, hpart⟩ :=
    exists_singleBlock_transverse_sequence S hS a ha
  let β : ℕ → H := fun k => ⟨b k, by
    simpa only [H, singleBlockClosureGroup] using
      (singleBlockRootGroup (S : Set (Fin n))).le_topologicalClosure (hbH k)⟩
  have hβ : Tendsto β atTop (𝓝 (1 : H)) := by
    apply tendsto_subtype_rng.mpr
    exact hb
  have hβpatch : ∀ᶠ k in atTop, ∀ u ∈ K₀, β k * u ∈ K₁ :=
    eventually_maps_compact_correction_patch β hβ W K₀ K₁ hW h1W hpatch
  have hK₀ne : K₀.Nonempty := by
    by_contra hnone
    have hempty : K₀ = ∅ := Set.not_nonempty_iff_eq_empty.mp hnone
    rw [hempty, measure_empty] at hsize
    exact (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ t + t from zero_le)) hsize
  obtain ⟨u₀, hu₀⟩ := hK₀ne
  have hchoose (k : ℕ) : ∃ u ∈ K₀,
      (∀ v ∈ K₀, β k * v ∈ K₁) →
        rightAction x u.val ∈ G₀ ∧ rightAction (rightAction x (a k)) ((β k * u).val) ∈ G₀ := by
    by_cases hk : ∀ v ∈ K₀, β k * v ∈ K₁
    · obtain ⟨u, hu, hux, huy⟩ := exists_common_goodOrbit_correction ρ
        (fun y v => rightAction y (v : G n))
        (fun y => ((continuous_rightAction_uncurry n).comp
          (continuous_const.prodMk continuous_subtype_val)).measurable)
        K₀ K₁ hK G₀ hG₀ x (rightAction x (a k)) (β k) hk
        ((add_le_add (hEfiber x hx).le (hEfiber _ (haE k).2).le).trans_lt hsize)
      exact ⟨u, hu, fun _ => ⟨hux, huy⟩⟩
    · exact ⟨u₀, hu₀, fun hp => (hk hp).elim⟩
  choose u hu hugood using hchoose
  obtain ⟨_u, _hu, φ, hφ, _hp, _hq, hrelative⟩ :=
    exists_common_corrected_pair_limit H K₀ hK₀ u hu a b ha hb x
  let p (k : ℕ) := rightAction x (u (φ k) : G n)
  let q (k : ℕ) := rightAction x (a (φ k) * b (φ k) * (u (φ k) : G n))
  let g (k : ℕ) := (u (φ k) : G n)⁻¹ * (a (φ k) * b (φ k)) * (u (φ k) : G n)
  refine ⟨p, q, g, c ∘ φ, hrelative, ?_, ?_, ?_⟩
  · intro k
    constructor
    · dsimp only [p, q, g]
      simp only [rightAction_mul]
      congr 1
      group
    · intro hg
      have hab : a (φ k) * b (φ k) ∈ B := by
        have hh := B.mul_mem (B.mul_mem (hHB (u (φ k)).property) hg)
          (B.inv_mem (hHB (u (φ k)).property))
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        dsimp only [g]
        group
      exact (haE (φ k)).1 (by
        have hh := B.mul_mem hab (B.inv_mem (hHB (β (φ k)).property))
        simpa only [β, Subgroup.coe_mk, mul_inv_cancel_right] using hh)
  · filter_upwards [hφ.tendsto_atTop.eventually hβpatch] with k hk
    obtain ⟨hpx, hqx⟩ := hugood (φ k) hk
    refine ⟨hpx, ?_⟩
    simpa only [q, β, Subgroup.coe_mul, Subgroup.coe_mk, rightAction_mul, mul_assoc] using hqx
  · filter_upwards [hφ.tendsto_atTop.eventually hpart] with k hk
    have hnormalized := withinBlockPart_singleBlock_closure_conjugation (↑S)
      (s (φ k)) (c (φ k)) hk.1 hk.2 (u (φ k) : G n)⁻¹
      (by simpa only [H, singleBlockClosureGroup] using H.inv_mem (u (φ k)).property)
    have heq : withinBlockPart (blockComplementSetoid (↑S)) (g k).val =
        withinBlockPart (blockComplementSetoid (↑S)) (s (φ k)).val := by
      simpa only [g, he, inv_inv] using hnormalized
    constructor
    · intro i hi
      have ht := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) heq
      simpa only [withinBlockPart, Setoid.refl, ite_true, if_true, hk.1 i hi,
        Function.comp_apply] using ht
    · intro i hi j hj hij
      have hr : blockComplementSetoid (↑S) i j := ⟨fun _ => hj, fun _ => hi⟩
      have ht := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) heq
      simpa only [withinBlockPart, hr, ite_true, if_true, hk.2 i hi j hj hij] using ht

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_TerminalPairComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Comparing two generic terminal windows

This is the finite-test form of the shearing contradiction. Uniform
closeness of the paired paths and two generic average estimates bound
the actual measure-invariance defect. Neither path is assumed to stay
in a compact set.
-/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_interval_average_sub_bound
    (F G : ℝ → ℝ) (a b ε : ℝ) (hab : a < b)
    (hF : IntervalIntegrable F volume a b)
    (hG : IntervalIntegrable G volume a b)
    (hclose : ∀ t ∈ Icc a b, |F t - G t| ≤ ε) :
    |(b - a)⁻¹ * (∫ t in a..b, F t) -
      (b - a)⁻¹ * (∫ t in a..b, G t)| ≤ ε := by
  have hpos : 0 < b - a := sub_pos.mpr hab
  rw [← mul_sub, ← intervalIntegral.integral_sub hF hG,
    abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => F t - G t) (a := a) (b := b) (C := ε)
    (fun t ht => by
      rw [uIoc_of_le hab.le] at ht
      simpa only [Real.norm_eq_abs] using hclose t ⟨ht.1.le, ht.2⟩)
  have hbnd : |∫ t in a..b, F t - G t| ≤ ε * (b - a) := by
    simpa only [Real.norm_eq_abs, abs_of_pos hpos] using hnorm
  calc
    _ ≤ (b - a)⁻¹ * (ε * (b - a)) :=
      mul_le_mul_of_nonneg_left hbnd (inv_nonneg.mpr hpos.le)
    _ = ε := by field_simp

lemma abs_sub_le_three_errors (a b c d ε : ℝ)
    (hab : |a - b| ≤ ε) (hbc : |b - c| ≤ ε) (hcd : |c - d| ≤ ε) :
    |a - d| ≤ 3 * ε := by
  calc
    |a - d| ≤ |a - b| + |b - d| := abs_sub_le a b d
    _ ≤ |a - b| + (|b - c| + |c - d|) :=
      add_le_add (le_refl _) (abs_sub_le b c d)
    _ ≤ ε + (ε + ε) := add_le_add hab (add_le_add hbc hcd)
    _ = 3 * ε := by ring

theorem terminal_pair_invarianceDefect_bound {n : ℕ}
    (μ : Measure (X n))
    (f : CompactlySupportedContinuousMap (X n) ℝ) (h : G n)
    (p q : ℝ → X n) (hp : Continuous p) (hq : Continuous q)
    (δ T ε : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (hleft : |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
      f (rightAction (p t) h)) - ∫ x, f (rightAction x h) ∂μ| ≤ ε)
    (hright : |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T, f (q t)) -
      ∫ x, f x ∂μ| ≤ ε)
    (hclose : ∀ t ∈ Icc ((1 - δ) * T) T,
      |f (rightAction (p t) h) - f (q t)| ≤ ε) :
    |invarianceDefect μ f h| ≤ 3 * ε := by
  have hab : (1 - δ) * T < T := by nlinarith
  have hF := ((f.continuous.comp (continuous_rightAction h)).comp hp).intervalIntegrable
    (μ := volume)
    ((1 - δ) * T) T
  have hG := (f.continuous.comp hq).intervalIntegrable (μ := volume) ((1 - δ) * T) T
  have hmiddle := normalized_interval_average_sub_bound
    (fun t => f (rightAction (p t) h)) (fun t => f (q t))
    ((1 - δ) * T) T ε hab hF hG hclose
  have hlength : T - (1 - δ) * T = δ * T := by ring
  rw [hlength] at hmiddle
  exact abs_sub_le_three_errors _ _ _ _ ε
    (by simpa only [abs_sub_comm] using hleft) hmiddle hright

/-- A test separating a compact transverse shell contradicts paired
genericity at error one quarter of that separation. -/
theorem no_terminal_pair_with_separated_defect {n : ℕ}
    (μ : Measure (X n))
    (f : CompactlySupportedContinuousMap (X n) ℝ) (h : G n)
    (p q : ℝ → X n) (hp : Continuous p) (hq : Continuous q)
    (δ T ε : ℝ) (hδ : 0 < δ) (hT : 0 < T) (hε : 0 < ε)
    (hsep : ε < |invarianceDefect μ f h|)
    (hleft : |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
      f (rightAction (p t) h)) - ∫ x, f (rightAction x h) ∂μ| ≤ ε / 4)
    (hright : |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T, f (q t)) -
      ∫ x, f x ∂μ| ≤ ε / 4)
    (hclose : ∀ t ∈ Icc ((1 - δ) * T) T,
      |f (rightAction (p t) h) - f (q t)| ≤ ε / 4) : False := by
  have hbound := terminal_pair_invarianceDefect_bound μ f h p q hp hq
    δ T (ε / 4) hδ hT hleft hright hclose
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockShearingContradiction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The fixed-window contradiction for a normalized transverse pair

All quantifiers retain the order needed by the argument: the compact
shell and its separating tests are fixed first, then the terminal
fraction and the generic set, and only then the nearby pair and its
root-dependent stopping times.  The limit is proved to lie in the shell
by its normalized matrix entries.
-/

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem singleBlock_fixed_window_contradiction {n : ℕ}
    (S : Set (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (μ : Measure (X n))
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (F : Finset (CompactlySupportedContinuousMap (X n) ℝ))
    (hsep : ∀ h ∈ transverseMatrixShell (blockComplementSetoid S) a,
      ∃ f ∈ F, ε < |invarianceDefect μ f h|)
    (δ : ℝ) (hδ : 0 < δ) (_hδ1 : δ < 1)
    (hwindow : ∀ (i j : Fin n) (hij : i ≠ j)
        (g : ℕ → G n) (T : ℕ → ℝ),
        (∀ m, 0 < T m) →
        (∀ m, ∀ t ∈ Icc 0 (T m), rootShearSize hij (g m) t ≤ a) →
        ∀ h ∈ transverseMatrixShell (blockComplementSetoid S) a,
          Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (T m) * g m *
            Matrix.SpecialLinearGroup.transvection hij (-(T m))) atTop (𝓝 h) →
          ∀ᶠ m in atTop, ∀ s ∈ Icc (1 - δ) 1, ∀ f ∈ F, ∀ x : X n,
            |f (rightAction x (Matrix.SpecialLinearGroup.transvection hij (s * T m) *
                g m * Matrix.SpecialLinearGroup.transvection hij (-(s * T m)))) -
              f (rightAction x h)| < ε / 4)
    (E : Set (X n)) (R : ℝ)
    (hgood : ∀ x ∈ E, ∀ i ∈ S, ∀ j ∈ S, ∀ (hij : i ≠ j), ∀ f ∈ F, ∀ T ≥ R,
      |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
        f (rightAction x (Matrix.SpecialLinearGroup.transvection hij (-t)))) -
          ∫ y, f y ∂μ| ≤ ε / 4 ∧
      ∀ h ∈ transverseMatrixShell (blockComplementSetoid S) a,
        |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
          f (rightAction (rightAction x
            (Matrix.SpecialLinearGroup.transvection hij (-t))) h)) -
              ∫ y, f (rightAction y h) ∂μ| ≤ ε / 4)
    (p q : ℕ → X n) (g : ℕ → G n) (c : ℕ → ℝ)
    (hg : Tendsto g atTop (𝓝 1))
    (hpq : ∀ m, q m = rightAction (p m) (g m) ∧
      g m ∉ blockMatrixGroup (blockComplementSetoid S))
    (hE : ∀ᶠ m in atTop, p m ∈ E ∧ q m ∈ E)
    (hpart : ∀ᶠ m in atTop,
      (∀ i ∈ S, (g m).val i i = c m) ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (g m).val i j = 0) : False := by
  obtain ⟨i, j, hij, hi, hj, φ, T, h, hφ, hTtop, _hne, _hout,
    hdiff, hlim, hT, _hcentral⟩ :=
    exists_singleBlock_transverse_shearing_limit S k l hkl hk hl g hg
      (fun m => (hpq m).2) c hpart a ha
  have hh : h ∈ transverseMatrixShell (blockComplementSetoid S) a := by
    refine ⟨?_, hdiff⟩
    apply singleBlock_conjugation_limit_withinPart S (g ∘ φ)
      (fun m => Matrix.SpecialLinearGroup.transvection hij (T m)) (c ∘ φ)
      (hg.comp hφ.tendsto_atTop)
      (fun m => root_mem_singleBlockRootGroup S i hi j hj hij (T m))
      (hφ.tendsto_atTop.eventually hpart) h
    simpa only [Function.comp_apply, Matrix.SpecialLinearGroup.transvection_inv] using hlim
  obtain ⟨f, hf, hfh⟩ := hsep h hh
  have hclose := hwindow i j hij (g ∘ φ) T (fun m => (hT m).1)
    (fun m => (hT m).2.2) h hh hlim
  obtain ⟨m, ⟨hmclose, hmE⟩, hmR⟩ :=
    ((hclose.and (hφ.tendsto_atTop.eventually hE)).and
      (hTtop.eventually (eventually_ge_atTop R))).exists
  let P (t : ℝ) := rightAction (p (φ m)) (Matrix.SpecialLinearGroup.transvection hij (-t))
  let Q (t : ℝ) := rightAction (q (φ m)) (Matrix.SpecialLinearGroup.transvection hij (-t))
  have hP : Continuous P := (continuous_rightAction_uncurry n).comp
    (continuous_const.prodMk ((continuous_rootTransvection hij).comp continuous_neg))
  have hQ : Continuous Q := (continuous_rightAction_uncurry n).comp
    (continuous_const.prodMk ((continuous_rootTransvection hij).comp continuous_neg))
  apply no_terminal_pair_with_separated_defect μ f h P Q hP hQ δ (T m) ε
    hδ (hT m).1 hε hfh
  · exact (hgood (p (φ m)) hmE.1 i hi j hj hij f hf (T m) hmR).2 h hh
  · exact (hgood (q (φ m)) hmE.2 i hi j hj hij f hf (T m) hmR).1
  · intro t ht
    have hTm : 0 < T m := (hT m).1
    have hs : t / T m ∈ Icc (1 - δ) 1 := by
      constructor
      · exact (le_div_iff₀ hTm).mpr ht.1
      · exact (div_le_iff₀ hTm).mpr (by simpa only [one_mul] using ht.2)
    have hc := hmclose (t / T m) hs f hf (P t)
    rw [div_mul_cancel₀ t (ne_of_gt hTm)] at hc
    simp only [Function.comp_apply] at hc
    have heq : Q t = rightAction (P t)
        (Matrix.SpecialLinearGroup.transvection hij t * g (φ m) *
          Matrix.SpecialLinearGroup.transvection hij (-t)) := by
      dsimp only [Q, P]
      rw [(hpq (φ m)).1]
      exact reverse_root_pair_displacement hij (p (φ m)) (g (φ m)) t
    rw [← heq] at hc
    exact (by simpa only [abs_sub_comm] using hc.le)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockOrbitExistence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A positive-mass block orbit from actual root ergodicity

Local block preservation of the measure stabilizer supplies the fixed
transverse shell.  Haar patches supply the common corrections, and root
ergodicity supplies a common generic set.  If every block orbit were
null, the resulting normalized transverse pairs would contradict the
fixed-window shearing estimate.
-/

noncomputable section
open Matrix MeasureTheory Set Filter
open MeasureTheory.Measure
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

attribute [local irreducible] singleBlockRootGroup blockMatrixGroup singleBlockClosureGroup

lemma exists_positive_real_fiber_budget (b t : ℝ≥0∞)
    (hb : b ≠ ⊤) (ht : t ≠ 0) (httop : t ≠ ⊤) :
    ∃ η : ℝ, 0 < η ∧ (b * ENNReal.ofReal η) / t < 1 := by
  let η : ℝ := t.toReal / (2 * (b.toReal + 1))
  have htpos : 0 < t.toReal := ENNReal.toReal_pos ht httop
  have hbpos : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have hden : 0 < 2 * (b.toReal + 1) := by positivity
  have hη : 0 < η := div_pos htpos hden
  refine ⟨η, hη, ?_⟩
  rw [ENNReal.div_lt_iff (Or.inl ht) (Or.inl httop), one_mul]
  apply (ENNReal.toReal_lt_toReal (by finiteness) httop).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.le]
  dsimp only [η]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hden).mpr
  nlinarith

theorem exists_positive_singleBlock_orbit_of_patch {n : ℕ}
    (S : Finset (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    [ErgodicSMul (singleBlockRootGroup (S : Set (Fin n))) (X n) μ]
    (hlocal : {g : invariantRightSubgroup μ |
      g.val ∈ blockMatrixGroup (blockComplementSetoid (S : Set (Fin n)))} ∈
        𝓝 (1 : invariantRightSubgroup μ))
    (ρ : Measure (singleBlockClosureGroup (n := n) (S : Set (Fin n)))) [SFinite ρ] [ρ.IsMulLeftInvariant]
    (W K₀ K₁ : Set (singleBlockClosureGroup (n := n) (S : Set (Fin n))))
    (hW : IsOpen W) (h1W : 1 ∈ W) (hK₀ : IsCompact K₀) (hK : K₀ ⊆ K₁)
    (hK₀pos : 0 < ρ K₀) (hK₁fin : ρ K₁ < ⊤)
    (hpatch : ∀ b ∈ W, ∀ u ∈ K₀, b * u ∈ K₁) :
    ∃ g : G n,
      μ (range (latticeOrbitPoint g (blockMatrixGroup (blockComplementSetoid (S : Set (Fin n)))))) ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hK₀fin : ρ K₀ ≠ ⊤ := ((measure_mono hK).trans_lt hK₁fin).ne
  have hmass : 0 < (ρ K₀).toReal := ENNReal.toReal_pos hK₀pos.ne' hK₀fin
  let t : ℝ≥0∞ := ENNReal.ofReal ((ρ K₀).toReal / 4)
  have ht : t ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have httop : t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsize : t + t < ρ K₀ := by
    rw [← ENNReal.ofReal_toReal hK₀fin]
    change ENNReal.ofReal ((ρ K₀).toReal / 4) +
      ENNReal.ofReal ((ρ K₀).toReal / 4) < ENNReal.ofReal (ρ K₀).toReal
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff hmass).mpr (by linarith)
  obtain ⟨η, hη, hbudget⟩ := exists_positive_real_fiber_budget (ρ K₁) t hK₁fin.ne ht httop
  obtain ⟨a, ha, F, ε, hε, hsep⟩ := exists_finite_small_transverse_separators
    μ (blockComplementSetoid (S : Set (Fin n))) hlocal
  let K := transverseMatrixShell (blockComplementSetoid (S : Set (Fin n))) a
  have hKcompact : IsCompact K := transverseMatrixShell_isCompact _ _
  obtain ⟨δ, hδ, hδ1, hwindow⟩ := exists_fixed_terminal_observable_fraction
    F K hKcompact a (ε / 4) ha.le (by positivity)
  obtain ⟨E, hE, hEμ, R, _hR, hgood⟩ := exists_singleBlock_terminal_generic_set
    (S : Set (Fin n)) μ F K hKcompact (ε / 4) δ η (by positivity) hδ hδ1 hη
  have hbudgetE : (ρ K₁ * μ Eᶜ) / t < 1 := by
    apply lt_of_le_of_lt _ hbudget
    gcongr
  have hH : singleBlockRootGroup (S : Set (Fin n)) ≤ invariantRightSubgroup μ :=
    subgroup_le_invariantRightSubgroup_of_invariant_action _ μ
  obtain ⟨p, q, g, c, hg, hpq, hpqE, hpart⟩ :=
    exists_singleBlock_corrected_generic_pairs S ⟨k, hk⟩ μ hH ρ K₀ K₁ hK₀ hK
      W hW h1W hpatch E hE t ht httop hsize hbudgetE hnone
  exact singleBlock_fixed_window_contradiction (S : Set (Fin n)) k l hkl hk hl μ a ε ha hε F hsep
    δ hδ hδ1 hwindow E R hgood p q g c hg hpq hpqE hpart

/-- The correction patches are constructed from Haar measure on the
closed root group; no patch or homogeneous-orbit assumption remains. -/
theorem exists_positive_singleBlock_orbit_oai {n : ℕ}
    (S : Finset (Fin n)) (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    [ErgodicSMul (singleBlockRootGroup (S : Set (Fin n))) (X n) μ]
    (hlocal : {g : invariantRightSubgroup μ |
      g.val ∈ blockMatrixGroup (blockComplementSetoid (S : Set (Fin n)))} ∈
        𝓝 (1 : invariantRightSubgroup μ)) :
    ∃ g : G n,
      μ (range (latticeOrbitPoint g (blockMatrixGroup (blockComplementSetoid (S : Set (Fin n)))))) ≠ 0 := by
  let H : Subgroup (G n) := singleBlockClosureGroup (n := n) (S : Set (Fin n))
  let : LocallyCompactSpace H := by
    unfold H singleBlockClosureGroup
    exact (singleBlockRootGroup (S : Set (Fin n))).isClosed_topologicalClosure.locallyCompactSpace
  let : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let ρ : Measure H := Measure.haar
  obtain ⟨W, K₀, K₁, hW, h1W, hK₀, _hK₁, hK, hpos, hfin, hpatch⟩ :=
    exists_compact_correction_patches ρ
  exact exists_positive_singleBlock_orbit_of_patch S k l hkl hk hl μ hlocal ρ
    W K₀ K₁ hW h1W hK₀ hK hpos hfin hpatch

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_positive_singleBlock_orbit_oai := @OAI.DukePrimeDegree.exists_positive_singleBlock_orbit_oai
