-- Prove2me | solution 1 for OAI.KadisonKastler.positiveCone_parts_mem_centralVectorSpace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:09:21.54112+00:00
-- url     : https://prove2.me/submissions/f9558d3d-5511-491b-8864-e6a3d6618aef

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K068
import Definitions.Def_Q260K034
import Theorems.Thm_OAI_KadisonKastler_matrixCentralProjection_eq

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PairedMatrixColumn
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.PointedMatrixSites.wordOperator_cons _root_.OAI.KadisonKastler.PointedMatrixSites.wordVector_cons _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The partial isometry from a matrix corner to central vectors

This is the algebraic corner map in Haagerup, Acta Math.158(1987),
Lemma3.5. Its initial projection is the matching minimal corner; its
final projection is the finite-matrix central-vector projection.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E F : MatrixUnitSystem ι (H →L[ℂ] H))
  (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

include hc in
omit [Nonempty ι] in
private theorem matchingEntry_mul (i j k l : ι) :
    (E.entry i j * F.entry i j) * (E.entry k l * F.entry k l) =
      if j = k then E.entry i l * F.entry i l else 0 := by
  calc
    _ = (E.entry i j * E.entry k l) * (F.entry i j * F.entry k l) := by
      rw [mul_assoc,← mul_assoc (F.entry i j),← (hc k l i j).eq]
      simp only [mul_assoc]
    _ = _ := by rw [E.mul_entry,F.mul_entry]; split_ifs <;> simp

include hc in
omit [Nonempty ι] in
private theorem matchingEntry_star (i j : ι) :
    star (E.entry i j * F.entry i j) = E.entry j i * F.entry j i := by
  rw [star_mul,E.star_entry,F.star_entry,← (hc j i j i).eq]

omit [DecidableEq ι] [Nonempty ι] in
private theorem pairedMatrixColumn_scalar_sq :
    (Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹) *
      Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹)) = (Fintype.card ι : ℂ)⁻¹ := by
  have he : (Real.sqrt (Fintype.card ι))⁻¹ * (Real.sqrt (Fintype.card ι))⁻¹ =
      (Fintype.card ι : ℝ)⁻¹ := by
    rw [← mul_inv_rev,← pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [← Complex.ofReal_mul,he,Complex.ofReal_inv,Complex.ofReal_natCast]

include hc in
omit [Nonempty ι] in
theorem pairedMatrixColumn_star (o : ι) :
    star (pairedMatrixColumn E F o) =
      Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹) •
        ∑ i, E.entry o i * F.entry o i := by
  have hs : star (Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹)) =
      Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹) :=
    Complex.conj_ofReal _
  simp only [pairedMatrixColumn,star_smul,star_sum]
  rw [hs]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => matchingEntry_star E F hc i o)

include hc in
omit [Nonempty ι] in
theorem pairedMatrixColumn_final (o : ι) :
    pairedMatrixColumn E F o * star (pairedMatrixColumn E F o) =
      pairedMatrixProjection E F := by
  rw [pairedMatrixColumn_star E F hc]
  simp only [pairedMatrixColumn,smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [pairedMatrixColumn_scalar_sq]
  simp only [Finset.sum_mul,Finset.mul_sum,matchingEntry_mul E F hc,ite_true, if_true]
  rw [Finset.sum_comm]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCentralCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The Hilbert-space identification of a matrix corner and central vectors

The map from Haagerup's Lemma3.5 is a genuine unitary between these
closed subspaces. State and natural-cone properties are separate claims.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E : MatrixUnitSystem ι (Algebra M))
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hright in
theorem matrixCentralColumn_final (o : ι) :
    matrixCentralColumn E J hJ o * star (matrixCentralColumn E J hJ o) =
      (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection := by
  rw [matrixCentralProjection_eq E J hJ hright]
  apply pairedMatrixColumn_final
  intro i j k l
  exact VonNeumannAlgebra.mem_commutant_iff.mp (hright (E.entry k l))
    (E.entry i j).val (E.entry i j).property

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveCone
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The cone generated by modular quadratic vectors

The definition uses actual vectors `a J a J ξ`, finite positive combinations,
and norm closure. Its invariance is algebraic. Positivity of the reference
pairing is kept explicit here and proved for the polar Tomita conjugation
in `TomitaPositivePairing`.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.instInnerProductSpaceReal_solutions
theorem modularQuadratic_mem_positiveCone (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (a : Algebra M) :
    modularQuadratic J a ξ ∈ modularPositiveCone (M := M) J ξ :=
  subset_closure (ConvexCone.subset_hull ⟨a,rfl⟩)

theorem zero_mem_modularPositiveCone (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    (0 : H) ∈ modularPositiveCone (M := M) J ξ := by
  have h := modularQuadratic_mem_positiveCone J ξ (0 : Algebra M)
  simpa only [modularQuadratic,ZeroMemClass.coe_zero,zero_mul,zero_apply] using h

theorem modularQuadratic_preserves_positiveCone
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a : Algebra M) {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    modularQuadratic J a η ∈ modularPositiveCone (M := M) J ξ := by
  let C := ConvexCone.hull ℝ (Set.range (fun b : Algebra M => modularQuadratic J b ξ))
  have hC : C ≤ C.comap ((modularQuadratic J a).restrictScalars ℝ).toLinearMap := by
    apply ConvexCone.hull_min
    rintro _ ⟨b,rfl⟩
    change modularQuadratic J a (modularQuadratic J b ξ) ∈ C
    change (modularQuadratic J a * modularQuadratic J b) ξ ∈ C
    rw [modularQuadratic_mul J hJ hright]
    exact ConvexCone.subset_hull ⟨a*b,rfl⟩
  exact map_mem_closure (modularQuadratic J a).continuous hη (fun _ hx => hC hx)

theorem modularPositiveCone_acute
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ) (hζ : ζ ∈ modularPositiveCone (M := M) J ξ) :
    0 ≤ inner ℝ η ζ := by
  let C := ConvexCone.hull ℝ (Set.range (fun a : Algebra M => modularQuadratic J a ξ))
  have hgen (a b : Algebra M) :
      0 ≤ inner ℝ (modularQuadratic J a ξ) (modularQuadratic J b ξ) := by
    rw [real_inner_eq_re_inner,← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint,modularQuadratic_star J hJ hright]
    change 0 ≤ (inner ℂ ξ ((modularQuadratic J (star a) * modularQuadratic J b) ξ)).re
    rw [modularQuadratic_mul J hJ hright]
    exact hpos (star a*b)
  have hleft (b : Algebra M) : C ≤ realInnerHalfspace (modularQuadratic J b ξ) := by
    apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    exact hgen a b
  have hh (υ : H) (hυ : υ ∈ C) : C ≤ realInnerHalfspace υ := by
    apply ConvexCone.hull_min
    rintro _ ⟨b,rfl⟩
    change 0 ≤ inner ℝ (modularQuadratic J b ξ) υ
    rw [real_inner_comm]
    exact hleft b hυ
  have hhclosed (υ : H) : IsClosed {v : H | 0 ≤ inner ℝ v υ} :=
    isClosed_le continuous_const (continuous_id.inner continuous_const)
  have hηC (υ : H) (hυ : υ ∈ C) : 0 ≤ inner ℝ η υ :=
    closure_minimal (fun _ hx => hh υ hυ hx) (hhclosed υ) hη
  rw [real_inner_comm]
  apply closure_minimal (s := (C : Set H)) ?_ (hhclosed η) hζ
  intro υ hυ
  change 0 ≤ inner ℝ υ η
  rw [real_inner_comm]
  exact hηC υ hυ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCentralCone
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix corner maps preserve the generated positive cone

Both directions of the corner partial isometry are positive sums of
modular quadratic operators. The central-vector projection therefore
preserves this cone as well.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
private theorem complex_ofReal_smul (r : ℝ) (η : H) : Complex.ofReal r • η = r • η := by
  simpa only [Complex.coe_algebraMap] using (IsScalarTower.algebraMap_smul ℂ r η)

theorem modularPositiveCone_sum_mem (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H)
    {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : ∀ i ∈ s, v i ∈ modularPositiveCone (M := M) J ξ) :
    ∑ i ∈ s, v i ∈ modularPositiveCone (M := M) J ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero_mem_modularPositiveCone (M := M) J ξ
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (modularPositiveCone J ξ).add_mem (hv i (Finset.mem_insert_self i s))
      (ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (E : MatrixUnitSystem ι (Algebra M))
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H)

include hright in
theorem matrixCentralColumn_preserves_positiveCone (o : ι) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    matrixCentralColumn E J hJ o η ∈ modularPositiveCone (M := M) J ξ := by
  have hs : ∑ i, modularQuadratic J (E.entry i o) η ∈ modularPositiveCone (M := M) J ξ :=
    modularPositiveCone_sum_mem J ξ Finset.univ _
      (fun i _ => modularQuadratic_preserves_positiveCone J hJ hright ξ _ hη)
  have hc : 0 < (Real.sqrt (Fintype.card ι))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  have h := (modularPositiveCone (M := M) J ξ).smul_mem hc hs
  change Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹) •
    ((∑ i, (E.entry i o).val * conjugationOperator J (E.entry i o).val) η) ∈ _
  simpa only [sum_apply,modularQuadratic,mul_apply_eq_comp,← complex_ofReal_smul] using h

include hright in
theorem matrixCentralColumn_star_preserves_positiveCone (o : ι) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    star (matrixCentralColumn E J hJ o) η ∈ modularPositiveCone (M := M) J ξ := by
  have hs : ∑ i, modularQuadratic J (E.entry o i) η ∈ modularPositiveCone (M := M) J ξ :=
    modularPositiveCone_sum_mem J ξ Finset.univ _
      (fun i _ => modularQuadratic_preserves_positiveCone J hJ hright ξ _ hη)
  have hc : 0 < (Real.sqrt (Fintype.card ι))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  have h := (modularPositiveCone (M := M) J ξ).smul_mem hc hs
  have hcomm (i j k l : ι) : Commute (E.entry i j).val
      (conjugationOperator J (E.entry k l).val) :=
    VonNeumannAlgebra.mem_commutant_iff.mp (hright (E.entry k l))
      (E.entry i j).val (E.entry i j).property
  change star (pairedMatrixColumn (E.map M.toStarSubalgebra.subtype)
    (conjugateMatrixUnits J hJ (E.map M.toStarSubalgebra.subtype)) o) η ∈ _
  rw [pairedMatrixColumn_star _ _ hcomm]
  change Complex.ofReal ((Real.sqrt (Fintype.card ι))⁻¹) •
    ((∑ i, (E.entry o i).val * conjugationOperator J (E.entry o i).val) η) ∈ _
  simpa only [sum_apply,modularQuadratic,mul_apply_eq_comp,← complex_ofReal_smul] using h

include hJ hright in
theorem matrixCentralProjection_preserves_positiveCone (o : ι) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection η ∈
      modularPositiveCone (M := M) J ξ := by
  rw [← matrixCentralColumn_final E J hJ hright o,mul_apply_eq_comp]
  exact matrixCentralColumn_preserves_positiveCone E J hJ hright ξ o
    (matrixCentralColumn_star_preserves_positiveCone E J hJ hright ξ o hη)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativePositiveDecomposition
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.PointedMatrixSites.wordOperator_cons _root_.OAI.KadisonKastler.PointedMatrixSites.wordVector_cons _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positive decomposition inside a finite-matrix central space

Orthogonal positive parts of a central vector remain central: the positive
central projection cannot discard a common nonzero component of those parts.
Their support projections therefore belong to the relative commutant.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

attribute [local instance] OAI.KadisonKastler.relativePositiveDecompositionRealInner
theorem positiveCone_parts_mem_centralVectorSpace_oai
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {α β : H} (hα : α ∈ modularPositiveCone (M := M) J ξ)
    (hβ : β ∈ modularPositiveCone (M := M) J ξ)
    (horth : inner ℝ α β=0)
    (hdiff : α-β ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J) :
    α ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J ∧
      β ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J := by
  classical
  let K := centralVectorSpace (matrixUnitConcreteAlgebra E) J
  let P := K.starProjection
  let d := α-P α
  have hPd : P (α-β)=α-β := Submodule.starProjection_eq_self_iff.mpr hdiff
  have he : β-P β=d := by
    rw [map_sub] at hPd
    dsimp [d]
    calc
      β-P β=α-(P α-P β)-P β := by rw [hPd]; abel
      _=α-P α := by abel
  have hd : d ∈ Kᗮ := K.sub_starProjection_mem_orthogonal α
  have hcrossa : inner ℝ (P α) d=0 := by
    exact congrArg Complex.re (K.inner_right_of_mem_orthogonal (K.starProjection_apply_mem α) hd)
  have hcrossb : inner ℝ d (P β)=0 := by
    exact congrArg Complex.re (K.inner_left_of_mem_orthogonal (K.starProjection_apply_mem β) hd)
  have hpair : inner ℝ α β=inner ℝ (P α) (P β)+‖d‖^2 := by
    have ha : α=P α+d := by dsimp [d]; abel
    have hb : β=P β+d := by rw [← he]; abel
    conv_lhs => rw [ha,hb]
    rw [inner_add_left,inner_add_right,inner_add_right,hcrossa,hcrossb,
      real_inner_self_eq_norm_sq]
    ring
  have hPα := matrixCentralProjection_preserves_positiveCone E J hJ hright ξ
    (Classical.choice inferInstance) hα
  have hPβ := matrixCentralProjection_preserves_positiveCone E J hJ hright ξ
    (Classical.choice inferInstance) hβ
  have hnonneg := modularPositiveCone_acute J hJ hright ξ hpos hPα hPβ
  have hd0 : d=0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg d]
  constructor
  · have ha : α=P α := sub_eq_zero.mp hd0
    rw [ha]
    exact K.starProjection_apply_mem α
  · have hb : β=P β := sub_eq_zero.mp (he.trans hd0)
    rw [hb]
    exact K.starProjection_apply_mem β

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.positiveCone_parts_mem_centralVectorSpace_oai.{u_1, u_2} := @OAI.KadisonKastler.positiveCone_parts_mem_centralVectorSpace_oai.{u_1, u_2}
