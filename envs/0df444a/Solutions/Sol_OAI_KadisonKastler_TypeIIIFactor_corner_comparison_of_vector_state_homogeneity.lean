-- Prove2me | solution 1 for OAI.KadisonKastler.TypeIIIFactor.corner_comparison_of_vector_state_homogeneity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:51:47.380243+00:00
-- url     : https://prove2.me/submissions/6779ccf1-2bce-4bd3-9d9c-4da29f00c3d3

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
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
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Extend
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
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
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
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
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K067
import Definitions.Def_Q260K033
import Theorems.Thm_OAI_KadisonKastler_TypeIIIFactor_exists_isometry_onto_projection
import Theorems.Thm_OAI_KadisonKastler_isometry_pullback_norm_sq
import Theorems.Thm_OAI_KadisonKastler_vectorCornerState_pullback

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerStateWeights
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalized corner states of faithful vector states

The weights of a proper nonzero projection lie strictly between zero and
one. The two normalized compressions have norm at most one and reconstruct
a state centralizing the projection with exactly those scalar weights.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem cornerFunctional_vectorFunctional (p : AlgebraProjection M) (ξ : H) :
    cornerFunctional (vectorFunctional ξ) p.val = vectorFunctional (p.val.val ξ) := by
  ext a
  change inner ℂ ξ (p.val.val (a.val (p.val.val ξ))) =
    inner ℂ (p.val.val ξ) (a.val (p.val.val ξ))
  have hs : p.val.val.adjoint = p.val.val :=
    (p.property.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
  rw [← p.val.val.adjoint_inner_right,hs]

theorem projectionVectorWeight_pos (p : AlgebraProjection M) (ξ : H)
    (hξ : Function.Injective (algebraVectorMap M ξ)) (hp : p.val ≠ 0) :
    0 < projectionVectorWeight p ξ := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  apply hp
  apply hξ
  change p.val.val ξ = (0 : H →L[ℂ] H) ξ
  simpa only [zero_apply] using hz

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerStatePullback
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Isometric pullback of corner-state comparisons

An isometry onto a projection identifies its corner with the original
algebra. The two sandwich maps preserve the norm of corner-supported
functionals, so a state comparison on the original factor supplies the
same comparison in the corner without a multiplicative loss.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem sandwichFunctional_comp (φ : A →L[ℂ] ℂ) (u v : A) :
    sandwichFunctional (sandwichFunctional φ u) v = sandwichFunctional φ (v*u) := by
  ext a
  simp only [sandwichFunctional_apply,star_mul,mul_assoc]

theorem sandwichFunctional_sub (φ ψ : A →L[ℂ] ℂ) (u : A) :
    sandwichFunctional (φ-ψ) u = sandwichFunctional φ u-sandwichFunctional ψ u := by
  ext a
  rfl

theorem sandwichFunctional_one (φ : A →L[ℂ] ℂ) : sandwichFunctional φ 1=φ := by
  ext a
  simp only [sandwichFunctional_apply,star_one,one_mul,mul_one]

theorem sandwichFunctional_projection (φ : A →L[ℂ] ℂ) (p : A)
    (hp : IsStarProjection p) : sandwichFunctional φ p=cornerFunctional φ p := by
  ext a
  simp only [sandwichFunctional_apply,cornerFunctional_apply,hp.isSelfAdjoint.star_eq]

theorem sandwichFunctional_norm_le (φ : A →L[ℂ] ℂ) (u : A) (hu : ‖u‖ ≤ 1) :
    ‖sandwichFunctional φ u‖ ≤ ‖φ‖ := by
  apply (sandwichFunctional φ u).opNorm_le_bound (norm_nonneg φ)
  intro a
  change ‖φ (star u*a*u)‖ ≤ ‖φ‖*‖a‖
  calc
    _ ≤ ‖φ‖*‖star u*a*u‖ := φ.le_opNorm _
    _ ≤ ‖φ‖*((‖u‖*‖a‖)*‖u‖) := by
      gcongr
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (by simpa only [norm_star] using norm_mul_le (star u) a)
          (norm_nonneg u))
    _ ≤ ‖φ‖*((1*‖a‖)*1) := by gcongr
    _ = _ := by ring

theorem sandwichFunctional_isometry_norm (φ : A →L[ℂ] ℂ)
    (v : A) (hv : star v*v=1) (hnorm : ‖v‖ ≤ 1) :
    ‖sandwichFunctional φ v‖=‖φ‖ := by
  apply le_antisymm (sandwichFunctional_norm_le φ v hnorm)
  have h := sandwichFunctional_norm_le (sandwichFunctional φ v) (star v)
    (by simpa only [norm_star] using hnorm)
  rwa [sandwichFunctional_comp,hv,sandwichFunctional_one] at h

theorem cornerFunctional_idempotent (φ : A →L[ℂ] ℂ) (p : A) (hp : IsStarProjection p) :
    cornerFunctional (cornerFunctional φ p) p=cornerFunctional φ p := by
  ext a
  change φ (p*(p*a*p)*p)=φ (p*a*p)
  congr 1
  calc
    _ = (p*p)*a*(p*p) := by simp only [mul_assoc]
    _ = _ := by rw [hp.isIdempotentElem.eq]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem isometry_norm_le_one (v : Algebra M) (hv : star v*v=1) : ‖v‖ ≤ 1 := by
  let a : PartialIsometry M := ⟨⟨1,IsStarProjection.one _⟩,v,hv⟩
  exact a.norm_le_one

theorem isometry_corner_unitary (p : AlgebraProjection M) (v : Algebra M)
    (hv : star v*v=1) (hvp : v*star v=p.val) (u : unitary (Algebra M)) :
    star (v*u.val*star v)*(v*u.val*star v)=p.val ∧
      (v*u.val*star v)*star (v*u.val*star v)=p.val := by
  have hs : star (v*u.val*star v)=v*star u.val*star v := by
    simp only [star_mul,star_star,mul_assoc]
  rw [hs]
  constructor
  · calc
      _ = v*(star u.val*(star v*v)*u.val)*star v := by simp only [mul_assoc]
      _ = _ := by rw [hv,mul_one,u.property.1,mul_one,hvp]
  · calc
      _ = v*(u.val*(star v*v)*star u.val)*star v := by simp only [mul_assoc]
      _ = _ := by rw [hv,mul_one,u.property.2,mul_one,hvp]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerPullbackVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithful vector states implementing the corner pullbacks

Pulling a normalized corner state back by an isometry gives a normalized
faithful vector state on the original represented factor. This avoids an
extra representation assumption in the corner homogeneity application.
-/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem isometry_sandwich_cancel (v : Algebra M) (hv : star v*v=1) (a : Algebra M) :
    star v*(v*a*star v)*v=a := by
  calc
    _ = (star v*v)*a*(star v*v) := by simp only [mul_assoc]
    _ = a := by rw [hv,one_mul,mul_one]

theorem isometry_pullback_vector_separating (v : Algebra M) (hv : star v*v=1)
    (ξ : H) (hξ : Function.Injective (algebraVectorMap M ξ)) :
    Function.Injective (algebraVectorMap M ((star v).val ξ)) := by
  intro a b hab
  have hh : (v*a*star v).val ξ=(v*b*star v).val ξ :=
    congrArg v.val hab
  have he : v*a*star v=v*b*star v := hξ hh
  have hf := congrArg (fun x : Algebra M => star v*x*v) he
  simpa only [isometry_sandwich_cancel v hv] using hf

theorem normalized_isometry_pullback_separating
    (v : Algebra M) (hv : star v*v=1) (ξ : H)
    (hξ : Function.Injective (algebraVectorMap M ξ))
    (hne : (star v).val ξ≠0) :
    Function.Injective (algebraVectorMap M (normalize ((star v).val ξ))) := by
  have hinj := isometry_pullback_vector_separating v hv ξ hξ
  intro a b hab
  apply hinj
  change a.val (‖(star v).val ξ‖⁻¹ • (star v).val ξ) =
    b.val (‖(star v).val ξ‖⁻¹ • (star v).val ξ) at hab
  rw [ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower] at hab
  exact smul_right_injective H (inv_ne_zero (norm_ne_zero_iff.mpr hne)) hab

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerHomogeneityTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transferring a norm comparison back into a projection corner

The transfer loses no norm: a unitary comparison of the pulled-back
functionals is exactly the comparison of the corresponding corner
functionals. Existence of the comparison unitary is a separate theorem.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem corner_unitary_comparison_norm (φ ψ : A →L[ℂ] ℂ)
    (p v : A) (hp : IsStarProjection p) (hv : star v*v=1)
    (hvp : v*star v=p) (hnorm : ‖v‖ ≤ 1)
    (hψ : cornerFunctional ψ p=ψ) (u : unitary A) :
    ‖sandwichFunctional φ (v*u.val*star v)-ψ‖ =
      ‖sandwichFunctional (sandwichFunctional φ (star v)) u.val -
        sandwichFunctional ψ (star v)‖ := by
  let f := sandwichFunctional (sandwichFunctional φ (star v)) u.val -
    sandwichFunctional ψ (star v)
  have he : sandwichFunctional f v = sandwichFunctional φ (v*u.val*star v)-ψ := by
    dsimp only [f]
    rw [sandwichFunctional_sub,sandwichFunctional_comp,sandwichFunctional_comp,
      sandwichFunctional_comp,hvp,sandwichFunctional_projection _ _ hp,hψ]
  rw [← he]
  exact sandwichFunctional_isometry_norm f v hv hnorm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerHomogeneityApplication
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The exact corner specialization of state homogeneity

Connes--Størmer, J. Funct. Anal. 28 (1978), 187--196, states norm
transitivity of inner automorphisms on faithful normal states of a type
III₁ factor. Its vector-state special case gives the corner application formalized here.
-/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem vectorCornerState_supported (p : AlgebraProjection M) (ξ : H) :
    cornerFunctional (vectorCornerState p ξ) p.val=vectorCornerState p ξ := by
  ext a
  change (projectionVectorWeight p ξ)⁻¹ •
      (vectorFunctional (p.val.val ξ)) (p.val*a*p.val) =
    (projectionVectorWeight p ξ)⁻¹ • (vectorFunctional (p.val.val ξ)) a
  congr 1
  have h := congrArg (fun f : Algebra M →L[ℂ] ℂ => f a)
    (cornerFunctional_idempotent (vectorFunctional ξ) p.val p.property)
  rw [cornerFunctional_vectorFunctional p] at h
  exact h

theorem TypeIIIFactor.corner_comparison_of_vector_state_homogeneity_oai
    [TopologicalSpace.SeparableSpace H] (hM : TypeIIIFactor M)
    (hhom : FaithfulVectorStateHomogeneity M) (p : AlgebraProjection M)
    (hp : p.val≠0) (ξ ζ : H)
    (hξ : Function.Injective (algebraVectorMap M ξ))
    (hζ : Function.Injective (algebraVectorMap M ζ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : Algebra M, star w*w=p.val ∧ w*star w=p.val ∧
      ‖sandwichFunctional (vectorCornerState p ξ) w-vectorCornerState p ζ‖ < ε := by
  obtain ⟨v,hv,hvp⟩ := hM.exists_isometry_onto_projection p.val p.property hp
  have hnξ : (star v).val ξ≠0 := by
    intro hz
    have he := isometry_pullback_norm_sq p v hvp ξ
    rw [hz,norm_zero,zero_pow (by decide)] at he
    exact (ne_of_gt (projectionVectorWeight_pos p ξ hξ hp)) he.symm
  have hnζ : (star v).val ζ≠0 := by
    intro hz
    have he := isometry_pullback_norm_sq p v hvp ζ
    rw [hz,norm_zero,zero_pow (by decide)] at he
    exact (ne_of_gt (projectionVectorWeight_pos p ζ hζ hp)) he.symm
  obtain ⟨u,hu⟩ := hhom (normalize ((star v).val ξ)) (normalize ((star v).val ζ))
    (norm_normalize hnξ) (norm_normalize hnζ)
    (normalized_isometry_pullback_separating v hv ξ hξ hnξ)
    (normalized_isometry_pullback_separating v hv ζ hζ hnζ) ε hε
  have hw := isometry_corner_unitary p v hv hvp u
  refine ⟨v*u.val*star v,hw.1,hw.2,?_⟩
  rw [corner_unitary_comparison_norm _ _ p.val v p.property hv hvp
    (isometry_norm_le_one v hv) (vectorCornerState_supported p ζ) u,
    vectorCornerState_pullback p v hv hvp ξ,vectorCornerState_pullback p v hv hvp ζ]
  exact hu

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.TypeIIIFactor.corner_comparison_of_vector_state_homogeneity_oai.{u_1} := @OAI.KadisonKastler.TypeIIIFactor.corner_comparison_of_vector_state_homogeneity_oai.{u_1}
