-- Prove2me | solution 1 for OAI.KadisonKastler.patched_vector_state_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:25:13.931831+00:00
-- url     : https://prove2.me/submissions/bea0eee5-841a-457a-9ef3-d80d8e88d42e

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
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
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
import Definitions.Def_Q260K033

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionNormDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Squared-norm decompositions for nested projections -/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projection_complement_inner {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    inner ℂ (P x) ((1 - P) x) = 0 := by
  have hs : P.adjoint = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hP.isSelfAdjoint.star_eq
  have hz : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP.isIdempotentElem.eq, sub_self]
  rw [← P.adjoint_inner_right, hs]
  change inner ℂ x ((P * (1 - P)) x) = 0
  rw [hz, zero_apply, inner_zero_right]

theorem projection_norm_sq_decomposition {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (x : H) :
    ‖P x‖ ^ 2 + ‖(1 - P) x‖ ^ 2 = ‖x‖ ^ 2 := by
  calc
    _ = ‖P x + (1 - P) x‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
          (projection_complement_inner hP x)).symm
    _ = ‖x‖ ^ 2 := by simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoCornerStateNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Combining state comparisons on complementary corners

A functional centralizing a projection is the sum of its two compressed
functionals. Comparing normalized corner states and their scalar weights
therefore controls the norm distance of the original states.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem functional_eq_two_corners (φ : A →L[ℂ] ℂ) (p : A)
    (hp : IsStarProjection p) (hcentral : ∀ a : A, φ (p*a) = φ (a*p)) :
    φ = cornerFunctional φ p + cornerFunctional φ (1-p) := by
  ext a
  have hpp : φ (p*a*p) = φ (p*a) := by
    have h := hcentral (p*a)
    rw [← mul_assoc,hp.isIdempotentElem.eq] at h
    exact h.symm
  have he : (1-p)*a*(1-p) = a-p*a-a*p+p*a*p := by noncomm_ring
  change φ a = φ (p*a*p) + φ ((1-p)*a*(1-p))
  rw [he,map_add,map_sub,map_sub,hpp,hcentral]
  abel

theorem state_mixture_norm_sub_le
    (φ₀ φ₁ ψ₀ ψ₁ : A →L[ℂ] ℂ) (a b δ : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hψ₀ : ‖ψ₀‖ ≤ 1) (hψ₁ : ‖ψ₁‖ ≤ 1)
    (h₀ : ‖φ₀-ψ₀‖ ≤ δ) (h₁ : ‖φ₁-ψ₁‖ ≤ δ) :
    ‖(a • φ₀ + (1-a) • φ₁) - (b • ψ₀ + (1-b) • ψ₁)‖ ≤
      δ + 2*|a-b| := by
  have he : (a • φ₀ + (1-a) • φ₁) - (b • ψ₀ + (1-b) • ψ₁) =
      (a • (φ₀-ψ₀) + (1-a) • (φ₁-ψ₁)) + (a-b) • (ψ₀-ψ₁) := by module
  have hψ : ‖ψ₀-ψ₁‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  rw [he]
  calc
    _ ≤ ‖a • (φ₀-ψ₀) + (1-a) • (φ₁-ψ₁)‖ + ‖(a-b) • (ψ₀-ψ₁)‖ := norm_add_le _ _
    _ ≤ (‖a • (φ₀-ψ₀)‖ + ‖(1-a) • (φ₁-ψ₁)‖) + ‖(a-b) • (ψ₀-ψ₁)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = (a * ‖φ₀-ψ₀‖ + (1-a) * ‖φ₁-ψ₁‖) + |a-b| * ‖ψ₀-ψ₁‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,
        abs_of_nonneg (sub_nonneg.mpr ha1)]
    _ ≤ (a*δ+(1-a)*δ)+|a-b| * 2 := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left h₀ ha)
          (mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr ha1)))
        (mul_le_mul_of_nonneg_left hψ (abs_nonneg _))
    _ = _ := by ring

theorem twoCorner_state_norm_le
    (φ ψ φ₀ φ₁ ψ₀ ψ₁ : A →L[ℂ] ℂ) (p : A)
    (hp : IsStarProjection p)
    (hφ : ∀ x : A, φ (p*x) = φ (x*p))
    (hψ : ∀ x : A, ψ (p*x) = ψ (x*p))
    (a b δ : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hφ₀ : cornerFunctional φ p = a • φ₀)
    (hφ₁ : cornerFunctional φ (1-p) = (1-a) • φ₁)
    (hψ₀ : cornerFunctional ψ p = b • ψ₀)
    (hψ₁ : cornerFunctional ψ (1-p) = (1-b) • ψ₁)
    (hψ₀norm : ‖ψ₀‖ ≤ 1) (hψ₁norm : ‖ψ₁‖ ≤ 1)
    (h₀ : ‖φ₀-ψ₀‖ ≤ δ) (h₁ : ‖φ₁-ψ₁‖ ≤ δ) :
    ‖φ-ψ‖ ≤ δ+2*|a-b| := by
  conv_lhs =>
    arg 1
    rw [functional_eq_two_corners φ p hp hφ,functional_eq_two_corners ψ p hp hψ]
  rw [hφ₀,hφ₁,hψ₀,hψ₁]
  exact state_mixture_norm_sub_le φ₀ φ₁ ψ₀ ψ₁ a b δ ha ha1 hψ₀norm hψ₁norm h₀ h₁

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ComplementaryCornerUnitary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Joining unitaries on complementary projection corners

The two corner conjugations used in state homogeneity join to one actual
unitary. Its two compressions remain exactly the specified corner maps.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem cornerUnitary_supports (p : AlgebraProjection M)
    (u : Algebra M) (hu : star u*u = p.val) (hu' : u*star u = p.val) :
    p.val*u = u ∧ u*p.val = u := by
  let a : PartialIsometry M := ⟨p,u,hu⟩
  have hat : a.target = p := Subtype.ext hu'
  exact ⟨hat ▸ a.target_mul,a.mul_support⟩

theorem complementaryCornerUnitary_compressions (p : AlgebraProjection M)
    (u v : Algebra M) (hu : star u*u = p.val) (hu' : u*star u = p.val)
    (hv : star v*v = 1-p.val) (hv' : v*star v = 1-p.val) :
    p.val*(u+v) = u ∧ (u+v)*p.val = u ∧
      (1-p.val)*(u+v) = v ∧ (u+v)*(1-p.val) = v := by
  obtain ⟨hpu,hup⟩ := cornerUnitary_supports p u hu hu'
  obtain ⟨hqv,hvq⟩ := cornerUnitary_supports ⟨1-p.val,p.property.one_sub⟩ v hv hv'
  change (1-p.val)*v=v at hqv
  change v*(1-p.val)=v at hvq
  have hpv : p.val*v=0 := by rw [sub_mul,one_mul] at hqv; exact sub_eq_self.mp hqv
  have hvp : v*p.val=0 := by rw [mul_sub,mul_one] at hvq; exact sub_eq_self.mp hvq
  have hqu : (1-p.val)*u=0 := by rw [sub_mul,one_mul,hpu,sub_self]
  have huq : u*(1-p.val)=0 := by rw [mul_sub,mul_one,hup,sub_self]
  simp only [mul_add,add_mul,hpu,hup,hpv,hvp,hqu,huq,hqv,hvq,zero_add,add_zero]
  trivial

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerStateWeights
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem projectionVectorWeight_add_complement (p : AlgebraProjection M) (ξ : H) :
    projectionVectorWeight p ξ +
      projectionVectorWeight ⟨1-p.val,p.property.one_sub⟩ ξ = ‖ξ‖^2 := by
  exact projection_norm_sq_decomposition
    (p.property.map M.toStarSubalgebra.subtype) ξ

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

theorem projectionVectorWeight_mem_Ioo (p : AlgebraProjection M) (ξ : H)
    (hξ : Function.Injective (algebraVectorMap M ξ)) (hunit : ‖ξ‖ = 1)
    (hp0 : p.val ≠ 0) (hp1 : p.val ≠ 1) :
    0 < projectionVectorWeight p ξ ∧ projectionVectorWeight p ξ < 1 := by
  have hp := projectionVectorWeight_pos p ξ hξ hp0
  have hq := projectionVectorWeight_pos ⟨1-p.val,p.property.one_sub⟩ ξ hξ
    (sub_ne_zero.mpr hp1.symm)
  have he := projectionVectorWeight_add_complement p ξ
  rw [hunit] at he
  exact ⟨hp,by linarith⟩

theorem vectorCornerState_norm_le (p : AlgebraProjection M) (ξ : H)
    (hp : 0 < projectionVectorWeight p ξ) : ‖vectorCornerState p ξ‖ ≤ 1 := by
  rw [vectorCornerState,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ (projectionVectorWeight p ξ)⁻¹ * ‖p.val.val ξ‖^2 :=
      mul_le_mul_of_nonneg_left (vectorFunctional_norm_le _) (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

theorem weight_smul_vectorCornerState (p : AlgebraProjection M) (ξ : H)
    (hp : 0 < projectionVectorWeight p ξ) :
    projectionVectorWeight p ξ • vectorCornerState p ξ = vectorFunctional (p.val.val ξ) := by
  rw [vectorCornerState,smul_smul,mul_inv_cancel₀ hp.ne',one_smul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerStateConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A single state comparison from two corner conjugations

Normalized corner estimates combine under the unitary formed from
two complementary corner unitaries. The resulting state comparison
is bounded by the sum of the corner errors.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem sandwichFunctional_centralizes (φ : A →L[ℂ] ℂ) (p u : A)
    (hp : IsStarProjection p) (hpu : p*u=u*p)
    (hφ : ∀ x : A, φ (p*x)=φ (x*p)) :
    ∀ x : A, sandwichFunctional φ u (p*x)=sandwichFunctional φ u (x*p) := by
  have hs : star u*p=p*star u := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpu
  intro x
  change φ (star u*(p*x)*u)=φ (star u*(x*p)*u)
  have hl : star u*(p*x)*u=p*(star u*x*u) := by
    rw [← mul_assoc (star u) p,hs]
    simp only [mul_assoc]
  have hr : star u*(x*p)*u=(star u*x*u)*p := by
    rw [mul_assoc (star u) (x*p),mul_assoc x p,hpu]
    simp only [mul_assoc]
  rw [hl,hr,hφ]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem sandwichFunctional_vectorFunctional (ξ : H) (u : Algebra M) :
    sandwichFunctional (vectorFunctional ξ) u = vectorFunctional (u.val ξ) := by
  ext x
  change inner ℂ ξ (u.val.adjoint (x.val (u.val ξ))) =
    inner ℂ (u.val ξ) (x.val (u.val ξ))
  exact u.val.adjoint_inner_right _ _

theorem cornerFunctional_patched_vector (p : AlgebraProjection M)
    (u v : Algebra M) (hu : star u*u=p.val) (hu' : u*star u=p.val)
    (hv : star v*v=1-p.val) (hv' : v*star v=1-p.val) (ξ : H) :
    cornerFunctional (vectorFunctional ((u+v).val ξ)) p.val =
        sandwichFunctional (vectorFunctional ξ) u ∧
      cornerFunctional (vectorFunctional ((u+v).val ξ)) (1-p.val) =
        sandwichFunctional (vectorFunctional ξ) v := by
  obtain ⟨hpu,_,hqv,_⟩ :=
    complementaryCornerUnitary_compressions p u v hu hu' hv hv'
  constructor
  · rw [cornerFunctional_vectorFunctional p, sandwichFunctional_vectorFunctional]
    congr 1
    exact congrArg (fun a : Algebra M => a.val ξ) hpu
  · rw [cornerFunctional_vectorFunctional (⟨1-p.val,p.property.one_sub⟩ : AlgebraProjection M),
      sandwichFunctional_vectorFunctional]
    congr 1
    exact congrArg (fun a : Algebra M => a.val ξ) hqv

theorem patched_vector_state_centralizes (p : AlgebraProjection M)
    (u v : Algebra M) (hu : star u*u=p.val) (hu' : u*star u=p.val)
    (hv : star v*v=1-p.val) (hv' : v*star v=1-p.val) (ξ : H)
    (hφ : ∀ x : Algebra M, vectorFunctional ξ (p.val*x)=vectorFunctional ξ (x*p.val)) :
    ∀ x : Algebra M, vectorFunctional ((u+v).val ξ) (p.val*x)=
      vectorFunctional ((u+v).val ξ) (x*p.val) := by
  have hc := complementaryCornerUnitary_compressions p u v hu hu' hv hv'
  rw [← sandwichFunctional_vectorFunctional]
  exact sandwichFunctional_centralizes _ _ _ p.property (hc.1.trans hc.2.1.symm) hφ

/-- Once each corner has a normalized comparison, their sum is the required
unitary comparison on the whole algebra. -/
theorem patched_vector_state_norm_le_oai (p : AlgebraProjection M)
    (u v : Algebra M) (hu : star u*u=p.val) (hu' : u*star u=p.val)
    (hv : star v*v=1-p.val) (hv' : v*star v=1-p.val) (ξ ζ : H)
    (hξ : Function.Injective (algebraVectorMap M ξ)) (hnξ : ‖ξ‖=1)
    (hζ : Function.Injective (algebraVectorMap M ζ)) (hnζ : ‖ζ‖=1)
    (hp0 : p.val≠0) (hp1 : p.val≠1)
    (hcξ : ∀ x : Algebra M, vectorFunctional ξ (p.val*x)=vectorFunctional ξ (x*p.val))
    (hcζ : ∀ x : Algebra M, vectorFunctional ζ (p.val*x)=vectorFunctional ζ (x*p.val))
    (δ : ℝ)
    (h₀ : ‖(projectionVectorWeight p ξ)⁻¹ • sandwichFunctional (vectorFunctional ξ) u -
      vectorCornerState p ζ‖ ≤ δ)
    (h₁ : ‖(1-projectionVectorWeight p ξ)⁻¹ • sandwichFunctional (vectorFunctional ξ) v -
      vectorCornerState ⟨1-p.val,p.property.one_sub⟩ ζ‖ ≤ δ) :
    ‖vectorFunctional (M := M) ((u+v).val ξ)-vectorFunctional ζ‖ ≤
      δ+2*|projectionVectorWeight p ξ-projectionVectorWeight p ζ| := by
  have ha := projectionVectorWeight_mem_Ioo p ξ hξ hnξ hp0 hp1
  have hb := projectionVectorWeight_mem_Ioo p ζ hζ hnζ hp0 hp1
  have hbq : 0 < projectionVectorWeight ⟨1-p.val,p.property.one_sub⟩ ζ :=
    projectionVectorWeight_pos _ ζ hζ (sub_ne_zero.mpr hp1.symm)
  have hbqeq : 1-projectionVectorWeight p ζ =
      projectionVectorWeight ⟨1-p.val,p.property.one_sub⟩ ζ := by
    have he := projectionVectorWeight_add_complement p ζ
    rw [hnζ] at he
    linarith
  obtain ⟨hcomp₀,hcomp₁⟩ := cornerFunctional_patched_vector p u v hu hu' hv hv' ξ
  apply twoCorner_state_norm_le
    (vectorFunctional ((u+v).val ξ)) (vectorFunctional ζ)
    ((projectionVectorWeight p ξ)⁻¹ • sandwichFunctional (vectorFunctional ξ) u)
    ((1-projectionVectorWeight p ξ)⁻¹ • sandwichFunctional (vectorFunctional ξ) v)
    (vectorCornerState p ζ) (vectorCornerState ⟨1-p.val,p.property.one_sub⟩ ζ)
    p.val p.property
    (patched_vector_state_centralizes p u v hu hu' hv hv' ξ hcξ) hcζ
    (projectionVectorWeight p ξ) (projectionVectorWeight p ζ) δ ha.1.le ha.2.le
  · rw [hcomp₀,smul_smul,mul_inv_cancel₀ ha.1.ne',one_smul]
  · rw [hcomp₁,smul_smul,mul_inv_cancel₀ (sub_pos.mpr ha.2).ne',one_smul]
  · rw [cornerFunctional_vectorFunctional,weight_smul_vectorCornerState p ζ hb.1]
  · rw [cornerFunctional_vectorFunctional (⟨1-p.val,p.property.one_sub⟩ : AlgebraProjection M),
      hbqeq,weight_smul_vectorCornerState _ ζ hbq]
  · exact vectorCornerState_norm_le p ζ hb.1
  · exact vectorCornerState_norm_le _ ζ hbq
  · exact h₀
  · exact h₁

end

end KadisonKastler

end OAI
end

theorem solution.{u_2} : type_of% @OAI.KadisonKastler.patched_vector_state_norm_le_oai.{u_2} := @OAI.KadisonKastler.patched_vector_state_norm_le_oai.{u_2}
