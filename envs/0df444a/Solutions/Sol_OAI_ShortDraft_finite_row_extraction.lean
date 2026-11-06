-- Prove2me | solution 1 for OAI.ShortDraft.finite_row_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:28:33.554197+00:00
-- url     : https://prove2.me/submissions/f2c807e0-46dc-4225-a842-d150c052a635

import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Covering.Quotient
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Order.PiLex
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.RingTheory.Multiplicity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Multiset.Interval
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic.Group
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
section
namespace OAI
open scoped BigOperators
namespace ShortDraft
private lemma square_le_two_squares {x y e : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (he : 0 ≤ e) (h : x ≤ y + e) :
    x ^ 2 ≤ 2 * y ^ 2 + 2 * e ^ 2 := by
  have h₁ : 0 ≤ y + e - x := sub_nonneg.mpr h
  have h₂ : 0 ≤ y + e + x := by nlinarith
  have h₃ := mul_nonneg h₁ h₂
  have h₄ := sq_nonneg (y - e)
  nlinarith
end ShortDraft
open MulChar AddChar
namespace ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end ShortDraftLocal
end OAI
end

set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.ShortDraft
namespace OAI.ShortDraft
theorem _root_.solution {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (a : α → ℝ) (a₀ error bound : ℝ)
    (ha₀ : 0 ≤ a₀) (ha : ∀ u, 0 ≤ a u) (herror : 0 ≤ error)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes, a₀ ≤ a (row p) + error)
    (hmean : (∑ u ∈ rows, (a u) ^ 2) ≤ bound) :
    (primes.card : ℝ) * a₀ ^ 2 ≤
      2 * bound + 2 * (primes.card : ℝ) * error ^ 2 := by
  have hselected : (∑ p ∈ primes, (a (row p)) ^ 2) ≤ bound := by
    calc
      (∑ p ∈ primes, (a (row p)) ^ 2) =
          ∑ u ∈ primes.image row, (a u) ^ 2 := by
            rw [Finset.sum_image hinj]
      _ ≤ ∑ u ∈ rows, (a u) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hrows (by
          intro u _ _
          positivity)
      _ ≤ bound := hmean
  have hpoint (p : β) (hp : p ∈ primes) :
      a₀ ^ 2 ≤ 2 * (a (row p)) ^ 2 + 2 * error ^ 2 :=
    square_le_two_squares ha₀ (ha _) herror (happrox p hp)
  have hsum :
      (∑ p ∈ primes, a₀ ^ 2) ≤
        ∑ p ∈ primes, (2 * (a (row p)) ^ 2 + 2 * error ^ 2) :=
    Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith
end OAI.ShortDraft
