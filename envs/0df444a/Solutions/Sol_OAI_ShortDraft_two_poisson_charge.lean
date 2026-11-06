-- Prove2me | solution 1 for OAI.ShortDraft.two_poisson_charge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:03:04.131857+00:00
-- url     : https://prove2.me/submissions/dfcc355f-49c9-40d5-8a96-8a9f346434af

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

set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.ShortDraft
namespace OAI.ShortDraft
theorem _root_.solution
    (R R' b0 B F A t ge Δ : ℝ)
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hF : 1 ≤ F) (hA : 1 ≤ A)
    (ht : 0 ≤ t) (hge : 0 ≤ ge)
    (hb0B : b0 ≤ B)
    (hR' : R' ≤ R * b0 * t * ge)
    (hΔ : Δ = B * F * A * t * ge) : R' ≤ R * Δ := by
  calc
    R' ≤ R * b0 * t * ge := hR'
    _ ≤ R * B * t * ge := by gcongr
    _ ≤ R * (B * F * A * t * ge) := by
      have hBA : B ≤ B * F * A := by
        have hBF : B ≤ B * F := by nlinarith
        have hBFA : B * F ≤ B * F * A := by
          nlinarith [mul_nonneg (mul_nonneg hB (le_trans zero_le_one hF))
            (sub_nonneg.mpr hA)]
        exact hBF.trans hBFA
      nlinarith [mul_nonneg (mul_nonneg hR (sub_nonneg.mpr hBA))
        (mul_nonneg ht hge)]
    _ = R * Δ := by rw [hΔ]
end OAI.ShortDraft
