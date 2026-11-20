-- Prove2me | solution 1 for LevyStochCalc.Ito.SecondMoment.mul_setIntegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:33:00.364273+00:00
-- url     : https://prove2.me/submissions/145b2eb8-80fe-4714-b92f-3e6db804d8a7

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Auxiliary lemmas for the second moment of an Itô–Lévy process

The `L²` lemmas behind the expectation form of the quadratic Itô formula: the second moment of a
square-integrable variable as the real part of its energy, the expansion of the square of a sum,
the evaluation of a square-integrable martingale paired against a variable measurable at an
earlier time, and the exchange of a time integral with a pairing. The running integral
`∫_0^s b_r dr` of a drift over a window `[0, T]` is introduced as a jointly measurable function of
the sample point and the time, together with the pathwise identities
`(∫_0^T b)² = 2 ∫_0^T (∫_0^s b) b_s ds` and, for two integrable functions,
`(∫_0^T b)(∫_0^T b') = ∫_0^T ((∫_0^s b) b'_s + b_s (∫_0^s b')) ds`; and the polarised isometry for
the Brownian integral, the expected product of two Brownian integrals at a time being the expected
time integral of the product of their integrands.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Toolkit

end Toolkit

section Running

variable (b : ℝ → Ω → ℝ) (T : ℝ)

variable {b T}

end Running

section Polarised

end Polarised

section PolarisedDrift

theorem _root_.solution {b b' : ℝ → ℝ} {T : ℝ}
    (hb : IntegrableOn b (Set.Icc (0 : ℝ) T)) (hb' : IntegrableOn b' (Set.Icc (0 : ℝ) T)) :
    (∫ s in Set.Icc (0 : ℝ) T, b s) * (∫ s in Set.Icc (0 : ℝ) T, b' s)
      = ∫ s in Set.Icc (0 : ℝ) T,
          ((∫ r in Set.Icc (0 : ℝ) s, b r) * b' s + b s * ∫ r in Set.Icc (0 : ℝ) s, b' r) := by
  set I := Set.Icc (0 : ℝ) T with hI
  set μ := volume.restrict I with hμ
  have hprod : Integrable (fun z : ℝ × ℝ => b z.1 * b' z.2) (μ.prod μ) :=
    Integrable.mul_prod hb hb'
  set S1 : Set (ℝ × ℝ) := {p | p.1 ≤ p.2} with hS1
  set S2 : Set (ℝ × ℝ) := {p | p.2 < p.1} with hS2
  have hS1m : MeasurableSet S1 := measurableSet_le measurable_fst measurable_snd
  have hS2m : MeasurableSet S2 := measurableSet_lt measurable_snd measurable_fst
  set f1 := S1.indicator (fun z : ℝ × ℝ => b z.1 * b' z.2) with hf1
  set f2 := S2.indicator (fun z : ℝ × ℝ => b z.1 * b' z.2) with hf2
  have hi1 : Integrable f1 (μ.prod μ) := hprod.indicator hS1m
  have hi2 : Integrable f2 (μ.prod μ) := hprod.indicator hS2m
  have hsum : (fun z : ℝ × ℝ => b z.1 * b' z.2) = fun z => f1 z + f2 z := by
    funext z
    simp only [hf1, hf2, Set.indicator_apply, hS1, hS2, Set.mem_setOf_eq]
    by_cases h : z.1 ≤ z.2
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  have key1 : ∀ s ∈ I, ∫ r, f1 (r, s) ∂μ = (∫ r in Set.Icc (0 : ℝ) s, b r) * b' s := by
    intro s hs
    have e : (fun r => f1 (r, s)) = (Set.Iic s).indicator (fun r => b r * b' s) := by
      funext r; simp [hf1, hS1, Set.indicator_apply]
    rw [e, integral_indicator measurableSet_Iic, hμ, Measure.restrict_restrict measurableSet_Iic,
      integral_mul_const]
    congr 2
    congr 1
    ext r; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, hI]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hs.2⟩
  have key2 : ∀ s ∈ I, ∫ u, f2 (s, u) ∂μ = b s * ∫ r in Set.Icc (0 : ℝ) s, b' r := by
    intro s hs
    have e : (fun u => f2 (s, u)) = (Set.Iio s).indicator (fun u => b s * b' u) := by
      funext u; simp [hf2, hS2, Set.indicator_apply]
    rw [e, integral_indicator measurableSet_Iio, hμ, Measure.restrict_restrict measurableSet_Iio,
      integral_const_mul, integral_Icc_eq_integral_Ico]
    congr 2
    congr 1
    ext r; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico, hI]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.le.trans hs.2⟩
  have hR : ∫ s in I, ((∫ r in Set.Icc (0 : ℝ) s, b r) * b' s + b s * ∫ r in Set.Icc (0 : ℝ) s, b' r)
      = ∫ s in I, ((∫ r, f1 (r, s) ∂μ) + ∫ u, f2 (s, u) ∂μ) := by
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    rw [key1 s hs, key2 s hs]
  rw [hR, ← integral_prod_mul (μ := μ) (ν := μ) b b', hsum, integral_add hi1 hi2,
    integral_prod_symm f1 hi1, integral_prod f2 hi2]
  rw [← hμ, integral_add hi1.integral_prod_right hi2.integral_prod_left]

end PolarisedDrift

end LevyStochCalc.Ito.SecondMoment
