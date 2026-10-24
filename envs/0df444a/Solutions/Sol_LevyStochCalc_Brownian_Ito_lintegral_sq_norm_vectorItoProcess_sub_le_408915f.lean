-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_sq_norm_vectorItoProcess_sub_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:34:24.804672+00:00
-- url     : https://prove2.me/submissions/8ee9be61-b872-49de-bed5-c69cb263301f

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_DenseCountable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Filtration
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Indistinguishable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LeftLimWithin
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Martingale
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_StoppedProcess
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Topology
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Upcrossing
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_Chaining
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_CoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_IsKolmogorovProcess
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsov
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsovInequality
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_LimitModification
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_BrownianMotion
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_Moment
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_StochasticProcesses
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Cadlag
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Predictable
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_Basic
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_SimpleProcess
import Definitions.Def_KLS408915f_KolmogorovExtension4_CompactSystem
import Definitions.Def_KLS408915f_KolmogorovExtension4_KolmogorovExtension
import Definitions.Def_KLS408915f_KolmogorovExtension4_RegularContent
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_AugmentedFiltration
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraProduct
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentLintegral
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoIncrementMomentRestrict
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionApi
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoQuadVarSum
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoTruncate
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoVersionExists
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimIto
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardBieleckiNorm
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardIntegrandBounds
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardIntegrandFrozen
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputModification
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputStepDiff
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardOutputWeighting
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiEDist
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceBieleckiQuotient
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardSpaceDiscrete
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardStepMap
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardStochasticLipschitz
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_Setting
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_CadlagModification
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Compensated
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedApprox
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityDyadic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityLimit
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkApprox
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkSum
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRectSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRefinement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityShifted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityStepIntegral
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityTruncation
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDiff
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleAdapted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedProcessQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepWeight
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_PoissonSuperposition
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Augmentation
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ProgressiveCadlag
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.SetSemiring
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_lt_top_of_bound_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_sq_enorm_finsetSum_le_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open MeasureTheory
/-- The integral of a jointly measurable function over a fixed set is measurable in the
parameter. -/
theorem LevyStochCalc.measurable_setIntegral {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (s : Set ℝ) :
    Measurable fun ω => ∫ t in s, f ω t ∂volume :=
  (MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict s) hf.stronglyMeasurable).measurable
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section PiNorm
variable {n : ℕ}
/-- The square of the supremum norm on `Fin n → ℝ` is at most the sum of the squared
coordinates. -/
theorem LevyStochCalc.Brownian.Ito.sq_norm_pi_le_sum_sq (x : Fin n → ℝ) : ‖x‖ ^ 2 ≤ ∑ m, (x m) ^ 2 := by
  have hs : (0 : ℝ) ≤ ∑ m, (x m) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (x j)
  have hle : ‖x‖ ≤ Real.sqrt (∑ m, (x m) ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun m => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ m))
  calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ m, (x m) ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hle 2
    _ = ∑ m, (x m) ^ 2 := Real.sq_sqrt hs
end PiNorm
section VectorProcess
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
/-- Each entry's Itô integral is measurable for the σ-algebra at its time. -/
theorem LevyStochCalc.Brownian.Ito.stronglyMeasurable_coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) :
    StronglyMeasurable[ℱ t] (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) :=
  stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k)
    (hHs m k) t
/-- Each entry's Itô integral is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) :
    Measurable (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) :=
  ((stronglyMeasurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t).mono (ℱ.le t)).measurable
/-- The martingale part of a coordinate is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_vectorItoMartingale (m : Fin n) (t : ℝ) :
    Measurable (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m t) :=
  Finset.measurable_sum _ fun k _ => measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t
/-- A vector Itô process is measurable in the sample point at each time. -/
theorem LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess {X₀ : Ω → Fin n → ℝ}
    (hX₀ : ∀ m, Measurable fun ω => X₀ ω m) {bdrift : Fin n → Ω → ℝ → ℝ}
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) (t : ℝ) :
    Measurable (vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t) := by
  refine measurable_pi_lambda _ fun m => ?_
  exact ((hX₀ m).add (measurable_setIntegral (hbm m) _)).add
    (measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs m t)
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
end VectorProcess
end
end
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLinear.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
/-- The squared extended norm of a real number is the extended real of its square. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq (z : ℝ) : (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) := by
  rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from (ofReal_norm z).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
section Energy
variable {H₁ H₂ : Ω → ℝ → ℝ}
/-- The energy density of an integrand is measurable in the sample point. -/
theorem LevyStochCalc.Brownian.Ito.measurable_energyDensity (hm : Measurable (Function.uncurry H₁)) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
  have hf : Measurable fun p : Ω × ℝ => (‖H₁ p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    (((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2)
  exact hf.lintegral_prod_right'
/-- The squared extended norm of a difference is dominated by twice the sum of the squares. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul (x y : ℝ) :
    (‖x - y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x + y)])
/-- The squared extended norm of a sum is dominated by twice the sum of the squares. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - y)])
end Energy
end
end
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoTruncate.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open MeasureTheory
open scoped NNReal ENNReal Topology
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open MeasureTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
section Difference
open LevyStochCalc.Brownian.Multidim
variable {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
/-- The squared norm of a real vector is at most the sum of its squared coordinates, in `ℝ≥0∞`. -/
theorem LevyStochCalc.Brownian.Ito.sq_enorm_pi_le_sum {m : ℕ} (x : Fin m → ℝ) :
    (‖x‖₊ : ℝ≥0∞) ^ 2 ≤ ∑ p, (‖x p‖₊ : ℝ≥0∞) ^ 2 := by
  have hnn : ‖x‖₊ ^ 2 ≤ ∑ p, ‖x p‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    simpa [Real.norm_eq_abs, sq_abs] using sq_norm_pi_le_sum_sq x
  calc (‖x‖₊ : ℝ≥0∞) ^ 2 = ((‖x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((∑ p, ‖x p‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hnn
    _ = ∑ p, (‖x p‖₊ : ℝ≥0∞) ^ 2 := by push_cast; ring
end Difference
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoProcessDiff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
section Diff
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
omit [IsProbabilityMeasure P] in
/-- A path with finite energy on a window is integrable there, almost surely. -/
theorem LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top {b : Ω → ℝ → ℝ}
    (hbm : Measurable (Function.uncurry b)) {t : ℝ}
    (hbq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, IntegrableOn (b ω) (Set.Icc (0 : ℝ) t) volume := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  filter_upwards [MeasureTheory.ae_lt_top (measurable_energyDensity hbm t) hbq.ne] with ω hω
  exact (LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
    (Measurable.of_uncurry_left hbm) hω).integrable (by norm_num)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
/-- **The `L²` distance between two vector Itô processes with the same initial value.** -/
theorem solution
    {H₁ H₂ : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm₁ : ∀ p k, Measurable (Function.uncurry (H₁ p k)))
    (hp₁ : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H₁ p k))
    (hq₁ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ p k, Measurable (Function.uncurry (H₂ p k)))
    (hp₂ : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H₂ p k))
    (hq₂ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b₁ b₂ : Fin n → Ω → ℝ → ℝ}
    (hbm₁ : ∀ p, Measurable (Function.uncurry (b₁ p)))
    (hbm₂ : ∀ p, Measurable (Function.uncurry (b₂ p)))
    {t : ℝ} (ht : 0 < t)
    (hbq₁ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hbq₂ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ p : Fin n, (2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
  classical
  have hXm₁ : Measurable (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t) :=
    LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ hX₀ hbm₁ t
  have hXm₂ : Measurable (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t) :=
    LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ hX₀ hbm₂ t
  have hcoordm : ∀ p : Fin n, Measurable fun ω =>
      (‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p‖₊ : ℝ≥0∞) ^ 2 := by
    intro p
    exact ((((measurable_pi_apply p).comp hXm₂).sub
      ((measurable_pi_apply p).comp hXm₁)).nnnorm.coe_nnreal_ennreal).pow_const 2
  -- reduce to the coordinates
  have hred : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ p : Fin n, ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    rw [← MeasureTheory.lintegral_finsetSum _ fun p _ => hcoordm p]
    refine MeasureTheory.lintegral_mono fun ω => ?_
    simpa using LevyStochCalc.Brownian.Ito.sq_enorm_pi_le_sum (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω
      - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω)
  refine hred.trans (Finset.sum_le_sum fun p _ => ?_)
  -- split the coordinate difference into a drift part and a martingale part
  have hsplit : ∀ ω : Ω,
      LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p
      = (((∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
            - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume))
        + (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
          - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω) := by
    intro ω
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess]
    ring
  have hDbm : Measurable fun ω : Ω =>
      (‖(∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
        - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume‖₊ : ℝ≥0∞) ^ 2 :=
    ((((LevyStochCalc.measurable_setIntegral (hbm₂ p) _).sub
      (LevyStochCalc.measurable_setIntegral (hbm₁ p) _)).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hDmm : Measurable fun ω : Ω =>
      (‖LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
        - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω‖₊ : ℝ≥0∞) ^ 2 :=
    ((((LevyStochCalc.Brownian.Ito.measurable_vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t).sub
      (LevyStochCalc.Brownian.Ito.measurable_vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t)).nnnorm
        ).coe_nnreal_ennreal).pow_const 2
  have hsum : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * ∫⁻ ω, (‖(∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
            - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P
        + 2 * ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
            - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    have hmono : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω p
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω p‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, (2 * (‖(∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
              - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume‖₊ : ℝ≥0∞) ^ 2
            + 2 * (‖LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
              - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
      refine MeasureTheory.lintegral_mono fun ω => ?_
      rw [hsplit ω]
      have := LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul
        ((∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
          - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume)
        (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
          - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω)
      refine this.trans (le_of_eq ?_)
      rw [mul_add]
    refine hmono.trans (le_of_eq ?_)
    rw [MeasureTheory.lintegral_add_left (hDbm.const_mul 2),
      MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤),
      MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
  refine hsum.trans (add_le_add ?_ ?_)
  · -- the drift part, by Cauchy–Schwarz
    have hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound_408915f (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _)
        (hbm₂ p) (hbm₁ p) (hbq₂ p) (hbq₁ p) t ht
    have heq : ∫⁻ ω, (‖(∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
          - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) t, (b₂ p ω s - b₁ p ω s) ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hbm₁ p) (hbq₁ p t ht),
        LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hbm₂ p) (hbq₂ p t ht)] with ω h1 h2
      rw [MeasureTheory.integral_sub h2 h1]
    rw [heq]
    exact mul_le_mul' le_rfl
      (LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le
        ((hbm₂ p).sub (hbm₁ p)) ht.le hfin)
  · -- the martingale part, by the difference isometry
    have hM : ∀ ω : Ω, LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
        - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω
        = ∑ k : Fin d, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H₂ hm₂ hp₂ hq₂ p k t ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H₁ hm₁ hp₁ hq₁ p k t ω) := by
      intro ω
      rw [LevyStochCalc.Brownian.Ito.vectorItoMartingale, LevyStochCalc.Brownian.Ito.vectorItoMartingale, ← Finset.sum_sub_distrib]
    have hkm : ∀ k : Fin d, Measurable fun ω : Ω =>
        (‖LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H₂ hm₂ hp₂ hq₂ p k t ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H₁ hm₁ hp₁ hq₁ p k t ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro k
      exact ((((LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H₂ hm₂ hp₂ hq₂ p k t).sub
        (LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H₁ hm₁ hp₁ hq₁ p k t)).nnnorm
          ).coe_nnreal_ennreal).pow_const 2
    have hstep : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
          - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ (d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω,
            (‖LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H₂ hm₂ hp₂ hq₂ p k t ω
              - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H₁ hm₁ hp₁ hq₁ p k t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      rw [← MeasureTheory.lintegral_finsetSum _ fun k _ => hkm k,
        ← MeasureTheory.lintegral_const_mul' _ _ (by simp : (d : ℝ≥0∞) ≠ ⊤)]
      refine MeasureTheory.lintegral_mono fun ω => ?_
      rw [hM ω]
      exact LevyStochCalc.Brownian.Ito.sq_enorm_finsetSum_le_408915f _
    refine mul_le_mul' le_rfl (hstep.trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun k _ => ?_)))
    exact le_of_eq (LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
      (H₂ p k) (H₁ p k) (hm₂ p k) (hm₁ p k) (hp₂ p k) (hp₁ p k) (hq₂ p k) (hq₁ p k) ht)
