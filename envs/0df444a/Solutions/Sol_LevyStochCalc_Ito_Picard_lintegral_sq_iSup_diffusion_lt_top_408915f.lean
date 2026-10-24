-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.lintegral_sq_iSup_diffusion_lt_top_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:56:02.426504+00:00
-- url     : https://prove2.me/submissions/7eeef4ff-6c2c-4519-987b-aa93ab617dff

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionApi
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimIto
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardBieleckiNorm
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardContractionEstimate
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardContractionFixedPoint
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardIntegrandBounds
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardIntegrandFrozen
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardLimit
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
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_DoobContinuous
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ProgressiveCadlag
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
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
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
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
import Theorems.Thm_LevyStochCalc_Probability_enorm_dyadicRunMax_408915f
import Theorems.Thm_LevyStochCalc_Probability_lintegral_sq_dyadicRunMax_le_408915f
import Theorems.Thm_LevyStochCalc_Probability_sq_sum_le_card_sq_mul_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionApi.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Itô L² isometry.**

  `𝔼[ (∫_0^T H_s dW_s)² ] = 𝔼[ ∫_0^T |H_s|² ds ]`

for predictable square-integrable `H`. ENNReal form.

Forwards to the L²-isometry conjunct of `itoIsometry_brownian_unified_existence`. -/
theorem LevyStochCalc.Brownian.Ito.itoIsometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (T : ℝ) (hT : 0 < T)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq_int_global T ω‖₊
      : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ((‖H ω s‖₊ : ℝ≥0∞))^2 ∂volume ∂P := by
  unfold stochasticIntegral
  exact isometry_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global hT
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
/-- Refining the level does not move the partition points: level `n`'s point `k` is level
`n + 1`'s point `2 * k`. -/
theorem LevyStochCalc.Probability.dyadicTime_succ_two_mul {T : ℝ} (n k : ℕ) :
    dyadicTime T (n + 1) (2 * k) = dyadicTime T n k := by
  unfold dyadicTime
  congr 1
  push_cast
  rw [pow_succ]
  ring
variable {M : ℝ → Ω → ℝ} {T : ℝ}
/-- Refining the level can only increase the sampled running maximum. -/
theorem LevyStochCalc.Probability.enorm_dyadicRunMax_mono (M : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    Monotone fun n => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [enorm_dyadicRunMax_408915f, enorm_dyadicRunMax_408915f]
  refine iSup_le fun k => ?_
  refine le_iSup_of_le ⟨2 * (k : ℕ), ?_⟩ (le_of_eq ?_)
  · have hk : (k : ℕ) ≤ 2 ^ n := Nat.lt_succ_iff.mp k.isLt
    calc 2 * (k : ℕ) ≤ 2 * 2 ^ n := by omega
      _ < 2 ^ (n + 1) + 1 := by rw [pow_succ]; omega
  · rw [dyadicTime_succ_two_mul]
/-- Each sampled running maximum is measurable when the sampled slices are. -/
theorem LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hM : ∀ t : ℝ, Measurable (M t)) (T : ℝ) (n : ℕ) :
    Measurable fun ω => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  have heq : (fun ω => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞))
      = fun ω => ⨆ k : Fin (2 ^ n + 1), (‖M (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) :=
    funext fun ω => enorm_dyadicRunMax_408915f M T n ω
  rw [heq]
  exact Measurable.iSup fun k =>
    ENNReal.continuous_coe.measurable.comp (hM (dyadicTime T n (k : ℕ))).nnnorm
/-- Squaring commutes with the supremum of a monotone sequence. -/
theorem LevyStochCalc.Probability.iSup_sq_of_monotone {a : ℕ → ℝ≥0∞} (ha : Monotone a) :
    (⨆ n, a n) ^ 2 = ⨆ n, a n ^ 2 := by
  refine le_antisymm ?_ (iSup_le fun n => pow_le_pow_left' (le_iSup a n) 2)
  rw [pow_two, ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => le_iSup_of_le (max n m) ?_
  rw [pow_two]
  exact mul_le_mul' (ha (le_max_left n m)) (ha (le_max_right n m))
/-- **Doob's `L²` inequality over the dyadic points.** No path regularity is needed: the
supremum runs over the countable family of partition points. -/
theorem LevyStochCalc.Probability.lintegral_iSup_dyadicRunMax_sq_le {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} (hM : MeasureTheory.Martingale M ℱ μ) (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)) ^ 2 ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have hMm : ∀ t : ℝ, Measurable (M t) := fun t => ((hM.1 t).mono (ℱ.le t)).measurable
  have heq : (fun ω => (⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)) ^ 2)
      = fun ω => ⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 :=
    funext fun ω => iSup_sq_of_monotone (enorm_dyadicRunMax_mono M T ω)
  rw [heq, lintegral_iSup (fun n => (measurable_enorm_dyadicRunMax hMm T n).pow_const 2)
    (fun m n hmn ω => pow_le_pow_left' (enorm_dyadicRunMax_mono M T ω hmn) 2)]
  exact iSup_le fun n => lintegral_sq_dyadicRunMax_le_408915f hM hT n
/-- The sampled running maximum of a finite sum is bounded by the sum of the running maxima. -/
theorem LevyStochCalc.Probability.enorm_dyadicRunMax_sum_le {ι : Type*} (s : Finset ι) (A : ι → ℝ → Ω → ℝ) (T : ℝ)
    (n : ℕ) (ω : Ω) :
    (‖dyadicRunMax (fun t ω => ∑ j ∈ s, A j t ω) T n ω‖₊ : ℝ≥0∞)
      ≤ ∑ j ∈ s, (‖dyadicRunMax (A j) T n ω‖₊ : ℝ≥0∞) := by
  rw [enorm_dyadicRunMax_408915f]
  refine iSup_le fun k => ?_
  have hpt : (‖∑ j ∈ s, A j (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞)
      ≤ ∑ j ∈ s, (‖A j (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by
    rw [← ENNReal.ofNNReal_finsetSum]
    exact ENNReal.coe_le_coe.mpr (nnnorm_sum_le _ _)
  refine le_trans hpt (Finset.sum_le_sum fun j _ => ?_)
  rw [enorm_dyadicRunMax_408915f]
  exact le_iSup (fun m : Fin (2 ^ n + 1) =>
    (‖A j (dyadicTime T n (m : ℕ)) ω‖₊ : ℝ≥0∞)) k
/-- The supremum of the sampled running maxima of a finite sum is bounded by the sum of the
suprema. -/
theorem LevyStochCalc.Probability.iSup_dyadicRunMax_sum_le {ι : Type*} (s : Finset ι) (A : ι → ℝ → Ω → ℝ) (T : ℝ)
    (ω : Ω) :
    (⨆ n, (‖dyadicRunMax (fun t ω => ∑ j ∈ s, A j t ω) T n ω‖₊ : ℝ≥0∞))
      ≤ ∑ j ∈ s, ⨆ n, (‖dyadicRunMax (A j) T n ω‖₊ : ℝ≥0∞) :=
  iSup_le fun n => le_trans (enorm_dyadicRunMax_sum_le s A T n ω)
    (Finset.sum_le_sum fun j _ => le_iSup (fun m => (‖dyadicRunMax (A j) T m ω‖₊ : ℝ≥0∞)) n)
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardSupL2.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Ito
end LevyStochCalc.Ito
open LevyStochCalc LevyStochCalc.Ito
section
namespace LevyStochCalc.Ito.Picard
end LevyStochCalc.Ito.Picard
open LevyStochCalc LevyStochCalc.Ito LevyStochCalc.Ito.Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
omit [MeasurableSpace E] in
/-- Doob's inequality for one Brownian coordinate of the Picard step. -/
theorem LevyStochCalc.Ito.Picard.lintegral_sq_iSup_brownian_coord_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (j : Fin d) {T' : ℝ} (hT' : 0 ≤ T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax (fun t ω =>
        LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j)
          (h_meas i j) (h_progMeas i j) (h_sq i j) t ω) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 4 * ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j)
          (h_meas i j) (h_progMeas i j) (h_sq i j) T' ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  obtain ⟨F, hF⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral (W.W j) ℱ (hℱW j)
    (fun ω' s => coeffs.σ s (X s ω') i j) (h_meas i j) (h_progMeas i j) (h_sq i j)
  exact lintegral_iSup_dyadicRunMax_sq_le hF hT'
omit [MeasurableSpace E] in
/-- Slice measurability of one Brownian coordinate's integral. -/
theorem LevyStochCalc.Ito.Picard.measurable_brownianIntegral_slice
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (j : Fin d) (t : ℝ) :
    Measurable fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j) (h_meas i j) (h_progMeas i j) (h_sq i j) t ω := by
  obtain ⟨F, hF⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral (W.W j) ℱ (hℱW j)
    (fun ω' s => coeffs.σ s (X s ω') i j) (h_meas i j) (h_progMeas i j) (h_sq i j)
  exact (hF.stronglyMeasurable t).measurable.mono (F.le t) le_rfl
namespace LevyStochCalc.Ito.Picard
end LevyStochCalc.Ito.Picard
open LevyStochCalc.Ito.Picard in
omit [MeasurableSpace E] in
/-- The dyadic supremum of the Brownian component, summed over the driving coordinates. -/
theorem solution
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω =>
        LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
        T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
  set g : Fin d → ℝ → Ω → ℝ := fun j t ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j) t ω with hg
  have hunfold : (fun t (ω : Ω) =>
      LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
      = fun t ω => ∑ j : Fin d, g j t ω := rfl
  have hmeas : ∀ j : Fin d, ∀ t : ℝ, Measurable (g j t) := fun j t =>
    LevyStochCalc.Ito.Picard.measurable_brownianIntegral_slice W ℱ hℱW coeffs X h_meas h_progMeas h_sq i j t
  have hsupm : ∀ j : Fin d, Measurable fun ω =>
      (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (g j) T' m ω‖₊ : ℝ≥0∞)) ^ 2 :=
    fun j => (Measurable.iSup fun m => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hmeas j) T' m).pow_const 2
  calc ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => ∑ j : Fin d, g j t ω) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ ∫⁻ ω, ((Finset.univ.card : ℝ≥0∞) ^ 2
          * ∑ j : Fin d, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (g j) T' m ω‖₊ : ℝ≥0∞)) ^ 2) ∂P :=
        lintegral_mono fun ω => le_trans
          (pow_le_pow_left' (LevyStochCalc.Probability.iSup_dyadicRunMax_sum_le Finset.univ g T' ω) 2)
          (LevyStochCalc.Probability.sq_sum_le_card_sq_mul_408915f Finset.univ _)
    _ = (Finset.univ.card : ℝ≥0∞) ^ 2
          * ∑ j : Fin d, ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (g j) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ fun j _ => hsupm j]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (by simp) (ENNReal.sum_lt_top.mpr fun j _ => ?_)
        refine lt_of_le_of_lt (LevyStochCalc.Ito.Picard.lintegral_sq_iSup_brownian_coord_le W ℱ hℱW coeffs X
          h_meas h_progMeas h_sq i j hT'.le) ?_
        refine ENNReal.mul_lt_top (by norm_num) ?_
        refine lt_of_le_of_lt ?_ (h_sq i j T' hT')
        exact le_of_eq (LevyStochCalc.Brownian.Ito.itoIsometry (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j) T' hT'
          (h_meas i j) (h_progMeas i j) (h_sq i j))
