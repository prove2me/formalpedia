-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:54:25.76252+00:00
-- url     : https://prove2.me/submissions/30c9da08-fe63-4df7-a12d-19de9fe3bdfb

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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_finsetSum_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_sq_enorm_finsetSum_le_408915f
import Theorems.Thm_LevyStochCalc_Probability_enorm_dyadicRunMax_408915f
import Theorems.Thm_LevyStochCalc_Probability_iSup_enorm_eq_iSup_dyadicRunMax_408915f
import Theorems.Thm_LevyStochCalc_Probability_lintegral_sq_dyadicRunMax_le_408915f
import Theorems.Thm_LevyStochCalc_Probability_sq_sum_le_card_sq_mul_408915f

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
theorem LevyStochCalc.Probability.dyadicTime_nonneg {T : ℝ} (hT : 0 ≤ T) (n k : ℕ) : 0 ≤ dyadicTime T n k :=
  le_min (by positivity) hT
theorem LevyStochCalc.Probability.dyadicTime_le {T : ℝ} (n k : ℕ) : dyadicTime T n k ≤ T := min_le_right _ _
theorem LevyStochCalc.Probability.dyadicTime_mem_Icc {T : ℝ} (hT : 0 ≤ T) (n k : ℕ) :
    dyadicTime T n k ∈ Set.Icc (0 : ℝ) T :=
  ⟨dyadicTime_nonneg hT n k, dyadicTime_le n k⟩
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
/-- The sampled running maximum is subadditive. -/
theorem LevyStochCalc.Probability.enorm_dyadicRunMax_add_le (A B : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    (‖dyadicRunMax (fun t ω => A t ω + B t ω) T n ω‖₊ : ℝ≥0∞)
      ≤ (‖dyadicRunMax A T n ω‖₊ : ℝ≥0∞) + (‖dyadicRunMax B T n ω‖₊ : ℝ≥0∞) := by
  rw [enorm_dyadicRunMax_408915f, enorm_dyadicRunMax_408915f, enorm_dyadicRunMax_408915f]
  refine iSup_le fun k => ?_
  have hpt : (‖A (dyadicTime T n (k : ℕ)) ω + B (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞)
      ≤ (‖A (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞)
        + (‖B (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by
    rw [← ENNReal.coe_add]
    exact ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _)
  exact le_trans hpt (add_le_add
    (le_iSup (fun j : Fin (2 ^ n + 1) => (‖A (dyadicTime T n (j : ℕ)) ω‖₊ : ℝ≥0∞)) k)
    (le_iSup (fun j : Fin (2 ^ n + 1) => (‖B (dyadicTime T n (j : ℕ)) ω‖₊ : ℝ≥0∞)) k))
/-- The supremum of the sampled running maxima is subadditive. -/
theorem LevyStochCalc.Probability.iSup_dyadicRunMax_add_le (A B : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    (⨆ n, (‖dyadicRunMax (fun t ω => A t ω + B t ω) T n ω‖₊ : ℝ≥0∞))
      ≤ (⨆ n, (‖dyadicRunMax A T n ω‖₊ : ℝ≥0∞))
        + ⨆ n, (‖dyadicRunMax B T n ω‖₊ : ℝ≥0∞) :=
  iSup_le fun n => le_trans (enorm_dyadicRunMax_add_le A B T n ω)
    (add_le_add (le_iSup (fun m => (‖dyadicRunMax A T m ω‖₊ : ℝ≥0∞)) n)
      (le_iSup (fun m => (‖dyadicRunMax B T m ω‖₊ : ℝ≥0∞)) n))
/-- A pathwise bound over the window bounds the supremum of the sampled running maxima. -/
theorem LevyStochCalc.Probability.iSup_dyadicRunMax_le_of_bound {A : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T) {ω : Ω} {c : ℝ≥0∞}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ≤ c) :
    (⨆ n, (‖dyadicRunMax A T n ω‖₊ : ℝ≥0∞)) ≤ c := by
  refine iSup_le fun n => ?_
  rw [enorm_dyadicRunMax_408915f]
  exact iSup_le fun k => h _ (dyadicTime_mem_Icc hT n (k : ℕ))
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcessVersion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section VectorVersion
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
variable {W ℱ hcoord H hHm hHp hHs} {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}
/-- A version's time slices are measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℝ) :
    Measurable (X t) := ((h.adapted t).mono (ℱ.le t)).measurable
/-- A version's coordinates are measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_coord
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℝ) (m : Fin n) :
    Measurable fun ω => X t ω m := (measurable_pi_apply m).comp (h.measurable t)
end VectorVersion
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
end Diff
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionSup.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u
section Helpers
variable {Ω : Type u}
/-- The extended norm does not see the absolute value. -/
theorem LevyStochCalc.Brownian.Ito.nnnorm_abs_real (x : ℝ) : ‖|x|‖₊ = ‖x‖₊ := by
  rw [← Real.norm_eq_abs, nnnorm_norm]
/-- A squared sum of two terms, up to a constant. -/
theorem LevyStochCalc.Brownian.Ito.add_sq_le_four_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have h := sq_sum_le_card_sq_mul_408915f (Finset.univ : Finset (Fin 2)) ![a, b]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finset.card_univ, Fintype.card_fin] at h
  have h4 : ((2 : ℕ) : ℝ≥0∞) ^ 2 = 4 := by norm_num
  rwa [h4] at h
/-- The sampled running maximum only sees the values at the dyadic points. -/
theorem LevyStochCalc.Brownian.Ito.dyadicRunMax_congr {A B : ℝ → Ω → ℝ} {T : ℝ} {ω : Ω}
    (h : ∀ m k : ℕ, A (dyadicTime T m k) ω = B (dyadicTime T m k) ω) (m : ℕ) :
    dyadicRunMax A T m ω = dyadicRunMax B T m ω := by
  simp only [dyadicRunMax]
  refine Finset.sup'_congr _ rfl fun k _ => ?_
  rw [h m k]
/-- The sampled running maximum does not see the absolute value. -/
theorem LevyStochCalc.Brownian.Ito.dyadicRunMax_abs (A : ℝ → Ω → ℝ) (T : ℝ) (m : ℕ) (ω : Ω) :
    dyadicRunMax (fun t ω => |A t ω|) T m ω = dyadicRunMax A T m ω := by
  simp only [dyadicRunMax]
  refine Finset.sup'_congr _ rfl fun k _ => ?_
  simp [Real.norm_eq_abs]
variable [MeasurableSpace Ω] {P : Measure Ω}
end Helpers
section SupBound
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
include hcoord in
/-- The martingale part of a vector Itô process is a martingale. -/
theorem LevyStochCalc.Brownian.Ito.martingale_vectorItoMartingale
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hq : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (p : Fin n) :
    MeasureTheory.Martingale
      (fun t ω => vectorItoMartingale W ℱ hcoord H hm hp hq p t ω) ℱ P := by
  have hrw : (fun (t : ℝ) (ω : Ω) => vectorItoMartingale W ℱ hcoord H hm hp hq p t ω)
      = fun t ω => ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k)
          (hm p k) (hp p k) (hq p k) t ω := rfl
  rw [hrw]
  exact martingale_finsetSum_408915f Finset.univ _ fun k _ =>
    martingale_stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hm p k) (hp p k) (hq p k)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hcoord in
/-- **The second moment of the window supremum of the difference of two vector Itô versions.**
The drift part is controlled pathwise by Cauchy–Schwarz and the martingale part by Doob's `L²`
maximal inequality. -/
theorem solution
    {H₁ H₂ : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm₁ : ∀ p k, Measurable (Function.uncurry (H₁ p k))}
    {hp₁ : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H₁ p k)}
    {hq₁ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {hm₂ : ∀ p k, Measurable (Function.uncurry (H₂ p k))}
    {hp₂ : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H₂ p k)}
    {hq₂ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {b₁ b₂ : Fin n → Ω → ℝ → ℝ}
    (hbm₁ : ∀ p, Measurable (Function.uncurry (b₁ p)))
    (hbm₂ : ∀ p, Measurable (Function.uncurry (b₂ p)))
    (hbq₁ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hbq₂ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X Y : ℝ → Ω → Fin n → ℝ}
    (hX : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ X)
    (hY : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ Y)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n,
          (4 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))) := by
  classical
  set Zc : Fin n → ℝ → Ω → ℝ := fun p t ω => Y t ω p - X t ω p with hZcdef
  set Zabs : ℝ → Ω → ℝ := fun t ω => ∑ p : Fin n, |Zc p t ω| with hZabsdef
  have hZcm : ∀ (p : Fin n) (t : ℝ), Measurable (Zc p t) :=
    fun p t => (hY.measurable_coord t p).sub (hX.measurable_coord t p)
  have hZccont : ∀ (p : Fin n) (ω : Ω), Continuous fun t => Zc p t ω := by
    intro p ω
    exact ((continuous_apply p).comp (hY.continuous_path ω)).sub
      ((continuous_apply p).comp (hX.continuous_path ω))
  have hZabscont : ∀ ω : Ω, Continuous fun t => Zabs t ω :=
    fun ω => continuous_finsetSum _ fun p _ => (hZccont p ω).abs
  set S : Fin n → Ω → ℝ≥0∞ := fun p ω => ⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax (Zc p) T m ω‖₊ : ℝ≥0∞)
    with hSdef
  have hSmeas : ∀ p : Fin n, Measurable (S p) :=
    fun p => Measurable.iSup fun m => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hZcm p) T m
  -- the window supremum is dominated by the coordinatewise dyadic suprema
  have hdom : ∀ ω : Ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞))
      ≤ ∑ p : Fin n, S p ω := by
    intro ω
    have hcad : ∀ t : ℝ, Filter.Tendsto (fun s => Zabs s ω) (nhdsWithin t (Set.Ioi t))
        (nhds (Zabs t ω)) := fun t => ((hZabscont ω).tendsto t).mono_left nhdsWithin_le_nhds
    have hstep1 : (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞))
        ≤ ⨆ t : Set.Icc (0 : ℝ) T, (‖Zabs (t : ℝ) ω‖₊ : ℝ≥0∞) := by
      refine iSup_le fun t => le_iSup_of_le t ?_
      have hnn : (0 : ℝ) ≤ ∑ q : Fin n, |Y (t : ℝ) ω q - X (t : ℝ) ω q| :=
        Finset.sum_nonneg fun q _ => abs_nonneg _
      have hreal : ‖Y (t : ℝ) ω - X (t : ℝ) ω‖
          ≤ ∑ q : Fin n, |Y (t : ℝ) ω q - X (t : ℝ) ω q| := by
        refine (pi_norm_le_iff_of_nonneg hnn).mpr fun q => ?_
        have hq : |Y (t : ℝ) ω q - X (t : ℝ) ω q|
            ≤ ∑ r : Fin n, |Y (t : ℝ) ω r - X (t : ℝ) ω r| :=
          Finset.single_le_sum (f := fun r : Fin n => |Y (t : ℝ) ω r - X (t : ℝ) ω r|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ q)
        simpa [Real.norm_eq_abs] using hq
      have hZ : ‖Zabs (t : ℝ) ω‖ = ∑ q : Fin n, |Y (t : ℝ) ω q - X (t : ℝ) ω q| := by
        simp only [hZabsdef, hZcdef]
        exact Real.norm_of_nonneg hnn
      have hle : ‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ ≤ ‖Zabs (t : ℝ) ω‖₊ := by
        rw [← NNReal.coe_le_coe]
        simpa only [coe_nnnorm, hZ] using hreal
      exact_mod_cast hle
    refine hstep1.trans ?_
    rw [LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax_408915f hT.le hcad]
    refine le_trans (LevyStochCalc.Probability.iSup_dyadicRunMax_sum_le Finset.univ (fun p t ω => |Zc p t ω|) T ω) ?_
    exact le_of_eq (Finset.sum_congr rfl fun p _ => by
      simp only [hSdef, LevyStochCalc.Brownian.Ito.dyadicRunMax_abs])
  -- square, and split the integral over the coordinates
  have hsq : ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n, ∫⁻ ω, (S p ω) ^ 2 ∂P := by
    calc ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
        ≤ ∫⁻ ω, ((n : ℝ≥0∞) ^ 2 * ∑ p : Fin n, (S p ω) ^ 2) ∂P := by
          refine MeasureTheory.lintegral_mono fun ω => ?_
          refine le_trans (pow_le_pow_left' (hdom ω) 2) ?_
          simpa using LevyStochCalc.Probability.sq_sum_le_card_sq_mul_408915f (Finset.univ : Finset (Fin n)) fun p => S p ω
      _ = (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n, ∫⁻ ω, (S p ω) ^ 2 ∂P := by
          rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
            MeasureTheory.lintegral_finsetSum _ fun p _ => (hSmeas p).pow_const 2]
  refine hsq.trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun p _ => ?_))
  -- the drift and martingale parts of the coordinate difference
  set D : ℝ → Ω → ℝ := fun t ω => (∫ s in Set.Icc (0 : ℝ) t, b₂ p ω s ∂volume)
    - ∫ s in Set.Icc (0 : ℝ) t, b₁ p ω s ∂volume with hDdef
  set M : ℝ → Ω → ℝ := fun t ω => LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t ω
    - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t ω with hMdef
  have hDm : ∀ t : ℝ, Measurable (D t) := fun t =>
    (LevyStochCalc.measurable_setIntegral (hbm₂ p) (Set.Icc (0 : ℝ) t)).sub
      (LevyStochCalc.measurable_setIntegral (hbm₁ p) (Set.Icc (0 : ℝ) t))
  have hMm : ∀ t : ℝ, Measurable (M t) := fun t =>
    (LevyStochCalc.Brownian.Ito.measurable_vectorItoMartingale W ℱ hcoord H₂ hm₂ hp₂ hq₂ p t).sub
      (LevyStochCalc.Brownian.Ito.measurable_vectorItoMartingale W ℱ hcoord H₁ hm₁ hp₁ hq₁ p t)
  have hsplit : ∀ᵐ ω ∂P, ∀ m k : ℕ,
      Zc p (LevyStochCalc.Probability.dyadicTime T m k) ω = D (LevyStochCalc.Probability.dyadicTime T m k) ω + M (LevyStochCalc.Probability.dyadicTime T m k) ω := by
    rw [MeasureTheory.ae_all_iff]
    intro m
    rw [MeasureTheory.ae_all_iff]
    intro k
    filter_upwards [hX.ae_eq (LevyStochCalc.Probability.dyadicTime T m k) (LevyStochCalc.Probability.dyadicTime_nonneg hT.le m k),
      hY.ae_eq (LevyStochCalc.Probability.dyadicTime T m k) (LevyStochCalc.Probability.dyadicTime_nonneg hT.le m k)] with ω e1 e2
    simp only [hZcdef, hDdef, hMdef, e1, e2, LevyStochCalc.Brownian.Ito.vectorItoProcess]
    ring
  have hSbound : ∀ᵐ ω ∂P, (S p ω) ^ 2
      ≤ 4 * ((⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2
        + (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax M T m ω‖₊ : ℝ≥0∞)) ^ 2) := by
    filter_upwards [hsplit] with ω hω
    have hcongr : ∀ m : ℕ, LevyStochCalc.Probability.dyadicRunMax (Zc p) T m ω
        = LevyStochCalc.Probability.dyadicRunMax (fun t ω => D t ω + M t ω) T m ω :=
      fun m => LevyStochCalc.Brownian.Ito.dyadicRunMax_congr (fun m' k => hω m' k) m
    have hle : S p ω ≤ (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞))
        + ⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax M T m ω‖₊ : ℝ≥0∞) := by
      simp only [hSdef, hcongr]
      exact LevyStochCalc.Probability.iSup_dyadicRunMax_add_le D M T ω
    exact le_trans (pow_le_pow_left' hle 2) (LevyStochCalc.Brownian.Ito.add_sq_le_four_mul _ _)
  -- the drift part, by Cauchy–Schwarz on the window
  have hΔbfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖|b₂ p ω s - b₁ p ω s|‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    have hbd : ∀ (ω : Ω) (s : ℝ), (‖|b₂ p ω s - b₁ p ω s|‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 + (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2) := by
      intro ω s
      have := LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul (b₂ p ω s) (b₁ p ω s)
      simpa [LevyStochCalc.Brownian.Ito.nnnorm_abs_real] using this
    exact LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound_408915f hbd (hbm₂ p) (hbm₁ p) (hbq₂ p) (hbq₁ p) T hT
  have hDrift : ∫⁻ ω, (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    have hint₁ : ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn (b₁ p ω) (Set.Icc (0 : ℝ) T) volume :=
      LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hbm₁ p) (hbq₁ p T hT)
    have hint₂ : ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn (b₂ p ω) (Set.Icc (0 : ℝ) T) volume :=
      LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hbm₂ p) (hbq₂ p T hT)
    have hptw : ∀ᵐ ω ∂P, (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞))
        ≤ (‖∫ s in Set.Icc (0 : ℝ) T, |b₂ p ω s - b₁ p ω s| ∂volume‖₊ : ℝ≥0∞) := by
      filter_upwards [hint₁, hint₂] with ω h1 h2
      refine LevyStochCalc.Probability.iSup_dyadicRunMax_le_of_bound hT.le fun t ht => ?_
      have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
      have hDt : D t ω = ∫ s in Set.Icc (0 : ℝ) t, (b₂ p ω s - b₁ p ω s) ∂volume := by
        simp only [hDdef]
        rw [MeasureTheory.integral_sub (h2.mono_set hsub) (h1.mono_set hsub)]
      have habs : |D t ω| ≤ ∫ s in Set.Icc (0 : ℝ) t, |b₂ p ω s - b₁ p ω s| ∂volume := by
        rw [hDt]
        exact MeasureTheory.abs_integral_le_integral_abs
      have hmono : ∫ s in Set.Icc (0 : ℝ) t, |b₂ p ω s - b₁ p ω s| ∂volume
          ≤ ∫ s in Set.Icc (0 : ℝ) T, |b₂ p ω s - b₁ p ω s| ∂volume :=
        MeasureTheory.setIntegral_mono_set (h2.sub h1).abs
          (Filter.Eventually.of_forall fun s => abs_nonneg _) hsub.eventuallyLE
      have hnn : ‖D t ω‖₊ ≤ ‖∫ s in Set.Icc (0 : ℝ) T, |b₂ p ω s - b₁ p ω s| ∂volume‖₊ := by
        rw [← NNReal.coe_le_coe]
        simp only [coe_nnnorm, Real.norm_eq_abs]
        have hAnn : (0 : ℝ) ≤ ∫ s in Set.Icc (0 : ℝ) T, |b₂ p ω s - b₁ p ω s| ∂volume :=
          MeasureTheory.integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun s => abs_nonneg _)
        rw [abs_of_nonneg hAnn]
        exact habs.trans hmono
      exact_mod_cast hnn
    calc ∫⁻ ω, (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
        ≤ ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) T,
            |b₂ p ω s - b₁ p ω s| ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P :=
          MeasureTheory.lintegral_mono_ae (hptw.mono fun ω h => pow_le_pow_left' h 2)
      _ ≤ ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖|b₂ p ω s - b₁ p ω s|‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
          LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le
            ((hbm₂ p).sub (hbm₁ p)).abs hT.le hΔbfin
      _ = ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
          simp
  -- the martingale part, by Doob's inequality
  have hMart : MeasureTheory.Martingale M ℱ P :=
    (LevyStochCalc.Brownian.Ito.martingale_vectorItoMartingale W ℱ hcoord hm₂ hp₂ hq₂ p).sub
      (LevyStochCalc.Brownian.Ito.martingale_vectorItoMartingale W ℱ hcoord hm₁ hp₁ hq₁ p)
  have hMT : ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    have hMTeq : ∀ ω : Ω, M T ω = ∑ k : Fin d,
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k) (hm₂ p k) (hp₂ p k)
            (hq₂ p k) T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k) (hm₁ p k) (hp₁ p k)
            (hq₁ p k) T ω) := by
      intro ω
      simp only [hMdef, LevyStochCalc.Brownian.Ito.vectorItoMartingale, LevyStochCalc.Brownian.Ito.coordItoIntegral]
      rw [Finset.sum_sub_distrib]
    have hkm : ∀ k : Fin d, Measurable fun ω : Ω =>
        (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k) (hm₂ p k) (hp₂ p k)
            (hq₂ p k) T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k) (hm₁ p k) (hp₁ p k)
            (hq₁ p k) T ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro k
      have h2 : Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k)
          (hm₂ p k) (hp₂ p k) (hq₂ p k) T) :=
        ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H₂ p k)
          (hm₂ p k) (hp₂ p k) (hq₂ p k) T).mono (ℱ.le T)).measurable
      have h1 : Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k)
          (hm₁ p k) (hp₁ p k) (hq₁ p k) T) :=
        ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H₁ p k)
          (hm₁ p k) (hp₁ p k) (hq₁ p k) T).mono (ℱ.le T)).measurable
      exact (((h2.sub h1).nnnorm).coe_nnreal_ennreal).pow_const 2
    calc ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, (d : ℝ≥0∞) * ∑ k : Fin d,
            (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k) (hm₂ p k) (hp₂ p k)
                (hq₂ p k) T ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k) (hm₁ p k) (hp₁ p k)
                (hq₁ p k) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
          refine MeasureTheory.lintegral_mono fun ω => ?_
          rw [hMTeq ω]
          exact LevyStochCalc.Brownian.Ito.sq_enorm_finsetSum_le_408915f _
      _ = (d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω,
            (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k) (hm₂ p k) (hp₂ p k)
                (hq₂ p k) T ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₁ p k) (hm₁ p k) (hp₁ p k)
                (hq₁ p k) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
          rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
            MeasureTheory.lintegral_finsetSum _ fun k _ => hkm k]
      _ = (d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
          refine congrArg (fun x => (d : ℝ≥0∞) * x) (Finset.sum_congr rfl fun k _ => ?_)
          exact LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H₂ p k)
            (H₁ p k) (hm₂ p k) (hm₁ p k) (hp₂ p k) (hp₁ p k) (hq₂ p k) (hq₁ p k) hT
  have hDoob : ∫⁻ ω, (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax M T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    LevyStochCalc.Probability.lintegral_iSup_dyadicRunMax_sq_le hMart hT.le
  calc ∫⁻ ω, (S p ω) ^ 2 ∂P
      ≤ ∫⁻ ω, 4 * ((⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2
          + (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax M T m ω‖₊ : ℝ≥0∞)) ^ 2) ∂P :=
        MeasureTheory.lintegral_mono_ae hSbound
    _ = 4 * (∫⁻ ω, (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax D T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
          + ∫⁻ ω, (⨆ m : ℕ, (‖LevyStochCalc.Probability.dyadicRunMax M T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ (by finiteness),
          MeasureTheory.lintegral_add_left
            ((Measurable.iSup fun m => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax hDm T m).pow_const 2)]
    _ ≤ 4 * (ENNReal.ofReal T * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            + 4 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) :=
        mul_le_mul' le_rfl (add_le_add hDrift (hDoob.trans (mul_le_mul' le_rfl hMT)))
    _ = 4 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
        rw [mul_add]
