-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardStep_lt_top_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:58:35.324899+00:00
-- url     : https://prove2.me/submissions/46a0aa16-de60-4177-9873-181f8fb438c0

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
import Theorems.Thm_LevyStochCalc_Ito_Picard_iSup_dyadicRunMax_drift_le_408915f
import Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_drift_bound_lt_top_408915f
import Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_iSup_diffusion_lt_top_408915f
import Theorems.Thm_LevyStochCalc_Probability_enorm_dyadicRunMax_408915f
import Theorems.Thm_LevyStochCalc_Probability_lintegral_sq_dyadicRunMax_le_408915f

section
-- Modified by kls-lean for synchronized BrownianMotion interfaces; see formalization/vendor/port.patch.

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Martingale/CadlagModification.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Martingale
end LevyStochCalc.Martingale
open LevyStochCalc LevyStochCalc.Martingale
section Modification
variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
  {μ : Measure Ω} {X Y : ι → Ω → ℝ}
/-- A strongly adapted modification of a martingale is a martingale. -/
lemma LevyStochCalc.Martingale.martingale_of_ae_eq (hX : Martingale X ℱ μ) (hY : StronglyAdapted ℱ Y)
    (h : ∀ t, Y t =ᵐ[μ] X t) : Martingale Y ℱ μ :=
  ⟨hY, fun s t hst => (condExp_congr_ae (h t)).trans ((hX.condExp_ae_eq hst).trans (h s).symm)⟩
end Modification
end
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/Compensated.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Poisson
end LevyStochCalc.Poisson
open LevyStochCalc LevyStochCalc.Poisson
section
namespace LevyStochCalc.Poisson.Compensated
end LevyStochCalc.Poisson.Compensated
open LevyStochCalc LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
section Integral
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ
    : IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
include hℱ in
/-- The stochastic integral is a martingale on the right-continuous natural filtration. -/
theorem LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral_rightCont :
    Martingale (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
      ℱ.rightCont P :=
  LevyStochCalc.Martingale.martingale_of_ae_eq
    (martingale_rightCont_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
    (fun t => (stochasticIntegral_adapted N ℱ hℱ φ h_meas h_progMeas h_sq_int_global
      t).stronglyMeasurable)
    (stochasticIntegral_ae_eq_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
end Integral
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
/-- A squared sum of two extended reals, up to the constant `4`. -/
theorem LevyStochCalc.Ito.Picard.sq_add_le_four_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have h1 : a + b ≤ 2 * (a ⊔ b) := by
    calc a + b ≤ (a ⊔ b) + (a ⊔ b) := add_le_add le_sup_left le_sup_right
      _ = 2 * (a ⊔ b) := by ring
  have h2 : (a ⊔ b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases max_choice a b with h | h <;> rw [h]
    · exact le_add_right le_rfl
    · exact le_add_left le_rfl
  calc (a + b) ^ 2 ≤ (2 * (a ⊔ b)) ^ 2 := pow_le_pow_left' h1 2
    _ = 4 * (a ⊔ b) ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl h2
/-- A squared sum of three extended reals, up to the constant `16`. -/
theorem LevyStochCalc.Ito.Picard.sq_add3_le_sixteen_mul (a b c : ℝ≥0∞) : (a + b + c) ^ 2 ≤ 16 * (a ^ 2 + b ^ 2 + c ^ 2) :=
  calc (a + b + c) ^ 2 ≤ 4 * ((a + b) ^ 2 + c ^ 2) := sq_add_le_four_mul _ _
    _ ≤ 4 * (4 * (a ^ 2 + b ^ 2) + c ^ 2) :=
        mul_le_mul' le_rfl (add_le_add (sq_add_le_four_mul a b) le_rfl)
    _ = 16 * (a ^ 2 + b ^ 2) + 4 * c ^ 2 := by ring
    _ ≤ 16 * (a ^ 2 + b ^ 2) + 16 * c ^ 2 :=
        add_le_add le_rfl (mul_le_mul' (by norm_num) le_rfl)
    _ = 16 * (a ^ 2 + b ^ 2 + c ^ 2) := by ring
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
/-- Doob's inequality for the jump component of the Picard step. -/
theorem LevyStochCalc.Ito.Picard.lintegral_sq_iSup_jump_le
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T') :
    ∫⁻ ω, (⨆ m, (‖dyadicRunMax
        (fun t ω => picardStep_jump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i)
        T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  have hmart : MeasureTheory.Martingale
      (fun t ω => picardStep_jump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i)
      ℱ.rightCont P :=
    LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral_rightCont N ℱ hℱN
      (fun ω s e => coeffs.γ s (X s ω) e i) (h_meas i) (h_progMeas i) (h_sq i)
  refine le_trans (lintegral_iSup_dyadicRunMax_sq_le hmart hT') ?_
  rw [lintegral_sq_picardStep_jump_eq N ℱ hℱN coeffs X h_meas h_progMeas h_sq i hT']
namespace LevyStochCalc.Ito.Picard
end LevyStochCalc.Ito.Picard
open LevyStochCalc.Ito.Picard in
/-- **The Picard step has finite `S²` norm on every window.** -/
theorem solution
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
      LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω =>
        LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
          h_γ_meas h_γ_progMeas h_γ_sq t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
  set A : ℝ → Ω → ℝ := fun t ω => LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ t ω i with hA
  set B : ℝ → Ω → ℝ := fun t ω =>
    LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω i with hB
  set C : ℝ → Ω → ℝ := fun t ω =>
    LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i with hC
  have hunfold : (fun t (ω : Ω) =>
      LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω i)
      = fun t ω => A t ω + B t ω + C t ω := rfl
  have hAm : ∀ t : ℝ, Measurable (A t) := fun t =>
    LevyStochCalc.Ito.Picard.measurable_picardStep_drift coeffs X x₀ i (hμm i) t
  have hBm : ∀ t : ℝ, Measurable (B t) := fun t =>
    LevyStochCalc.Ito.Picard.measurable_picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i t
  have hCm : ∀ t : ℝ, Measurable (C t) := fun t =>
    LevyStochCalc.Ito.Picard.measurable_picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq i t
  have hsupm : ∀ (D : ℝ → Ω → ℝ), (∀ t, Measurable (D t)) →
      Measurable fun ω => (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax D T' m ω‖₊ : ℝ≥0∞)) ^ 2 :=
    fun D hD => (Measurable.iSup fun m => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax hD T' m).pow_const 2
  -- the drift is dominated pathwise
  have hAfin : ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax A T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae ?_)
      (LevyStochCalc.Ito.Picard.lintegral_sq_drift_bound_lt_top_408915f coeffs X x₀ i hT'.le (hμm i) (hμsq i T' hT'))
    filter_upwards [LevyStochCalc.Ito.Picard.ae_integrableOn_of_lintegral_sq (P := P) (hμm i) (hμsq i)] with ω hω
    exact pow_le_pow_left' (LevyStochCalc.Ito.Picard.iSup_dyadicRunMax_drift_le_408915f coeffs X x₀ i hT'.le (hω T')) 2
  have hBfin : ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax B T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ :=
    LevyStochCalc.Ito.Picard.lintegral_sq_iSup_diffusion_lt_top_408915f W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i hT'
  have hCfin : ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax C T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
    refine lt_of_le_of_lt (LevyStochCalc.Ito.Picard.lintegral_sq_iSup_jump_le N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas
      h_γ_sq i hT'.le) ?_
    exact ENNReal.mul_lt_top (by norm_num) (h_γ_sq i T' hT')
  rw [hunfold]
  calc ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => A t ω + B t ω + C t ω) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ ∫⁻ ω, (16 : ℝ≥0∞) * ((⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax A T' m ω‖₊ : ℝ≥0∞)) ^ 2
          + (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax B T' m ω‖₊ : ℝ≥0∞)) ^ 2
          + (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax C T' m ω‖₊ : ℝ≥0∞)) ^ 2) ∂P :=
        lintegral_mono fun ω => le_trans (pow_le_pow_left' (le_trans
          (LevyStochCalc.Probability.iSup_dyadicRunMax_add_le (fun t ω => A t ω + B t ω) C T' ω)
          (add_le_add (LevyStochCalc.Probability.iSup_dyadicRunMax_add_le A B T' ω) le_rfl)) 2)
          (LevyStochCalc.Ito.Picard.sq_add3_le_sixteen_mul _ _ _)
    _ < ⊤ := by
        have hAB : Measurable fun ω : Ω => (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax A T' m ω‖₊ : ℝ≥0∞)) ^ 2
            + (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax B T' m ω‖₊ : ℝ≥0∞)) ^ 2 := (hsupm A hAm).add (hsupm B hBm)
        rw [lintegral_const_mul' _ _ (by norm_num : (16 : ℝ≥0∞) ≠ ⊤),
          lintegral_add_left hAB, lintegral_add_left (hsupm A hAm)]
        exact ENNReal.mul_lt_top (by norm_num)
          (ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hAfin, hBfin⟩, hCfin⟩)
