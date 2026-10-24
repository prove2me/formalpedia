-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.solvesOn_globalPatch_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:59:15.647211+00:00
-- url     : https://prove2.me/submissions/ea417b4a-3133-4426-85c9-2f0cea37aab0

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
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardGlobal
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
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardWindow
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
import Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_diffusion_congr_ae_408915f
import Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_jump_congr_ae_408915f
import Theorems.Thm_LevyStochCalc_Ito_Picard_progressivelyMeasurable_globalPatch_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section Step
variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The drift component at `t` only reads its input on `[0, t]`. -/
theorem LevyStochCalc.Ito.Picard.picardStep_drift_congr_ae {t : ℝ}
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P, picardStep_drift coeffs X x₀ t ω = picardStep_drift coeffs Y x₀ t ω := by
  filter_upwards [hXY] with ω hω
  have hω' : ∀ᵐ s ∂volume, s ∈ Set.Icc (0 : ℝ) t → X s ω = Y s ω :=
    (ae_restrict_iff' measurableSet_Icc).mp hω
  have hint : (fun i : Fin n => ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i)
      = fun i : Fin n => ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Y s ω) i := by
    funext i
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hω'] with s hs hsmem
    rw [hs hsmem]
  simp only [picardStep_drift, hint]
/-- **The Picard step is local.** Inputs agreeing a.e. on `[0, t]` give a.e. equal steps at `t`. -/
theorem LevyStochCalc.Ito.Picard.picardStep_congr_ae
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_X : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_Y : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P,
      picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
          h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        = picardStep W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω := by
  filter_upwards [picardStep_drift_congr_ae coeffs X Y x₀ hXY,
    picardStep_diffusion_congr_ae_408915f W ℱ hℱW coeffs X Y h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y ht hXY,
    picardStep_jump_congr_ae_408915f N ℱ hℱN coeffs X Y h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y ht hXY] with ω h1 h2 h3
  simp only [picardStep, h1, h2, h3]
end Step
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardGlobal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The glued path map is jointly measurable. -/
theorem LevyStochCalc.Ito.Picard.measurable_globalPatch {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ k, Measurable (Function.uncurry (Y k))) :
    Measurable (Function.uncurry (globalPatch Y)) := by
  have h : Measurable fun p : ℕ × (ℝ × Ω) => Function.uncurry (Y p.1) p.2 :=
    measurable_from_prod_countable_right fun k => hY k
  exact h.comp ((measurable_fst.nat_ceil).prodMk measurable_id)
section Glue
variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
omit [MeasurableSpace E] [SigmaFinite ν] [IsProbabilityMeasure P] in
/-- The glued path map has a finite `S²` norm on every window. -/
theorem LevyStochCalc.Ito.Picard.lintegral_sq_iSup_globalPatch_lt_top {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      globalPatch Y t ω = Y k t ω)
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (T' : ℝ) (hT' : 0 < T') :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i,
      (‖globalPatch Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) (hYS ⌈T'⌉₊ T' hT')
  filter_upwards [hagree] with ω hω
  refine le_of_eq (iSup_congr fun t => ?_)
  rw [hω ⌈T'⌉₊ (t : ℝ) ⟨t.2.1, t.2.2.trans ((Nat.le_ceil T').trans (by linarith))⟩]
namespace LevyStochCalc.Ito.Picard
end LevyStochCalc.Ito.Picard
open LevyStochCalc.Ito.Picard in
/-- **The glued path map solves the equation on every window.** -/
theorem solution
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hYm : ∀ k, Measurable (Function.uncurry (Y k)))
    (hYa : ∀ k, ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      LevyStochCalc.Ito.Picard.globalPatch Y t ω = Y k t ω)
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYsol : ∀ k : ℕ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ (Y k) ((k : ℝ) + 1)) (T : ℝ) :
    LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ (LevyStochCalc.Ito.Picard.globalPatch Y) T := by
  have hpm := LevyStochCalc.Ito.Picard.measurable_globalPatch hYm
  have hpa := fun i => LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch_408915f hYa i
  have hpS := LevyStochCalc.Ito.Picard.lintegral_sq_iSup_globalPatch_lt_top hagree hYS
  refine ⟨LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hpm,
    LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hpa,
    LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hpm hpS,
    LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hpm,
    LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hpa,
    LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hpm hpS, ?_⟩
  intro t ht
  have htk : t ≤ (⌈t⌉₊ : ℝ) + 1 := (Nat.le_ceil t).trans (by linarith)
  have heqn := (hYsol ⌈t⌉₊).eqn t ⟨ht.1, htk⟩
  rcases ht.1.lt_or_eq with ht0 | ht0
  · have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
        Y ⌈t⌉₊ s ω = LevyStochCalc.Ito.Picard.globalPatch Y s ω := by
      filter_upwards [hagree] with ω hω
      refine (ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun s hs => ?_)
      exact (hω ⌈t⌉₊ s ⟨hs.1, hs.2.trans htk⟩).symm
    have hcongr := LevyStochCalc.Ito.Picard.picardStep_congr_ae W N ℱ hℱW hℱN coeffs (Y ⌈t⌉₊) (LevyStochCalc.Ito.Picard.globalPatch Y) x₀
      (hYsol ⌈t⌉₊).h_σ_meas (hYsol ⌈t⌉₊).h_σ_progMeas (hYsol ⌈t⌉₊).h_σ_sq
      (hYsol ⌈t⌉₊).h_γ_meas (hYsol ⌈t⌉₊).h_γ_progMeas (hYsol ⌈t⌉₊).h_γ_sq
      (LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hpm)
      (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hpa)
      (LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hpm hpS)
      (LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hpm)
      (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hpa)
      (LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hpm hpS) ht0 hae
    filter_upwards [heqn, hagree, hcongr] with ω h1 h2 h3
    intro i
    rw [h2 ⌈t⌉₊ t ⟨ht.1, htk⟩, h1 i, h3]
  · subst ht0
    filter_upwards [heqn, hagree,
      LevyStochCalc.Ito.Picard.ae_picardStep_zero W N ℱ hℱW hℱN coeffs (Y ⌈(0 : ℝ)⌉₊) x₀
        (hYsol ⌈(0 : ℝ)⌉₊).h_σ_meas (hYsol ⌈(0 : ℝ)⌉₊).h_σ_progMeas
        (hYsol ⌈(0 : ℝ)⌉₊).h_σ_sq (hYsol ⌈(0 : ℝ)⌉₊).h_γ_meas
        (hYsol ⌈(0 : ℝ)⌉₊).h_γ_progMeas (hYsol ⌈(0 : ℝ)⌉₊).h_γ_sq,
      LevyStochCalc.Ito.Picard.ae_picardStep_zero W N ℱ hℱW hℱN coeffs (LevyStochCalc.Ito.Picard.globalPatch Y) x₀
        (LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hpm)
        (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hpa)
        (LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hpm hpS)
        (LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hpm)
        (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hpa)
        (LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hpm hpS)] with ω h1 h2 h3 h4
    intro i
    rw [h2 ⌈(0 : ℝ)⌉₊ 0 ⟨le_rfl, htk⟩, h1 i, h3 i, h4 i]
