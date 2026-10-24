-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:57:02.658569+00:00
-- url     : https://prove2.me/submissions/90aa2d53-16b8-4dfe-8e80-6ebcfd8b763a

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
import Theorems.Thm_LevyStochCalc_Ito_Picard_bieleckiNorm_picardStepOnStop_sub_rawStop_le_408915f
import Theorems.Thm_LevyStochCalc_Ito_Picard_measurable_picardStepOnRawStop_slice_408915f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardContractionFixedPoint.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
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
variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
variable {L : ℝ}
  (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
  (x₀ : Fin n → ℝ)
namespace LevyStochCalc.Ito.Picard
end LevyStochCalc.Ito.Picard
open LevyStochCalc.Ito.Picard in
/-- **The limit of the Picard iterates is a fixed point of the Picard step**: the Bielecki
distance between the step along the limit and the limit itself is zero. -/
theorem solution {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : LevyStochCalc.Ito.Picard.SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1) :
    LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
        LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip
            (LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
            (LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
              x₀ hT X₀)
            (LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
              hβ hT X₀ hq)
            hT.le x₀ t ω i
          - LevyStochCalc.Ito.Picard.picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ t ω i) = 0 := by
  set q := (ENNReal.ofReal
      ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
        / (2 * β))) ^ ((1 : ℝ) / 2) with hqdef
  set Y := LevyStochCalc.Ito.Picard.picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ with hYdef
  have hYm := LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hYa := LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
    x₀ hT X₀
  have hYb := LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
    hβ hT X₀ hq
  set Φ := LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hYm hYa hYb hT.le x₀ with hΦdef
  set D := (1 - q)⁻¹ * LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
      (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
        - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X t ω i)
    with hDdef
  have hDfin : D ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hq).ne')
      (LevyStochCalc.Ito.Picard.bieleckiNorm_sub_lt_top ℱ' hβ.le _ _).ne
  have hiter := fun k => LevyStochCalc.Ito.Picard.bieleckiNorm_picardIter_sub_bieleckiLimit_le W N ℱ' hℱW hℱN hℱ0 hnull
    coeffs hReg hLip x₀ hβ hT X₀ hq k
  have hbound : ∀ k : ℕ, LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => Φ t ω i - Y t ω i)
      ≤ q ^ (k + 1) * D + q ^ (k + 1) * D := by
    intro k
    have hXm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω =>
        (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i :=
      fun t i => LevyStochCalc.Ito.Picard.measurable_slice_of_uncurry
        (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
          (k + 1)).measurable_path t i
    have hΦm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Φ t ω i := fun t i =>
      LevyStochCalc.Ito.Picard.measurable_picardStepOnRawStop_slice_408915f W N ℱ' hℱW hℱN coeffs hReg hLip x₀
        hYm hYa hYb hT.le t i
    have hYsl : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Y t ω i :=
      fun t i => LevyStochCalc.Ito.Picard.measurable_slice_of_uncurry hYm t i
    have hEq : (fun t ω i => Φ t ω i - Y t ω i)
        = fun t (ω : Ω) =>
          (fun i => Φ t ω i
            - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
          + fun i =>
            (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i
              - Y t ω i := by
      funext t ω i
      simp [Pi.add_apply, sub_add_sub_cancel]
    have hadd := LevyStochCalc.Ito.Picard.bieleckiNorm_add_le (P := P) β T
      (fun t ω => fun i => Φ t ω i
        - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
      (fun t ω => fun i =>
        (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i
          - Y t ω i)
      (LevyStochCalc.Ito.Picard.bieleckiNorm_inner_aemeasurable_of_slice fun t i => (hΦm t i).sub (hXm t i))
      (LevyStochCalc.Ito.Picard.bieleckiNorm_inner_aemeasurable_of_slice fun t i => (hXm t i).sub (hYsl t i))
    have hcongr : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => Φ t ω i
          - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
        = LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
            LevyStochCalc.Ito.Picard.picardStepOnStop W N hℱW hℱN coeffs hReg hLip
              (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k) hT.le x₀ t ω i
              - Φ t ω i) := by
      rw [LevyStochCalc.Ito.Picard.bieleckiNorm_sub_comm (P := P) β T]
      refine LevyStochCalc.Ito.Picard.bieleckiNorm_congr_ae (P := P) β T fun t => ?_
      filter_upwards [LevyStochCalc.Ito.Picard.picardSelfMap_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
        (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k) t] with ω hω
      funext i
      have hunfold : (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
            (k + 1)).X t ω
          = (LevyStochCalc.Ito.Picard.picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
              (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k)).X t ω := rfl
      rw [hunfold, hω]
    have hfirst : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => Φ t ω i
          - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
        ≤ q ^ (k + 1) * D := by
      rw [hcongr]
      refine le_trans (LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnStop_sub_rawStop_le_408915f W N ℱ' hℱW hℱN
        coeffs hReg hLip hYm hYa hYb x₀ hβ hT _) ?_
      refine le_trans (mul_le_mul' le_rfl (hiter k)) (le_of_eq ?_)
      rw [← mul_assoc, ← pow_succ']
    rw [hEq]
    exact hadd.trans (add_le_add hfirst (hiter (k + 1)))
  have htend : Filter.Tendsto (fun k : ℕ => q ^ (k + 1) * D + q ^ (k + 1) * D)
      Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun k : ℕ => q ^ (k + 1)) Filter.atTop (nhds 0) :=
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq).comp (Filter.tendsto_add_atTop_nat 1)
    have hm : Filter.Tendsto (fun k : ℕ => q ^ (k + 1) * D) Filter.atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.mul_const hp (Or.inr hDfin)
    simpa using hm.add hm
  exact le_antisymm (ge_of_tendsto' htend hbound) zero_le
