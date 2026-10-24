-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.ae_ae_tendsto_version_clamp_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:46:30.935556+00:00
-- url     : https://prove2.me/submissions/b8698e4d-a2e0-4351-8662-5665a9d91833

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CoordDerivative
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossVariation
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossVariationSum
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraProduct
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoCutoff
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFormulaGrid
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentLintegral
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoIncrementMomentRestrict
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionApi
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoLocality
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoOptionalStopping
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoPullOut
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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_PolarisedQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SmoothCutoff
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoFormula
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_ItoFormulaUnboundedClamp
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
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ExitTime
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ProgressiveCadlag
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_StoppedProgressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Rat.Denumerable
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_window_sq_norm_version_clamp_sub_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_of_tendsto_sq_enorm_408915f

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
/-- A version's paths are jointly measurable in the sample point and the time. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) :
    Measurable (Function.uncurry fun ω s => X s ω) := by
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable h.continuous_path h.measurable
  exact hjoint.comp measurable_swap
end VectorVersion
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section Clamped
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
section ClampProcess
variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')
/-- If the integrals of a sequence of nonnegative functions are summable, their sum is finite
almost everywhere. -/
theorem LevyStochCalc.Brownian.Ito.ae_tsum_ne_top_of_lintegral_summable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hsum : ∑' i : ℕ, ∫⁻ a, g i a ∂μ ≠ ⊤) : ∀ᵐ a ∂μ, ∑' i : ℕ, g i a ≠ ⊤ := by
  have h1 : ∫⁻ a, ∑' i : ℕ, g i a ∂μ ≠ ⊤ := by
    rw [MeasureTheory.lintegral_tsum fun i => (hg i).aemeasurable]
    exact hsum
  filter_upwards [MeasureTheory.ae_lt_top (Measurable.tsum hg) h1] with a ha
  exact ha.ne
/-- If the integrals of a sequence of nonnegative functions are summable, the functions tend to
zero almost everywhere. -/
theorem LevyStochCalc.Brownian.Ito.ae_tendsto_zero_of_lintegral_summable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hsum : ∑' i : ℕ, ∫⁻ a, g i a ∂μ ≠ ⊤) :
    ∀ᵐ a ∂μ, Filter.Tendsto (fun i => g i a) Filter.atTop (𝓝 0) := by
  filter_upwards [ae_tsum_ne_top_of_lintegral_summable hg hsum] with a ha
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha
/-- The geometric bound the summability argument uses. -/
theorem LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    ∑' i : ℕ, c * ((2 : ℝ≥0∞)⁻¹) ^ i ≠ ⊤ := by
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  refine ne_of_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) ?_)
  have hne : (1 : ℝ≥0∞) - 2⁻¹ ≠ 0 := by
    rw [Ne, tsub_eq_zero_iff_le]
    exact not_le.mpr (ENNReal.inv_lt_one.mpr (by norm_num))
  exact lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hne)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
/-- **Along the chosen levels the clamped versions converge to the original process almost
everywhere on the window.** -/
theorem solution
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Xj : ℕ → ℝ → Ω → Fin n → ℝ}
    (hX : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X)
    (hXj : ∀ j : ℕ, LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ' hcoord (LevyStochCalc.Brownian.Ito.clampCoeff H j)
      (fun p k => LevyStochCalc.Brownian.Ito.measurable_clampCoeff hm j p k)
      (fun p k => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => LevyStochCalc.Brownian.Ito.energy_clampCoeff_lt_top j p k T' hT')
      X₀ (LevyStochCalc.Brownian.Ito.clampDrift b j) (Xj j))
    {T : ℝ} {ns : ℕ → ℕ}
    (hns : ∀ i : ℕ, LevyStochCalc.Brownian.Ito.clampMesh P H b T (ns i) < ((2 : ℝ≥0∞)⁻¹) ^ i) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Xj (ns i) s ω) Filter.atTop (𝓝 (X s ω)) := by
  have hmeasi : ∀ i : ℕ, Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro i
    have hjoint : Measurable fun q : Ω × ℝ => (‖Xj (ns i) q.2 q.1 - X q.2 q.1‖₊ : ℝ≥0∞) ^ 2 :=
      ((((hXj (ns i)).measurable_uncurry.sub
        hX.measurable_uncurry).nnnorm).coe_nnreal_ennreal).pow_const 2
    exact hjoint.lintegral_prod_right'
  have hsum : ∑' i : ℕ, ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => ?_)
      (lt_top_iff_ne_top.mpr (LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top (ENNReal.ofReal T)
        ENNReal.ofReal_ne_top)))
    refine (LevyStochCalc.Brownian.Ito.lintegral_window_sq_norm_version_clamp_sub_le_408915f W ℱ' hcoord hX₀ hbm hbq hX
      (hXj (ns i))).trans ?_
    exact mul_le_mul' le_rfl (hns i).le
  filter_upwards [LevyStochCalc.Brownian.Ito.ae_tsum_ne_top_of_lintegral_summable (μ := P) hmeasi hsum] with ω hω
  have hmeasω : ∀ i : ℕ, Measurable fun s : ℝ => (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro i
    have h1 : Measurable fun s : ℝ => Xj (ns i) s ω :=
      ((hXj (ns i)).measurable_uncurry.comp (measurable_const.prodMk measurable_id))
    have h2 : Measurable fun s : ℝ => X s ω :=
      (hX.measurable_uncurry.comp (measurable_const.prodMk measurable_id))
    exact (((h1.sub h2).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hinner := LevyStochCalc.Brownian.Ito.ae_tendsto_zero_of_lintegral_summable
    (μ := volume.restrict (Set.Icc (0 : ℝ) T)) hmeasω hω
  filter_upwards [hinner] with s hs
  exact LevyStochCalc.Brownian.Ito.tendsto_of_tendsto_sq_enorm_408915f hs
