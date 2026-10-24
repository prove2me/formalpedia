-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded_coeff_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:48:52.103864+00:00
-- url     : https://prove2.me/submissions/6dde9cf8-9fe8-474f-a412-40039081fb52

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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_itoFormula_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_ae_tendsto_version_clamp_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_tendsto_drift_clamp_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_tendsto_quadVar_clamp_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_tendsto_version_clamp_at_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_isVectorItoVersion_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_seq_ae_tendsto_stochInt_clamp_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_energy_window_clamp_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_version_ae_eq_zero_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/Progressive.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω}
section Add
variable [NormedAddCommGroup E] {ℱ : Filtration ℝ mΩ}
/-- The pointwise sum of two progressively measurable processes is progressively measurable. -/
theorem LevyStochCalc.Probability.ProgressivelyMeasurable.add {A B : Ω → ℝ → E} (hA : ProgressivelyMeasurable ℱ A)
    (hB : ProgressivelyMeasurable ℱ B) :
    ProgressivelyMeasurable ℱ fun ω s => A ω s + B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s + B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 + (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, add_zero]
  rw [key]
  exact (hA t).add (hB t)
end Add
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
/-- A version's paths are jointly measurable in the sample point and the time. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) :
    Measurable (Function.uncurry fun ω s => X s ω) := by
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable h.continuous_path h.measurable
  exact hjoint.comp measurable_swap
/-- A continuous function of a version is progressively measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.progressivelyMeasurable_comp
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Continuous φ) : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) := by
  refine Probability.ProgressivelyMeasurable.of_isStronglyProgressive ?_
  refine MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => hφ.comp_stronglyMeasurable (h.adapted t)) fun ω => ?_
  exact hφ.comp (h.continuous_path ω)
/-- A measurable function of a version is jointly measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry_comp
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Measurable φ) : Measurable (Function.uncurry fun ω s => φ (X s ω)) :=
  hφ.comp h.measurable_uncurry
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open ContinuousLinearMap
variable {n : ℕ}
section Coord
variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
/-- A partial derivative is bounded by the operator norm of the Fréchet derivative. -/
theorem LevyStochCalc.abs_coordDeriv_le {K₁ : ℝ} (h : ∀ x, ‖f' x‖ ≤ K₁) (p : Fin n) (x : Fin n → ℝ) :
    |coordDeriv f' p x| ≤ K₁ := by
  have hnorm : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by
    rw [Pi.norm_single, norm_one]
  calc |coordDeriv f' p x| = ‖f' x (Pi.single p 1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f' x‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ := (f' x).le_opNorm _
    _ = ‖f' x‖ := by rw [hnorm, mul_one]
    _ ≤ K₁ := h x
/-- Continuity of a partial derivative. -/
theorem LevyStochCalc.continuous_coordDeriv (hf'c : Continuous f') (p : Fin n) :
    Continuous (coordDeriv f' p) :=
  hf'c.clm_apply continuous_const
end Coord
end
end

section
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
theorem LevyStochCalc.Brownian.Ito.measurable_clampDrift {b : Fin n → Ω → ℝ → ℝ}
    (hm : ∀ p, Measurable (Function.uncurry (b p))) (j : ℕ) (p : Fin n) :
    Measurable (Function.uncurry (clampDrift b j p)) :=
  (continuous_clampAt (j : ℝ)).measurable.comp (hm p)
theorem LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampDrift {b : Fin n → Ω → ℝ → ℝ}
    (hp : ∀ p, Probability.ProgressivelyMeasurable ℱ (b p)) (j : ℕ) (p : Fin n) :
    Probability.ProgressivelyMeasurable ℱ (clampDrift b j p) :=
  Probability.ProgressivelyMeasurable.comp_continuous (continuous_clampAt (j : ℝ))
    (clampAt_zero (Nat.cast_nonneg j)) (hp p)
omit [MeasurableSpace Ω] in
theorem LevyStochCalc.Brownian.Ito.abs_clampDrift_le (b : Fin n → Ω → ℝ → ℝ) (j : ℕ) (p : Fin n) (ω : Ω) (s : ℝ) :
    |clampDrift b j p ω s| ≤ (j : ℝ) :=
  abs_clampAt_le (Nat.cast_nonneg j) _
section ClampProcess
variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')
/-- A sequence tending to zero drops below the geometric thresholds along indices that grow. -/
theorem LevyStochCalc.Brownian.Ito.exists_seq_lt_of_tendsto_zero {u : ℕ → ℝ≥0∞}
    (h : Filter.Tendsto u Filter.atTop (𝓝 0)) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧ ∀ i : ℕ, u (ms i) < ((2 : ℝ≥0∞)⁻¹) ^ i := by
  have hchoice : ∀ i : ℕ, ∃ j : ℕ, i ≤ j ∧ u j < ((2 : ℝ≥0∞)⁻¹) ^ i := by
    intro i
    have hpos : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ i := by
      refine pos_iff_ne_zero.mpr (pow_ne_zero i ?_)
      simp
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h.eventually (gt_mem_nhds hpos))
    exact ⟨max N i, le_max_right N i, hN (max N i) (le_max_left N i)⟩
  choose ms hge hms using hchoice
  exact ⟨ms, hge, hms⟩
/-- **A clamping level along which the approximation error is summable.** -/
theorem LevyStochCalc.Brownian.Ito.exists_seq_clampMesh_lt
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤)
    (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
    ∃ ns : ℕ → ℕ, (∀ i : ℕ, i ≤ ns i) ∧
      ∀ i : ℕ, clampMesh P H b T (ns i) < ((2 : ℝ≥0∞)⁻¹) ^ i := by
  exact exists_seq_lt_of_tendsto_zero (tendsto_energy_window_clamp_408915f hm hbm hq hbq)
end ClampProcess
end Clamped
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section Limits
variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
variable (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
/-- **Itô's formula for a vector Itô process with unbounded coefficients**, for a function whose
first two derivatives are bounded. -/
theorem solution
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    (hf'c : Continuous f') (hf''c : Continuous f'')
    (hf''unif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z w : Fin n → ℝ, ‖z - w‖ < δ → ‖f'' z - f'' w‖ ≤ ε)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
      fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
  classical
  have hX₀' : ∀ p : Fin n, Measurable fun ω => X₀ ω p :=
    fun p => (hX₀ p).mono (ℱ'.le 0) le_rfl
  have hqT : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := fun p k => (hHs p k T hT).ne
  have hbqT : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := fun p => (hbq p T hT).ne
  obtain ⟨ns, hge, hns⟩ := LevyStochCalc.Brownian.Ito.exists_seq_clampMesh_lt hHm hbm hqT hbqT
  -- the versions driven by the clamped coefficients
  have hex : ∀ j : ℕ, ∃ Z : ℝ → Ω → Fin n → ℝ,
      LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ' hcoord (LevyStochCalc.Brownian.Ito.clampCoeff H j)
        (fun p k => LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm j p k)
        (fun p k => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp j p k)
        (fun p k T' hT' => LevyStochCalc.Brownian.Ito.energy_clampCoeff_lt_top j p k T' hT')
        X₀ (LevyStochCalc.Brownian.Ito.clampDrift bdrift j) Z := fun j =>
    LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_408915f W ℱ' hcoord (LevyStochCalc.Brownian.Ito.clampCoeff H j)
      (fun p k => LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm j p k)
      (fun p k => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp j p k)
      (fun p k T' hT' => LevyStochCalc.Brownian.Ito.energy_clampCoeff_lt_top j p k T' hT')
      (Nat.cast_nonneg j) (LevyStochCalc.Brownian.Ito.abs_clampCoeff_le H j) hℱ0 hnull hX₀ (LevyStochCalc.Brownian.Ito.clampDrift bdrift j)
      (fun p => LevyStochCalc.Brownian.Ito.measurable_clampDrift hbm j p)
      (fun p => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampDrift hbp j p)
      (Nat.cast_nonneg j) (LevyStochCalc.Brownian.Ito.abs_clampDrift_le bdrift j)
  choose Xj hXj using hex
  have hYm : ∀ i : ℕ, Measurable (Function.uncurry fun ω s => Xj (ns i) s ω) :=
    fun i => (hXj (ns i)).measurable_uncurry
  have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Xj (ns i) s ω) Filter.atTop (𝓝 (X s ω)) :=
    LevyStochCalc.Brownian.Ito.ae_ae_tendsto_version_clamp_408915f W ℱ' hcoord hX₀' hbm hbq h hXj hns
  -- the integrands along the clamped versions
  have hmY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv f' p (Xj (ns i) s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s) :=
    fun i p k => ((hXj (ns i)).measurable_uncurry_comp
      (LevyStochCalc.continuous_coordDeriv hf'c p).measurable).mul (LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm (ns i) p k)
  have hpY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
      fun ω s => LevyStochCalc.coordDeriv f' p (Xj (ns i) s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s :=
    fun i p k => ((hXj (ns i)).progressivelyMeasurable_comp
      (LevyStochCalc.continuous_coordDeriv hf'c p)).mul (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp (ns i) p k)
  have hqY : ∀ (i : ℕ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.coordDeriv f' p (Xj (ns i) s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := by
    intro i p k
    refine LevyStochCalc.Brownian.Ito.energy_lt_top_of_bounded (M := K₁ * ((ns i : ℕ) : ℝ)) fun ω s => ?_
    rw [abs_mul]
    exact mul_le_mul (LevyStochCalc.abs_coordDeriv_le hf'bd p _) (LevyStochCalc.Brownian.Ito.abs_clampCoeff_le H (ns i) p k ω s)
      (abs_nonneg _) hK₁0
  -- the polarised coefficients of the clamped model
  have hma : ∀ (i : ℕ) (p q : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s + LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s) :=
    fun i p q k => (LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm (ns i) p k).add
      (LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm (ns i) q k)
  have hpa : ∀ (i : ℕ) (p q : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
      fun ω s => LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s + LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s :=
    fun i p q k => (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp (ns i) p k).add
      (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp (ns i) q k)
  have hqa : ∀ (i : ℕ) (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s + LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := by
    intro i p q k
    refine LevyStochCalc.Brownian.Ito.energy_lt_top_of_bounded (M := 2 * ((ns i : ℕ) : ℝ)) fun ω s => ?_
    calc |LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s + LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s|
        ≤ |LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s| + |LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s| := abs_add_le _ _
      _ ≤ ((ns i : ℕ) : ℝ) + ((ns i : ℕ) : ℝ) :=
          add_le_add (LevyStochCalc.Brownian.Ito.abs_clampCoeff_le H (ns i) p k ω s) (LevyStochCalc.Brownian.Ito.abs_clampCoeff_le H (ns i) q k ω s)
      _ = 2 * ((ns i : ℕ) : ℝ) := by ring
  -- Itô's formula for each clamped model
  have hform : ∀ i : ℕ,
      (fun ω : Ω => f (Xj (ns i) T ω) - f (Xj (ns i) 0 ω)) =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv f' p (Xj (ns i) s ω) * LevyStochCalc.Brownian.Ito.clampDrift bdrift (ns i) p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (Xj (ns i) s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s)
              (hmY i p k) (hpY i p k) (hqY i p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              LevyStochCalc.coordDeriv₂ f'' p q (Xj (ns i) s ω)
                * ∑ k : Fin d, LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s
                    * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s ∂volume := fun i =>
    (hXj (ns i)).itoFormula_408915f (Nat.cast_nonneg (ns i)) (LevyStochCalc.Brownian.Ito.abs_clampCoeff_le H (ns i)) hX₀'
      (fun p => LevyStochCalc.Brownian.Ito.measurable_clampDrift hbm (ns i) p) (Nat.cast_nonneg (ns i))
      (LevyStochCalc.Brownian.Ito.abs_clampDrift_le bdrift (ns i)) (hma i) (hpa i) (hqa i) hf hf' hf'bd hK₂0 hf''bd
      hf''c hf''unif (hmY i) (hpY i) (hqY i) hT
  obtain ⟨ms, hmsge, hSI⟩ := LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_stochInt_clamp_408915f W ℱ' hcoord hf'c hK₁0 hf'bd
    hHm hT (fun p k => hHs p k T hT) hYm h.measurable_uncurry hge hae hmY hpY hqY hmg hpg hqg
  have hmsTop : Filter.Tendsto ms Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hmsge Filter.tendsto_id
  have hfc : Continuous f :=
    Differentiable.continuous fun z => (hf z).differentiableAt
  have hTlim : ∀ᵐ ω ∂P, Filter.Tendsto (fun i => Xj (ns i) T ω) Filter.atTop (𝓝 (X T ω)) :=
    LevyStochCalc.Brownian.Ito.ae_tendsto_version_clamp_at_408915f W ℱ' hcoord hX₀' hbm hbq h hXj hns hT le_rfl
  have hzeroj : ∀ᵐ ω ∂P, ∀ j : ℕ, Xj j 0 ω = X₀ ω :=
    MeasureTheory.ae_all_iff.mpr fun j => LevyStochCalc.Brownian.Ito.version_ae_eq_zero_408915f W ℱ' hcoord (hXj j)
  have hzeroX : X 0 =ᵐ[P] X₀ := LevyStochCalc.Brownian.Ito.version_ae_eq_zero_408915f W ℱ' hcoord h
  have hdrift := LevyStochCalc.Brownian.Ito.ae_tendsto_drift_clamp_408915f hf'c hf'bd hbm (fun p => hbq p T hT) hYm
    hge hae
  have hqv := LevyStochCalc.Brownian.Ito.ae_tendsto_quadVar_clamp_408915f hf''c hK₂0 hf''bd hHm (fun p k => hHs p k T hT) hYm
    hge hae
  filter_upwards [MeasureTheory.ae_all_iff.mpr hform, hTlim, hzeroj, hzeroX, hdrift, hqv, hSI]
    with ω h1 h2 h3 h4 h5 h6 h7
  have hlhs : Filter.Tendsto
      (fun i : ℕ => f (Xj (ns (ms i)) T ω) - f (Xj (ns (ms i)) 0 ω)) Filter.atTop
      (𝓝 (f (X T ω) - f (X 0 ω))) := by
    have hzeroeq : ∀ i : ℕ, f (Xj (ns (ms i)) 0 ω) = f (X 0 ω) := by
      intro i
      rw [h3 (ns (ms i)), h4]
    have hTt : Filter.Tendsto (fun i : ℕ => f (Xj (ns (ms i)) T ω)) Filter.atTop
        (𝓝 (f (X T ω))) := (hfc.continuousAt.tendsto.comp h2).comp hmsTop
    have hconst : Filter.Tendsto (fun i : ℕ => f (Xj (ns (ms i)) 0 ω)) Filter.atTop
        (𝓝 (f (X 0 ω))) := by
      refine Filter.Tendsto.congr (fun i => (hzeroeq i).symm) ?_
      exact tendsto_const_nhds
    exact hTt.sub hconst
  have hrhs : Filter.Tendsto (fun i : ℕ =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.coordDeriv f' p (Xj (ns (ms i)) s ω) * LevyStochCalc.Brownian.Ito.clampDrift bdrift (ns (ms i)) p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s => LevyStochCalc.coordDeriv f' p (Xj (ns (ms i)) s ω)
              * LevyStochCalc.Brownian.Ito.clampCoeff H (ns (ms i)) p k ω s)
            (hmY (ms i) p k) (hpY (ms i) p k) (hqY (ms i) p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv₂ f'' p q (Xj (ns (ms i)) s ω)
              * ∑ k : Fin d, LevyStochCalc.Brownian.Ito.clampCoeff H (ns (ms i)) p k ω s
                  * LevyStochCalc.Brownian.Ito.clampCoeff H (ns (ms i)) q k ω s ∂volume) Filter.atTop
      (𝓝 ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) := by
    refine ((tendsto_finsetSum _ fun p _ => (h5 p).comp hmsTop).add
      (tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun k _ => h7 p k)).add ?_
    exact (tendsto_finsetSum _ fun p _ =>
      tendsto_finsetSum _ fun q _ => (h6 p q).comp hmsTop).const_mul _
  exact tendsto_nhds_unique (Filter.Tendsto.congr (fun i => h1 (ms i)) hlhs) hrhs
