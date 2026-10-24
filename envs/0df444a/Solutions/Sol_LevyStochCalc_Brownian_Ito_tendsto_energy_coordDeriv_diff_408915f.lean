-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.tendsto_energy_coordDeriv_diff_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:39:13.89177+00:00
-- url     : https://prove2.me/submissions/2b9e59d6-4f33-4675-9973-0587739cc656

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
section Energy
variable {H₁ H₂ : Ω → ℝ → ℝ}
/-- The energy density of an integrand is measurable in the sample point. -/
theorem LevyStochCalc.Brownian.Ito.measurable_energyDensity (hm : Measurable (Function.uncurry H₁)) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
  have hf : Measurable fun p : Ω × ℝ => (‖H₁ p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    (((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2)
  exact hf.lintegral_prod_right'
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoTimeRiemann.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The absolute value of a difference is at most the sum of the absolute values. -/
theorem LevyStochCalc.Brownian.Ito.abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  simpa using abs_add_le a (-b)
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoCutoff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open scoped Topology
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u
section Bounded
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
/-- A pointwise bound `|u| ≤ c|v|` squares into a bound on the extended norms. -/
theorem LevyStochCalc.Brownian.Ito.sq_enorm_le_of_abs_le {c : ℝ} (hc : 0 ≤ c) {u v : ℝ} (h : |u| ≤ c * |v|) :
    (‖u‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (c ^ 2) * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  have h1 : ‖u‖₊ ≤ Real.toNNReal c * ‖v‖₊ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [Real.coe_toNNReal c hc]
    simpa [Real.norm_eq_abs] using h
  calc (‖u‖₊ : ℝ≥0∞) ^ 2 ≤ ((Real.toNNReal c * ‖v‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 := by
        exact pow_le_pow_left' (by exact_mod_cast h1) 2
    _ = ENNReal.ofReal (c ^ 2) * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.coe_mul, mul_pow, ← ENNReal.coe_pow, ← Real.toNNReal_pow hc]
        rfl
end Bounded
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
/-- **The energies of the perturbed diffusion integrands vanish.** -/
theorem solution
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {G : Ω → ℝ → ℝ} (hmG : Measurable (Function.uncurry G)) {T : ℝ}
    (hqG : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (p : Fin n) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P) Filter.atTop (𝓝 0) := by
  set c : ℝ := 2 * K₁ with hc
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hbnd : ∀ (i : ℕ) (ω : Ω) (s : ℝ),
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (c ^ 2) * (‖G ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro i ω s
    refine LevyStochCalc.Brownian.Ito.sq_enorm_le_of_abs_le hc0 ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    calc |LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)|
        ≤ |LevyStochCalc.coordDeriv f' p (Y i s ω)| + |LevyStochCalc.coordDeriv f' p (X s ω)| :=
          LevyStochCalc.Brownian.Ito.abs_sub_le_abs_add_abs _ _
      _ ≤ K₁ + K₁ := add_le_add (LevyStochCalc.abs_coordDeriv_le hf'bd p _) (LevyStochCalc.abs_coordDeriv_le hf'bd p _)
      _ = c := by rw [hc]; ring
  have hjoint : ∀ i : ℕ, Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      (LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s) := by
    intro i
    exact (((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp (hYm i)).sub
      ((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp hXm)).mul hmG
  have hFmeas : ∀ i : ℕ, Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun i => LevyStochCalc.Brownian.Ito.measurable_energyDensity (hjoint i) T
  have hGmeas : Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := LevyStochCalc.Brownian.Ito.measurable_energyDensity hmG T
  -- inner limit, for almost every path
  have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun i : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      Filter.atTop (𝓝 0) := by
    filter_upwards [hae, MeasureTheory.ae_lt_top hGmeas hqG.ne] with ω hω hfin
    have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (F := fun (i : ℕ) (s : ℝ) =>
        (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2)
      (f := fun _s : ℝ => (0 : ℝ≥0∞))
      (bound := fun s => ENNReal.ofReal (c ^ 2) * (‖G ω s‖₊ : ℝ≥0∞) ^ 2)
      (fun i => (((Measurable.of_uncurry_left (hjoint i)).nnnorm).coe_nnreal_ennreal).pow_const 2)
      (fun i => Filter.Eventually.of_forall fun s => hbnd i ω s) ?_ ?_
    · simpa using hlim
    · rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (c ^ 2) ≠ ⊤)]
      exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne
    · filter_upwards [hω] with s hs
      have hcd : Filter.Tendsto (fun i : ℕ => LevyStochCalc.coordDeriv f' p (Y i s ω)) Filter.atTop
          (𝓝 (LevyStochCalc.coordDeriv f' p (X s ω))) :=
        (LevyStochCalc.continuous_coordDeriv hf'c p).continuousAt.tendsto.comp hs
      have hconstX : Filter.Tendsto (fun _ : ℕ => LevyStochCalc.coordDeriv f' p (X s ω)) Filter.atTop
          (𝓝 (LevyStochCalc.coordDeriv f' p (X s ω))) := tendsto_const_nhds
      have hconstG : Filter.Tendsto (fun _ : ℕ => G ω s) Filter.atTop (𝓝 (G ω s)) :=
        tendsto_const_nhds
      have hzero : Filter.Tendsto (fun i : ℕ =>
          (LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s) Filter.atTop (𝓝 0) := by
        have hs2 := (hcd.sub hconstX).mul hconstG
        simpa using hs2
      have hcont : Continuous fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2 := by
        have h1 : Continuous fun x : ℝ => (‖x‖₊ ^ 2 : ℝ≥0) := continuous_nnnorm.pow 2
        have h2 := ENNReal.continuous_coe.comp h1
        simp only [Function.comp_def, ENNReal.coe_pow] at h2
        exact h2
      have hres := (hcont.tendsto (0 : ℝ)).comp hzero
      simp only [Function.comp_def] at hres
      have hz0 : ((‖(0 : ℝ)‖₊ : ℝ≥0∞)) ^ 2 = 0 := by simp
      rw [hz0] at hres
      exact hres
  have hdom : ∀ (i : ℕ) (ω : Ω), (∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      ≤ ENNReal.ofReal (c ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro i ω
    rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (c ^ 2) ≠ ⊤)]
    exact MeasureTheory.lintegral_mono fun s => hbnd i ω s
  -- outer limit
  have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (μ := P)
    (F := fun (i : ℕ) (ω : Ω) => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    (f := fun _ω : Ω => (0 : ℝ≥0∞))
    (bound := fun ω => ENNReal.ofReal (c ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    hFmeas
    (fun i => Filter.Eventually.of_forall fun ω => hdom i ω) ?_ hinner
  · simpa using hlim
  · rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (c ^ 2) ≠ ⊤)]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hqG).ne
