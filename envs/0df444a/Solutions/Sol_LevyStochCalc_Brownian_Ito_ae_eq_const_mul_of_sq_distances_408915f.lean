-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.ae_eq_const_mul_of_sq_distances_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:58:57.146408+00:00
-- url     : https://prove2.me/submissions/e43f644e-5221-46b0-9fb1-569b930f154a

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_DenseCountable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Topology
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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
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
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
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
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.MonotoneContinuity

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
omit [IsProbabilityMeasure P] in
/-- The Bochner integral of a square as the extended integral of the squared norm. -/
theorem LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal {X : Ω → ℝ} (hX : AEStronglyMeasurable X P) :
    ∫ ω, X ω ^ 2 ∂P = (∫⁻ ω, (‖X ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω))
    ((hX.mul hX).congr (Filter.Eventually.of_forall fun ω => (pow_two (X ω)).symm))]
  congr 1
  exact lintegral_congr fun ω => (sq_nnnorm_eq_ofReal_sq (X ω)).symm
omit [IsProbabilityMeasure P] in
/-- The square of a square-integrable function is integrable. -/
theorem LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp {X : Ω → ℝ} (hX : MemLp X 2 P) :
    Integrable (fun ω => X ω ^ 2) P := by
  have h := hX.integrable_mul hX
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  exact (pow_two (X ω)).symm
section Scaling
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
omit [IsProbabilityMeasure P] in
/-- **Squared distances of a scalar multiple force the scalar relation.** -/
theorem solution {x y : Ω → ℝ} (hx : MemLp x 2 P) (hy : MemLp y 2 P)
    {c : ℝ} {X Y Z : ℝ≥0∞}
    (hSx : ∫⁻ ω, (‖x ω‖₊ : ℝ≥0∞) ^ 2 ∂P = X)
    (hSy : ∫⁻ ω, (‖y ω‖₊ : ℝ≥0∞) ^ 2 ∂P = Y)
    (hSxy : ∫⁻ ω, (‖x ω - y ω‖₊ : ℝ≥0∞) ^ 2 ∂P = Z)
    (hXY : X.toReal = c ^ 2 * Y.toReal) (hZY : Z.toReal = (c - 1) ^ 2 * Y.toReal) :
    x =ᵐ[P] fun ω => c * y ω := by
  have ex : ∫ ω, x ω ^ 2 ∂P = X.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal hx.aestronglyMeasurable, hSx]
  have ey : ∫ ω, y ω ^ 2 ∂P = Y.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal hy.aestronglyMeasurable, hSy]
  have exy : ∫ ω, (x ω - y ω) ^ 2 ∂P = Z.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal (X := fun ω => x ω - y ω)
      (hx.aestronglyMeasurable.sub hy.aestronglyMeasurable), hSxy]
  have hsub : Integrable (fun ω => (x ω - y ω) ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp (hx.sub hy)
  have hX2 : Integrable (fun ω => (1 - c) * x ω ^ 2) P :=
    (LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp hx).const_mul _
  have hY2 : Integrable (fun ω => (c ^ 2 - c) * y ω ^ 2) P :=
    (LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp hy).const_mul _
  have hZ2 : Integrable (fun ω => c * (x ω - y ω) ^ 2) P := hsub.const_mul _
  have hF : Integrable (fun ω => (x ω - c * y ω) ^ 2) P := by
    have : MemLp (fun ω => x ω - c * y ω) 2 P := hx.sub (hy.const_mul c)
    exact LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp this
  have hkey : ∫ ω, (x ω - c * y ω) ^ 2 ∂P = 0 := by
    have hid : ∀ ω : Ω, (x ω - c * y ω) ^ 2
        = (1 - c) * x ω ^ 2 + ((c ^ 2 - c) * y ω ^ 2 + c * (x ω - y ω) ^ 2) := fun ω => by ring
    have h1 : ∫ ω, (x ω - c * y ω) ^ 2 ∂P
        = ∫ ω, ((1 - c) * x ω ^ 2 + ((c ^ 2 - c) * y ω ^ 2 + c * (x ω - y ω) ^ 2)) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    have hYZ : Integrable (fun ω => (c ^ 2 - c) * y ω ^ 2 + c * (x ω - y ω) ^ 2) P :=
      hY2.add hZ2
    rw [h1, integral_add hX2 hYZ, integral_add hY2 hZ2,
      integral_const_mul, integral_const_mul, integral_const_mul, ex, ey, exy, hXY, hZY]
    ring
  have hzero : (fun ω => (x ω - c * y ω) ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hF).mp hkey
  filter_upwards [hzero] with ω hω
  have h2 : (x ω - c * y ω) ^ 2 = 0 := by simpa using hω
  nlinarith [h2, sq_nonneg (x ω - c * y ω)]
