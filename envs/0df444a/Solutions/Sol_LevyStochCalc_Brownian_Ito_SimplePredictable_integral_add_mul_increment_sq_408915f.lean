-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.integral_add_mul_increment_sq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:15:41.762171+00:00
-- url     : https://prove2.me/submissions/712284de-4614-47b7-ad36-403f4c681aec

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraProduct
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentIncrements
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_mul_increment_pow_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_pow_gaussianReal_zero_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
/-- The odd moments of the standard real Gaussian vanish. -/
theorem LevyStochCalc.Brownian.Ito.integral_pow_gaussianReal_odd (m : ℕ) (hm : Odd m) :
    ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) = 0 := by
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  have h1 : ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1)
      = ∫ x : ℝ, (-x) ^ m ∂(gaussianReal 0 1) := by
    conv_lhs => rw [← hmap]
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [hm.neg_pow] at h1
  rw [integral_neg] at h1
  linarith
section Increments
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
/-- The moments of a Brownian increment scale with the square root of its length. -/
theorem LevyStochCalc.Brownian.Ito.integral_increment_pow {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (m : ℕ) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P
      = Real.sqrt (b - a) ^ m * ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [← integral_map hmeas.aemeasurable
      (f := fun x : ℝ => x ^ m) (by fun_prop),
    W.increment_gaussian ha hab]
  exact integral_pow_gaussianReal_zero_408915f _ m
/-- Odd moments of a Brownian increment vanish. -/
theorem LevyStochCalc.Brownian.Ito.integral_increment_pow_odd {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {m : ℕ} (hm : Odd m) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P = 0 := by
  rw [integral_increment_pow W ha hab m, integral_pow_gaussianReal_odd m hm, mul_zero]
/-- The second moment of a Brownian increment is its length. -/
theorem LevyStochCalc.Brownian.Ito.integral_increment_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P = b - a := by
  rw [integral_increment_pow W ha hab 2,
    LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment 1]
  rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ b - a)]
  norm_num
/-- A Brownian increment has moments of every order. -/
theorem LevyStochCalc.Brownian.Ito.memLp_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun ω => W.W b ω - W.W a ω) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have h := (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (μ := P)
    (f := fun ω => W.W b ω - W.W a ω) (p := p)
    (by fun_prop) hmeas.aemeasurable).1
  rw [W.increment_gaussian ha hab] at h
  exact h (memLp_id_gaussianReal' p hp)
end Increments
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section
namespace LevyStochCalc.Brownian.Ito.SimplePredictable
end LevyStochCalc.Brownian.Ito.SimplePredictable
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Ito.SimplePredictable
variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
omit [IsProbabilityMeasure P] in
/-- A real random variable in `Lᵐ` has an integrable `m`-th power. -/
private theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integrable_pow_of_memLp {f : Ω → ℝ} {m : ℕ} (hm : m ≠ 0)
    {p : ℝ≥0∞} (hp : p = (m : ℝ≥0∞)) (h : MemLp f p P) : Integrable (fun ω => f ω ^ m) P := by
  subst hp
  refine (h.integrable_norm_pow hm).mono ((continuous_pow m).comp_aestronglyMeasurable h.1)
    (Filter.Eventually.of_forall fun ω => ?_)
  simp
section Moments
namespace LevyStochCalc.Brownian.Ito.SimplePredictable
end LevyStochCalc.Brownian.Ito.SimplePredictable
open LevyStochCalc.Brownian.Ito.SimplePredictable in
/-- One step of a second-moment recursion. -/
 theorem solution
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S ξ : Ω → ℝ}
    (hS2 : MemLp S 2 P) (hSm : Measurable S)
    (hSad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) S)
    (hξm : Measurable ξ) (hξad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) ξ)
    {C : ℝ} (hC0 : 0 ≤ C) (hCξ : ∀ ω, |ξ ω| ≤ C) :
    ∫ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 2 ∂P
      = (∫ ω, S ω ^ 2 ∂P) + (∫ ω, ξ ω ^ 2 ∂P) * (b - a) := by
  have hDm : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hD2 : MemLp (fun ω => W.W b ω - W.W a ω) 2 P := LevyStochCalc.Brownian.Ito.memLp_increment W ha hab 2 (by simp)
  have hSD : Integrable (fun ω => |S ω| * |W.W b ω - W.W a ω|) P := by
    have h := (hS2.abs).integrable_mul (hD2.abs)
    exact h
  have hD2int : Integrable (fun ω => (W.W b ω - W.W a ω) ^ 2) P :=
    integrable_pow_of_memLp (m := 2) (by norm_num) (by simp) hD2
  have hi1 : Integrable (fun ω => S ω ^ 2) P :=
    integrable_pow_of_memLp (m := 2) (by norm_num) (by simp) hS2
  have hi2 : Integrable (fun ω => (2 * (S ω * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := by
    refine (hSD.const_mul (2 * C)).mono
      (((measurable_const.mul (hSm.mul hξm)).mul (hDm.pow_const 1)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := hCξ ω
    have h2 := abs_nonneg (S ω)
    have h3 := abs_nonneg (W.W b ω - W.W a ω)
    rw [pow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * C * (|S ω| * |W.W b ω - W.W a ω|))]
    have h4 : |(2 : ℝ)| = 2 := by norm_num
    rw [h4]
    nlinarith [mul_nonneg (mul_nonneg h2 h3) (sub_nonneg.mpr h1)]
  have hi3 : Integrable (fun ω => ξ ω ^ 2 * (W.W b ω - W.W a ω) ^ 2) P := by
    refine (hD2int.const_mul (C ^ 2)).mono
      (((hξm.pow_const 2).mul (hDm.pow_const 2)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := hCξ ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ C ^ 2 * (W.W b ω - W.W a ω) ^ 2)]
    have h2 : |W.W b ω - W.W a ω| ^ 2 = (W.W b ω - W.W a ω) ^ 2 := by
      rw [← abs_pow, abs_of_nonneg (sq_nonneg _)]
    rw [h2]
    nlinarith [sq_nonneg (W.W b ω - W.W a ω),
      mul_le_mul h1 h1 (abs_nonneg (ξ ω)) hC0]
  have hexp : ∀ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 2
      = S ω ^ 2 + (2 * (S ω * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + ξ ω ^ 2 * (W.W b ω - W.W a ω) ^ 2 := fun ω => by ring
  have hξ2ad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) (fun ω => ξ ω ^ 2) := by
    have hfun : (fun ω => ξ ω ^ 2) = ξ * ξ := by funext ω; rw [pow_two]; rfl
    rw [hfun]; exact hξad.mul hξad
  have hi12 : Integrable
      (fun ω => S ω ^ 2 + (2 * (S ω * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := hi1.add hi2
  simp_rw [hexp]
  rw [integral_add hi12 hi3, integral_add hi1 hi2,
    LevyStochCalc.Brownian.Ito.integral_mul_increment_pow_408915f W ℱ hℱ ha hab (Y := fun ω => 2 * (S ω * ξ ω))
      (MeasureTheory.stronglyMeasurable_const.mul (hSad.mul hξad))
      (measurable_const.mul (hSm.mul hξm)) 1,
    LevyStochCalc.Brownian.Ito.integral_increment_pow_odd W ha hab odd_one, mul_zero, add_zero,
    LevyStochCalc.Brownian.Ito.integral_mul_increment_pow_408915f W ℱ hℱ ha hab (Y := fun ω => ξ ω ^ 2)
      hξ2ad (hξm.pow_const 2) 2,
    LevyStochCalc.Brownian.Ito.integral_increment_sq W ha hab]
