-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero_of_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:19:24.814022+00:00
-- url     : https://prove2.me/submissions/901adaa0-03c0-4ec3-b403-caf9fc3e0b8b

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_AugmentedFiltration
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross
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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Augmentation
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
import Mathlib.MeasureTheory.Measure.NullMeasurable
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
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integrable_cross_term_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_mul_increment_mul_increment_eq_zero_408915f

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
end Increments
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
section
namespace LevyStochCalc.Brownian.Multidim
end LevyStochCalc.Brownian.Multidim
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
section
namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
section DirectCross
/-- A coefficient measurable at the start of an interval is orthogonal to the Brownian increment
over it. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (V : BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hV : IsBrownianFiltration V ℱ) {s u : ℝ}
    (hs : 0 ≤ s) (hsu : s < u) {Y : Ω → ℝ} (hY : StronglyMeasurable[ℱ s] Y) (hYm : Measurable Y) :
    ∫ ω, Y ω * (V.W u ω - V.W s ω) ∂P = 0 := by
  have h := Ito.integral_mul_increment_pow_408915f V ℱ hV hs hsu hY hYm 1
  rw [Ito.integral_increment_pow_odd V hs hsu odd_one, mul_zero] at h
  simpa only [pow_one] using h
end DirectCross
end
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
section
namespace LevyStochCalc.Brownian.Multidim
end LevyStochCalc.Brownian.Multidim
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
section
namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
section SimpleIntegrands
open LevyStochCalc.Brownian.Ito
variable {W : MultidimBrownianMotion P d}
namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
open LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion in
/-- **The cross term vanishes, when the `Wʲ` interval starts last.** -/
theorem solution (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hrv : r < v) (hpr : p ≤ r) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
      * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
  have hΔ : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P) (x y : ℝ), Measurable fun ω => V.W y ω - V.W x ω :=
    fun V x y => (V.measurable_eval y).sub (V.measurable_eval x)
  have hΔℱ : ∀ (k : Fin d) {x y s : ℝ}, x ≤ s → y ≤ s →
      Measurable[ℱ s] fun ω => (W.W k).W y ω - (W.W k).W x ω := fun k x y s hxs hys =>
    (((hcoord k).measurable y).mono (ℱ.mono hys) le_rfl).sub
      (((hcoord k).measurable x).mono (ℱ.mono hxs) le_rfl)
  have hξη : StronglyMeasurable[ℱ r] fun ω => ξ ω * η ω := (hξ.mono (ℱ.mono hpr)).mul hη
  have hξηb : ∀ ω, |ξ ω * η ω| ≤ |Mξ| * |Mη| := fun ω => by
    rw [abs_mul]
    exact mul_le_mul ((hξb ω).trans (le_abs_self _)) ((hηb ω).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  rcases le_or_gt q r with hqr | hrq
  · -- the `Wⁱ` increment is already known at time `r`
    have hY : StronglyMeasurable[ℱ r] fun ω => ξ ω * ((W.W i).W q ω - (W.W i).W p ω) * η ω :=
      ((hξ.mono (ℱ.mono hpr)).mul (hΔℱ i hpr hqr).stronglyMeasurable).mul hη
    have h := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (W.W j) (hcoord j) hr hrv hY
      ((hξm.mul (hΔ (W.W i) p q)).mul hηm)
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  · -- split the `Wⁱ` increment at `r`
    have hsplit : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
          * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
        = fun ω => (ξ ω * ((W.W i).W r ω - (W.W i).W p ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω))
          + (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) := by
      funext ω; ring
    rw [hsplit,
      integral_add (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_408915f (W.W i) (W.W j) hp hpr hr hrv.le hξm hηm hξb hηb)
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_408915f (W.W i) (W.W j) hr hrq.le hr hrv.le hξm hηm hξb hηb)]
    have h1 : ∫ ω, (ξ ω * ((W.W i).W r ω - (W.W i).W p ω))
        * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
      have hY : StronglyMeasurable[ℱ r] fun ω => ξ ω * ((W.W i).W r ω - (W.W i).W p ω) * η ω :=
        ((hξ.mono (ℱ.mono hpr)).mul (hΔℱ i hpr le_rfl).stronglyMeasurable).mul hη
      have h := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (W.W j) (hcoord j) hr hrv hY
        ((hξm.mul (hΔ (W.W i) p r)).mul hηm)
      rw [← h]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [h1, zero_add]
    -- both increments now start at `r`
    rcases lt_trichotomy q v with hqv | rfl | hvq
    · have hsplit' : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
                * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω))
            + (ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
                * ((W.W j).W v ω - (W.W j).W q ω) := by
        funext ω; ring
      have hint1 : Integrable (fun ω => (ξ ω * η ω)
          * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω))) P := by
        have := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_408915f (W.W i) (W.W j) hr hrq.le hr hrq.le hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      have hint2 : Integrable (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
          * ((W.W j).W v ω - (W.W j).W q ω)) P := by
        have := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_408915f (W.W i) (W.W j) hr hrq.le (hr.trans hrq.le) hqv.le
          hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      rw [hsplit', integral_add hint1 hint2,
        LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_zero_408915f W hij hcoord hr hrq hξη (hξm.mul hηm) hξηb,
        LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (W.W j) (hcoord j) (hr.trans hrq.le) hqv
          (Y := fun ω => ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
          (((hξ.mono (ℱ.mono (hpr.trans hrq.le))).mul
            (hΔℱ i hrq.le le_rfl).stronglyMeasurable).mul (hη.mono (ℱ.mono hrq.le)))
          ((hξm.mul (hΔ (W.W i) r q)).mul hηm), add_zero]
    · have heq : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W q ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
              * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω)) := by
        funext ω; ring
      rw [heq]
      exact LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_zero_408915f W hij hcoord hr hrq hξη (hξm.mul hηm) hξηb
    · have hsplit' : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
                * (((W.W i).W v ω - (W.W i).W r ω) * ((W.W j).W v ω - (W.W j).W r ω))
            + (ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
                * ((W.W i).W q ω - (W.W i).W v ω) := by
        funext ω; ring
      have hint1 : Integrable (fun ω => (ξ ω * η ω)
          * (((W.W i).W v ω - (W.W i).W r ω) * ((W.W j).W v ω - (W.W j).W r ω))) P := by
        have := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_408915f (W.W i) (W.W j) hr hrv.le hr hrv.le hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      have hint2 : Integrable (fun ω => (ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
          * ((W.W i).W q ω - (W.W i).W v ω)) P := by
        have := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_408915f (W.W i) (W.W j) (hr.trans hrv.le) hvq.le hr hrv.le
          hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      rw [hsplit', integral_add hint1 hint2,
        LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_zero_408915f W hij hcoord hr hrv hξη (hξm.mul hηm) hξηb,
        LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (W.W i) (hcoord i) (hr.trans hrv.le) hvq
          (Y := fun ω => ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
          (((hξ.mono (ℱ.mono (hpr.trans hrv.le))).mul (hη.mono (ℱ.mono hrv.le))).mul
            (hΔℱ j hrv.le le_rfl).stronglyMeasurable)
          ((hξm.mul hηm).mul (hΔ (W.W j) r v)), add_zero]
