-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:08:13.139967+00:00
-- url     : https://prove2.me/submissions/c437bfe9-7870-430b-8d87-8e796c41a1e8

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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIoc_eval_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIoc_zero_eval_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_integralAgainst_408915f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem LevyStochCalc.Brownian.Ito.stepIoc_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    ∀ i : Fin (stepIoc Ω ha hab).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIoc Ω ha hab).partition i.castSucc)) ((stepIoc Ω ha hab).ξ i) := by
  intro i
  fin_cases i <;> exact MeasureTheory.stronglyMeasurable_const
theorem LevyStochCalc.Brownian.Ito.stepIoc₀_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ} (hb : 0 < b) :
    ∀ i : Fin (stepIoc₀ Ω hb).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIoc₀ Ω hb).partition i.castSucc)) ((stepIoc₀ Ω hb).ξ i) := by
  intro i
  fin_cases i
  exact MeasureTheory.stronglyMeasurable_const
theorem LevyStochCalc.Brownian.Ito.stepIoc_integralAgainst {a b : ℝ} (ha : 0 < a) (hab : a < b) (M : ℝ → Ω → ℝ)
    (t : ℝ) (ω : Ω) :
    (stepIoc Ω ha hab).integralAgainst M t ω = M (min b t) ω - M (min a t) ω := by
  have hrw : (stepIoc Ω ha hab).integralAgainst M t ω
      = ∑ i : Fin 2, (![fun _ => (0 : ℝ), fun _ => (1 : ℝ)] : Fin 2 → Ω → ℝ) i ω
        * (M (min ((![0, a, b] : Fin 3 → ℝ) i.succ) t) ω
          - M (min ((![0, a, b] : Fin 3 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_two]
  simp
theorem LevyStochCalc.Brownian.Ito.stepIoc₀_integralAgainst {b : ℝ} (hb : 0 < b) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (stepIoc₀ Ω hb).integralAgainst M t ω = M (min b t) ω - M (min 0 t) ω := by
  have hrw : (stepIoc₀ Ω hb).integralAgainst M t ω
      = ∑ i : Fin 1, (![fun _ => (1 : ℝ)] : Fin 1 → Ω → ℝ) i ω
        * (M (min ((![0, b] : Fin 2 → ℝ) i.succ) t) ω
          - M (min ((![0, b] : Fin 2 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_one]
  simp
/-- The `L²` Itô integral depends on the integrand only through the function itself. -/
theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {F₁ F₂ : Ω → ℝ → ℝ} (hEq : F₁ = F₂)
    (hm₁ : Measurable (Function.uncurry F₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ F₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry F₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ F₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ F₁ hm₁ hp₁ hq₁ t
      = stochasticIntegralBrownian W ℱ hℱ F₂ hm₂ hp₂ hq₂ t := by
  subst hEq; rfl
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
/-- **Locality of the `L²` Itô integral.** Restricting the integrand to `(a, b]` gives the
increment of the integral across `(a, b]`. -/
theorem solution
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (him : Measurable (Function.uncurry fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s))
    (hip : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s) him hip hiq t
      =ᵐ[P] fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min b t) ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min a t) ω := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hfun : (fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s)
        = fun ω s => (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s * H ω s := by
      funext ω s; rw [LevyStochCalc.Brownian.Ito.stepIoc_zero_eval_408915f]
    have hpt : ∀ (ω : Ω) (s : ℝ), (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s
        = (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
      fun ω s => congrFun (congrFun hfun ω) s
    have him' : Measurable
        (Function.uncurry fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s) := by
      rw [hfun]; exact him
    have hip' : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
        (fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s) := by rw [hfun]; exact hip
    have hiq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab).eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hiq T hT
    have hkey := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst_408915f W ℱ hℱ (LevyStochCalc.Brownian.Ito.stepIoc₀ Ω hab)
      (LevyStochCalc.Brownian.Ito.stepIoc₀_adapt ℱ hab) H hm hp hq him' hip' hiq' ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun him' hip' hiq' him hip hiq t] at hkey
    exact hkey.symm.trans
      (Filter.Eventually.of_forall fun ω => LevyStochCalc.Brownian.Ito.stepIoc₀_integralAgainst hab _ t ω)
  · have hfun : (fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s)
        = fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s := by
      funext ω s; rw [LevyStochCalc.Brownian.Ito.stepIoc_eval_408915f]
    have hpt : ∀ (ω : Ω) (s : ℝ), (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s
        = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
      fun ω s => congrFun (congrFun hfun ω) s
    have him' : Measurable
        (Function.uncurry fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s) := by
      rw [hfun]; exact him
    have hip' : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
        (fun ω s => (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s) := by rw [hfun]; exact hip
    have hiq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab).eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hiq T hT
    have hkey := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst_408915f W ℱ hℱ (LevyStochCalc.Brownian.Ito.stepIoc Ω ha' hab)
      (LevyStochCalc.Brownian.Ito.stepIoc_adapt ℱ ha' hab) H hm hp hq him' hip' hiq' ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun him' hip' hiq' him hip hiq t] at hkey
    exact hkey.symm.trans
      (Filter.Eventually.of_forall fun ω => LevyStochCalc.Brownian.Ito.stepIoc_integralAgainst ha' hab _ t ω)
