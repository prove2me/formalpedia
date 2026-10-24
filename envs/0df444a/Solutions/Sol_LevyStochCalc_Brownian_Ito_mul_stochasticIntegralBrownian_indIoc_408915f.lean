-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_indIoc_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:10:55.432833+00:00
-- url     : https://prove2.me/submissions/3ca9c269-33cd-4857-8f49-41c36ff36355

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionApi
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoPullOut
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIocMul_eval_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIocMul_zero_eval_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_indicator_Ioc_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_integralAgainst_408915f

section
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
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoPullOut.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
theorem LevyStochCalc.Brownian.Ito.stepIocMul_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V) :
    ∀ i : Fin (stepIocMul Ω ha hab V hVb hVm).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocMul Ω ha hab V hVb hVm).partition i.castSucc))
      ((stepIocMul Ω ha hab V hVb hVm).ξ i) := by
  intro i
  fin_cases i
  · exact MeasureTheory.stronglyMeasurable_const
  · exact hVa
theorem LevyStochCalc.Brownian.Ito.stepIocMul₀_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ} (hb : 0 < b)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ 0) V) :
    ∀ i : Fin (stepIocMul₀ Ω hb V hVb hVm).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocMul₀ Ω hb V hVb hVm).partition i.castSucc))
      ((stepIocMul₀ Ω hb V hVb hVm).ξ i) := by
  intro i
  fin_cases i
  exact hVa
theorem LevyStochCalc.Brownian.Ito.stepIocMul_integralAgainst {a b : ℝ} (ha : 0 < a) (hab : a < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (stepIocMul Ω ha hab V hVb hVm).integralAgainst M t ω
      = V ω * (M (min b t) ω - M (min a t) ω) := by
  have hrw : (stepIocMul Ω ha hab V hVb hVm).integralAgainst M t ω
      = ∑ i : Fin 2, (![fun _ => (0 : ℝ), V] : Fin 2 → Ω → ℝ) i ω
        * (M (min ((![0, a, b] : Fin 3 → ℝ) i.succ) t) ω
          - M (min ((![0, a, b] : Fin 3 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_two]
  simp
theorem LevyStochCalc.Brownian.Ito.stepIocMul₀_integralAgainst {b : ℝ} (hb : 0 < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (stepIocMul₀ Ω hb V hVb hVm).integralAgainst M t ω
      = V ω * (M (min b t) ω - M (min 0 t) ω) := by
  have hrw : (stepIocMul₀ Ω hb V hVb hVm).integralAgainst M t ω
      = ∑ i : Fin 1, (![V] : Fin 1 → Ω → ℝ) i ω
        * (M (min ((![0, b] : Fin 2 → ℝ) i.succ) t) ω
          - M (min ((![0, b] : Fin 2 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_one]
  simp
section PullOut
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hℱ in
/-- **A past weight passes inside an Itô integral over a window.** For `V` bounded and
`ℱ_a`-measurable and an integrand restricted to `(a, b]`, multiplying by `V` outside the integral
is the same as multiplying the integrand by `V`. -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
    (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (him : Measurable (Function.uncurry fun ω s => LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s))
    (hip : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hvm : Measurable (Function.uncurry fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s))
    (hvp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s)
    (hvq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    (fun ω => V ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s) him hip hiq t ω)
      =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s) hvm hvp hvq t := by
  have hloc := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc_408915f W ℱ hℱ K hm hp hq ha hab him hip hiq ht
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hpt : ∀ (ω : Ω) (s : ℝ),
        (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s
          = V ω * LevyStochCalc.Brownian.Ito.indIoc Ω 0 b ω s * K ω s := by
      intro ω s; rw [LevyStochCalc.Brownian.Ito.stepIocMul_zero_eval_408915f]
    have hGeval : (fun ω s => (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s)
        = fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω 0 b ω s * K ω s := by
      funext ω s; exact hpt ω s
    have hmm : Measurable (Function.uncurry fun ω s =>
        (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s) := by rw [hGeval]; exact hvm
    have hmp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s =>
        (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s := by rw [hGeval]; exact hvp
    have hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hvq T hT
    have hass := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst_408915f W ℱ hℱ
      (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm) (LevyStochCalc.Brownian.Ito.stepIocMul₀_adapt ℱ hab hVb hVm hVa) K hm hp hq
      hmm hmp hmq ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hGeval hmm hmp hmq hvm hvp hvq t] at hass
    refine Filter.EventuallyEq.trans ?_ hass
    filter_upwards [hloc] with ω hω
    rw [LevyStochCalc.Brownian.Ito.stepIocMul₀_integralAgainst]
    exact congrArg (fun x => V ω * x) hω
  · have hpt : ∀ (ω : Ω) (s : ℝ),
        (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s
          = V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s := by
      intro ω s; rw [LevyStochCalc.Brownian.Ito.stepIocMul_eval_408915f]
    have hGeval : (fun ω s => (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s)
        = fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s := by
      funext ω s; exact hpt ω s
    have hmm : Measurable (Function.uncurry fun ω s =>
        (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s) := by rw [hGeval]; exact hvm
    have hmp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s =>
        (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s := by rw [hGeval]; exact hvp
    have hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hvq T hT
    have hass := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst_408915f W ℱ hℱ
      (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm) (LevyStochCalc.Brownian.Ito.stepIocMul_adapt ℱ ha' hab hVb hVm hVa) K hm hp hq
      hmm hmp hmq ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hGeval hmm hmp hmq hvm hvp hvq t] at hass
    refine Filter.EventuallyEq.trans ?_ hass
    filter_upwards [hloc] with ω hω
    rw [LevyStochCalc.Brownian.Ito.stepIocMul_integralAgainst]
    exact congrArg (fun x => V ω * x) hω
