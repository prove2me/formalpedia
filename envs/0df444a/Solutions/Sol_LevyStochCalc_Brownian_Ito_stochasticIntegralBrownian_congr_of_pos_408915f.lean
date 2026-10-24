-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:10:42.225277+00:00
-- url     : https://prove2.me/submissions/4de04754-63d6-4ead-a64d-c1d2f7adbfe3

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoLocality
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoOptionalStopping
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
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_StoppedProgressive
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
import Mathlib.Probability.Process.Stopping
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIoc_zero_eval_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_indicator_Ioc_408915f

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
theorem LevyStochCalc.Brownian.Ito.stepIoc₀_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ} (hb : 0 < b) :
    ∀ i : Fin (stepIoc₀ Ω hb).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIoc₀ Ω hb).partition i.castSucc)) ((stepIoc₀ Ω hb).ξ i) := by
  intro i
  fin_cases i
  exact MeasureTheory.stronglyMeasurable_const
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

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section Indicator
theorem LevyStochCalc.Brownian.Ito.indIoc_le_one (a b : ℝ) (ω : Ω) (s : ℝ) : |indIoc Ω a b ω s| ≤ 1 := by
  unfold indIoc
  by_cases h : s ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num
theorem LevyStochCalc.Brownian.Ito.measurable_uncurry_indIoc (a b : ℝ) :
    Measurable (Function.uncurry (indIoc Ω a b)) :=
  ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd)
theorem LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indIoc₀ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ}
    (hb : 0 < b) : Probability.ProgressivelyMeasurable ℱ (indIoc Ω 0 b) := by
  have hfun : indIoc Ω 0 b = fun ω s => (stepIoc₀ Ω hb).eval s ω := by
    funext ω s; rw [stepIoc_zero_eval_408915f]; rfl
  rw [hfun]
  exact (stepIoc₀ Ω hb).progressivelyMeasurable_eval ℱ (stepIoc₀_adapt ℱ hb)
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
end Indicator
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)
section Local
variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
/-- **The Itô integral to a positive time sees the integrand only at positive times.** -/
theorem solution
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → H₁ ω s = H₂ ω s)
    {t : ℝ} (ht : 0 < t) :
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t
      =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t := by
  classical
  have hle1 : ∀ (H : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ),
      |(Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ |H ω s| := by
    intro H ω s
    rw [abs_mul]
    refine mul_le_of_le_one_left (abs_nonneg _) ?_
    simpa [LevyStochCalc.Brownian.Ito.indIoc] using LevyStochCalc.Brownian.Ito.indIoc_le_one (Ω := Ω) 0 t ω s
  have hmI : ∀ {H : Ω → ℝ → ℝ}, Measurable (Function.uncurry H) →
      Measurable (Function.uncurry fun ω s =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s) :=
    fun hm => (LevyStochCalc.Brownian.Ito.measurable_uncurry_indIoc (Ω := Ω) 0 t).mul hm
  have hpI : ∀ {H : Ω → ℝ → ℝ}, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H →
      LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (fun ω s =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s) :=
    fun hp => (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indIoc₀ ℱ ht).mul hp
  have hqI : ∀ {H : Ω → ℝ → ℝ}, (∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) →
      ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ :=
    fun {H} hq => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (hle1 H) hq
  have key : ∀ (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
      (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
      (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H ω s)
          (hmI hm) (hpI hp) (hqI hq) t
        =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
    intro H hm hp hq
    have hsplit := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc_408915f W ℱ hℱ H hm hp hq
      (le_refl (0 : ℝ)) ht (hmI hm) (hpI hp) (hqI hq) ht
    have hz := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H hm hp hq (le_refl (0 : ℝ))
    filter_upwards [hsplit, hz] with ω hω hω0
    rw [hω, min_self, min_eq_left ht.le]
    simpa using hω0
  have hfun : (fun (ω : Ω) (s : ℝ) =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H₁ ω s)
      = fun ω s => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * H₂ ω s := by
    funext ω s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) t
    · rw [hagree ω s hs.1]
    · rw [Set.indicator_of_notMem hs, zero_mul, zero_mul]
  have hcongr := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun
    (hmI hm₁) (hpI hp₁) (hqI hq₁) (hmI hm₂) (hpI hp₂) (hqI hq₂) t
  refine ((key H₁ hm₁ hp₁ hq₁).symm.trans ?_).trans (key H₂ hm₂ hp₂ hq₂)
  rw [hcongr]
