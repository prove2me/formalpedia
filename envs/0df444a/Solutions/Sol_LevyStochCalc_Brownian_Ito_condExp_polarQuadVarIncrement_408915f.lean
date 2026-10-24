-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.condExp_polarQuadVarIncrement_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:33:19.108033+00:00
-- url     : https://prove2.me/submissions/57720803-18c0-47f9-b548-e5dbedf63aab

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentLintegral
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoIncrementMomentRestrict
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionApi
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoQuadVarSum
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_PolarisedQuadVar
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_compensator_add_sq_eq_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_compensator_sub_bounds_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_condExp_quadVarIncrement_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_memLp_two_sq_increment_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_add_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section MasterSequence
variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
include h_meas h_sq_int_global in
/-- The `H`-compensator `A_t = ∫₀ᵗ H² ds` is `P`-integrable (`t ≥ 0`). -/
lemma LevyStochCalc.Brownian.Ito.compensatorH_integrable {t : ℝ} (ht : 0 ≤ t) :
    MeasureTheory.Integrable (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · exact (compensatorH_memLp_prod H h_meas h_sq_int_global ht').integrable_sq.integral_prod_left
  · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
      funext ω; rw [← ht', Set.Icc_self, MeasureTheory.setIntegral_measure_zero _ (by simp)]
    rw [heq]; exact MeasureTheory.integrable_const 0
end MasterSequence
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoQuadVarSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section IncrementL2
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hm hq hC0 hCH in
/-- The compensator increment lies in `L²`. -/
theorem LevyStochCalc.Brownian.Ito.memLp_two_compensator_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MemLp (fun ω => (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
      - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) 2 P := by
  have hint := ((compensatorH_integrable H hm hq (ha.trans hab)).sub
    (compensatorH_integrable H hm hq ha))
  refine MeasureTheory.MemLp.of_bound hint.aestronglyMeasurable (C ^ 2 * (b - a)) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  obtain ⟨h1, h2⟩ := compensator_sub_bounds_408915f H hm hC0 hCH ha hab ω
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  exact h2
include hℱ hC0 hCH in
/-- The compensated square increment lies in `L²`. -/
theorem LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (quadVarIncrement W ℱ hℱ H hm hp hq a b) 2 P :=
  (memLp_two_sq_increment_408915f W ℱ hℱ H hm hp hq hC0 hCH ha hab).sub
    (memLp_two_compensator_sub H hm hq hC0 hCH ha hab.le)
end IncrementL2
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/PolarisedQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section Polarised
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H₁ H₂ : Ω → ℝ → ℝ)
  (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
  (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
  (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
  (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
  (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
  (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
include hℱ in
/-- Additivity of the Itô integral in the integrand, at every nonnegative time. -/
theorem LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_add_ae_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
        + stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · filter_upwards [stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ
        (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa (le_refl (0 : ℝ)),
      stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H₁ hm₁ hp₁ hq₁ (le_refl (0 : ℝ)),
      stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H₂ hm₂ hp₂ hq₂ (le_refl (0 : ℝ))]
      with ω e0 e1 e2
    rw [e0, e1, e2, Pi.zero_apply, add_zero]
  · exact stochasticIntegralBrownian_add_408915f W ℱ hℱ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hma hpa hqa ht'
section Bounds
variable {C : ℝ} (hC0 : 0 ≤ C) (hCH₁ : ∀ ω s, |H₁ ω s| ≤ C) (hCH₂ : ∀ ω s, |H₂ ω s| ≤ C)
include hℱ hC0 hCH₁ hCH₂ in
/-- **Polarisation.** Twice the compensated product is the compensated square increment of
`H₁ + H₂` less those of `H₁` and of `H₂`. -/
theorem LevyStochCalc.Brownian.Ito.smul_two_polarQuadVarIncrement_ae {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (2 : ℝ) • polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b
      =ᵐ[P] fun ω =>
        quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
          - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
          - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω := by
  have hb : (0 : ℝ) ≤ b := ha.trans hab
  filter_upwards [stochasticIntegralBrownian_add_ae_of_nonneg W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂
      hq₁ hq₂ hma hpa hqa hb,
    stochasticIntegralBrownian_add_ae_of_nonneg W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
      hma hpa hqa ha] with ω eb ea
  simp only [Pi.smul_apply, smul_eq_mul, polarQuadVarIncrement, quadVarIncrement]
  rw [eb, ea, compensator_add_sq_eq_408915f H₁ H₂ hm₁ hm₂ hC0 hCH₁ hCH₂ ω,
    compensator_add_sq_eq_408915f H₁ H₂ hm₁ hm₂ hC0 hCH₁ hCH₂ ω]
  ring
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hℱ hma hpa hqa hC0 hCH₁ hCH₂ in
/-- **The compensated product is conditionally centred at the left endpoint.** -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b | ℱ.rightCont a]
      =ᵐ[P] 0 := by
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  have hb₁ : ∀ ω s, |H₁ ω s| ≤ 2 * C := fun ω s => (hCH₁ ω s).trans (by linarith)
  have hb₂ : ∀ ω s, |H₂ ω s| ≤ 2 * C := fun ω s => (hCH₂ ω s).trans (by linarith)
  have hba : ∀ ω s, |H₁ ω s + H₂ ω s| ≤ 2 * C := fun ω s =>
    (abs_add_le _ _).trans (by linarith [hCH₁ ω s, hCH₂ ω s])
  have iAdd := (LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab).integrable (by norm_num)
  have i₁ := (LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab).integrable
    (by norm_num)
  have i₂ := (LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab).integrable
    (by norm_num)
  have cAdd := LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement_408915f W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa ha hab.le
  have c₁ := LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement_408915f W ℱ hℱ H₁ hm₁ hp₁ hq₁ ha hab.le
  have c₂ := LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement_408915f W ℱ hℱ H₂ hm₂ hp₂ hq₂ ha hab.le
  have e1 := MeasureTheory.condExp_sub (iAdd.sub i₁) i₂ (ℱ.rightCont a)
  have e2 := MeasureTheory.condExp_sub iAdd i₁ (ℱ.rightCont a)
  have hcond0 : P[LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b
        - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b
        - LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b | ℱ.rightCont a] =ᵐ[P] 0 := by
    filter_upwards [e1, e2, cAdd, c₁, c₂] with ω h1 h2 hA hh1 hh2
    rw [h1, Pi.sub_apply, h2, Pi.sub_apply, hA, hh1, hh2, Pi.zero_apply]
    ring
  have hpol := LevyStochCalc.Brownian.Ito.smul_two_polarQuadVarIncrement_ae W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab.le
  have hkey := (MeasureTheory.condExp_congr_ae hpol).trans hcond0
  have hsm := MeasureTheory.condExp_smul (μ := P) (m := ℱ.rightCont a) (2 : ℝ)
    (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b)
  filter_upwards [hkey, hsm] with ω h1 h2
  rw [h2, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  rw [Pi.zero_apply]
  linarith
