-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:06:33.17786+00:00
-- url     : https://prove2.me/submissions/10fb730e-6f7f-4076-a5cf-929a6c791462

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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_exists_mul_simple_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_lintegral_eval_sq_lt_top_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_eval_simple_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
/-- A simple integrand is jointly measurable in the form the integral consumes. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.measurable_uncurry_eval {T : ℝ} (G : SimplePredictable Ω T) :
    Measurable (Function.uncurry fun ω s => G.eval s ω) := G.eval_jointly_measurable
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraProduct.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section SimpleVsGeneral
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
include hℱ h_adapt in
/-- **Difference isometry between an elementary integral and an `L²` integral.** -/
theorem LevyStochCalc.Brownian.Ito.isometry_simple_sub_stochasticIntegralBrownian {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖simpleIntegral W G T ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖G.eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hiso := isometry_diff_stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) H
    G.measurable_uncurry_eval hm (G.progressivelyMeasurable_eval ℱ h_adapt) hp
    (G.lintegral_eval_sq_lt_top_408915f P) hq hT
  rw [← hiso]
  refine lintegral_congr_ae ?_
  filter_upwards [stochasticIntegralBrownian_eval_simple_408915f W ℱ hℱ G h_adapt
    G.measurable_uncurry_eval (G.progressivelyMeasurable_eval ℱ h_adapt)
    (G.lintegral_eval_sq_lt_top_408915f P) hT.le] with ω hω
  rw [hω]
end SimpleVsGeneral
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
private lemma LevyStochCalc.Brownian.Ito.eLpNorm_mul_le_of_bound {P : Measure Ω} {c g : Ω → ℝ} {M : ℝ}
    (hM : ∀ ω, |c ω| ≤ M) :
    MeasureTheory.eLpNorm (fun ω => c ω * g ω) 2 P
      ≤ (‖M‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm g 2 P := by
  have hsm : (fun ω => M * g ω) = (M • g : Ω → ℝ) := by funext ω; simp
  refine le_trans (MeasureTheory.eLpNorm_mono (g := fun ω => M * g ω) fun ω => ?_) ?_
  · have hM0 : 0 ≤ M := (abs_nonneg (c ω)).trans (hM ω)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hM0]
    exact mul_le_mul_of_nonneg_right (hM ω) (abs_nonneg _)
  · rw [hsm]; exact MeasureTheory.eLpNorm_const_smul_le
section Associativity
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hmm : Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s))
  (hmp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s)
  (hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hℱ h_adapt in
/-- **Associativity against a simple integrand.** Summing the increments of the `L²` Itô integral
of `H` against the coefficients of a simple integrand `G` gives the `L²` Itô integral of the
product `G · H`. -/
theorem solution {t : ℝ} (ht : 0 < t) :
    G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t
      =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
        hmm hmp hmq t := by
  classical
  obtain ⟨B, hB0, hB⟩ := G.exists_eval_bound
  choose Th Q hQadapt hQeval hQint using fun n : ℕ =>
    LevyStochCalc.Brownian.Ito.SimplePredictable.exists_mul_simple_408915f W ℱ G (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) h_adapt
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H hm hp hq n)
  choose Mb hMb using G.ξ_bounded
  -- measurability bookkeeping
  have hMmeas : ∀ u : ℝ, Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u) :=
    fun u => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq u).mono
      (ℱ.le u)).measurable
  have hInmeas : ∀ (n : ℕ) (u : ℝ),
      Measurable (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) u) := by
    intro n u
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _))
  have hQmeas : ∀ n : ℕ, Measurable (LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t) := by
    intro n
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((Q n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hIAmeas : Measurable (G.integralAgainst
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t) := by
    unfold LevyStochCalc.Brownian.Ito.SimplePredictable.integralAgainst
    exact Finset.measurable_sum _ fun i _ =>
      (G.ξ_measurable i).mul ((hMmeas _).sub (hMmeas _))
  have hconv : ∀ g : Ω → ℝ, MeasureTheory.eLpNorm g 2 P * MeasureTheory.eLpNorm g 2 P
      = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro g
    rw [← LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  -- (d) the product elementary integrals converge to the `L²` integral of `G.eval · H`
  have hd : Filter.Tendsto (fun n => ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    have hbd : ∀ s ω, (‖G.eval s ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal B := by
      intro s ω
      calc (‖G.eval s ω‖₊ : ℝ≥0∞)
          = ENNReal.ofReal ‖G.eval s ω‖ := by
            rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
        _ ≤ ENNReal.ofReal B :=
            ENNReal.ofReal_le_ofReal ((Real.norm_eq_abs _).le.trans (hB s ω))
    have hne : ENNReal.ofReal B ^ 2 ≠ ⊤ := (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
    have hkey : ∀ n, ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
            hmm hmp hmq t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
        ≤ ENNReal.ofReal B ^ 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P := by
      intro n
      rw [LevyStochCalc.Brownian.Ito.isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ (Q n) (hQadapt n)
        (fun ω s => G.eval s ω * H ω s) hmm hmp hmq ht,
        ← MeasureTheory.lintegral_const_mul' _ _ hne]
      refine lintegral_mono fun ω => ?_
      rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
      refine lintegral_mono fun s => ?_
      have hrw : (Q n).eval s ω - G.eval s ω * H ω s
          = G.eval s ω * -(H ω s - (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n).eval s ω) := by
        rw [hQeval n s ω]; ring
      rw [hrw, nnnorm_mul, nnnorm_neg, ENNReal.coe_mul, mul_pow]
      gcongr
      exact hbd s ω
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Filter.Eventually.of_forall fun n => bot_le) (Filter.Eventually.of_forall hkey)
    have hml := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal B ^ 2)
      (LevyStochCalc.Brownian.Ito.masterApprox_eval_tendsto (t := t) ℱ H hm hp hq) (Or.inr hne)
    simpa using hml
  -- (e) the product elementary integrals converge to the integral against the `L²` integral
  have hu_nn : ∀ i : Fin G.N, 0 ≤ min (G.partition i.succ) t :=
    fun i => le_min (G.partition_nonneg _) ht.le
  have hu_nn' : ∀ i : Fin G.N, 0 ≤ min (G.partition i.castSucc) t :=
    fun i => le_min (G.partition_nonneg _) ht.le
  have hstep : ∀ n : ℕ, (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
      - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω)
      = ∑ i : Fin G.N,
        ((fun ω => G.ξ i ω * (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n)
            (min (G.partition i.succ) t) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω))
        - (fun ω => G.ξ i ω * (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n)
            (min (G.partition i.castSucc) t) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
              (min (G.partition i.castSucc) t) ω))) := by
    intro n
    funext ω
    simp only [Finset.sum_apply, Pi.sub_apply]
    rw [← hQint n t ω]
    unfold LevyStochCalc.Brownian.Ito.SimplePredictable.integralAgainst
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbound : ∀ n : ℕ, MeasureTheory.eLpNorm (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
      - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω) 2 P
      ≤ ∑ i : Fin G.N, ((‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) (min (G.partition i.succ) t) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω) 2 P
        + (‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) (min (G.partition i.castSucc) t) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
                (min (G.partition i.castSucc) t) ω) 2 P) := by
    intro n
    have haesm : ∀ (i : Fin G.N) (u : ℝ), MeasureTheory.AEStronglyMeasurable
        (fun ω => G.ξ i ω * (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) u ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)) P :=
      fun i u => ((G.ξ_measurable i).mul ((hInmeas n u).sub (hMmeas u))).aestronglyMeasurable
    rw [hstep n]
    refine le_trans (MeasureTheory.eLpNorm_sum_le
      (fun i _ => (haesm i _).sub (haesm i _)) (by norm_num)) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (MeasureTheory.eLpNorm_sub_le (haesm i _) (haesm i _) (by norm_num)) ?_
    exact add_le_add (eLpNorm_mul_le_of_bound (hMb i)) (eLpNorm_mul_le_of_bound (hMb i))
  have hlim : Filter.Tendsto (fun n : ℕ =>
      ∑ i : Fin G.N, ((‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) (min (G.partition i.succ) t) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω) 2 P
        + (‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hm hp hq n) (min (G.partition i.castSucc) t) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
                (min (G.partition i.castSucc) t) ω) 2 P)) Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ≥0∞) = ∑ _i : Fin G.N, (0 : ℝ≥0∞) := by simp
    rw [h0]
    refine tendsto_finsetSum _ fun i _ => ?_
    have h1 := ENNReal.Tendsto.const_mul (a := (‖Mb i‖₊ : ℝ≥0∞))
      (LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2 W ℱ hℱ H hm hp hq (hu_nn i)) (Or.inr ENNReal.coe_ne_top)
    have h2 := ENNReal.Tendsto.const_mul (a := (‖Mb i‖₊ : ℝ≥0∞))
      (LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2 W ℱ hℱ H hm hp hq (hu_nn' i)) (Or.inr ENNReal.coe_ne_top)
    simpa using h1.add h2
  have heL : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω =>
      LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
        - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω) 2 P)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall hbound)
  have he : Filter.Tendsto (fun n => ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
      - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    have h2 := ENNReal.Tendsto.mul heL (Or.inr (by simp)) heL (Or.inr (by simp))
    simpa [hconv] using h2
  -- squeeze the two limits together
  have hle : ∫⁻ ω,
      (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P ≤ 0 := by
    have hlim2 : Filter.Tendsto (fun n => 2 * ((∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
          - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
            : ℝ≥0∞) ^ 2 ∂P)
        + ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
              hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)) Filter.atTop (nhds 0) := by
      have h3 := ENNReal.Tendsto.const_mul (a := 2) (he.add hd) (Or.inr (by simp))
      simpa using h3
    refine ge_of_tendsto hlim2 (Filter.Eventually.of_forall fun n => ?_)
    have hm2 : AEMeasurable (fun ω => (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
        - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
          : ℝ≥0∞) ^ 2) P :=
      ((((hQmeas n).sub hIAmeas).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.aemeasurable
    calc ∫⁻ ω, (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
              hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * ((‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
              - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
                : ℝ≥0∞) ^ 2
            + (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                  hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hrw : G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
                - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                    hmm hmp hmq t ω
              = -(LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
                    - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω)
                + (LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
                    - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                        hmm hmp hmq t ω) := by ring
          rw [hrw]
          refine le_trans (LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul_brownian _ _) ?_
          rw [nnnorm_neg]
      _ = 2 * ((∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
              - G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
                : ℝ≥0∞) ^ 2 ∂P)
            + ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) t ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                  hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) := by
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hm2]
  have hzero : ∫⁻ ω,
      (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P = 0 := le_antisymm hle bot_le
  have hSIm : Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => G.eval s ω * H ω s) hmm hmp hmq t) :=
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
      hmm hmp hmq t).mono (ℱ.le t)).measurable
  have hmeas : Measurable fun ω =>
      (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
            hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 :=
    (((hIAmeas.sub hSIm).nnnorm).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hzero] with ω hω
  have h0 : (‖G.integralAgainst (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  simpa [sub_eq_zero] using h0
