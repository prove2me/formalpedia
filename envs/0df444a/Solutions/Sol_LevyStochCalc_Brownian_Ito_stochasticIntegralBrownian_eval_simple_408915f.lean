-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eval_simple_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:04:09.905633+00:00
-- url     : https://prove2.me/submissions/0abf53d8-ca19-44e7-85e3-cebe648ce468

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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_simpleIntegral_diff_isometry_of_adapted_408915f

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
section EvalSimple
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (hm : Measurable (Function.uncurry fun ω s => G.eval s ω))
  (hp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hℱ h_adapt in
/-- **The `L²` Itô integral of a simple integrand is its elementary integral.** -/
theorem solution {t : ℝ} (ht : 0 ≤ t) :
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t
      =ᵐ[P] LevyStochCalc.Brownian.Ito.simpleIntegral W G t := by
  classical
  have hIn : ∀ n : ℕ, Measurable
      (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t) := by
    intro n
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _))
  have hIG : Measurable (LevyStochCalc.Brownian.Ito.simpleIntegral W G t) := by
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      (G.ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hSI : Measurable
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t) :=
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ (fun ω s => G.eval s ω) hm
      hp hq t).mono (ℱ.le t)).measurable
  -- the master integrals converge to the elementary integral of `G`
  have hA : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
        - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    refine (LevyStochCalc.Brownian.Ito.masterApprox_eval_tendsto (t := t) ℱ (fun ω s => G.eval s ω) hm hp hq).congr
      fun n => ?_
    rw [LevyStochCalc.Brownian.Ito.simpleIntegral_diff_isometry_of_adapted_408915f W ℱ hℱ _ G
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ (fun ω s => G.eval s ω) hm hp hq n) h_adapt ht]
    refine lintegral_congr fun ω =>
      MeasureTheory.setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    rw [← nnnorm_neg, neg_sub]
  -- and to the `L²` Itô integral
  have hconv : ∀ g : Ω → ℝ, MeasureTheory.eLpNorm g 2 P * MeasureTheory.eLpNorm g 2 P
      = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro g
    rw [← LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  have hB : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    have h := LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2 W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq ht
    have h2 := ENNReal.Tendsto.mul h (Or.inr (by simp)) h (Or.inr (by simp))
    simpa [hconv] using h2
  -- squeeze
  have hle : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
      hq t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ 0 := by
    have hlim : Filter.Tendsto (fun n => 2 * ((∫⁻ ω,
        (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
            hq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
            hq n) t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P))
        Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul (a := 2) (hB.add hA) (Or.inr (by simp))
      simpa using this
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
    calc ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
          hq t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * ((‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm
              hp hq n) t ω - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
              (fun ω s => G.eval s ω) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2
            + (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
              hq n) t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hrw : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
                hq t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω
              = -(LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
                  hq n) t ω - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω)
                  hm hp hq t ω)
                + (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
                  hq n) t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) := by ring
          rw [hrw]
          refine le_trans (LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul_brownian _ _) ?_
          rw [nnnorm_neg]
      _ = 2 * ((∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm
              hp hq n) t ω - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
              (fun ω s => G.eval s ω) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
            + ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
              hq n) t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) := by
          have hm2 : AEMeasurable (fun ω => (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ
              (fun ω s => G.eval s ω) hm hp hq n) t ω
                - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
                  hq t ω‖₊ : ℝ≥0∞) ^ 2) P :=
            ((((hIn n).sub hSI).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.aemeasurable
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hm2]
  have hzero : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm
      hp hq t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 :=
    le_antisymm hle bot_le
  have hmeas : Measurable fun ω => (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => G.eval s ω) hm hp hq t ω
        - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 :=
    (((hSI.sub hIG).nnnorm).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hzero] with ω hω
  have h0 : (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t ω
      - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  simpa [sub_eq_zero] using h0
