-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.martingale_quadVar_stochasticIntegralBrownian_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:28:24.204077+00:00
-- url     : https://prove2.me/submissions/3b83ea2d-cbb7-43a5-9066-2c70db533e4c

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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_simpleIntegral_sq_sub_compensator_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_masterApprox_compensator_tendsto_L1_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_setIntegral_eval_sq_Icc_clamped_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_eLpNorm_one_sq_sub_408915f

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
include h_progMeas in
/-- The `H`-compensator `A_t = ∫₀ᵗ H² ds` is `ℱ_t`-adapted. -/
lemma LevyStochCalc.Brownian.Ito.compensatorH_adapted (t : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) := by
  rcases le_or_gt 0 t with ht | ht
  · have hsq : Probability.ProgressivelyMeasurable ℱ fun ω s => (H ω s) ^ 2 :=
      (continuous_pow 2).comp_progressivelyMeasurable (by simp) h_progMeas
    exact hsq.stronglyMeasurable_setIntegral measurableSet_Icc Set.Icc_subset_Iic_self volume
  · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
      funext ω; rw [Set.Icc_eq_empty (not_le.mpr ht)]; simp
    rw [heq]; exact stronglyMeasurable_const
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include h_meas h_progMeas h_sq_int_global hℱ in
/-- **Conjunct 2: the compensated square is a martingale.**
`t ↦ (F t)² − ∫₀ᵗ H² ds` is an `ℱ`-martingale. The simple-level
compensated squares `martingale_simpleIntegral_sq_sub_compensator` (for `masterApprox n`)
are martingales converging in `L¹` to the `F`-process: the integrand-squares converge
(`masterApprox_tendsto_L2` + `tendsto_eLpNorm_one_sq_sub`) and the compensators
converge (`masterApprox_compensator_tendsto_L1`). -/
lemma solution :
    MeasureTheory.Martingale
      (fun t ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
      ℱ P := by
  set F := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global with hF
  have hAHint : ∀ t, MeasureTheory.Integrable
      (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact LevyStochCalc.Brownian.Ito.compensatorH_integrable H h_meas h_sq_int_global ht
    · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
        funext ω; rw [Set.Icc_eq_empty (not_le.mpr ht)]; simp
      rw [heq]; exact MeasureTheory.integrable_const 0
  refine LevyStochCalc.Brownian.Ito.martingale_of_tendsto_eLpNorm_one
    (M := fun n t ω =>
      (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t,
            ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
    (fun n => LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_sq_sub_compensator_408915f W ℱ hℱ (LevyStochCalc.Brownian.Ito.master_horizon_pos n)
      (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n))
    (fun n t => (LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_sq_sub_compensator_408915f W ℱ hℱ (LevyStochCalc.Brownian.Ito.master_horizon_pos n)
      (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n)).integrable t)
    (fun t => ?_) (fun t => ?_) (fun t => ?_)
  · -- StronglyAdapted
    have hFsq : @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ t) (fun ω => (F t ω) ^ 2) := by
      simpa [pow_two, Pi.mul_def] using
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global t).mul
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas h_sq_int_global t)
    exact hFsq.sub (LevyStochCalc.Brownian.Ito.compensatorH_adapted ℱ H h_progMeas t)
  · -- integrability of the F-process at each `t`
    exact ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t).integrable_sq).sub
      (hAHint t)
  · -- `L¹`-convergence of the simple compensated squares to the F-process
    rcases le_or_gt 0 t with ht | ht
    · have hX : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
          (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
            h_sq_int_global n) t ω) ^ 2
            - (F t ω) ^ 2) 1 P) Filter.atTop (nhds 0) :=
        LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub_408915f
          (fun n => (Finset.measurable_sum _ (fun i _ =>
            ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).mul
              ((W.measurable_eval _).sub (W.measurable_eval _)))).aemeasurable)
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
            h_sq_int_global t).1.aemeasurable
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).2.ne
          (LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2 W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht)
      have hY := LevyStochCalc.Brownian.Ito.masterApprox_compensator_tendsto_L1_408915f ℱ H h_meas h_progMeas h_sq_int_global ht
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using hX.add hY)
        (Filter.Eventually.of_forall (fun n => bot_le))
        (Filter.Eventually.of_forall (fun n => ?_))
      have hXaesm : MeasureTheory.AEStronglyMeasurable
          (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
            h_sq_int_global n) t ω) ^ 2
            - (F t ω) ^ 2) P :=
        (((Finset.measurable_sum _ (fun i _ =>
          ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).mul
            ((W.measurable_eval _).sub (W.measurable_eval _)))).pow_const
              2).aestronglyMeasurable).sub
          ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
            h_sq_int_global t).1.aemeasurable.pow_const 2).aestronglyMeasurable
      have hAn_meas : Measurable (fun ω => ∫ u in Set.Icc (0 : ℝ) t,
          ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume) := by
        rw [show (fun ω => ∫ u in Set.Icc (0 : ℝ) t,
              ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
            = fun ω => ∑ i : Fin (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).N,
                (min ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).partition i.succ) t
                  - min ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).partition
                      i.castSucc) t)
                  * ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ i ω) ^ 2 from
          funext (fun ω => LevyStochCalc.Brownian.Ito.setIntegral_eval_sq_Icc_clamped_408915f
            (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) ω)]
        exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
          (((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).pow_const 2))
      have hYaesm : MeasureTheory.AEStronglyMeasurable
          (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
              ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P :=
        hAn_meas.aestronglyMeasurable.sub (hAHint t).aestronglyMeasurable
      calc MeasureTheory.eLpNorm
            ((fun t' ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
              h_sq_int_global n) t' ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t', ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                  h_sq_int_global n).eval u ω) ^ 2 ∂volume) t
              - fun ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P
          = MeasureTheory.eLpNorm
              ((fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                h_sq_int_global n) t ω) ^ 2
                  - (F t ω) ^ 2)
                - fun ω => (∫ u in Set.Icc (0 : ℝ) t,
                    ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
                  - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P := by
            refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
            simp only [Pi.sub_apply]; ring
        _ ≤ _ := MeasureTheory.eLpNorm_sub_le hXaesm hYaesm le_rfl
    · have hzero : ∀ n, MeasureTheory.eLpNorm
          ((fun t' ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
            h_sq_int_global n) t' ω) ^ 2
              - ∫ u in Set.Icc (0 : ℝ) t', ((LevyStochCalc.Brownian.Ito.masterApprox ℱ H h_meas h_progMeas
                h_sq_int_global n).eval u ω) ^ 2 ∂volume) t
            - fun ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P = 0 := by
        intro n
        refine (MeasureTheory.eLpNorm_eq_zero_of_ae_zero ?_)
        filter_upwards [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global ht] with ω hF0
        simp only [Pi.sub_apply, Pi.zero_apply,
          LevyStochCalc.Brownian.Ito.simpleIntegral_eq_zero_of_nonpos W _ (le_of_lt ht) ω, hF, hF0,
          Set.Icc_eq_empty (not_le.mpr ht)]
        simp
      simp only [hzero]; exact tendsto_const_nhds
