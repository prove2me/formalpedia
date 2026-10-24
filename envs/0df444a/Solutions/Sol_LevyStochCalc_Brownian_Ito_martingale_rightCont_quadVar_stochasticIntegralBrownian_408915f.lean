-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.martingale_rightCont_quadVar_stochasticIntegralBrownian_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:29:54.581668+00:00
-- url     : https://prove2.me/submissions/1642244d-c120-42ea-961b-3698036d70f0

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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_quadVar_stochasticIntegralBrownian_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_eLpNorm_one_sq_sub_408915f

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
end MasterSequence
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionApi.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include h_meas h_progMeas h_sq_int_global hℱ in
/-- **Conjunct 2 on `rightCont`: `(F)² − ∫₀ᵗH²` is a `rightCont`-martingale.**
The `ℱ`-martingale (`martingale_quadVar_stochasticIntegralBrownian`) lifts
via right-`L¹`-continuity: the `F²`-part is controlled by `F`'s right-`L²`-continuity
(`tendsto_eLpNorm_one_sq_sub`), the compensator part by the horizon slab
`∫⁻∫⁻_{(s,r]}‖H‖² → 0` (`tendsto_setLIntegral_Ioc_prod_zero`). -/
lemma solution :
    MeasureTheory.Martingale
      (fun t ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
      ℱ.rightCont P := by
  refine LevyStochCalc.Martingale.martingale_rightCont_of_tendsto_eLpNorm_one
    (LevyStochCalc.Brownian.Ito.martingale_quadVar_stochasticIntegralBrownian_408915f W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
    (fun s => ?_)
  set F := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global with hFdef
  -- `F²`-part: right-`L¹`-continuity of the square.
  have hF2 : Filter.Tendsto (fun r => MeasureTheory.eLpNorm
      (fun ω => (F r ω) ^ 2 - (F s ω) ^ 2) 1 P) (nhdsWithin s (Set.Ioi s)) (nhds 0) :=
    LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub_408915f (l := nhdsWithin s (Set.Ioi s)) (a := fun r => F r) (b := F s)
      (fun r => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global r).1.aemeasurable)
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global s).1.aemeasurable
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global s).2.ne
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eLpNorm_two_right_tendsto W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global s)
  -- compensator part: right-`L¹`-continuity of `A_t = ∫₀ᵗ H²`.
  have hA : Filter.Tendsto (fun r => MeasureTheory.eLpNorm
      (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
    rcases le_or_gt 0 s with hs | hs
    · have hslab := LevyStochCalc.Brownian.Ito.tendsto_setLIntegral_Ioc_prod_zero (fun ω u => (‖H ω u‖₊ : ℝ≥0∞) ^ 2)
        ((h_meas.nnnorm.coe_nnreal_ennreal).pow_const 2) hs (lt_add_one s)
        (h_sq_int_global (s + 1) (by linarith)).ne
      refine hslab.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hsr : s ≤ r := le_of_lt hr
      have hrpos : 0 < r := lt_of_le_of_lt hs hr
      have hHr : ∀ᵐ ω ∂P, MeasureTheory.Integrable
          (fun u => (H ω u) ^ 2) (volume.restrict (Set.Icc (0 : ℝ) r)) :=
        (LevyStochCalc.Brownian.Ito.compensatorH_memLp_prod H h_meas h_sq_int_global hrpos).integrable_sq.prod_right_ae
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      refine (lintegral_congr_ae ?_).symm
      filter_upwards [hHr] with ω hHrω
      have hHsω : MeasureTheory.Integrable (fun u => (H ω u) ^ 2)
          (volume.restrict (Set.Icc (0 : ℝ) s)) :=
        hHrω.mono_measure (MeasureTheory.Measure.restrict_mono (Set.Icc_subset_Icc_right hsr)
          (le_refl _))
      have hHscω : MeasureTheory.Integrable (fun u => (H ω u) ^ 2)
          (volume.restrict (Set.Ioc s r)) :=
        hHrω.mono_measure (MeasureTheory.Measure.restrict_mono
          (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left hs)) (le_refl _))
      have hsplit : (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume
          = ∫ u in Set.Ioc s r, (H ω u) ^ 2 ∂volume := by
        rw [← Set.Icc_union_Ioc_eq_Icc hs hsr,
          MeasureTheory.setIntegral_union
            (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)))
            measurableSet_Ioc hHsω hHscω]
        ring
      rw [hsplit, ← ofReal_norm, Real.norm_eq_abs,
        abs_of_nonneg (MeasureTheory.integral_nonneg (fun u => sq_nonneg _)),
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hHscω
          (Filter.Eventually.of_forall (fun u => sq_nonneg _))]
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
      rw [show (‖H ω u‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((H ω u) ^ 2) from by
        rw [show (‖H ω u‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H ω u‖ from (ofReal_norm _).symm,
          ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]]
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsGT hs] with r hr
      have hAr : (fun u => (H · u) ^ 2) = (fun u => (H · u) ^ 2) := rfl
      symm
      rw [show (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) = (0 : Ω → ℝ) from by
        funext ω
        rw [Set.Icc_eq_empty (not_le.mpr hr.2), Set.Icc_eq_empty (not_le.mpr hs)]
        simp]
      exact MeasureTheory.eLpNorm_zero
  -- combine the two parts.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hF2.add hA)
    (Filter.Eventually.of_forall (fun r => bot_le)) (Filter.Eventually.of_forall (fun r => ?_))
  have hF2aesm : MeasureTheory.AEStronglyMeasurable (fun ω => (F r ω) ^ 2 - (F s ω) ^ 2) P :=
    (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global r).1.aemeasurable.pow_const
        2).aestronglyMeasurable).sub
      (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global s).1.aemeasurable.pow_const
        2).aestronglyMeasurable)
  have hAaesm : MeasureTheory.AEStronglyMeasurable
      (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) P :=
    ((LevyStochCalc.Brownian.Ito.compensatorH_adapted ℱ H h_progMeas r).mono
      (ℱ.le r)).aestronglyMeasurable.sub
      (((LevyStochCalc.Brownian.Ito.compensatorH_adapted ℱ H h_progMeas s).mono
        (ℱ.le s)).aestronglyMeasurable)
  calc MeasureTheory.eLpNorm
        ((fun t ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) r
          - fun ω => (F s ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P
      = MeasureTheory.eLpNorm
          ((fun ω => (F r ω) ^ 2 - (F s ω) ^ 2)
            - fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
              - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P := by
        refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
        simp only [Pi.sub_apply]; ring
    _ ≤ _ := MeasureTheory.eLpNorm_sub_le hF2aesm hAaesm le_rfl
