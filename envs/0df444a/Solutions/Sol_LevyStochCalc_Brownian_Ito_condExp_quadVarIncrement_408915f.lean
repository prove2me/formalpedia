-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:31:34.572037+00:00
-- url     : https://prove2.me/submissions/fd825dc0-dc13-4015-a1b9-e3016606ceaa

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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_rightCont_quadVar_stochasticIntegralBrownian_408915f

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
section QuadVarIncrement
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hℱ in
/-- The compensated square increment is conditionally centred at its left endpoint. -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    P[LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b | ℱ.rightCont a] =ᵐ[P] 0 := by
  have hMmart := LevyStochCalc.Brownian.Ito.martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H hm hp hq
  have hQmart := LevyStochCalc.Brownian.Ito.martingale_rightCont_quadVar_stochasticIntegralBrownian_408915f W ℱ hℱ H hm hp hq
  have hMmem : ∀ t : ℝ, MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t) 2 P :=
    fun t => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H hm hp hq t
  have hMint : ∀ t : ℝ, Integrable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t) P :=
    fun t => (hMmem t).integrable (by norm_num)
  have hAint : ∀ t : ℝ, 0 ≤ t →
      Integrable (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P :=
    fun t ht => LevyStochCalc.Brownian.Ito.compensatorH_integrable H hm hq ht
  have hMsq : ∀ t : ℝ,
      Integrable (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω) ^ 2) P := by
    intro t
    have hfun : (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω) ^ 2)
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t
          * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact (hMmem t).integrable_mul (hMmem t)
  have hb : (0 : ℝ) ≤ b := ha.trans hab
  -- the three pieces of the decomposition
  have hi1 : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) ^ 2
      - ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume) P := (hMsq b).sub (hAint b hb)
  have hi2 : Integrable (fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
      * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) P :=
    (hMmem a).integrable_mul (hMmem b)
  have hi3 : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
      + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) P := (hMsq a).add (hAint a ha)
  have hdecomp : LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b
      = (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        + ((-2 : ℝ) • fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
            * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω)
        + (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
            + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) := by
    funext ω
    simp only [LevyStochCalc.Brownian.Ito.quadVarIncrement, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- conditional expectations of the three pieces
  have h1 : P[fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume | ℱ.rightCont a]
      =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume := hQmart.2 a b hab
  have h2 : P[fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω | ℱ.rightCont a]
      =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 := by
    have hMa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont a)
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a) := hMmart.1 a
    have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := ℱ.rightCont a)
      hMa hi2 (hMint b)
    have hfun : (fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω)
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a
          * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b := rfl
    rw [hfun]
    filter_upwards [hkey, hMmart.2 a b hab] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', pow_two]
  have h3 : P[fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume | ℱ.rightCont a]
      =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume := by
    refine Filter.EventuallyEq.of_eq (MeasureTheory.condExp_of_stronglyMeasurable
      (ℱ.rightCont.le a) ?_ hi3)
    have hMa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont a)
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a) := hMmart.1 a
    have hAa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont a)
        (fun ω => ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) :=
      (LevyStochCalc.Brownian.Ito.compensatorH_adapted ℱ H hp a).mono (ℱ.le_rightCont a)
    exact ((hMa.measurable.pow_const 2).stronglyMeasurable).add hAa
  -- assemble
  rw [hdecomp]
  have hadd1 := MeasureTheory.condExp_add hi1 (hi2.smul (-2 : ℝ)) (ℱ.rightCont a)
  have hadd2 := MeasureTheory.condExp_add (hi1.add (hi2.smul (-2 : ℝ))) hi3 (ℱ.rightCont a)
  have hsmul := MeasureTheory.condExp_smul (μ := P) (m := ℱ.rightCont a) (-2 : ℝ)
    (fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
      * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω)
  filter_upwards [hadd2, hadd1, hsmul, h1, h2, h3] with ω e2 e1 es f1 f2 f3
  rw [e2, Pi.add_apply, e1, Pi.add_apply, es, Pi.smul_apply, f1, f2, f3, Pi.zero_apply]
  simp only [smul_eq_mul]
  ring
