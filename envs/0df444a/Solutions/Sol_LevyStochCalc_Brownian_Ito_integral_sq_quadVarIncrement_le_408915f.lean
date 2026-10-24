-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:28:52.966244+00:00
-- url     : https://prove2.me/submissions/c1d87dbd-8fe6-48ff-9203-3e6ce01c179a

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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_compensator_sub_bounds_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_stochasticIntegralBrownian_sub_pow_four_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_memLp_two_sq_increment_408915f

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
theorem LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg : 0 ≤ gaussianFourthMoment :=
  integral_nonneg fun x => by positivity
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
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hℱ hC0 hCH in
/-- Second moment of the compensated square increment. -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2 ∂P
      ≤ (2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * C ^ 4 * (b - a) ^ 2 := by
  have hcg : (0 : ℝ) ≤ LevyStochCalc.Brownian.Ito.gaussianFourthMoment := LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hXmem := LevyStochCalc.Brownian.Ito.memLp_two_sq_increment_408915f W ℱ hℱ H hm hp hq hC0 hCH ha hab
  have hYmem := LevyStochCalc.Brownian.Ito.memLp_two_compensator_sub H hm hq hC0 hCH ha hab.le
  have hXint : Integrable (fun ω => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2) P := by
    have hfun : (fun ω => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
        = (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2)
          * (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact hXmem.integrable_mul hXmem
  have hYint : Integrable (fun ω => ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
      - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2) P := by
    have hfun : (fun ω => ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2)
        = (fun ω => (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume)
          * (fun ω => (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact hYmem.integrable_mul hYmem
  -- the fourth moment of the increment
  have hX : ∫ ω, ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2 ∂P
      ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by
    have hK : (0 : ℝ) ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by positivity
    have heq : ENNReal.ofReal (∫ ω, ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2) ∂P :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hXint
        (Filter.Eventually.of_forall fun ω => by positivity)
    have hpt : ∀ ω : Ω, ENNReal.ofReal (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
        = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
      have key : ∀ x : ℝ, ENNReal.ofReal ((x ^ 2) ^ 2) = (‖x‖₊ : ℝ≥0∞) ^ 4 := by
        intro x
        have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
          rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
          exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
        rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
        congr 1
        ring
      exact fun ω => key _
    rw [← ENNReal.ofReal_le_ofReal_iff hK, heq]
    simp_rw [hpt]
    exact LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_pow_four_le_408915f W ℱ hℱ H hm hp hq hC0 hCH ha hab
  -- the compensator increment
  have hY : ∫ ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ∂P
      ≤ C ^ 4 * (b - a) ^ 2 := by
    have hbnd : ∀ ω : Ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ≤ C ^ 4 * (b - a) ^ 2 := by
      intro ω
      obtain ⟨h1, h2⟩ := LevyStochCalc.Brownian.Ito.compensator_sub_bounds_408915f H hm hC0 hCH ha hab.le ω
      nlinarith [sq_nonneg C, mul_nonneg (mul_nonneg hC0 hC0) hba]
    calc ∫ ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ∂P
        ≤ ∫ _ω : Ω, C ^ 4 * (b - a) ^ 2 ∂P :=
          MeasureTheory.integral_mono hYint (integrable_const _) hbnd
      _ = C ^ 4 * (b - a) ^ 2 := by simp
  -- combine
  have hptwise : ∀ ω : Ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2
      ≤ 2 * (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
        + 2 * (((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2) := by
    intro ω
    simp only [LevyStochCalc.Brownian.Ito.quadVarIncrement]
    nlinarith [sq_nonneg ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
      + ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume))]
  have hζint : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2) P := by
    have hmem := LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H hm hp hq hC0 hCH ha hab
    have hfun : (fun ω => (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2)
        = LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact hmem.integrable_mul hmem
  calc ∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2 ∂P
      ≤ ∫ ω, (2 * (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
          + 2 * (((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2)) ∂P :=
        MeasureTheory.integral_mono hζint ((hXint.const_mul 2).add (hYint.const_mul 2)) hptwise
    _ = 2 * (∫ ω, ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2 ∂P)
          + 2 * (∫ ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ∂P) := by
        rw [MeasureTheory.integral_add (hXint.const_mul 2) (hYint.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) + 2 * (C ^ 4 * (b - a) ^ 2) := by
        gcongr
    _ = (2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * C ^ 4 * (b - a) ^ 2 := by ring
