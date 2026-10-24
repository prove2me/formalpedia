-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le_Ioc_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:23:21.049464+00:00
-- url     : https://prove2.me/submissions/fb472af3-9196-42e7-96dd-2ea8c70805ed

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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_exists_restrict_Ioc_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_integral_partialSum_pow_four_le_varClock_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_lintegral_eval_sq_lt_top_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_lintegral_pow_four_eq_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_varClock_le_Ioc_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_abs_clamp_sub_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_comp_sum_ite_408915f
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
section
namespace LevyStochCalc.Brownian.Ito.SimplePredictable
end LevyStochCalc.Brownian.Ito.SimplePredictable
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Ito.SimplePredictable
variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.partialSum_card (ω : Ω) : G.partialSum W G.N ω = simpleIntegral W G T ω := by
  rw [simpleIntegral_eq_sum, partialSum, ← Fin.sum_univ_eq_sum_range
    (fun i => G.term W i ω) G.N]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [term, dif_pos i.isLt]
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_nonneg (c : Fin G.N → ℝ) (k : ℕ) : 0 ≤ G.varClock c k := by
  unfold varClock
  refine Finset.sum_nonneg fun j _ => ?_
  by_cases h : j < G.N
  · rw [dif_pos h]
    exact mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le)
  · rw [dif_neg h]
end
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section
namespace LevyStochCalc.Brownian.Ito.SimplePredictable
end LevyStochCalc.Brownian.Ito.SimplePredictable
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Ito.SimplePredictable
variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
section Moments
variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
include hℱ h_adapt hC0 hC in
/-- **Fourth-moment bound for the elementary integral against a per-tile coefficient
bound.** -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integral_simpleIntegral_pow_four_le_varClock {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ (6 + gaussianFourthMoment) * G.varClock c G.N ^ 2 := by
  have hcard := G.integral_partialSum_pow_four_le_varClock_408915f W ℱ hℱ h_adapt hC0 hC hc G.N le_rfl
  have hfun : ∀ ω, G.partialSum W G.N ω = simpleIntegral W G T ω := G.partialSum_card W
  simp_rw [hfun] at hcard
  calc ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ 6 * (G.varClock c G.N * G.varClock c G.N)
        + gaussianFourthMoment * G.varClock c G.N ^ 2 := hcard
    _ = (6 + gaussianFourthMoment) * G.varClock c G.N ^ 2 := by ring
end Moments
end
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.abs_truncate_xi_le {T : ℝ} (G : SimplePredictable Ω T) {C : ℝ}
    (hC : 0 ≤ C) (i : Fin G.N) (ω : Ω) : |(G.truncate C).ξ i ω| ≤ C := by
  refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.truncate_eval {T : ℝ} (G : SimplePredictable Ω T) {C : ℝ}
    (hC : 0 ≤ C) (s : ℝ) (ω : Ω) :
    (G.truncate C).eval s ω = max (-C) (min C (G.eval s ω)) := by
  have hg0 : max (-C) (min C (0 : ℝ)) = 0 := by
    rw [min_eq_right hC, max_eq_right (by linarith : -C ≤ (0 : ℝ))]
  exact (comp_sum_ite_408915f G.partition_strictMono (fun i => G.ξ i ω) s
    (fun x => max (-C) (min C x)) hg0).symm
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.truncate_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (G : SimplePredictable Ω T) (C : ℝ)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    ∀ i : Fin (G.truncate C).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((G.truncate C).partition i.castSucc)) ((G.truncate C).ξ i) := by
  intro i
  exact (measurable_const.max
    (measurable_const.min (h_adapt i).measurable)).stronglyMeasurable
section LintegralForm
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
include hℱ in
/-- The fourth-moment bound against a per-tile coefficient bound, in `lintegral` form. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_simpleIntegral_pow_four_le_varClock {T : ℝ}
    (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    {c : Fin G.N → ℝ} (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∫⁻ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * G.varClock c G.N ^ 2) := by
  rw [G.lintegral_pow_four_eq_408915f W hC]
  exact ENNReal.ofReal_le_ofReal
    (G.integral_simpleIntegral_pow_four_le_varClock W ℱ hℱ h_adapt hC0 hC hc)
end LintegralForm
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
/-- A simple integrand whose coefficients vanish on every tile not contained in `(a, b]` has the
same elementary integral at every time past `b`. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.simpleIntegral_eq_of_support
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {a b : ℝ}
    (hz : ∀ (j : Fin H.N) (ω : Ω),
      ¬(a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b) → H.ξ j ω = 0)
    {t : ℝ} (hbt : b ≤ t) (ω : Ω) : simpleIntegral W H t ω = simpleIntegral W H T ω := by
  rw [simpleIntegral_eq_sum]
  unfold simpleIntegral
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b
  · have h1 : H.partition j.succ ≤ t := hj.2.trans hbt
    have h2 : H.partition j.castSucc ≤ t :=
      ((H.partition_strictMono Fin.castSucc_lt_succ).le).trans h1
    rw [min_eq_left h1, min_eq_left h2]
  · rw [hz j ω hj, zero_mul, zero_mul]
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section IncrementBound
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hℱ in
/-- **Fourth-moment bound for the `L²` Itô integral of an integrand supported in `(a, b]`.**
The bound sees only the length of the support. -/
theorem solution
    (F : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry F))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ F)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCF : ∀ ω s, |F ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ ω s, s ∉ Set.Ioc a b → F ω s = 0) :
    ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by
  classical
  have hb : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  choose G0 hG0adapt hG0within using fun n : ℕ =>
    LevyStochCalc.Brownian.Ito.exists_adaptedSimple_within ℱ F hm hp hb (hq b hb)
      (show (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ from ENNReal.inv_pos.mpr
        (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩))
  have hGadapt : ∀ n, ∀ i : Fin ((G0 n).truncate C).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (((G0 n).truncate C).partition i.castSucc)) (((G0 n).truncate C).ξ i) :=
    fun n => LevyStochCalc.Brownian.Ito.SimplePredictable.truncate_adapt ℱ (G0 n) C (hG0adapt n)
  have hGbdd : ∀ n, ∀ (i : Fin ((G0 n).truncate C).N) (ω : Ω),
      |((G0 n).truncate C).ξ i ω| ≤ C := fun n i ω => (G0 n).abs_truncate_xi_le hC0 i ω
  choose T3 Q hQadapt hQeval hQxi using fun n : ℕ =>
    LevyStochCalc.Brownian.Ito.SimplePredictable.exists_restrict_Ioc_408915f W ℱ ((G0 n).truncate C) (hGadapt n) hC0
      (hGbdd n) ha hab
  -- the restricted approximants are bounded by `C` and vanish off `(a, b]`
  have hQC : ∀ (n : ℕ) (j : Fin (Q n).N) (ω : Ω), |(Q n).ξ j ω| ≤ C := by
    intro n j ω
    refine (hQxi n j ω).trans ?_
    by_cases h : a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b
    · rw [if_pos h]
    · rw [if_neg h]; exact hC0
  have hQz : ∀ (n : ℕ) (j : Fin (Q n).N) (ω : Ω),
      ¬(a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b) → (Q n).ξ j ω = 0 := by
    intro n j ω h
    have := (hQxi n j ω).trans (le_of_eq (if_neg h))
    exact abs_nonpos_iff.mp this
  -- their elementary integrals at `b` are the ones the variance budget bounds
  have hQsimp : ∀ (n : ℕ) (ω : Ω),
      LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω = LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) (T3 n) ω :=
    fun n ω => (Q n).simpleIntegral_eq_of_support W (hQz n) le_rfl ω
  have hQbound : ∀ n : ℕ, ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by
    intro n
    simp_rw [hQsimp n]
    refine le_trans ((Q n).lintegral_simpleIntegral_pow_four_le_varClock W ℱ hℱ (hQadapt n)
      hC0 (hQC n) (c := fun j => if a ≤ (Q n).partition j.castSucc
        ∧ (Q n).partition j.succ ≤ b then C else 0) (hQxi n)) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hV := (Q n).varClock_le_Ioc_408915f (a := a) (b := b) (C := C) hab.le
    have hV0 := (Q n).varClock_nonneg
      (fun j => if a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b then C else 0)
      (Q n).N
    have hcg : (0 : ℝ) ≤ 6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment := by
      linarith [LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg]
    have hsq : (Q n).varClock
        (fun j => if a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b then C else 0)
        (Q n).N ^ 2 ≤ (C ^ 2 * (b - a)) ^ 2 := by
      nlinarith [hV, hV0]
    calc (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (Q n).varClock
            (fun j => if a ≤ (Q n).partition j.castSucc
              ∧ (Q n).partition j.succ ≤ b then C else 0) (Q n).N ^ 2
        ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 2 * (b - a)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hcg
      _ = (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by ring
  -- the restricted approximants still approximate `F`
  have hQwithin : ∀ n : ℕ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖(Q n).eval s ω - F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    refine le_trans ?_ (hG0within n).le
    refine lintegral_mono fun ω => lintegral_mono fun s => ?_
    have hle : ‖(Q n).eval s ω - F ω s‖₊ ≤ ‖F ω s - (G0 n).eval s ω‖₊ := by
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm, Real.norm_eq_abs]
      have hstep : |(Q n).eval s ω - F ω s|
          ≤ |((G0 n).truncate C).eval s ω - F ω s| := by
        rw [hQeval n s ω]
        by_cases hs : s ∈ Set.Ioc a b
        · rw [Set.indicator_of_mem hs]
          simp
        · rw [Set.indicator_of_notMem hs, zero_mul, hsupp ω s hs]
          simp
      refine hstep.trans ?_
      rw [(G0 n).truncate_eval hC0 s ω, abs_sub_comm (F ω s)]
      exact LevyStochCalc.Brownian.Ito.abs_clamp_sub_le_408915f hC0 (hCF ω s)
    exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr hle) 2
  have htol : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
    have h := ENNReal.tendsto_inv_nat_nhds_zero.comp hg
    refine h.congr fun n => ?_
    simp [Nat.cast_add_one]
  have hsq : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htol
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall fun n => ?_)
    rw [LevyStochCalc.Brownian.Ito.isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ (Q n) (hQadapt n) F hm hp hq hb]
    exact hQwithin n
  have heL : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω) 2 P) Filter.atTop (nhds 0) := by
    have hrw : ∀ n, MeasureTheory.eLpNorm
        (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω) 2 P
        = (∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
              ^ ((2 : ℝ))⁻¹ := by
      intro n
      rw [← LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq]
      exact (ENNReal.rpow_rpow_inv (by norm_num) _).symm
    simp_rw [hrw]
    have h := (ENNReal.continuous_rpow_const (y := ((2 : ℝ))⁻¹)).tendsto 0 |>.comp hsq
    simpa [Function.comp_def,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < ((2 : ℝ))⁻¹)] using h
  have hmeasG : ∀ n, Measurable (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω) := by
    intro n
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((Q n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hmeasSI : Measurable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b) :=
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ F hm hp hq b).mono (ℱ.le b)).measurable
  have hTIM : MeasureTheory.TendstoInMeasure P
      (fun n ω => LevyStochCalc.Brownian.Ito.simpleIntegral W (Q n) b ω) Filter.atTop
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun n => (hmeasG n).aestronglyMeasurable) hmeasSI.aestronglyMeasurable heL
  obtain ⟨ns, -, hns_ae⟩ := hTIM.exists_seq_tendsto_ae
  have hcont : Continuous fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 4 := by
    have hfun : (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 4)
        = fun x : ℝ => ((‖x‖₊ ^ 4 : ℝ≥0) : ℝ≥0∞) := by
      funext x; rw [ENNReal.coe_pow]
    rw [hfun]
    exact ENNReal.continuous_coe.comp (continuous_nnnorm.pow 4)
  have hfatou : ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ Filter.liminf (fun k => ∫⁻ ω,
        (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q (ns k)) b ω‖₊ : ℝ≥0∞) ^ 4 ∂P) Filter.atTop := by
    have h1 : ∀ᵐ ω ∂P,
        (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4
        = Filter.liminf (fun k =>
            (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (Q (ns k)) b ω‖₊ : ℝ≥0∞) ^ 4) Filter.atTop := by
      filter_upwards [hns_ae] with ω hω
      exact ((hcont.tendsto _).comp hω).liminf_eq.symm
    rw [lintegral_congr_ae h1]
    exact lintegral_liminf_le fun k => (hcont.measurable.comp (hmeasG (ns k)))
  exact hfatou.trans (Filter.liminf_le_of_frequently_le
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun k => hQbound (ns k))))
