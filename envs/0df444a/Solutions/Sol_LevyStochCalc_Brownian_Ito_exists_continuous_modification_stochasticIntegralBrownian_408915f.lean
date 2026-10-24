-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.exists_continuous_modification_stochasticIntegralBrownian_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:43:49.32661+00:00
-- url     : https://prove2.me/submissions/ab017c1f-4713-48c1-81c6-d407ea6581bc

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
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_kolmogorovChentsov_modification_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_stochasticIntegralBrownian_sub_pow_four_le_408915f

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
section ContinuousModification
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
/-- The extended distance between two reals is the norm of their difference. -/
theorem LevyStochCalc.Brownian.Ito.edist_eq_coe_nnnorm_sub (x y : ℝ) : edist x y = (‖x - y‖₊ : ℝ≥0∞) := by
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
  exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hℱ hC0 hCH in
/-- **A continuous modification of the `L²` Itô integral of a bounded integrand.** The
fourth-moment increment bound is the Kolmogorov–Chentsov condition with exponents `(4, 2)`. -/
theorem solution :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous fun t => Y t ω)
        ∧ ∀ t : ℝ, 0 ≤ t →
            Y t =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
  classical
  set K : ℝ := (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 with hK
  have hK0 : 0 ≤ K := by
    have := LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg
    positivity
  set Xc : ℝ → Ω → ℝ :=
    fun t ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (max t 0) ω with hXc
  have hXmeas : ∀ t : ℝ, Measurable (Xc t) := fun t =>
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq (max t 0)).mono
      (ℱ.le _)).measurable
  -- the Kolmogorov condition with exponents `(4, 2)`
  have hpair : ∀ a b : ℝ, 0 ≤ a → a < b →
      ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
        ≤ ENNReal.ofReal (K * (b - a) ^ 2) := by
    intro a b ha hab
    have hswap : ∀ ω : Ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω‖₊ : ℝ≥0∞)
        = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) := by
      intro ω
      rw [← nnnorm_neg, neg_sub]
    simp_rw [hswap]
    exact LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_pow_four_le_408915f W ℱ hℱ H hm hp hq hC0 hCH ha hab
  have hkol : ∀ s t : ℝ, ∫⁻ ω, edist (Xc s ω) (Xc t ω) ^ (4 : ℝ) ∂P
      ≤ (K.toNNReal : ℝ≥0∞) * edist s t ^ (2 : ℝ) := by
    intro s t
    have hnat4 : ∀ ω : Ω, edist (Xc s ω) (Xc t ω) ^ (4 : ℝ)
        = (‖Xc s ω - Xc t ω‖₊ : ℝ≥0∞) ^ (4 : ℕ) := by
      intro ω
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast,
        LevyStochCalc.Brownian.Ito.edist_eq_coe_nnnorm_sub]
    have hnat2 : edist s t ^ (2 : ℝ) = ENNReal.ofReal (|s - t| ^ 2) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, edist_dist,
        Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _)]
    have hdiff : |max s 0 - max t 0| ≤ |s - t| := abs_max_sub_max_le_abs s t 0
    simp_rw [hnat4]
    rw [hnat2, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      Real.coe_toNNReal K hK0]
    rcases lt_trichotomy (max s 0) (max t 0) with hst | hst | hst
    · refine le_trans (hpair (max s 0) (max t 0) (le_max_right _ _) hst) ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : max t 0 - max s 0 ≤ |s - t| := by
        rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ max t 0 - max s 0), abs_sub_comm]
        exact hdiff
      have h2 : (0 : ℝ) ≤ max t 0 - max s 0 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 2) hK0
    · have hzero : ∀ ω : Ω, (‖Xc s ω - Xc t ω‖₊ : ℝ≥0∞) ^ (4 : ℕ) = 0 := by
        intro ω
        simp [hXc, hst]
      simp_rw [hzero]
      simp
    · have hswap : ∀ ω : Ω, (‖Xc s ω - Xc t ω‖₊ : ℝ≥0∞)
          = (‖Xc t ω - Xc s ω‖₊ : ℝ≥0∞) := fun ω => by rw [← nnnorm_neg, neg_sub]
      simp_rw [hswap]
      refine le_trans (hpair (max t 0) (max s 0) (le_max_right _ _) hst) ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : max s 0 - max t 0 ≤ |s - t| := by
        rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ max s 0 - max t 0)]
        exact hdiff
      have h2 : (0 : ℝ) ≤ max s 0 - max t 0 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 2) hK0
  have hKolProc : ProbabilityTheory.IsKolmogorovProcess Xc P 4 2 K.toNNReal :=
    ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology hXmeas hkol
      (by norm_num) (by norm_num)
  obtain ⟨Y, hYcont, hYmod⟩ :=
    LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification_408915f P Xc hKolProc
      (by norm_num)
  refine ⟨Y, hYcont, fun t ht => ?_⟩
  have h := hYmod t
  simp only [hXc, max_eq_left ht] at h
  exact h
