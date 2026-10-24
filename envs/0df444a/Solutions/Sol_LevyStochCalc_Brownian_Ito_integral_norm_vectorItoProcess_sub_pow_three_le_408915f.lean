-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_pow_three_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:35:38.489417+00:00
-- url     : https://prove2.me/submissions/6ac308bc-4ca3-408e-86fd-e884c756062a

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFormulaGrid
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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Algebra.Order.Chebyshev
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_abs_drift_pow_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_abs_sum_pow_three_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_sub_pow_three_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_vectorItoProcess_sub_pow_three_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_norm_pi_pow_three_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_measurable_vectorItoProcess_sub_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open MeasureTheory
/-- A bounded measurable function is integrable on any set of finite measure. -/
theorem LevyStochCalc.integrableOn_of_bounded_of_measurable {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    MeasureTheory.IntegrableOn f s volume := by
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := B) hs hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hB u
/-- The increment of `t ↦ ∫_{[0,t]} f` across `(a, b]` is the integral over `(a, b]`. -/
theorem LevyStochCalc.setIntegral_Icc_sub_Icc {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in Set.Icc (0 : ℝ) b, f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) a, f s ∂volume
      = ∫ s in Set.Ioc a b, f s ∂volume := by
  have hsplit : Set.Icc (0 : ℝ) b = Set.Icc (0 : ℝ) a ∪ Set.Ioc a b := by
    rw [Set.Icc_union_Ioc_eq_Icc ha hab]
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
  have hint1 : MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) a) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  have hint2 : MeasureTheory.IntegrableOn f (Set.Ioc a b) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  rw [hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2,
    add_sub_cancel_left]
/-- The integral of a jointly measurable function over a fixed set is measurable in the
parameter. -/
theorem LevyStochCalc.measurable_setIntegral {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (s : Set ℝ) :
    Measurable fun ω => ∫ t in s, f ω t ∂volume :=
  (MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict s) hf.stronglyMeasurable).measurable
/-- The integral of a jointly measurable function over a fixed window is measurable in the
parameter. -/
theorem LevyStochCalc.measurable_setIntegral_Ioc {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (a b : ℝ) :
    Measurable fun ω => ∫ s in Set.Ioc a b, f ω s ∂volume :=
  measurable_setIntegral hf (Set.Ioc a b)
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
/-- `(a + b)³ ≤ 4(a³ + b³)` for nonnegative reals. -/
theorem LevyStochCalc.Brownian.Ito.add_pow_three_le_four {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [sq_nonneg (a - b), mul_nonneg ha hb, sq_nonneg (a + b)]
section Drift
variable {P : Measure Ω} [IsProbabilityMeasure P]
/-- The cube of the absolute increment of a bounded drift's integral is integrable. -/
theorem LevyStochCalc.Brownian.Ito.integrable_abs_drift_pow_three
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    MeasureTheory.Integrable
      (fun ω : Ω => |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ^ 3) P :=
  integrable_abs_drift_pow_408915f (P := P) bdrift hbm hB0 hB huv 3
end Drift
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section FiniteSums
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Fintype ι]
/-- A sum of two functions with integrable absolute cubes has integrable absolute cube. -/
theorem LevyStochCalc.Brownian.Ito.integrable_abs_add_pow_three {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : Integrable (fun ω => |A ω| ^ 3) P) (hB : Integrable (fun ω => |B ω| ^ 3) P) :
    Integrable (fun ω => |A ω + B ω| ^ 3) P := by
  have hdom : Integrable (fun ω => 4 * (|A ω| ^ 3 + |B ω| ^ 3)) P := (hA.add hB).const_mul 4
  have hpt : ∀ ω, |A ω + B ω| ^ 3 ≤ 4 * (|A ω| ^ 3 + |B ω| ^ 3) := fun ω =>
    (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le (A ω) (B ω)) 3).trans
      (add_pow_three_le_four (abs_nonneg _) (abs_nonneg _))
  have hmeas : Measurable fun ω => |A ω + B ω| ^ 3 := (hAm.add hBm).abs.pow_const 3
  refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
  exact hpt ω
end FiniteSums
section VectorProcess
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
/-- Each entry's Itô integral is measurable for the σ-algebra at its time. -/
theorem LevyStochCalc.Brownian.Ito.stronglyMeasurable_coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) :
    StronglyMeasurable[ℱ t] (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) :=
  stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k)
    (hHs m k) t
/-- Each entry's Itô integral is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) :
    Measurable (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) :=
  ((stronglyMeasurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t).mono (ℱ.le t)).measurable
/-- The martingale part of a coordinate is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_vectorItoMartingale (m : Fin n) (t : ℝ) :
    Measurable (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m t) :=
  Finset.measurable_sum _ fun k _ => measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t
/-- The increment of the martingale part is the sum of the entries' increments. -/
theorem LevyStochCalc.Brownian.Ito.vectorItoMartingale_sub (m : Fin n) (u v : ℝ) (ω : Ω) :
    vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω
      = ∑ k : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
        - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) := by
  simp only [vectorItoMartingale, Finset.sum_sub_distrib]
/-- The increment of a coordinate of a vector Itô process is the drift's increment plus the
martingale part's. -/
theorem LevyStochCalc.Brownian.Ito.vectorItoProcess_sub (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ}
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (m : Fin n) (ω : Ω) :
    vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m
      = (∫ s in Set.Ioc u v, bdrift m ω s ∂volume)
        + (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) := by
  simp only [vectorItoProcess]
  rw [← setIntegral_Icc_sub_Icc (Measurable.of_uncurry_left (hbm m)) (hB m ω) hu huv]
  ring
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
include hC0 hCH in
/-- The cube of the absolute increment of the martingale part is integrable. -/
theorem LevyStochCalc.Brownian.Ito.integrable_abs_vectorItoMartingale_sub_pow_three (m : Fin n) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u < v) :
    Integrable (fun ω => |vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
      - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω| ^ 3) P := by
  have hint := integrable_abs_sum_pow_three_408915f (P := P)
    (f := fun (k : Fin d) ω => coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
      - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω)
    (fun k => (measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v).sub
      (measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u))
    (fun k => (integral_abs_sub_pow_three_le_408915f (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k)
      (hHs m k) hC0 (hCH m k) hu huv).1)
  simp_rw [vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs m u v]
  exact hint
section VectorMoments
variable (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
  (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
include hbm hC0 hCH hB0 hB in
/-- The cube of the absolute increment of a coordinate is integrable. -/
theorem LevyStochCalc.Brownian.Ito.integrable_abs_vectorItoProcess_sub_pow_three (m : Fin n) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u < v) :
    Integrable (fun ω => |vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
      - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m| ^ 3) P := by
  simp_rw [vectorItoProcess_sub W ℱ hcoord H hHm hHp hHs X₀ bdrift hbm hB hu huv.le m]
  exact integrable_abs_add_pow_three (measurable_setIntegral_Ioc (hbm m) _ _)
    ((measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v).sub
      (measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u))
    (integrable_abs_drift_pow_three (P := P) (bdrift m) (hbm m) hB0 (hB m) huv.le)
    (integrable_abs_vectorItoMartingale_sub_pow_three W ℱ hcoord H hHm hHp hHs hC0 hCH m hu huv)
end VectorMoments
end VectorProcess
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoThirdMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section VectorThird
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hC0 hCH in
/-- **Third moment of the norm of the increment.** -/
theorem solution (X₀ : Ω → Fin n → ℝ)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ m, Measurable (Function.uncurry (bdrift m)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    ∫ ω, ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ^ 3 ∂P
      ≤ (n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((B * (v - u)) ^ 3
        + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * ((v - u) * Real.sqrt (v - u))))))) := by
  have h3 : ∀ p : Fin n, Integrable (fun ω =>
      |(LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω) p| ^ 3) P := fun p =>
    LevyStochCalc.Brownian.Ito.integrable_abs_vectorItoProcess_sub_pow_three W ℱ hcoord H hHm hHp hHs hC0 hCH X₀ bdrift
      hbm hB0 hB p hu huv
  have hc : ∀ p : Fin n, ∫ ω, |(LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω) p| ^ 3 ∂P
      ≤ 4 * ((B * (v - u)) ^ 3
        + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * ((v - u) * Real.sqrt (v - u))))) := fun p =>
    LevyStochCalc.Brownian.Ito.integral_abs_vectorItoProcess_sub_pow_three_le_408915f W ℱ hcoord H hHm hHp hHs hC0 hCH X₀ bdrift
      hbm hB0 hB p hu huv
  refine (LevyStochCalc.Brownian.Ito.integral_norm_pi_pow_three_le_408915f
    (LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess_sub_408915f W ℱ hcoord H hHm hHp hHs X₀ bdrift hbm hB hu huv.le)
    h3 hc).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
