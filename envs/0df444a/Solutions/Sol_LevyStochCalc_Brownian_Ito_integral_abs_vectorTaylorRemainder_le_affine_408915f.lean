-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le_affine_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:38:47.259327+00:00
-- url     : https://prove2.me/submissions/8be8867c-fc6d-4329-a36c-bca246eb1377

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
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
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_norm_vectorItoProcess_sub_pow_three_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_norm_vectorItoProcess_sub_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_measurable_taylorRemainderNormed_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_sum_integral_norm_vectorItoIncrement_pow_three_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_sum_integral_sq_norm_vectorItoIncrement_le_408915f
import Theorems.Thm_LevyStochCalc_abs_taylorRemainderNormed_le_affine_408915f

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
/-- The integral of a jointly measurable function over a fixed set is measurable in the
parameter. -/
theorem LevyStochCalc.measurable_setIntegral {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (s : Set ℝ) :
    Measurable fun ω => ∫ t in s, f ω t ∂volume :=
  (MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict s) hf.stronglyMeasurable).measurable
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
/-- A vector Itô process is measurable in the sample point at each time. -/
theorem LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess {X₀ : Ω → Fin n → ℝ}
    (hX₀ : ∀ m, Measurable fun ω => X₀ ω m) {bdrift : Fin n → Ω → ℝ → ℝ}
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) (t : ℝ) :
    Measurable (vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t) := by
  refine measurable_pi_lambda _ fun m => ?_
  exact ((hX₀ m).add (measurable_setIntegral (hbm m) _)).add
    (measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs m t)
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
end VectorProcess
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFormulaGrid.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
theorem LevyStochCalc.Brownian.Ito.unifGrid_nonneg {T : ℝ} (hT : 0 ≤ T) (m i : ℕ) : 0 ≤ unifGrid T m i := by
  rw [unifGrid]
  positivity
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoTaylor.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section VectorTaylor
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
/-- **The second-order Taylor remainder of a vector Itô process along a uniform grid under an
affine oscillation bound on the second derivative.** -/
theorem solution (X₀ : Ω → Fin n → ℝ)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A)
    (hK0 : 0 ≤ K) (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf''c : Continuous f'') (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => LevyStochCalc.taylorRemainderNormed f f' f''
        (fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m) P
      ∧ ∫ ω, |LevyStochCalc.taylorRemainderNormed f f' f''
          (fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m| ∂P
        ≤ A * ((n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T))))
          + K * ((n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
            + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
              * (T * Real.sqrt (T / (m : ℝ))))))))) := by
  have hX : ∀ i : ℕ,
      Measurable (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i)) :=
    fun i => LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess W ℱ hcoord H hHm hHp hHs hX₀ hbm _
  have hfd : Differentiable ℝ f := fun z => (hf z).differentiableAt
  have hf'd : Differentiable ℝ f' := fun z => (hf' z).differentiableAt
  have hR := LevyStochCalc.Brownian.Ito.measurable_taylorRemainderNormed_408915f hfd.continuous hf'd.continuous hf''c hX m
  have hptw : ∀ ω : Ω, |LevyStochCalc.taylorRemainderNormed f f' f''
      (fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m|
      ≤ A * ∑ i ∈ Finset.range m,
          ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2
        + K * ∑ i ∈ Finset.range m,
          ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 3 :=
    fun ω => LevyStochCalc.abs_taylorRemainderNormed_le_affine_408915f hA0 hK0 hf hf' hf'' _ m
  have hsq : ∀ i ∈ Finset.range m, Integrable (fun ω : Ω =>
      ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2) P :=
    fun i _ => (LevyStochCalc.Brownian.Ito.integral_sq_norm_vectorItoProcess_sub_le_408915f W ℱ hcoord H hHm hHp hHs hC0 hCH
      X₀ bdrift hbm hB0 hB (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i)).1
  have hcu : ∀ i ∈ Finset.range m, Integrable (fun ω : Ω =>
      ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 3) P :=
    fun i _ => LevyStochCalc.Brownian.Ito.integrable_norm_vectorItoProcess_sub_pow_three_408915f W ℱ hcoord H hHm hHp hHs hC0 hCH
      X₀ bdrift hbm hB0 hB (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i)
  have hsumint : Integrable (fun ω : Ω =>
      A * ∑ i ∈ Finset.range m,
        ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2
      + K * ∑ i ∈ Finset.range m,
        ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 3) P :=
    ((MeasureTheory.integrable_finsetSum _ hsq).const_mul A).add
      ((MeasureTheory.integrable_finsetSum _ hcu).const_mul K)
  have hRint : Integrable (fun ω : Ω => |LevyStochCalc.taylorRemainderNormed f f' f''
      (fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m|) P := by
    refine hsumint.mono hR.abs.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact (hptw ω).trans (le_abs_self _)
  have hRint0 : Integrable (fun ω : Ω => LevyStochCalc.taylorRemainderNormed f f' f''
      (fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m) P := by
    refine hsumint.mono hR.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hptw ω).trans (le_abs_self _)
  refine ⟨hRint0, ?_⟩
  calc ∫ ω, |LevyStochCalc.taylorRemainderNormed f f' f''
        (fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m| ∂P
      ≤ ∫ ω, (A * ∑ i ∈ Finset.range m,
            ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2
          + K * ∑ i ∈ Finset.range m,
            ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 3) ∂P :=
        MeasureTheory.integral_mono hRint hsumint hptw
    _ = A * ∑ i ∈ Finset.range m, ∫ ω,
            ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2 ∂P
          + K * ∑ i ∈ Finset.range m, ∫ ω,
            ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 3 ∂P := by
        rw [MeasureTheory.integral_add ((MeasureTheory.integrable_finsetSum _ hsq).const_mul A)
          ((MeasureTheory.integrable_finsetSum _ hcu).const_mul K),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finsetSum _ hsq, MeasureTheory.integral_finsetSum _ hcu]
    _ ≤ A * ((n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T))))
          + K * ((n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
            + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
              * (T * Real.sqrt (T / (m : ℝ))))))))) := by
        gcongr
        · exact LevyStochCalc.Brownian.Ito.sum_integral_sq_norm_vectorItoIncrement_le_408915f W ℱ hcoord H hHm hHp hHs hC0 hCH
            X₀ bdrift hbm hB0 hB hT hm0
        · exact LevyStochCalc.Brownian.Ito.sum_integral_norm_vectorItoIncrement_pow_three_le_408915f W ℱ hcoord H hHm hHp hHs
            hC0 hCH X₀ bdrift hbm hB0 hB hT hm0
