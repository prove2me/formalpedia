-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_vectorItoFormula_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:41:17.838915+00:00
-- url     : https://prove2.me/submissions/d439dc00-c076-4644-9b79-2584eddbb040

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_AugmentedFiltration
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CoordDerivative
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossVariation
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossVariationSum
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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoQuadVarSum
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_PolarisedQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoFormula
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Augmentation
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
import Mathlib.MeasureTheory.Measure.NullMeasurable
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_frozenRiemann_sub_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_quadVarRiemann_sub_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_lintegral_sq_martingaleRiemann_sub_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_vectorItoFormula_decomp_ae_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_le_sqrt_of_lintegral_sq_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_vectorTaylorRemainder_le_affine_408915f
import Theorems.Thm_LevyStochCalc_abs_coordDeriv_two_sub_le_affine_408915f
import Theorems.Thm_LevyStochCalc_integral_abs_add_four_le_408915f

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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcessVersion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section VectorVersion
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
variable {W ℱ hcoord H hHm hHp hHs} {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}
/-- A version's time slices are measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℝ) :
    Measurable (X t) := ((h.adapted t).mono (ℱ.le t)).measurable
/-- A version agrees with the vector Itô process at every time of a countable family,
simultaneously. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.ae_eq_all
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℕ → ℝ)
    (ht : ∀ i, 0 ≤ t i) :
    ∀ᵐ ω ∂P, ∀ i : ℕ, X (t i) ω = vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (t i) ω :=
  MeasureTheory.ae_all_iff.mpr fun i => h.ae_eq (t i) (ht i)
end VectorVersion
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

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open ContinuousLinearMap
variable {n : ℕ}
section Coord
variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
/-- A partial derivative is bounded by the operator norm of the Fréchet derivative. -/
theorem LevyStochCalc.abs_coordDeriv_le {K₁ : ℝ} (h : ∀ x, ‖f' x‖ ≤ K₁) (p : Fin n) (x : Fin n → ℝ) :
    |coordDeriv f' p x| ≤ K₁ := by
  have hnorm : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by
    rw [Pi.norm_single, norm_one]
  calc |coordDeriv f' p x| = ‖f' x (Pi.single p 1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f' x‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ := (f' x).le_opNorm _
    _ = ‖f' x‖ := by rw [hnorm, mul_one]
    _ ≤ K₁ := h x
/-- A second partial derivative is bounded by the operator norm of the second Fréchet
derivative. -/
theorem LevyStochCalc.abs_coordDeriv₂_le {K₂ : ℝ} (h : ∀ x, ‖f'' x‖ ≤ K₂) (p q : Fin n) (x : Fin n → ℝ) :
    |coordDeriv₂ f'' p q x| ≤ K₂ := by
  have hnorm : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  have hnormq : ‖(Pi.single q 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  calc |coordDeriv₂ f'' p q x| = ‖f'' x (Pi.single p 1) (Pi.single q 1)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖f'' x‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ * ‖(Pi.single q 1 : Fin n → ℝ)‖ :=
        (f'' x).le_opNorm₂ _ _
    _ = ‖f'' x‖ := by rw [hnorm, hnormq, mul_one, mul_one]
    _ ≤ K₂ := h x
/-- **The mean value theorem for the first derivative.** A bound on the second Fréchet derivative
is a Lipschitz constant for the first. -/
theorem LevyStochCalc.norm_fderiv_sub_le (hf' : ∀ z, HasFDerivAt f' (f'' z) z) {K₂ : ℝ}
    (h : ∀ z, ‖f'' z‖ ≤ K₂) (x y : Fin n → ℝ) : ‖f' x - f' y‖ ≤ K₂ * ‖x - y‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := f') (f' := f'') (s := Set.univ)
    (C := K₂) (fun z _ => (hf' z).hasFDerivWithinAt) (fun z _ => h z) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
/-- A partial derivative is Lipschitz with the second derivative's bound. -/
theorem LevyStochCalc.abs_coordDeriv_sub_le (hf' : ∀ z, HasFDerivAt f' (f'' z) z) {K₂ : ℝ}
    (h : ∀ z, ‖f'' z‖ ≤ K₂) (p : Fin n) (x y : Fin n → ℝ) :
    |coordDeriv f' p x - coordDeriv f' p y| ≤ K₂ * ‖x - y‖ := by
  have hnorm : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  have hsub : coordDeriv f' p x - coordDeriv f' p y = (f' x - f' y) (Pi.single p 1) := by
    simp [coordDeriv]
  calc |coordDeriv f' p x - coordDeriv f' p y| = ‖(f' x - f' y) (Pi.single p 1)‖ := by
        rw [hsub]; exact (Real.norm_eq_abs _).symm
    _ ≤ ‖f' x - f' y‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ := (f' x - f' y).le_opNorm _
    _ = ‖f' x - f' y‖ := by rw [hnorm, mul_one]
    _ ≤ K₂ * ‖x - y‖ := norm_fderiv_sub_le hf' h x y
/-- Continuity of a partial derivative. -/
theorem LevyStochCalc.continuous_coordDeriv (hf'c : Continuous f') (p : Fin n) :
    Continuous (coordDeriv f' p) :=
  hf'c.clm_apply continuous_const
/-- Continuity of a second partial derivative. -/
theorem LevyStochCalc.continuous_coordDeriv₂ (hf''c : Continuous f'') (p q : Fin n) :
    Continuous (coordDeriv₂ f'' p q) :=
  (hf''c.clm_apply continuous_const).clm_apply continuous_const
end Coord
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section CellSums
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
/-- The first absolute moment of a finite sum is at most the sum of the bounds. -/
theorem LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le {ι : Type*} (s : Finset ι) (F : ι → Ω → ℝ)
    (hF : ∀ j ∈ s, Integrable (F j) P) (c : ι → ℝ) (hc : ∀ j ∈ s, ∫ ω, |F j ω| ∂P ≤ c j) :
    ∫ ω, |∑ j ∈ s, F j ω| ∂P ≤ ∑ j ∈ s, c j := by
  have hsum : Integrable (fun ω => ∑ j ∈ s, F j ω) P :=
    MeasureTheory.integrable_finsetSum _ hF
  have habs : Integrable (fun ω => ∑ j ∈ s, |F j ω|) P :=
    MeasureTheory.integrable_finsetSum _ fun j hj => (hF j hj).abs
  calc ∫ ω, |∑ j ∈ s, F j ω| ∂P ≤ ∫ ω, ∑ j ∈ s, |F j ω| ∂P :=
        MeasureTheory.integral_mono hsum.abs habs fun ω => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ s, ∫ ω, |F j ω| ∂P :=
        MeasureTheory.integral_finsetSum _ fun j hj => (hF j hj).abs
    _ ≤ ∑ j ∈ s, c j := Finset.sum_le_sum hc
end CellSums
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoFormula.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
open scoped NNReal ENNReal Topology
universe u
section Formula
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)
namespace LevyStochCalc.Brownian.Ito.IsVectorItoVersion
end LevyStochCalc.Brownian.Ito.IsVectorItoVersion
open LevyStochCalc.Brownian.Ito.IsVectorItoVersion in
include hC0 hCH in
/-- **The `L¹` defect of Itô's formula for a vector Itô process on a uniform grid.** -/
theorem solution
    (h : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (hma : ∀ (p q : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ (p q : Fin n) (k : Fin d),
      LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K) (hf''c : Continuous f'')
    (hf''aff : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) P
      ∧ ∫ ω, |f (X T ω) - f (X 0 ω)
          - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| ∂P
        ≤ LevyStochCalc.Brownian.Ito.vectorItoGridError (n : ℝ) (d : ℝ) B C T A K K₂ (T / (m : ℝ)) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hf'd : Differentiable ℝ f' := fun z => (hf' z).differentiableAt
  have hf'c : Continuous f' := hf'd.continuous
  have hdecomp := h.vectorItoFormula_decomp_ae_408915f (f := f) (f'' := f'') hbm hB hmg hpg hqg hT hm0
  -- (1) the Taylor remainder, transferred to the version
  obtain ⟨hZ1int0, hZ1le0⟩ := LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le_affine_408915f W ℱ hcoord H hHm hHp
    hHs hC0 hCH X₀ hX₀ bdrift hbm hB0 hB hA0 hK0 hf hf' hf''c hf''aff hT hm0
  have hRae : (fun ω : Ω => LevyStochCalc.taylorRemainderNormed f f' f''
        (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m)
      =ᵐ[P] fun ω : Ω => LevyStochCalc.taylorRemainderNormed f f' f''
        (fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m := by
    filter_upwards [h.ae_eq_all (LevyStochCalc.Brownian.Ito.unifGrid T m) fun i => LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i] with ω hω
    have hfun : (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        = fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω :=
      funext hω
    rw [hfun]
  have e1 : (m : ℝ) * (B * (T / (m : ℝ))) ^ 3 = B ^ 3 * T * (T / (m : ℝ)) ^ 2 := by field_simp
  rw [e1] at hZ1le0
  have hZ1int : Integrable (fun ω : Ω => LevyStochCalc.taylorRemainderNormed f f' f''
      (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m) P := hZ1int0.congr hRae.symm
  have hZ1le := le_trans (le_of_eq (MeasureTheory.integral_congr_ae (hRae.fun_comp abs))) hZ1le0
  -- (2) the drift Riemann sums
  have hZ2 := fun p : Fin n =>
    h.integral_abs_frozenRiemann_sub_le_408915f hC0 hCH hbm hB0 hB (bdrift p) (hbm p) hB0 (hB p)
      (LevyStochCalc.continuous_coordDeriv hf'c p) (LevyStochCalc.abs_coordDeriv_le hf'bd p) le_rfl hK₂0
      (fun x y => by simpa using LevyStochCalc.abs_coordDeriv_sub_le hf' hf''bd p x y) hT hm0
  -- (3) the martingale Riemann sums
  have hZ3 : ∀ (p : Fin n) (k : Fin d),
      Integrable (fun ω : Ω => (∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω) P
        ∧ ∫ ω, |(∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
                - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω| ∂P
          ≤ Real.sqrt (C ^ 2 * (K₂ ^ 2 * (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
              + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))))) := by
    intro p k
    have hfin : ∀ ω : Ω,
        (∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
          = ∑ i : Fin m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω)
            * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
                  (hHs p k) (LevyStochCalc.Brownian.Ito.unifGrid T m ((i : ℕ) + 1)) ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
                  (hHs p k) (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω) := fun ω =>
      (Fin.sum_univ_eq_sum_range (fun i => LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
              (hHs p k) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
              (hHs p k) (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)) m).symm
    have hmeas : Measurable (fun ω : Ω =>
        (∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω) := by
      refine Measurable.sub (Finset.measurable_sum _ fun i _ =>
        (((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp
            (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m i))).mul
          ((LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs p k _).sub
            (LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs p k _)))) ?_
      exact ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) _ (hmg p k)
        (hpg p k) (hqg p k) T).mono (ℱ.le T)).measurable
    have hV0 : (0 : ℝ) ≤ C ^ 2 * (K₂ ^ 2 * (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
        + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ)))))))) := by positivity
    refine LevyStochCalc.Brownian.Ito.integral_abs_le_sqrt_of_lintegral_sq_le_408915f hmeas.aestronglyMeasurable hV0 ?_
    have hsq := h.lintegral_sq_martingaleRiemann_sub_le_408915f hC0 hCH hbm hB0 hB
      (LevyStochCalc.abs_coordDeriv_le hf'bd p) hK₂0 (LevyStochCalc.abs_coordDeriv_sub_le hf' hf''bd p) k
      (hHm p k) (hHp p k) (hHs p k) hC0 (hCH p k) (hmg p k) (hpg p k) (hqg p k) hT hm0
    simp only [hfin]
    refine hsq.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  -- (4) the weighted quadratic variations
  have hZ4 := fun p q : Fin n =>
    h.integral_abs_quadVarRiemann_sub_le_408915f hC0 hCH hbm hB0 hB p q (hma p q) (hpa p q) (hqa p q)
      (LevyStochCalc.continuous_coordDeriv₂ hf''c p q) hK₂0 (LevyStochCalc.abs_coordDeriv₂_le hf''bd p q) hA0 hK0
      (LevyStochCalc.abs_coordDeriv_two_sub_le_affine_408915f hf''aff p q) hT hm0
  have e2 : (m : ℝ) * (K₂ * (B * (T / (m : ℝ))) ^ 2) = K₂ * B ^ 2 * T * (T / (m : ℝ)) := by
    field_simp
  have e3 : (m : ℝ) * (K₂ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
      = K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ)) := by
    field_simp
  have e4 : T ^ 2 / (m : ℝ) = T * (T / (m : ℝ)) := by
    field_simp
  simp only [e2, e3, e4] at hZ4
  -- assemble the four families
  have hZ2int : Integrable (fun ω : Ω => ∑ p : Fin n,
      ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        - ∫ s in Set.Ioc (0 : ℝ) T, LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)) P :=
    MeasureTheory.integrable_finsetSum _ fun p _ => (hZ2 p).1
  have hZ2le : ∫ ω, |∑ p : Fin n,
        ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)| ∂P
      ≤ (n : ℝ) * (0 * B * T + K₂ * B * (T * ((n : ℝ) * (B * (T / (m : ℝ))
        + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by
    refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _ (fun p _ => (hZ2 p).1) _ (fun p _ => (hZ2 p).2)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hZ3int : Integrable (fun ω : Ω => ∑ p : Fin n, ∑ k : Fin d,
      ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)) P :=
    MeasureTheory.integrable_finsetSum _ fun p _ =>
      MeasureTheory.integrable_finsetSum _ fun k _ => (hZ3 p k).1
  have hZ3le : ∫ ω, |∑ p : Fin n, ∑ k : Fin d,
        ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)| ∂P
      ≤ (n : ℝ) * ((d : ℝ) * Real.sqrt (C ^ 2 * (K₂ ^ 2 * (T * ((n : ℝ)
        * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ)))))))))) := by
    refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _
      (fun p _ => MeasureTheory.integrable_finsetSum _ fun k _ => (hZ3 p k).1)
      (fun _ => (d : ℝ) * Real.sqrt (C ^ 2 * (K₂ ^ 2 * (T * ((n : ℝ)
        * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))))))
      (fun p _ => ?_)).trans ?_
    · refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _ (fun k _ => (hZ3 p k).1) _
        (fun k _ => (hZ3 p k).2)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hZ4int : Integrable (fun ω : Ω => 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
      ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv₂ f'' p q (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
            * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) P :=
    (MeasureTheory.integrable_finsetSum _ fun p _ =>
      MeasureTheory.integrable_finsetSum _ fun q _ => (hZ4 p q).1).const_mul _
  have hZ4le : ∫ ω, |1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
        ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv₂ f'' p q (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
              * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
          - ∫ s in Set.Ioc (0 : ℝ) T,
              LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| ∂P
      ≤ 1 / 2 * ((n : ℝ) * ((n : ℝ) * (K₂ * B ^ 2 * T * (T / (m : ℝ))
        + K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ))
        + K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ))
        + (d : ℝ) * Real.sqrt (K₂ ^ 2
            * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4))
            * (T * (T / (m : ℝ))))
        + (d : ℝ) ^ 2 * Real.sqrt (K₂ ^ 2
            * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T * (T / (m : ℝ))))
        + (A * ((d : ℝ) * C ^ 2) * T
          + K * ((d : ℝ) * C ^ 2) * (T * ((n : ℝ) * (B * (T / (m : ℝ))
            + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))))))) := by
    have habs : ∀ ω : Ω, |1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
          ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv₂ f'' p q (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
                * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
            - ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)|
        = 1 / 2 * |∑ p : Fin n, ∑ q : Fin n,
          ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv₂ f'' p q (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
                * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
            - ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| := by
      intro ω
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simp_rw [habs]
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _
      (fun p _ => MeasureTheory.integrable_finsetSum _ fun q _ => (hZ4 p q).1)
      (fun _ => (n : ℝ) * (K₂ * B ^ 2 * T * (T / (m : ℝ))
        + K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ))
        + K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ))
        + (d : ℝ) * Real.sqrt (K₂ ^ 2
            * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4))
            * (T * (T / (m : ℝ))))
        + (d : ℝ) ^ 2 * Real.sqrt (K₂ ^ 2
            * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T * (T / (m : ℝ))))
        + (A * ((d : ℝ) * C ^ 2) * T
          + K * ((d : ℝ) * C ^ 2) * (T * ((n : ℝ) * (B * (T / (m : ℝ))
            + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))))))
      (fun p _ => ?_)).trans ?_
    · refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _ (fun q _ => (hZ4 p q).1) _
        (fun q _ => (hZ4 p q).2)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine ⟨(((hZ1int.add hZ2int).add hZ3int).add hZ4int).congr hdecomp.symm, ?_⟩
  refine le_trans (le_of_eq (MeasureTheory.integral_congr_ae (hdecomp.fun_comp abs))) ?_
  refine le_trans (LevyStochCalc.integral_abs_add_four_le_408915f hZ1int hZ2int hZ3int hZ4int hZ1le hZ2le hZ3le hZ4le)
    (le_of_eq ?_)
  unfold LevyStochCalc.Brownian.Ito.vectorItoGridError
  ring
