-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_crossSum_sq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:14:41.720392+00:00
-- url     : https://prove2.me/submissions/ef948258-04c9-4ce8-8235-7a67c46d2978

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross
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
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Augmentation
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
import Mathlib.MeasureTheory.Measure.NullMeasurable
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_mul_increment_pow_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_pow_gaussianReal_zero_408915f

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
/-- The odd moments of the standard real Gaussian vanish. -/
theorem LevyStochCalc.Brownian.Ito.integral_pow_gaussianReal_odd (m : ℕ) (hm : Odd m) :
    ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) = 0 := by
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  have h1 : ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1)
      = ∫ x : ℝ, (-x) ^ m ∂(gaussianReal 0 1) := by
    conv_lhs => rw [← hmap]
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [hm.neg_pow] at h1
  rw [integral_neg] at h1
  linarith
section Increments
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
/-- The moments of a Brownian increment scale with the square root of its length. -/
theorem LevyStochCalc.Brownian.Ito.integral_increment_pow {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (m : ℕ) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P
      = Real.sqrt (b - a) ^ m * ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [← integral_map hmeas.aemeasurable
      (f := fun x : ℝ => x ^ m) (by fun_prop),
    W.increment_gaussian ha hab]
  exact integral_pow_gaussianReal_zero_408915f _ m
/-- Odd moments of a Brownian increment vanish. -/
theorem LevyStochCalc.Brownian.Ito.integral_increment_pow_odd {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {m : ℕ} (hm : Odd m) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P = 0 := by
  rw [integral_increment_pow W ha hab m, integral_pow_gaussianReal_odd m hm, mul_zero]
/-- The second moment of a Brownian increment is its length. -/
theorem LevyStochCalc.Brownian.Ito.integral_increment_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P = b - a := by
  rw [integral_increment_pow W ha hab 2,
    LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment 1]
  rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ b - a)]
  norm_num
/-- A Brownian increment has moments of every order. -/
theorem LevyStochCalc.Brownian.Ito.memLp_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun ω => W.W b ω - W.W a ω) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have h := (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (μ := P)
    (f := fun ω => W.W b ω - W.W a ω) (p := p)
    (by fun_prop) hmeas.aemeasurable).1
  rw [W.increment_gaussian ha hab] at h
  exact h (memLp_id_gaussianReal' p hp)
end Increments
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
section
namespace LevyStochCalc.Brownian.Multidim
end LevyStochCalc.Brownian.Multidim
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
section
namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
section DirectCross
/-- Borel functionals of the paths of two distinct coordinates are independent. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.indepFun_comp_coord (W : MultidimBrownianMotion P d) {i j : Fin d} (hij : i ≠ j)
    {φ ψ : (ℝ → ℝ) → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (fun ω => φ fun t => (W.W i).W t ω) (fun ω => ψ fun t => (W.W j).W t ω) P :=
  (W.components_independent.indepFun hij).comp hφ hψ
/-- An increment of a Brownian motion over a possibly degenerate interval is square-integrable. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le (V : BrownianMotion P) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    MemLp (fun ω => V.W q ω - V.W p ω) 2 P := by
  rcases eq_or_lt_of_le hpq with h | h
  · subst h
    simp only [sub_self]
    exact memLp_const 0
  · exact Ito.memLp_increment V hp h 2 (by simp)
/-- Increments of a Brownian motion over two intervals, the second starting after the first
ends, are uncorrelated. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_increment_mul_increment_eq_zero (V : BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hV : IsBrownianFiltration V ℱ) {p q r v : ℝ}
    (hpr : p ≤ r) (hqr : q ≤ r) (hr : 0 ≤ r) (hrv : r < v) :
    ∫ ω, (V.W q ω - V.W p ω) * (V.W v ω - V.W r ω) ∂P = 0 := by
  have hY : StronglyMeasurable[ℱ r] fun ω => V.W q ω - V.W p ω :=
    (((hV.measurable q).mono (ℱ.mono hqr) le_rfl).sub
      ((hV.measurable p).mono (ℱ.mono hpr) le_rfl)).stronglyMeasurable
  have hYm : Measurable fun ω => V.W q ω - V.W p ω :=
    (V.measurable_eval q).sub (V.measurable_eval p)
  have h := Ito.integral_mul_increment_pow_408915f V ℱ hV hr hrv hY hYm 1
  rw [Ito.integral_increment_pow_odd V hr hrv odd_one, mul_zero] at h
  simpa only [pow_one] using h
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_zero (a h : ℝ) : affineGrid a h 0 = a := by simp [affineGrid]
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_succ_sub (a h : ℝ) (k : ℕ) : affineGrid a h (k + 1) - affineGrid a h k = h := by
  simp only [affineGrid, Nat.cast_succ]; ring
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono {a h : ℝ} (hh : 0 ≤ h) {k l : ℕ} (hkl : k ≤ l) :
    affineGrid a h k ≤ affineGrid a h l := by
  simp only [affineGrid]
  have hkl' : (k : ℝ) ≤ l := Nat.cast_le.2 hkl
  nlinarith
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_lt_succ {a h : ℝ} (hh : 0 < h) (k : ℕ) :
    affineGrid a h k < affineGrid a h (k + 1) := by
  have := affineGrid_succ_sub a h k
  linarith
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.le_affineGrid {a h : ℝ} (hh : 0 ≤ h) (k : ℕ) : a ≤ affineGrid a h k := by
  simpa [affineGrid_zero] using affineGrid_mono (a := a) hh (Nat.zero_le k)
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_nonneg {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (k : ℕ) : 0 ≤ affineGrid a h k :=
  ha.trans (le_affineGrid hh k)
namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
open LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion in
/-- The second moment of the sum of cross products of the increments of two distinct
coordinates over the cells of a uniform grid. -/
lemma solution (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d) {i j : Fin d} (hij : i ≠ j)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (m : ℕ) :
    Integrable (fun ω => (∑ k ∈ Finset.range m,
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)) ^ 2) P
    ∧ ∫ ω, (∑ k ∈ Finset.range m,
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)) ^ 2 ∂P
      = m * h ^ 2 := by
  have hg0 : ∀ k : ℕ, 0 ≤ LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_nonneg ha hh.le
  have hglt : ∀ k : ℕ, LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k < LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1) := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_lt_succ hh
  -- the functional on path space picking out the product of two increments
  have hφ : ∀ k l : ℕ, Measurable fun path : ℝ → ℝ =>
      (path (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) - path (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k))
        * (path (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) - path (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l)) := fun k l => by
    fun_prop
  have hind : ∀ k l : ℕ, IndepFun
      (fun ω => ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
      (fun ω => ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) P :=
    fun k l => LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.indepFun_comp_coord W hij (hφ k l) (hφ k l)
  have hint2 : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P) (k l : ℕ), Integrable
      (fun ω => (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) P := fun V k l =>
    MemLp.integrable_mul (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le V (hg0 k) (hglt k).le)
      (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le V (hg0 l) (hglt l).le)
  have hcov : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P), LevyStochCalc.Brownian.IsBrownianFiltration V ℱ → ∀ k l : ℕ,
      ∫ ω, (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω) ∂P
        = if k = l then h else 0 := by
    intro V hV k l
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · rw [if_neg hkl.ne]
      exact LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_increment_mul_increment_eq_zero V hV
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono hh.le hkl.le) (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono hh.le hkl) (hg0 l) (hglt l)
    · have hsq := LevyStochCalc.Brownian.Ito.integral_increment_sq V (hg0 k) (hglt k)
      rw [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_succ_sub] at hsq
      have hsq' : ∫ ω, (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω) ∂P
          = ∫ ω, (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω) ^ 2 ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => (sq _).symm)
      rw [if_pos rfl, hsq', hsq]
    · rw [if_neg hlk.ne']
      rw [show (fun ω => (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
          = fun ω => (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
            * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω) from
        funext fun ω => mul_comm _ _]
      exact LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_increment_mul_increment_eq_zero V hV
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono hh.le hlk.le) (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono hh.le hlk) (hg0 k) (hglt k)
  have hterm : ∀ k l : ℕ,
      ∫ ω, (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) ∂P
        = if k = l then h ^ 2 else 0 := by
    intro k l
    have hrw : (fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)))
        = fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
        * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) := by
      funext ω; ring
    rw [hrw]
    have hmul := (hind k l).integral_mul_eq_mul_integral
      (hint2 (W.W i) k l).1 (hint2 (W.W j) k l).1
    rw [show ∫ ω, (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
        * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) ∂P
        = (∫ ω, ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω) ∂P)
        * ∫ ω, ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω) ∂P from hmul,
      hcov (W.W i) (hcoord i) k l, hcov (W.W j) (hcoord j) k l]
    by_cases hkl : k = l
    · simp [hkl, sq]
    · simp [hkl]
  have hint : ∀ k l : ℕ, Integrable
      (fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))) P := by
    intro k l
    have hrw : (fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)))
        = fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
        * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) := by
      funext ω; ring
    rw [hrw]
    exact (hind k l).integrable_mul (hint2 (W.W i) k l) (hint2 (W.W j) k l)
  have hexp : (fun ω => (∑ k ∈ Finset.range m,
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)) ^ 2)
      = fun ω => ∑ k ∈ Finset.range m, ∑ l ∈ Finset.range m,
        (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) := by
    funext ω
    rw [sq, Finset.sum_mul_sum]
  rw [hexp]
  refine ⟨integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l, ?_⟩
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  simp_rw [integral_finsetSum _ fun l _ => hint _ l, hterm, Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl fun x hx => if_pos hx, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
