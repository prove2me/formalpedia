-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_crossSum_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:14:54.155888+00:00
-- url     : https://prove2.me/submissions/9e393675-7216-4789-8594-8df2018a3a06

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
/-- An increment of a Brownian motion over a possibly degenerate interval is square-integrable. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le (V : BrownianMotion P) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    MemLp (fun ω => V.W q ω - V.W p ω) 2 P := by
  rcases eq_or_lt_of_le hpq with h | h
  · subst h
    simp only [sub_self]
    exact memLp_const 0
  · exact Ito.memLp_increment V hp h 2 (by simp)
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
/-- A coefficient measurable at the start of an interval is orthogonal to the Brownian increment
over it. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero (V : BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hV : IsBrownianFiltration V ℱ) {s u : ℝ}
    (hs : 0 ≤ s) (hsu : s < u) {Y : Ω → ℝ} (hY : StronglyMeasurable[ℱ s] Y) (hYm : Measurable Y) :
    ∫ ω, Y ω * (V.W u ω - V.W s ω) ∂P = 0 := by
  have h := Ito.integral_mul_increment_pow_408915f V ℱ hV hs hsu hY hYm 1
  rw [Ito.integral_increment_pow_odd V hs hsu odd_one, mul_zero] at h
  simpa only [pow_one] using h
namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
open LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion in
/-- Against a bounded coefficient measurable at the start of a uniform grid, the product of the
increments of two coordinates over the whole grid pairs like the sum of the cell-wise cross
products. -/
lemma solution (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (i j : Fin d) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (m : ℕ) {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ a] Z)
    (hZm : Measurable Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h m) ω - (W.W i).W a ω)
      * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h m) ω - (W.W j).W a ω)) ∂P
      = ∫ ω, Z ω * ∑ k ∈ Finset.range m,
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω) ∂P := by
  have hg0 : ∀ k : ℕ, 0 ≤ LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_nonneg ha hh.le
  have hglt : ∀ k : ℕ, LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k < LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1) := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_lt_succ hh
  have hag : ∀ k : ℕ, a ≤ LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.le_affineGrid hh.le
  have hCabs : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ |C| := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact (hZb ω).trans (le_abs_self C)
  have hAm : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P) (k : ℕ),
      Measurable fun ω => V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - V.W a ω :=
    fun V k => (V.measurable_eval _).sub (V.measurable_eval _)
  -- a bounded coefficient times a past increment is killed by a fresh increment
  have hzero : ∀ (V V' : LevyStochCalc.Brownian.BrownianMotion P), LevyStochCalc.Brownian.IsBrownianFiltration V ℱ →
      LevyStochCalc.Brownian.IsBrownianFiltration V' ℱ → ∀ k : ℕ,
      ∫ ω, Z ω * ((V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - V.W a ω)
        * (V'.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V'.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)) ∂P = 0 := by
    intro V V' hV hV' k
    have hY : StronglyMeasurable[ℱ (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k)] fun ω =>
        Z ω * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - V.W a ω) :=
      (hZ.mono (ℱ.mono (hag k))).mul
        ((hV.measurable _).sub ((hV.measurable a).mono (ℱ.mono (hag k)) le_rfl)).stronglyMeasurable
    have h := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero V' hV' (hg0 k) (hglt k) hY (hZm.mul (hAm V k))
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (mul_assoc _ _ _).symm)
  have hintA : ∀ (V V' : LevyStochCalc.Brownian.BrownianMotion P) (k : ℕ), Integrable (fun ω =>
      Z ω * ((V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - V.W a ω)
        * (V'.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V'.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))) P := fun V V' k =>
    Integrable.bdd_mul (MemLp.integrable_mul (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le V ha (hag k))
      (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le V' (hg0 k) (hglt k).le)) hZm.aestronglyMeasurable hCabs
  have hintΔ : ∀ k : ℕ, Integrable (fun ω =>
      Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))) P := fun k =>
    Integrable.bdd_mul (MemLp.integrable_mul (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le (W.W i) (hg0 k) (hglt k).le)
      (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le (W.W j) (hg0 k) (hglt k).le)) hZm.aestronglyMeasurable hCabs
  have htel : ∀ ω, Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h m) ω - (W.W i).W a ω)
        * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h m) ω - (W.W j).W a ω))
      = ∑ k ∈ Finset.range m,
        (Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W i).W a ω)
            * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
          + Z ω * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W j).W a ω)
            * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
          + Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
            * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))) := by
    intro ω
    have h0 := Finset.sum_range_sub (fun k => ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W i).W a ω)
      * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W j).W a ω)) m
    simp only [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_zero, sub_self, mul_zero, sub_zero] at h0
    rw [← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hint3 : ∀ k : ℕ, Integrable (fun ω =>
      Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W i).W a ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        + Z ω * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W j).W a ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        + Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))) P :=
    fun k => ((hintA (W.W i) (W.W j) k).add (hintA (W.W j) (W.W i) k)).add (hintΔ k)
  have hint12 : ∀ k : ℕ, Integrable (fun ω =>
      Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W i).W a ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        + Z ω * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W j).W a ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))) P :=
    fun k => (hintA (W.W i) (W.W j) k).add (hintA (W.W j) (W.W i) k)
  rw [integral_congr_ae (Filter.Eventually.of_forall htel), integral_finsetSum _ fun k _ => hint3 k]
  simp_rw [integral_add (hint12 _) (hintΔ _),
    integral_add (hintA (W.W i) (W.W j) _) (hintA (W.W j) (W.W i) _),
    hzero (W.W i) (W.W j) (hcoord i) (hcoord j), hzero (W.W j) (W.W i) (hcoord j) (hcoord i),
    add_zero, zero_add]
  rw [← integral_finsetSum _ fun k _ => hintΔ k]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (Finset.mul_sum _ _ _).symm)
