-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_zero_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:16:38.581552+00:00
-- url     : https://prove2.me/submissions/11b9e07f-b2f4-4b98-aad6-9fcfcfc0f9d0

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
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_crossSum_sq_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_mul_increment_mul_increment_eq_crossSum_408915f

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
section Increments
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
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
namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
open LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion in
/-- **The cross term over a common interval vanishes.** For distinct coordinates, the product of
the two increments over one interval is orthogonal to every bounded coefficient measurable at its
start. -/
theorem solution (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d) {i j : Fin d}
    (hij : i ≠ j) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ a] Z) (hZm : Measurable Z) {C : ℝ}
    (hZb : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * (((W.W i).W b ω - (W.W i).W a ω) * ((W.W j).W b ω - (W.W j).W a ω)) ∂P = 0 := by
  set I := ∫ ω, Z ω * (((W.W i).W b ω - (W.W i).W a ω) * ((W.W j).W b ω - (W.W j).W a ω)) ∂P
    with hI
  have hC : ∀ ω, |Z ω| ≤ |C| := fun ω => (hZb ω).trans (le_abs_self C)
  have hCabs : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ |C| :=
    Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ,
      |I| ≤ |C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * (1 / ((m : ℝ) + 1)) := by
    intro ε hε m
    have hnpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hh : 0 < (b - a) / (m + 1 : ℕ) := div_pos (by linarith) hnpos
    have hgm : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (m + 1) = b := by
      simp only [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid]
      field_simp
      ring
    obtain ⟨hQ2int, hQ2⟩ := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_crossSum_sq_408915f W hij hcoord ha hh (m + 1)
    have hI' := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_crossSum_408915f W i j hcoord ha hh (m + 1) hZ
      hZm hZb
    rw [hgm] at hI'
    rw [hI, hI']
    have hg0 : ∀ k : ℕ, 0 ≤ LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_nonneg ha hh.le
    have hglt : ∀ k : ℕ, LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k
        < LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1) := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_lt_succ hh
    have hQint : Integrable (fun ω => ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) P :=
      integrable_finsetSum _ fun k _ => MemLp.integrable_mul
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le (W.W i) (hg0 k) (hglt k).le)
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le (W.W j) (hg0 k) (hglt k).le)
    have hZQ := Integrable.bdd_mul hQint hZm.aestronglyMeasurable hCabs
    -- the arithmetic-geometric bound
    have hpt : ∀ ω, |Z ω * ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)|
        ≤ |C| * ε / 2 + |C| / (2 * ε) * (∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) ^ 2 := by
      intro ω
      generalize (∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) = Q
      have hQ : |Q| ≤ ε / 2 + Q ^ 2 / (2 * ε) := by
        rw [div_add_div _ _ two_ne_zero (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (ε - |Q|), sq_abs Q]
      calc |Z ω * Q| = |Z ω| * |Q| := abs_mul _ _
        _ ≤ |C| * (ε / 2 + Q ^ 2 / (2 * ε)) :=
          mul_le_mul (hC ω) hQ (abs_nonneg _) (abs_nonneg _)
        _ = |C| * ε / 2 + |C| / (2 * ε) * Q ^ 2 := by ring
    calc |∫ ω, Z ω * ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω) ∂P|
        ≤ ∫ ω, |Z ω * ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)| ∂P :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ ω, (|C| * ε / 2 + |C| / (2 * ε) * (∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) ^ 2) ∂P :=
          integral_mono hZQ.abs ((integrable_const _).add (hQ2int.const_mul _)) hpt
      _ = |C| * ε / 2 + |C| / (2 * ε) * ((m + 1 : ℕ) * ((b - a) / (m + 1 : ℕ)) ^ 2) := by
          rw [integral_add (integrable_const _) (hQ2int.const_mul _), integral_const,
            integral_const_mul, hQ2]
          simp
      _ = |C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * (1 / ((m : ℝ) + 1)) := by
          have hn : ((m : ℝ) + 1) ≠ 0 := by positivity
          push_cast
          rw [div_pow, mul_div_assoc', sq ((m : ℝ) + 1), mul_div_mul_left _ _ hn]
          ring
  have hlim : ∀ ε : ℝ, 0 < ε → |I| ≤ |C| * ε / 2 := by
    intro ε hε
    have ht : Filter.Tendsto (fun m : ℕ =>
        |C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * (1 / ((m : ℝ) + 1))) Filter.atTop
        (nhds (|C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * 0)) :=
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _)
    rw [mul_zero, add_zero] at ht
    exact ge_of_tendsto' ht (hbound ε hε)
  have hI0 : |I| ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have h1 := hlim (|I| / (|C| + 1)) (by positivity)
    have h2 : |C| * (|I| / (|C| + 1)) ≤ |I| := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg C, abs_nonneg I]
    linarith
  exact abs_nonpos_iff.mp hI0
