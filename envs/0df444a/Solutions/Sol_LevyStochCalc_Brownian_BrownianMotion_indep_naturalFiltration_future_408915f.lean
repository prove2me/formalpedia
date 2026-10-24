-- Prove2me | solution 1 for LevyStochCalc.Brownian.BrownianMotion.indep_naturalFiltration_future_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:04:08.189258+00:00
-- url     : https://prove2.me/submissions/f0aedc94-cc13-456a-bb1e-c8bf7fdddd57

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
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
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.AddContent
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
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasIndepIncrements_408915f
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_408915f
import Theorems.Thm_LevyStochCalc_Probability_IsTrivialSigma_indep_408915f
import Theorems.Thm_LevyStochCalc_Probability_indep_sup_left_of_indep_408915f
import Theorems.Thm_LevyStochCalc_Probability_isTrivialSigma_comap_of_ae_const_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/MathlibBridge.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
open MeasureTheory ProbabilityTheory
open scoped NNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
section
namespace LevyStochCalc.Brownian.BrownianMotion
end LevyStochCalc.Brownian.BrownianMotion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.BrownianMotion
/-- A Brownian motion, read on nonnegative times, is a pre-Brownian motion. -/
theorem LevyStochCalc.Brownian.BrownianMotion.isPreBrownianReal (W : BrownianMotion P) :
    IsPreBrownianReal (fun t : ℝ≥0 ↦ W.W t) P :=
  HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t ↦ W.hasLaw_eval_408915f t) W.hasIndepIncrements_408915f
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/TrivialSigma.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
theorem LevyStochCalc.Probability.isTrivialSigma_trivialSigma [IsProbabilityMeasure P] :
    IsTrivialSigma P (trivialSigma mΩ P) := fun _ hA => hA.2
theorem LevyStochCalc.Probability.trivialSigma_le [IsProbabilityMeasure P] : trivialSigma mΩ P ≤ mΩ := fun _ hA => hA.1
/-- The σ-algebra generated by an almost-surely constant random variable sits inside the
null-or-conull σ-algebra. -/
theorem LevyStochCalc.Probability.comap_le_trivialSigma [IsProbabilityMeasure P] {𝓨 : Type*} [MeasurableSpace 𝓨]
    {f : Ω → 𝓨} {y : 𝓨} (hf : Measurable f) (h : ∀ᵐ ω ∂P, f ω = y) :
    MeasurableSpace.comap f inferInstance ≤ trivialSigma mΩ P := fun A hA =>
  ⟨by obtain ⟨S, hS, rfl⟩ := hA; exact hf hS, isTrivialSigma_comap_of_ae_const_408915f h A hA⟩
/-- **A trivial factor can be joined onto either side of an independence statement.** -/
theorem LevyStochCalc.Probability.IsTrivialSigma.indep_sup [IsProbabilityMeasure P] {m₁ m₂ m₃ : MeasurableSpace Ω}
    (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) (h₃ : m₃ ≤ mΩ) (h : IsTrivialSigma P m₂)
    (h13 : Indep m₁ m₃ P) : Indep (m₁ ⊔ m₂) m₃ P :=
  indep_sup_left_of_indep_408915f h₁ h₂ h₃ h13 (h.indep_408915f h₂)
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/FutureIndependence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
open MeasureTheory ProbabilityTheory
open scoped NNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
section
namespace LevyStochCalc.Brownian.BrownianMotion
end LevyStochCalc.Brownian.BrownianMotion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.BrownianMotion
namespace LevyStochCalc.Brownian.BrownianMotion
end LevyStochCalc.Brownian.BrownianMotion
open LevyStochCalc.Brownian.BrownianMotion in
/-- **Weak Markov property, σ-algebra form.** For `0 ≤ s` the natural filtration of a Brownian
motion at time `s` is independent of the σ-algebra generated by all increments `W t - W s`,
`t > s`. -/
theorem solution (W : LevyStochCalc.Brownian.BrownianMotion P) {s : ℝ} (hs : 0 ≤ s) :
    Indep (LevyStochCalc.Brownian.Martingale.naturalFiltration W s)
      (⨆ t ∈ Set.Ioi s, MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance) P := by
  have hs₀ : ((Real.toNNReal s : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs
  -- The past path on `[0, s]` is independent of the whole shifted increment path.
  have hindep :
      Indep (MeasurableSpace.comap
          (fun ω (r : Set.Iic (Real.toNNReal s)) => W.W ((r : ℝ≥0) : ℝ) ω) inferInstance)
        (MeasurableSpace.comap
          (fun ω (r : ℝ≥0) => W.W ((Real.toNNReal s + r : ℝ≥0) : ℝ) ω
            - W.W ((Real.toNNReal s : ℝ≥0) : ℝ) ω) inferInstance) P :=
    (W.isPreBrownianReal.indepFun_shift (Real.toNNReal s)).symm
  -- Each increment based at `s` is a coordinate of the shifted increment path.
  have hfut : (⨆ t ∈ Set.Ioi s,
        MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance)
      ≤ MeasurableSpace.comap
        (fun ω (r : ℝ≥0) => W.W ((Real.toNNReal s + r : ℝ≥0) : ℝ) ω
          - W.W ((Real.toNNReal s : ℝ≥0) : ℝ) ω) inferInstance := by
    refine iSup₂_le fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := hs.trans (Set.mem_Ioi.mp ht).le
    have hst : Real.toNNReal s ≤ Real.toNNReal t :=
      Real.toNNReal_le_toNNReal (Set.mem_Ioi.mp ht).le
    have hfun : (fun ω => W.W t ω - W.W s ω)
        = (fun p : ℝ≥0 → ℝ => p (Real.toNNReal t - Real.toNNReal s))
          ∘ (fun ω (r : ℝ≥0) => W.W ((Real.toNNReal s + r : ℝ≥0) : ℝ) ω
              - W.W ((Real.toNNReal s : ℝ≥0) : ℝ) ω) := by
      funext ω
      simp only [Function.comp_apply, add_tsub_cancel_of_le hst, Real.coe_toNNReal t ht0, hs₀]
    rw [hfun]
    exact Measurable.comap_le ((measurable_pi_apply _).comp (Measurable.of_comap_le le_rfl))
  -- Each generator of the natural filtration at a nonnegative time is a coordinate of the past
  -- path; the generators at negative times are almost surely constant.
  have hnat : LevyStochCalc.Brownian.Martingale.naturalFiltration W s
      ≤ MeasurableSpace.comap
          (fun ω (r : Set.Iic (Real.toNNReal s)) => W.W ((r : ℝ≥0) : ℝ) ω) inferInstance
        ⊔ LevyStochCalc.Probability.trivialSigma ‹MeasurableSpace Ω› P := by
    have hseq : LevyStochCalc.Brownian.Martingale.naturalFiltration W s
        = ⨆ j ≤ s, MeasurableSpace.comap (W.W j) inferInstance := rfl
    rw [hseq]
    refine iSup₂_le fun j hj => ?_
    rcases le_or_gt 0 j with hj0 | hj0
    · refine le_sup_of_le_left ?_
      have hjs : Real.toNNReal j ≤ Real.toNNReal s := Real.toNNReal_le_toNNReal hj
      have hfun : W.W j
          = (fun p : Set.Iic (Real.toNNReal s) → ℝ => p ⟨Real.toNNReal j, hjs⟩)
            ∘ (fun ω (r : Set.Iic (Real.toNNReal s)) => W.W ((r : ℝ≥0) : ℝ) ω) := by
        funext ω
        show W.W j ω = W.W ((Real.toNNReal j : ℝ≥0) : ℝ) ω
        rw [Real.coe_toNNReal j hj0]
      rw [hfun]
      exact Measurable.comap_le ((measurable_pi_apply _).comp (Measurable.of_comap_le le_rfl))
    · exact le_sup_of_le_right
        (LevyStochCalc.Probability.comap_le_trivialSigma (y := 0) (W.measurable_eval j) (W.negative_zero j hj0))
  refine indep_of_indep_of_le_left (LevyStochCalc.Probability.IsTrivialSigma.indep_sup ?_
    LevyStochCalc.Probability.trivialSigma_le ?_ LevyStochCalc.Probability.isTrivialSigma_trivialSigma
    (indep_of_indep_of_le_right hindep hfut)) hnat
  · exact Measurable.comap_le (measurable_pi_lambda _ fun r => W.measurable_eval ((r : ℝ≥0) : ℝ))
  · exact iSup₂_le fun t _ => Measurable.comap_le
      ((W.measurable_eval t).sub (W.measurable_eval s))
