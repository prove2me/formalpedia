-- Prove2me | solution 1 for LevyStochCalc.Brownian.BrownianMotion.hasIndepIncrements_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:02:37.754878+00:00
-- url     : https://prove2.me/submissions/6a2ba6ec-1135-496a-b271-5e25e63fd39b

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
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
import Theorems.Thm_LevyStochCalc_Brownian_iIndep_of_indep_biSup_lt_408915f

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
namespace LevyStochCalc.Brownian.BrownianMotion
end LevyStochCalc.Brownian.BrownianMotion
open LevyStochCalc.Brownian.BrownianMotion in
/-- A Brownian motion, read on nonnegative times, has independent increments. -/
theorem solution (W : LevyStochCalc.Brownian.BrownianMotion P) :
    HasIndepIncrements (fun t : ℝ≥0 ↦ W.W t) P := by
  intro n t ht
  refine (iIndepFun_iff_iIndep _ _ _).2 (LevyStochCalc.Brownian.iIndep_of_indep_biSup_lt_408915f fun i ↦ ?_)
  have hab : ((t i.castSucc : ℝ)) ≤ (t i.succ : ℝ) :=
    NNReal.coe_le_coe.2 (ht (Fin.castSucc_le_succ i))
  have hsub : (⨆ j < i, MeasurableSpace.comap
        (fun ω ↦ W.W (t j.succ : ℝ) ω - W.W (t j.castSucc : ℝ) ω) inferInstance)
      ≤ ⨆ q ∈ Set.Iic ((t i.castSucc : ℝ)),
        MeasurableSpace.comap (W.W q) inferInstance := by
    refine iSup₂_le fun j hj ↦ ?_
    have hji : (j : ℕ) < (i : ℕ) := hj
    have hjs : ((t j.succ : ℝ)) ≤ (t i.castSucc : ℝ) := by
      refine NNReal.coe_le_coe.2 (ht ?_)
      rw [Fin.le_def]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have hjc : ((t j.castSucc : ℝ)) ≤ (t i.castSucc : ℝ) :=
      le_trans (NNReal.coe_le_coe.2 (ht (Fin.castSucc_le_succ j))) hjs
    have hmem : ∀ {r : ℝ}, r ≤ (t i.castSucc : ℝ) →
        Measurable[⨆ q ∈ Set.Iic ((t i.castSucc : ℝ)),
          MeasurableSpace.comap (W.W q) inferInstance] (W.W r) := fun {r} hr ↦
      Measurable.of_comap_le (le_iSup₂ (f := fun q (_ : q ∈ Set.Iic ((t i.castSucc : ℝ))) ↦
        MeasurableSpace.comap (W.W q) inferInstance) r hr)
    exact Measurable.comap_le ((hmem hjs).sub (hmem hjc))
  rcases eq_or_lt_of_le hab with hEq | hLt
  · have hconst : (fun ω ↦ W.W (t i.succ : ℝ) ω - W.W (t i.castSucc : ℝ) ω)
        = fun _ : Ω ↦ (0 : ℝ) := by
      funext ω; rw [hEq]; ring
    have hbot : MeasurableSpace.comap
        (fun ω ↦ W.W (t i.succ : ℝ) ω - W.W (t i.castSucc : ℝ) ω) inferInstance
        = (⊥ : MeasurableSpace Ω) := by
      rw [hconst]; exact MeasurableSpace.comap_const 0
    exact indep_of_indep_of_le_right (indep_bot_right _) (le_of_eq hbot)
  · exact indep_of_indep_of_le_left
      (W.joint_increment_independent (t i.castSucc).coe_nonneg hLt) hsub
