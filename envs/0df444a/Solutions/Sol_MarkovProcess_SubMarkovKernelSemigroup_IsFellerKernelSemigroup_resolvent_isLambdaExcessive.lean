-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.resolvent_isLambdaExcessive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:54:03.364336+00:00
-- url     : https://prove2.me/submissions/63598de4-1803-4b8e-bf71-74834c8024cd

import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
import Definitions.Def_MarkovProcess_V3H_Trajectory_DynkinMartingale_970781f3
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExcessiveStopping_8ea33a1f
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_exp_smul_operator_sub_eq_integral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Kernel operators on continuous functions vanishing at infinity

This file records the spatial `C₀` property of a sub-Markov kernel semigroup and packages its
raw integral as a contractive continuous linear map on `C₀(α, ℝ)`.  It makes no assertion about
continuity in time or the existence of an associated stochastic process.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal ZeroAtInfty

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]



variable (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0)





variable [BorelSpace α]















/-- The `C₀` kernel operator preserves pointwise nonnegativity. -/
theorem c0Operator_apply_nonneg (t : NNReal) {f : C₀(α, ℝ)}
    (hf : ∀ x, 0 ≤ f x) (x : α) : 0 ≤ P.c0Operator hC0 t f x := by
  rw [c0Operator_apply]
  exact integral_nonneg hf

end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Excessive functions and stopping

This file turns the semigroup definition of an exponentially excessive `C₀` function into a
supermartingale along the canonical continuous process.  Continuous-time optional stopping then
gives the corresponding inequality at bounded stopping times and, by Fatou's lemma, at the finite
exit time from an open set.

The exit inequality is the lower-bound half paired with
`IsFellerKernelSemigroup.lintegral_pathResolvent_eq_killedResolvent_add`.  No model-specific
assumptions enter here.

Main results: `IsFellerKernelSemigroup.resolvent_isLambdaExcessive`,
`IsLambdaExcessive.supermartingale_discountedValueProcess`,
`IsLambdaExcessive.integral_discountedValueProcess_stoppingTime_le`, and
`IsLambdaExcessive.lintegral_discountedValue_exitTime_le`.

No converse characterization of excessive functions is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

section Supermedian

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}





end Supermedian

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}























end

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Excessive functions and stopping

This file turns the semigroup definition of an exponentially excessive `C₀` function into a
supermartingale along the canonical continuous process.  Continuous-time optional stopping then
gives the corresponding inequality at bounded stopping times and, by Fatou's lemma, at the finite
exit time from an open set.

The exit inequality is the lower-bound half paired with
`IsFellerKernelSemigroup.lintegral_pathResolvent_eq_killedResolvent_add`.  No model-specific
assumptions enter here.

Main results: `IsFellerKernelSemigroup.resolvent_isLambdaExcessive`,
`IsLambdaExcessive.supermartingale_discountedValueProcess`,
`IsLambdaExcessive.integral_discountedValueProcess_stoppingTime_le`, and
`IsLambdaExcessive.lintegral_discountedValue_exitTime_le`.

No converse characterization of excessive functions is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty




variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}



namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] in

theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (lam : ℝ) (hlam : 0 < lam)
    (f : C₀(alpha, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    P.IsLambdaExcessive lam
      (hFeller.c0Semigroup.resolvent (⟨lam, hlam⟩ : Semigroup.PositiveShift) f) := by
  let mu : Semigroup.PositiveShift := ⟨lam, hlam⟩
  let S := hFeller.c0Semigroup
  let v : C₀(alpha, ℝ) := S.resolvent mu f
  have hv : ∀ x, 0 ≤ v x := by
    intro x
    dsimp only [v, S]
    rw [hFeller.resolvent_apply_apply]
    exact integral_nonneg fun t ↦ mul_nonneg (Real.exp_pos _).le (integral_nonneg hf)
  change P.IsLambdaExcessive lam v
  refine ⟨hv, fun t x ↦ ?_⟩
  change Real.exp (-lam * (t : ℝ)) * S t v x ≤ v x
  let vdom : S.generatorDomain := ⟨v, by
    dsimp only [v]
    exact S.resolvent_mem_generatorDomain mu f⟩
  have hgen : S.generator vdom - lam • (vdom : C₀(alpha, ℝ)) = -f := by
    have hgenerator : S.generator vdom = lam • v - f := by
      dsimp only [vdom, v]
      exact S.generator_resolvent mu f
    rw [hgenerator]
    change (lam • v - f) - lam • v = -f
    module
  have hidentity : Real.exp (-lam * (t : ℝ)) * S t v x - v x =
      ∫ s in (0 : ℝ)..t,
        Real.exp (-lam * s) * S (Real.toNNReal s) (-f) x := by
    calc
      Real.exp (-lam * (t : ℝ)) * S t v x - v x =
          c0EvalCLM x (Real.exp (-lam * (t : ℝ)) • S t (vdom : C₀(alpha, ℝ)) - vdom) := by
        rw [map_sub, map_smul, c0EvalCLM_apply, c0EvalCLM_apply, smul_eq_mul]
      _ = c0EvalCLM x (∫ s in (0 : ℝ)..t, Real.exp (-lam * s) •
            S (Real.toNNReal s) (S.generator vdom - lam • (vdom : C₀(alpha, ℝ)))) := by
        rw [S.exp_smul_operator_sub_eq_integral vdom lam t]
      _ = c0EvalCLM x (∫ s in (0 : ℝ)..t,
            Real.exp (-lam * s) • S (Real.toNNReal s) (-f)) := by rw [hgen]
      _ = ∫ s in (0 : ℝ)..t,
            c0EvalCLM x (Real.exp (-lam * s) • S (Real.toNNReal s) (-f)) := by
        rw [← (c0EvalCLM x).intervalIntegral_comp_comm]
        exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
          (S.continuous_operator_toNNReal (-f))).intervalIntegrable _ _
      _ = ∫ s in (0 : ℝ)..t,
            Real.exp (-lam * s) * S (Real.toNNReal s) (-f) x := by
        refine intervalIntegral.integral_congr fun s _ ↦ ?_
        rw [map_smul, c0EvalCLM_apply, smul_eq_mul]
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..t,
      Real.exp (-lam * s) * S (Real.toNNReal s) f x := by
    refine intervalIntegral.integral_nonneg t.coe_nonneg fun s _ ↦
      mul_nonneg (Real.exp_pos _).le ?_
    change 0 ≤ P.c0Operator hFeller.mapsC0 (Real.toNNReal s) f x
    exact P.c0Operator_apply_nonneg hFeller.mapsC0 _ hf x
  have hneg : (∫ s in (0 : ℝ)..t,
      Real.exp (-lam * s) * S (Real.toNNReal s) (-f) x) =
      -(∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * S (Real.toNNReal s) f x) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    rw [map_neg]
    change Real.exp (-lam * s) * (-S (Real.toNNReal s) f x) =
      -(Real.exp (-lam * s) * S (Real.toNNReal s) f x)
    ring
  apply sub_nonpos.mp
  rw [hidentity, hneg]
  exact neg_nonpos.mpr hnonneg
