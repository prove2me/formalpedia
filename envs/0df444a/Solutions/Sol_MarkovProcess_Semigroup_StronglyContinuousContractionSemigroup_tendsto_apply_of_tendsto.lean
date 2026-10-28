-- Prove2me | solution 1 for MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_apply_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:00:18.250143+00:00
-- url     : https://prove2.me/submissions/cc01e08e-2a1e-44bd-9f58-b56050dd7dad

import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_C0_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess MarkovProcess.Semigroup MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strongly continuous contraction semigroups

This file provides a small reusable interface for strongly continuous contraction
semigroups on real normed spaces, parametrized by nonnegative real time.
-/

open Filter Topology

namespace MarkovProcess.Semigroup



namespace StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





variable (S : StronglyContinuousContractionSemigroup E)









theorem norm_operator_le_one (t : NNReal) : ‖S t‖ ≤ 1 :=
  S.opNorm_le_one t



theorem dist_apply_le (t : NNReal) (x y : E) : dist (S t x) (S t y) ≤ dist x y := by
  calc
    dist (S t x) (S t y) ≤ ‖S t‖ * dist x y := (S t).dist_le_opNorm x y
    _ ≤ 1 * dist x y :=
      mul_le_mul_of_nonneg_right (S.norm_operator_le_one t) dist_nonneg
    _ = dist x y := one_mul _

theorem continuous (x : E) : Continuous (fun t ↦ S t x) :=
  S.continuous_orbit x
end StronglyContinuousContractionSemigroup
end MarkovProcess.Semigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuity tools for finite-time Feller kernels

This file records the analytic continuity mechanism needed in a recursive proof of continuity of
finite-time laws.  In particular, strong continuity and contractivity imply joint continuity in
the time and in a varying `C₀` test function.  After evaluation, this gives convergence of kernel
integrals when both the transition time and the test function vary.

The extension from product tests to arbitrary compactly supported tests on a finite product is
not asserted here.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem solution
    (S : StronglyContinuousContractionSemigroup E) {X : Type*} {l : Filter X}
    {t : X → NNReal} {t₀ : NNReal} {f : X → E} {f₀ : E}
    (ht : Tendsto t l (nhds t₀)) (hf : Tendsto f l (nhds f₀)) :
    Tendsto (fun x ↦ S (t x) (f x)) l (nhds (S t₀ f₀)) := by
  rw [Metric.tendsto_nhds] at hf ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have htime : ∀ᶠ x in l, dist (S (t x) f₀) (S t₀ f₀) < ε / 2 :=
    ((S.continuous f₀).tendsto t₀ |>.comp ht) (Metric.ball_mem_nhds _ hhalf)
  filter_upwards [hf (ε / 2) hhalf, htime] with x hx htx
  calc
    dist (S (t x) (f x)) (S t₀ f₀)
        ≤ dist (S (t x) (f x)) (S (t x) f₀) +
            dist (S (t x) f₀) (S t₀ f₀) := dist_triangle _ _ _
    _ ≤ dist (f x) f₀ + dist (S (t x) f₀) (S t₀ f₀) :=
      by
        simpa only [add_comm] using
          add_le_add_right (S.dist_apply_le (t x) (f x) f₀)
            (dist (S (t x) f₀) (S t₀ f₀))
    _ < ε / 2 + ε / 2 := add_lt_add hx htx
    _ = ε := add_halves ε
