-- Prove2me | solution 1 for MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.hasDerivWithinAt_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:16:05.502817+00:00
-- url     : https://prove2.me/submissions/dbff0709-0158-4481-afb7-093aaf43ed3c

import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The generator of a strongly continuous contraction semigroup

For `S : StronglyContinuousContractionSemigroup E` this file defines the generator domain
`S.generatorDomain`, the submodule of vectors `f` whose difference quotients
`t⁻¹ • (S t f - f)` converge as `t → 0⁺`, and the generator
`S.generator : S.generatorDomain →ₗ[ℝ] E` as that limit.  The main results are:

* `tendsto_generator`: the defining limit, and `generator_eq_of_tendsto`, its uniqueness;
* `operator_mem_generatorDomain` and `generator_operator`: the domain is invariant under every
  `S t`, and `S t` commutes with the generator;
* `tendsto_differenceQuotient_add`: every orbit `t ↦ S t f` of a vector in the domain is right
  differentiable at every time, with derivative `S t (S.generator f)`; its real-variable forms are
  `hasDerivWithinAt_Ioi` and `hasDerivWithinAt_Ici`, and at positive times the derivative is
  two-sided, `hasDerivAt_operator_toNNReal`;
* `operator_sub_eq_integral` and `exp_smul_operator_sub_eq_integral`: the fundamental identity
  and its exponentially weighted form;
* `orbitIntegral_mem_generatorDomain` and `generator_orbitIntegral`: for every vector `f`, the
  orbit integral `∫₀ᵗ S s f ds` lies in the domain with generator `S t f - f`; hence
  `dense_generatorDomain`, the domain is dense.

Times are `NNReal` throughout the library; the real-variable statements read the semigroup at
`Real.toNNReal s`.  The fundamental identity is what Dynkin's formula consumes.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)

section DifferenceQuotient













end DifferenceQuotient

section Domain







end Domain

section Generator

















end Generator

section Invariance







end Invariance

section RealVariable















variable [CompleteSpace E]





end RealVariable

section OrbitIntegral









variable [CompleteSpace E]















end OrbitIntegral

end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup


open MarkovProcess
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The generator of a strongly continuous contraction semigroup

For `S : StronglyContinuousContractionSemigroup E` this file defines the generator domain
`S.generatorDomain`, the submodule of vectors `f` whose difference quotients
`t⁻¹ • (S t f - f)` converge as `t → 0⁺`, and the generator
`S.generator : S.generatorDomain →ₗ[ℝ] E` as that limit.  The main results are:

* `tendsto_generator`: the defining limit, and `generator_eq_of_tendsto`, its uniqueness;
* `operator_mem_generatorDomain` and `generator_operator`: the domain is invariant under every
  `S t`, and `S t` commutes with the generator;
* `tendsto_differenceQuotient_add`: every orbit `t ↦ S t f` of a vector in the domain is right
  differentiable at every time, with derivative `S t (S.generator f)`; its real-variable forms are
  `hasDerivWithinAt_Ioi` and `hasDerivWithinAt_Ici`, and at positive times the derivative is
  two-sided, `hasDerivAt_operator_toNNReal`;
* `operator_sub_eq_integral` and `exp_smul_operator_sub_eq_integral`: the fundamental identity
  and its exponentially weighted form;
* `orbitIntegral_mem_generatorDomain` and `generator_orbitIntegral`: for every vector `f`, the
  orbit integral `∫₀ᵗ S s f ds` lies in the domain with generator `S t f - f`; hence
  `dense_generatorDomain`, the domain is dense.

Times are `NNReal` throughout the library; the real-variable statements read the semigroup at
`Real.toNNReal s`.  The fundamental identity is what Dynkin's formula consumes.
-/

open Filter Topology
open scoped NNReal



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)












namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
theorem solution (f : S.generatorDomain) (t : NNReal) :
    HasDerivWithinAt (fun s : ℝ ↦ S (Real.toNNReal s) f) (S t (S.generator f))
      (Set.Ioi (t : ℝ)) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hdiff : Set.Ioi (t : ℝ) \ {(t : ℝ)} = Set.Ioi (t : ℝ) := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact fun hy ↦ ne_of_gt hy
  rw [hdiff]
  refine ((S.tendsto_differenceQuotient_add f t).comp (tendsto_toNNReal_sub t)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyt : (t : ℝ) < y := hy
  have hy0 : (0 : ℝ) ≤ y := le_trans t.coe_nonneg hyt.le
  have hcoe : ((Real.toNNReal (y - t) : NNReal) : ℝ) = y - t :=
    Real.coe_toNNReal _ (sub_nonneg.mpr hyt.le)
  have htoNN : Real.toNNReal y = t + Real.toNNReal (y - t) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, hcoe, Real.coe_toNNReal y hy0]
    ring
  show ((Real.toNNReal (y - t) : NNReal) : ℝ)⁻¹ •
      (S (t + Real.toNNReal (y - t)) f - S t f) =
    slope (fun s : ℝ ↦ S (Real.toNNReal s) f) (t : ℝ) y
  rw [slope_def_module, hcoe, Real.toNNReal_coe, htoNN]
