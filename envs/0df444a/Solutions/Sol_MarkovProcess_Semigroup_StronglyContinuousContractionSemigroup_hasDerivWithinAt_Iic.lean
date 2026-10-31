-- Prove2me | solution 1 for MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.hasDerivWithinAt_Iic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:36:04.254568+00:00
-- url     : https://prove2.me/submissions/d493fa8d-76c3-427d-abac-e3e33db645cd

import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_MarkovProcess_Semigroup_tendsto_apply_of_opNorm_le_one

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
theorem solution (f : S.generatorDomain) {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (fun s : ℝ ↦ S (Real.toNNReal s) f)
      (S (Real.toNNReal t) (S.generator f)) (Set.Iic t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hdiff : Set.Iic t \ {t} = Set.Iio t := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Iic, Set.mem_singleton_iff, Set.mem_Iio]
    exact ⟨fun hy ↦ lt_of_le_of_ne hy.1 hy.2, fun hy ↦ ⟨hy.le, hy.ne⟩⟩
  rw [hdiff]
  have horbit : Tendsto (fun y : ℝ ↦ S (Real.toNNReal y) (S.generator f)) (𝓝[<] t)
      (𝓝 (S (Real.toNNReal t) (S.generator f))) :=
    ((S.continuous_operator_toNNReal (S.generator f)).tendsto t).mono_left nhdsWithin_le_nhds
  have hquot : Tendsto (fun y : ℝ ↦ S.differenceQuotient f (Real.toNNReal (t - y))) (𝓝[<] t)
      (𝓝 (S.generator f)) :=
    (S.tendsto_generator f).comp (tendsto_toNNReal_const_sub t)
  have hmain := tendsto_apply_of_opNorm_le_one (fun y : ℝ ↦ S (Real.toNNReal y))
    (S (Real.toNNReal t)) (fun y : ℝ ↦ S.differenceQuotient f (Real.toNNReal (t - y)))
    (S.generator f) (fun y ↦ S.norm_operator_le_one _) horbit hquot
  refine hmain.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ht] with y hy
  have hcoe : ((Real.toNNReal (t - y) : NNReal) : ℝ) = t - y :=
    Real.coe_toNNReal _ (sub_nonneg.mpr hy.2.le)
  have hsum : Real.toNNReal y + Real.toNNReal (t - y) = Real.toNNReal t := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, hcoe, Real.coe_toNNReal y hy.1.le,
      Real.coe_toNNReal t (hy.1.trans hy.2).le]
    ring
  have hinv : (y - t)⁻¹ = -(t - y)⁻¹ := by rw [neg_inv, neg_sub]
  show S (Real.toNNReal y) (S.differenceQuotient f (Real.toNNReal (t - y)))
    = slope (fun s : ℝ ↦ S (Real.toNNReal s) f) t y
  rw [S.differenceQuotient_apply, map_smul, map_sub, ← S.add_apply, hsum, hcoe,
    slope_def_module, hinv, neg_smul, ← smul_neg, neg_sub]
