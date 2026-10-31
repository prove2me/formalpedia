-- Prove2me | solution 1 for MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.exp_smul_operator_sub_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:35:56.098101+00:00
-- url     : https://prove2.me/submissions/6bc46895-6c02-470a-a793-c89642ee31ea

import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_hasDerivWithinAt_Ioi

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




















variable [CompleteSpace E]



namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
theorem solution (f : S.generatorDomain) (lam : ℝ) (t : NNReal) :
    Real.exp (-lam * (t : ℝ)) • S t (f : E) - f =
      ∫ s in (0 : ℝ)..t, Real.exp (-lam * s) •
        S (Real.toNNReal s) (S.generator f - lam • (f : E)) := by
  let F : ℝ → E := fun s ↦ Real.exp (-lam * s) • S (Real.toNNReal s) (f : E)
  let F' : ℝ → E := fun s ↦
    Real.exp (-lam * s) • S (Real.toNNReal s) (S.generator f - lam • (f : E))
  have hcont : ContinuousOn F (Set.Icc 0 (t : ℝ)) := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      (S.continuous_operator_toNNReal f)).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) t,
      HasDerivWithinAt F (F' x) (Set.Ioi x) x := by
    intro x hx
    have hexp : HasDerivAt (fun s : ℝ ↦ Real.exp (-lam * s))
        ((-lam) * Real.exp (-lam * x)) x := by
      have h : HasDerivAt (fun s : ℝ ↦ Real.exp (-lam * s))
          (Real.exp (-lam * x) * (-lam * 1)) x := by
        simpa only [id_eq] using ((hasDerivAt_id x).const_mul (-lam)).exp
      exact h.congr_deriv (by ring)
    have horbit := S.hasDerivWithinAt_Ioi f (Real.toNNReal x)
    rw [Real.coe_toNNReal x hx.1.le] at horbit
    have hprod := hexp.hasDerivWithinAt.smul horbit
    refine hprod.congr_deriv ?_
    dsimp only [F']
    rw [map_sub, map_smul]
    module
  have hint : IntervalIntegrable F' MeasureTheory.volume 0 t := by
    have hc : Continuous F' :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
        (S.continuous_operator_toNNReal _)
    exact hc.intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.coe_nonneg hcont
    hderiv hint
  simpa only [F, F', Real.toNNReal_coe, Real.toNNReal_zero, S.zero_apply, mul_zero,
    Real.exp_zero, one_smul] using hftc.symm
