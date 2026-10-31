-- Prove2me | solution 1 for MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.eq_zero_of_generator_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:15:38.434956+00:00
-- url     : https://prove2.me/submissions/1e520837-0a43-48f7-9389-552a28f7b105

import Definitions.Def_MarkovProcess_V3H_Semigroup_GeneratorInjectivity_5e725388
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Eigenvectors of a generator, and injectivity of `μ - L`

Let `S` be a strongly continuous contraction semigroup with generator `L`.  If `f` lies in the
generator domain with `L f = μ f`, then the orbit of `f` is the scalar exponential
`S t f = exp (μ t) f`: the defect `w t = S t f - exp (μ t) f` vanishes at `t = 0` and has right
derivative `μ w t`, so Grönwall's inequality forces it to vanish
(`operator_eq_exp_smul_of_generator_eq_smul`).

Since `S` is contractive, an eigenvalue `μ > 0` therefore forces `f = 0`
(`eq_zero_of_generator_eq_smul`); equivalently, `μ - L` is injective on the generator domain
(`eq_of_smul_sub_generator_eq`).  This is the uniqueness half of the assertion that the resolvent
`(μ - L)⁻¹` is a well-defined operator.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)















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
# Eigenvectors of a generator, and injectivity of `μ - L`

Let `S` be a strongly continuous contraction semigroup with generator `L`.  If `f` lies in the
generator domain with `L f = μ f`, then the orbit of `f` is the scalar exponential
`S t f = exp (μ t) f`: the defect `w t = S t f - exp (μ t) f` vanishes at `t = 0` and has right
derivative `μ w t`, so Grönwall's inequality forces it to vanish
(`operator_eq_exp_smul_of_generator_eq_smul`).

Since `S` is contractive, an eigenvalue `μ > 0` therefore forces `f = 0`
(`eq_zero_of_generator_eq_smul`); equivalently, `μ - L` is injective on the generator domain
(`eq_of_smul_sub_generator_eq`).  This is the uniqueness half of the assertion that the resolvent
`(μ - L)⁻¹` is a well-defined operator.
-/

open Filter Set Topology
open scoped NNReal



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)











namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
theorem solution {μ : ℝ} (hμ : 0 < μ) (f : S.generatorDomain)
    (hgen : S.generator f = μ • (f : E)) : (f : E) = 0 := by
  have hcontract : Real.exp μ * ‖(f : E)‖ ≤ ‖(f : E)‖ := by
    have hle := S.norm_apply_le 1 (f : E)
    rw [S.operator_eq_exp_smul_of_generator_eq_smul f hgen 1, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), NNReal.coe_one, mul_one] at hle
    exact hle
  have hone : 1 < Real.exp μ := by
    have hexp := Real.add_one_le_exp μ
    linarith only [hexp, hμ]
  rw [← norm_le_zero_iff]
  by_contra hpos
  push Not at hpos
  have hstrict : 1 * ‖(f : E)‖ < Real.exp μ * ‖(f : E)‖ := by
    exact mul_lt_mul_of_pos_right hone hpos
  rw [one_mul] at hstrict
  linarith only [hstrict, hcontract]
