-- Prove2me | solution 1 for MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.operator_resolvent_sub_resolvent_operator_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:52:24.124138+00:00
-- url     : https://prove2.me/submissions/176c374d-c211-4103-b543-6f779d04d585

import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Definitions.Def_MarkovProcess_V3H_Semigroup_OrbitContinuity_8cf8e1f5
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_hasDerivWithinAt_operator_apply

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Comparing two semigroups through their resolvents

Two strongly continuous contraction semigroups `S` and `S'` on the same Banach space have, in
general, unrelated generator domains, so the naive Duhamel comparison of their orbits is not
available.  Inserting one resolvent of each semigroup repairs this: the curve

  `y ↦ S y (R_μ (S' (t − y) (R'_μ z)))`,

where `R_μ` and `R'_μ` are the resolvents of `S` and of `S'` at a positive shift `μ`, takes values
in the generator domain of `S` at every time, is differentiable because `R'_μ z` lies in the
generator domain of `S'`, and its derivative telescopes to the difference of the two resolvents:

  `S t (R_μ (R'_μ z)) − R_μ (S' t (R'_μ z)) = ∫₀ᵗ S y ((R_μ − R'_μ) (S' (t − y) z)) dy.`

Consequently the left-hand side is bounded by `t` times the largest value of `‖(R_μ − R'_μ) v‖`
over the orbit `{S' u z : 0 ≤ u ≤ t}`, which is a compact set.  This is the mechanism behind the
Trotter--Kato theorem in `Semigroup/TrotterKato.lean`.

Main results: `operator_resolvent_sub_resolvent_operator_eq_integral`,
`norm_operator_resolvent_sub_resolvent_operator_le`.

Both semigroups are read at the same shift `μ`; nothing is asserted when the two resolvents are
taken at different shifts, and no relation between the two generators is assumed.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The derivative of the comparison curve `u ↦ S u (R_μ (S' (t − u) (R'_μ z)))` at an interior
time is `S y ((R_μ − R'_μ) (S' (t − y) z))`: the generator of `S` acting on the resolvent value
and the derivative of the inner orbit cancel except for the difference of the resolvents. -/
private theorem hasDerivWithinAt_comparison
    (S S' : StronglyContinuousContractionSemigroup E) (μ : PositiveShift) (t : ℝ) (z : E)
    {y : ℝ} (hy0 : 0 ≤ y) (hyt : y < t) :
    HasDerivWithinAt
      (fun u : ℝ ↦ S (Real.toNNReal u)
        (S.resolvent μ (S' (Real.toNNReal (t - u)) (S'.resolvent μ z))))
      (S (Real.toNNReal y)
        (S.resolvent μ (S' (Real.toNNReal (t - y)) z) -
          S'.resolvent μ (S' (Real.toNNReal (t - y)) z)))
      (Set.Ioi y) y := by
  have hwmem : S'.resolvent μ z ∈ S'.generatorDomain := S'.resolvent_mem_generatorDomain μ z
  have hmem : S.resolvent μ (S' (Real.toNNReal (t - y)) (S'.resolvent μ z)) ∈
      S.generatorDomain := S.resolvent_mem_generatorDomain μ _
  have hty : (0 : ℝ) < t - y := sub_pos.mpr hyt
  have h1 : HasDerivAt (fun u : ℝ ↦ S' (Real.toNNReal u) (S'.resolvent μ z))
      (S' (Real.toNNReal (t - y)) (S'.generator ⟨S'.resolvent μ z, hwmem⟩)) (t - y) :=
    S'.hasDerivAt_operator_toNNReal ⟨S'.resolvent μ z, hwmem⟩ hty
  have h2 : HasDerivAt (fun u : ℝ ↦ t - u) (-1) y := by
    simpa using! (hasDerivAt_const y t).sub (hasDerivAt_id y)
  have h3 := h1.scomp (𝕜 := ℝ) y h2
  have hd : HasDerivWithinAt
      (fun u : ℝ ↦ S.resolvent μ (S' (Real.toNNReal (t - u)) (S'.resolvent μ z)))
      (S.resolvent μ ((-1 : ℝ) •
        S' (Real.toNNReal (t - y)) (S'.generator ⟨S'.resolvent μ z, hwmem⟩)))
      (Set.Ioi y) y :=
    ((S.resolvent μ).hasFDerivAt.comp_hasDerivAt y h3).hasDerivWithinAt
  refine (S.hasDerivWithinAt_operator_apply hy0 hmem hd).congr_deriv ?_
  have hgen1 : S.generator ⟨S.resolvent μ (S' (Real.toNNReal (t - y)) (S'.resolvent μ z)),
      hmem⟩ =
      (μ : ℝ) • S.resolvent μ (S' (Real.toNNReal (t - y)) (S'.resolvent μ z)) -
        S' (Real.toNNReal (t - y)) (S'.resolvent μ z) :=
    S.generator_eq_of_resolvent_eq μ hmem rfl
  have hgen2 : S'.generator ⟨S'.resolvent μ z, hwmem⟩ = (μ : ℝ) • S'.resolvent μ z - z :=
    S'.generator_eq_of_resolvent_eq μ hwmem rfl
  have hcomm : S' (Real.toNNReal (t - y)) (S'.resolvent μ z) =
      S'.resolvent μ (S' (Real.toNNReal (t - y)) z) :=
    S'.operator_resolvent μ _ z
  congr 1
  rw [hgen1, hgen2]
  simp only [map_sub, map_smul, hcomm]
  module





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
# Comparing two semigroups through their resolvents

Two strongly continuous contraction semigroups `S` and `S'` on the same Banach space have, in
general, unrelated generator domains, so the naive Duhamel comparison of their orbits is not
available.  Inserting one resolvent of each semigroup repairs this: the curve

  `y ↦ S y (R_μ (S' (t − y) (R'_μ z)))`,

where `R_μ` and `R'_μ` are the resolvents of `S` and of `S'` at a positive shift `μ`, takes values
in the generator domain of `S` at every time, is differentiable because `R'_μ z` lies in the
generator domain of `S'`, and its derivative telescopes to the difference of the two resolvents:

  `S t (R_μ (R'_μ z)) − R_μ (S' t (R'_μ z)) = ∫₀ᵗ S y ((R_μ − R'_μ) (S' (t − y) z)) dy.`

Consequently the left-hand side is bounded by `t` times the largest value of `‖(R_μ − R'_μ) v‖`
over the orbit `{S' u z : 0 ≤ u ≤ t}`, which is a compact set.  This is the mechanism behind the
Trotter--Kato theorem in `Semigroup/TrotterKato.lean`.

Main results: `operator_resolvent_sub_resolvent_operator_eq_integral`,
`norm_operator_resolvent_sub_resolvent_operator_le`.

Both semigroups are read at the same shift `μ`; nothing is asserted when the two resolvents are
taken at different shifts, and no relation between the two generators is assumed.
-/

open Filter MeasureTheory Topology
open scoped NNReal



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]



namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
theorem solution
    (S S' : StronglyContinuousContractionSemigroup E) (μ : PositiveShift) (t : NNReal) (z : E) :
    S t (S.resolvent μ (S'.resolvent μ z)) - S.resolvent μ (S' t (S'.resolvent μ z)) =
      ∫ y in (0 : ℝ)..(t : ℝ), S (Real.toNNReal y)
        (S.resolvent μ (S' (Real.toNNReal ((t : ℝ) - y)) z) -
          S'.resolvent μ (S' (Real.toNNReal ((t : ℝ) - y)) z)) := by
  have hcurve : Continuous fun u : ℝ ↦ S (Real.toNNReal u)
      (S.resolvent μ (S' (Real.toNNReal ((t : ℝ) - u)) (S'.resolvent μ z))) := by
    refine S.continuous_operator_apply continuous_real_toNNReal ?_
    exact (S.resolvent μ).continuous.comp
      ((S'.continuous_operator_toNNReal (S'.resolvent μ z)).comp
        (continuous_const.sub continuous_id))
  have hderiv : Continuous fun u : ℝ ↦ S (Real.toNNReal u)
      (S.resolvent μ (S' (Real.toNNReal ((t : ℝ) - u)) z) -
        S'.resolvent μ (S' (Real.toNNReal ((t : ℝ) - u)) z)) := by
    refine S.continuous_operator_apply continuous_real_toNNReal ?_
    have h : Continuous fun u : ℝ ↦ S' (Real.toNNReal ((t : ℝ) - u)) z :=
      (S'.continuous_operator_toNNReal z).comp (continuous_const.sub continuous_id)
    exact ((S.resolvent μ).continuous.comp h).sub ((S'.resolvent μ).continuous.comp h)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.coe_nonneg
    hcurve.continuousOn
    (fun y hy ↦ hasDerivWithinAt_comparison S S' μ (t : ℝ) z hy.1.le hy.2)
    (hderiv.intervalIntegrable 0 (t : ℝ))
  rw [hFTC]
  simp only [sub_self, sub_zero, Real.toNNReal_zero, Real.toNNReal_coe, _root_.MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.zero_apply]
