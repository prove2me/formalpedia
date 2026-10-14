-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.no_fixed_data_of_interpolation_and_analytic_aggregate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T14:39:16.554061+00:00
-- url     : https://prove2.me/submissions/f42a614d-a654-4b6b-b2df-8805d5077e1f

import Mathlib.Tactic
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_tendsto_collisionRate_source017
import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_exists_full_row_minor_of_surjective
import Theorems.Thm_OAI_PiExponent_determinant_bounds_inconsistent
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualMean_bounds
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_arithmetic_lower_bound_source017

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter
open scoped Topology

namespace OAI
namespace PiExponent
namespace AdmissibleParameters

variable {nu Lambda c : ℝ} (d : AdmissibleParameters nu Lambda c)

theorem total_error_lt_gap :
    nu / d.F0 +
      ((Lambda * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
        100 * (d.K : ℝ) / (d.w0 : ℝ)) +
      (Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
        weightErrorCoefficient nu d.base.theta d.K / d.wstar) <
      nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
        (1 - d.base.theta) := by
  have h1 := d.initial_margin
  have h2 := d.dimension_margin
  have h3 := d.weight_margin
  have h4 := d.epsilon_lt_gap
  linarith

theorem collision_exceeds_one_add_error :
    1 + (nu / d.F0 +
      ((Lambda * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
        100 * (d.K : ℝ) / (d.w0 : ℝ)) +
      (Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
        weightErrorCoefficient nu d.base.theta d.K / d.wstar)) <
      c * (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
        (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m)) := by
  have h1 := d.initial_margin
  have h2 := d.dimension_margin
  have h3 := d.weight_margin
  have h4 := d.epsilon_le_half
  have h5 := d.collision_margin
  linarith

theorem error_sum_eq : d.arithmeticError + d.analyticError =
    nu / d.F0 +
      ((Lambda * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
        100 * (d.K : ℝ) / (d.w0 : ℝ)) +
      (Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
        weightErrorCoefficient nu d.base.theta d.K / d.wstar) := by
  unfold arithmeticError analyticError translationError holomorphicError weightErrorCoefficient
  ring

theorem error_sum_lt_gap : d.arithmeticError + d.analyticError <
    nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
      (1 - d.base.theta) := by
  rw [d.error_sum_eq]
  exact d.total_error_lt_gap

theorem collision_exceeds_error_sum : 1 + d.arithmeticError + d.analyticError <
    c * (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m)) := by
  rw [add_assoc, d.error_sum_eq]
  exact d.collision_exceeds_one_add_error
end AdmissibleParameters
end PiExponent
end OAI

theorem solution
    (hgeometry : GlobalInterpolationStatement) (hanalytic : AnalyticAggregateStatement)
    (nu : ℝ) (hnu : 2 < nu) (d : FixedData nu) : False := by
  classical
  obtain ⟨error, herror, hupper⟩ := hanalytic nu hnu d
  have hsum : Tendsto (fun H : ℝ => d.arithmeticError + d.analyticError + error H)
      atTop (𝓝 (d.arithmeticError + d.analyticError + 0)) :=
    tendsto_const_nhds.add herror
  have hsmall : ∀ᶠ H : ℝ in atTop,
      d.arithmeticError + d.analyticError + error H <
        nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
          (1 - d.base.theta) :=
    hsum.eventually (Iio_mem_nhds (by simpa using d.error_sum_lt_gap))
  have hdiff : Tendsto (fun H : ℝ =>
      collisionRate d H - (1 + d.arithmeticError + d.analyticError + error H))
      atTop (𝓝 (collisionLimit d - (1 + d.arithmeticError + d.analyticError + 0))) :=
    (tendsto_collisionRate_source017 d).sub (tendsto_const_nhds.add herror)
  have hlarge : ∀ᶠ H : ℝ in atTop,
      0 < collisionRate d H - (1 + d.arithmeticError + d.analyticError + error H) := by
    apply hdiff.eventually (Ioi_mem_nhds ?_)
    have hh := d.collision_exceeds_error_sum
    change 1 + d.arithmeticError + d.analyticError < collisionLimit d at hh
    linarith
  have hcontradiction : ∀ᶠ H : ℝ in atTop,
      Function.Surjective (actualMatrix d H).mulVecLin → False := by
    filter_upwards [hsmall, hlarge, hupper,
      eventually_gt_atTop (0 : ℝ)] with H hsmall hlarge hupper hH
    intro hsurj
    obtain ⟨selection, _hselection, hdet⟩ :=
      InterpolationMatrix.exists_full_row_minor_of_surjective (actualMatrix d H) hsurj
    have hdet' : (actualMinor d H selection).det ≠ 0 := hdet
    have hlower := actual_minor_arithmetic_lower_bound_source017 d H hH selection hdet'
    have hb := actualMean_bounds d H hH
    exact determinant_bounds_inconsistent nu d.base.theta
      ((d.base.A : ℝ) * (1 - d.base.eta)) (actualMean d H)
      d.arithmeticError d.analyticError (error H) (collisionRate d H)
      (Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H))
      (by linarith) hb.1 hb.2 hsmall (by linarith) hlower (hupper selection hdet')
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hcontradiction
  obtain ⟨H, hLH, hsurj⟩ := hgeometry nu hnu d L
  exact hL H hLH hsurj