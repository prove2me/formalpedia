-- Prove2me | solution 1 for OAI.FiniteRingSieve.unit_char_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:18.30797+00:00
-- url     : https://prove2.me/submissions/83529d43-3b0b-492c-8d3f-fb0c1f8cbec6

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FiniteRingSieve_sum_chars

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.FiniteRingSieve
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
attribute [local instance] OAI.FiniteRingSieve.logProfilesFintypeMulChar
attribute [local instance] logProfilesFintypeMulChar
namespace OAI.FiniteRingSieve
theorem _root_.solution (u v : Rˣ) :
    (∑ χ : MulChar R ℂ, star (χ (u : R)) * χ (v : R)) =
      if u = v then (Fintype.card Rˣ : ℂ) else 0 := by
  calc
    _ = ∑ χ : MulChar R ℂ, χ ((u⁻¹ * v : Rˣ) : R) := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit,
        Units.val_mul, map_mul]
    _ = if ((u⁻¹ * v : Rˣ) : R) = 1 then (Fintype.card Rˣ : ℂ) else 0 :=
      sum_chars _
    _ = _ := by simp only [Units.val_eq_one, inv_mul_eq_one]
end OAI.FiniteRingSieve
