-- Prove2me | solution 1 for NewtonCartan.geometrization_unique
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:58:41.159562+00:00
-- url     : https://prove2.me/submissions/f7832beb-7b0f-4971-82c7-af66847267ec

import Definitions.Def_NewtonCartan_defs
import Theorems.Thm_NewtonCartan_conn_eq_of_unitTimelike_quad
import Theorems.Thm_NewtonCartan_sameTrajectories_diff_quad
import Mathlib.Tactic.Ring

open scoped ContDiff BigOperators
open Classical
open NewtonCartan

/-! Uniqueness (G2): reduce to spray agreement on the unit-timelike cone + polarization. -/

theorem solution (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ) :
    ∀ Γ' : Conn, IsDerivOp Γ' → SameTrajectories Γ φ Γ' → Γ' = geomΓ Γ φ := by
  intro Γ' hD hS
  funext x a b c
  let C : Fin 4 → Fin 4 → Fin 4 → ℝ := fun a b c => Γ' x a b c - geomΓ Γ φ x a b c
  have hsym : ∀ a b c, C a b c = C a c b := by
    intro a b c
    simp only [C, geomΓ, hD.2 x a b c, hNG.1.1.2 x a b c, mul_comm (tt b)]
  have hquad : ∀ a (ξ : Fin 4 → ℝ), ξ 0 = 1 →
      (∑ b : Fin 4, ∑ c : Fin 4, C a b c * ξ b * ξ c) = 0 := by
    intro a ξ hξ
    simpa [C, sub_mul, Finset.sum_sub_distrib] using
      sameTrajectories_diff_quad Γ φ hNG Γ' hD hS x a ξ hξ
  have h0 := conn_eq_of_unitTimelike_quad C hsym hquad a b c
  -- C a b c = 0 ⇒ Γ' = geomΓ at this component
  simpa [C, sub_eq_zero] using h0
