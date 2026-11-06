-- Prove2me | solution 3 for OAI.SevenEighths.CubicSieve.cubic_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:19.938637+00:00
-- url     : https://prove2.me/submissions/fba97a4f-5846-4f35-b9fa-40f15e5eb551

import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Algebra
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite Rˣ]
omit [Finite Rˣ]
theorem OA1Aux.cube_apply {R : Type*} [CommRing R] (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 3 = if IsUnit x then 1 else 0 := by
  have h := MulChar.pow_apply' χ (n := 3) (by norm_num) x
  rw [← h, hχ]
  split_ifs with hx
  · obtain ⟨u, rfl⟩ := hx
    exact MulChar.one_apply_coe u
  · exact MulChar.map_nonunit _ hx

theorem solution (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    ‖χ x‖ ≤ 1 := by
  have h := OA1Aux.cube_apply χ hχ x
  have h2 : ‖χ x‖ ^ 3 ≤ 1 := by
    rw [← norm_pow, h]
    split_ifs <;> simp
  by_contra hc
  push_neg at hc
  have : 1 < ‖χ x‖ ^ 3 := one_lt_pow₀ hc (by norm_num)
  linarith
