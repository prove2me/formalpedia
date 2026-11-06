-- Prove2me | solution 2 for OAI.SevenEighths.FiniteFourier.exists_unit_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:55.882193+00:00
-- url     : https://prove2.me/submissions/3a3789fa-4ae4-4b66-9f78-571fe46287cc

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]

theorem solution (χ : MulChar R ℂ) (hχ : IsPrimitiveOnIdeals χ)
    {a : R} (ha : ¬ IsUnit a) :
    ∃ u : Rˣ, a * (u : R) = a ∧ χ (u : R) ≠ 1 := by
  let I : Ideal R :=
    { carrier := {r | a * r = 0}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [mul_add, hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
        rw [mul_left_comm, hx, mul_zero] }
  have hI : I ≠ ⊥ := by
    intro hbot
    have hnu := ha
    simp only [isUnit_iff_mem_nonZeroDivisors_of_finite, mem_nonZeroDivisors_iff_right,
      not_forall] at hnu
    obtain ⟨x, hx, hx0⟩ := hnu
    have hxI : x ∈ I := by
      show a * x = 0
      first | exact hx | (rw [mul_comm]; exact hx)
    rw [hbot] at hxI
    exact hx0 ((Ideal.mem_bot).mp hxI)
  obtain ⟨u, hu1, hu2⟩ := hχ I hI
  refine ⟨u, ?_, hu2⟩
  have h1 : a * ((u : R) - 1) = 0 := hu1
  rw [mul_sub, mul_one, sub_eq_zero] at h1
  exact h1
