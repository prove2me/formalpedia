-- Prove2me | solution 2 for OAI.SevenEighths.FiniteFourier.primitive_gaussSum_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:53.091863+00:00
-- url     : https://prove2.me/submissions/cbe6755d-55a5-4e8a-8ddd-55b958954313

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

theorem OA2Aux.exists_unit_stabilizer (χ : MulChar R ℂ) (hχ : IsPrimitiveOnIdeals χ)
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

theorem solution (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ≠ 0 := by
  classical
  intro hg
  have hT : ∀ a : R, ∑ x : R, χ x * ψ (a * x) = 0 := by
    intro a
    have e : ∑ x : R, χ x * ψ (a * x) = gaussSum χ (ψ.mulShift a) := by
      simp [gaussSum, AddChar.mulShift_apply]
    rw [e]
    by_cases ha : IsUnit a
    · obtain ⟨b, rfl⟩ := ha
      rw [gaussSum_mulShift_eq, hg, mul_zero]
    · obtain ⟨u, hu1, hu2⟩ := OA2Aux.exists_unit_stabilizer χ hχ ha
      have h2 : ∑ x : R, χ ((u : R) * x) * (ψ.mulShift a) ((u : R) * x) =
          gaussSum χ (ψ.mulShift a) :=
        Fintype.sum_bijective (fun x => (u : R) * x) u.mulLeft_bijective _ _ (fun x => rfl)
      have h1 : gaussSum χ (ψ.mulShift a) = χ (u : R) * gaussSum χ (ψ.mulShift a) := by
        calc gaussSum χ (ψ.mulShift a)
            = ∑ x : R, χ ((u : R) * x) * (ψ.mulShift a) ((u : R) * x) := h2.symm
          _ = χ (u : R) * ∑ x : R, χ x * (ψ.mulShift a) x := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x _ => ?_
              simp only [AddChar.mulShift_apply, map_mul]
              rw [show a * ((u : R) * x) = a * x by rw [← mul_assoc, hu1]]
              ring
          _ = χ (u : R) * gaussSum χ (ψ.mulShift a) := rfl
      have h3 : (1 - χ (u : R)) * gaussSum χ (ψ.mulShift a) = 0 := by
        rw [sub_mul, one_mul, ← h1, sub_self]
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hu2
      · exact h
  have hS : ∀ x : R, ∑ a : R, ψ (a * (x - 1)) = if x = 1 then (Fintype.card R : ℂ) else 0 := by
    intro x
    rw [AddChar.sum_mulShift (x - 1) hψ]
    by_cases hx : x = 1 <;> simp [hx, sub_eq_zero]
  have key : ∑ a : R, (∑ x : R, χ x * ψ (a * x)) * ψ (-a) = Fintype.card R := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    have hx : ∀ x : R, ∑ a : R, χ x * ψ (a * x) * ψ (-a) =
        χ x * (if x = 1 then (Fintype.card R : ℂ) else 0) := by
      intro x
      rw [← hS x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    simp_rw [hx]
    rw [Finset.sum_eq_single (1 : R)]
    · simp
    · intro x _ hx1
      simp [hx1]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h0 : (Fintype.card R : ℂ) = 0 := by
    rw [← key]
    simp [hT]
  exact Fintype.card_ne_zero (by exact_mod_cast h0)
