-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.linearMap_vanishes_on_ideal_power_of_products
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T08:05:43.975905+00:00
-- url     : https://prove2.me/submissions/97d3906c-1ced-4c6e-83df-28ff6684e843

import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Complex.Basic

open scoped Pointwise

theorem solution
    {A V : Type} [CommRing A] [AddCommMonoid V] [Module Complex V] [Algebra Complex A]
    (I : Ideal A) (n : Nat) (hn : 0 < n) (F : A →ₗ[Complex] V)
    (hProducts : ∀ f : Fin n → A, (∀ i, f i ∈ I) → F (∏ i, f i) = 0)
    (P : A) (hP : P ∈ I ^ n) : F P = 0 := by
  rw [Submodule.pow_eq_span_pow_set] at hP
  have hspan : ∀ x ∈ (I : Set A) ^ n, ∀ a : A, F (a * x) = 0 := by
    intro x hx a
    obtain ⟨f, hf, hfx⟩ := (Set.mem_pow_iff_prod).mp hx
    let i0 : Fin n := ⟨0, hn⟩
    let g : Fin n → A := Function.update f i0 (a * f i0)
    have hg : ∀ i, g i ∈ I := by
      intro i
      by_cases hi : i = i0
      · subst i
        exact I.mul_mem_left a (hf i0)
      · simpa [g, hi] using hf i
    have hprod : (∏ i, g i) = a * x := by
      calc
        (∏ i, g i) = (a * f i0) * ∏ i ∈ Finset.univ \ {i0}, f i := by
          simp [g, Finset.prod_update_of_mem]
        _ = a * (f i0 * ∏ i ∈ Finset.univ.erase i0, f i) := by
          rw [Finset.sdiff_singleton_eq_erase]
          ring
        _ = a * x := by rw [Finset.mul_prod_erase (s := Finset.univ) (f := f) (a := i0) (by simp), hfx]
    rw [← hprod]
    exact hProducts g hg
  have hzero : ∀ a : A, F (a * (0 : A)) = 0 := by simp
  have hadd : ∀ x y : A, x ∈ Submodule.span A ((I : Set A) ^ n) →
      y ∈ Submodule.span A ((I : Set A) ^ n) → (∀ a : A, F (a * x) = 0) →
      (∀ a : A, F (a * y) = 0) → ∀ a : A, F (a * (x + y)) = 0 := by
    intro x y _ _ hx hy a
    rw [mul_add, map_add, hx a, hy a, add_zero]
  have hsmul : ∀ b : A, ∀ x : A, x ∈ Submodule.span A ((I : Set A) ^ n) →
      (∀ a : A, F (a * x) = 0) →
      ∀ a : A, F (a * (b * x)) = 0 := by
    intro b x _ hx a
    rw [← mul_assoc]
    exact hx (a * b)
  have hresult : ∀ a : A, F (a * P) = 0 := by
    exact Submodule.span_induction hspan hzero hadd hsmul hP
  simpa using hresult 1
