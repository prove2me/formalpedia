-- Prove2me | solution 1 for NRLFormulary.rothe_hagen_identity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:43:53.636058+00:00
-- url     : https://prove2.me/submissions/41c01401-1f03-43c9-a9d7-d745efa5c7af

import Mathlib
import Definitions.Def_NRLFormulary_cbinom

open NRLFormulary

namespace Ag3Aux_RotheHagen

/-- Local copy of the singularity-free Rothe factor (same formula as `NRLFormulary.rotheA`). -/
noncomputable def rotheA (x z : ℂ) : ℕ → ℂ
  | 0 => 1
  | (k + 1) =>
      x * (∏ j ∈ Finset.range k, (x + ((k : ℂ) + 1) * z - ((j : ℂ) + 1))) /
        (Nat.factorial (k + 1) : ℂ)


open Polynomial

theorem rec (x z : ℂ) (k : ℕ) :
    rotheA (x + 1) z (k + 1) = rotheA x z (k + 1) + rotheA (x + z) z k := by
  cases k with
  | zero => simp [rotheA]
  | succ m =>
    simp only [rotheA]
    obtain ⟨w, hw⟩ : ∃ w : ℂ, w = x + (((m + 1 : ℕ) : ℂ) + 1) * z := ⟨_, rfl⟩
    have e1 : ∏ j ∈ Finset.range (m + 1), (x + 1 + (((m + 1 : ℕ) : ℂ) + 1) * z - ((j : ℂ) + 1))
        = (∏ j ∈ Finset.range m, (w - ((j : ℂ) + 1))) * w := by
      rw [Finset.prod_range_succ']
      congr 1
      · exact Finset.prod_congr rfl (fun j _ => by rw [hw]; push_cast; ring)
      · rw [hw]; push_cast; ring
    have e2 : ∏ j ∈ Finset.range (m + 1), (x + (((m + 1 : ℕ) : ℂ) + 1) * z - ((j : ℂ) + 1))
        = (∏ j ∈ Finset.range m, (w - ((j : ℂ) + 1))) * (w - ((m : ℂ) + 1)) := by
      rw [Finset.prod_range_succ]
      congr 1
      · exact Finset.prod_congr rfl (fun j _ => by rw [hw])
      · rw [hw]
    have e3 : ∏ j ∈ Finset.range m, (x + z + ((m : ℂ) + 1) * z - ((j : ℂ) + 1))
        = ∏ j ∈ Finset.range m, (w - ((j : ℂ) + 1)) :=
      Finset.prod_congr rfl (fun j _ => by rw [hw]; push_cast; ring)
    rw [e1, e2, e3]
    rw [Nat.factorial_succ (m + 1)]
    have hf : ((m + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hm : ((m + 1 + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (m + 1))
    push_cast at hm ⊢
    field_simp
    rw [hw]
    push_cast
    ring

theorem at_zero (z : ℂ) (k : ℕ) : rotheA 0 z k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp [rotheA]
  | succ k => simp [rotheA]

noncomputable def RP (z : ℂ) : ℕ → ℂ[X]
  | 0 => 1
  | (k + 1) => C (1 / ((k + 1).factorial : ℂ)) * X *
      ∏ j ∈ Finset.range k, (X + C (((k : ℂ) + 1) * z - ((j : ℂ) + 1)))

theorem RP_eval (x z : ℂ) (k : ℕ) : (RP z k).eval x = rotheA x z k := by
  cases k with
  | zero => simp [RP, rotheA]
  | succ k =>
    simp only [RP, rotheA, eval_mul, eval_C, eval_X, eval_prod, eval_add]
    have : ∀ j ∈ Finset.range k, x + (((k : ℂ) + 1) * z - ((j : ℂ) + 1))
        = x + ((k : ℂ) + 1) * z - ((j : ℂ) + 1) := fun j _ => by ring
    rw [Finset.prod_congr rfl this]
    ring

theorem A0 (x z : ℂ) : rotheA x z 0 = 1 := rfl

theorem conv (x y z : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), rotheA x z k * rotheA y z (n - k) = rotheA (x + y) z n := by
  induction n generalizing x y with
  | zero => simp [rotheA]
  | succ n ih =>
    have hS : ∀ x, ∑ k ∈ Finset.range (n + 1 + 1), rotheA x z k * rotheA y z (n + 1 - k)
        = ∑ k ∈ Finset.range (n + 1), rotheA x z (k + 1) * rotheA y z (n - k) + rotheA y z (n + 1) := by
      intro x
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero, A0, one_mul]
    set D : ℂ → ℂ := fun x => ∑ k ∈ Finset.range (n + 1 + 1), rotheA x z k * rotheA y z (n + 1 - k)
        - rotheA (x + y) z (n + 1) with hD
    have hper : ∀ x, D (x + 1) = D x := by
      intro x
      simp only [hD, hS]
      rw [show x + 1 + y = (x + y) + 1 by ring, rec (x + y)]
      simp_rw [rec x]
      rw [Finset.sum_congr rfl (fun k _ => add_mul _ _ _), Finset.sum_add_distrib, ih (x + z) y,
        show x + z + y = x + y + z by ring]
      ring
    have hnat : ∀ m : ℕ, D m = 0 := by
      intro m
      induction m with
      | zero =>
        simp only [hD, hS, Nat.cast_zero, zero_add, at_zero]
        simp
      | succ m ihm => rw [Nat.cast_succ, hper, ihm]
    set Q : ℂ[X] := ∑ k ∈ Finset.range (n + 1 + 1), RP z k * C (rotheA y z (n + 1 - k))
        - (RP z (n + 1)).comp (X + C y) with hQ
    have hQe : ∀ x, Q.eval x = D x := by
      intro x
      simp only [hQ, hD, eval_sub, eval_finset_sum, eval_mul, eval_C, eval_comp, eval_add, eval_X,
        RP_eval]
    have hQ0 : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.Infinite.mono (s := Set.range (Nat.cast : ℕ → ℂ))
      · rintro _ ⟨m, rfl⟩
        simp only [Set.mem_setOf_eq, IsRoot, hQe, hnat]
      · exact Set.infinite_range_of_injective Nat.cast_injective
    have := hQe x
    rw [hQ0, eval_zero] at this
    simp only [hD] at this
    exact (sub_eq_zero.mp this.symm)


theorem rothe_div (x z : ℂ) (k : ℕ) (h : x + (k : ℂ) * z ≠ 0) :
    rotheA x z k = x / (x + (k : ℂ) * z) * cbinom (x + (k : ℂ) * z) k := by
  cases k with
  | zero =>
    simp at h
    simp [rotheA, cbinom, h]
  | succ k =>
    rw [rotheA, cbinom, Finset.prod_range_succ']
    have h1 : ∏ j ∈ Finset.range k, (x + ((k + 1 : ℕ) : ℂ) * z - ((j + 1 : ℕ) : ℂ))
        = ∏ j ∈ Finset.range k, (x + ((k : ℂ) + 1) * z - ((j : ℂ) + 1)) := by
      refine Finset.prod_congr rfl (fun j _ => ?_); push_cast; ring
    rw [h1]
    simp only [Nat.cast_zero, sub_zero]
    have h' : x + z * ((k + 1 : ℕ) : ℂ) ≠ 0 := by rwa [mul_comm] at h
    field_simp

end Ag3Aux_RotheHagen

open Ag3Aux_RotheHagen

theorem solution (x y z : ℂ) (n : ℕ)
    (hx : ∀ k ≤ n, x + (k : ℂ) * z ≠ 0)
    (hy : ∀ k ≤ n, y + (k : ℂ) * z ≠ 0)
    (hxy : x + y + (n : ℂ) * z ≠ 0) :
    ∑ k ∈ Finset.range (n + 1),
        (x / (x + (k : ℂ) * z) * cbinom (x + (k : ℂ) * z) k) *
          (y / (y + ((n - k : ℕ) : ℂ) * z) * cbinom (y + ((n - k : ℕ) : ℂ) * z) (n - k))
      = (x + y) / (x + y + (n : ℂ) * z) * cbinom (x + y + (n : ℂ) * z) n := by
  rw [← rothe_div (x + y) z n hxy, ← conv x y z n]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [rothe_div x z k (hx k hk'), rothe_div y z (n - k) (hy (n - k) (Nat.sub_le n k))]
