-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_capped_uniform_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:11:12.319294+00:00
-- url     : https://prove2.me/submissions/d1cbbcff-3356-4bb2-8d07-5908d7f6ca9c

import Mathlib
open Filter Topology
open scoped NNReal
set_option autoImplicit false

/-- The capped equal subdivision supplies monotone bounded grids and
a real mesh tending to zero, including zero-length intervals. -/
theorem solution
    (a b : NNReal) (hab : a ≤ b) :
    let u : Nat → Nat → NNReal := fun n i =>
      a + (b - a) * ((min i (n+1) : Nat) : NNReal) / ((n+1 : Nat) : NNReal)
    (∀ n, Monotone (u n)) ∧
    (∀ n, u n 0 = a) ∧
    (∀ n, u n (n+1) = b) ∧
    (∀ n i, u n i ≤ b) ∧
    (∀ n i, i < n+1 →
      (u n (i+1) : Real) - (u n i : Real) =
        ((b : Real) - (a : Real)) / ((n+1 : Nat) : Real)) ∧
    Tendsto (fun n : Nat => ((b : Real)-(a : Real)) /
      ((n+1 : Nat) : Real)) atTop (nhds 0) := by
  dsimp only
  let u : Nat → Nat → NNReal := fun n i =>
    a + (b-a) * ((min i (n+1) : Nat) : NNReal) / ((n+1 : Nat) : NNReal)
  change (∀ n, Monotone (u n)) ∧ (∀ n, u n 0 = a) ∧
    (∀ n, u n (n+1) = b) ∧ (∀ n i, u n i ≤ b) ∧
    (∀ n i, i < n+1 → (u n (i+1) : Real) - (u n i : Real) =
      ((b : Real)-(a : Real)) / ((n+1 : Nat) : Real)) ∧ _
  have hmono (n : Nat) : Monotone (u n) := by
    intro i j hij
    dsimp [u]
    gcongr
  have h0 (n : Nat) : u n 0 = a := by simp [u]
  have hN (n : Nat) : u n (n+1) = b := by
    have hn : ((n+1 : Nat) : NNReal) ≠ 0 := by positivity
    dsimp [u]
    rw [min_self, mul_div_cancel_right₀ _ hn, add_tsub_cancel_of_le hab]
  refine ⟨hmono,h0,hN,?_,?_,?_⟩
  · intro n i
    have he : u n i = u n (min i (n+1)) := by
      simp only [u, min_assoc, min_self]
    rw [he, ← hN n]
    exact hmono n (min_le_right _ _)
  · intro n i hi
    have hs : i+1 ≤ n+1 := Nat.succ_le_of_lt hi
    have hd : ((n+1 : Nat) : Real) ≠ 0 := by positivity
    simp only [u, NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul,
      NNReal.coe_sub hab, NNReal.coe_natCast, min_eq_left (le_of_lt hi),
      min_eq_left hs, Nat.cast_add, Nat.cast_one]
    norm_num <;> ring
  · have h := tendsto_const_div_atTop_nhds_zero_nat ((b : Real)-(a : Real))
    simpa only [Function.comp_def] using
      h.comp (tendsto_add_atTop_nat 1)
