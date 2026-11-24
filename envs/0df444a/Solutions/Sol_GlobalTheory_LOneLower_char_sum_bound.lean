-- Prove2me | solution 1 for GlobalTheory.LOneLower.char_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:35:08.148063+00:00
-- url     : https://prove2.me/submissions/1956e388-89d7-4e69-a049-a29e23b62760

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower
namespace GlobalTheory.LOneLower
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q)‖ ≤ q := by
  have h0 : ∑ n ∈ Finset.range q, χ (n : ZMod q) = 0 := by
    rw [← MulChar.sum_eq_zero_of_ne_one hχ]
    refine Finset.sum_nbij' (fun n => (n : ZMod q)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
    · simp
    · intro a _
      simpa using ZMod.val_lt a
    · intro n hn
      exact ZMod.val_cast_of_lt (by simpa using hn)
    · intro a _
      simp
    · simp
  have h1 : ∑ n ∈ Finset.range q, χ ((n + 1 : ℕ) : ZMod q) = 0 := by
    have e1 := Finset.sum_range_succ (fun n : ℕ => χ (n : ZMod q)) q
    have e2 := Finset.sum_range_succ' (fun n : ℕ => χ (n : ZMod q)) q
    rw [e1, h0] at e2
    simp only [ZMod.natCast_self, Nat.cast_zero, zero_add] at e2
    exact left_eq_add.1 (by rw [add_comm]; exact e2)
  have h2 : ∀ N, ∑ n ∈ Finset.range (q + N), χ ((n + 1 : ℕ) : ZMod q)
      = ∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) := by
    intro N
    rw [Finset.sum_range_add, h1, zero_add]
    simp
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases h : N ≤ q
    · refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun n _ => χ.norm_le_one _).trans ?_
      simpa using h
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_le.1 h).le
      rw [h2]
      exact ih k (by have := NeZero.pos q; omega)
end GlobalTheory.LOneLower
