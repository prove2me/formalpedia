-- Prove2me | solution 1 for GlobalTheory.BasicFlow.splitLarge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:27:32.371432+00:00
-- url     : https://prove2.me/submissions/29911603-d260-4331-813d-4e8c5dfac070

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DropLevelsBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.BasicFlow
namespace GlobalTheory.BasicFlow
theorem _root_.solution : SplitLarge := by
  intro l n l1 W ys hn hl1 hl hy hW
  obtain ⟨q, rfl⟩ : ∃ q, l = q + 1 + n := ⟨l - 1 - n, by omega⟩
  have hq : q + 1 + n - 1 - n = q := by omega
  rw [hq]
  have hq0 : 0 < q := by omega
  refine ⟨(⌊ys⌋₊ % q) :: List.replicate (⌊ys⌋₊ / q) q, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.1 hp with h | h
    · exact h ▸ (Nat.mod_lt _ hq0).le
    · exact (List.eq_of_mem_replicate h).le
  · simp only [List.sum_cons, List.sum_replicate, smul_eq_mul]
    exact Nat.mod_add_div' _ _
  · simp only [List.length_cons, List.length_replicate]
    push_cast at *
    set k : ℕ := ⌊ys⌋₊ / q with hk
    have h1 : (k : ℝ) * q ≤ ys := by
      refine le_trans ?_ (Nat.floor_le hy)
      exact_mod_cast Nat.div_mul_le_self _ _
    have h2 : (n : ℝ) + 1 ≤ q := by exact_mod_cast (by omega : n + 1 ≤ q)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h3 : (k : ℝ) ≤ 2 * W / l1 ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h4 : l1 ^ 2 ≤ ((q : ℝ) + 1 + n + 1) * (2 * q) := by nlinarith
      calc (k : ℝ) * l1 ^ 2 ≤ k * (((q : ℝ) + 1 + n + 1) * (2 * q)) :=
            mul_le_mul_of_nonneg_left h4 hk0
        _ = 2 * (((q : ℝ) + 1 + n + 1) * (k * q)) := by ring
        _ ≤ 2 * (((q : ℝ) + 1 + n + 1) * ys) := by gcongr
        _ ≤ 2 * W := by linarith
    linarith
end GlobalTheory.BasicFlow
