-- Prove2me | solution 1 for GlobalTheory.LamSize.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:34:39.657054+00:00
-- url     : https://prove2.me/submissions/1448e0a3-11aa-472e-a96f-75afdc683251

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.LamSize
namespace GlobalTheory.LamSize
theorem _root_.solution : ∀ (C b T T' : ℝ) (r N : ℕ), 0 ≤ C → 3 ≤ b → (N : ℝ) ≤ b → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T' → 1 ≤ b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ)) ∧ (N : ℝ) * b ^ (11 * (2 * r + 2)) ≤ (b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 * (T * T') := by
  intro C b T T' r N hC hb hN hT hT'
  have hm1 : 1 ≤ 2 * r + 2 := by omega
  generalize 2 * r + 2 = m at *
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine ⟨Real.one_le_rpow hb1 (by positivity), ?_⟩
  have hp : 0 < b ^ (-(C * (m : ℝ))) := Real.rpow_pos_of_pos hb0 _
  have hTT : b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))) ≤ T * T' :=
    mul_le_mul hT hT' hp.le (hp.le.trans hT)
  have key : (b ^ ((6 + C) * (m : ℝ))) ^ 2 * (b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))))
      = b ^ (12 * m) := by
    rw [sq, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  calc (N : ℝ) * b ^ (11 * m) ≤ b * b ^ (11 * m) := by gcongr
    _ = b ^ (11 * m + 1) := by ring
    _ ≤ b ^ (12 * m) := pow_le_pow_right₀ hb1 (by omega)
    _ = _ := key.symm
    _ ≤ _ := by gcongr
end GlobalTheory.LamSize
