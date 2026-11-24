-- Prove2me | solution 1 for GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:10:34.355871+00:00
-- url     : https://prove2.me/submissions/f7905b7b-8b3a-4cae-9c79-cfeb11812499

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ValuationPowSubPowLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.ValuationPowSubPow
namespace GlobalTheory.ValuationPowSubPow
theorem _root_.solution {K : Type u_1} {Γ : Type u_2} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {a b : K}
    (ha : w a ≤ 1) (hb : w b ≤ 1) (m : ℕ) : w (a ^ m - b ^ m) ≤ w (a - b) := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by ring
    rw [h]
    refine w.map_add_le ?_ ?_
    · rw [map_mul]
      exact (mul_le_of_le_one_left' ha).trans ih
    · rw [map_mul, map_pow]
      exact mul_le_of_le_one_left' (pow_le_one' hb n)
end GlobalTheory.ValuationPowSubPow
