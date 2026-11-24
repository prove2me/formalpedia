-- Prove2me | solution 1 for GlobalTheory.chord_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:29:10.974624+00:00
-- url     : https://prove2.me/submissions/c5aff1f7-7dfe-4f5c-8157-38f05ca8897a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {x y p q g₂ g₃ s : ℂ} (hxp : x - p ≠ 0) (hs : s = (y - q) / (x - p))
    (h : y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃) (h' : q ^ 2 = 4 * p ^ 3 - g₂ * p - g₃) :
    q = y - s * (x - p) ∧ g₂ = 4 * (x ^ 2 + x * p + p ^ 2) - s * (2 * y - s * (x - p)) ∧
      g₃ = 4 * x ^ 3 - g₂ * x - y ^ 2 := by
  have hq : q = y - s * (x - p) := by rw [hs]; field_simp; ring
  refine ⟨hq, mul_left_cancel₀ hxp ?_, by linear_combination h⟩
  rw [hq] at h'
  linear_combination h - h'
end GlobalTheory
