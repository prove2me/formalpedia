-- Prove2me | solution 1 for GlobalTheory.IntersectionSymm.arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:33.908594+00:00
-- url     : https://prove2.me/submissions/901703c9-6636-4224-84e5-516588e26cda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.IntersectionSymm
namespace GlobalTheory.IntersectionSymm
theorem _root_.solution (h : ℕ∞) (d : WithBot ℕ∞) (h1 : (h : WithBot ℕ∞) + d ≤ 2) (h2 : ¬ d ≤ 0) :
    h ≤ 1 ∧ (h = 1 → d = 1) := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le h2
  | coe e =>
    have h1' : h + e ≤ 2 := by
      rw [← WithBot.coe_add, ← WithBot.coe_ofNat, WithBot.coe_le_coe] at h1; exact h1
    have h2' : ¬ e ≤ 0 := fun h => h2 (by exact_mod_cast h)
    induction e using ENat.recTopCoe with
    | top => simp at h1'
    | coe n =>
      induction h using ENat.recTopCoe with
      | top => simp at h1'
      | coe m =>
        have a1 : m + n ≤ 2 := by exact_mod_cast h1'
        have a2 : ¬ n ≤ 0 := fun h => h2' (by exact_mod_cast h)
        refine ⟨by exact_mod_cast (show m ≤ 1 by omega), fun hm => ?_⟩
        have : m = 1 := by exact_mod_cast hm
        have : n = 1 := by omega
        subst this; rfl
end GlobalTheory.IntersectionSymm
