-- Prove2me | solution 1 for GlobalTheory.BddFinite.exists_le_exp_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:24.211182+00:00
-- url     : https://prove2.me/submissions/c696f7e5-aebd-4275-8ca9-670cc5aa45dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfBoundedEmbeddingsAndValuations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
open GlobalTheory GlobalTheory.BddFinite
namespace GlobalTheory.BddFinite
theorem _root_.solution (B : WithZero (Multiplicative ℤ)) : ∃ n : ℕ, B ≤ WithZero.exp (n : ℤ) := by
  induction B using WithZero.recZeroCoe with
  | zero => exact ⟨0, zero_le'⟩
  | coe m =>
    refine ⟨(Multiplicative.toAdd m).toNat, ?_⟩
    rw [WithZero.exp, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]
    simp only [toAdd_ofAdd]
    exact Int.self_le_toNat _
end GlobalTheory.BddFinite
