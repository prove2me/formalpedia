-- Prove2me | solution 1 for GlobalTheory.ValBoundDenom.exists_nat_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:28.172955+00:00
-- url     : https://prove2.me/submissions/71ece683-696d-4125-b736-d0ffb9bfc5ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCommonDenominatorOfValuationLeCofinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.ValBoundDenom
namespace GlobalTheory.ValBoundDenom
theorem _root_.solution (a : WithZero (Multiplicative ℤ)) : ∃ n : ℕ, a ≤ WithZero.exp (n : ℤ) := by
  induction a using WithZero.recZeroCoe with
  | zero => exact ⟨0, zero_le'⟩
  | coe m =>
    refine ⟨(Multiplicative.toAdd m).toNat, ?_⟩
    show (m : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd ((Multiplicative.toAdd m).toNat : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [WithZero.coe_le_coe]
    exact Int.self_le_toNat (Multiplicative.toAdd m)
end GlobalTheory.ValBoundDenom
