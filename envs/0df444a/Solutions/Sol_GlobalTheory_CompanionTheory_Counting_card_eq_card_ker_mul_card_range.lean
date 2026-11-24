-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Counting.card_eq_card_ker_mul_card_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:41:38.268334+00:00
-- url     : https://prove2.me/submissions/01667cf4-95ff-4e90-93e7-7122329acb6b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardEqCardKerMulCardRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Counting
namespace GlobalTheory.CompanionTheory.Counting
theorem _root_.solution (R A B : Type) [Ring R] [AddCommGroup A] [Module R A] [Finite A]
    [AddCommGroup B] [Module R B] (f : A →ₗ[R] B) :
    Nat.card A = Nat.card ↥(LinearMap.ker f) * Nat.card ↥(LinearMap.range f) := by
  have h1 : Nat.card (A ⧸ LinearMap.ker f) = Nat.card ↥(LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have h2 : Nat.card A = Nat.card (A ⧸ (LinearMap.ker f).toAddSubgroup) * Nat.card (LinearMap.ker f).toAddSubgroup :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h3 : Nat.card (A ⧸ (LinearMap.ker f).toAddSubgroup) = Nat.card (A ⧸ LinearMap.ker f) := rfl
  have h4 : Nat.card (LinearMap.ker f).toAddSubgroup = Nat.card ↥(LinearMap.ker f) := rfl
  rw [h2, h3, h4, h1, Nat.mul_comm]
end GlobalTheory.CompanionTheory.Counting
