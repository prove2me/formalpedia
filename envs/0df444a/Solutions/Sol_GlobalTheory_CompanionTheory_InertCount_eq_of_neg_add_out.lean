-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCount.eq_of_neg_add_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:06:31.109674+00:00
-- url     : https://prove2.me/submissions/27b6078f-d32c-451a-a455-089f1b1b8980

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCount
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}
namespace GlobalTheory.CompanionTheory.InertCount
theorem _root_.solution {G : Type*} [AddGroup G] {S : AddSubgroup G} (y y' : G ⧸ S)
    (h : -y.out + y'.out ∈ S) : y = y' := by
  calc y = QuotientAddGroup.mk y.out := (QuotientAddGroup.out_eq' y).symm
    _ = QuotientAddGroup.mk y'.out := QuotientAddGroup.eq.mpr h
    _ = y' := QuotientAddGroup.out_eq' y'
end GlobalTheory.CompanionTheory.InertCount
