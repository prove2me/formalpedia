-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCount.neg_add_out_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:05:10.609583+00:00
-- url     : https://prove2.me/submissions/c0199a9b-4313-42b7-b9a8-df09ca60f105

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
theorem _root_.solution {G : Type*} [AddGroup G] {S : AddSubgroup G} (a : G) :
    -a + (QuotientAddGroup.mk a : G ⧸ S).out ∈ S := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (QuotientAddGroup.mk a : G ⧸ S)).symm
end GlobalTheory.CompanionTheory.InertCount
