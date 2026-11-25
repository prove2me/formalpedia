-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.zero_not_isIrrChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:52:03.868474+00:00
-- url     : https://prove2.me/submissions/d988bbe6-b3e1-4d26-aeba-32d1611e17a1

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CuspElliptic
open GlobalTheory GlobalTheory.CuspCharCheck
variable {G : Type} [Group G]
namespace GlobalTheory.CuspCharCheck
theorem _root_.solution [Fintype G] : ¬ IsIrrChar (fun _ : G => (0 : ℂ)) := by
  rintro ⟨-, h⟩
  simp only [zero_mul, Finset.sum_const_zero] at h
  exact (Nat.cast_ne_zero.2 Fintype.card_ne_zero) h.symm
end GlobalTheory.CuspCharCheck
