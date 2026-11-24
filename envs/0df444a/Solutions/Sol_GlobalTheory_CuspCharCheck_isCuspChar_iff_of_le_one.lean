-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.isCuspChar_iff_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:36.54039+00:00
-- url     : https://prove2.me/submissions/17377f34-0d02-4e2a-a3a8-bcb41df07364

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
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
namespace GlobalTheory.CuspCharCheck
theorem _root_.solution {d : ℕ} (hd : d ≤ 1) (χ : GL (Fin d) F → ℂ) : IsCuspChar χ ↔ IsIrrChar χ :=
  ⟨fun h => h.1, fun h => ⟨h, fun a h0 h1 => by omega⟩⟩
end GlobalTheory.CuspCharCheck
