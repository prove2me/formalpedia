-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.isCuspChar_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:56:17.995628+00:00
-- url     : https://prove2.me/submissions/1105d7a6-9ad6-4d3d-8be8-c3c2e39a3df8

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff
import Theorems.Thm_GlobalTheory_CuspCharCheck_isCuspChar_iff_of_le_one
import Theorems.Thm_GlobalTheory_CuspCharCheck_isIrrChar_of_hom

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
theorem _root_.solution (c : GL (Fin 1) F →* ℂˣ) : IsCuspChar (fun x => (c x : ℂ)) :=
  (isCuspChar_iff_of_le_one le_rfl _).2 (isIrrChar_of_hom c)
end GlobalTheory.CuspCharCheck
