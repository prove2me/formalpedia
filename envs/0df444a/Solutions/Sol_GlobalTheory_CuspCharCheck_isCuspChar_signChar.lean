-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.isCuspChar_signChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:57:29.385785+00:00
-- url     : https://prove2.me/submissions/8e242a9d-7e76-46df-b759-629b8c2e1a97

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff
import Theorems.Thm_GlobalTheory_CuspCharCheck_isCuspChar_of_hom
import Theorems.Thm_GlobalTheory_CuspCharCheck_transv_mem
import Theorems.Thm_GlobalTheory_CuspCharCheck_signChar_transv

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
theorem _root_.solution : IsCuspChar (fun x => (signChar x : ℂ)) := by
  refine isCuspChar_of_hom _ fun a h0 h1 => ?_
  obtain rfl : a = 1 := by omega
  refine ⟨transv, transv_mem, ?_⟩
  rw [signChar_transv]
  norm_num
end GlobalTheory.CuspCharCheck
