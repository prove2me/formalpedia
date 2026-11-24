-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.signChar_transv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:38.244222+00:00
-- url     : https://prove2.me/submissions/316dbe71-5e19-4a43-b966-11fcc9b0ac2a

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
theorem _root_.solution : signChar transv = -1 := by
  have hp : permOfGL 2 transv = Equiv.swap ![0, 1] ![1, 1] := by
    ext v i
    revert v i
    decide
  show Units.map _ (Equiv.Perm.sign (permOfGL 2 transv)) = -1
  rw [hp, Equiv.Perm.sign_swap (by decide)]
  ext; simp
end GlobalTheory.CuspCharCheck
