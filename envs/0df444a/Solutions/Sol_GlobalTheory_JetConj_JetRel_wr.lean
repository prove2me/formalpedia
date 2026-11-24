-- Prove2me | solution 1 for GlobalTheory.JetConj.JetRel.wr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:23:23.82892+00:00
-- url     : https://prove2.me/submissions/49e0e6d6-1737-4cbc-9309-810e661e51c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero
import Theorems.Thm_GlobalTheory_JetConj_JetRel_mul
import Theorems.Thm_GlobalTheory_JetConj_JetRel_pow
import Theorems.Thm_GlobalTheory_JetConj_JetRel_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
open GlobalTheory GlobalTheory.JetConj
variable {L : PeriodPair} {σ : ℂ → ℂ}
namespace GlobalTheory.JetConj
namespace JetRel
theorem _root_.solution {S : Subring (ℂ × ℂ)} {f f' : ℂ → ℂ} (H : JetRel S f f') : JetRel S (wr f) (wr f') :=
  (H.mul H.deriv.deriv).sub (H.deriv.pow 2)
end JetRel
end GlobalTheory.JetConj
