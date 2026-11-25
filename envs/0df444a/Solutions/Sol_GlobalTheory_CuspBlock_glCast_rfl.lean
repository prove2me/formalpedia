-- Prove2me | solution 1 for GlobalTheory.CuspBlock.glCast_rfl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:38:58.700415+00:00
-- url     : https://prove2.me/submissions/ea7ab99a-66fd-47e1-a1e7-21a80423fcc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TripSizesSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SmGL
open GlobalTheory GlobalTheory.CuspBlock
variable (k : Type) [CommRing k]
namespace GlobalTheory.CuspBlock
theorem _root_.solution {a : ℕ} : glCast (k := k) (rfl : a = a) = MonoidHom.id _ := rfl
end GlobalTheory.CuspBlock
