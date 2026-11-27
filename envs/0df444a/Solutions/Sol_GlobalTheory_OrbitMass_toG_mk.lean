-- Prove2me | solution 1 for GlobalTheory.OrbitMass.toG_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:59.64503+00:00
-- url     : https://prove2.me/submissions/9b8f4e68-a85b-4a17-aa67-69104085a45c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitMassFormulaFiniteIndexSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MulAction
open GlobalTheory GlobalTheory.OrbitMass
variable {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D]
namespace GlobalTheory.OrbitMass
theorem _root_.solution (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (y : D) :
    toG ι hc (Quotient.mk'' y) = Quotient.mk'' y := rfl
end GlobalTheory.OrbitMass
