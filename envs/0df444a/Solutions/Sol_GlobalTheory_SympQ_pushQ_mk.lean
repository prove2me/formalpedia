-- Prove2me | solution 1 for GlobalTheory.SympQ.pushQ_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:23:05.273785+00:00
-- url     : https://prove2.me/submissions/78c3a3e9-0319-4963-bfce-ec39b1669165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WpQTrivRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open GlobalTheory GlobalTheory.SympQ
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.SympQ
theorem _root_.solution (M n : ℕ) (p : N.QT M) :
    pushQ N M n (QuotientGroup.mk p) = QuotientGroup.mk (pushRep N M n p) := rfl
end GlobalTheory.SympQ
