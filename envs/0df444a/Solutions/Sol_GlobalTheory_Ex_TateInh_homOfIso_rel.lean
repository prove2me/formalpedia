-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.homOfIso_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:58.857722+00:00
-- url     : https://prove2.me/submissions/64ea3be8-9428-42c5-86b3-441d6cc9eb60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh
namespace GlobalTheory.Ex.TateInh
theorem _root_.solution {N N' : NumD O} (I : NumD.Iso N N') (g : N.Gt) (g' : N'.Gt) :
    (homOfIso I).Rel g g' ↔ I.Rel g g' := Iff.rfl
end GlobalTheory.Ex.TateInh
