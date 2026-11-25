-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.isoOfBijective_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:32.286446+00:00
-- url     : https://prove2.me/submissions/fbf5a580-3898-42c4-89fd-3e4e2d2feea5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Hom
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')
local notation "F" => Units.map (RingHom.toMonoidHom f)
namespace GlobalTheory.Ex.NumD.Hom
theorem _root_.solution {M M' : NumD O} (J : NumD.Hom (RingHom.id O) M M') (hJ : Function.Bijective J.φ)
    (g : M.Gt) (g' : M'.Gt) : (J.isoOfBijective hJ).Rel g g' ↔ J.Rel g g' := Iff.rfl
end GlobalTheory.Ex.NumD.Hom
