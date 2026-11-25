-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.ev_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:59.529364+00:00
-- url     : https://prove2.me/submissions/e3bc43ed-b213-4387-ab90-f155683252ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}
  (I : TateIso D k Q (fun a x => ρ a x) e)
namespace GlobalTheory.HeckeCompare
theorem _root_.solution (n : ℕ) (a b : D.La) : I.ev n (a - b) = I.ev n a / I.ev n b := (evH I n).map_sub a b
end GlobalTheory.HeckeCompare
