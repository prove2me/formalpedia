-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.isoRefl_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:34.203665+00:00
-- url     : https://prove2.me/submissions/f510ab15-71b9-474a-840a-f50f20042183

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
theorem _root_.solution (N : NumD O) (g g' : N.Gt) : (isoRefl N).Rel g g' ↔ g' = g :=
  ⟨fun h => NumD.Gt.ext h.1 (funext fun χ => by simpa [isoRefl] using h.2 χ), by
    rintro rfl; exact ⟨rfl, fun χ => by simp [isoRefl]⟩⟩
end GlobalTheory.Ex.TateInh
