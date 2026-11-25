-- Prove2me | solution 1 for GlobalTheory.SatBlocks.mem_intRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:16:49.481708+00:00
-- url     : https://prove2.me/submissions/dca1daeb-f63a-4a32-a50f-1e7cb48ca952

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SaturatedBlocksSummand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.SatBlocks
namespace GlobalTheory.SatBlocks
theorem _root_.solution {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (z : C) :
    z ∈ intRing v ↔ ((0 : ℝ) : WithTop ℝ) ≤ v z := Iff.rfl
end GlobalTheory.SatBlocks
