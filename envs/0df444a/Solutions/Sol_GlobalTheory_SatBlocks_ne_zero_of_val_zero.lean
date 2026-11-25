-- Prove2me | solution 1 for GlobalTheory.SatBlocks.ne_zero_of_val_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:17:19.0909+00:00
-- url     : https://prove2.me/submissions/04e52445-36aa-444b-94c6-ee32b5c7d673

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
theorem _root_.solution {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {z : C}
    (h : v z = 0) : z ≠ 0 := by
  rintro rfl
  simp at h
end GlobalTheory.SatBlocks
