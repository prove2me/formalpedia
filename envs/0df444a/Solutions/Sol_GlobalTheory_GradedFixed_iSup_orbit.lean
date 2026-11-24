-- Prove2me | solution 1 for GlobalTheory.GradedFixed.iSup_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:36:27.283165+00:00
-- url     : https://prove2.me/submissions/969983b0-b69b-4432-babf-c169769d4d7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight
import Theorems.Thm_GlobalTheory_GradedFixed_le_WA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.GradedFixed
theorem _root_.solution (V : ι → Submodule ℂ M) (i : ι) :
    (⨆ g : G, V (g • i)) = WA V (orbit G i) := by
  apply le_antisymm
  · exact iSup_le fun g => le_WA V (mem_orbit i g)
  · refine iSup₂_le fun j hj => ?_
    obtain ⟨g, rfl⟩ := hj
    exact le_iSup (fun g : G => V (g • i)) g
end GlobalTheory.GradedFixed
