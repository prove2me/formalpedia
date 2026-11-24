-- Prove2me | solution 1 for GlobalTheory.Ex.Level3.bun_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:07:57.427862+00:00
-- url     : https://prove2.me/submissions/a1f28ebe-0f7d-4efb-bc7c-d1aa9ad86eed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Theorems.Thm_GlobalTheory_Ex_Level3_cube_nondeg

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
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.Level3
namespace GlobalTheory.Ex.Level3
theorem _root_.solution (f : Multiplicative (ZMod 3) →* Oˣ) (hf : Function.Injective f) (s : A₃ → O) (b : A₃)
    (hb : ∀ b' : A₃, (bun f s).weil 3 b b' = 1) : b = 1 := by
  refine cube_nondeg b fun b' => hf ?_
  rw [map_one, map_div, cubN, cubN, map_prod, map_prod]
  exact hb b'
end GlobalTheory.Ex.Level3
