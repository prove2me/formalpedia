-- Prove2me | solution 1 for GroundTheory.ProfCoh.unitsTowerHom_hom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:22:49.659744+00:00
-- url     : https://prove2.me/submissions/200f3099-e15f-4fb8-b611-3d8794c516ee

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_BrauerInflationDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology
universe u
variable (K E F : Type u) [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [Normal K E]
namespace GroundTheory.ProfCoh
theorem _root_.solution (x : Additive Eˣ) :
    ((Additive.toMul (α := Fˣ) ((unitsTowerHom K E F).hom x) : Fˣ) : F) =
      algebraMap E F ((Additive.toMul (α := Eˣ) x : Eˣ) : E) :=
  rfl
end GroundTheory.ProfCoh
