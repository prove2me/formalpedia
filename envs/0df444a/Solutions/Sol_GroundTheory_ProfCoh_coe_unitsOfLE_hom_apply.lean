-- Prove2me | solution 1 for GroundTheory.ProfCoh.coe_unitsOfLE_hom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:23:21.85789+00:00
-- url     : https://prove2.me/submissions/829b22e5-9bb8-41aa-9200-60e5332b5adf

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
variable {K L : Type u} [Field K] [Field L] [Algebra K L] {E F : IntermediateField K L}
  (h : E ≤ F) [Normal K E]
namespace GroundTheory.ProfCoh
theorem _root_.solution (x : Additive Eˣ) :
    (((Additive.toMul (α := Fˣ) ((unitsOfLE h).hom x) : Fˣ) : F) : L) =
      (((Additive.toMul (α := Eˣ) x : Eˣ) : E) : L) :=
  rfl
end GroundTheory.ProfCoh
