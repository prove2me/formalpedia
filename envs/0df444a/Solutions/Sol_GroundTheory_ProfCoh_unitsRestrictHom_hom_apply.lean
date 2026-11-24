-- Prove2me | solution 1 for GroundTheory.ProfCoh.unitsRestrictHom_hom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:20:17.463318+00:00
-- url     : https://prove2.me/submissions/a5499bb9-c322-4e2d-a155-fc414cb4165a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisCohomology_UnitsInflationCochainsFHomApply

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
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable {K L}
namespace GroundTheory.ProfCoh
theorem _root_.solution (E : IntermediateField K L) [Normal K E]
    (x : Additive Eˣ) :
    ((Additive.toMul (α := Lˣ) ((unitsRestrictHom E).hom x) : Lˣ) : L) =
      ((Additive.toMul (α := Eˣ) x : Eˣ) : E) :=
  rfl
end GroundTheory.ProfCoh
