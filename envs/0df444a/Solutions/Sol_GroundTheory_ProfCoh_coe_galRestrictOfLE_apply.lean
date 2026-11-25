-- Prove2me | solution 1 for GroundTheory.ProfCoh.coe_galRestrictOfLE_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:24:38.881836+00:00
-- url     : https://prove2.me/submissions/7e662642-7176-40fe-a640-be24929d2740

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
theorem _root_.solution (σ : Gal(F/K)) (x : E) :
    ((galRestrictOfLE h σ x : E) : L) = ((σ (IntermediateField.inclusion h x) : F) : L) := by
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  exact congrArg (fun y : F => (y : L)) (AlgEquiv.restrictNormal_commutes σ E x)
end GroundTheory.ProfCoh
