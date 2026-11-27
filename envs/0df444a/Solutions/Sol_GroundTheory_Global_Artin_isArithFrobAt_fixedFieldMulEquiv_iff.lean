-- Prove2me | solution 1 for GroundTheory.Global.Artin.isArithFrobAt_fixedFieldMulEquiv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:46.223293+00:00
-- url     : https://prove2.me/submissions/9289db34-6e5e-4715-b4e6-6d51ee1c2592

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesInfinite
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))
namespace GroundTheory.Global.Artin
theorem _root_.solution (h : H) (P : Ideal (𝓞 L)) :
    IsArithFrobAt (𝓞 (fixedField H)) (fixedFieldMulEquiv H h) P ↔
      IsArithFrobAt (𝓞 (fixedField H)) h P :=
  Iff.rfl
end GroundTheory.Global.Artin
