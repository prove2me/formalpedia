-- Prove2me | solution 1 for GroundTheory.Global.Artin.subfieldInfinitePlaceEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:40:12.492078+00:00
-- url     : https://prove2.me/submissions/e5f34425-9a01-47de-8048-feb2b5580cd5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesInfinite

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
open NumberField IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))
variable (w : InfinitePlace L)
namespace GroundTheory.Global.Artin
theorem _root_.solution (x : Gal(L/K)) :
    (subfieldInfinitePlaceEquiv H w (DoubleCoset.mk _ _ x) : InfinitePlace (fixedField H)) =
      subfieldInfinitePlace H w x :=
  rfl
end GroundTheory.Global.Artin
