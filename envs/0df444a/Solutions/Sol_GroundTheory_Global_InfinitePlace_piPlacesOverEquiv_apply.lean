-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.piPlacesOverEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:28:19.651397+00:00
-- url     : https://prove2.me/submissions/9f5c487a-6608-49d3-9621-7c21d75813a0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (x : (v : InfinitePlace K) → PiPlacesOver (L := L) v)
    (w : InfinitePlace L) :
    piPlacesOverEquiv x w = x (w.comap (algebraMap K L)) ⟨w, liesOver_comap w⟩ := rfl
end GroundTheory.Global.InfinitePlace
