-- Prove2me | solution 1 for GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingHomeomorph_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:10.035952+00:00
-- url     : https://prove2.me/submissions/0b47d470-4aa7-4b9e-ae79-d7821ed38243

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdele
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology

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
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace GroundTheory.Global.InfinitePlace
theorem _root_.solution (x : L ⊗[K] InfiniteAdeleRing K) :
    tensorInfiniteAdeleRingHomeomorph x = tensorInfiniteAdeleRingEquiv x := rfl
end GroundTheory.Global.InfinitePlace
