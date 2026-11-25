-- Prove2me | solution 1 for GroundTheory.Brauer.finrank_baseChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:25:39.646548+00:00
-- url     : https://prove2.me/submissions/de9a698b-f2d2-45be-836e-4402c795da25

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct Algebra.TensorProduct
variable (K L A : Type*) [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]
namespace GroundTheory.Brauer
theorem _root_.solution : Module.finrank L (L ⊗[K] A) = Module.finrank K A :=
  Module.finrank_baseChange
end GroundTheory.Brauer
