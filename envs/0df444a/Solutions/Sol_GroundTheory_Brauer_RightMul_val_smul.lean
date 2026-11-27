-- Prove2me | solution 1 for GroundTheory.Brauer.RightMul.val_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:25.662207+00:00
-- url     : https://prove2.me/submissions/f64d8922-f595-4a0c-9b73-c969b5e50f90

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting

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
open TensorProduct Module
universe u v w
variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A] {L : Type*} [Field L]
  [Algebra K L]
open GroundTheory.Brauer.RightMul
variable (ι : L →ₐ[K] A)
namespace GroundTheory.Brauer.RightMul
theorem _root_.solution (l : L) (x : RightMul ι) : (l • x).val = x.val * ι l := rfl
end GroundTheory.Brauer.RightMul
