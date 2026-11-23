-- Prove2me | solution 1 for GroundTheory.Brauer.SkolemNoether.Twist.of_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:09:41.033198+00:00
-- url     : https://prove2.me/submissions/1afef391-5ff1-4f32-a59d-11b0835ab73c

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether

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
open TensorProduct
open GroundTheory.Brauer.SkolemNoether
variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
open GroundTheory.Brauer.SkolemNoether.Twist
variable (f : B →ₐ[K] A)
namespace GroundTheory.Brauer.SkolemNoether.Twist
theorem _root_.solution (x : Twist f) : of f x.val = x := rfl
end GroundTheory.Brauer.SkolemNoether.Twist
