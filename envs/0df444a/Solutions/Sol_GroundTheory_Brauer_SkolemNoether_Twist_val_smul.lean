-- Prove2me | solution 1 for GroundTheory.Brauer.SkolemNoether.Twist.val_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:01.012974+00:00
-- url     : https://prove2.me/submissions/d9851866-39f8-4c7e-8a98-12552ba22102

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
theorem _root_.solution (r : A ⊗[K] Bᵐᵒᵖ) (x : Twist f) : (r • x).val = bimoduleHom f r x.val := rfl
end GroundTheory.Brauer.SkolemNoether.Twist
