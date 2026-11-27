-- Prove2me | solution 1 for GroundTheory.Brauer.CentralizerModule.mulRight_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:47:29.518887+00:00
-- url     : https://prove2.me/submissions/ed54b6c5-fbd4-4b18-b09f-ee96be6df7d5

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer

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
open SkolemNoether
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A)
open GroundTheory.Brauer.CentralizerModule
namespace GroundTheory.Brauer.CentralizerModule
theorem _root_.solution (c : Subalgebra.centralizer K (B : Set A)) (x : Twist B.val) :
    (mulRight B c x).val = x.val * c := rfl
end GroundTheory.Brauer.CentralizerModule
