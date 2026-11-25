-- Prove2me | solution 1 for GroundTheory.Brauer.isSeparable_coe_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:11.879607+00:00
-- url     : https://prove2.me/submissions/72ad0df7-243b-4746-abb8-9ca84a3d5d0e

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
variable {K : Type*} [Field K] {D : Type*} [DivisionRing D] [Algebra K D]
namespace GroundTheory.Brauer
theorem _root_.solution {A : Type*} [Ring A] [Algebra K A] {S : Subalgebra K A} (x : S) :
    IsSeparable K (x : A) ↔ IsSeparable K x := by
  unfold IsSeparable
  rw [← minpoly.algHom_eq S.val Subtype.val_injective x]
  rfl
end GroundTheory.Brauer
