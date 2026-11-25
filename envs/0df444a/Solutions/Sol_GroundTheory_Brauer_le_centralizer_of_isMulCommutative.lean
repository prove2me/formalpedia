-- Prove2me | solution 1 for GroundTheory.Brauer.le_centralizer_of_isMulCommutative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:30:50.737349+00:00
-- url     : https://prove2.me/submissions/dabfa954-bbab-40fc-b2b0-90841dd5824f

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
theorem _root_.solution (F : Subalgebra K D) [IsMulCommutative F] :
    F ≤ Subalgebra.centralizer K (F : Set D) := by
  intro x hx
  rw [Subalgebra.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val ((isMulCommutative_iff.mp inferInstance) (⟨y, hy⟩ : F) ⟨x, hx⟩)
end GroundTheory.Brauer
