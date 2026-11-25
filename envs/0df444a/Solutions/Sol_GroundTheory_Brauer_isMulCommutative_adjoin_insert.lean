-- Prove2me | solution 1 for GroundTheory.Brauer.isMulCommutative_adjoin_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:41:33.270643+00:00
-- url     : https://prove2.me/submissions/8742bc55-aea7-40d5-89eb-e2d49f4b733f

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
theorem _root_.solution (F : Subalgebra K D) [IsMulCommutative F] {y : D}
    (hy : y ∈ Subalgebra.centralizer K (F : Set D)) :
    IsMulCommutative (Algebra.adjoin K (insert y (F : Set D))) := by
  refine Algebra.isMulCommutative_adjoin K fun a ha b hb ↦ ?_
  rw [Subalgebra.mem_centralizer_iff] at hy
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · rfl
  · exact (hy b hb).symm
  · exact hy a ha
  · exact congrArg Subtype.val ((isMulCommutative_iff.mp inferInstance) (⟨a, ha⟩ : F) ⟨b, hb⟩)
end GroundTheory.Brauer
