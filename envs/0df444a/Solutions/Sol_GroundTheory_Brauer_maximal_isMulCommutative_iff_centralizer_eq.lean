-- Prove2me | solution 1 for GroundTheory.Brauer.maximal_isMulCommutative_iff_centralizer_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:40.642138+00:00
-- url     : https://prove2.me/submissions/b600787f-2238-4866-a41f-921ed46ff1bc

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting
import Theorems.Thm_GroundTheory_Brauer_le_centralizer_of_isMulCommutative
import Theorems.Thm_GroundTheory_Brauer_isMulCommutative_adjoin_insert

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
    Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F ↔
      Subalgebra.centralizer K (F : Set D) = F := by
  constructor
  · intro hmax
    refine le_antisymm (fun x hx ↦ ?_) (le_centralizer_of_isMulCommutative F)
    have hG := isMulCommutative_adjoin_insert F hx
    have hle : F ≤ Algebra.adjoin K (insert x (F : Set D)) :=
      fun z hz ↦ Algebra.subset_adjoin (Set.mem_insert_of_mem _ hz)
    exact hmax.2 hG hle (Algebra.subset_adjoin (Set.mem_insert x _))
  · intro hc
    refine ⟨inferInstance, fun G hG hle ↦ ?_⟩
    have hG' : IsMulCommutative G := hG
    rw [← hc]
    intro y hy
    rw [Subalgebra.mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val ((isMulCommutative_iff.mp hG') ⟨z, hle hz⟩ ⟨y, hy⟩)
end GroundTheory.Brauer
