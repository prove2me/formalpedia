-- Prove2me | solution 1 for GroundTheory.Brauer.tfae_maximal_subfield
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:07:26.871818+00:00
-- url     : https://prove2.me/submissions/3c6add71-a0fe-45af-93b9-55a318727d95

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting
import Theorems.Thm_GroundTheory_Brauer_maximal_isMulCommutative_iff_centralizer_eq
import Theorems.Thm_GroundTheory_Brauer_centralizer_eq_iff_finrank_sq
import Theorems.Thm_GroundTheory_Brauer_degree_eq_iff


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
variable [Algebra.IsCentral K D] [FiniteDimensional K D]
namespace GroundTheory.Brauer
theorem _root_.solution (F : Subalgebra K D) [IsMulCommutative F] :
    List.TFAE [Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F,
      Subalgebra.centralizer K (F : Set D) = F, finrank K F ^ 2 = finrank K D,
      finrank K F = degree K D] := by
  tfae_have 1 ↔ 2 := maximal_isMulCommutative_iff_centralizer_eq F
  tfae_have 2 ↔ 3 := centralizer_eq_iff_finrank_sq F
  tfae_have 3 ↔ 4 :=
    ⟨fun h ↦ ((degree_eq_iff K D _).mpr h.symm).symm,
      fun h ↦ ((degree_eq_iff K D _).mp h.symm).symm⟩
  tfae_finish
end GroundTheory.Brauer
