-- Prove2me | solution 1 for GroundTheory.Brauer.nonempty_algEquiv_matrix_of_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:04:04.924796+00:00
-- url     : https://prove2.me/submissions/473826d2-d3f3-4ac4-b728-e3ef01f78750

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting
import Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_matrix_of_algHom
import Theorems.Thm_GroundTheory_Brauer_tfae_maximal_subfield
import Theorems.Thm_GroundTheory_Brauer_finrank_eq_degree_of_maximal

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
theorem _root_.solution (F : Subalgebra K D) [IsMulCommutative F]
    (hF : Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F) :
    letI := fieldOfIsMulCommutative F
    Nonempty (F ⊗[K] D ≃ₐ[F] Matrix (Fin (degree K D)) (Fin (degree K D)) F) := by
  let _ := fieldOfIsMulCommutative F
  have h2 : finrank K F ^ 2 = finrank K D := ((tfae_maximal_subfield F).out 0 2).mp hF
  rw [← finrank_eq_degree_of_maximal F hF]
  exact nonempty_algEquiv_matrix_of_algHom F.val h2
end GroundTheory.Brauer
