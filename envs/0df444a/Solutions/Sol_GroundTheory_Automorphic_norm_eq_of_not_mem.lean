-- Prove2me | solution 1 for GroundTheory.Automorphic.norm_eq_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:43.99117+00:00
-- url     : https://prove2.me/submissions/8f793e29-49d9-4326-82d7-384c1f655146

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Theorems.Thm_GroundTheory_Automorphic_repr_self_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E]
variable {F E}
variable [Algebra.IsQuadraticExtension F E]
namespace GroundTheory.Automorphic
theorem _root_.solution {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.norm F x = -(basisOneOf hx).repr (x * x) 0 := by
  rw [Algebra.norm_eq_matrix_det (basisOneOf hx), Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisOneOf_zero,
    basisOneOf_one, mul_one, repr_self_zero, repr_self_one]
  ring
end GroundTheory.Automorphic
