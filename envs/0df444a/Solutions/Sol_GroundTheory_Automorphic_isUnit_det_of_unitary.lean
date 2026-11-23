-- Prove2me | solution 1 for GroundTheory.Automorphic.isUnit_det_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:59.272546+00:00
-- url     : https://prove2.me/submissions/187fc25c-2e60-4ecb-8225-b7c01e22937a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix
variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
theorem _root_.solution (s : A →+* A) {H : Matrix ι ι A} (hH : IsUnit H.det)
    {M : Matrix ι ι A} (hM : (M.map s)ᵀ * H * M = H) : IsUnit M.det := by
  have hd := congrArg Matrix.det hM
  have hs : (M.map s).det = s M.det := (RingHom.map_det s M).symm
  rw [det_mul, det_mul, det_transpose, hs] at hd
  have h2 : M.det * s M.det = 1 := by
    apply hH.mul_left_cancel
    linear_combination hd
  exact IsUnit.of_mul_eq_one _ h2
end GroundTheory.Automorphic
