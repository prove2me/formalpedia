-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_mem_unitaryGroupMatrix_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:27.922454+00:00
-- url     : https://prove2.me/submissions/630b40c1-5692-46f8-bf36-98f719ebb105

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Theorems.Thm_GroundTheory_Automorphic_isUnit_det_of_unitary

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
    (M : Matrix ι ι A) :
    (∃ g ∈ unitaryGroupMatrix s H, (g : Matrix ι ι A) = M) ↔ (M.map s)ᵀ * H * M = H := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hM
    exact ⟨nonsingInvUnit M (isUnit_det_of_unitary s hH hM), hM, rfl⟩
end GroundTheory.Automorphic
