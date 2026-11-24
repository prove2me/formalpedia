-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.polyEmb_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:41:12.446226+00:00
-- url     : https://prove2.me/submissions/ef70e9c8-d031-4a24-aee7-cf63b8ea9b4e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
import Theorems.Thm_GroundTheory_Automorphic_Spherical_natToInt_apply
import Theorems.Thm_GroundTheory_Automorphic_Spherical_polyEmb_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open AddMonoidAlgebra MvPolynomial
open GroundTheory.Automorphic.Spherical
variable {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (i : Fin n) : polyEmb n (X i) = monomial (Pi.single i 1) := by
  rw [X, polyEmb_monomial]
  congr 1
  funext j
  rw [natToInt_apply, Finsupp.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Ne.symm h]
end GroundTheory.Automorphic.Spherical
