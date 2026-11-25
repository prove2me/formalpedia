-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.coeff_orbitSum_self_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:27.990264+00:00
-- url     : https://prove2.me/submissions/6bb14376-5e8c-492f-b86c-71545facb357

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
import Theorems.Thm_GroundTheory_Automorphic_Spherical_coeff_orbitSum

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
theorem _root_.solution (ν : Fin n → ℤ) : (orbitSum ν).coeff ν ≠ 0 := by
  rw [coeff_orbitSum, Nat.cast_ne_zero, Finset.card_ne_zero]
  exact ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
end GroundTheory.Automorphic.Spherical
