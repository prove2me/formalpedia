-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.exists_of_coeff_orbitSum_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:31.317293+00:00
-- url     : https://prove2.me/submissions/5b0dc981-9f44-42b0-96d4-27070fb2bee5

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
theorem _root_.solution {ν l : Fin n → ℤ} (h : (orbitSum ν).coeff l ≠ 0) :
    ∃ σ : Equiv.Perm (Fin n), ν ∘ σ.symm = l := by
  rw [coeff_orbitSum] at h
  obtain ⟨σ, hσ⟩ := Finset.card_ne_zero.1 (fun h' => h (by rw [h', Nat.cast_zero]))
  exact ⟨σ, (Finset.mem_filter.1 hσ).2⟩
end GroundTheory.Automorphic.Spherical
