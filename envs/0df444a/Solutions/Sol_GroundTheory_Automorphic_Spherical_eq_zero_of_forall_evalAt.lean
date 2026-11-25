-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.eq_zero_of_forall_evalAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:35.783624+00:00
-- url     : https://prove2.me/submissions/fd45941b-7ab3-4c64-a34a-e8073a3ffe2f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Theorems.Thm_GroundTheory_Automorphic_Spherical_evalAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Spherical_monomialChar_injective

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
open GroundTheory.Automorphic.Spherical
open AddMonoidAlgebra
variable {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution {p : LaurentRing n} (h : ∀ w, evalAt w p = 0) : p = 0 := by
  have hli : LinearIndependent ℂ (fun l : Fin n → ℤ => ((monomialChar l : (Fin n → ℂˣ) →* ℂ) :
      (Fin n → ℂˣ) → ℂ)) :=
    (linearIndependent_monoidHom (Fin n → ℂˣ) ℂ).comp _ monomialChar_injective
  have hz : Finsupp.linearCombination ℂ (fun l : Fin n → ℤ =>
      ((monomialChar l : (Fin n → ℂˣ) →* ℂ) : (Fin n → ℂˣ) → ℂ)) p.coeff =
      Finsupp.linearCombination ℂ (fun l : Fin n → ℤ =>
      ((monomialChar l : (Fin n → ℂˣ) →* ℂ) : (Fin n → ℂˣ) → ℂ)) 0 := by
    rw [map_zero]
    funext w
    rw [Finsupp.linearCombination_apply, Pi.zero_apply, ← h w, evalAt_apply, Finsupp.sum,
      Finsupp.sum, Finset.sum_apply]
    rfl
  exact AddMonoidAlgebra.coeff_eq_zero.1 (hli hz)
end GroundTheory.Automorphic.Spherical
