-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.polyEmb_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:51.944081+00:00
-- url     : https://prove2.me/submissions/34ef8997-1cfb-4906-902f-7a3de109d93f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
import Theorems.Thm_GroundTheory_Automorphic_Spherical_permAct_single
import Theorems.Thm_GroundTheory_Automorphic_Spherical_polyEmb_X

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
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (Q : MvPolynomial (Fin n) ℂ) :
    polyEmb n (rename σ Q) = permAct σ (polyEmb n Q) := by
  have : (polyEmb n).comp (rename σ) = (permAct σ).comp (polyEmb n) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, polyEmb_X, polyEmb_X, permAct_single]
    congr 1
    funext j
    simp only [Function.comp_apply, Pi.single_apply, Equiv.symm_apply_eq]
  exact AlgHom.congr_fun this Q
end GroundTheory.Automorphic.Spherical
