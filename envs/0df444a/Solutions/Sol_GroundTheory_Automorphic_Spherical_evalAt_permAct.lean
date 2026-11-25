-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.evalAt_permAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:50.438174+00:00
-- url     : https://prove2.me/submissions/06f06c78-6665-4007-a0db-83208b0fd9a5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
import Theorems.Thm_GroundTheory_Automorphic_Spherical_permAct_single
import Theorems.Thm_GroundTheory_Automorphic_Spherical_evalAt_single


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
theorem _root_.solution (w : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) (p : LaurentRing n) :
    evalAt w (permAct σ p) = evalAt (w ∘ σ) p := by
  have : (evalAt w).comp (permAct σ) = evalAt (w ∘ σ) := by
    refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
    rw [AlgHom.comp_apply, permAct_single, evalAt_single, evalAt_single, monomialChar_apply,
      monomialChar_apply]
    congr 1
    exact Fintype.prod_equiv σ.symm _ _ fun i => by simp
  exact AlgHom.congr_fun this p
end GroundTheory.Automorphic.Spherical
