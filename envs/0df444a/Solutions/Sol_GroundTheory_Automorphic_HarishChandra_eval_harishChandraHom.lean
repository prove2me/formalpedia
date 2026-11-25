-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.eval_harishChandraHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:56:21.477878+00:00
-- url     : https://prove2.me/submissions/b9e626ab-6661-475f-bc0b-194c040c4cba

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eval_translate
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_harishChandraHom_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (z : Subalgebra.center ℂ (U n)) (lam : Fin n → ℂ) :
    eval lam (harishChandraHom z) = eval (lam - rhoVec n) (hcProjLin (z : U n)) := by
  rw [harishChandraHom_apply, eval_translate, sub_eq_add_neg]
end GroundTheory.Automorphic.HarishChandra
