-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.translate_neg_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:13:02.871191+00:00
-- url     : https://prove2.me/submissions/88e1bba4-e0c2-45ab-bc1d-235875eeaade

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Injective
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eval_translate


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
theorem _root_.solution (c : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    translate (-c) (translate c p) = p := by
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_translate, eval_translate, neg_add_cancel_right]
end GroundTheory.Automorphic.HarishChandra
