-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rep_center_apply_of_highestWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:55.257137+00:00
-- url     : https://prove2.me/submissions/ce1bd3d8-1bc5-4a58-a9fa-df269d673b6c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Consequences
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eval_harishChandraHom
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_centralizerT_of_mem_center
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rep_apply_of_highestWeight


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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : U n →ₐ[ℂ] Module.End ℂ V) {v : V} (lam : Fin n → ℂ)
    (hup : ∀ a, IsUpper a → φ (e a) v = 0) (hH : ∀ k, φ (e (k, k)) v = lam k • v)
    (z : Subalgebra.center ℂ (U n)) :
    φ z v = eval (lam + rhoVec n) (harishChandraHom z) • v := by
  rw [rep_apply_of_highestWeight φ lam hup hH
    (commute_e_diag_of_mem (mem_centralizerT_of_mem_center z.2)), eval_harishChandraHom,
    add_sub_cancel_right]
end GroundTheory.Automorphic.HarishChandra
