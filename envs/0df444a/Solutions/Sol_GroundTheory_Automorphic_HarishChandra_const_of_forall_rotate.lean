-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.const_of_forall_rotate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:35:25.177975+00:00
-- url     : https://prove2.me/submissions/6862ba70-d0fd-47de-aeaf-3662672d81b3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction


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
theorem _root_.solution {k : ℕ} {i : Fin (k + 1) → Fin n}
    (h : ∀ t, i t = i (finRotate (k + 1) t)) (t : Fin (k + 1)) : i t = i 0 := by
  induction t using Fin.induction with
  | zero => rfl
  | succ t ih =>
    have := h (Fin.castSucc t)
    rw [finRotate_apply, Fin.coeSucc_eq_succ] at this
    rw [← this, ih]
end GroundTheory.Automorphic.HarishChandra
