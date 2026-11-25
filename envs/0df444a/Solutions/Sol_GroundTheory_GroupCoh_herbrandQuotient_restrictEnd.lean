-- Prove2me | solution 1 for GroundTheory.GroupCoh.herbrandQuotient_restrictEnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:26.814358+00:00
-- url     : https://prove2.me/submissions/75ad1d44-13d7-435f-9862-7985e67459c5

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_herbrandQuotient_eq_of_injective_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
namespace GroundTheory.GroupCoh
theorem _root_.solution {f g : B →+ B} (S : AddSubgroup B) [S.FiniteIndex]
    (hfS : ∀ x ∈ S, f x ∈ S) (hgS : ∀ x ∈ S, g x ∈ S) (hfg : ∀ b, f (g b) = 0)
    (hgf : ∀ b, g (f b) = 0) :
    herbrandQuotient (restrictEnd f S hfS) (restrictEnd g S hgS) = herbrandQuotient f g := by
  have : Finite (B ⧸ S.subtype.range) := by rw [AddSubgroup.range_subtype]; infer_instance
  exact herbrandQuotient_eq_of_injective_of_finite S.subtype_injective (fun _ => rfl)
    (fun _ => rfl) hfg hgf
end GroundTheory.GroupCoh
