-- Prove2me | solution 1 for GroundTheory.GroupCoh.hasHerbrandQuotient_restrictEnd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:16.599883+00:00
-- url     : https://prove2.me/submissions/8cb8a130-8fa6-4e85-b49c-a1b7fcf824f6

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_hasHerbrandQuotient_iff_of_injective_of_finite

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
    HasHerbrandQuotient (restrictEnd f S hfS) (restrictEnd g S hgS) ↔ HasHerbrandQuotient f g := by
  have : Finite (B ⧸ S.subtype.range) := by rw [AddSubgroup.range_subtype]; infer_instance
  exact hasHerbrandQuotient_iff_of_injective_of_finite S.subtype_injective (fun _ => rfl)
    (fun _ => rfl) hfg hgf
end GroundTheory.GroupCoh
