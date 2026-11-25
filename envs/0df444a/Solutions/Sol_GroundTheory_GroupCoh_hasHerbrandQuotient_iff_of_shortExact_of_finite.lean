-- Prove2me | solution 1 for GroundTheory.GroupCoh.hasHerbrandQuotient_iff_of_shortExact_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:22.741307+00:00
-- url     : https://prove2.me/submissions/7ba2bfbe-af03-4035-bbc6-669fea8a46d8

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_hasHerbrandQuotient_of_finite
import Theorems.Thm_GroundTheory_GroupCoh_HasHerbrandQuotient_of_shortExact_left_right
import Theorems.Thm_GroundTheory_GroupCoh_HasHerbrandQuotient_of_shortExact_mid_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  {fA gA : A →+ A} {fB gB : B →+ B} {fC gC : C →+ C} {i : A →+ B} {p : B →+ C}
namespace GroundTheory.GroupCoh
theorem _root_.solution [Finite C] (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    HasHerbrandQuotient fA gA ↔ HasHerbrandQuotient fB gB :=
  ⟨fun hA => HasHerbrandQuotient.of_shortExact_left_right hi hp hex hfi hgi hfp hgp hfgB hgfB hA
      (hasHerbrandQuotient_of_finite _ _),
    fun hB => HasHerbrandQuotient.of_shortExact_mid_right hi hp hex hfi hgi hfp hgp hfgB hgfB hB
      (hasHerbrandQuotient_of_finite _ _)⟩
end GroundTheory.GroupCoh
