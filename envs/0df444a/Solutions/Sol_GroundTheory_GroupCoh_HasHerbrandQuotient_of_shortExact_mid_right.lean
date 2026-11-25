-- Prove2me | solution 1 for GroundTheory.GroupCoh.HasHerbrandQuotient.of_shortExact_mid_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:51.862964+00:00
-- url     : https://prove2.me/submissions/c6d3d077-5f28-4ba6-afa2-720aedf7cbe4

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_finite_of_exact
import Theorems.Thm_GroundTheory_GroupCoh_range_connecting

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
namespace HasHerbrandQuotient
theorem _root_.solution (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (hB : HasHerbrandQuotient fB gB) (hC : HasHerbrandQuotient fC gC) :
    HasHerbrandQuotient fA gA := by
  have := hB.1; have := hB.2; have := hC.1; have := hC.2
  exact ⟨finite_of_exact (connecting hi hp hex hgi hfi hgp hfp hgfB hfgB) (KerModRange.map i hfi hgi)
      (range_connecting hi hp hex hgi hfi hgp hfp hgfB hfgB).symm,
    finite_of_exact (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB) (KerModRange.map i hgi hfi)
      (range_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).symm⟩
end HasHerbrandQuotient
end GroundTheory.GroupCoh
