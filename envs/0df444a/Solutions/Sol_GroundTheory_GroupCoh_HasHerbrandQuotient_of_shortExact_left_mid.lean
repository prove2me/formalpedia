-- Prove2me | solution 1 for GroundTheory.GroupCoh.HasHerbrandQuotient.of_shortExact_left_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:30.385328+00:00
-- url     : https://prove2.me/submissions/26ef7205-770c-427f-9da3-160860cbf37b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_finite_of_exact
import Theorems.Thm_GroundTheory_GroupCoh_ker_connecting

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
    (hA : HasHerbrandQuotient fA gA) (hB : HasHerbrandQuotient fB gB) :
    HasHerbrandQuotient fC gC := by
  have := hA.1; have := hA.2; have := hB.1; have := hB.2
  exact ⟨finite_of_exact (KerModRange.map p hfp hgp) (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB)
      (ker_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB),
    finite_of_exact (KerModRange.map p hgp hfp) (connecting hi hp hex hgi hfi hgp hfp hgfB hfgB)
      (ker_connecting hi hp hex hgi hfi hgp hfp hgfB hfgB)⟩
end HasHerbrandQuotient
end GroundTheory.GroupCoh
