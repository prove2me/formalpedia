-- Prove2me | solution 1 for GroundTheory.GroupCoh.HasHerbrandQuotient.of_shortExact_left_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:00.606547+00:00
-- url     : https://prove2.me/submissions/b9bc8f82-8a28-4c31-bc6d-631ce4f7d368

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_finite_of_exact
import Theorems.Thm_GroundTheory_GroupCoh_KerModRange_ker_map_eq_range_map

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
    (hA : HasHerbrandQuotient fA gA) (hC : HasHerbrandQuotient fC gC) :
    HasHerbrandQuotient fB gB := by
  have := hA.1; have := hA.2; have := hC.1; have := hC.2
  exact ⟨finite_of_exact (KerModRange.map i hfi hgi) (KerModRange.map p hfp hgp)
      (KerModRange.ker_map_eq_range_map hi hp hex hfi hgi hfp hgp hfgB),
    finite_of_exact (KerModRange.map i hgi hfi) (KerModRange.map p hgp hfp)
      (KerModRange.ker_map_eq_range_map hi hp hex hgi hfi hgp hfp hgfB)⟩
end HasHerbrandQuotient
end GroundTheory.GroupCoh
