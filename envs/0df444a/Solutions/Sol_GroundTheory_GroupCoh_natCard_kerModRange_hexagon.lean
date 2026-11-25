-- Prove2me | solution 1 for GroundTheory.GroupCoh.natCard_kerModRange_hexagon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:24.208531+00:00
-- url     : https://prove2.me/submissions/029b2a7f-3693-47a6-a7b6-9192fc112e09

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_natCard_hexagon
import Theorems.Thm_GroundTheory_GroupCoh_KerModRange_ker_map_eq_range_map
import Theorems.Thm_GroundTheory_GroupCoh_ker_connecting
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
theorem _root_.solution (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    Nat.card (KerModRange fA gA) * Nat.card (KerModRange fC gC) * Nat.card (KerModRange gB fB) =
      Nat.card (KerModRange fB gB) * Nat.card (KerModRange gA fA) *
        Nat.card (KerModRange gC fC) :=
  natCard_hexagon (KerModRange.map i hfi hgi) (KerModRange.map p hfp hgp)
    (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB) (KerModRange.map i hgi hfi)
    (KerModRange.map p hgp hfp) (connecting hi hp hex hgi hfi hgp hfp hgfB hfgB)
    (range_connecting hi hp hex hgi hfi hgp hfp hgfB hfgB).symm
    (KerModRange.ker_map_eq_range_map hi hp hex hfi hgi hfp hgp hfgB)
    (ker_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB)
    (range_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).symm
    (KerModRange.ker_map_eq_range_map hi hp hex hgi hfi hgp hfp hgfB)
    (ker_connecting hi hp hex hgi hfi hgp hfp hgfB hfgB)
end GroundTheory.GroupCoh
