-- Prove2me | solution 1 for GroundTheory.GroupCoh.connecting_connLeft
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:36.930544+00:00
-- url     : https://prove2.me/submissions/45aa6971-1b66-4af6-b15b-c3370edc4ca1

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract

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
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (s : connDomain fB i) :
    connecting hi hp hex hfi hgi hfp hgp hfgB hgfB (connLeft hex hfp s) =
      (connRight hi hgi hgfB s : KerModRange gA fA) := by
  have : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (connLeft_surjective hp hex hfp)).symm (connLeft hex hfp s : KerModRange fC gC) =
      (QuotientAddGroup.mk s : connDomain fB i ⧸ (connLeft hex hfp :
        connDomain fB i →+ KerModRange fC gC).ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  rw [connecting, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, this,
    QuotientAddGroup.lift_mk]
end GroundTheory.GroupCoh
