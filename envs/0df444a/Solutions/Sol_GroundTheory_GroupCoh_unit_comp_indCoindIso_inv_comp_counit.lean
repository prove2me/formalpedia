-- Prove2me | solution 1 for GroundTheory.GroupCoh.unit_comp_indCoindIso_inv_comp_counit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:04:08.797382+00:00
-- url     : https://prove2.me/submissions/a1f4d418-8552-49ad-91ed-333cdda6da37

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Theorems.Thm_GroundTheory_GroupCoh_indResAdjunction_counit_app_hom_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (S : Subgroup G) [S.FiniteIndex] [DecidableRel (QuotientGroup.rightRel S)]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} k G) :
    (resCoindAdjunction.{u, u} k S.subtype).unit.app A ≫ (indCoindIso (res S.subtype A)).inv ≫
      (indResAdjunction.{u} k S.subtype).counit.app A = S.index • 𝟙 A := by
  ext a
  change ((indResAdjunction k S.subtype).counit.app A).hom
      (coindToInd (res S.subtype A) (((resCoindAdjunction.{u, u} k S.subtype).unit.app A).hom a)) =
    S.index • a
  rw [coindToInd_apply, map_sum]
  refine (Finset.sum_congr rfl (g := fun _ => a) fun x _ => ?_).trans ?_
  · induction x using Quotient.inductionOn with
    | h g =>
      rw [Quotient.liftOn_mk, indResAdjunction_counit_app_hom_mk]
      change A.ρ g⁻¹ (A.ρ g a) = a
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · rw [Finset.sum_const, Finset.card_univ]
    congr 1
    rw [← Nat.card_eq_fintype_card,
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]
    rfl
end GroundTheory.GroupCoh
