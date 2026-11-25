-- Prove2me | solution 1 for GroundTheory.GroupCoh.counit_indCoindIso_inv_coindConst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:04:06.145448+00:00
-- url     : https://prove2.me/submissions/8e78e154-129a-4152-9f79-a6a3280d0741

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
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
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]
omit [Fintype S]
namespace GroundTheory.GroupCoh
theorem _root_.solution [DecidableRel (QuotientGroup.rightRel S)]
    (A : Rep.{u} k G) (y : (res S.subtype A).ρ.invariants) :
    ((Rep.indResAdjunction.{u} k S.subtype).counit.app A).hom
      ((indCoindIso (res S.subtype A)).inv.hom (coindConst S (res S.subtype A) y)) =
      transferSum S y := by
  classical
  change ((Rep.indResAdjunction k S.subtype).counit.app A).hom
      (coindToInd (res S.subtype A) (coindConst S (res S.subtype A) y)) = _
  rw [coindToInd_apply, map_sum, transferSum]
  refine (Finset.sum_congr (by convert rfl) fun x _ => ?_ : _ = ∑ x : Quotient (QuotientGroup.rightRel S),
    cosetSMul S y (QuotientGroup.quotientRightRelEquivQuotientLeftRel S x)).trans (Equiv.sum_comp _ _)
  induction x using Quotient.inductionOn with
  | h g =>
    rw [Quotient.liftOn_mk, indResAdjunction_counit_app_hom_mk]
    rfl
end GroundTheory.GroupCoh
