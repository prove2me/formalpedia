-- Prove2me | solution 1 for GroundTheory.GroupCoh.card_smul_tateCohomology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:07:14.179882+00:00
-- url     : https://prove2.me/submissions/4aa5896a-a19e-4616-aa28-1fae5e5db6be

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_Annihilation
import Theorems.Thm_GroundTheory_GroupCoh_card_smul_tateCohomology_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
private theorem card_smul_succ {n : ℤ}
    (h : ∀ (A : Rep.{u} R G) (x : tateCohomology A n), Fintype.card G • x = 0)
    (A : Rep.{u} R G) (x : tateCohomology A (n + 1)) : Fintype.card G • x = 0 := by
  let e := (coindShiftIso A n).toLinearEquiv
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [← map_nsmul, h, map_zero]
private theorem card_smul_pred {n : ℤ}
    (h : ∀ (A : Rep.{u} R G) (x : tateCohomology A (n + 1)), Fintype.card G • x = 0)
    (A : Rep.{u} R G) (x : tateCohomology A n) : Fintype.card G • x = 0 := by
  let e := (indShiftIso A n).toLinearEquiv
  apply e.injective
  rw [map_nsmul, map_zero, h]
end GroundTheory.GroupCoh
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep.{u} R G) (n : ℤ) (x : tateCohomology A n) :
    Fintype.card G • x = 0 := by
  induction n using Int.induction_on generalizing A with
  | zero => exact card_smul_tateCohomology_zero A x
  | succ n ih => exact card_smul_succ (fun A x => ih A x) A x
  | pred n ih =>
    refine card_smul_pred ?_ A x
    rw [sub_add_cancel]
    exact ih
end GroundTheory.GroupCoh
