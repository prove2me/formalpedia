-- Prove2me | solution 1 for GroundTheory.GroupCoh.nsmul_eq_zero_indShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:25:32.844802+00:00
-- url     : https://prove2.me/submissions/b7985f5f-0816-4fe6-ab0a-544bb39aa5b3

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
import Theorems.Thm_GroundTheory_GroupCoh_nsmul_eq_zero_of_injective
import Theorems.Thm_GroundTheory_GroupCoh_nsmul_eq_zero_coind

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
open CategoryTheory Limits Rep groupHomology
universe u
variable {k G : Type u} [CommRing k] [Group G]
namespace GroundTheory.GroupCoh
theorem _root_.solution [Fintype G] (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0) :
    ∀ y : indShift M, n • y = 0 := by
  classical
  let e := indCoindIso (G := G) (res (⊥ : Subgroup G).subtype M)
  have he : Function.Injective e.hom.hom := (Rep.mono_iff_injective e.hom).1 inferInstance
  have h₂ := nsmul_eq_zero_of_injective e.hom he (nsmul_eq_zero_coind M hM)
  exact nsmul_eq_zero_of_injective (indSES.obj M).f
    ((Rep.mono_iff_injective _).1 (indSES_shortExact M).mono_f) h₂
end GroundTheory.GroupCoh
