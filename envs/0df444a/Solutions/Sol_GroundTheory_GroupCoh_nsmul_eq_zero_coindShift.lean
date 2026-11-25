-- Prove2me | solution 1 for GroundTheory.GroupCoh.nsmul_eq_zero_coindShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:26.911256+00:00
-- url     : https://prove2.me/submissions/51818468-4a4f-4bf9-8145-9bbe8afc2c70

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
import Theorems.Thm_GroundTheory_GroupCoh_nsmul_eq_zero_of_surjective
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
theorem _root_.solution (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0) :
    ∀ y : coindShift M, n • y = 0 :=
  nsmul_eq_zero_of_surjective (coindSES.obj M).g
    ((Rep.epi_iff_surjective _).1 (coindSES_shortExact M).epi_g) (nsmul_eq_zero_coind M hM)
end GroundTheory.GroupCoh
