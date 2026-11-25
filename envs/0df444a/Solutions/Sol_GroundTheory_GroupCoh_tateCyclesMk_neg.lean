-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateCyclesMk_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:28:01.724662+00:00
-- url     : https://prove2.me/submissions/a0abf676-a3bd-4cf4-8194-8f892c4d760b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Theorems.Thm_GroundTheory_GroupCoh_iCycles_tateCyclesMk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep k G) (i : ℤ) (x : (tateComplex A).X i)
    (hx : ((tateComplex A).d i (i + 1)).hom x = 0) (hx' : ((tateComplex A).d i (i + 1)).hom (-x) = 0) :
    tateCyclesMk A i (-x) hx' = -tateCyclesMk A i x hx := by
  apply (ModuleCat.mono_iff_injective ((tateComplex A).iCycles i)).1 inferInstance
  rw [map_neg, iCycles_tateCyclesMk, iCycles_tateCyclesMk]
end GroundTheory.GroupCoh
