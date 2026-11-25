-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateCyclesMk_iCycles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:14:56.295984+00:00
-- url     : https://prove2.me/submissions/90254a3a-3930-4eda-82a8-fdfd8cce031a

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
theorem _root_.solution (A : Rep k G) (i : ℤ) (z : (tateComplex A).cycles i)
    (hz : ((tateComplex A).d i (i + 1)).hom (((tateComplex A).iCycles i).hom z) = 0) :
    tateCyclesMk A i (((tateComplex A).iCycles i).hom z) hz = z := by
  apply (ModuleCat.mono_iff_injective ((tateComplex A).iCycles i)).1 inferInstance
  rw [iCycles_tateCyclesMk]
end GroundTheory.GroupCoh
