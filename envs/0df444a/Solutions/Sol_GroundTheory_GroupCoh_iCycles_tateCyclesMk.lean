-- Prove2me | solution 1 for GroundTheory.GroupCoh.iCycles_tateCyclesMk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:59:59.871963+00:00
-- url     : https://prove2.me/submissions/7c77fc66-ed46-4009-b9f0-63f3190020f5

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (A : Rep k G) (i : ℤ) (x : (tateComplex A).X i)
    (hx : ((tateComplex A).d i (i + 1)).hom x = 0) :
    ((tateComplex A).iCycles i).hom (tateCyclesMk A i x hx) = x :=
  (tateComplex A).i_cyclesMk x (i + 1) (by simp) hx
end GroundTheory.GroupCoh
