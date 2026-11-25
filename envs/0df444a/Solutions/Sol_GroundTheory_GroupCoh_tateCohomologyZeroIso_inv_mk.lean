-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateCohomologyZeroIso_inv_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:47:59.778091+00:00
-- url     : https://prove2.me/submissions/5bd8e932-0d2c-47e7-8a74-b0583f0403c8

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateCohomologyZeroIso_hom_homology__94582ad74da4

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
open CategoryTheory Limits Representation groupCohomology groupHomology
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} R G) (z : (tateComplex M).cycles 0)
    (x : M.ρ.invariants) (hx : (cochainsIso₀ M).inv.hom x = ((tateComplex M).iCycles 0).hom z) :
    ((tateCohomologyZeroIso R G).app M).inv.hom (Submodule.Quotient.mk x) =
      ((tateComplex M).homologyπ 0).hom z := by
  exact (congrArg (fun w => ((tateCohomologyZeroIso R G).app M).inv.hom w)
    (tateCohomologyZeroIso_hom_homologyπ M z x hx)).symm.trans
      (iso_inv_hom_apply ((tateCohomologyZeroIso R G).app M) _)
end GroundTheory.GroupCoh
