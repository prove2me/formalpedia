-- Prove2me | solution 1 for GroundTheory.GroupCoh.exists_tateComplex_cycles_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:23.741813+00:00
-- url     : https://prove2.me/submissions/be981b5c-8ecc-4783-a60a-4985a6222a9a

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Theorems.Thm_GroundTheory_GroupCoh_exists_cycles_of_moduleLeftHomologyData


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
theorem _root_.solution (M : Rep.{u} R G) (x : M.ρ.invariants) :
    ∃ z : (tateComplex M).cycles 0,
      ((tateComplex M).iCycles 0).hom z = (cochainsIso₀ M).inv.hom x :=
  exists_cycles_of_moduleLeftHomologyData (tateComplex M) (-1) 0 1 (by simp) (by simp)
    M.ρ.invariants (tateZeroι M) (tateZeroι_injective M) (tateZeroι_range M)
    (normRangeInvariants M) (tateZero_mem_iff M) x
end GroundTheory.GroupCoh
