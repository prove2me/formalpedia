-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_mulProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:17.81322+00:00
-- url     : https://prove2.me/submissions/35fe79cc-1e86-41be-b1d0-3da717702555

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTateNegOneOrbitEquivSymmMk
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleHerbrand_Product
import Theorems.Thm_GroundTheory_Global_cycHerbrand_prod_eq_mul
import Theorems.Thm_GroundTheory_Global_cycHerbrand_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
noncomputable section
variable {G : Type*} [Group G]
variable (M N : Type*) [CommGroup M] [CommGroup N] [MulDistribMulAction G M]
  [MulDistribMulAction G N] [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution (σ : G) :
    cycHerbrand (Representation.ofMulDistribMulAction G (M × N)) σ =
      cycHerbrand (Representation.ofMulDistribMulAction G M) σ *
        cycHerbrand (Representation.ofMulDistribMulAction G N) σ := by
  rw [cycHerbrand_congr (ρ' := (Representation.ofMulDistribMulAction G M).prod
      (Representation.ofMulDistribMulAction G N)) (additiveProdEquiv M N) (fun _ _ ↦ rfl) σ,
    cycHerbrand_prod_eq_mul]
end GroundTheory.Global
