-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_mulPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:14.909816+00:00
-- url     : https://prove2.me/submissions/3aee5a53-dbe9-4c18-86b5-ce4f94f260b6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTateNegOneOrbitEquivSymmMk
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleHerbrand_Product
import Theorems.Thm_GroundTheory_Global_cycHerbrand_congr
import Theorems.Thm_GroundTheory_Global_cycHerbrand_pi


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
variable {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)] [∀ i, MulDistribMulAction G (M i)]
  [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution [Fintype ι] (σ : G) :
    cycHerbrand (Representation.ofMulDistribMulAction G (∀ i, M i)) σ =
      ∏ i, cycHerbrand (Representation.ofMulDistribMulAction G (M i)) σ := by
  rw [cycHerbrand_congr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ, cycHerbrand_pi]
end GroundTheory.Global
