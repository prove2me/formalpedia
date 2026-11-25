-- Prove2me | solution 1 for GroundTheory.LocalField.cycHerbrand_ofMulDistribMulAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:35:03.297014+00:00
-- url     : https://prove2.me/submissions/6ddae582-b484-4adf-a69d-d4b4e61c6ae0

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Theorems.Thm_GroundTheory_LocalField_natCard_tateZero_eq
import Theorems.Thm_GroundTheory_LocalField_natCard_tateNegOne_eq
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open GroundTheory.GroupCoh GroundTheory.Global
variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {σ : G}
namespace GroundTheory.LocalField
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (Representation.ofMulDistribMulAction G M) σ =
      (Nat.card (TateZero G M) : ℚ) / Nat.card (TateNegOne G M) := by
  rw [cycHerbrand_eq, natCard_tateZero_eq hσ, natCard_tateNegOne_eq hσ]
end GroundTheory.LocalField
