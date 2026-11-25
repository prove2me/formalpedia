-- Prove2me | solution 1 for GroundTheory.Global.card_stabilizer_dvd_card_filter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:04.525377+00:00
-- url     : https://prove2.me/submissions/c747fc49-a270-4a6c-bf00-bde6d5f959f9

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Theorems.Thm_GroundTheory_Global_card_filter_smul_eq

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
open GroundTheory.GroupCoh MulAction
variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
variable {G}
variable [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution [DecidableEq X] (p y : X) :
    Nat.card (stabilizer G p) ∣ (Finset.univ.filter fun g : G => g • p = y).card := by
  by_cases hy : y ∈ orbit G p
  · obtain ⟨g₀, rfl⟩ := hy
    rw [card_filter_smul_eq]
  · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun g _ hg => hy ⟨g, hg⟩)]
    exact dvd_zero _
end GroundTheory.Global
