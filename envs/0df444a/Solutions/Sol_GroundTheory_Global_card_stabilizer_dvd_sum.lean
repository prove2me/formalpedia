-- Prove2me | solution 1 for GroundTheory.Global.card_stabilizer_dvd_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:24.222078+00:00
-- url     : https://prove2.me/submissions/d7dbaf63-8f1f-403a-bd10-07c38ef14f56

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Theorems.Thm_GroundTheory_Global_card_stabilizer_dvd_card_filter

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
theorem _root_.solution [Finite X] (F : X → ℤ) (p : X) :
    (Nat.card (stabilizer G p) : ℤ) ∣ ∑ g : G, F (g • p) := by
  classical
  have := Fintype.ofFinite X
  rw [← Finset.sum_fiberwise Finset.univ (fun g : G => g • p) (fun g => F (g • p))]
  refine Finset.dvd_sum fun y _ => ?_
  rw [Finset.sum_congr rfl fun g hg => by rw [(Finset.mem_filter.1 hg).2], Finset.sum_const,
    nsmul_eq_mul]
  exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 (card_stabilizer_dvd_card_filter p y)) _
end GroundTheory.Global
