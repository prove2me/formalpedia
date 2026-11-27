-- Prove2me | solution 1 for GroundTheory.GroupCoh.map_braiding_cupH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:11.723934+00:00
-- url     : https://prove2.me/submissions/f76b6b25-5ec3-43f6-9d9a-896b113f4c78

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse
import Definitions.Def_GroundTheory_TateCohomology_CupGraded
import Theorems.Thm_GroundTheory_GroupCoh_cupH_eq_neg_one_pow_smul_map_braiding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (h : p + q = n) (h' : q + p = n) (x : groupCohomology A p)
    (y : groupCohomology B q) :
    map (MonoidHom.id G) (β_ A B).hom n (cupH h x y) = (-1 : k) ^ (p * q) • cupH h' y x := by
  rw [cupH_eq_neg_one_pow_smul_map_braiding h' h y x, smul_smul, ← pow_add, mul_comm q p,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
end GroundTheory.GroupCoh
