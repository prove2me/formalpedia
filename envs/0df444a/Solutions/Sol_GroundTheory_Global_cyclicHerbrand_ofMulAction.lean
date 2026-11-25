-- Prove2me | solution 1 for GroundTheory.Global.cyclicHerbrand_ofMulAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:25:18.17566+00:00
-- url     : https://prove2.me/submissions/beffc6bc-4e53-459a-988a-f1c5d0b2fa82

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Theorems.Thm_GroundTheory_Global_natCard_kerModRange_normHom_ofMulAction
import Theorems.Thm_GroundTheory_Global_natCard_kerModRange_cycSub_ofMulAction

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
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] {σ : G}
namespace GroundTheory.Global
theorem _root_.solution [Fintype (orbitRel.Quotient G X)]
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cyclicHerbrand (Representation.ofMulAction ℤ G X) σ =
      ∏ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G (Quotient.out ω)) : ℚ) := by
  rw [cyclicHerbrand, herbrandQuotient, natCard_kerModRange_cycSub_ofMulAction hσ,
    natCard_kerModRange_normHom_ofMulAction hσ, Nat.cast_one, div_one, Nat.cast_prod]
end GroundTheory.Global
