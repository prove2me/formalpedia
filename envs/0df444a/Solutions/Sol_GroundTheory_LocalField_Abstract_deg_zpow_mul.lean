-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.deg_zpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:07.221344+00:00
-- url     : https://prove2.me/submissions/91405d4d-89f4-40b0-96bc-5318982315c1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {N : ℕ} (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) (k : ℤ) {j : G}
    (hj : j ∈ L ⊓ d.ker) :
    Multiplicative.toAdd (d (σ ^ k * j)) = ((k * N : ℤ) : ℤ̂) := by
  rw [map_mul, map_zpow, hdσ, (MonoidHom.mem_ker).1 hj.2, mul_one, ← ofAdd_zsmul, toAdd_ofAdd,
    zsmul_eq_mul]
  push_cast
  ring
end GroundTheory.LocalField.Abstract
