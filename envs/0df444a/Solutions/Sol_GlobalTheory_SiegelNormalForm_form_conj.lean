-- Prove2me | solution 1 for GlobalTheory.SiegelNormalForm.form_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:09.434372+00:00
-- url     : https://prove2.me/submissions/5085edc0-6c0a-4ae5-92d4-ef1629365956

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.SiegelNormalForm
variable {g : ℕ}
open Complex Matrix Filter Topology
open scoped BigOperators Real
variable {g : ℕ}
namespace GlobalTheory.SiegelNormalForm
namespace _root_.GlobalTheory.SiegelNormalForm
theorem _root_.solution {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    star (z ⬝ᵥ Hm *ᵥ star w) = w ⬝ᵥ Hm *ᵥ star z := by
  rw [← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]
end _root_.GlobalTheory.SiegelNormalForm
end GlobalTheory.SiegelNormalForm
