-- Prove2me | solution 1 for GlobalTheory.UnitWitt.exists_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:25:59.272858+00:00
-- url     : https://prove2.me/submissions/974f8910-1dd6-4b9e-af61-d388979596cb

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
import Theorems.Thm_GlobalTheory_UnitWitt_refl_mem
import Theorems.Thm_GlobalTheory_UnitWitt_refl_mulVec
import Theorems.Thm_GlobalTheory_UnitWitt_star_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitWitt
variable {E : Type} [Field E] [StarRing E] {r : ℕ}
namespace GlobalTheory.UnitWitt
theorem _root_.solution (u v : Fin r → E) (hc : star u ⬝ᵥ u = star v ⬝ᵥ v) (ha : star (u - v) ⬝ᵥ u ≠ 0) :
    ∃ g : unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  have hN : star (u - v) ⬝ᵥ (u - v) = star (u - v) ⬝ᵥ u + star (star (u - v) ⬝ᵥ u) := by
    rw [star_dot]
    simp only [star_sub, sub_dotProduct, dotProduct_sub]
    rw [← hc]
    ring
  refine ⟨⟨_, refl_mem (u - v) _ ha hN⟩, ?_⟩
  show (1 - (star (u - v) ⬝ᵥ u)⁻¹ • vecMulVec (u - v) (star (u - v))) *ᵥ u = v
  rw [refl_mulVec (u - v) u _ rfl ha]
  abel
end GlobalTheory.UnitWitt
