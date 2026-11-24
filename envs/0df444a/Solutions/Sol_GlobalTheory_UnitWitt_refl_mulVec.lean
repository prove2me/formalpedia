-- Prove2me | solution 1 for GlobalTheory.UnitWitt.refl_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:15:32.500929+00:00
-- url     : https://prove2.me/submissions/58cb12f6-7f68-47c6-9e8c-dcde22af2b10

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
import Theorems.Thm_GlobalTheory_UnitWitt_vecMulVec_mulVec_eq

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
theorem _root_.solution (w u : Fin r → E) (a : E) (ha : star w ⬝ᵥ u = a) (ha0 : a ≠ 0) :
    (1 - a⁻¹ • vecMulVec w (star w)) *ᵥ u = u - w := by
  have h1 : (a⁻¹ • vecMulVec w (star w)) *ᵥ u = a⁻¹ • (vecMulVec w (star w) *ᵥ u) := by
    ext i; simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [sub_mulVec, one_mulVec, h1, vecMulVec_mulVec_eq, ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
end GlobalTheory.UnitWitt
