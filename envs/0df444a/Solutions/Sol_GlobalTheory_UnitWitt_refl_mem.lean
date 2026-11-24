-- Prove2me | solution 1 for GlobalTheory.UnitWitt.refl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:49.105522+00:00
-- url     : https://prove2.me/submissions/7ea85146-ec71-4408-8aea-1137b2c8da80

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
import Theorems.Thm_GlobalTheory_UnitWitt_conjTranspose_vecMulVec_self
import Theorems.Thm_GlobalTheory_UnitWitt_vecMulVec_self_mul

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
theorem _root_.solution (w : Fin r → E) (a : E) (ha : a ≠ 0) (hN : star w ⬝ᵥ w = a + star a) :
    (1 - a⁻¹ • vecMulVec w (star w)) ∈ unitaryGroup (Fin r) E := by
  rw [mem_unitaryGroup_iff']
  have hs : star (1 - a⁻¹ • vecMulVec w (star w)) = 1 - (star a)⁻¹ • vecMulVec w (star w) := by
    rw [star_sub, star_one, star_smul, star_inv₀]
    congr 2
    exact conjTranspose_vecMulVec_self w
  have ha' : star a ≠ 0 := by simpa using ha
  rw [hs]
  have key : (star a)⁻¹ + a⁻¹ - (star a)⁻¹ * a⁻¹ * (star w ⬝ᵥ w) = 0 := by
    rw [hN]; field_simp; ring
  calc (1 - (star a)⁻¹ • vecMulVec w (star w)) * (1 - a⁻¹ • vecMulVec w (star w))
      = 1 - ((star a)⁻¹ + a⁻¹ - (star a)⁻¹ * a⁻¹ * (star w ⬝ᵥ w)) • vecMulVec w (star w) := by
        rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm, vecMulVec_self_mul,
          smul_smul, sub_smul, add_smul]
        abel
    _ = 1 := by rw [key, zero_smul, sub_zero]
end GlobalTheory.UnitWitt
