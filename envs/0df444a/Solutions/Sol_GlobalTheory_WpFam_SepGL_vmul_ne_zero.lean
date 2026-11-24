-- Prove2me | solution 1 for GlobalTheory.WpFam.SepGL.vmul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:17:25.660285+00:00
-- url     : https://prove2.me/submissions/6d9be19f-d80f-473a-a16a-9086d59491d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfWeierstrassPDerivWeierstrassPTorsionEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VmulNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.SepGL
namespace GlobalTheory.WpFam.SepGL
theorem _root_.solution {N : ℕ} (x : Fin 2 → ZMod N) (hx : x ≠ 0) (α : GL (Fin 2) (ZMod N)) :
    vmul x α ≠ 0 := by
  intro h
  apply hx
  have h2 : (x ᵥ* (α : Matrix (Fin 2) (Fin 2) (ZMod N))) ᵥ*
      ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  unfold vmul at h
  rw [← h2, h, Matrix.zero_vecMul]
end GlobalTheory.WpFam.SepGL
