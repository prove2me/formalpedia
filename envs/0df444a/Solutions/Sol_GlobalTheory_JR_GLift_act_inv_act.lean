-- Prove2me | solution 1 for GlobalTheory.JR.GLift.act_inv_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:58:38.034818+00:00
-- url     : https://prove2.me/submissions/e058bfa4-a25a-40d6-8e69-88b1ffb1271a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockGlBorderedConjugationActionI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift
namespace GlobalTheory.JR.GLift
theorem _root_.solution {F : Type} [Field F] {n : ℕ} (k : GL (Fin n) F) (Y : Gl n F) :
    act k⁻¹ (act k Y) = Y := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [act, inv_inv, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((k : Matrix (Fin n) (Fin n) F) * A *
        ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * (k : Matrix (Fin n) (Fin n) F) = A
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  · show (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (k : Matrix (Fin n) (Fin n) F)) *ᵥ b = b
    rw [Units.inv_mul, Matrix.one_mulVec]
  · show c ᵥ* (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (k : Matrix (Fin n) (Fin n) F)) = c
    rw [Units.inv_mul, Matrix.vecMul_one]
end GlobalTheory.JR.GLift
