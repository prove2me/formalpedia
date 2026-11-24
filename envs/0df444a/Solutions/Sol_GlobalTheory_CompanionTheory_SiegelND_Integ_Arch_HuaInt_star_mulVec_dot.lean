-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.star_mulVec_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:00:06.506134+00:00
-- url     : https://prove2.me/submissions/e3f3dfc7-ec5d-41a3-b40e-9ffdc852583e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DetWBlockMatrixFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_quad_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open MeasureTheory Matrix
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
theorem _root_.solution {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (v : Fin n → ℂ) :
    star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v =
      ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) - Complex.I * ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) := by
  rw [quad_real hb, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have hH : (1 + Complex.I • b)ᴴ = 1 - Complex.I • b := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hb.eq, sub_eq_add_neg]
  rw [hH, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  congr 1
  simp [dotProduct, Complex.normSq_eq_conj_mul_self]
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
