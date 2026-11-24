-- Prove2me | solution 1 for GlobalTheory.ClassFin.HarmMin.trace_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:09.803798+00:00
-- url     : https://prove2.me/submissions/c4f1d06b-ec39-4036-b45d-fcf654776797

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HermitianLogTraceSqFirstVariationBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MulLogEqNegLogMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsHermitianLogOfPosDefGramStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SumHermitianLogGramEqZeroOfEnergyMinimum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin GlobalTheory.ClassFin.HarmMin
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ClassFin.HarmMin
theorem _root_.solution {g g' H H' X : Matrix ι ι ℂ} (hg : g' * g = 1) (hc : (gᴴ * g) * H = H * (gᴴ * g))
    (hi : g * H = -(H' * g)) :
    Matrix.trace (H * (gᴴ * g)⁻¹ * (-X * (gᴴ * g) + gᴴ * X * g + gᴴ * X * g - (gᴴ * g) * X)) =
      -2 * Matrix.trace (H * X) - 2 * Matrix.trace (H' * X) := by
  have hg2 : g * g' = 1 := mul_eq_one_comm.1 hg
  have hg3 : g'ᴴ * gᴴ = 1 := by rw [← conjTranspose_mul, hg2, conjTranspose_one]
  have hA : (g' * g'ᴴ) * (gᴴ * g) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc g'ᴴ, hg3, Matrix.one_mul, hg]
  have hinv : (gᴴ * g)⁻¹ = g' * g'ᴴ := Matrix.inv_eq_left_inv hA
  have hA' : (gᴴ * g) * (g' * g'ᴴ) = 1 := mul_eq_one_comm.1 hA
  rw [hinv]
  have e1 : Matrix.trace (H * (g' * g'ᴴ) * (X * (gᴴ * g))) = Matrix.trace (H * X) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc (gᴴ * g) H, hc,
      Matrix.mul_assoc H, hA', Matrix.mul_one]
  have e2 : Matrix.trace (H * (g' * g'ᴴ) * ((gᴴ * g) * X)) = Matrix.trace (H * X) := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc H, hA, Matrix.mul_one]
  have e3 : Matrix.trace (H * (g' * g'ᴴ) * (gᴴ * X * g)) = - Matrix.trace (H' * X) := by
    have : H * (g' * g'ᴴ) * (gᴴ * X * g) = (H * g' * X) * g := by
      calc _ = H * g' * (g'ᴴ * gᴴ) * X * g := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hg3, Matrix.mul_one]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hi, Matrix.neg_mul,
      Matrix.mul_assoc H', hg2, Matrix.mul_one, Matrix.neg_mul, Matrix.trace_neg]
  rw [Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_add, Matrix.mul_neg, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_neg, e1, e2, e3]
  ring
end GlobalTheory.ClassFin.HarmMin
