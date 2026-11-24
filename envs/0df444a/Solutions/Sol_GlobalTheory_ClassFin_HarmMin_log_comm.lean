-- Prove2me | solution 1 for GlobalTheory.ClassFin.HarmMin.log_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:51.880277+00:00
-- url     : https://prove2.me/submissions/bb2f14a4-8e3c-44be-b0d4-ba58d6eb9d5d

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
theorem _root_.solution {H A : Matrix ι ι ℂ} (h : IsLog H A) : A * H = H * A := by
  obtain ⟨U, d, hU, rfl, rfl⟩ := h
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.1 hU
  have e : ∀ Z : Matrix ι ι ℂ, Uᴴ * (U * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, hU', Matrix.one_mul]
  simp only [Matrix.mul_assoc, e]
  congr 1
  simp only [← Matrix.mul_assoc, diagonal_mul_diagonal]
  congr 2
  ext i
  ring
end GlobalTheory.ClassFin.HarmMin
