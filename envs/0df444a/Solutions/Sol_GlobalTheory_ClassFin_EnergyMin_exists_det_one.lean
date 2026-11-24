-- Prove2me | solution 1 for GlobalTheory.ClassFin.EnergyMin.exists_det_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:45.966972+00:00
-- url     : https://prove2.me/submissions/a367a5b6-40de-4bb3-80ad-f215e9301c32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EntriesBoundedOfConjSpanningBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsClosedIsHermitianLogOfPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MatrixEntriesBoundedOfHermitianLogTraceSqLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsHermitianLogOfPosDefGramStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEnergyMin

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
open GlobalTheory GlobalTheory.ClassFin GlobalTheory.ClassFin.EnergyMin
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ClassFin.EnergyMin
theorem _root_.solution (P : Matrix ι ι ℂ) (hP : IsUnit P.det) :
    ∃ Q : Matrix ι ι ℂ, Q.det = 1 ∧ ∀ x : Matrix ι ι ℂ, Q * x * Q⁻¹ = P * x * P⁻¹ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨P, Matrix.det_isEmpty, fun _ => rfl⟩
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq P.det (Fintype.card_pos (α := ι))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow Fintype.card_ne_zero] at hc
    exact hP.ne_zero hc.symm
  refine ⟨c⁻¹ • P, ?_, fun x => ?_⟩
  · rw [Matrix.det_smul, ← hc, ← mul_pow, inv_mul_cancel₀ hc0, one_pow]
  · have : (c⁻¹ • P)⁻¹ = c • P⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.mul_nonsing_inv _ hP]
    rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
end GlobalTheory.ClassFin.EnergyMin
