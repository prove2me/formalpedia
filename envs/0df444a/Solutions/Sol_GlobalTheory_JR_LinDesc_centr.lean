-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.centr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:52:03.23082+00:00
-- url     : https://prove2.me/submissions/a1301275-34cf-4981-b51a-589ba19b5663

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitLeftMulMatrixOfCommuteCompanion
import Theorems.Thm_GlobalTheory_JR_LinDesc_exists_leftMul_of_comm
import Theorems.Thm_GlobalTheory_JR_LinDesc_tm_coe


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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (t : GL (Fin r) F), (t : Matrix (Fin r) (Fin r) F) * companion p = companion p * (t : Matrix (Fin r) (Fin r) F) → ∃ t₁ : A.Kˣ, LinDesc.tm A hG t₁ = t := by
  intro F E _ _ _ _ A r τ p hG t ht
  have ht' : ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p =
      companion p * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
    have h1 : ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (t : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (t : Matrix (Fin r) (Fin r) F) * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p
        = ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p *
            ((t : Matrix (Fin r) (Fin r) F) * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) := by
          rw [h2, Matrix.mul_one]
      _ = ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * ((t : Matrix (Fin r) (Fin r) F) * companion p) *
            ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
          rw [ht]; simp only [Matrix.mul_assoc]
      _ = companion p * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨k, hk⟩ := exists_leftMul_of_comm A hG _ ht
  obtain ⟨k', hk'⟩ := exists_leftMul_of_comm A hG _ ht'
  have hinj := Algebra.leftMulMatrix_injective (bas A hG)
  have e1 : k * k' = 1 := by
    apply hinj
    rw [map_mul, map_one, ← hk, ← hk', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : k' * k = 1 := by rw [mul_comm, e1]
  refine ⟨⟨k, k', e1, e2⟩, ?_⟩
  apply Units.ext
  rw [tm_coe]
  exact hk.symm
end GlobalTheory.JR.LinDesc
