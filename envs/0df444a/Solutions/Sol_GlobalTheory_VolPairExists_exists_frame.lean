-- Prove2me | solution 1 for GlobalTheory.VolPairExists.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:01.26882+00:00
-- url     : https://prove2.me/submissions/3b84d5a5-39ce-4d60-92b5-9ab462ebb2fb

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LeftInvOfUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.VolPairExists
variable {P Q : ℕ}
variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
namespace GlobalTheory.VolPairExists
theorem _root_.solution (h : Formalism.UG.HasSignature G P Q) :
    ∃ (A : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ) (L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ),
      Aᴴ * Formalism.UG.Jpq P Q * A = G ∧ L * A = 1 ∧ A * L = 1 := by
  unfold Formalism.UG.HasSignature at h
  obtain ⟨e, g, hg⟩ := h
  have hg' : (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Matrix.reindex e e G * g = Formalism.UG.Jpq P Q := hg
  have key : Matrix.reindex e e G =
      ((g⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Formalism.UG.Jpq P Q *
        ((g⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
    set u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := g.val
    set v : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := (g⁻¹).val
    have huv : u * v = 1 := Units.mul_inv g
    calc Matrix.reindex e e G = (u * v)ᴴ * Matrix.reindex e e G * (u * v) := by
          rw [huv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = vᴴ * (uᴴ * Matrix.reindex e e G * u) * v := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = vᴴ * Formalism.UG.Jpq P Q * v := by rw [hg']
  refine ⟨((g⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix id e,
    (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix e id, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_id_id (Formalism.UG.Jpq P Q),
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← key]
    ext i j
    simp [Matrix.reindex_apply]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Units.mul_inv, Matrix.submatrix_one_equiv]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ e.bijective, Units.inv_mul, Matrix.submatrix_id_id]
end GlobalTheory.VolPairExists
