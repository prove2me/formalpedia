-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.exists_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:45:33.932347+00:00
-- url     : https://prove2.me/submissions/3d25a07f-5744-4227-85d6-8b567971b6f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
import Theorems.Thm_GlobalTheory_SW_UniSp_sw_sw
import Theorems.Thm_GlobalTheory_SW_UniSp_qm_mul
import Theorems.Thm_GlobalTheory_SW_UniSp_qm_one
import Theorems.Thm_GlobalTheory_SW_UniSp_exists_reg
import Theorems.Thm_GlobalTheory_SW_UniSp_exists_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UniSp
noncomputable section
open Classical
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
variable {Ψ : Finset (E →+* ℂ)} {N : ℕ}
namespace GlobalTheory.SW.UniSp
theorem _root_.solution [IsCMField E] (hΨ : IsType Ψ)
    {S' : Matrix ((Fin N ⊕ Fin N) × Ψ) (QI E N) ℂ} (h1 : Sm Ψ N * S' = 1) (h2 : S' * Sm Ψ N = 1)
    (A B C D : Matrix (Fin N) (Fin N) E) :
    ∃ σ : Matrix (QI E N ⊕ QI E N) (QI E N ⊕ QI E N) ℚ,
      qm σ.toBlocks₁₁ = Sm Ψ N * blockDiagonal (fun τ : Ψ => dl (A.map τ.1)) * S' ∧
      qm σ.toBlocks₁₂ = Sm Ψ N * blockDiagonal (fun τ : Ψ => dl (B.map τ.1) * sw _) * (Sm Ψ N)ᵀ ∧
      qm σ.toBlocks₂₁ = S'ᵀ * blockDiagonal (fun τ : Ψ => sw _ * dl (C.map τ.1)) * S' ∧
      qm σ.toBlocks₂₂ = S'ᵀ * blockDiagonal (fun τ : Ψ => sw _ * dl (D.map τ.1) * sw _) *
        (Sm Ψ N)ᵀ := by
  have hR : ∀ X : Matrix (Fin N) (Fin N) E, ∃ R : Matrix (QI E N) (QI E N) ℚ,
      qm R = Sm Ψ N * (blockDiagonal fun τ : Ψ => dl (X.map τ.1)) * S' := fun X => by
    obtain ⟨R, hR⟩ := exists_reg (Ψ := Ψ) X
    exact ⟨R, by rw [← hR, Matrix.mul_assoc, h1, Matrix.mul_one]⟩
  choose R hR using hR
  obtain ⟨G, hG⟩ := exists_gram (N := N) hΨ
  have t2 : (Sm Ψ N)ᵀ * S'ᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  have c2 : ∀ X : Matrix ((Fin N ⊕ Fin N) × Ψ) (QI E N) ℂ,
      S' * (Sm Ψ N * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have c3 : ∀ X : Matrix ((Fin N ⊕ Fin N) × Ψ) (QI E N) ℂ,
      (Sm Ψ N)ᵀ * (S'ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, t2, Matrix.one_mul]
  have hGi : qm G * (S'ᵀ * blockDiagonal (fun _ : Ψ => sw (Fin N)) * S') = 1 := by
    rw [hG]
    simp only [Matrix.mul_assoc, c3]
    rw [← Matrix.mul_assoc (blockDiagonal _), ← blockDiagonal_mul]
    simp only [sw_sw]
    rw [show (fun _ : Ψ => (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ)) = 1 from rfl,
      blockDiagonal_one, Matrix.one_mul, h1]
  have hdet : G.det ≠ 0 := by
    intro h0
    have e : (qm G).det = ((G.det : ℚ) : ℂ) := ((Rat.castHom ℂ).map_det G).symm
    have := congrArg det hGi
    rw [det_mul, e, h0] at this
    simp at this
  have hGinv : qm G⁻¹ = S'ᵀ * blockDiagonal (fun _ : Ψ => sw (Fin N)) * S' := by
    rw [← Matrix.mul_one (qm G⁻¹), ← hGi, ← Matrix.mul_assoc, ← qm_mul,
      nonsing_inv_mul _ (Ne.isUnit hdet), qm_one, Matrix.one_mul]
  refine ⟨fromBlocks (R A) (R B * G) (G⁻¹ * R C) (G⁻¹ * R D * G), hR A, ?_, ?_, ?_⟩
  all_goals
    simp only [toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, qm_mul, hR,
      hGinv, hG, blockDiagonal_mul, Matrix.mul_assoc, c2]
end GlobalTheory.SW.UniSp
