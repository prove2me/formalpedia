-- Prove2me | solution 1 for GlobalTheory.SympBlocks.det_ne_zero_and_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:13:31.926094+00:00
-- url     : https://prove2.me/submissions/92458c2f-608e-454d-971f-11c70fe55138

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticHolPartDetNeZeroAndIsSymm
import Theorems.Thm_GlobalTheory_SympBlocks_herm_identity
import Theorems.Thm_GlobalTheory_SympBlocks_symm_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.SympBlocks
open scoped ComplexOrder
namespace GlobalTheory.SympBlocks
theorem _root_.solution : ∀ (l : Type) [Fintype l] [DecidableEq l]
    (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ),
    (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) →
    (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) →
    s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 ∧ (-(Q * P⁻¹)).IsSymm := by
  intro l _ _ s P Q hP hQ hs
  have hs' : fromBlocks s.toBlocks₁₁ s.toBlocks₁₂ s.toBlocks₂₁ s.toBlocks₂₂ ∈
      Matrix.symplecticGroup l ℝ := by rwa [fromBlocks_toBlocks]
  obtain ⟨r1, r2, r3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hs'
  set A := s.toBlocks₁₁.map Complex.ofRealHom
  set B := s.toBlocks₁₂.map Complex.ofRealHom
  set C := s.toBlocks₂₁.map Complex.ofRealHom
  set D := s.toBlocks₂₂.map Complex.ofRealHom
  have h1 : Aᵀ * C = Cᵀ * A := by
    simp only [A, C, ← transpose_map, ← Matrix.map_mul, r1]
  have h2 : Bᵀ * D = Dᵀ * B := by
    simp only [B, D, ← transpose_map, ← Matrix.map_mul, r2]
  have h3 : Aᵀ * D - Cᵀ * B = 1 := by
    simp only [A, B, C, D, ← transpose_map, ← Matrix.map_mul]
    rw [← Matrix.map_sub _ (fun a b => map_sub Complex.ofRealHom a b), r3]; simp
  have ePQ : P = A - I • B ∧ Q = C - I • D := by
    constructor <;> ext a b <;> simp [A, B, C, D, hP, hQ, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁,
      toBlocks₂₂]
  obtain ⟨eP, eQ⟩ := ePQ
  have hPc : Pᴴ = Aᵀ + I • Bᵀ := by
    rw [eP]; ext a b; simp [A, B, conjTranspose_apply, transpose_apply]
  have hQc : Qᴴ = Cᵀ + I • Dᵀ := by
    rw [eQ]; ext a b; simp [C, D, conjTranspose_apply, transpose_apply]
  have hH : Pᴴ * Q - Qᴴ * P = (-(2 * I)) • (1 : Matrix l l ℂ) := by
    rw [hPc, hQc, eP, eQ]; exact herm_identity A B C D h1 h2 h3
  have hS : Pᵀ * Q = Qᵀ * P := by
    rw [eP, eQ]; exact symm_identity A B C D h1 h2 h3
  have hdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have key : star v ⬝ᵥ ((Pᴴ * Q - Qᴴ * P) *ᵥ v) = 0 := by
      rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_zero, dotProduct_zero, sub_zero, dotProduct_mulVec, ← star_mulVec, hv,
        star_zero, zero_dotProduct]
    rw [hH, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at key
    have h2I : (-(2 * I)) ≠ 0 := by simp [I_ne_zero]
    have : star v ⬝ᵥ v = 0 := (mul_eq_zero.1 key).resolve_left h2I
    exact hv0 (dotProduct_star_self_eq_zero.1 this)
  refine ⟨hdet, ?_⟩
  have hu : IsUnit P.det := isUnit_iff_ne_zero.2 hdet
  have huT : IsUnit Pᵀ.det := by rwa [det_transpose]
  apply Matrix.IsSymm.neg
  unfold Matrix.IsSymm
  rw [transpose_mul, transpose_nonsing_inv]
  calc Pᵀ⁻¹ * Qᵀ = Pᵀ⁻¹ * (Qᵀ * P) * P⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = Pᵀ⁻¹ * (Pᵀ * Q) * P⁻¹ := by rw [hS]
    _ = Q * P⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ huT, Matrix.one_mul]
end GlobalTheory.SympBlocks
