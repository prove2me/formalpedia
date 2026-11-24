-- Prove2me | solution 1 for GlobalTheory.EisConstTerm.eisTerm_pair_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:26:23.379688+00:00
-- url     : https://prove2.me/submissions/a63b7258-0381-44d4-ac8e-254ebb2bbf2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinConstantTermPartialZeta
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_prod_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open GlobalTheory GlobalTheory.EisConstTerm
namespace GlobalTheory.EisConstTerm
theorem _root_.solution (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (s : ℕ) (z : Emb F → ℂ) (a : F) :
    eisTerm (2 * s) 0 z (a, 0) = ((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
      ((|((Algebra.norm ℚ a : ℚ) : ℝ)| : ℝ) : ℂ)⁻¹ ^ (2 * s) := by
  have hcard : Fintype.card (Emb F) = Module.finrank ℚ F := by
    rw [← NumberField.Embeddings.card F ℂ]
    refine Fintype.card_of_bijective (f := fun τ : Emb F => (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
    · intro τ τ' hτ
      ext y
      have := DFunLike.congr_fun hτ y
      simpa using this
    · intro φ
      have hr : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
      exact ⟨hr.embedding, by ext y; simp⟩
  have hprod : ∏ τ, latPt z (a, 0) τ = (2 * (Real.pi : ℂ) * Complex.I) ^ Module.finrank ℚ F * ((Algebra.norm ℚ a : ℚ) : ℂ) := by
    rw [← prod_emb, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [latPt]
  unfold eisTerm
  rw [hprod, mul_zero, Complex.cpow_zero, mul_one, mul_inv, mul_pow, inv_pow ((2 * (Real.pi : ℂ) * Complex.I) ^ Module.finrank ℚ F), ← pow_mul, mul_comm (Module.finrank ℚ F)]
  congr 1
  rw [← Complex.ofReal_ratCast, inv_pow, inv_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, (even_two_mul s).pow_abs]
end GlobalTheory.EisConstTerm
