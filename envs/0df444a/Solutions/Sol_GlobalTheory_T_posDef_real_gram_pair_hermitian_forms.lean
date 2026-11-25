-- Prove2me | solution 1 for GlobalTheory.T.posDef_real_gram_pair_hermitian_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:26:32.366362+00:00
-- url     : https://prove2.me/submissions/5b26be89-4e8c-4c4d-acc3-59c3455c3b7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefRealGramPairHermitianForms
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefRealGramPairHermitianFormsStatement
import Theorems.Thm_GlobalTheory_HermGram_gram_posDef_pair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re).PosDef ∧
    ((Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ)).PosDef := by
  first | exact @GlobalTheory.HermGram.gram_posDef_pair | exact GlobalTheory.HermGram.gram_posDef_pair | (intros; apply GlobalTheory.HermGram.gram_posDef_pair <;> assumption)
end _root_.GlobalTheory.T
