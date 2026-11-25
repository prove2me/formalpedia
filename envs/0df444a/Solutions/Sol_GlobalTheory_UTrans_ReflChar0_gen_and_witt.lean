-- Prove2me | solution 1 for GlobalTheory.UTrans.ReflChar0.gen_and_witt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:21.069991+00:00
-- url     : https://prove2.me/submissions/bfe2ec1b-295f-40c7-a9ad-9418945a00ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWitt
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_exists_prod_mulVec_eq
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_exists_basis
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_isU_prod
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_exists_inv
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_exists_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.ReflChar0
open GlobalTheory.UTrans.Calc
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.UTrans.ReflChar0
theorem _root_.solution : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → (∀ γ, GlobalTheory.UTrans.IsU σ G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, GlobalTheory.UTrans.hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) ∧ γ = (l.map fun p => GlobalTheory.UTrans.tv σ G p.1 ((p.2 - 1) / GlobalTheory.UTrans.hf σ G p.1 p.1)).prod) ∧ ∀ x z : Fin n → E, GlobalTheory.UTrans.hf σ G x x ≠ 0 → GlobalTheory.UTrans.hf σ G z z = GlobalTheory.UTrans.hf σ G x x → ∃ γ, GlobalTheory.UTrans.IsU σ G γ ∧ γ *ᵥ z = x := by
  intro E _ _ n σ G hG
  refine ⟨fun γ hγ => ?_, fun x z hx hz => ?_⟩
  · obtain ⟨x, h1, h2, h3⟩ := exists_basis hG
    obtain ⟨l, hl, hfix⟩ := exists_fix hG hγ x h1 h2 n
    obtain ⟨l', hl', hinv⟩ := exists_inv hG l hl
    refine ⟨l', hl', ?_⟩
    have hone : (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod * γ = 1 := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext_on_range h3 fun i => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix i i.2, Matrix.one_mulVec]
    rw [← one_mul γ, ← hinv, mul_assoc, hone, mul_one]
  · obtain ⟨l, hl, e⟩ := exists_prod_mulVec_eq hG x z hx hz
    exact ⟨_, isU_prod hG l fun p hp => ⟨(hl p hp).1, (hl p hp).2.1⟩, e⟩
end GlobalTheory.UTrans.ReflChar0
