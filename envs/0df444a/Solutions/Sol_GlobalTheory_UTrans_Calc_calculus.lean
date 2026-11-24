-- Prove2me | solution 1 for GlobalTheory.UTrans.Calc.calculus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:57:05.614192+00:00
-- url     : https://prove2.me/submissions/8150a5cc-e262-4493-bdbd-27f3bf6c267d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_conj
import Theorems.Thm_GlobalTheory_UTrans_Calc_tv_mulVec
import Theorems.Thm_GlobalTheory_UTrans_Calc_tv_mul
import Theorems.Thm_GlobalTheory_UTrans_Calc_tv_det
import Theorems.Thm_GlobalTheory_UTrans_Calc_isU_tv
import Theorems.Thm_GlobalTheory_UTrans_Calc_conj_tv
import Theorems.Thm_GlobalTheory_UTrans_Calc_tv_smul
import Theorems.Thm_GlobalTheory_UTrans_Calc_isU_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Calc
variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)
namespace GlobalTheory.UTrans.Calc
theorem _root_.solution : ∀ (R : Type) [CommRing R] (n : ℕ) (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R), (∀ a, σ (σ a) = a) → (∀ a b, σ (G a b) = G b a) → (∀ x y, σ (hf σ G x y) = hf σ G y x) ∧ (∀ x t v, tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x) ∧ (∀ x t t', tv σ G x t * tv σ G x t' = tv σ G x (t + t' + t * t' * hf σ G x x)) ∧ (∀ x t, (tv σ G x t).det = 1 + t * hf σ G x x) ∧ (∀ x t, t + σ t + t * σ t * hf σ G x x = 0 → IsU σ G (tv σ G x t)) ∧ (∀ γ x t, IsU σ G γ → γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ) ∧ (∀ (a : R) x t, tv σ G (a • x) t = tv σ G x (t * a * σ a)) ∧ (∀ γ γ', IsU σ G γ → IsU σ G γ' → IsU σ G (γ * γ')) :=
  fun _ _ _ σ G hσ hG => ⟨hf_conj σ G hσ hG, tv_mulVec σ G, tv_mul σ G, tv_det σ G, isU_tv σ G hσ hG,
    conj_tv σ G, tv_smul σ G, isU_mul σ G⟩
end GlobalTheory.UTrans.Calc
