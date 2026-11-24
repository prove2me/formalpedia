-- Prove2me | solution 1 for GlobalTheory.UTrans.Calc.isU_tv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:38.045416+00:00
-- url     : https://prove2.me/submissions/6aec1201-ad32-485d-865a-1f0a265cc43a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_add_left
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_add_right
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_smul_left
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_smul_right
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_conj
import Theorems.Thm_GlobalTheory_UTrans_Calc_tv_mulVec

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
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a) (x : Fin n → R) (t : R)
    (h : t + σ t + t * σ t * hf σ G x x = 0) : IsU σ G (tv σ G x t) := by
  intro v w
  rw [tv_mulVec, tv_mulVec]
  simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, map_mul, hf_conj σ G hσ hG]
  linear_combination (hf σ G v x * hf σ G x w) * h
end GlobalTheory.UTrans.Calc
