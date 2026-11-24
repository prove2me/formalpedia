-- Prove2me | solution 1 for GlobalTheory.UTrans.Model.isU_tv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:43:36.852058+00:00
-- url     : https://prove2.me/submissions/309c574b-efb5-49df-be1c-41136fe4c3e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_NontrivialTransvection
import Theorems.Thm_GlobalTheory_UTrans_Model_tv_mulVec
import Theorems.Thm_GlobalTheory_UTrans_Model_hf_add_smul_left
import Theorems.Thm_GlobalTheory_UTrans_Model_hf_add_smul_right
import Theorems.Thm_GlobalTheory_UTrans_Model_hf_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Model
open GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.UTrans.Model
theorem _root_.solution (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (hσ : ∀ a, σ (σ a) = a)
    (hG : ∀ a b, σ (G a b) = G b a) (x : Fin n → R) (t : R)
    (h : t + σ t + t * σ t * hf σ G x x = 0) : IsU σ G (tv σ G x t) := by
  intro v w
  rw [tv_mulVec, tv_mulVec, hf_add_smul_left, hf_add_smul_right, hf_add_smul_right, map_mul,
    hf_conj σ G hσ hG w x]
  linear_combination (hf σ G v x * hf σ G x w) * h
end GlobalTheory.UTrans.Model
