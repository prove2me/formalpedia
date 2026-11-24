-- Prove2me | solution 1 for GlobalTheory.UTrans.Calc.conj_tv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:36.568804+00:00
-- url     : https://prove2.me/submissions/7b8cbd68-4e2e-4970-ba61-bc753d60885a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Theorems.Thm_GlobalTheory_UTrans_Calc_tv_mulVec
import Theorems.Thm_GlobalTheory_UTrans_Calc_ext_mulVec

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
theorem _root_.solution (γ : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (t : R) (h : IsU σ G γ) :
    γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ := by
  refine ext_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, h, Matrix.mulVec_add,
    Matrix.mulVec_smul]
end GlobalTheory.UTrans.Calc
