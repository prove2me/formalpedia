-- Prove2me | solution 1 for GlobalTheory.UTrans.Calc.tv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:42.736879+00:00
-- url     : https://prove2.me/submissions/2a940de0-393e-4420-918d-572705d86581

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Theorems.Thm_GlobalTheory_UTrans_Calc_hf_smul_right
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
theorem _root_.solution (a : R) (x : Fin n → R) (t : R) :
    tv σ G (a • x) t = tv σ G x (t * a * σ a) := by
  refine ext_mulVec fun v => ?_
  rw [tv_mulVec, tv_mulVec, hf_smul_right, smul_smul]
  congr 2
  ring
end GlobalTheory.UTrans.Calc
