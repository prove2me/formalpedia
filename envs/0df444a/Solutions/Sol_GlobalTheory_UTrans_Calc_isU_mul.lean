-- Prove2me | solution 1 for GlobalTheory.UTrans.Calc.isU_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:37.470741+00:00
-- url     : https://prove2.me/submissions/5943819f-278d-49eb-a9a6-7b4f28967055

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary

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
theorem _root_.solution (γ γ' : Matrix (Fin n) (Fin n) R) (h : IsU σ G γ) (h' : IsU σ G γ') :
    IsU σ G (γ * γ') := by
  intro v w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, h']
end GlobalTheory.UTrans.Calc
