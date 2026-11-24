-- Prove2me | solution 1 for GlobalTheory.UTrans.Calc.tv_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:40.017465+00:00
-- url     : https://prove2.me/submissions/bde94c2d-ad5c-4e56-b340-ec084fbab620

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
theorem _root_.solution (x : Fin n → R) (t : R) : (tv σ G x t).det = 1 + t * hf σ G x x := by
  have h : tv σ G x t = 1 + Matrix.replicateCol Unit (t • x) *
      Matrix.replicateRow Unit (fun b => ∑ e, G b e * σ (x e)) := by
    rw [tv]
    congr 1
    ext a b
    simp [Matrix.mul_apply]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp only [dotProduct, hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring
end GlobalTheory.UTrans.Calc
