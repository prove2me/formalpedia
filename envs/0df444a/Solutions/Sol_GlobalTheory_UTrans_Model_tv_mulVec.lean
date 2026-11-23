-- Prove2me | solution 1 for GlobalTheory.UTrans.Model.tv_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:34.695804+00:00
-- url     : https://prove2.me/submissions/96a7046a-691c-4696-918d-74332b496fa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_NontrivialTransvection

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
theorem _root_.solution (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x v : Fin n → R) (t : R) :
    (tv σ G x t).mulVec v = v + (t * hf σ G v x) • x := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec]
  ext a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.of_apply, hf,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => by ring
end GlobalTheory.UTrans.Model
