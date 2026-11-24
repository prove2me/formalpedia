-- Prove2me | solution 1 for GlobalTheory.UTrans.Model.det_tv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:43:36.132721+00:00
-- url     : https://prove2.me/submissions/8a15dde4-f25e-4b58-8003-3553ee9df0ee

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
theorem _root_.solution (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (t : R) :
    (tv σ G x t).det = 1 + t * hf σ G x x := by
  have e : tv σ G x t = (1 : Matrix (Fin n) (Fin n) R) + Matrix.replicateCol (Fin 1) x *
      Matrix.replicateRow (Fin 1) (fun b : Fin n => t * ∑ e : Fin n, G b e * σ (x e)) := by
    unfold tv
    congr 1
    ext a b
    simp [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    ring
  rw [e]
  refine (Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) x _).trans ?_
  simp only [dotProduct, hf, Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
end GlobalTheory.UTrans.Model
