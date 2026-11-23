-- Prove2me | solution 1 for GlobalTheory.UTrans.Model.hf_add_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:13:49.215007+00:00
-- url     : https://prove2.me/submissions/04cc5c16-3eb3-46fc-bcf8-b1180d32cab1

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
theorem _root_.solution (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (v x y : Fin n → R) (c : R) :
    hf σ G y (v + c • x) = hf σ G y v + σ c * hf σ G y x := by
  simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
end GlobalTheory.UTrans.Model
