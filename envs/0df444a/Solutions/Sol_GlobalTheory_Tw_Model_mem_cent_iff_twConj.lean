-- Prove2me | solution 1 for GlobalTheory.Tw.Model.mem_cent_iff_twConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:15.923458+00:00
-- url     : https://prove2.me/submissions/2222d594-5db7-4275-879c-d799cd21be92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.Model
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
namespace GlobalTheory.Tw.Model
theorem _root_.solution {δ g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    g ∈ cent δ ↔ twConj g δ = δ := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).mp hg
  simp only [cent, Set.mem_setOf_eq, hg, true_and, twConj, Matrix.mul_assoc]
  constructor
  · intro h
    rw [← h, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hd]
end GlobalTheory.Tw.Model
