-- Prove2me | solution 1 for GlobalTheory.ThetaPositivity.form_add_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:43:11.590315+00:00
-- url     : https://prove2.me/submissions/8fbc45bf-f744-481f-b9b6-04ae33ab3e05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ReFormPosOfThetaNeZero
import Theorems.Thm_GlobalTheory_ThetaPositivity_form_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaPositivity
variable {g : ℕ}
open Complex Matrix Filter Topology
open scoped BigOperators Real
variable {g : ℕ}
namespace GlobalTheory.ThetaPositivity
namespace _root_.GlobalTheory.ThetaPositivity
theorem _root_.solution {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    ((z + w) ⬝ᵥ Hm.mulVec (star (z + w))).re =
      (z ⬝ᵥ Hm.mulVec (star z)).re + 2 * (z ⬝ᵥ Hm.mulVec (star w)).re
        + (w ⬝ᵥ Hm.mulVec (star w)).re := by
  rw [star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    _root_.GlobalTheory.ThetaPositivity.form_conj hH z w]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring
end _root_.GlobalTheory.ThetaPositivity
end GlobalTheory.ThetaPositivity
