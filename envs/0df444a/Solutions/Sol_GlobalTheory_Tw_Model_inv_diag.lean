-- Prove2me | solution 1 for GlobalTheory.Tw.Model.inv_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:21.258092+00:00
-- url     : https://prove2.me/submissions/ff1b3a95-6ddf-4bf8-bdee-1c1d13e06246

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
theorem _root_.solution : (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = !![1/2, 0; 0, 1] := by
  apply Matrix.inv_eq_right_inv
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
end GlobalTheory.Tw.Model
