-- Prove2me | solution 1 for GlobalTheory.UTrans.Model.not_isU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:31.16304+00:00
-- url     : https://prove2.me/submissions/1ea1819a-c50b-4cce-81dc-d8132416a228

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
theorem _root_.solution : ¬ IsU (starRingEnd ℂ) !![0, 1; 1, 0] !![1, 1; 0, 1] := by
  intro h
  have h1 := h ![0, 1] ![0, 1]
  norm_num [hf, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
end GlobalTheory.UTrans.Model
