-- Prove2me | solution 1 for GlobalTheory.Tw.Model.Phi_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:45.399948+00:00
-- url     : https://prove2.me/submissions/834ad771-f43f-472b-8c52-0ce965894ca2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Theorems.Thm_P2M_GlobalTheory_Tw_Model_Phi_apply__7c1f3a1c520a

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
theorem _root_.solution : (Phi n R)ᴴ = (Phi n R)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Phi_apply']
  split_ifs <;> simp
end GlobalTheory.Tw.Model
