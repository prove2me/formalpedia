-- Prove2me | solution 1 for GlobalTheory.Tw.Model.Phi_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:20.576739+00:00
-- url     : https://prove2.me/submissions/12208ca7-a88e-48d3-98e9-55bace00a534

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
theorem _root_.solution : Phi 2 ℂ = !![0, 1; -1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi]
end GlobalTheory.Tw.Model
