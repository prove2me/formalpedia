-- Prove2me | solution 1 for GlobalTheory.Tw.dot_star_comm_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:52.475985+00:00
-- url     : https://prove2.me/submissions/72ce1ab1-e890-4bf3-bbc2-b552eb022d68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars

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
open GlobalTheory GlobalTheory.Tw
variable {n : ℕ}
namespace GlobalTheory.Tw
theorem _root_.solution {v w : Fin n → ℂ} (h : v ⬝ᵥ star w = 0) : w ⬝ᵥ star v = 0 := by
  have := congrArg star h
  rwa [star_zero, ← star_dotProduct_star, star_star] at this
end GlobalTheory.Tw
