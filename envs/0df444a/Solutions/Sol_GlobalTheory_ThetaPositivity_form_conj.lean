-- Prove2me | solution 1 for GlobalTheory.ThetaPositivity.form_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:31:21.566178+00:00
-- url     : https://prove2.me/submissions/8a927a03-7cf9-4f24-8652-f5ebdc46f8d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ReFormPosOfThetaNeZero

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
    w ⬝ᵥ Hm.mulVec (star z) = star (z ⬝ᵥ Hm.mulVec (star w)) := by
  rw [← star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, ← Matrix.dotProduct_mulVec]
end _root_.GlobalTheory.ThetaPositivity
end GlobalTheory.ThetaPositivity
