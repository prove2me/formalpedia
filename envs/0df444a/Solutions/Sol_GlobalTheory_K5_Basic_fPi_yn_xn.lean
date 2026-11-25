-- Prove2me | solution 1 for GlobalTheory.K5.Basic.fPi_yn_xn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:20.403428+00:00
-- url     : https://prove2.me/submissions/ff81893e-f382-48ba-bc09-f041d09dff99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable (p : ℕ) [hp : Fact p.Prime]
namespace GlobalTheory.K5.Basic
theorem _root_.solution (n : ℕ) : fPi p n 0 0 1 0 0 1 = xn p n - 1 := by simp [fPi]
end GlobalTheory.K5.Basic
