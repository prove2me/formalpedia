-- Prove2me | solution 1 for GlobalTheory.K5.Basic.fPi_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:01:44.834531+00:00
-- url     : https://prove2.me/submissions/d6d313d8-84b1-4f7d-861c-a7cdb17215b1

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
theorem _root_.solution (n : ℕ) (k l : ℤ) (α β α' β' : On p n) :
    fPi p n l k α' β' α β = - fPi p n k l α β α' β' := by simp only [fPi]; ring
end GlobalTheory.K5.Basic
