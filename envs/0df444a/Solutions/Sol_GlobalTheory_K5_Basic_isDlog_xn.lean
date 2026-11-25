-- Prove2me | solution 1 for GlobalTheory.K5.Basic.isDlog_xn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:55:05.487227+00:00
-- url     : https://prove2.me/submissions/b4d94136-2d27-4bdd-a6d9-ad4f6535a296

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
theorem _root_.solution (n : ℕ) : IsDlog p n (xn p n) 0 1 := by
  simp [IsDlog]
end GlobalTheory.K5.Basic
