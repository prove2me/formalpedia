-- Prove2me | solution 1 for GlobalTheory.K5.Basic.isDlog_yn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:55:10.205325+00:00
-- url     : https://prove2.me/submissions/2c0dbd6c-577c-4f96-bbe9-9f0995f6a4dc

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
theorem _root_.solution (n : ℕ) : IsDlog p n (yn p n) 1 0 := by
  simp [IsDlog, mul_comm]
end GlobalTheory.K5.Basic
