-- Prove2me | solution 1 for GlobalTheory.K5.Basic.isInt_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:24:55.727127+00:00
-- url     : https://prove2.me/submissions/770e78ec-972a-408b-b0f3-e285dfbfbcd7

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
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
namespace GlobalTheory.K5.Basic
theorem _root_.solution (m : ℤ) : IsInt p (m : Ω) := by
  rw [IsInt, ← map_intCast (algebraMap (O0 p) Ω)]
  exact isIntegral_algebraMap
end GlobalTheory.K5.Basic
