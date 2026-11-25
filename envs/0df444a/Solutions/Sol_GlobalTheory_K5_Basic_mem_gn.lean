-- Prove2me | solution 1 for GlobalTheory.K5.Basic.mem_gn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:58:22.264519+00:00
-- url     : https://prove2.me/submissions/e8013083-eb7a-4c1a-8bc2-1319bd5b7fe3

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
theorem _root_.solution (T : Tower p Ω) (n : ℕ) (g : Gal p Ω) :
    g ∈ Gn T n ↔ g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := Iff.rfl
end GlobalTheory.K5.Basic
