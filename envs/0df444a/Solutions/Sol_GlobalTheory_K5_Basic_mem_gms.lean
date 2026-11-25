-- Prove2me | solution 1 for GlobalTheory.K5.Basic.mem_gms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:55:19.914439+00:00
-- url     : https://prove2.me/submissions/cee1b287-fa68-44cb-b3c5-8203a307fd3a

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
theorem _root_.solution (T : Tower p Ω) (m s : ℕ) (g : Gal p Ω) :
    g ∈ Gms T m s ↔ g (T.ζ m) = T.ζ m ∧ g (T.qq s) = T.qq s := Iff.rfl
end GlobalTheory.K5.Basic
