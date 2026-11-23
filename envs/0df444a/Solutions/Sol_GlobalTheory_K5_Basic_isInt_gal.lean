-- Prove2me | solution 1 for GlobalTheory.K5.Basic.isInt_gal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:48.637902+00:00
-- url     : https://prove2.me/submissions/5364b846-ba3b-4999-b295-174c50f5f9f8

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
theorem _root_.solution (g : Gal p Ω) {x : Ω} (hx : IsInt p x) : IsInt p (g x) :=
  IsIntegral.map g.toAlgHom hx
end GlobalTheory.K5.Basic
