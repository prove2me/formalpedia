-- Prove2me | solution 1 for GlobalTheory.Glue.KT.mem_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:45:20.05745+00:00
-- url     : https://prove2.me/submissions/8dabe8a4-fc49-43d3-b345-209d51f4c7bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EeProd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open GlobalTheory GlobalTheory.Glue
open GlobalTheory.KZ GlobalTheory.K5
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
variable {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]
namespace GlobalTheory.Glue
namespace KT
theorem _root_.solution (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (f : X.K) : f ∈ KT X L ↔ X.sl (ofSL (ModularGroup.T ^ L)) f = f := Iff.rfl
end KT
end GlobalTheory.Glue
