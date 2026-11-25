-- Prove2me | solution 1 for GlobalTheory.Glue.IsNTr.iff_isNT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:44:45.533934+00:00
-- url     : https://prove2.me/submissions/8f05db1b-2a5f-445e-b47b-e65d22c91e89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EeProd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
import Theorems.Thm_GlobalTheory_Glue_InZl_mem_adjoin

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
namespace IsNTr
theorem _root_.solution {l n m : ℕ} [NeZero l] {F F' : Ω} (hm : 1 ≤ m) (hmn : m ≤ n) (hF : InZl ε l n F) :
    IsNTr ε l n m F F' ↔ IsNT ε l n m F F' :=
  ⟨fun h => h.2.2.2, fun h => ⟨hm, hmn, hF.mem_adjoin, h⟩⟩
end IsNTr
end GlobalTheory.Glue
