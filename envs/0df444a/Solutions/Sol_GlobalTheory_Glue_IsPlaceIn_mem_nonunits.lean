-- Prove2me | solution 1 for GlobalTheory.Glue.IsPlaceIn.mem_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:44:58.459706+00:00
-- url     : https://prove2.me/submissions/9901423f-7671-45f4-bf5e-a43c7d0fb359

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EeProd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
import Theorems.Thm_GlobalTheory_K5_Basic_charZero_of_isClo
import Theorems.Thm_GlobalTheory_K5_Basic_not_cong_one_zero


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
namespace IsPlaceIn
theorem _root_.solution (hc : IsClo p Ωl) {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl}
    (h : IsPlaceIn ε A T j) : ((p : ℕ) : Ω) ∈ A.nonunits := by
  haveI := Basic.charZero_of_isClo hc
  rw [ValuationSubring.mem_nonunits_iff_or]
  refine Or.inr fun hA => Basic.not_cong_one_zero hc 1 one_ne_zero ⟨_, (h.int _).1 hA, ?_⟩
  have hp0 : (p : Ωl) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  rw [map_inv₀, map_natCast, pow_one, mul_inv_cancel₀ hp0, sub_zero]
end IsPlaceIn
end GlobalTheory.Glue
