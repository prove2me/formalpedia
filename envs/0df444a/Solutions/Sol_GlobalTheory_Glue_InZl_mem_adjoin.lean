-- Prove2me | solution 1 for GlobalTheory.Glue.InZl.mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:33:05.165882+00:00
-- url     : https://prove2.me/submissions/f58705bd-ee2a-41d1-9e48-2cd11fff03d8

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
namespace InZl
theorem _root_.solution {l n : ℕ} {F : Ω} (h : InZl ε l n F) : F ∈ IntermediateField.adjoin ℚ {zt ε l n} := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨D, hD, hF⟩ := h
  have hD0 : (D : Ω) ≠ 0 := by
    rintro h0
    exact hD (by rw [Nat.cast_eq_zero.1 h0]; exact dvd_zero _)
  have h1 : (D : Ω) * F ∈ IntermediateField.adjoin ℚ {zt ε l n} :=
    (Subring.closure_le (t := (IntermediateField.adjoin ℚ {zt ε l n}).toSubring)).2
      (IntermediateField.subset_adjoin ℚ _) hF
  have h2 := mul_mem (inv_mem (natCast_mem (IntermediateField.adjoin ℚ {zt ε l n}) D)) h1
  rwa [inv_mul_cancel_left₀ hD0] at h2
end InZl
end GlobalTheory.Glue
