-- Prove2me | solution 1 for GlobalTheory.K5.Basic.tw_exists_prim_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:24:51.433348+00:00
-- url     : https://prove2.me/submissions/52872d50-a871-4d4a-8767-72c58ceb7143

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
theorem _root_.solution (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] :
    ∃ z : Ω, IsPrimitiveRoot z p := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (cyclotomic p Ω)
    (ne_of_gt (degree_cyclotomic_pos p Ω hp.out.pos))
  exact ⟨z, (isRoot_cyclotomic_iff).1 hz⟩
end GlobalTheory.K5.Basic
