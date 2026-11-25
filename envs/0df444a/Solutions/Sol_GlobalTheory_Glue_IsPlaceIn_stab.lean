-- Prove2me | solution 1 for GlobalTheory.Glue.IsPlaceIn.stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:45:05.512058+00:00
-- url     : https://prove2.me/submissions/4806e105-e36a-420f-92d9-28f5081f7f5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EeProd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
import Theorems.Thm_GlobalTheory_K5_Basic_isInt_gal


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
theorem _root_.solution {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} (h : IsPlaceIn ε A T j)
    {g : Gal p Ωl} {s : Ω ≃ₐ[ℚ] Ω} (hs : ∀ x, g (j x) = j (s x)) : Stab A s := fun x => by
  rw [h.int, h.int, ← hs]
  exact ⟨fun hx => by simpa using Basic.isInt_gal g.symm hx, Basic.isInt_gal g⟩
end IsPlaceIn
end GlobalTheory.Glue
