-- Prove2me | solution 1 for GlobalTheory.Glue.IsCusp.isPlaceIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:47:23.309821+00:00
-- url     : https://prove2.me/submissions/ecfef1f4-a0f9-4ffa-8faf-3c090ac2d9ba

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
namespace IsCusp
theorem _root_.solution {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} (h : IsCusp ε A T j) :
    IsPlaceIn ε A T j := ⟨h.int, h.alg, h.root⟩
end IsCusp
end GlobalTheory.Glue
