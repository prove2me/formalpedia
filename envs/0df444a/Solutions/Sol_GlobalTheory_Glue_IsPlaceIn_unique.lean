-- Prove2me | solution 1 for GlobalTheory.Glue.IsPlaceIn.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:45:11.935709+00:00
-- url     : https://prove2.me/submissions/dd08b6d1-6c26-484b-9efd-36858fef9e65

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
namespace IsPlaceIn
theorem _root_.solution {A A' : ValuationSubring Ω} {T T' : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} (h : IsPlaceIn ε A T j)
    (h' : IsPlaceIn ε A' T' j) : A = A' :=
  ValuationSubring.ext _ _ fun x => (h.int x).trans (h'.int x).symm
end IsPlaceIn
end GlobalTheory.Glue
