-- Prove2me | solution 1 for GlobalTheory.Glue.IsIo.isExpIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:47:33.180712+00:00
-- url     : https://prove2.me/submissions/96a37e8a-f098-4847-88c5-809b57045692

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
variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ} {ψ : O0 p →+* Ωl}
  {io : KT X (p ^ n) →+* Ωl}
namespace GlobalTheory.Glue
namespace IsIo
theorem _root_.solution (h : IsIo X A T j n ψ io) (hj : IsPlaceIn ε A T j) (hψ : IsReb T n ψ) : IsExpIn X A T j n ψ io :=
  ⟨hj, hψ, h.ev⟩
end IsIo
end GlobalTheory.Glue
