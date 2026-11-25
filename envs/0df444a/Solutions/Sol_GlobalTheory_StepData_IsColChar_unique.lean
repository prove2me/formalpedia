-- Prove2me | solution 1 for GlobalTheory.StepData.IsColChar.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:58:20.148269+00:00
-- url     : https://prove2.me/submissions/be1b66f0-2845-424e-8536-f58b1899e7e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_mem_Cgrp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.StepData
namespace IsColChar
theorem _root_.solution {ψ : AddChar k Circle} {P : Level (GL (n ⊕ Fin c) k)} {h : GL (n ⊕ Fin c) k}
    {χ χ' : prX (Cgrp P.J h) →* ℂˣ} (H : IsColChar ψ P h χ) (H' : IsColChar ψ P h χ') : χ = χ' := by
  ext g
  obtain ⟨u, hu, hc⟩ := g.2
  rw [H g u hu (mem_Cgrp.1 hc).2, H' g u hu (mem_Cgrp.1 hc).2]
end IsColChar
end GlobalTheory.StepData
