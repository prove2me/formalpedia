-- Prove2me | solution 1 for GlobalTheory.StepData.mem_Cgrp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:53:37.391691+00:00
-- url     : https://prove2.me/submissions/65414838-8ad7-4e81-8334-2882ff703f90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock

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
theorem _root_.solution {J : Subgroup (GL (n ⊕ Fin c) k)} {h x : GL (n ⊕ Fin c) k} :
    x ∈ Cgrp J h ↔ x ∈ R k n c 1 ∧ h⁻¹ * x * h ∈ J := by
  simp [Cgrp, Subgroup.mem_comap]
end GlobalTheory.StepData
