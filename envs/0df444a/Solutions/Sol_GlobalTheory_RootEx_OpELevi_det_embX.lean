-- Prove2me | solution 1 for GlobalTheory.RootEx.OpELevi.det_embX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:06:04.00056+00:00
-- url     : https://prove2.me/submissions/93353405-b471-4d9f-8762-47e73c5700d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_embX_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpELevi
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.RootEx.OpELevi
theorem _root_.solution (g : GL n k) :
    Matrix.GeneralLinearGroup.det (embX c g) = Matrix.GeneralLinearGroup.det g := by
  ext
  simp [embX_val]
end GlobalTheory.RootEx.OpELevi
