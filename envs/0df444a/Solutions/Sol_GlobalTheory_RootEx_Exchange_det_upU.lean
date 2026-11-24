-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.det_upU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:57:47.102802+00:00
-- url     : https://prove2.me/submissions/162eda74-d6a6-4f0a-a3f9-fbe645b4516e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero

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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution (C : Matrix n (Fin c) k) : Matrix.GeneralLinearGroup.det (upU C) = 1 := by
  ext
  simp [upU, Matrix.GeneralLinearGroup.val_det_apply]
end GlobalTheory.RootEx.Exchange
