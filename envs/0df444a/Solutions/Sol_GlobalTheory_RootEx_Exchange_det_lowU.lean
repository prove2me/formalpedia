-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.det_lowU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:57:46.429799+00:00
-- url     : https://prove2.me/submissions/70883a39-db10-4397-814c-de2cb6af2e27

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
theorem _root_.solution (C : Matrix (Fin c) n k) : Matrix.GeneralLinearGroup.det (lowU C) = 1 := by
  ext
  simp [lowU, Matrix.GeneralLinearGroup.val_det_apply]
end GlobalTheory.RootEx.Exchange
