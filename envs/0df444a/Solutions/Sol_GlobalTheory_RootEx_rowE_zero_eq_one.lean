-- Prove2me | solution 1 for GlobalTheory.RootEx.rowE_zero_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:04:58.359624+00:00
-- url     : https://prove2.me/submissions/6c58f8f2-ade4-49dc-80fe-956c808856be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx
namespace GlobalTheory.RootEx
theorem _root_.solution {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] (c p : ℕ) :
    rowE c p (0 : n → k) = 1 := by
  apply Units.ext
  have hC : (Matrix.of fun (l : Fin c) (s : n) => if l.val + 1 = p then (0 : n → k) s else 0) = 0 := by
    ext l s
    simp
  show Matrix.fromBlocks 1 0
      (Matrix.of fun (l : Fin c) (s : n) => if l.val + 1 = p then (0 : n → k) s else 0) 1 = 1
  rw [hC, Matrix.fromBlocks_one]
end GlobalTheory.RootEx
