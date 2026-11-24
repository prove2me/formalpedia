-- Prove2me | solution 1 for GlobalTheory.RootEx.colE_zero_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:03:23.074582+00:00
-- url     : https://prove2.me/submissions/8d5db9dd-abe9-405f-9748-eab09e71c9bd

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
    colE c p (0 : n → k) = 1 := by
  apply Units.ext
  have hB : (Matrix.of fun (r : n) (i : Fin c) => if i.val + 1 = p then (0 : n → k) r else 0) = 0 := by
    ext r i
    simp
  show Matrix.fromBlocks 1
      (Matrix.of fun (r : n) (i : Fin c) => if i.val + 1 = p then (0 : n → k) r else 0) 0 1 = 1
  rw [hB, Matrix.fromBlocks_one]
end GlobalTheory.RootEx
