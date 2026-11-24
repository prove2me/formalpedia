-- Prove2me | solution 1 for GlobalTheory.KSp.transvRankOne_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:35.174802+00:00
-- url     : https://prove2.me/submissions/9a575699-72bd-4bad-8ed2-286c9ed0b32f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianSplitUnitaryLowerBlockInvertible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp
variable {k : Type} [Field k] {ν : Type} [Fintype ν] [DecidableEq ν]
namespace GlobalTheory.KSp
theorem _root_.solution (S : Matrix ν ν k) (j : ν) (v : ν → k) :
    transvRankOne S j *ᵥ v = Pi.single j ((v ᵥ* S) j) := by
  funext a
  by_cases h : a = j
  · subst h; simp [transvRankOne, mulVec, vecMul, dotProduct, mul_comm]
  · simp [transvRankOne, mulVec, dotProduct, h]
end GlobalTheory.KSp
