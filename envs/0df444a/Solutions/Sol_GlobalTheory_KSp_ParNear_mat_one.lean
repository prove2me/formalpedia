-- Prove2me | solution 1 for GlobalTheory.KSp.ParNear.mat_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:29:11.684335+00:00
-- url     : https://prove2.me/submissions/eacdf00b-615e-44e5-9a6e-8052c3adc297

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCharacterAbsScalarEventuallyEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatFixedNearOneSiegelParabolic

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
open Filter Topology
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.ParNear
variable {E : Type} [Field E] {ν : Type} [Fintype ν] [DecidableEq ν]
variable {F : Type} [Field F] [Algebra F E] (c : E →ₐ[F] E) {α : Type} [Fintype α] [DecidableEq α]
namespace GlobalTheory.KSp.ParNear
theorem _root_.solution : mat c (1 : UG c (stdJ ν E)) = 1 := rfl
end GlobalTheory.KSp.ParNear
