-- Prove2me | solution 1 for GlobalTheory.KSp.ParNear.continuous_pr_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:40:05.237345+00:00
-- url     : https://prove2.me/submissions/de4a8996-5665-4d95-99d1-06d06495f083

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCharacterAbsScalarEventuallyEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatFixedNearOneSiegelParabolic
import Theorems.Thm_GlobalTheory_KSp_ParNear_continuous_pr

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
variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E]
namespace GlobalTheory.KSp.ParNear
theorem _root_.solution (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F] (Q : Matrix α α E)
    {X : Type} [TopologicalSpace X] {f g : X → Matrix α ν E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => pr c Q (f x) (g x) := by
  have h := (continuous_pr (ν := ν) c hc htr Q).comp (hf.prodMk hg)
  exact h
end GlobalTheory.KSp.ParNear
