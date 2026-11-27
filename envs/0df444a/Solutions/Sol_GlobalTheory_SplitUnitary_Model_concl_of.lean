-- Prove2me | solution 1 for GlobalTheory.SplitUnitary.Model.concl_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:54.413792+00:00
-- url     : https://prove2.me/submissions/516d8393-e389-4a04-a51f-d3055a7d3b7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_SumSquaresNeThreeThreeAdic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ConclRankZeroRight
import Theorems.Thm_GlobalTheory_HermLocal_Model_conjSqrt_apply
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_invol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.SplitUnitary GlobalTheory.SplitUnitary.Model
open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
open GlobalTheory.HermLocal.Model (conjSqrt conjSqrt_apply)
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
namespace GlobalTheory.SplitUnitary.Model
theorem _root_.solution [CharZero F] (h : GlobalTheory.Published.KudlaSplittingSplitUnitary) {δ : E} (hE : IsQuad c δ) (Q : Matrix α α E)
    (hQ : IsHerm c Q) {ψ : AddChar F ℂ} (hψ : Continuous ψ) (h1 : ∀ t, ‖ψ t‖ = 1) (h2 : ψ ≠ 1) (χ : Eˣ →* Circle)
    (hχ : Continuous χ) (hr : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) : Concl c hE.invol ν Q hψ χ :=
  h F E c δ hE α ν Q hQ ψ hψ h1 h2 χ hχ hr
end GlobalTheory.SplitUnitary.Model
