-- Prove2me | solution 1 for GlobalTheory.StepData.Chain.xiPen_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:55:59.890682+00:00
-- url     : https://prove2.me/submissions/9de68552-ecc7-4b35-9021-bb9c4b9d30a0

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
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]
open GlobalTheory.StepData.Chain
variable (T : Chain k s X Z)
variable (A : RepFam k s X)
variable (S M : Submodule 𝒪[k] (X (s + 1) → k))
variable {T A S M}
namespace GlobalTheory.StepData.Chain
theorem _root_.solution (H : T.Adapted A S M) {g : GL (X s ⊕ Fin (0 + 1)) k} (hg : g ∈ A s 0 rfl) (y : X (s + 1) → k)
    (x₀ : Matrix (X (s + 1)) (X s) k) : T.xiPen M g (Submodule.Quotient.mk y) x₀ = T.Psi g x₀ y := by
  have h1 : Quotient.out (Submodule.Quotient.mk (p := M) y) - y ∈ M :=
    (Submodule.Quotient.eq M).1 (Quotient.out_eq' _)
  rw [← (H g hg x₀ y).2 _ h1, add_sub_cancel]; rfl
end GlobalTheory.StepData.Chain
