-- Prove2me | solution 1 for GlobalTheory.StepData.eq_mul_of_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:53:30.490655+00:00
-- url     : https://prove2.me/submissions/0d7bd5d8-ed9d-4b2a-bc8a-048ea63def90

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
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData
theorem _root_.solution {G S : Type*} [Group G] (act : G → S → S) (hact : ∀ g x, act g⁻¹ (act g x) = x)
    {f : S → ℂ} {c : G → ℂˣ} (h : ∀ g x, f x ≠ 0 → f (act g x) = c g * f x) (g : G) (x : S) :
    f (act g x) = c g * f x := by
  by_cases hx : f x = 0
  · by_contra hne
    have h1 : f (act g x) ≠ 0 := fun h0 => hne (by rw [h0, hx, mul_zero])
    have h2 := h g⁻¹ _ h1
    rw [hact, hx] at h2
    exact mul_ne_zero (Units.ne_zero _) h1 h2.symm
  · exact h g x hx
end GlobalTheory.StepData
