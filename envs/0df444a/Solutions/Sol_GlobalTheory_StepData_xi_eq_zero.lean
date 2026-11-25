-- Prove2me | solution 1 for GlobalTheory.StepData.xi_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:13:26.919191+00:00
-- url     : https://prove2.me/submissions/de53f400-0028-4b16-98eb-2e7eb27b97d9

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
  [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
  (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
omit [BorelSpace k]
namespace GlobalTheory.StepData
theorem _root_.solution {J : Subgroup (GL (n ⊕ Fin c) k)} (b : GL (n ⊕ Fin c) k) {h' : GL (n' ⊕ Fin (c + 1)) k}
    {h : GL (n ⊕ Fin c) k} (hh : DoubleCoset.mk (R k n c 1) J h ∉ idxAt ψ ν μ Φ J h') :
    xi ψ ν μ Φ J b h' h = 0 := by
  have : flat ψ ν μ Φ h' h = 0 := by_contra fun h0 => hh ⟨h, rfl, h0⟩
  funext x; simp [xi, this]
end GlobalTheory.StepData
