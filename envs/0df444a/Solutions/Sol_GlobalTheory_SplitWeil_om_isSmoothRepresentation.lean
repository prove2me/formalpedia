-- Prove2me | solution 1 for GlobalTheory.SplitWeil.om_isSmoothRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:35:13.525692+00:00
-- url     : https://prove2.me/submissions/f460ab01-47c0-4c9f-aa25-9157b8a99694

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Theorems.Thm_GlobalTheory_SplitWeil_om_smul_add
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_stabilizer_om
import Theorems.Thm_GlobalTheory_SplitWeil_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_om_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.SplitWeil
namespace GlobalTheory.SplitWeil
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)), (∀ Φ : Matrix b a k → ℂ, om μ 1 1 Φ = Φ) ∧ (∀ (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ), om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ)) ∧ (∀ (g : GL a k) (h : GL b k) (z : ℂ) (Φ Ψ : Matrix b a k → ℂ), om μ g h (z • Φ + Ψ) = z • om μ g h Φ + om μ g h Ψ) ∧ (∀ (g : GL a k) (h : GL b k), ∀ Φ ∈ SB (Matrix b a k), om μ g h Φ ∈ SB (Matrix b a k)) ∧ ∀ Φ ∈ SB (Matrix b a k), IsOpen {gh : GL a k × GL b k | om μ gh.1 gh.2 Φ = Φ} :=
  fun _ _ _ _ _ _ _ _ _ _ _ μ hμ =>
    ⟨om_one μ, om_mul μ, om_smul_add μ, fun g h _ hΦ => om_mem_SB μ g h hΦ,
      fun _ hΦ => isOpen_stabilizer_om hμ hΦ⟩
end GlobalTheory.SplitWeil
