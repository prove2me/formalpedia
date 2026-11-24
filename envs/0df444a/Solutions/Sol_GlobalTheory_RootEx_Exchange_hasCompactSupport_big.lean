-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.hasCompactSupport_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:57:47.862928+00:00
-- url     : https://prove2.me/submissions/fe32aef8-cbf8-43a9-b0f6-5206a9357800

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution (ψ : AddChar k Circle) (q : Fin c) (χ : (n' → k) → ℂ)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : HasCompactSupport Φ) (x₀ : Matrix n n' k) :
    HasCompactSupport fun y => big ψ q χ Φ (mat x₀ y) := by
  haveI := t2Space k
  refine HasCompactSupport.intro
    (K := (fun (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (i : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) =>
      x i.1 i.2 - basePt c x₀ i.1 i.2) '' tsupport Φ)
    (hΦ.isCompact.image (continuous_pi fun i => (continuous_id.matrix_elem _ _).sub continuous_const))
    fun y hy => ?_
  have : Φ (mat x₀ y) = 0 := by
    by_contra h
    refine hy ⟨_, subset_tsupport _ h, ?_⟩
    funext i
    simp [mat]
  simp [big, this]
end GlobalTheory.RootEx.Exchange
