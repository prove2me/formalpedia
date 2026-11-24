-- Prove2me | solution 1 for GlobalTheory.PosOne.ToOnePos.toOne_bil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:24:43.429688+00:00
-- url     : https://prove2.me/submissions/1ea2ef9f-d39c-4445-9cb3-246038dad991

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeToPositionOneIsPositionOne
import Theorems.Thm_GlobalTheory_PosOne_toOne_succ
import Theorems.Thm_GlobalTheory_RootEx_Exchange_exchange_isPos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
noncomputable section
open GlobalTheory GlobalTheory.PosOne GlobalTheory.PosOne.ToOnePos
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.PosOne.ToOnePos
theorem _root_.solution (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (π : Representation ℂ (GL n k) P) :
    ∀ m : ℕ, m + 1 ≤ c → ∀ b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, IsPos ψ (m + 1) π σ b →
      ∃ b₁ : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b₁ φ v = toOne ν σ (m + 1) (b φ) v) ∧ IsPos ψ 1 π σ b₁ := by
  intro m
  induction m with
  | zero => intro _ b hb; exact ⟨b, fun φ v => rfl, hb⟩
  | succ m ih =>
    intro hm b hb
    obtain ⟨b', hb'v, hb'⟩ := ((GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) (by omega) ψ hψ hψ1
      ν A σ hσ).2.2 P π b).2 hb
    obtain ⟨b₁, hb₁v, hb₁⟩ := ih (by omega) b' hb'
    refine ⟨b₁, fun φ v => ?_, hb₁⟩
    rw [hb₁v, toOne_succ]
    congr 1
    funext w
    exact hb'v φ w
end GlobalTheory.PosOne.ToOnePos
