-- Prove2me | solution 1 for GlobalTheory.T.exchangeToPositionOne_isPositionOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:44:42.677727+00:00
-- url     : https://prove2.me/submissions/a6de9cce-97a9-4b2a-ab82-41acd9ff2349

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeToPositionOneIsPositionOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeToPositionOneIsPositionOneStatement
import Theorems.Thm_GlobalTheory_PosOne_toOne_isPosOne


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ), (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ P σ l → ∃ l₁ : A →ₗ[ℂ] ℂ, (∀ v, l₁ v = toOne ν σ P l v) ∧ IsNEquiv ψ 1 σ l₁) ∧ ∀ (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ P σ B → ∃ B₁ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ Ψ v, B₁ Ψ v = toOne ν σ P (B Ψ) v) ∧ BilPos ψ μ 1 σ B₁ := by
  first | exact @GlobalTheory.PosOne.toOne_isPosOne | exact GlobalTheory.PosOne.toOne_isPosOne | (intros; apply GlobalTheory.PosOne.toOne_isPosOne <;> assumption)
end _root_.GlobalTheory.T
