-- Prove2me | solution 1 for GlobalTheory.PosOne.toOne_isPosOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:56.771714+00:00
-- url     : https://prove2.me/submissions/33791676-945d-47ea-873d-42956ffeda53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeToPositionOneIsPositionOne
import Theorems.Thm_GlobalTheory_PosOne_ToOnePos_toOne_lin
import Theorems.Thm_GlobalTheory_PosOne_ToOnePos_toOne_bil
import Theorems.Thm_GlobalTheory_PosOne_ToOnePos_bilPos_iff

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
open GlobalTheory.PosOne.ToOnePos
namespace GlobalTheory.PosOne
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ), (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ P σ l → ∃ l₁ : A →ₗ[ℂ] ℂ, (∀ v, l₁ v = toOne ν σ P l v) ∧ IsNEquiv ψ 1 σ l₁) ∧ ∀ (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ P σ B → ∃ B₁ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ Ψ v, B₁ Ψ v = toOne ν σ P (B Ψ) v) ∧ BilPos ψ μ 1 σ B₁ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP hPc ψ hψ hψ1 ν _ A _ _ σ hσ
  obtain ⟨m, rfl⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
  refine ⟨toOne_lin ψ hψ hψ1 ν σ hσ m hPc, fun μ hμ B hB => ?_⟩
  obtain ⟨B₁, hB₁v, hB₁⟩ := toOne_bil ψ hψ hψ1 ν σ hσ (omRep μ hμ) m hPc B ((bilPos_iff ψ μ hμ _ σ B).1 hB)
  exact ⟨B₁, hB₁v, (bilPos_iff ψ μ hμ 1 σ B₁).2 hB₁⟩
end GlobalTheory.PosOne
