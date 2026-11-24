-- Prove2me | solution 1 for GlobalTheory.PosOne.ToOnePos.bilPos_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:21:04.807327+00:00
-- url     : https://prove2.me/submissions/572b26c2-cd79-4523-bae9-f1660224c27d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeToPositionOneIsPositionOne

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
variable {n' : Type} [Fintype n'] [DecidableEq n']
namespace GlobalTheory.PosOne.ToOnePos
theorem _root_.solution (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) (p : ℕ)
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) : BilPos ψ μ p σ B ↔ IsPos ψ p (omRep μ hμ) σ B := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g Ψ v => h2 g Ψ _ v rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g Ψ Ψ₁ v hΨ => ?_⟩
    have : Ψ₁ = omRep μ hμ g Ψ := Subtype.ext hΨ
    subst this
    exact h2 g Ψ v
end GlobalTheory.PosOne.ToOnePos
