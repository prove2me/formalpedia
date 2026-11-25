-- Prove2me | solution 1 for GlobalTheory.PosOneSpherical.toOne_spherical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:13:01.77497+00:00
-- url     : https://prove2.me/submissions/a0a2aa21-8165-4ddb-8326-42ae226af98e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSelfDualOfHasConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ToOneSpherical
import Theorems.Thm_GlobalTheory_RootEx_Exchange_exchange_isPos
import Theorems.Thm_GlobalTheory_RootEx_exDown_exUp_and_exUp_exDown
import Theorems.Thm_GlobalTheory_RootExchangeFixed_exUp_fixed_vector
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_ne_one
import Theorems.Thm_GlobalTheory_SplitWeil_selfDual_measure


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
open GlobalTheory GlobalTheory.PosOneSpherical
namespace GlobalTheory.PosOneSpherical
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (_ : IsNEquiv ψ P σ l) (v : A), (∀ g ∈ KO k (n ⊕ Fin c), σ g v = v) → toOne ν σ P l v = l v := by
  intro k _ _ _ _ _ _ n _ _ c P hP hPc ψ hψc hcond ν hν A _ _ σ hσ l hl v hK
  have hne : ψ ≠ 1 := hcond.ne_one
  have hsd : IsSelfDual ψ ν := ((selfDual_measure k ψ hψc hne).2.1 hcond ν).1 hν
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨m, rfl⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
  have key : ∀ m : ℕ, m + 1 ≤ c → ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ (m + 1) σ l →
      (Nat.rec (motive := fun _ => (A → ℂ) → A → ℂ) (fun l => l)
        (fun p rec l => rec (exDown ν (p + 1) σ l)) m : (A → ℂ) → A → ℂ) l v = l v := by
    intro m
    induction m with
    | zero => intro _ l _; rfl
    | succ m ih =>
      intro hm l hl
      have hlt : m + 1 < c := by omega
      obtain ⟨l', hl'v, hl'⟩ := (GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) hlt ψ hψc hne ν A σ hσ).2.1 l hl
      have hfun : exDown ν (m + 1) σ l = l' := funext fun w => (hl'v w).symm
      show (Nat.rec (motive := fun _ => (A → ℂ) → A → ℂ) (fun l => l)
        (fun p rec l => rec (exDown ν (p + 1) σ l)) m : (A → ℂ) → A → ℂ) (exDown ν (m + 1) σ l) v = l v
      rw [hfun, ih (by omega) l' hl']
      have h1 := (exDown_exUp_and_exUp_exDown k n c (m + 1) (by omega) hlt ψ hψc hne ν hsd A σ hσ l v).2 hl
      rw [hfun] at h1
      have h2 := (GlobalTheory.RootExchangeFixed.exUp_fixed_vector k n c (m + 1) (by omega) hlt ψ hcond ν hν A σ l' hl' v).2 hK
      rw [← h2, h1]
  exact key m hPc l hl
end GlobalTheory.PosOneSpherical
