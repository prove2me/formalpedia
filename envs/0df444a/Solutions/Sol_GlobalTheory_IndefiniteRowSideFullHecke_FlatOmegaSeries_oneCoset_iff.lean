-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries.oneCoset_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:19.336153+00:00
-- url     : https://prove2.me/submissions/61e9c339-a12c-4c72-8fbe-26db105e0cf5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {P P' A : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P'] [AddCommGroup A] [Module ℂ A]
variable [MeasurableSpace k] [BorelSpace k]
omit [BorelSpace k]
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (J : Subgroup (GL (n ⊕ Fin c) k)) :
    OneCoset ψ ν μ Φ J ↔ ∀ h, flat ψ ν μ Φ 1 h ≠ 0 → ∃ r ∈ R k n c 1, ∃ κ ∈ J, h = r * κ := by
  constructor
  · intro H h hh
    have h1 : DoubleCoset.mk (R k n c 1) J h = DoubleCoset.mk (R k n c 1) J 1 := H ⟨h, rfl, hh⟩
    obtain ⟨r, hr, κ, hκ, e⟩ := (DoubleCoset.eq _ _ _ _).1 h1.symm
    exact ⟨r, hr, κ, hκ, by simpa using e⟩
  · rintro H _ ⟨h, rfl, hh⟩
    obtain ⟨r, hr, κ, hκ, e⟩ := H h hh
    exact ((DoubleCoset.eq _ _ _ _).2 ⟨r, hr, κ, hκ, by simpa using e⟩).symm
end GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
