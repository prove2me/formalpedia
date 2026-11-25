-- Prove2me | solution 1 for GlobalTheory.SymChain.exists_affPt_of_flat_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:05.945626+00:00
-- url     : https://prove2.me/submissions/b5eedc0f-8c41-4307-9adf-030eb572898b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EntriesWellDefined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_OneIndexOfOneClassOfSupportOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymChain
namespace GlobalTheory.SymChain
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c : ℕ} (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (h : GL (n ⊕ Fin c) k) (h0 : flat ψ ν μ Φ 1 h ≠ 0) :
    ∃ x₀ e, Φ ((h⁻¹).val * affPt 1 x₀ e) ≠ 0 := by
  by_contra hne
  simp only [not_exists, not_not] at hne
  apply h0
  funext x₀
  have key : ∀ e, om μ 1 h Φ (affPt 1 x₀ e) = 0 := fun e => by
    have h1 : Φ ((h⁻¹).val * affPt 1 x₀ e * (1 : GL (n' ⊕ Fin (c + 1)) k).val) = 0 := by
      rw [Units.val_one, Matrix.mul_one]; exact hne x₀ e
    exact mul_eq_zero_of_right _ h1
  unfold flat opE
  simp only [key, zero_mul, integral_zero, Pi.zero_apply]
end GlobalTheory.SymChain
