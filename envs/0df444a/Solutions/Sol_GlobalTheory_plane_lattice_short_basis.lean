-- Prove2me | solution 1 for GlobalTheory.plane_lattice_short_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:18.808+00:00
-- url     : https://prove2.me/submissions/31402861-2228-44e0-8b6d-7bca0a1e8fee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PlaneLatticeShortBasisOfBoundPowTwo
import Theorems.Thm_GlobalTheory_plane_lattice_short_basis_of_bound_pow_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ e₁ e₂ : ℂ, ((starRingEnd ℂ) e₁ * e₂).im ≠ 0 →
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      ‖f₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by
  intro e₁ e₂ h
  have hD : 0 < 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (‖e₁‖ ^ 2 / (2 * |((starRingEnd ℂ) e₁ * e₂).im|)) (one_lt_two (α := ℝ))
  exact plane_lattice_short_basis_of_bound_pow_two n e₁ e₂ ((div_lt_iff₀ hD).mp hn).le
end GlobalTheory
