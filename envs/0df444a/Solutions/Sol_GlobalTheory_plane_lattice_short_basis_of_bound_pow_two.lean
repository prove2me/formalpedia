-- Prove2me | solution 1 for GlobalTheory.plane_lattice_short_basis_of_bound_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:32.781942+00:00
-- url     : https://prove2.me/submissions/576323ef-4083-4072-82d1-3035f43876b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PlaneLatticeShortBasisOfBoundPowTwo
import Theorems.Thm_GlobalTheory_plane_lattice_reduction_step

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
theorem _root_.solution (n : ℕ) : ∀ e₁ e₂ : ℂ,
    ‖e₁‖ ^ 2 ≤ 2 ^ n * (2 * |((starRingEnd ℂ) e₁ * e₂).im|) →
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      ‖f₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by
  induction n with
  | zero =>
    intro e₁ e₂ h
    exact ⟨e₁, e₂, rfl, rfl, by simpa using h⟩
  | succ n ih =>
    intro e₁ e₂ h
    by_cases hc : ‖e₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im|
    · exact ⟨e₁, e₂, rfl, rfl, hc⟩
    · obtain ⟨g₁, g₂, hs, hi, hn⟩ := plane_lattice_reduction_step e₁ e₂ (not_le.mp hc)
      obtain ⟨f₁, f₂, hs', hi', hn'⟩ := ih g₁ g₂ (by
        rw [hi]
        rw [pow_succ (2 : ℝ) n] at h
        linarith)
      exact ⟨f₁, f₂, hs'.trans hs, hi'.trans hi, hi ▸ hn'⟩
end GlobalTheory
