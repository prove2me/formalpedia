-- Prove2me | solution 1 for GlobalTheory.epsteinZeta_shifted_continuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:57.865134+00:00
-- url     : https://prove2.me/submissions/df12c654-6322-493c-b5e3-91e4771b6d5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptoticsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuation
import Theorems.Thm_GlobalTheory_summable_shiftedLattice_normSq_rpow
import Theorems.Thm_GlobalTheory_exists_entire_dirichlet_of_theta
import Theorems.Thm_GlobalTheory_T_lattice_theta_asymptotics


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open GlobalTheory
open Set MeasureTheory
open scoped Topology
namespace GlobalTheory
theorem _root_.solution : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / |(starRingEnd ℂ w₁ * w₂).im| : ℝ) ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → Summable (fun p : ℤ × ℤ => ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s)) ∧ Z s = (s - 1) * ∑' p : ℤ × ℤ, ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s) := by
  intro w₁ w₂ x₀ h hx
  obtain ⟨c, hc, htop, hbot⟩ := GlobalTheory.T.lattice_theta_asymptotics w₁ w₂ x₀ h hx
  exact exists_entire_dirichlet_of_theta
    (q := fun p : ℤ × ℤ => ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)
    (fun p => pow_pos (norm_pos_iff.mpr (hx p.1 p.2)) 2)
    (fun σ hσ => summable_shiftedLattice_normSq_rpow w₁ w₂ x₀ h hσ) hc htop hbot
end GlobalTheory
