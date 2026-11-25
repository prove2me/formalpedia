-- Prove2me | solution 1 for GlobalTheory.T.lattice_theta_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:24.639669+00:00
-- url     : https://prove2.me/submissions/2912dfa9-2164-48b2-9c4e-571982c0ee25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptotics
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptoticsStatement
import Theorems.Thm_GlobalTheory_PlaneTheta_theta_asymptotics


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) =O[atTop] (fun t => Real.exp (-c * t)) ∧ (fun t : ℝ => (∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) - 1 / (t * |(starRingEnd ℂ w₁ * w₂).im|)) =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by
  first | exact @GlobalTheory.PlaneTheta.theta_asymptotics | exact GlobalTheory.PlaneTheta.theta_asymptotics | (intros; apply GlobalTheory.PlaneTheta.theta_asymptotics <;> assumption)
end _root_.GlobalTheory.T
