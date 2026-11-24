-- Prove2me | solution 1 for GlobalTheory.entire_eq_zero_or_eq_zero_of_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:35.257019+00:00
-- url     : https://prove2.me/submissions/415b0e33-ae2c-4fa4-9985-853e8d93f4fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_EntireEqZeroOrEqZeroOfMulEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {g : ℕ} (A B : (Fin g → ℂ) → ℂ)
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) (hAB : ∀ z, A z * B z = 0) :
    (∀ z, A z = 0) ∨ (∀ z, B z = 0) := by
  by_cases hz : ∀ z, A z = 0
  · exact Or.inl hz
  right
  obtain ⟨z0, hz0⟩ := not_forall.1 hz
  intro z
  have hLd : Differentiable ℂ (fun t : ℂ => z0 + t • (z - z0)) := by fun_prop
  have ha : Differentiable ℂ (fun t : ℂ => A (z0 + t • (z - z0))) := hA.comp hLd
  have hb : Differentiable ℂ (fun t : ℂ => B (z0 + t • (z - z0))) := hB.comp hLd
  have ha0 : ∀ᶠ t in nhds (0 : ℂ), A (z0 + t • (z - z0)) ≠ 0 := by
    have h0 : A (z0 + (0 : ℂ) • (z - z0)) ≠ 0 := by simpa using hz0
    exact ha.continuous.continuousAt.eventually_ne h0
  have hb0 : (fun t : ℂ => B (z0 + t • (z - z0))) =ᶠ[nhds (0 : ℂ)] 0 := by
    filter_upwards [ha0] with t ht
    exact (mul_eq_zero.1 (hAB (z0 + t • (z - z0)))).resolve_left ht
  have hbA : AnalyticOnNhd ℂ (fun t : ℂ => B (z0 + t • (z - z0))) Set.univ := fun t _ => hb.analyticAt t
  have h1 := hbA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hb0
    (Set.mem_univ (1 : ℂ))
  simpa using h1
end GlobalTheory
