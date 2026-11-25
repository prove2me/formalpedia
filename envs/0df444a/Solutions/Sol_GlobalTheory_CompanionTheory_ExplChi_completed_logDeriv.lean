-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExplChi.completed_logDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:59:45.081046+00:00
-- url     : https://prove2.me/submissions/d5ff13a0-afb4-4644-a820-ef1b750076eb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DirichletLogDerivReflectionFormula
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_ExplChi_hasDerivAt_Gamma__of_ne_8141e52e745e
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_ExplChi_Gamma__ne_zero_of_ne_fc8dfb497730

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplChi
open Complex DirichletCharacter
namespace GlobalTheory.CompanionTheory.ExplChi
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hN : N ≠ 1)
    (hχ : χ ≠ 1) {a : ℂ} (ha : χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) {z : ℂ}
    (hz : ∀ n : ℕ, (z + a) / 2 ≠ -(n : ℂ)) (hL : LFunction χ z ≠ 0) :
    completedLFunction χ z ≠ 0 ∧
      deriv (completedLFunction χ) z / completedLFunction χ z =
        -(Real.log Real.pi : ℂ) / 2 + digamma ((z + a) / 2) / 2 +
          deriv (LFunction χ) z / LFunction χ z := by
  have hgf : ∀ w, gammaFactor χ w = Gammaℝ (w + a) := by
    intro w
    rcases ha with ⟨he, rfl⟩ | ⟨ho, rfl⟩
    · rw [he.gammaFactor_def, add_zero]
    · rw [ho.gammaFactor_def]
  have hG : HasDerivAt (fun w : ℂ => Gammaℝ (w + a)) _ z :=
    (hasDerivAt_Gammaℝ_of_ne hz).comp_add_const z a
  have hGne : Gammaℝ (z + a) ≠ 0 := Gammaℝ_ne_zero_of_ne hz
  have hprod : ∀ w, Gammaℝ (w + a) ≠ 0 →
      completedLFunction χ w = Gammaℝ (w + a) * LFunction χ w := by
    intro w hw
    have h := LFunction_eq_completed_div_gammaFactor χ w (Or.inr hN)
    rw [hgf] at h
    rw [h]
    field_simp
  have hev : completedLFunction χ =ᶠ[nhds z] fun w => Gammaℝ (w + a) * LFunction χ w := by
    filter_upwards [hG.continuousAt.eventually_ne hGne] with w hw using hprod w hw
  have hder : HasDerivAt (fun w => Gammaℝ (w + a) * LFunction χ w) _ z :=
    hG.mul (differentiable_LFunction hχ z).hasDerivAt
  have hne : completedLFunction χ z ≠ 0 := by
    rw [hprod z hGne]; exact mul_ne_zero hGne hL
  refine ⟨hne, ?_⟩
  rw [hev.deriv_eq, hder.deriv, hprod z hGne]
  field_simp
end GlobalTheory.CompanionTheory.ExplChi
