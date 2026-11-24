-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Analysis.OscPhase.hasDerivAt_integral_oscillating_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:27.817219+00:00
-- url     : https://prove2.me/submissions/52aac3c1-64e2-4482-a8ed-0c9f655944da

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierParameterDerivative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory
namespace GlobalTheory.CompanionTheory.Analysis.OscPhase
private lemma norm_exp_two_pi_I_mul_real (r : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp
end GlobalTheory.CompanionTheory.Analysis.OscPhase
end

set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Analysis GlobalTheory.CompanionTheory.Analysis.OscPhase
namespace GlobalTheory.CompanionTheory.Analysis.OscPhase
theorem _root_.solution
    (X : Type) [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) (M : X → ℝ)
    (hM : Measurable M) (hg : Integrable g μ)
    (hMg : Integrable (fun y => (M y : ℂ) * g y) μ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ y, g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) ∂μ)
      (2 * Real.pi * Complex.I * ∫ y, (M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)) ∂μ) s := by
  have hnorm : ∀ r : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := norm_exp_two_pi_I_mul_real
  have hmeasE : ∀ t : ℝ,
      Measurable fun y => Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) :=
    fun t => by fun_prop
  have hdiff : ∀ (y : X) (t : ℝ), HasDerivAt
      (fun t : ℝ => g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))
      (2 * Real.pi * Complex.I *
        ((M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))) t := by
    intro y t
    have h1 : HasDerivAt (fun t : ℝ => ((t * M y : ℝ) : ℂ)) ((M y : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_id t).mul_const (M y)).ofReal_comp
    have h2 := ((h1.const_mul (2 * Real.pi * Complex.I)).cexp).const_mul (g y)
    exact h2.congr_deriv (by ring)
  obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s)
    (F := fun (t : ℝ) y => g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)))
    (F' := fun (t : ℝ) y => 2 * Real.pi * Complex.I *
      ((M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ))))
    (bound := fun y => ‖2 * Real.pi * Complex.I‖ * ‖(M y : ℂ) * g y‖) Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      hg.aestronglyMeasurable.mul (hmeasE t).aestronglyMeasurable)
    (hg.mono (hg.aestronglyMeasurable.mul (hmeasE s).aestronglyMeasurable)
      (ae_of_all _ fun y => by rw [norm_mul, hnorm, mul_one]))
    ((hMg.aestronglyMeasurable.mul (hmeasE s).aestronglyMeasurable).const_mul _)
    (ae_of_all _ fun y t _ => by simp only [norm_mul, hnorm, mul_one, le_refl])
    (hMg.norm.const_mul _)
    (ae_of_all _ fun y t _ => hdiff y t)
  rwa [integral_const_mul] at hd
end GlobalTheory.CompanionTheory.Analysis.OscPhase
