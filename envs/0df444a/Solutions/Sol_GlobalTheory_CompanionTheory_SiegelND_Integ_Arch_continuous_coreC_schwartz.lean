-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:00:07.478207+00:00
-- url     : https://prove2.me/submissions/7559edf0-0a08-4c94-bb81-4e4141995d8f

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanOrbitalIntegralContinuous
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_Cont_continuous_phaseM_X
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_Cont_continuous_phaseM_b
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_Cont_integrable_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
theorem _root_.solution
    (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ)
    (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)) (he : Continuous e)
    (hes : Continuous e.symm) (f : SchwartzMap (Fin N → ℝ) ℂ)
    (μ : Measure (W → Fin n → Fin M → ℂ)) (hμ : μ.IsAddHaarMeasure) :
    Continuous (coreC J μ (fun X => f (e X))) := by
  have hint := Cont.integrable_comp N e he hes f μ
  have hg : Continuous fun X => f (e X) := f.continuous.comp he
  have hnorm : ∀ t : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    have : (2 * Real.pi * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  unfold coreC
  refine continuous_of_dominated (bound := fun X => ‖f (e X)‖) ?_ ?_ hint.norm ?_
  · intro b
    refine Continuous.aestronglyMeasurable (hg.mul ?_)
    have := Cont.continuous_phaseM_X J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ))
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp this))
  · intro b
    refine Filter.Eventually.of_forall fun X => ?_
    rw [norm_mul, hnorm, mul_one]
  · refine Filter.Eventually.of_forall fun X => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (Cont.continuous_phaseM_b J X))))
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
