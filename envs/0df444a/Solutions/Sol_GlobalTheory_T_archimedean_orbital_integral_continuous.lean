-- Prove2me | solution 1 for GlobalTheory.T.archimedean_orbital_integral_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:43.164057+00:00
-- url     : https://prove2.me/submissions/254b9284-b9c0-4557-afad-9c88a7f51afd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanOrbitalIntegralContinuous
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanOrbitalIntegralContinuousStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_continuous_coreC_schwartz


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ)
  (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  Continuous (coreC J μ (fun X => f (e X))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz <;> assumption)
end _root_.GlobalTheory.T
