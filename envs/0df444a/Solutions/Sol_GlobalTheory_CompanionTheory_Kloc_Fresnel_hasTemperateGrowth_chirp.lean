-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.hasTemperateGrowth_chirp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:56:28.788166+00:00
-- url     : https://prove2.me/submissions/3f761803-ff36-4051-8d4d-e49db43f0218

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_hasTemperateGrowth_expI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
theorem _root_.solution (k : ℝ) : Function.HasTemperateGrowth (chirp k : V → ℂ) := by
  have h1 : Function.HasTemperateGrowth (fun u : V => 2 * Real.pi * k * ‖u‖ ^ 2) := by fun_prop
  have h2 := hasTemperateGrowth_expI.comp h1
  convert h2 using 1
  funext u
  simp only [chirp, Function.comp]
  congr 1; push_cast; ring
end GlobalTheory.CompanionTheory.Kloc.Fresnel
