-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.chirpS_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:12:13.951794+00:00
-- url     : https://prove2.me/submissions/1bd5f3ae-251a-4ac4-876e-6cf44371849a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_hasTemperateGrowth_chirp

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
theorem _root_.solution (k : ℝ) (f : 𝓢(V, ℂ)) (u : V) : chirpS k f u = chirp k u * f u := by
  simp [chirpS, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_chirp k)]
end GlobalTheory.CompanionTheory.Kloc.Fresnel
