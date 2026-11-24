-- Prove2me | solution 1 for GlobalTheory.NarrowGauss.fourier_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:13:31.929081+00:00
-- url     : https://prove2.me/submissions/94df568d-53be-4497-97fc-81872ada1633

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartzStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NarrowGaussConvolutionDense
import Theorems.Thm_GlobalTheory_NarrowGauss_gauss_apply
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NarrowGauss
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory.NarrowGauss
theorem _root_.solution (c : ℝ) (hc : 0 < c) (w : E) :
    (𝓕 (gauss (E := E) c hc) : SchwartzMap E ℂ) w = (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
      Complex.exp (-Real.pi ^ 2 * ‖w‖ ^ 2 / c) := by
  rw [SchwartzMap.fourier_coe]
  have : (⇑(gauss c hc) : E → ℂ) = fun v ↦ Complex.exp (-(c : ℂ) * ‖v‖ ^ 2) :=
    funext (gauss_apply c hc)
  rw [this, fourier_gaussian_innerProductSpace (by simpa using hc)]
end GlobalTheory.NarrowGauss
