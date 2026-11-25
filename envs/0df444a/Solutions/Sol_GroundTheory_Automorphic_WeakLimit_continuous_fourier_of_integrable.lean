-- Prove2me | solution 1 for GroundTheory.Automorphic.WeakLimit.continuous_fourier_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:22.334727+00:00
-- url     : https://prove2.me/submissions/245b54bf-2d67-4b20-9704-b6a9ce956cb6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Set
open scoped FourierTransform ContDiff
open GroundTheory.Automorphic.WeakLimit
namespace GroundTheory.Automorphic.WeakLimit
theorem _root_.solution {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf
end GroundTheory.Automorphic.WeakLimit
