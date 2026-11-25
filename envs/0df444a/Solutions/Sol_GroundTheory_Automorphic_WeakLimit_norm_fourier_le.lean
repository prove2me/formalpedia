-- Prove2me | solution 1 for GroundTheory.Automorphic.WeakLimit.norm_fourier_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:25.603345+00:00
-- url     : https://prove2.me/submissions/dd01d9b3-3387-4087-9c6d-e478c2d3b402

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
theorem _root_.solution (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
end GroundTheory.Automorphic.WeakLimit
