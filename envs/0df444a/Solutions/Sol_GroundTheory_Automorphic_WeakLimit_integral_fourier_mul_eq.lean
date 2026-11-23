-- Prove2me | solution 1 for GroundTheory.Automorphic.WeakLimit.integral_fourier_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:08.97082+00:00
-- url     : https://prove2.me/submissions/f4efa827-4fbd-40fa-91c8-dc7b9829eb53

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
theorem _root_.solution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hf hg)
end GroundTheory.Automorphic.WeakLimit
