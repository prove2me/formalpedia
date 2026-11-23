-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.khat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:54.065814+00:00
-- url     : https://prove2.me/submissions/be35df85-c6c0-4b92-93a6-5c187b085d94

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function
open scoped ContDiff FourierTransform
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (a r ξ : ℝ) :
    khat a r ξ = ∫ t, Complex.exp (↑(-2 * π * t * ξ) * Complex.I) * (kern a r t : ℂ) := by
  rw [khat, fourier_real_eq_integral_exp_smul]; rfl
end GroundTheory.Automorphic.LineKernel
