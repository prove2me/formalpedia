-- Prove2me | solution 1 for GroundTheory.Global.cexp_neg_two_pi_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:05.967241+00:00
-- url     : https://prove2.me/submissions/8c3c619d-f071-4cfe-929c-b78ca16a1d5e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (w : ℂ) :
    Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2) = Complex.exp (-2 * π * (w * conj w)) := by
  congr 2
  rw [mul_conj, normSq_eq_norm_sq]
  push_cast
  ring
end GroundTheory.Global
