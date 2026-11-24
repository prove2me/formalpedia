-- Prove2me | solution 1 for GlobalTheory.norm_eTwoPi_I_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:01.288248+00:00
-- url     : https://prove2.me/submissions/d93e4b80-1be3-4d83-b135-8ff736798563

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentCoeffNegEqZeroOfBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (y : ℝ) : ‖eTwoPi (Complex.I * y)‖ = Real.exp (-(2 * Real.pi * y)) := by
  rw [eTwoPi, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
end GlobalTheory
