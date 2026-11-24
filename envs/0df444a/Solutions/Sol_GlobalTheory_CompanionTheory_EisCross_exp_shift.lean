-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisCross.exp_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:18.85549+00:00
-- url     : https://prove2.me/submissions/f3da915a-1da6-4db7-a39e-ce5f15472305

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisCross
open PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.EisCross
theorem _root_.solution (e a b A : ℝ) (h : |a - b| ≤ A) :
    Real.exp (e * a) ≤ Real.exp (|e| * A) * Real.exp (e * b) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : e * (a - b) ≤ |e| * |a - b| := by
    rw [← abs_mul]
    exact le_abs_self _
  have h2 : |e| * |a - b| ≤ |e| * A := mul_le_mul_of_nonneg_left h (abs_nonneg e)
  have h3 : e * (a - b) = e * a - e * b := by ring
  linarith
end GlobalTheory.CompanionTheory.EisCross
