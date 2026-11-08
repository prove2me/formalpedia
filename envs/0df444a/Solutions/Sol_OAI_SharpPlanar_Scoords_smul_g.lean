-- Prove2me | solution 1 for OAI.SharpPlanar.Scoords_smul_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:11:22.652625+00:00
-- url     : https://prove2.me/submissions/29bc23dd-d2a7-45c3-b5cf-e2b5edf21d8e

import Mathlib
import Definitions.Def_OAIQ098G001

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma density_positive_smul (r : ℝ) (x : X) (j : ℕ) (t : ℝ) :
    density (positiveData (r • x)) j t = (r : ℂ) * density (positiveData x) j t := by
  simp only [density, positiveData, Complex.ofReal_zero, zero_mul, zero_add,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  simp_rw [mul_assoc, ← mul_add, tsum_mul_left]

lemma K_positive_smul (r : ℝ) (x : X) (ell : ℕ) (s : ℝ) :
    K (positiveData (r • x)) ell s = r * K (positiveData x) ell s := by
  unfold K
  simp only [positiveData, Complex.ofReal_zero, zero_mul, zero_add]
  change (∑ j ∈ Finset.range 6, ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
    density (positiveData (r • x)) j t * kernelMoment ell s t).re = _
  simp_rw [density_positive_smul, mul_assoc, intervalIntegral.integral_const_mul,
    ← Finset.mul_sum]
  simp [Complex.mul_re, positiveData]


lemma Scoords_smul_g_oai (r : ℝ) (x : X) (ni : Node × Bool) :
    Scoords (r • x) ni = r * Scoords x ni := by
  unfold Scoords
  split <;> simp only [K_positive_smul] <;> ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Scoords_smul_g_oai := @OAI.SharpPlanar.Scoords_smul_g_oai
