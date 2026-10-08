-- Prove2me | solution 1 for MazurTransfer.order27_denominator_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T13:38:23.578345+00:00
-- url     : https://prove2.me/submissions/1806e6e3-160d-4ebb-9dad-641a17e3e770

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenLegs
import Definitions.Def_MazurTransfer_OrderTwentySevenTrisectionData
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData1
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData2
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData3
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData4
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

noncomputable section


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part00. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




/-!
# Generated third-leg chunks

This file is one load-balanced shard of the generated polynomial data used by
the order-27 third-leg certificate.
The `order27_rat%` wrapper fixes rational-operation instances during
elaboration while retaining the standard rational expressions after reduction.
-/



section

namespace MazurTorsion.Kubert

lemma quad_ne (f : ℚ) : f ^ 2 - f + 1 ≠ 0 := by
  intro h
  nlinarith [sq_nonneg (2 * f - 1)]

































































































































































































end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenLegStagesB.DenominatorNonzero. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Nonvanishing of the trisection denominator

The independent nonvanishing steps and their denominator consequence.
-/



section

namespace MazurTorsion.Kubert

lemma tl_ne_Zero {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ξ ≠ (0 : ℚ) := by
  intro hz
  subst hz
  have hval : f ^ 14 * (f - 1) ^ 7 * (f ^ 2 - f + 1) ^ 6 = 0 := by
    simp only [tlT0, tlT1, tlT2, tlT3] at hT
    linear_combination hT
  rcases mul_eq_zero.mp hval with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hf0 (pow_eq_zero_iff (by norm_num) |>.mp h')
    · exact hf1 (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h'))
  · exact quad_ne f (pow_eq_zero_iff (by norm_num) |>.mp h)

lemma tl_ne_C {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ξ ≠ f ^ 2 * (f - 1) := by
  intro hz
  subst hz
  have hval : f ^ 18 * (f - 1) ^ 18 = 0 := by
    simp only [tlT0, tlT1, tlT2, tlT3] at hT
    linear_combination hT
  rcases mul_eq_zero.mp hval with h | h
  · exact hf0 (pow_eq_zero_iff (by norm_num) |>.mp h)
  · exact hf1 (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h))

lemma tl_ne_BF {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ξ ≠ f * (f - 1) * (f ^ 2 - f + 1) := by
  intro hz
  subst hz
  have hval : f ^ 8 * (f - 1) ^ 19 * (f ^ 2 - f + 1) ^ 6 = 0 := by
    simp only [tlT0, tlT1, tlT2, tlT3] at hT
    linear_combination hT
  rcases mul_eq_zero.mp hval with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hf0 (pow_eq_zero_iff (by norm_num) |>.mp h')
    · exact hf1 (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h'))
  · exact quad_ne f (pow_eq_zero_iff (by norm_num) |>.mp h)

lemma tl_ne_B {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ξ ≠ f ^ 2 * (f - 1) * (f ^ 2 - f + 1) := by
  intro hz
  subst hz
  have hval : f ^ 20 * (f - 1) ^ 13 * (f ^ 2 - f + 1) ^ 6 = 0 := by
    simp only [tlT0, tlT1, tlT2, tlT3] at hT
    linear_combination hT
  rcases mul_eq_zero.mp hval with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hf0 (pow_eq_zero_iff (by norm_num) |>.mp h')
    · exact hf1 (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h'))
  · exact quad_ne f (pow_eq_zero_iff (by norm_num) |>.mp h)

lemma tl_d_ne {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlD0 f ξ + tlD1 f ξ) ≠ 0 := by
  have h1 := tl_ne_Zero hf0 hf1 hT
  have h2 := tl_ne_C hf0 hf1 hT
  have h3 := tl_ne_BF hf0 hf1 hT
  have h4 := tl_ne_B hf0 hf1 hT
  have hfac : (tlD0 f ξ + tlD1 f ξ) = ξ ^ 2 * (ξ - f ^ 2 * (f - 1)) ^ 2 *
      (ξ - f * (f - 1) * (f ^ 2 - f + 1)) ^ 2 *
      (ξ - f ^ 2 * (f - 1) * (f ^ 2 - f + 1)) ^ 2 := by
    simp only [tlD0, tlD1]
    ring
  rw [hfac]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (pow_ne_zero 2 h1) (pow_ne_zero 2 (sub_ne_zero.mpr h2)))
    (pow_ne_zero 2 (sub_ne_zero.mpr h3))) (pow_ne_zero 2 (sub_ne_zero.mpr h4))


end MazurTorsion.Kubert

end

end

open MazurTorsion.Kubert

theorem solution {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlD0 f ξ + tlD1 f ξ) ≠ 0  := by
  exact MazurTorsion.Kubert.tl_d_ne hf0 hf1 hT

#print axioms solution

end
