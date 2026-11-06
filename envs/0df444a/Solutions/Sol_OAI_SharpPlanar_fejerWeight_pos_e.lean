-- Prove2me | solution 1 for OAI.SharpPlanar.fejerWeight_pos_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:40:33.052209+00:00
-- url     : https://prove2.me/submissions/d9ffdd20-3d46-4096-8720-4a697e7ac3a9

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_fejer_recip_sum_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar

lemma fejerWeight_pos_e_oai (v : ℕ) : 1/(256*255:ℝ) ≤ fejerWeight v := by
  have hsum : (2:ℝ)*∑ a ∈ Finset.Icc (1:ℕ) 127,
      Real.cos (2*(a:ℝ)*fejerAngle v)/(4*(a:ℝ)^2-1) ≤ 254/255 := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ a ∈ Finset.Icc (1:ℕ) 127, (2:ℝ)/(4*(a:ℝ)^2-1) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha' : (1:ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
        have hd : 0 < 4*(a:ℝ)^2-1 := by nlinarith
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by nlinarith [Real.cos_le_one (2*(a:ℝ)*fejerAngle v)]) hd.le
      _ = 254/255 := by rw [fejer_recip_sum_e]; norm_num
  unfold fejerWeight
  linarith


end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejerWeight_pos_e_oai := @OAI.SharpPlanar.fejerWeight_pos_e_oai
