-- Prove2me | solution 1 for OAI.SharpPlanar.disk_delta_bounds_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:35:44.317024+00:00
-- url     : https://prove2.me/submissions/c0791706-030a-4338-91ee-6fcc9a5fd9b2

import Mathlib
import Definitions.Def_OAIQ098E018

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
open Complex

lemma disk_delta_bounds_e_oai {j : ℕ} (hj : j < 6) :
    167/1200 ≤ Complex.normSq ((diskCenter j:ℂ)+Complex.I*(h:ℂ))-(1/6:ℝ)^2 ∧
    Complex.normSq ((diskCenter j:ℂ)+Complex.I*(h:ℂ))-(1/6:ℝ)^2 ≤ 389/400 := by
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
  have hj5 : (j:ℝ) ≤ 5 := by exact_mod_cast (by omega : j ≤ 5)
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_mul_re,Complex.I_mul_im,
    neg_zero,add_zero,zero_add]
  unfold diskCenter h
  constructor <;> nlinarith [sq_nonneg (j:ℝ)]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.disk_delta_bounds_e_oai := @OAI.SharpPlanar.disk_delta_bounds_e_oai
