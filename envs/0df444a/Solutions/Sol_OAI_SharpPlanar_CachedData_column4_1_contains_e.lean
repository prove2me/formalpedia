-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.column4_1_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:24:45.999193+00:00
-- url     : https://prove2.me/submissions/76cc9ce4-decb-4bd8-9267-2717dfa745eb

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a11_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a5_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b10_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b1_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b2_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b3_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b5_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b6_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b9_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weightRows_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_neg_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_ofReal_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar.IntegerIntervals

lemma rcast_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (rcast a).Contains (x:ℂ) := CBox.ofReal_contains_e hx

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma phase12_periodic (n : ℕ) : phase12 (n+12) = phase12 n := by
  unfold phase12
  have he : Complex.I*Real.pi*(((n+12:ℕ):ℂ)/6) =
      Complex.I*Real.pi*((n:ℂ)/6)+2*Real.pi*Complex.I := by push_cast <;> ring
  rw [he,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
lemma phase12_mod (n : ℕ) : phase12 (n%12) = phase12 n :=
  (show Function.Periodic phase12 12 from phase12_periodic).map_mod_nat n

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma u_factored (n j : ℕ) (t : ℝ) : u n j t =
    -2*(Real.pi:ℂ)^2*Complex.exp (-Complex.I*Real.pi*t*n)*
      (basisBeta n j-(t:ℂ)*basisAlpha n j) := by
  unfold u basisBeta basisAlpha spectralCoefficient
  congr 1
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring
lemma v_factored (n j : ℕ) (t : ℝ) : v n j t =
    2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n)*basisAlpha n j := by
  unfold v basisAlpha spectralCoefficient
  rfl

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma spectralCoefficient_eq_phase (n l : ℕ) :
    spectralCoefficient n l = Pcoeff l*phase12 (l*n) := by
  unfold spectralCoefficient phase12
  congr 2
  push_cast
  ring
lemma spectralCoefficient_mod (n l : ℕ) :
    spectralCoefficient (n%12) l = spectralCoefficient n l := by
  simp only [spectralCoefficient_eq_phase]
  rw [← phase12_mod (l*(n%12)),← phase12_mod (l*n)]
  congr 2
  simp only [Nat.mul_mod, Nat.mod_mod]
lemma basisAlpha_mod (n j : ℕ) : basisAlpha (n%12) j = basisAlpha n j := by
  unfold basisAlpha
  simp only [spectralCoefficient_mod]
lemma basisBeta_mod (n j : ℕ) : basisBeta (n%12) j = basisBeta n j := by
  unfold basisBeta
  simp only [spectralCoefficient_mod]

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow0_contains (j : Fin 6) : (aRow0 j).Contains (basisAlpha 0 j.val) := by
  fin_cases j
  · exact a0_0_contains_e
  · exact a0_1_contains_e
  · exact a0_2_contains_e
  · exact a0_3_contains_e
  · exact a0_4_contains_e
  · exact a0_5_contains_e
lemma bRow0_contains (j : Fin 6) : (bRow0 j).Contains (basisBeta 0 j.val) := by
  fin_cases j
  · exact b0_0_contains_e
  · exact b0_1_contains_e
  · exact b0_2_contains_e
  · exact b0_3_contains_e
  · exact b0_4_contains_e
  · exact b0_5_contains_e
lemma aRow1_contains (j : Fin 6) : (aRow1 j).Contains (basisAlpha 1 j.val) := by
  fin_cases j
  · exact a1_0_contains_e
  · exact a1_1_contains_e
  · exact a1_2_contains_e
  · exact a1_3_contains_e
  · exact a1_4_contains_e
  · exact a1_5_contains_e
lemma bRow1_contains (j : Fin 6) : (bRow1 j).Contains (basisBeta 1 j.val) := by
  fin_cases j
  · exact b1_0_contains_e
  · exact b1_1_contains_e
  · exact b1_2_contains_e
  · exact b1_3_contains_e
  · exact b1_4_contains_e
  · exact b1_5_contains_e
lemma aRow2_contains (j : Fin 6) : (aRow2 j).Contains (basisAlpha 2 j.val) := by
  fin_cases j
  · exact a2_0_contains_e
  · exact a2_1_contains_e
  · exact a2_2_contains_e
  · exact a2_3_contains_e
  · exact a2_4_contains_e
  · exact a2_5_contains_e
lemma bRow2_contains (j : Fin 6) : (bRow2 j).Contains (basisBeta 2 j.val) := by
  fin_cases j
  · exact b2_0_contains_e
  · exact b2_1_contains_e
  · exact b2_2_contains_e
  · exact b2_3_contains_e
  · exact b2_4_contains_e
  · exact b2_5_contains_e
lemma aRow3_contains (j : Fin 6) : (aRow3 j).Contains (basisAlpha 3 j.val) := by
  fin_cases j
  · exact a3_0_contains_e
  · exact a3_1_contains_e
  · exact a3_2_contains_e
  · exact a3_3_contains_e
  · exact a3_4_contains_e
  · exact a3_5_contains_e
lemma bRow3_contains (j : Fin 6) : (bRow3 j).Contains (basisBeta 3 j.val) := by
  fin_cases j
  · exact b3_0_contains_e
  · exact b3_1_contains_e
  · exact b3_2_contains_e
  · exact b3_3_contains_e
  · exact b3_4_contains_e
  · exact b3_5_contains_e
lemma aRow4_contains (j : Fin 6) : (aRow4 j).Contains (basisAlpha 4 j.val) := by
  fin_cases j
  · exact a4_0_contains_e
  · exact a4_1_contains_e
  · exact a4_2_contains_e
  · exact a4_3_contains_e
  · exact a4_4_contains_e
  · exact a4_5_contains_e
lemma bRow4_contains (j : Fin 6) : (bRow4 j).Contains (basisBeta 4 j.val) := by
  fin_cases j
  · exact b4_0_contains_e
  · exact b4_1_contains_e
  · exact b4_2_contains_e
  · exact b4_3_contains_e
  · exact b4_4_contains_e
  · exact b4_5_contains_e
lemma aRow5_contains (j : Fin 6) : (aRow5 j).Contains (basisAlpha 5 j.val) := by
  fin_cases j
  · exact a5_0_contains_e
  · exact a5_1_contains_e
  · exact a5_2_contains_e
  · exact a5_3_contains_e
  · exact a5_4_contains_e
  · exact a5_5_contains_e
lemma bRow5_contains (j : Fin 6) : (bRow5 j).Contains (basisBeta 5 j.val) := by
  fin_cases j
  · exact b5_0_contains_e
  · exact b5_1_contains_e
  · exact b5_2_contains_e
  · exact b5_3_contains_e
  · exact b5_4_contains_e
  · exact b5_5_contains_e
lemma aRow6_contains (j : Fin 6) : (aRow6 j).Contains (basisAlpha 6 j.val) := by
  fin_cases j
  · exact a6_0_contains_e
  · exact a6_1_contains_e
  · exact a6_2_contains_e
  · exact a6_3_contains_e
  · exact a6_4_contains_e
  · exact a6_5_contains_e
lemma bRow6_contains (j : Fin 6) : (bRow6 j).Contains (basisBeta 6 j.val) := by
  fin_cases j
  · exact b6_0_contains_e
  · exact b6_1_contains_e
  · exact b6_2_contains_e
  · exact b6_3_contains_e
  · exact b6_4_contains_e
  · exact b6_5_contains_e
lemma aRow7_contains (j : Fin 6) : (aRow7 j).Contains (basisAlpha 7 j.val) := by
  fin_cases j
  · exact a7_0_contains_e
  · exact a7_1_contains_e
  · exact a7_2_contains_e
  · exact a7_3_contains_e
  · exact a7_4_contains_e
  · exact a7_5_contains_e
lemma bRow7_contains (j : Fin 6) : (bRow7 j).Contains (basisBeta 7 j.val) := by
  fin_cases j
  · exact b7_0_contains_e
  · exact b7_1_contains_e
  · exact b7_2_contains_e
  · exact b7_3_contains_e
  · exact b7_4_contains_e
  · exact b7_5_contains_e
lemma aRow8_contains (j : Fin 6) : (aRow8 j).Contains (basisAlpha 8 j.val) := by
  fin_cases j
  · exact a8_0_contains_e
  · exact a8_1_contains_e
  · exact a8_2_contains_e
  · exact a8_3_contains_e
  · exact a8_4_contains_e
  · exact a8_5_contains_e
lemma bRow8_contains (j : Fin 6) : (bRow8 j).Contains (basisBeta 8 j.val) := by
  fin_cases j
  · exact b8_0_contains_e
  · exact b8_1_contains_e
  · exact b8_2_contains_e
  · exact b8_3_contains_e
  · exact b8_4_contains_e
  · exact b8_5_contains_e
lemma aRow9_contains (j : Fin 6) : (aRow9 j).Contains (basisAlpha 9 j.val) := by
  fin_cases j
  · exact a9_0_contains_e
  · exact a9_1_contains_e
  · exact a9_2_contains_e
  · exact a9_3_contains_e
  · exact a9_4_contains_e
  · exact a9_5_contains_e
lemma bRow9_contains (j : Fin 6) : (bRow9 j).Contains (basisBeta 9 j.val) := by
  fin_cases j
  · exact b9_0_contains_e
  · exact b9_1_contains_e
  · exact b9_2_contains_e
  · exact b9_3_contains_e
  · exact b9_4_contains_e
  · exact b9_5_contains_e
lemma aRow10_contains (j : Fin 6) : (aRow10 j).Contains (basisAlpha 10 j.val) := by
  fin_cases j
  · exact a10_0_contains_e
  · exact a10_1_contains_e
  · exact a10_2_contains_e
  · exact a10_3_contains_e
  · exact a10_4_contains_e
  · exact a10_5_contains_e
lemma bRow10_contains (j : Fin 6) : (bRow10 j).Contains (basisBeta 10 j.val) := by
  fin_cases j
  · exact b10_0_contains_e
  · exact b10_1_contains_e
  · exact b10_2_contains_e
  · exact b10_3_contains_e
  · exact b10_4_contains_e
  · exact b10_5_contains_e
lemma aRow11_contains (j : Fin 6) : (aRow11 j).Contains (basisAlpha 11 j.val) := by
  fin_cases j
  · exact a11_0_contains_e
  · exact a11_1_contains_e
  · exact a11_2_contains_e
  · exact a11_3_contains_e
  · exact a11_4_contains_e
  · exact a11_5_contains_e
lemma bRow11_contains (j : Fin 6) : (bRow11 j).Contains (basisBeta 11 j.val) := by
  fin_cases j
  · exact b11_0_contains_e
  · exact b11_1_contains_e
  · exact b11_2_contains_e
  · exact b11_3_contains_e
  · exact b11_4_contains_e
  · exact b11_5_contains_e
lemma aTable_contains (n : Fin 12) (j : Fin 6) : (aTable n j).Contains (basisAlpha n.val j.val) := by
  fin_cases n
  · exact aRow0_contains j
  · exact aRow1_contains j
  · exact aRow2_contains j
  · exact aRow3_contains j
  · exact aRow4_contains j
  · exact aRow5_contains j
  · exact aRow6_contains j
  · exact aRow7_contains j
  · exact aRow8_contains j
  · exact aRow9_contains j
  · exact aRow10_contains j
  · exact aRow11_contains j
lemma aLookup_contains (n : ℕ) (j : Fin 6) : (aLookup n j).Contains (basisAlpha n j.val) := by
  simpa only [aLookup,basisAlpha_mod] using aTable_contains ⟨n%12,by omega⟩ j
lemma bTable_contains (n : Fin 12) (j : Fin 6) : (bTable n j).Contains (basisBeta n.val j.val) := by
  fin_cases n
  · exact bRow0_contains j
  · exact bRow1_contains j
  · exact bRow2_contains j
  · exact bRow3_contains j
  · exact bRow4_contains j
  · exact bRow5_contains j
  · exact bRow6_contains j
  · exact bRow7_contains j
  · exact bRow8_contains j
  · exact bRow9_contains j
  · exact bRow10_contains j
  · exact bRow11_contains j
lemma bLookup_contains (n : ℕ) (j : Fin 6) : (bLookup n j).Contains (basisBeta n j.val) := by
  simpa only [bLookup,basisBeta_mod] using bTable_contains ⟨n%12,by omega⟩ j
end SharpPlanar.IntegerAlpha

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma exp_direct_step {p q : CBox} {t : ℝ} {n : ℕ}
    (hp : p.Contains (Complex.exp (-Complex.I*Real.pi*t*n)))
    (hq : q.Contains (Complex.exp (-Complex.I*Real.pi*t))) :
    (p.mul q).Contains (Complex.exp (-Complex.I*Real.pi*t*(n+1))) := by
  have hh := CBox.contains_mul_e hp hq
  rw [← Complex.exp_add] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring
lemma waveAmplitude_mod (d : Bool) (n j : ℕ) (t : ℝ) :
    waveAmplitude d (n%12) j t = waveAmplitude d n j t := by
  simp only [waveAmplitude,basisAlpha_mod,basisBeta_mod]
lemma basisFunction_wave (d : Bool) (n j : ℕ) (t : ℝ) :
    basisFunction d n j t = waveAmplitude d n j t*Complex.exp (-Complex.I*Real.pi*t*n) := by
  cases d <;> simp only [basisFunction,waveAmplitude,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  · rw [u_factored]; ring
  · rw [v_factored]; ring
lemma waveAmplitudeBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t)
    {a b : CBox} {n j : ℕ} (ha : a.Contains (basisAlpha n j))
    (hb : b.Contains (basisBeta n j)) (d : Bool) :
    (waveAmplitudeBox p a b d).Contains (waveAmplitude d n j t) := by
  cases d
  · have hh := CBox.contains_mul_e
      (CBox.contains_scale_e (CBox.contains_mul_e (rcast_contains piBounds_contains_e)
        (rcast_contains piBounds_contains_e)) (-2) 1 (by norm_num))
      (CBox.contains_add_e hb (CBox.neg_contains_e (CBox.contains_mul_e (rcast_contains hp.1) ha)))
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [waveAmplitudeBox,waveAmplitude,Bool.false_eq_true,ite_false, if_false,Int.cast_neg,Int.cast_ofNat,Int.cast_one] <;> ring)
  · have hh := CBox.contains_mul_e (CBox.contains_scale_e piI_contains_e 2 1 (by norm_num)) ha
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [waveAmplitudeBox,waveAmplitude,ite_true, if_true,Int.cast_ofNat,Int.cast_one] <;> ring)

end SharpPlanar.IntegerBasis

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Amplitudes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma amp4_10_0_eq : ∀ k : Fin 16, amp4_1Expr 0 0 k = amp4_10_0 k := by decide +kernel
lemma amp4_10_1_eq : ∀ k : Fin 16, amp4_1Expr 0 1 k = amp4_10_1 k := by decide +kernel
lemma amp4_10_2_eq : ∀ k : Fin 16, amp4_1Expr 0 2 k = amp4_10_2 k := by decide +kernel
lemma amp4_10_3_eq : ∀ k : Fin 16, amp4_1Expr 0 3 k = amp4_10_3 k := by decide +kernel
lemma amp4_10_4_eq : ∀ k : Fin 16, amp4_1Expr 0 4 k = amp4_10_4 k := by decide +kernel
lemma amp4_10_5_eq : ∀ k : Fin 16, amp4_1Expr 0 5 k = amp4_10_5 k := by decide +kernel
lemma amp4_10_6_eq : ∀ k : Fin 16, amp4_1Expr 0 6 k = amp4_10_6 k := by decide +kernel
lemma amp4_10_7_eq : ∀ k : Fin 16, amp4_1Expr 0 7 k = amp4_10_7 k := by decide +kernel
lemma amp4_10_8_eq : ∀ k : Fin 16, amp4_1Expr 0 8 k = amp4_10_8 k := by decide +kernel
lemma amp4_10_9_eq : ∀ k : Fin 16, amp4_1Expr 0 9 k = amp4_10_9 k := by decide +kernel
lemma amp4_10_10_eq : ∀ k : Fin 16, amp4_1Expr 0 10 k = amp4_10_10 k := by decide +kernel
lemma amp4_10_11_eq : ∀ k : Fin 16, amp4_1Expr 0 11 k = amp4_10_11 k := by decide +kernel
lemma amp4_10_12_eq : ∀ k : Fin 16, amp4_1Expr 0 12 k = amp4_10_12 k := by decide +kernel
lemma amp4_10_13_eq : ∀ k : Fin 16, amp4_1Expr 0 13 k = amp4_10_13 k := by decide +kernel
lemma amp4_10_14_eq : ∀ k : Fin 16, amp4_1Expr 0 14 k = amp4_10_14 k := by decide +kernel
lemma amp4_10_15_eq : ∀ k : Fin 16, amp4_1Expr 0 15 k = amp4_10_15 k := by decide +kernel
lemma amp4_10_eq (i k : Fin 16) : amp4_1Expr 0 i k = amp4_10 i k := by
  fin_cases i
  · exact amp4_10_0_eq k
  · exact amp4_10_1_eq k
  · exact amp4_10_2_eq k
  · exact amp4_10_3_eq k
  · exact amp4_10_4_eq k
  · exact amp4_10_5_eq k
  · exact amp4_10_6_eq k
  · exact amp4_10_7_eq k
  · exact amp4_10_8_eq k
  · exact amp4_10_9_eq k
  · exact amp4_10_10_eq k
  · exact amp4_10_11_eq k
  · exact amp4_10_12_eq k
  · exact amp4_10_13_eq k
  · exact amp4_10_14_eq k
  · exact amp4_10_15_eq k
lemma amp4_11_0_eq : ∀ k : Fin 16, amp4_1Expr 1 0 k = amp4_11_0 k := by decide +kernel
lemma amp4_11_1_eq : ∀ k : Fin 16, amp4_1Expr 1 1 k = amp4_11_1 k := by decide +kernel
lemma amp4_11_2_eq : ∀ k : Fin 16, amp4_1Expr 1 2 k = amp4_11_2 k := by decide +kernel
lemma amp4_11_3_eq : ∀ k : Fin 16, amp4_1Expr 1 3 k = amp4_11_3 k := by decide +kernel
lemma amp4_11_4_eq : ∀ k : Fin 16, amp4_1Expr 1 4 k = amp4_11_4 k := by decide +kernel
lemma amp4_11_5_eq : ∀ k : Fin 16, amp4_1Expr 1 5 k = amp4_11_5 k := by decide +kernel
lemma amp4_11_6_eq : ∀ k : Fin 16, amp4_1Expr 1 6 k = amp4_11_6 k := by decide +kernel
lemma amp4_11_7_eq : ∀ k : Fin 16, amp4_1Expr 1 7 k = amp4_11_7 k := by decide +kernel
lemma amp4_11_8_eq : ∀ k : Fin 16, amp4_1Expr 1 8 k = amp4_11_8 k := by decide +kernel
lemma amp4_11_9_eq : ∀ k : Fin 16, amp4_1Expr 1 9 k = amp4_11_9 k := by decide +kernel
lemma amp4_11_10_eq : ∀ k : Fin 16, amp4_1Expr 1 10 k = amp4_11_10 k := by decide +kernel
lemma amp4_11_11_eq : ∀ k : Fin 16, amp4_1Expr 1 11 k = amp4_11_11 k := by decide +kernel
lemma amp4_11_12_eq : ∀ k : Fin 16, amp4_1Expr 1 12 k = amp4_11_12 k := by decide +kernel
lemma amp4_11_13_eq : ∀ k : Fin 16, amp4_1Expr 1 13 k = amp4_11_13 k := by decide +kernel
lemma amp4_11_14_eq : ∀ k : Fin 16, amp4_1Expr 1 14 k = amp4_11_14 k := by decide +kernel
lemma amp4_11_15_eq : ∀ k : Fin 16, amp4_1Expr 1 15 k = amp4_11_15 k := by decide +kernel
lemma amp4_11_eq (i k : Fin 16) : amp4_1Expr 1 i k = amp4_11 i k := by
  fin_cases i
  · exact amp4_11_0_eq k
  · exact amp4_11_1_eq k
  · exact amp4_11_2_eq k
  · exact amp4_11_3_eq k
  · exact amp4_11_4_eq k
  · exact amp4_11_5_eq k
  · exact amp4_11_6_eq k
  · exact amp4_11_7_eq k
  · exact amp4_11_8_eq k
  · exact amp4_11_9_eq k
  · exact amp4_11_10_eq k
  · exact amp4_11_11_eq k
  · exact amp4_11_12_eq k
  · exact amp4_11_13_eq k
  · exact amp4_11_14_eq k
  · exact amp4_11_15_eq k
lemma amp4_12_0_eq : ∀ k : Fin 16, amp4_1Expr 2 0 k = amp4_12_0 k := by decide +kernel
lemma amp4_12_1_eq : ∀ k : Fin 16, amp4_1Expr 2 1 k = amp4_12_1 k := by decide +kernel
lemma amp4_12_2_eq : ∀ k : Fin 16, amp4_1Expr 2 2 k = amp4_12_2 k := by decide +kernel
lemma amp4_12_3_eq : ∀ k : Fin 16, amp4_1Expr 2 3 k = amp4_12_3 k := by decide +kernel
lemma amp4_12_4_eq : ∀ k : Fin 16, amp4_1Expr 2 4 k = amp4_12_4 k := by decide +kernel
lemma amp4_12_5_eq : ∀ k : Fin 16, amp4_1Expr 2 5 k = amp4_12_5 k := by decide +kernel
lemma amp4_12_6_eq : ∀ k : Fin 16, amp4_1Expr 2 6 k = amp4_12_6 k := by decide +kernel
lemma amp4_12_7_eq : ∀ k : Fin 16, amp4_1Expr 2 7 k = amp4_12_7 k := by decide +kernel
lemma amp4_12_8_eq : ∀ k : Fin 16, amp4_1Expr 2 8 k = amp4_12_8 k := by decide +kernel
lemma amp4_12_9_eq : ∀ k : Fin 16, amp4_1Expr 2 9 k = amp4_12_9 k := by decide +kernel
lemma amp4_12_10_eq : ∀ k : Fin 16, amp4_1Expr 2 10 k = amp4_12_10 k := by decide +kernel
lemma amp4_12_11_eq : ∀ k : Fin 16, amp4_1Expr 2 11 k = amp4_12_11 k := by decide +kernel
lemma amp4_12_12_eq : ∀ k : Fin 16, amp4_1Expr 2 12 k = amp4_12_12 k := by decide +kernel
lemma amp4_12_13_eq : ∀ k : Fin 16, amp4_1Expr 2 13 k = amp4_12_13 k := by decide +kernel
lemma amp4_12_14_eq : ∀ k : Fin 16, amp4_1Expr 2 14 k = amp4_12_14 k := by decide +kernel
lemma amp4_12_15_eq : ∀ k : Fin 16, amp4_1Expr 2 15 k = amp4_12_15 k := by decide +kernel
lemma amp4_12_eq (i k : Fin 16) : amp4_1Expr 2 i k = amp4_12 i k := by
  fin_cases i
  · exact amp4_12_0_eq k
  · exact amp4_12_1_eq k
  · exact amp4_12_2_eq k
  · exact amp4_12_3_eq k
  · exact amp4_12_4_eq k
  · exact amp4_12_5_eq k
  · exact amp4_12_6_eq k
  · exact amp4_12_7_eq k
  · exact amp4_12_8_eq k
  · exact amp4_12_9_eq k
  · exact amp4_12_10_eq k
  · exact amp4_12_11_eq k
  · exact amp4_12_12_eq k
  · exact amp4_12_13_eq k
  · exact amp4_12_14_eq k
  · exact amp4_12_15_eq k
lemma amp4_13_0_eq : ∀ k : Fin 16, amp4_1Expr 3 0 k = amp4_13_0 k := by decide +kernel
lemma amp4_13_1_eq : ∀ k : Fin 16, amp4_1Expr 3 1 k = amp4_13_1 k := by decide +kernel
lemma amp4_13_2_eq : ∀ k : Fin 16, amp4_1Expr 3 2 k = amp4_13_2 k := by decide +kernel
lemma amp4_13_3_eq : ∀ k : Fin 16, amp4_1Expr 3 3 k = amp4_13_3 k := by decide +kernel
lemma amp4_13_4_eq : ∀ k : Fin 16, amp4_1Expr 3 4 k = amp4_13_4 k := by decide +kernel
lemma amp4_13_5_eq : ∀ k : Fin 16, amp4_1Expr 3 5 k = amp4_13_5 k := by decide +kernel
lemma amp4_13_6_eq : ∀ k : Fin 16, amp4_1Expr 3 6 k = amp4_13_6 k := by decide +kernel
lemma amp4_13_7_eq : ∀ k : Fin 16, amp4_1Expr 3 7 k = amp4_13_7 k := by decide +kernel
lemma amp4_13_8_eq : ∀ k : Fin 16, amp4_1Expr 3 8 k = amp4_13_8 k := by decide +kernel
lemma amp4_13_9_eq : ∀ k : Fin 16, amp4_1Expr 3 9 k = amp4_13_9 k := by decide +kernel
lemma amp4_13_10_eq : ∀ k : Fin 16, amp4_1Expr 3 10 k = amp4_13_10 k := by decide +kernel
lemma amp4_13_11_eq : ∀ k : Fin 16, amp4_1Expr 3 11 k = amp4_13_11 k := by decide +kernel
lemma amp4_13_12_eq : ∀ k : Fin 16, amp4_1Expr 3 12 k = amp4_13_12 k := by decide +kernel
lemma amp4_13_13_eq : ∀ k : Fin 16, amp4_1Expr 3 13 k = amp4_13_13 k := by decide +kernel
lemma amp4_13_14_eq : ∀ k : Fin 16, amp4_1Expr 3 14 k = amp4_13_14 k := by decide +kernel
lemma amp4_13_15_eq : ∀ k : Fin 16, amp4_1Expr 3 15 k = amp4_13_15 k := by decide +kernel
lemma amp4_13_eq (i k : Fin 16) : amp4_1Expr 3 i k = amp4_13 i k := by
  fin_cases i
  · exact amp4_13_0_eq k
  · exact amp4_13_1_eq k
  · exact amp4_13_2_eq k
  · exact amp4_13_3_eq k
  · exact amp4_13_4_eq k
  · exact amp4_13_5_eq k
  · exact amp4_13_6_eq k
  · exact amp4_13_7_eq k
  · exact amp4_13_8_eq k
  · exact amp4_13_9_eq k
  · exact amp4_13_10_eq k
  · exact amp4_13_11_eq k
  · exact amp4_13_12_eq k
  · exact amp4_13_13_eq k
  · exact amp4_13_14_eq k
  · exact amp4_13_15_eq k
lemma amp4_14_0_eq : ∀ k : Fin 16, amp4_1Expr 4 0 k = amp4_14_0 k := by decide +kernel
lemma amp4_14_1_eq : ∀ k : Fin 16, amp4_1Expr 4 1 k = amp4_14_1 k := by decide +kernel
lemma amp4_14_2_eq : ∀ k : Fin 16, amp4_1Expr 4 2 k = amp4_14_2 k := by decide +kernel
lemma amp4_14_3_eq : ∀ k : Fin 16, amp4_1Expr 4 3 k = amp4_14_3 k := by decide +kernel
lemma amp4_14_4_eq : ∀ k : Fin 16, amp4_1Expr 4 4 k = amp4_14_4 k := by decide +kernel
lemma amp4_14_5_eq : ∀ k : Fin 16, amp4_1Expr 4 5 k = amp4_14_5 k := by decide +kernel
lemma amp4_14_6_eq : ∀ k : Fin 16, amp4_1Expr 4 6 k = amp4_14_6 k := by decide +kernel
lemma amp4_14_7_eq : ∀ k : Fin 16, amp4_1Expr 4 7 k = amp4_14_7 k := by decide +kernel
lemma amp4_14_8_eq : ∀ k : Fin 16, amp4_1Expr 4 8 k = amp4_14_8 k := by decide +kernel
lemma amp4_14_9_eq : ∀ k : Fin 16, amp4_1Expr 4 9 k = amp4_14_9 k := by decide +kernel
lemma amp4_14_10_eq : ∀ k : Fin 16, amp4_1Expr 4 10 k = amp4_14_10 k := by decide +kernel
lemma amp4_14_11_eq : ∀ k : Fin 16, amp4_1Expr 4 11 k = amp4_14_11 k := by decide +kernel
lemma amp4_14_12_eq : ∀ k : Fin 16, amp4_1Expr 4 12 k = amp4_14_12 k := by decide +kernel
lemma amp4_14_13_eq : ∀ k : Fin 16, amp4_1Expr 4 13 k = amp4_14_13 k := by decide +kernel
lemma amp4_14_14_eq : ∀ k : Fin 16, amp4_1Expr 4 14 k = amp4_14_14 k := by decide +kernel
lemma amp4_14_15_eq : ∀ k : Fin 16, amp4_1Expr 4 15 k = amp4_14_15 k := by decide +kernel
lemma amp4_14_eq (i k : Fin 16) : amp4_1Expr 4 i k = amp4_14 i k := by
  fin_cases i
  · exact amp4_14_0_eq k
  · exact amp4_14_1_eq k
  · exact amp4_14_2_eq k
  · exact amp4_14_3_eq k
  · exact amp4_14_4_eq k
  · exact amp4_14_5_eq k
  · exact amp4_14_6_eq k
  · exact amp4_14_7_eq k
  · exact amp4_14_8_eq k
  · exact amp4_14_9_eq k
  · exact amp4_14_10_eq k
  · exact amp4_14_11_eq k
  · exact amp4_14_12_eq k
  · exact amp4_14_13_eq k
  · exact amp4_14_14_eq k
  · exact amp4_14_15_eq k
lemma amp4_15_0_eq : ∀ k : Fin 16, amp4_1Expr 5 0 k = amp4_15_0 k := by decide +kernel
lemma amp4_15_1_eq : ∀ k : Fin 16, amp4_1Expr 5 1 k = amp4_15_1 k := by decide +kernel
lemma amp4_15_2_eq : ∀ k : Fin 16, amp4_1Expr 5 2 k = amp4_15_2 k := by decide +kernel
lemma amp4_15_3_eq : ∀ k : Fin 16, amp4_1Expr 5 3 k = amp4_15_3 k := by decide +kernel
lemma amp4_15_4_eq : ∀ k : Fin 16, amp4_1Expr 5 4 k = amp4_15_4 k := by decide +kernel
lemma amp4_15_5_eq : ∀ k : Fin 16, amp4_1Expr 5 5 k = amp4_15_5 k := by decide +kernel
lemma amp4_15_6_eq : ∀ k : Fin 16, amp4_1Expr 5 6 k = amp4_15_6 k := by decide +kernel
lemma amp4_15_7_eq : ∀ k : Fin 16, amp4_1Expr 5 7 k = amp4_15_7 k := by decide +kernel
lemma amp4_15_8_eq : ∀ k : Fin 16, amp4_1Expr 5 8 k = amp4_15_8 k := by decide +kernel
lemma amp4_15_9_eq : ∀ k : Fin 16, amp4_1Expr 5 9 k = amp4_15_9 k := by decide +kernel
lemma amp4_15_10_eq : ∀ k : Fin 16, amp4_1Expr 5 10 k = amp4_15_10 k := by decide +kernel
lemma amp4_15_11_eq : ∀ k : Fin 16, amp4_1Expr 5 11 k = amp4_15_11 k := by decide +kernel
lemma amp4_15_12_eq : ∀ k : Fin 16, amp4_1Expr 5 12 k = amp4_15_12 k := by decide +kernel
lemma amp4_15_13_eq : ∀ k : Fin 16, amp4_1Expr 5 13 k = amp4_15_13 k := by decide +kernel
lemma amp4_15_14_eq : ∀ k : Fin 16, amp4_1Expr 5 14 k = amp4_15_14 k := by decide +kernel
lemma amp4_15_15_eq : ∀ k : Fin 16, amp4_1Expr 5 15 k = amp4_15_15 k := by decide +kernel
lemma amp4_15_eq (i k : Fin 16) : amp4_1Expr 5 i k = amp4_15 i k := by
  fin_cases i
  · exact amp4_15_0_eq k
  · exact amp4_15_1_eq k
  · exact amp4_15_2_eq k
  · exact amp4_15_3_eq k
  · exact amp4_15_4_eq k
  · exact amp4_15_5_eq k
  · exact amp4_15_6_eq k
  · exact amp4_15_7_eq k
  · exact amp4_15_8_eq k
  · exact amp4_15_9_eq k
  · exact amp4_15_10_eq k
  · exact amp4_15_11_eq k
  · exact amp4_15_12_eq k
  · exact amp4_15_13_eq k
  · exact amp4_15_14_eq k
  · exact amp4_15_15_eq k
lemma amp4_1_eq (j : Fin 6) (i k : Fin 16) : amp4_1Expr j i k = amp4_1 j i k := by
  fin_cases j
  · exact amp4_10_eq i k
  · exact amp4_11_eq i k
  · exact amp4_12_eq i k
  · exact amp4_13_eq i k
  · exact amp4_14_eq i k
  · exact amp4_15_eq i k
lemma amp4_1_contains (j : Fin 6) (i k : Fin 16) :
    (amp4_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*waveAmplitude true 4 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← amp4_1_eq]
  exact CBox.contains_mul_e (rcast_contains (weightRows_contains_e i k))
    (waveAmplitudeBox_contains (gridRows_contains_e j i k) (aLookup_contains 4 j) (bLookup_contains 4 j) true)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma power0_contains (j : Fin 6) (i k : Fin 16) :
    (power0 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(0:ℕ))) := by
  simpa only [power0,Nat.cast_zero,mul_zero,Complex.exp_zero,Int.cast_one,one_div,inv_one,Int.cast_zero,zero_div,mul_zero,zero_mul,add_zero] using
    (CBox.contains_rat_e 1 1 0 1 (by norm_num) (by norm_num))
lemma power1_r0_0_eq : ∀ k : Fin 16, power1Expr 0 0 k = power1_r0_0 k := by decide +kernel
lemma power1_r0_1_eq : ∀ k : Fin 16, power1Expr 0 1 k = power1_r0_1 k := by decide +kernel
lemma power1_r0_2_eq : ∀ k : Fin 16, power1Expr 0 2 k = power1_r0_2 k := by decide +kernel
lemma power1_r0_3_eq : ∀ k : Fin 16, power1Expr 0 3 k = power1_r0_3 k := by decide +kernel
lemma power1_r0_4_eq : ∀ k : Fin 16, power1Expr 0 4 k = power1_r0_4 k := by decide +kernel
lemma power1_r0_5_eq : ∀ k : Fin 16, power1Expr 0 5 k = power1_r0_5 k := by decide +kernel
lemma power1_r0_6_eq : ∀ k : Fin 16, power1Expr 0 6 k = power1_r0_6 k := by decide +kernel
lemma power1_r0_7_eq : ∀ k : Fin 16, power1Expr 0 7 k = power1_r0_7 k := by decide +kernel
lemma power1_r0_8_eq : ∀ k : Fin 16, power1Expr 0 8 k = power1_r0_8 k := by decide +kernel
lemma power1_r0_9_eq : ∀ k : Fin 16, power1Expr 0 9 k = power1_r0_9 k := by decide +kernel
lemma power1_r0_10_eq : ∀ k : Fin 16, power1Expr 0 10 k = power1_r0_10 k := by decide +kernel
lemma power1_r0_11_eq : ∀ k : Fin 16, power1Expr 0 11 k = power1_r0_11 k := by decide +kernel
lemma power1_r0_12_eq : ∀ k : Fin 16, power1Expr 0 12 k = power1_r0_12 k := by decide +kernel
lemma power1_r0_13_eq : ∀ k : Fin 16, power1Expr 0 13 k = power1_r0_13 k := by decide +kernel
lemma power1_r0_14_eq : ∀ k : Fin 16, power1Expr 0 14 k = power1_r0_14 k := by decide +kernel
lemma power1_r0_15_eq : ∀ k : Fin 16, power1Expr 0 15 k = power1_r0_15 k := by decide +kernel
lemma power1_r0_eq (i k : Fin 16) : power1Expr 0 i k = power1_r0 i k := by
  fin_cases i
  · exact power1_r0_0_eq k
  · exact power1_r0_1_eq k
  · exact power1_r0_2_eq k
  · exact power1_r0_3_eq k
  · exact power1_r0_4_eq k
  · exact power1_r0_5_eq k
  · exact power1_r0_6_eq k
  · exact power1_r0_7_eq k
  · exact power1_r0_8_eq k
  · exact power1_r0_9_eq k
  · exact power1_r0_10_eq k
  · exact power1_r0_11_eq k
  · exact power1_r0_12_eq k
  · exact power1_r0_13_eq k
  · exact power1_r0_14_eq k
  · exact power1_r0_15_eq k
lemma power1_r1_0_eq : ∀ k : Fin 16, power1Expr 1 0 k = power1_r1_0 k := by decide +kernel
lemma power1_r1_1_eq : ∀ k : Fin 16, power1Expr 1 1 k = power1_r1_1 k := by decide +kernel
lemma power1_r1_2_eq : ∀ k : Fin 16, power1Expr 1 2 k = power1_r1_2 k := by decide +kernel
lemma power1_r1_3_eq : ∀ k : Fin 16, power1Expr 1 3 k = power1_r1_3 k := by decide +kernel
lemma power1_r1_4_eq : ∀ k : Fin 16, power1Expr 1 4 k = power1_r1_4 k := by decide +kernel
lemma power1_r1_5_eq : ∀ k : Fin 16, power1Expr 1 5 k = power1_r1_5 k := by decide +kernel
lemma power1_r1_6_eq : ∀ k : Fin 16, power1Expr 1 6 k = power1_r1_6 k := by decide +kernel
lemma power1_r1_7_eq : ∀ k : Fin 16, power1Expr 1 7 k = power1_r1_7 k := by decide +kernel
lemma power1_r1_8_eq : ∀ k : Fin 16, power1Expr 1 8 k = power1_r1_8 k := by decide +kernel
lemma power1_r1_9_eq : ∀ k : Fin 16, power1Expr 1 9 k = power1_r1_9 k := by decide +kernel
lemma power1_r1_10_eq : ∀ k : Fin 16, power1Expr 1 10 k = power1_r1_10 k := by decide +kernel
lemma power1_r1_11_eq : ∀ k : Fin 16, power1Expr 1 11 k = power1_r1_11 k := by decide +kernel
lemma power1_r1_12_eq : ∀ k : Fin 16, power1Expr 1 12 k = power1_r1_12 k := by decide +kernel
lemma power1_r1_13_eq : ∀ k : Fin 16, power1Expr 1 13 k = power1_r1_13 k := by decide +kernel
lemma power1_r1_14_eq : ∀ k : Fin 16, power1Expr 1 14 k = power1_r1_14 k := by decide +kernel
lemma power1_r1_15_eq : ∀ k : Fin 16, power1Expr 1 15 k = power1_r1_15 k := by decide +kernel
lemma power1_r1_eq (i k : Fin 16) : power1Expr 1 i k = power1_r1 i k := by
  fin_cases i
  · exact power1_r1_0_eq k
  · exact power1_r1_1_eq k
  · exact power1_r1_2_eq k
  · exact power1_r1_3_eq k
  · exact power1_r1_4_eq k
  · exact power1_r1_5_eq k
  · exact power1_r1_6_eq k
  · exact power1_r1_7_eq k
  · exact power1_r1_8_eq k
  · exact power1_r1_9_eq k
  · exact power1_r1_10_eq k
  · exact power1_r1_11_eq k
  · exact power1_r1_12_eq k
  · exact power1_r1_13_eq k
  · exact power1_r1_14_eq k
  · exact power1_r1_15_eq k
lemma power1_r2_0_eq : ∀ k : Fin 16, power1Expr 2 0 k = power1_r2_0 k := by decide +kernel
lemma power1_r2_1_eq : ∀ k : Fin 16, power1Expr 2 1 k = power1_r2_1 k := by decide +kernel
lemma power1_r2_2_eq : ∀ k : Fin 16, power1Expr 2 2 k = power1_r2_2 k := by decide +kernel
lemma power1_r2_3_eq : ∀ k : Fin 16, power1Expr 2 3 k = power1_r2_3 k := by decide +kernel
lemma power1_r2_4_eq : ∀ k : Fin 16, power1Expr 2 4 k = power1_r2_4 k := by decide +kernel
lemma power1_r2_5_eq : ∀ k : Fin 16, power1Expr 2 5 k = power1_r2_5 k := by decide +kernel
lemma power1_r2_6_eq : ∀ k : Fin 16, power1Expr 2 6 k = power1_r2_6 k := by decide +kernel
lemma power1_r2_7_eq : ∀ k : Fin 16, power1Expr 2 7 k = power1_r2_7 k := by decide +kernel
lemma power1_r2_8_eq : ∀ k : Fin 16, power1Expr 2 8 k = power1_r2_8 k := by decide +kernel
lemma power1_r2_9_eq : ∀ k : Fin 16, power1Expr 2 9 k = power1_r2_9 k := by decide +kernel
lemma power1_r2_10_eq : ∀ k : Fin 16, power1Expr 2 10 k = power1_r2_10 k := by decide +kernel
lemma power1_r2_11_eq : ∀ k : Fin 16, power1Expr 2 11 k = power1_r2_11 k := by decide +kernel
lemma power1_r2_12_eq : ∀ k : Fin 16, power1Expr 2 12 k = power1_r2_12 k := by decide +kernel
lemma power1_r2_13_eq : ∀ k : Fin 16, power1Expr 2 13 k = power1_r2_13 k := by decide +kernel
lemma power1_r2_14_eq : ∀ k : Fin 16, power1Expr 2 14 k = power1_r2_14 k := by decide +kernel
lemma power1_r2_15_eq : ∀ k : Fin 16, power1Expr 2 15 k = power1_r2_15 k := by decide +kernel
lemma power1_r2_eq (i k : Fin 16) : power1Expr 2 i k = power1_r2 i k := by
  fin_cases i
  · exact power1_r2_0_eq k
  · exact power1_r2_1_eq k
  · exact power1_r2_2_eq k
  · exact power1_r2_3_eq k
  · exact power1_r2_4_eq k
  · exact power1_r2_5_eq k
  · exact power1_r2_6_eq k
  · exact power1_r2_7_eq k
  · exact power1_r2_8_eq k
  · exact power1_r2_9_eq k
  · exact power1_r2_10_eq k
  · exact power1_r2_11_eq k
  · exact power1_r2_12_eq k
  · exact power1_r2_13_eq k
  · exact power1_r2_14_eq k
  · exact power1_r2_15_eq k
lemma power1_r3_0_eq : ∀ k : Fin 16, power1Expr 3 0 k = power1_r3_0 k := by decide +kernel
lemma power1_r3_1_eq : ∀ k : Fin 16, power1Expr 3 1 k = power1_r3_1 k := by decide +kernel
lemma power1_r3_2_eq : ∀ k : Fin 16, power1Expr 3 2 k = power1_r3_2 k := by decide +kernel
lemma power1_r3_3_eq : ∀ k : Fin 16, power1Expr 3 3 k = power1_r3_3 k := by decide +kernel
lemma power1_r3_4_eq : ∀ k : Fin 16, power1Expr 3 4 k = power1_r3_4 k := by decide +kernel
lemma power1_r3_5_eq : ∀ k : Fin 16, power1Expr 3 5 k = power1_r3_5 k := by decide +kernel
lemma power1_r3_6_eq : ∀ k : Fin 16, power1Expr 3 6 k = power1_r3_6 k := by decide +kernel
lemma power1_r3_7_eq : ∀ k : Fin 16, power1Expr 3 7 k = power1_r3_7 k := by decide +kernel
lemma power1_r3_8_eq : ∀ k : Fin 16, power1Expr 3 8 k = power1_r3_8 k := by decide +kernel
lemma power1_r3_9_eq : ∀ k : Fin 16, power1Expr 3 9 k = power1_r3_9 k := by decide +kernel
lemma power1_r3_10_eq : ∀ k : Fin 16, power1Expr 3 10 k = power1_r3_10 k := by decide +kernel
lemma power1_r3_11_eq : ∀ k : Fin 16, power1Expr 3 11 k = power1_r3_11 k := by decide +kernel
lemma power1_r3_12_eq : ∀ k : Fin 16, power1Expr 3 12 k = power1_r3_12 k := by decide +kernel
lemma power1_r3_13_eq : ∀ k : Fin 16, power1Expr 3 13 k = power1_r3_13 k := by decide +kernel
lemma power1_r3_14_eq : ∀ k : Fin 16, power1Expr 3 14 k = power1_r3_14 k := by decide +kernel
lemma power1_r3_15_eq : ∀ k : Fin 16, power1Expr 3 15 k = power1_r3_15 k := by decide +kernel
lemma power1_r3_eq (i k : Fin 16) : power1Expr 3 i k = power1_r3 i k := by
  fin_cases i
  · exact power1_r3_0_eq k
  · exact power1_r3_1_eq k
  · exact power1_r3_2_eq k
  · exact power1_r3_3_eq k
  · exact power1_r3_4_eq k
  · exact power1_r3_5_eq k
  · exact power1_r3_6_eq k
  · exact power1_r3_7_eq k
  · exact power1_r3_8_eq k
  · exact power1_r3_9_eq k
  · exact power1_r3_10_eq k
  · exact power1_r3_11_eq k
  · exact power1_r3_12_eq k
  · exact power1_r3_13_eq k
  · exact power1_r3_14_eq k
  · exact power1_r3_15_eq k
lemma power1_r4_0_eq : ∀ k : Fin 16, power1Expr 4 0 k = power1_r4_0 k := by decide +kernel
lemma power1_r4_1_eq : ∀ k : Fin 16, power1Expr 4 1 k = power1_r4_1 k := by decide +kernel
lemma power1_r4_2_eq : ∀ k : Fin 16, power1Expr 4 2 k = power1_r4_2 k := by decide +kernel
lemma power1_r4_3_eq : ∀ k : Fin 16, power1Expr 4 3 k = power1_r4_3 k := by decide +kernel
lemma power1_r4_4_eq : ∀ k : Fin 16, power1Expr 4 4 k = power1_r4_4 k := by decide +kernel
lemma power1_r4_5_eq : ∀ k : Fin 16, power1Expr 4 5 k = power1_r4_5 k := by decide +kernel
lemma power1_r4_6_eq : ∀ k : Fin 16, power1Expr 4 6 k = power1_r4_6 k := by decide +kernel
lemma power1_r4_7_eq : ∀ k : Fin 16, power1Expr 4 7 k = power1_r4_7 k := by decide +kernel
lemma power1_r4_8_eq : ∀ k : Fin 16, power1Expr 4 8 k = power1_r4_8 k := by decide +kernel
lemma power1_r4_9_eq : ∀ k : Fin 16, power1Expr 4 9 k = power1_r4_9 k := by decide +kernel
lemma power1_r4_10_eq : ∀ k : Fin 16, power1Expr 4 10 k = power1_r4_10 k := by decide +kernel
lemma power1_r4_11_eq : ∀ k : Fin 16, power1Expr 4 11 k = power1_r4_11 k := by decide +kernel
lemma power1_r4_12_eq : ∀ k : Fin 16, power1Expr 4 12 k = power1_r4_12 k := by decide +kernel
lemma power1_r4_13_eq : ∀ k : Fin 16, power1Expr 4 13 k = power1_r4_13 k := by decide +kernel
lemma power1_r4_14_eq : ∀ k : Fin 16, power1Expr 4 14 k = power1_r4_14 k := by decide +kernel
lemma power1_r4_15_eq : ∀ k : Fin 16, power1Expr 4 15 k = power1_r4_15 k := by decide +kernel
lemma power1_r4_eq (i k : Fin 16) : power1Expr 4 i k = power1_r4 i k := by
  fin_cases i
  · exact power1_r4_0_eq k
  · exact power1_r4_1_eq k
  · exact power1_r4_2_eq k
  · exact power1_r4_3_eq k
  · exact power1_r4_4_eq k
  · exact power1_r4_5_eq k
  · exact power1_r4_6_eq k
  · exact power1_r4_7_eq k
  · exact power1_r4_8_eq k
  · exact power1_r4_9_eq k
  · exact power1_r4_10_eq k
  · exact power1_r4_11_eq k
  · exact power1_r4_12_eq k
  · exact power1_r4_13_eq k
  · exact power1_r4_14_eq k
  · exact power1_r4_15_eq k
lemma power1_r5_0_eq : ∀ k : Fin 16, power1Expr 5 0 k = power1_r5_0 k := by decide +kernel
lemma power1_r5_1_eq : ∀ k : Fin 16, power1Expr 5 1 k = power1_r5_1 k := by decide +kernel
lemma power1_r5_2_eq : ∀ k : Fin 16, power1Expr 5 2 k = power1_r5_2 k := by decide +kernel
lemma power1_r5_3_eq : ∀ k : Fin 16, power1Expr 5 3 k = power1_r5_3 k := by decide +kernel
lemma power1_r5_4_eq : ∀ k : Fin 16, power1Expr 5 4 k = power1_r5_4 k := by decide +kernel
lemma power1_r5_5_eq : ∀ k : Fin 16, power1Expr 5 5 k = power1_r5_5 k := by decide +kernel
lemma power1_r5_6_eq : ∀ k : Fin 16, power1Expr 5 6 k = power1_r5_6 k := by decide +kernel
lemma power1_r5_7_eq : ∀ k : Fin 16, power1Expr 5 7 k = power1_r5_7 k := by decide +kernel
lemma power1_r5_8_eq : ∀ k : Fin 16, power1Expr 5 8 k = power1_r5_8 k := by decide +kernel
lemma power1_r5_9_eq : ∀ k : Fin 16, power1Expr 5 9 k = power1_r5_9 k := by decide +kernel
lemma power1_r5_10_eq : ∀ k : Fin 16, power1Expr 5 10 k = power1_r5_10 k := by decide +kernel
lemma power1_r5_11_eq : ∀ k : Fin 16, power1Expr 5 11 k = power1_r5_11 k := by decide +kernel
lemma power1_r5_12_eq : ∀ k : Fin 16, power1Expr 5 12 k = power1_r5_12 k := by decide +kernel
lemma power1_r5_13_eq : ∀ k : Fin 16, power1Expr 5 13 k = power1_r5_13 k := by decide +kernel
lemma power1_r5_14_eq : ∀ k : Fin 16, power1Expr 5 14 k = power1_r5_14 k := by decide +kernel
lemma power1_r5_15_eq : ∀ k : Fin 16, power1Expr 5 15 k = power1_r5_15 k := by decide +kernel
lemma power1_r5_eq (i k : Fin 16) : power1Expr 5 i k = power1_r5 i k := by
  fin_cases i
  · exact power1_r5_0_eq k
  · exact power1_r5_1_eq k
  · exact power1_r5_2_eq k
  · exact power1_r5_3_eq k
  · exact power1_r5_4_eq k
  · exact power1_r5_5_eq k
  · exact power1_r5_6_eq k
  · exact power1_r5_7_eq k
  · exact power1_r5_8_eq k
  · exact power1_r5_9_eq k
  · exact power1_r5_10_eq k
  · exact power1_r5_11_eq k
  · exact power1_r5_12_eq k
  · exact power1_r5_13_eq k
  · exact power1_r5_14_eq k
  · exact power1_r5_15_eq k
lemma power1_eq (j : Fin 6) (i k : Fin 16) : power1Expr j i k = power1 j i k := by
  fin_cases j
  · exact power1_r0_eq i k
  · exact power1_r1_eq i k
  · exact power1_r2_eq i k
  · exact power1_r3_eq i k
  · exact power1_r4_eq i k
  · exact power1_r5_eq i k
lemma power1_contains (j : Fin 6) (i k : Fin 16) :
    (power1 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(1:ℕ))) := by
  rw [← power1_eq]
  unfold power1Expr
  convert exp_direct_step (power0_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power2_r0_0_eq : ∀ k : Fin 16, power2Expr 0 0 k = power2_r0_0 k := by decide +kernel
lemma power2_r0_1_eq : ∀ k : Fin 16, power2Expr 0 1 k = power2_r0_1 k := by decide +kernel
lemma power2_r0_2_eq : ∀ k : Fin 16, power2Expr 0 2 k = power2_r0_2 k := by decide +kernel
lemma power2_r0_3_eq : ∀ k : Fin 16, power2Expr 0 3 k = power2_r0_3 k := by decide +kernel
lemma power2_r0_4_eq : ∀ k : Fin 16, power2Expr 0 4 k = power2_r0_4 k := by decide +kernel
lemma power2_r0_5_eq : ∀ k : Fin 16, power2Expr 0 5 k = power2_r0_5 k := by decide +kernel
lemma power2_r0_6_eq : ∀ k : Fin 16, power2Expr 0 6 k = power2_r0_6 k := by decide +kernel
lemma power2_r0_7_eq : ∀ k : Fin 16, power2Expr 0 7 k = power2_r0_7 k := by decide +kernel
lemma power2_r0_8_eq : ∀ k : Fin 16, power2Expr 0 8 k = power2_r0_8 k := by decide +kernel
lemma power2_r0_9_eq : ∀ k : Fin 16, power2Expr 0 9 k = power2_r0_9 k := by decide +kernel
lemma power2_r0_10_eq : ∀ k : Fin 16, power2Expr 0 10 k = power2_r0_10 k := by decide +kernel
lemma power2_r0_11_eq : ∀ k : Fin 16, power2Expr 0 11 k = power2_r0_11 k := by decide +kernel
lemma power2_r0_12_eq : ∀ k : Fin 16, power2Expr 0 12 k = power2_r0_12 k := by decide +kernel
lemma power2_r0_13_eq : ∀ k : Fin 16, power2Expr 0 13 k = power2_r0_13 k := by decide +kernel
lemma power2_r0_14_eq : ∀ k : Fin 16, power2Expr 0 14 k = power2_r0_14 k := by decide +kernel
lemma power2_r0_15_eq : ∀ k : Fin 16, power2Expr 0 15 k = power2_r0_15 k := by decide +kernel
lemma power2_r0_eq (i k : Fin 16) : power2Expr 0 i k = power2_r0 i k := by
  fin_cases i
  · exact power2_r0_0_eq k
  · exact power2_r0_1_eq k
  · exact power2_r0_2_eq k
  · exact power2_r0_3_eq k
  · exact power2_r0_4_eq k
  · exact power2_r0_5_eq k
  · exact power2_r0_6_eq k
  · exact power2_r0_7_eq k
  · exact power2_r0_8_eq k
  · exact power2_r0_9_eq k
  · exact power2_r0_10_eq k
  · exact power2_r0_11_eq k
  · exact power2_r0_12_eq k
  · exact power2_r0_13_eq k
  · exact power2_r0_14_eq k
  · exact power2_r0_15_eq k
lemma power2_r1_0_eq : ∀ k : Fin 16, power2Expr 1 0 k = power2_r1_0 k := by decide +kernel
lemma power2_r1_1_eq : ∀ k : Fin 16, power2Expr 1 1 k = power2_r1_1 k := by decide +kernel
lemma power2_r1_2_eq : ∀ k : Fin 16, power2Expr 1 2 k = power2_r1_2 k := by decide +kernel
lemma power2_r1_3_eq : ∀ k : Fin 16, power2Expr 1 3 k = power2_r1_3 k := by decide +kernel
lemma power2_r1_4_eq : ∀ k : Fin 16, power2Expr 1 4 k = power2_r1_4 k := by decide +kernel
lemma power2_r1_5_eq : ∀ k : Fin 16, power2Expr 1 5 k = power2_r1_5 k := by decide +kernel
lemma power2_r1_6_eq : ∀ k : Fin 16, power2Expr 1 6 k = power2_r1_6 k := by decide +kernel
lemma power2_r1_7_eq : ∀ k : Fin 16, power2Expr 1 7 k = power2_r1_7 k := by decide +kernel
lemma power2_r1_8_eq : ∀ k : Fin 16, power2Expr 1 8 k = power2_r1_8 k := by decide +kernel
lemma power2_r1_9_eq : ∀ k : Fin 16, power2Expr 1 9 k = power2_r1_9 k := by decide +kernel
lemma power2_r1_10_eq : ∀ k : Fin 16, power2Expr 1 10 k = power2_r1_10 k := by decide +kernel
lemma power2_r1_11_eq : ∀ k : Fin 16, power2Expr 1 11 k = power2_r1_11 k := by decide +kernel
lemma power2_r1_12_eq : ∀ k : Fin 16, power2Expr 1 12 k = power2_r1_12 k := by decide +kernel
lemma power2_r1_13_eq : ∀ k : Fin 16, power2Expr 1 13 k = power2_r1_13 k := by decide +kernel
lemma power2_r1_14_eq : ∀ k : Fin 16, power2Expr 1 14 k = power2_r1_14 k := by decide +kernel
lemma power2_r1_15_eq : ∀ k : Fin 16, power2Expr 1 15 k = power2_r1_15 k := by decide +kernel
lemma power2_r1_eq (i k : Fin 16) : power2Expr 1 i k = power2_r1 i k := by
  fin_cases i
  · exact power2_r1_0_eq k
  · exact power2_r1_1_eq k
  · exact power2_r1_2_eq k
  · exact power2_r1_3_eq k
  · exact power2_r1_4_eq k
  · exact power2_r1_5_eq k
  · exact power2_r1_6_eq k
  · exact power2_r1_7_eq k
  · exact power2_r1_8_eq k
  · exact power2_r1_9_eq k
  · exact power2_r1_10_eq k
  · exact power2_r1_11_eq k
  · exact power2_r1_12_eq k
  · exact power2_r1_13_eq k
  · exact power2_r1_14_eq k
  · exact power2_r1_15_eq k
lemma power2_r2_0_eq : ∀ k : Fin 16, power2Expr 2 0 k = power2_r2_0 k := by decide +kernel
lemma power2_r2_1_eq : ∀ k : Fin 16, power2Expr 2 1 k = power2_r2_1 k := by decide +kernel
lemma power2_r2_2_eq : ∀ k : Fin 16, power2Expr 2 2 k = power2_r2_2 k := by decide +kernel
lemma power2_r2_3_eq : ∀ k : Fin 16, power2Expr 2 3 k = power2_r2_3 k := by decide +kernel
lemma power2_r2_4_eq : ∀ k : Fin 16, power2Expr 2 4 k = power2_r2_4 k := by decide +kernel
lemma power2_r2_5_eq : ∀ k : Fin 16, power2Expr 2 5 k = power2_r2_5 k := by decide +kernel
lemma power2_r2_6_eq : ∀ k : Fin 16, power2Expr 2 6 k = power2_r2_6 k := by decide +kernel
lemma power2_r2_7_eq : ∀ k : Fin 16, power2Expr 2 7 k = power2_r2_7 k := by decide +kernel
lemma power2_r2_8_eq : ∀ k : Fin 16, power2Expr 2 8 k = power2_r2_8 k := by decide +kernel
lemma power2_r2_9_eq : ∀ k : Fin 16, power2Expr 2 9 k = power2_r2_9 k := by decide +kernel
lemma power2_r2_10_eq : ∀ k : Fin 16, power2Expr 2 10 k = power2_r2_10 k := by decide +kernel
lemma power2_r2_11_eq : ∀ k : Fin 16, power2Expr 2 11 k = power2_r2_11 k := by decide +kernel
lemma power2_r2_12_eq : ∀ k : Fin 16, power2Expr 2 12 k = power2_r2_12 k := by decide +kernel
lemma power2_r2_13_eq : ∀ k : Fin 16, power2Expr 2 13 k = power2_r2_13 k := by decide +kernel
lemma power2_r2_14_eq : ∀ k : Fin 16, power2Expr 2 14 k = power2_r2_14 k := by decide +kernel
lemma power2_r2_15_eq : ∀ k : Fin 16, power2Expr 2 15 k = power2_r2_15 k := by decide +kernel
lemma power2_r2_eq (i k : Fin 16) : power2Expr 2 i k = power2_r2 i k := by
  fin_cases i
  · exact power2_r2_0_eq k
  · exact power2_r2_1_eq k
  · exact power2_r2_2_eq k
  · exact power2_r2_3_eq k
  · exact power2_r2_4_eq k
  · exact power2_r2_5_eq k
  · exact power2_r2_6_eq k
  · exact power2_r2_7_eq k
  · exact power2_r2_8_eq k
  · exact power2_r2_9_eq k
  · exact power2_r2_10_eq k
  · exact power2_r2_11_eq k
  · exact power2_r2_12_eq k
  · exact power2_r2_13_eq k
  · exact power2_r2_14_eq k
  · exact power2_r2_15_eq k
lemma power2_r3_0_eq : ∀ k : Fin 16, power2Expr 3 0 k = power2_r3_0 k := by decide +kernel
lemma power2_r3_1_eq : ∀ k : Fin 16, power2Expr 3 1 k = power2_r3_1 k := by decide +kernel
lemma power2_r3_2_eq : ∀ k : Fin 16, power2Expr 3 2 k = power2_r3_2 k := by decide +kernel
lemma power2_r3_3_eq : ∀ k : Fin 16, power2Expr 3 3 k = power2_r3_3 k := by decide +kernel
lemma power2_r3_4_eq : ∀ k : Fin 16, power2Expr 3 4 k = power2_r3_4 k := by decide +kernel
lemma power2_r3_5_eq : ∀ k : Fin 16, power2Expr 3 5 k = power2_r3_5 k := by decide +kernel
lemma power2_r3_6_eq : ∀ k : Fin 16, power2Expr 3 6 k = power2_r3_6 k := by decide +kernel
lemma power2_r3_7_eq : ∀ k : Fin 16, power2Expr 3 7 k = power2_r3_7 k := by decide +kernel
lemma power2_r3_8_eq : ∀ k : Fin 16, power2Expr 3 8 k = power2_r3_8 k := by decide +kernel
lemma power2_r3_9_eq : ∀ k : Fin 16, power2Expr 3 9 k = power2_r3_9 k := by decide +kernel
lemma power2_r3_10_eq : ∀ k : Fin 16, power2Expr 3 10 k = power2_r3_10 k := by decide +kernel
lemma power2_r3_11_eq : ∀ k : Fin 16, power2Expr 3 11 k = power2_r3_11 k := by decide +kernel
lemma power2_r3_12_eq : ∀ k : Fin 16, power2Expr 3 12 k = power2_r3_12 k := by decide +kernel
lemma power2_r3_13_eq : ∀ k : Fin 16, power2Expr 3 13 k = power2_r3_13 k := by decide +kernel
lemma power2_r3_14_eq : ∀ k : Fin 16, power2Expr 3 14 k = power2_r3_14 k := by decide +kernel
lemma power2_r3_15_eq : ∀ k : Fin 16, power2Expr 3 15 k = power2_r3_15 k := by decide +kernel
lemma power2_r3_eq (i k : Fin 16) : power2Expr 3 i k = power2_r3 i k := by
  fin_cases i
  · exact power2_r3_0_eq k
  · exact power2_r3_1_eq k
  · exact power2_r3_2_eq k
  · exact power2_r3_3_eq k
  · exact power2_r3_4_eq k
  · exact power2_r3_5_eq k
  · exact power2_r3_6_eq k
  · exact power2_r3_7_eq k
  · exact power2_r3_8_eq k
  · exact power2_r3_9_eq k
  · exact power2_r3_10_eq k
  · exact power2_r3_11_eq k
  · exact power2_r3_12_eq k
  · exact power2_r3_13_eq k
  · exact power2_r3_14_eq k
  · exact power2_r3_15_eq k
lemma power2_r4_0_eq : ∀ k : Fin 16, power2Expr 4 0 k = power2_r4_0 k := by decide +kernel
lemma power2_r4_1_eq : ∀ k : Fin 16, power2Expr 4 1 k = power2_r4_1 k := by decide +kernel
lemma power2_r4_2_eq : ∀ k : Fin 16, power2Expr 4 2 k = power2_r4_2 k := by decide +kernel
lemma power2_r4_3_eq : ∀ k : Fin 16, power2Expr 4 3 k = power2_r4_3 k := by decide +kernel
lemma power2_r4_4_eq : ∀ k : Fin 16, power2Expr 4 4 k = power2_r4_4 k := by decide +kernel
lemma power2_r4_5_eq : ∀ k : Fin 16, power2Expr 4 5 k = power2_r4_5 k := by decide +kernel
lemma power2_r4_6_eq : ∀ k : Fin 16, power2Expr 4 6 k = power2_r4_6 k := by decide +kernel
lemma power2_r4_7_eq : ∀ k : Fin 16, power2Expr 4 7 k = power2_r4_7 k := by decide +kernel
lemma power2_r4_8_eq : ∀ k : Fin 16, power2Expr 4 8 k = power2_r4_8 k := by decide +kernel
lemma power2_r4_9_eq : ∀ k : Fin 16, power2Expr 4 9 k = power2_r4_9 k := by decide +kernel
lemma power2_r4_10_eq : ∀ k : Fin 16, power2Expr 4 10 k = power2_r4_10 k := by decide +kernel
lemma power2_r4_11_eq : ∀ k : Fin 16, power2Expr 4 11 k = power2_r4_11 k := by decide +kernel
lemma power2_r4_12_eq : ∀ k : Fin 16, power2Expr 4 12 k = power2_r4_12 k := by decide +kernel
lemma power2_r4_13_eq : ∀ k : Fin 16, power2Expr 4 13 k = power2_r4_13 k := by decide +kernel
lemma power2_r4_14_eq : ∀ k : Fin 16, power2Expr 4 14 k = power2_r4_14 k := by decide +kernel
lemma power2_r4_15_eq : ∀ k : Fin 16, power2Expr 4 15 k = power2_r4_15 k := by decide +kernel
lemma power2_r4_eq (i k : Fin 16) : power2Expr 4 i k = power2_r4 i k := by
  fin_cases i
  · exact power2_r4_0_eq k
  · exact power2_r4_1_eq k
  · exact power2_r4_2_eq k
  · exact power2_r4_3_eq k
  · exact power2_r4_4_eq k
  · exact power2_r4_5_eq k
  · exact power2_r4_6_eq k
  · exact power2_r4_7_eq k
  · exact power2_r4_8_eq k
  · exact power2_r4_9_eq k
  · exact power2_r4_10_eq k
  · exact power2_r4_11_eq k
  · exact power2_r4_12_eq k
  · exact power2_r4_13_eq k
  · exact power2_r4_14_eq k
  · exact power2_r4_15_eq k
lemma power2_r5_0_eq : ∀ k : Fin 16, power2Expr 5 0 k = power2_r5_0 k := by decide +kernel
lemma power2_r5_1_eq : ∀ k : Fin 16, power2Expr 5 1 k = power2_r5_1 k := by decide +kernel
lemma power2_r5_2_eq : ∀ k : Fin 16, power2Expr 5 2 k = power2_r5_2 k := by decide +kernel
lemma power2_r5_3_eq : ∀ k : Fin 16, power2Expr 5 3 k = power2_r5_3 k := by decide +kernel
lemma power2_r5_4_eq : ∀ k : Fin 16, power2Expr 5 4 k = power2_r5_4 k := by decide +kernel
lemma power2_r5_5_eq : ∀ k : Fin 16, power2Expr 5 5 k = power2_r5_5 k := by decide +kernel
lemma power2_r5_6_eq : ∀ k : Fin 16, power2Expr 5 6 k = power2_r5_6 k := by decide +kernel
lemma power2_r5_7_eq : ∀ k : Fin 16, power2Expr 5 7 k = power2_r5_7 k := by decide +kernel
lemma power2_r5_8_eq : ∀ k : Fin 16, power2Expr 5 8 k = power2_r5_8 k := by decide +kernel
lemma power2_r5_9_eq : ∀ k : Fin 16, power2Expr 5 9 k = power2_r5_9 k := by decide +kernel
lemma power2_r5_10_eq : ∀ k : Fin 16, power2Expr 5 10 k = power2_r5_10 k := by decide +kernel
lemma power2_r5_11_eq : ∀ k : Fin 16, power2Expr 5 11 k = power2_r5_11 k := by decide +kernel
lemma power2_r5_12_eq : ∀ k : Fin 16, power2Expr 5 12 k = power2_r5_12 k := by decide +kernel
lemma power2_r5_13_eq : ∀ k : Fin 16, power2Expr 5 13 k = power2_r5_13 k := by decide +kernel
lemma power2_r5_14_eq : ∀ k : Fin 16, power2Expr 5 14 k = power2_r5_14 k := by decide +kernel
lemma power2_r5_15_eq : ∀ k : Fin 16, power2Expr 5 15 k = power2_r5_15 k := by decide +kernel
lemma power2_r5_eq (i k : Fin 16) : power2Expr 5 i k = power2_r5 i k := by
  fin_cases i
  · exact power2_r5_0_eq k
  · exact power2_r5_1_eq k
  · exact power2_r5_2_eq k
  · exact power2_r5_3_eq k
  · exact power2_r5_4_eq k
  · exact power2_r5_5_eq k
  · exact power2_r5_6_eq k
  · exact power2_r5_7_eq k
  · exact power2_r5_8_eq k
  · exact power2_r5_9_eq k
  · exact power2_r5_10_eq k
  · exact power2_r5_11_eq k
  · exact power2_r5_12_eq k
  · exact power2_r5_13_eq k
  · exact power2_r5_14_eq k
  · exact power2_r5_15_eq k
lemma power2_eq (j : Fin 6) (i k : Fin 16) : power2Expr j i k = power2 j i k := by
  fin_cases j
  · exact power2_r0_eq i k
  · exact power2_r1_eq i k
  · exact power2_r2_eq i k
  · exact power2_r3_eq i k
  · exact power2_r4_eq i k
  · exact power2_r5_eq i k
lemma power2_contains (j : Fin 6) (i k : Fin 16) :
    (power2 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(2:ℕ))) := by
  rw [← power2_eq]
  unfold power2Expr
  convert exp_direct_step (power1_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power3_r0_0_eq : ∀ k : Fin 16, power3Expr 0 0 k = power3_r0_0 k := by decide +kernel
lemma power3_r0_1_eq : ∀ k : Fin 16, power3Expr 0 1 k = power3_r0_1 k := by decide +kernel
lemma power3_r0_2_eq : ∀ k : Fin 16, power3Expr 0 2 k = power3_r0_2 k := by decide +kernel
lemma power3_r0_3_eq : ∀ k : Fin 16, power3Expr 0 3 k = power3_r0_3 k := by decide +kernel
lemma power3_r0_4_eq : ∀ k : Fin 16, power3Expr 0 4 k = power3_r0_4 k := by decide +kernel
lemma power3_r0_5_eq : ∀ k : Fin 16, power3Expr 0 5 k = power3_r0_5 k := by decide +kernel
lemma power3_r0_6_eq : ∀ k : Fin 16, power3Expr 0 6 k = power3_r0_6 k := by decide +kernel
lemma power3_r0_7_eq : ∀ k : Fin 16, power3Expr 0 7 k = power3_r0_7 k := by decide +kernel
lemma power3_r0_8_eq : ∀ k : Fin 16, power3Expr 0 8 k = power3_r0_8 k := by decide +kernel
lemma power3_r0_9_eq : ∀ k : Fin 16, power3Expr 0 9 k = power3_r0_9 k := by decide +kernel
lemma power3_r0_10_eq : ∀ k : Fin 16, power3Expr 0 10 k = power3_r0_10 k := by decide +kernel
lemma power3_r0_11_eq : ∀ k : Fin 16, power3Expr 0 11 k = power3_r0_11 k := by decide +kernel
lemma power3_r0_12_eq : ∀ k : Fin 16, power3Expr 0 12 k = power3_r0_12 k := by decide +kernel
lemma power3_r0_13_eq : ∀ k : Fin 16, power3Expr 0 13 k = power3_r0_13 k := by decide +kernel
lemma power3_r0_14_eq : ∀ k : Fin 16, power3Expr 0 14 k = power3_r0_14 k := by decide +kernel
lemma power3_r0_15_eq : ∀ k : Fin 16, power3Expr 0 15 k = power3_r0_15 k := by decide +kernel
lemma power3_r0_eq (i k : Fin 16) : power3Expr 0 i k = power3_r0 i k := by
  fin_cases i
  · exact power3_r0_0_eq k
  · exact power3_r0_1_eq k
  · exact power3_r0_2_eq k
  · exact power3_r0_3_eq k
  · exact power3_r0_4_eq k
  · exact power3_r0_5_eq k
  · exact power3_r0_6_eq k
  · exact power3_r0_7_eq k
  · exact power3_r0_8_eq k
  · exact power3_r0_9_eq k
  · exact power3_r0_10_eq k
  · exact power3_r0_11_eq k
  · exact power3_r0_12_eq k
  · exact power3_r0_13_eq k
  · exact power3_r0_14_eq k
  · exact power3_r0_15_eq k
lemma power3_r1_0_eq : ∀ k : Fin 16, power3Expr 1 0 k = power3_r1_0 k := by decide +kernel
lemma power3_r1_1_eq : ∀ k : Fin 16, power3Expr 1 1 k = power3_r1_1 k := by decide +kernel
lemma power3_r1_2_eq : ∀ k : Fin 16, power3Expr 1 2 k = power3_r1_2 k := by decide +kernel
lemma power3_r1_3_eq : ∀ k : Fin 16, power3Expr 1 3 k = power3_r1_3 k := by decide +kernel
lemma power3_r1_4_eq : ∀ k : Fin 16, power3Expr 1 4 k = power3_r1_4 k := by decide +kernel
lemma power3_r1_5_eq : ∀ k : Fin 16, power3Expr 1 5 k = power3_r1_5 k := by decide +kernel
lemma power3_r1_6_eq : ∀ k : Fin 16, power3Expr 1 6 k = power3_r1_6 k := by decide +kernel
lemma power3_r1_7_eq : ∀ k : Fin 16, power3Expr 1 7 k = power3_r1_7 k := by decide +kernel
lemma power3_r1_8_eq : ∀ k : Fin 16, power3Expr 1 8 k = power3_r1_8 k := by decide +kernel
lemma power3_r1_9_eq : ∀ k : Fin 16, power3Expr 1 9 k = power3_r1_9 k := by decide +kernel
lemma power3_r1_10_eq : ∀ k : Fin 16, power3Expr 1 10 k = power3_r1_10 k := by decide +kernel
lemma power3_r1_11_eq : ∀ k : Fin 16, power3Expr 1 11 k = power3_r1_11 k := by decide +kernel
lemma power3_r1_12_eq : ∀ k : Fin 16, power3Expr 1 12 k = power3_r1_12 k := by decide +kernel
lemma power3_r1_13_eq : ∀ k : Fin 16, power3Expr 1 13 k = power3_r1_13 k := by decide +kernel
lemma power3_r1_14_eq : ∀ k : Fin 16, power3Expr 1 14 k = power3_r1_14 k := by decide +kernel
lemma power3_r1_15_eq : ∀ k : Fin 16, power3Expr 1 15 k = power3_r1_15 k := by decide +kernel
lemma power3_r1_eq (i k : Fin 16) : power3Expr 1 i k = power3_r1 i k := by
  fin_cases i
  · exact power3_r1_0_eq k
  · exact power3_r1_1_eq k
  · exact power3_r1_2_eq k
  · exact power3_r1_3_eq k
  · exact power3_r1_4_eq k
  · exact power3_r1_5_eq k
  · exact power3_r1_6_eq k
  · exact power3_r1_7_eq k
  · exact power3_r1_8_eq k
  · exact power3_r1_9_eq k
  · exact power3_r1_10_eq k
  · exact power3_r1_11_eq k
  · exact power3_r1_12_eq k
  · exact power3_r1_13_eq k
  · exact power3_r1_14_eq k
  · exact power3_r1_15_eq k
lemma power3_r2_0_eq : ∀ k : Fin 16, power3Expr 2 0 k = power3_r2_0 k := by decide +kernel
lemma power3_r2_1_eq : ∀ k : Fin 16, power3Expr 2 1 k = power3_r2_1 k := by decide +kernel
lemma power3_r2_2_eq : ∀ k : Fin 16, power3Expr 2 2 k = power3_r2_2 k := by decide +kernel
lemma power3_r2_3_eq : ∀ k : Fin 16, power3Expr 2 3 k = power3_r2_3 k := by decide +kernel
lemma power3_r2_4_eq : ∀ k : Fin 16, power3Expr 2 4 k = power3_r2_4 k := by decide +kernel
lemma power3_r2_5_eq : ∀ k : Fin 16, power3Expr 2 5 k = power3_r2_5 k := by decide +kernel
lemma power3_r2_6_eq : ∀ k : Fin 16, power3Expr 2 6 k = power3_r2_6 k := by decide +kernel
lemma power3_r2_7_eq : ∀ k : Fin 16, power3Expr 2 7 k = power3_r2_7 k := by decide +kernel
lemma power3_r2_8_eq : ∀ k : Fin 16, power3Expr 2 8 k = power3_r2_8 k := by decide +kernel
lemma power3_r2_9_eq : ∀ k : Fin 16, power3Expr 2 9 k = power3_r2_9 k := by decide +kernel
lemma power3_r2_10_eq : ∀ k : Fin 16, power3Expr 2 10 k = power3_r2_10 k := by decide +kernel
lemma power3_r2_11_eq : ∀ k : Fin 16, power3Expr 2 11 k = power3_r2_11 k := by decide +kernel
lemma power3_r2_12_eq : ∀ k : Fin 16, power3Expr 2 12 k = power3_r2_12 k := by decide +kernel
lemma power3_r2_13_eq : ∀ k : Fin 16, power3Expr 2 13 k = power3_r2_13 k := by decide +kernel
lemma power3_r2_14_eq : ∀ k : Fin 16, power3Expr 2 14 k = power3_r2_14 k := by decide +kernel
lemma power3_r2_15_eq : ∀ k : Fin 16, power3Expr 2 15 k = power3_r2_15 k := by decide +kernel
lemma power3_r2_eq (i k : Fin 16) : power3Expr 2 i k = power3_r2 i k := by
  fin_cases i
  · exact power3_r2_0_eq k
  · exact power3_r2_1_eq k
  · exact power3_r2_2_eq k
  · exact power3_r2_3_eq k
  · exact power3_r2_4_eq k
  · exact power3_r2_5_eq k
  · exact power3_r2_6_eq k
  · exact power3_r2_7_eq k
  · exact power3_r2_8_eq k
  · exact power3_r2_9_eq k
  · exact power3_r2_10_eq k
  · exact power3_r2_11_eq k
  · exact power3_r2_12_eq k
  · exact power3_r2_13_eq k
  · exact power3_r2_14_eq k
  · exact power3_r2_15_eq k
lemma power3_r3_0_eq : ∀ k : Fin 16, power3Expr 3 0 k = power3_r3_0 k := by decide +kernel
lemma power3_r3_1_eq : ∀ k : Fin 16, power3Expr 3 1 k = power3_r3_1 k := by decide +kernel
lemma power3_r3_2_eq : ∀ k : Fin 16, power3Expr 3 2 k = power3_r3_2 k := by decide +kernel
lemma power3_r3_3_eq : ∀ k : Fin 16, power3Expr 3 3 k = power3_r3_3 k := by decide +kernel
lemma power3_r3_4_eq : ∀ k : Fin 16, power3Expr 3 4 k = power3_r3_4 k := by decide +kernel
lemma power3_r3_5_eq : ∀ k : Fin 16, power3Expr 3 5 k = power3_r3_5 k := by decide +kernel
lemma power3_r3_6_eq : ∀ k : Fin 16, power3Expr 3 6 k = power3_r3_6 k := by decide +kernel
lemma power3_r3_7_eq : ∀ k : Fin 16, power3Expr 3 7 k = power3_r3_7 k := by decide +kernel
lemma power3_r3_8_eq : ∀ k : Fin 16, power3Expr 3 8 k = power3_r3_8 k := by decide +kernel
lemma power3_r3_9_eq : ∀ k : Fin 16, power3Expr 3 9 k = power3_r3_9 k := by decide +kernel
lemma power3_r3_10_eq : ∀ k : Fin 16, power3Expr 3 10 k = power3_r3_10 k := by decide +kernel
lemma power3_r3_11_eq : ∀ k : Fin 16, power3Expr 3 11 k = power3_r3_11 k := by decide +kernel
lemma power3_r3_12_eq : ∀ k : Fin 16, power3Expr 3 12 k = power3_r3_12 k := by decide +kernel
lemma power3_r3_13_eq : ∀ k : Fin 16, power3Expr 3 13 k = power3_r3_13 k := by decide +kernel
lemma power3_r3_14_eq : ∀ k : Fin 16, power3Expr 3 14 k = power3_r3_14 k := by decide +kernel
lemma power3_r3_15_eq : ∀ k : Fin 16, power3Expr 3 15 k = power3_r3_15 k := by decide +kernel
lemma power3_r3_eq (i k : Fin 16) : power3Expr 3 i k = power3_r3 i k := by
  fin_cases i
  · exact power3_r3_0_eq k
  · exact power3_r3_1_eq k
  · exact power3_r3_2_eq k
  · exact power3_r3_3_eq k
  · exact power3_r3_4_eq k
  · exact power3_r3_5_eq k
  · exact power3_r3_6_eq k
  · exact power3_r3_7_eq k
  · exact power3_r3_8_eq k
  · exact power3_r3_9_eq k
  · exact power3_r3_10_eq k
  · exact power3_r3_11_eq k
  · exact power3_r3_12_eq k
  · exact power3_r3_13_eq k
  · exact power3_r3_14_eq k
  · exact power3_r3_15_eq k
lemma power3_r4_0_eq : ∀ k : Fin 16, power3Expr 4 0 k = power3_r4_0 k := by decide +kernel
lemma power3_r4_1_eq : ∀ k : Fin 16, power3Expr 4 1 k = power3_r4_1 k := by decide +kernel
lemma power3_r4_2_eq : ∀ k : Fin 16, power3Expr 4 2 k = power3_r4_2 k := by decide +kernel
lemma power3_r4_3_eq : ∀ k : Fin 16, power3Expr 4 3 k = power3_r4_3 k := by decide +kernel
lemma power3_r4_4_eq : ∀ k : Fin 16, power3Expr 4 4 k = power3_r4_4 k := by decide +kernel
lemma power3_r4_5_eq : ∀ k : Fin 16, power3Expr 4 5 k = power3_r4_5 k := by decide +kernel
lemma power3_r4_6_eq : ∀ k : Fin 16, power3Expr 4 6 k = power3_r4_6 k := by decide +kernel
lemma power3_r4_7_eq : ∀ k : Fin 16, power3Expr 4 7 k = power3_r4_7 k := by decide +kernel
lemma power3_r4_8_eq : ∀ k : Fin 16, power3Expr 4 8 k = power3_r4_8 k := by decide +kernel
lemma power3_r4_9_eq : ∀ k : Fin 16, power3Expr 4 9 k = power3_r4_9 k := by decide +kernel
lemma power3_r4_10_eq : ∀ k : Fin 16, power3Expr 4 10 k = power3_r4_10 k := by decide +kernel
lemma power3_r4_11_eq : ∀ k : Fin 16, power3Expr 4 11 k = power3_r4_11 k := by decide +kernel
lemma power3_r4_12_eq : ∀ k : Fin 16, power3Expr 4 12 k = power3_r4_12 k := by decide +kernel
lemma power3_r4_13_eq : ∀ k : Fin 16, power3Expr 4 13 k = power3_r4_13 k := by decide +kernel
lemma power3_r4_14_eq : ∀ k : Fin 16, power3Expr 4 14 k = power3_r4_14 k := by decide +kernel
lemma power3_r4_15_eq : ∀ k : Fin 16, power3Expr 4 15 k = power3_r4_15 k := by decide +kernel
lemma power3_r4_eq (i k : Fin 16) : power3Expr 4 i k = power3_r4 i k := by
  fin_cases i
  · exact power3_r4_0_eq k
  · exact power3_r4_1_eq k
  · exact power3_r4_2_eq k
  · exact power3_r4_3_eq k
  · exact power3_r4_4_eq k
  · exact power3_r4_5_eq k
  · exact power3_r4_6_eq k
  · exact power3_r4_7_eq k
  · exact power3_r4_8_eq k
  · exact power3_r4_9_eq k
  · exact power3_r4_10_eq k
  · exact power3_r4_11_eq k
  · exact power3_r4_12_eq k
  · exact power3_r4_13_eq k
  · exact power3_r4_14_eq k
  · exact power3_r4_15_eq k
lemma power3_r5_0_eq : ∀ k : Fin 16, power3Expr 5 0 k = power3_r5_0 k := by decide +kernel
lemma power3_r5_1_eq : ∀ k : Fin 16, power3Expr 5 1 k = power3_r5_1 k := by decide +kernel
lemma power3_r5_2_eq : ∀ k : Fin 16, power3Expr 5 2 k = power3_r5_2 k := by decide +kernel
lemma power3_r5_3_eq : ∀ k : Fin 16, power3Expr 5 3 k = power3_r5_3 k := by decide +kernel
lemma power3_r5_4_eq : ∀ k : Fin 16, power3Expr 5 4 k = power3_r5_4 k := by decide +kernel
lemma power3_r5_5_eq : ∀ k : Fin 16, power3Expr 5 5 k = power3_r5_5 k := by decide +kernel
lemma power3_r5_6_eq : ∀ k : Fin 16, power3Expr 5 6 k = power3_r5_6 k := by decide +kernel
lemma power3_r5_7_eq : ∀ k : Fin 16, power3Expr 5 7 k = power3_r5_7 k := by decide +kernel
lemma power3_r5_8_eq : ∀ k : Fin 16, power3Expr 5 8 k = power3_r5_8 k := by decide +kernel
lemma power3_r5_9_eq : ∀ k : Fin 16, power3Expr 5 9 k = power3_r5_9 k := by decide +kernel
lemma power3_r5_10_eq : ∀ k : Fin 16, power3Expr 5 10 k = power3_r5_10 k := by decide +kernel
lemma power3_r5_11_eq : ∀ k : Fin 16, power3Expr 5 11 k = power3_r5_11 k := by decide +kernel
lemma power3_r5_12_eq : ∀ k : Fin 16, power3Expr 5 12 k = power3_r5_12 k := by decide +kernel
lemma power3_r5_13_eq : ∀ k : Fin 16, power3Expr 5 13 k = power3_r5_13 k := by decide +kernel
lemma power3_r5_14_eq : ∀ k : Fin 16, power3Expr 5 14 k = power3_r5_14 k := by decide +kernel
lemma power3_r5_15_eq : ∀ k : Fin 16, power3Expr 5 15 k = power3_r5_15 k := by decide +kernel
lemma power3_r5_eq (i k : Fin 16) : power3Expr 5 i k = power3_r5 i k := by
  fin_cases i
  · exact power3_r5_0_eq k
  · exact power3_r5_1_eq k
  · exact power3_r5_2_eq k
  · exact power3_r5_3_eq k
  · exact power3_r5_4_eq k
  · exact power3_r5_5_eq k
  · exact power3_r5_6_eq k
  · exact power3_r5_7_eq k
  · exact power3_r5_8_eq k
  · exact power3_r5_9_eq k
  · exact power3_r5_10_eq k
  · exact power3_r5_11_eq k
  · exact power3_r5_12_eq k
  · exact power3_r5_13_eq k
  · exact power3_r5_14_eq k
  · exact power3_r5_15_eq k
lemma power3_eq (j : Fin 6) (i k : Fin 16) : power3Expr j i k = power3 j i k := by
  fin_cases j
  · exact power3_r0_eq i k
  · exact power3_r1_eq i k
  · exact power3_r2_eq i k
  · exact power3_r3_eq i k
  · exact power3_r4_eq i k
  · exact power3_r5_eq i k
lemma power3_contains (j : Fin 6) (i k : Fin 16) :
    (power3 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(3:ℕ))) := by
  rw [← power3_eq]
  unfold power3Expr
  convert exp_direct_step (power2_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power4_r0_0_eq : ∀ k : Fin 16, power4Expr 0 0 k = power4_r0_0 k := by decide +kernel
lemma power4_r0_1_eq : ∀ k : Fin 16, power4Expr 0 1 k = power4_r0_1 k := by decide +kernel
lemma power4_r0_2_eq : ∀ k : Fin 16, power4Expr 0 2 k = power4_r0_2 k := by decide +kernel
lemma power4_r0_3_eq : ∀ k : Fin 16, power4Expr 0 3 k = power4_r0_3 k := by decide +kernel
lemma power4_r0_4_eq : ∀ k : Fin 16, power4Expr 0 4 k = power4_r0_4 k := by decide +kernel
lemma power4_r0_5_eq : ∀ k : Fin 16, power4Expr 0 5 k = power4_r0_5 k := by decide +kernel
lemma power4_r0_6_eq : ∀ k : Fin 16, power4Expr 0 6 k = power4_r0_6 k := by decide +kernel
lemma power4_r0_7_eq : ∀ k : Fin 16, power4Expr 0 7 k = power4_r0_7 k := by decide +kernel
lemma power4_r0_8_eq : ∀ k : Fin 16, power4Expr 0 8 k = power4_r0_8 k := by decide +kernel
lemma power4_r0_9_eq : ∀ k : Fin 16, power4Expr 0 9 k = power4_r0_9 k := by decide +kernel
lemma power4_r0_10_eq : ∀ k : Fin 16, power4Expr 0 10 k = power4_r0_10 k := by decide +kernel
lemma power4_r0_11_eq : ∀ k : Fin 16, power4Expr 0 11 k = power4_r0_11 k := by decide +kernel
lemma power4_r0_12_eq : ∀ k : Fin 16, power4Expr 0 12 k = power4_r0_12 k := by decide +kernel
lemma power4_r0_13_eq : ∀ k : Fin 16, power4Expr 0 13 k = power4_r0_13 k := by decide +kernel
lemma power4_r0_14_eq : ∀ k : Fin 16, power4Expr 0 14 k = power4_r0_14 k := by decide +kernel
lemma power4_r0_15_eq : ∀ k : Fin 16, power4Expr 0 15 k = power4_r0_15 k := by decide +kernel
lemma power4_r0_eq (i k : Fin 16) : power4Expr 0 i k = power4_r0 i k := by
  fin_cases i
  · exact power4_r0_0_eq k
  · exact power4_r0_1_eq k
  · exact power4_r0_2_eq k
  · exact power4_r0_3_eq k
  · exact power4_r0_4_eq k
  · exact power4_r0_5_eq k
  · exact power4_r0_6_eq k
  · exact power4_r0_7_eq k
  · exact power4_r0_8_eq k
  · exact power4_r0_9_eq k
  · exact power4_r0_10_eq k
  · exact power4_r0_11_eq k
  · exact power4_r0_12_eq k
  · exact power4_r0_13_eq k
  · exact power4_r0_14_eq k
  · exact power4_r0_15_eq k
lemma power4_r1_0_eq : ∀ k : Fin 16, power4Expr 1 0 k = power4_r1_0 k := by decide +kernel
lemma power4_r1_1_eq : ∀ k : Fin 16, power4Expr 1 1 k = power4_r1_1 k := by decide +kernel
lemma power4_r1_2_eq : ∀ k : Fin 16, power4Expr 1 2 k = power4_r1_2 k := by decide +kernel
lemma power4_r1_3_eq : ∀ k : Fin 16, power4Expr 1 3 k = power4_r1_3 k := by decide +kernel
lemma power4_r1_4_eq : ∀ k : Fin 16, power4Expr 1 4 k = power4_r1_4 k := by decide +kernel
lemma power4_r1_5_eq : ∀ k : Fin 16, power4Expr 1 5 k = power4_r1_5 k := by decide +kernel
lemma power4_r1_6_eq : ∀ k : Fin 16, power4Expr 1 6 k = power4_r1_6 k := by decide +kernel
lemma power4_r1_7_eq : ∀ k : Fin 16, power4Expr 1 7 k = power4_r1_7 k := by decide +kernel
lemma power4_r1_8_eq : ∀ k : Fin 16, power4Expr 1 8 k = power4_r1_8 k := by decide +kernel
lemma power4_r1_9_eq : ∀ k : Fin 16, power4Expr 1 9 k = power4_r1_9 k := by decide +kernel
lemma power4_r1_10_eq : ∀ k : Fin 16, power4Expr 1 10 k = power4_r1_10 k := by decide +kernel
lemma power4_r1_11_eq : ∀ k : Fin 16, power4Expr 1 11 k = power4_r1_11 k := by decide +kernel
lemma power4_r1_12_eq : ∀ k : Fin 16, power4Expr 1 12 k = power4_r1_12 k := by decide +kernel
lemma power4_r1_13_eq : ∀ k : Fin 16, power4Expr 1 13 k = power4_r1_13 k := by decide +kernel
lemma power4_r1_14_eq : ∀ k : Fin 16, power4Expr 1 14 k = power4_r1_14 k := by decide +kernel
lemma power4_r1_15_eq : ∀ k : Fin 16, power4Expr 1 15 k = power4_r1_15 k := by decide +kernel
lemma power4_r1_eq (i k : Fin 16) : power4Expr 1 i k = power4_r1 i k := by
  fin_cases i
  · exact power4_r1_0_eq k
  · exact power4_r1_1_eq k
  · exact power4_r1_2_eq k
  · exact power4_r1_3_eq k
  · exact power4_r1_4_eq k
  · exact power4_r1_5_eq k
  · exact power4_r1_6_eq k
  · exact power4_r1_7_eq k
  · exact power4_r1_8_eq k
  · exact power4_r1_9_eq k
  · exact power4_r1_10_eq k
  · exact power4_r1_11_eq k
  · exact power4_r1_12_eq k
  · exact power4_r1_13_eq k
  · exact power4_r1_14_eq k
  · exact power4_r1_15_eq k
lemma power4_r2_0_eq : ∀ k : Fin 16, power4Expr 2 0 k = power4_r2_0 k := by decide +kernel
lemma power4_r2_1_eq : ∀ k : Fin 16, power4Expr 2 1 k = power4_r2_1 k := by decide +kernel
lemma power4_r2_2_eq : ∀ k : Fin 16, power4Expr 2 2 k = power4_r2_2 k := by decide +kernel
lemma power4_r2_3_eq : ∀ k : Fin 16, power4Expr 2 3 k = power4_r2_3 k := by decide +kernel
lemma power4_r2_4_eq : ∀ k : Fin 16, power4Expr 2 4 k = power4_r2_4 k := by decide +kernel
lemma power4_r2_5_eq : ∀ k : Fin 16, power4Expr 2 5 k = power4_r2_5 k := by decide +kernel
lemma power4_r2_6_eq : ∀ k : Fin 16, power4Expr 2 6 k = power4_r2_6 k := by decide +kernel
lemma power4_r2_7_eq : ∀ k : Fin 16, power4Expr 2 7 k = power4_r2_7 k := by decide +kernel
lemma power4_r2_8_eq : ∀ k : Fin 16, power4Expr 2 8 k = power4_r2_8 k := by decide +kernel
lemma power4_r2_9_eq : ∀ k : Fin 16, power4Expr 2 9 k = power4_r2_9 k := by decide +kernel
lemma power4_r2_10_eq : ∀ k : Fin 16, power4Expr 2 10 k = power4_r2_10 k := by decide +kernel
lemma power4_r2_11_eq : ∀ k : Fin 16, power4Expr 2 11 k = power4_r2_11 k := by decide +kernel
lemma power4_r2_12_eq : ∀ k : Fin 16, power4Expr 2 12 k = power4_r2_12 k := by decide +kernel
lemma power4_r2_13_eq : ∀ k : Fin 16, power4Expr 2 13 k = power4_r2_13 k := by decide +kernel
lemma power4_r2_14_eq : ∀ k : Fin 16, power4Expr 2 14 k = power4_r2_14 k := by decide +kernel
lemma power4_r2_15_eq : ∀ k : Fin 16, power4Expr 2 15 k = power4_r2_15 k := by decide +kernel
lemma power4_r2_eq (i k : Fin 16) : power4Expr 2 i k = power4_r2 i k := by
  fin_cases i
  · exact power4_r2_0_eq k
  · exact power4_r2_1_eq k
  · exact power4_r2_2_eq k
  · exact power4_r2_3_eq k
  · exact power4_r2_4_eq k
  · exact power4_r2_5_eq k
  · exact power4_r2_6_eq k
  · exact power4_r2_7_eq k
  · exact power4_r2_8_eq k
  · exact power4_r2_9_eq k
  · exact power4_r2_10_eq k
  · exact power4_r2_11_eq k
  · exact power4_r2_12_eq k
  · exact power4_r2_13_eq k
  · exact power4_r2_14_eq k
  · exact power4_r2_15_eq k
lemma power4_r3_0_eq : ∀ k : Fin 16, power4Expr 3 0 k = power4_r3_0 k := by decide +kernel
lemma power4_r3_1_eq : ∀ k : Fin 16, power4Expr 3 1 k = power4_r3_1 k := by decide +kernel
lemma power4_r3_2_eq : ∀ k : Fin 16, power4Expr 3 2 k = power4_r3_2 k := by decide +kernel
lemma power4_r3_3_eq : ∀ k : Fin 16, power4Expr 3 3 k = power4_r3_3 k := by decide +kernel
lemma power4_r3_4_eq : ∀ k : Fin 16, power4Expr 3 4 k = power4_r3_4 k := by decide +kernel
lemma power4_r3_5_eq : ∀ k : Fin 16, power4Expr 3 5 k = power4_r3_5 k := by decide +kernel
lemma power4_r3_6_eq : ∀ k : Fin 16, power4Expr 3 6 k = power4_r3_6 k := by decide +kernel
lemma power4_r3_7_eq : ∀ k : Fin 16, power4Expr 3 7 k = power4_r3_7 k := by decide +kernel
lemma power4_r3_8_eq : ∀ k : Fin 16, power4Expr 3 8 k = power4_r3_8 k := by decide +kernel
lemma power4_r3_9_eq : ∀ k : Fin 16, power4Expr 3 9 k = power4_r3_9 k := by decide +kernel
lemma power4_r3_10_eq : ∀ k : Fin 16, power4Expr 3 10 k = power4_r3_10 k := by decide +kernel
lemma power4_r3_11_eq : ∀ k : Fin 16, power4Expr 3 11 k = power4_r3_11 k := by decide +kernel
lemma power4_r3_12_eq : ∀ k : Fin 16, power4Expr 3 12 k = power4_r3_12 k := by decide +kernel
lemma power4_r3_13_eq : ∀ k : Fin 16, power4Expr 3 13 k = power4_r3_13 k := by decide +kernel
lemma power4_r3_14_eq : ∀ k : Fin 16, power4Expr 3 14 k = power4_r3_14 k := by decide +kernel
lemma power4_r3_15_eq : ∀ k : Fin 16, power4Expr 3 15 k = power4_r3_15 k := by decide +kernel
lemma power4_r3_eq (i k : Fin 16) : power4Expr 3 i k = power4_r3 i k := by
  fin_cases i
  · exact power4_r3_0_eq k
  · exact power4_r3_1_eq k
  · exact power4_r3_2_eq k
  · exact power4_r3_3_eq k
  · exact power4_r3_4_eq k
  · exact power4_r3_5_eq k
  · exact power4_r3_6_eq k
  · exact power4_r3_7_eq k
  · exact power4_r3_8_eq k
  · exact power4_r3_9_eq k
  · exact power4_r3_10_eq k
  · exact power4_r3_11_eq k
  · exact power4_r3_12_eq k
  · exact power4_r3_13_eq k
  · exact power4_r3_14_eq k
  · exact power4_r3_15_eq k
lemma power4_r4_0_eq : ∀ k : Fin 16, power4Expr 4 0 k = power4_r4_0 k := by decide +kernel
lemma power4_r4_1_eq : ∀ k : Fin 16, power4Expr 4 1 k = power4_r4_1 k := by decide +kernel
lemma power4_r4_2_eq : ∀ k : Fin 16, power4Expr 4 2 k = power4_r4_2 k := by decide +kernel
lemma power4_r4_3_eq : ∀ k : Fin 16, power4Expr 4 3 k = power4_r4_3 k := by decide +kernel
lemma power4_r4_4_eq : ∀ k : Fin 16, power4Expr 4 4 k = power4_r4_4 k := by decide +kernel
lemma power4_r4_5_eq : ∀ k : Fin 16, power4Expr 4 5 k = power4_r4_5 k := by decide +kernel
lemma power4_r4_6_eq : ∀ k : Fin 16, power4Expr 4 6 k = power4_r4_6 k := by decide +kernel
lemma power4_r4_7_eq : ∀ k : Fin 16, power4Expr 4 7 k = power4_r4_7 k := by decide +kernel
lemma power4_r4_8_eq : ∀ k : Fin 16, power4Expr 4 8 k = power4_r4_8 k := by decide +kernel
lemma power4_r4_9_eq : ∀ k : Fin 16, power4Expr 4 9 k = power4_r4_9 k := by decide +kernel
lemma power4_r4_10_eq : ∀ k : Fin 16, power4Expr 4 10 k = power4_r4_10 k := by decide +kernel
lemma power4_r4_11_eq : ∀ k : Fin 16, power4Expr 4 11 k = power4_r4_11 k := by decide +kernel
lemma power4_r4_12_eq : ∀ k : Fin 16, power4Expr 4 12 k = power4_r4_12 k := by decide +kernel
lemma power4_r4_13_eq : ∀ k : Fin 16, power4Expr 4 13 k = power4_r4_13 k := by decide +kernel
lemma power4_r4_14_eq : ∀ k : Fin 16, power4Expr 4 14 k = power4_r4_14 k := by decide +kernel
lemma power4_r4_15_eq : ∀ k : Fin 16, power4Expr 4 15 k = power4_r4_15 k := by decide +kernel
lemma power4_r4_eq (i k : Fin 16) : power4Expr 4 i k = power4_r4 i k := by
  fin_cases i
  · exact power4_r4_0_eq k
  · exact power4_r4_1_eq k
  · exact power4_r4_2_eq k
  · exact power4_r4_3_eq k
  · exact power4_r4_4_eq k
  · exact power4_r4_5_eq k
  · exact power4_r4_6_eq k
  · exact power4_r4_7_eq k
  · exact power4_r4_8_eq k
  · exact power4_r4_9_eq k
  · exact power4_r4_10_eq k
  · exact power4_r4_11_eq k
  · exact power4_r4_12_eq k
  · exact power4_r4_13_eq k
  · exact power4_r4_14_eq k
  · exact power4_r4_15_eq k
lemma power4_r5_0_eq : ∀ k : Fin 16, power4Expr 5 0 k = power4_r5_0 k := by decide +kernel
lemma power4_r5_1_eq : ∀ k : Fin 16, power4Expr 5 1 k = power4_r5_1 k := by decide +kernel
lemma power4_r5_2_eq : ∀ k : Fin 16, power4Expr 5 2 k = power4_r5_2 k := by decide +kernel
lemma power4_r5_3_eq : ∀ k : Fin 16, power4Expr 5 3 k = power4_r5_3 k := by decide +kernel
lemma power4_r5_4_eq : ∀ k : Fin 16, power4Expr 5 4 k = power4_r5_4 k := by decide +kernel
lemma power4_r5_5_eq : ∀ k : Fin 16, power4Expr 5 5 k = power4_r5_5 k := by decide +kernel
lemma power4_r5_6_eq : ∀ k : Fin 16, power4Expr 5 6 k = power4_r5_6 k := by decide +kernel
lemma power4_r5_7_eq : ∀ k : Fin 16, power4Expr 5 7 k = power4_r5_7 k := by decide +kernel
lemma power4_r5_8_eq : ∀ k : Fin 16, power4Expr 5 8 k = power4_r5_8 k := by decide +kernel
lemma power4_r5_9_eq : ∀ k : Fin 16, power4Expr 5 9 k = power4_r5_9 k := by decide +kernel
lemma power4_r5_10_eq : ∀ k : Fin 16, power4Expr 5 10 k = power4_r5_10 k := by decide +kernel
lemma power4_r5_11_eq : ∀ k : Fin 16, power4Expr 5 11 k = power4_r5_11 k := by decide +kernel
lemma power4_r5_12_eq : ∀ k : Fin 16, power4Expr 5 12 k = power4_r5_12 k := by decide +kernel
lemma power4_r5_13_eq : ∀ k : Fin 16, power4Expr 5 13 k = power4_r5_13 k := by decide +kernel
lemma power4_r5_14_eq : ∀ k : Fin 16, power4Expr 5 14 k = power4_r5_14 k := by decide +kernel
lemma power4_r5_15_eq : ∀ k : Fin 16, power4Expr 5 15 k = power4_r5_15 k := by decide +kernel
lemma power4_r5_eq (i k : Fin 16) : power4Expr 5 i k = power4_r5 i k := by
  fin_cases i
  · exact power4_r5_0_eq k
  · exact power4_r5_1_eq k
  · exact power4_r5_2_eq k
  · exact power4_r5_3_eq k
  · exact power4_r5_4_eq k
  · exact power4_r5_5_eq k
  · exact power4_r5_6_eq k
  · exact power4_r5_7_eq k
  · exact power4_r5_8_eq k
  · exact power4_r5_9_eq k
  · exact power4_r5_10_eq k
  · exact power4_r5_11_eq k
  · exact power4_r5_12_eq k
  · exact power4_r5_13_eq k
  · exact power4_r5_14_eq k
  · exact power4_r5_15_eq k
lemma power4_eq (j : Fin 6) (i k : Fin 16) : power4Expr j i k = power4 j i k := by
  fin_cases j
  · exact power4_r0_eq i k
  · exact power4_r1_eq i k
  · exact power4_r2_eq i k
  · exact power4_r3_eq i k
  · exact power4_r4_eq i k
  · exact power4_r5_eq i k
lemma power4_contains (j : Fin 6) (i k : Fin 16) :
    (power4 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(4:ℕ))) := by
  rw [← power4_eq]
  unfold power4Expr
  convert exp_direct_step (power3_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma column4_1_r0_0_eq : ∀ k : Fin 16, column4_1Expr 0 0 k = column4_1_r0_0 k := by decide +kernel
lemma column4_1_r0_1_eq : ∀ k : Fin 16, column4_1Expr 0 1 k = column4_1_r0_1 k := by decide +kernel
lemma column4_1_r0_2_eq : ∀ k : Fin 16, column4_1Expr 0 2 k = column4_1_r0_2 k := by decide +kernel
lemma column4_1_r0_3_eq : ∀ k : Fin 16, column4_1Expr 0 3 k = column4_1_r0_3 k := by decide +kernel
lemma column4_1_r0_4_eq : ∀ k : Fin 16, column4_1Expr 0 4 k = column4_1_r0_4 k := by decide +kernel
lemma column4_1_r0_5_eq : ∀ k : Fin 16, column4_1Expr 0 5 k = column4_1_r0_5 k := by decide +kernel
lemma column4_1_r0_6_eq : ∀ k : Fin 16, column4_1Expr 0 6 k = column4_1_r0_6 k := by decide +kernel
lemma column4_1_r0_7_eq : ∀ k : Fin 16, column4_1Expr 0 7 k = column4_1_r0_7 k := by decide +kernel
lemma column4_1_r0_8_eq : ∀ k : Fin 16, column4_1Expr 0 8 k = column4_1_r0_8 k := by decide +kernel
lemma column4_1_r0_9_eq : ∀ k : Fin 16, column4_1Expr 0 9 k = column4_1_r0_9 k := by decide +kernel
lemma column4_1_r0_10_eq : ∀ k : Fin 16, column4_1Expr 0 10 k = column4_1_r0_10 k := by decide +kernel
lemma column4_1_r0_11_eq : ∀ k : Fin 16, column4_1Expr 0 11 k = column4_1_r0_11 k := by decide +kernel
lemma column4_1_r0_12_eq : ∀ k : Fin 16, column4_1Expr 0 12 k = column4_1_r0_12 k := by decide +kernel
lemma column4_1_r0_13_eq : ∀ k : Fin 16, column4_1Expr 0 13 k = column4_1_r0_13 k := by decide +kernel
lemma column4_1_r0_14_eq : ∀ k : Fin 16, column4_1Expr 0 14 k = column4_1_r0_14 k := by decide +kernel
lemma column4_1_r0_15_eq : ∀ k : Fin 16, column4_1Expr 0 15 k = column4_1_r0_15 k := by decide +kernel
lemma column4_1_r0_eq (i k : Fin 16) : column4_1Expr 0 i k = column4_1_r0 i k := by
  fin_cases i
  · exact column4_1_r0_0_eq k
  · exact column4_1_r0_1_eq k
  · exact column4_1_r0_2_eq k
  · exact column4_1_r0_3_eq k
  · exact column4_1_r0_4_eq k
  · exact column4_1_r0_5_eq k
  · exact column4_1_r0_6_eq k
  · exact column4_1_r0_7_eq k
  · exact column4_1_r0_8_eq k
  · exact column4_1_r0_9_eq k
  · exact column4_1_r0_10_eq k
  · exact column4_1_r0_11_eq k
  · exact column4_1_r0_12_eq k
  · exact column4_1_r0_13_eq k
  · exact column4_1_r0_14_eq k
  · exact column4_1_r0_15_eq k
lemma column4_1_r1_0_eq : ∀ k : Fin 16, column4_1Expr 1 0 k = column4_1_r1_0 k := by decide +kernel
lemma column4_1_r1_1_eq : ∀ k : Fin 16, column4_1Expr 1 1 k = column4_1_r1_1 k := by decide +kernel
lemma column4_1_r1_2_eq : ∀ k : Fin 16, column4_1Expr 1 2 k = column4_1_r1_2 k := by decide +kernel
lemma column4_1_r1_3_eq : ∀ k : Fin 16, column4_1Expr 1 3 k = column4_1_r1_3 k := by decide +kernel
lemma column4_1_r1_4_eq : ∀ k : Fin 16, column4_1Expr 1 4 k = column4_1_r1_4 k := by decide +kernel
lemma column4_1_r1_5_eq : ∀ k : Fin 16, column4_1Expr 1 5 k = column4_1_r1_5 k := by decide +kernel
lemma column4_1_r1_6_eq : ∀ k : Fin 16, column4_1Expr 1 6 k = column4_1_r1_6 k := by decide +kernel
lemma column4_1_r1_7_eq : ∀ k : Fin 16, column4_1Expr 1 7 k = column4_1_r1_7 k := by decide +kernel
lemma column4_1_r1_8_eq : ∀ k : Fin 16, column4_1Expr 1 8 k = column4_1_r1_8 k := by decide +kernel
lemma column4_1_r1_9_eq : ∀ k : Fin 16, column4_1Expr 1 9 k = column4_1_r1_9 k := by decide +kernel
lemma column4_1_r1_10_eq : ∀ k : Fin 16, column4_1Expr 1 10 k = column4_1_r1_10 k := by decide +kernel
lemma column4_1_r1_11_eq : ∀ k : Fin 16, column4_1Expr 1 11 k = column4_1_r1_11 k := by decide +kernel
lemma column4_1_r1_12_eq : ∀ k : Fin 16, column4_1Expr 1 12 k = column4_1_r1_12 k := by decide +kernel
lemma column4_1_r1_13_eq : ∀ k : Fin 16, column4_1Expr 1 13 k = column4_1_r1_13 k := by decide +kernel
lemma column4_1_r1_14_eq : ∀ k : Fin 16, column4_1Expr 1 14 k = column4_1_r1_14 k := by decide +kernel
lemma column4_1_r1_15_eq : ∀ k : Fin 16, column4_1Expr 1 15 k = column4_1_r1_15 k := by decide +kernel
lemma column4_1_r1_eq (i k : Fin 16) : column4_1Expr 1 i k = column4_1_r1 i k := by
  fin_cases i
  · exact column4_1_r1_0_eq k
  · exact column4_1_r1_1_eq k
  · exact column4_1_r1_2_eq k
  · exact column4_1_r1_3_eq k
  · exact column4_1_r1_4_eq k
  · exact column4_1_r1_5_eq k
  · exact column4_1_r1_6_eq k
  · exact column4_1_r1_7_eq k
  · exact column4_1_r1_8_eq k
  · exact column4_1_r1_9_eq k
  · exact column4_1_r1_10_eq k
  · exact column4_1_r1_11_eq k
  · exact column4_1_r1_12_eq k
  · exact column4_1_r1_13_eq k
  · exact column4_1_r1_14_eq k
  · exact column4_1_r1_15_eq k
lemma column4_1_r2_0_eq : ∀ k : Fin 16, column4_1Expr 2 0 k = column4_1_r2_0 k := by decide +kernel
lemma column4_1_r2_1_eq : ∀ k : Fin 16, column4_1Expr 2 1 k = column4_1_r2_1 k := by decide +kernel
lemma column4_1_r2_2_eq : ∀ k : Fin 16, column4_1Expr 2 2 k = column4_1_r2_2 k := by decide +kernel
lemma column4_1_r2_3_eq : ∀ k : Fin 16, column4_1Expr 2 3 k = column4_1_r2_3 k := by decide +kernel
lemma column4_1_r2_4_eq : ∀ k : Fin 16, column4_1Expr 2 4 k = column4_1_r2_4 k := by decide +kernel
lemma column4_1_r2_5_eq : ∀ k : Fin 16, column4_1Expr 2 5 k = column4_1_r2_5 k := by decide +kernel
lemma column4_1_r2_6_eq : ∀ k : Fin 16, column4_1Expr 2 6 k = column4_1_r2_6 k := by decide +kernel
lemma column4_1_r2_7_eq : ∀ k : Fin 16, column4_1Expr 2 7 k = column4_1_r2_7 k := by decide +kernel
lemma column4_1_r2_8_eq : ∀ k : Fin 16, column4_1Expr 2 8 k = column4_1_r2_8 k := by decide +kernel
lemma column4_1_r2_9_eq : ∀ k : Fin 16, column4_1Expr 2 9 k = column4_1_r2_9 k := by decide +kernel
lemma column4_1_r2_10_eq : ∀ k : Fin 16, column4_1Expr 2 10 k = column4_1_r2_10 k := by decide +kernel
lemma column4_1_r2_11_eq : ∀ k : Fin 16, column4_1Expr 2 11 k = column4_1_r2_11 k := by decide +kernel
lemma column4_1_r2_12_eq : ∀ k : Fin 16, column4_1Expr 2 12 k = column4_1_r2_12 k := by decide +kernel
lemma column4_1_r2_13_eq : ∀ k : Fin 16, column4_1Expr 2 13 k = column4_1_r2_13 k := by decide +kernel
lemma column4_1_r2_14_eq : ∀ k : Fin 16, column4_1Expr 2 14 k = column4_1_r2_14 k := by decide +kernel
lemma column4_1_r2_15_eq : ∀ k : Fin 16, column4_1Expr 2 15 k = column4_1_r2_15 k := by decide +kernel
lemma column4_1_r2_eq (i k : Fin 16) : column4_1Expr 2 i k = column4_1_r2 i k := by
  fin_cases i
  · exact column4_1_r2_0_eq k
  · exact column4_1_r2_1_eq k
  · exact column4_1_r2_2_eq k
  · exact column4_1_r2_3_eq k
  · exact column4_1_r2_4_eq k
  · exact column4_1_r2_5_eq k
  · exact column4_1_r2_6_eq k
  · exact column4_1_r2_7_eq k
  · exact column4_1_r2_8_eq k
  · exact column4_1_r2_9_eq k
  · exact column4_1_r2_10_eq k
  · exact column4_1_r2_11_eq k
  · exact column4_1_r2_12_eq k
  · exact column4_1_r2_13_eq k
  · exact column4_1_r2_14_eq k
  · exact column4_1_r2_15_eq k
lemma column4_1_r3_0_eq : ∀ k : Fin 16, column4_1Expr 3 0 k = column4_1_r3_0 k := by decide +kernel
lemma column4_1_r3_1_eq : ∀ k : Fin 16, column4_1Expr 3 1 k = column4_1_r3_1 k := by decide +kernel
lemma column4_1_r3_2_eq : ∀ k : Fin 16, column4_1Expr 3 2 k = column4_1_r3_2 k := by decide +kernel
lemma column4_1_r3_3_eq : ∀ k : Fin 16, column4_1Expr 3 3 k = column4_1_r3_3 k := by decide +kernel
lemma column4_1_r3_4_eq : ∀ k : Fin 16, column4_1Expr 3 4 k = column4_1_r3_4 k := by decide +kernel
lemma column4_1_r3_5_eq : ∀ k : Fin 16, column4_1Expr 3 5 k = column4_1_r3_5 k := by decide +kernel
lemma column4_1_r3_6_eq : ∀ k : Fin 16, column4_1Expr 3 6 k = column4_1_r3_6 k := by decide +kernel
lemma column4_1_r3_7_eq : ∀ k : Fin 16, column4_1Expr 3 7 k = column4_1_r3_7 k := by decide +kernel
lemma column4_1_r3_8_eq : ∀ k : Fin 16, column4_1Expr 3 8 k = column4_1_r3_8 k := by decide +kernel
lemma column4_1_r3_9_eq : ∀ k : Fin 16, column4_1Expr 3 9 k = column4_1_r3_9 k := by decide +kernel
lemma column4_1_r3_10_eq : ∀ k : Fin 16, column4_1Expr 3 10 k = column4_1_r3_10 k := by decide +kernel
lemma column4_1_r3_11_eq : ∀ k : Fin 16, column4_1Expr 3 11 k = column4_1_r3_11 k := by decide +kernel
lemma column4_1_r3_12_eq : ∀ k : Fin 16, column4_1Expr 3 12 k = column4_1_r3_12 k := by decide +kernel
lemma column4_1_r3_13_eq : ∀ k : Fin 16, column4_1Expr 3 13 k = column4_1_r3_13 k := by decide +kernel
lemma column4_1_r3_14_eq : ∀ k : Fin 16, column4_1Expr 3 14 k = column4_1_r3_14 k := by decide +kernel
lemma column4_1_r3_15_eq : ∀ k : Fin 16, column4_1Expr 3 15 k = column4_1_r3_15 k := by decide +kernel
lemma column4_1_r3_eq (i k : Fin 16) : column4_1Expr 3 i k = column4_1_r3 i k := by
  fin_cases i
  · exact column4_1_r3_0_eq k
  · exact column4_1_r3_1_eq k
  · exact column4_1_r3_2_eq k
  · exact column4_1_r3_3_eq k
  · exact column4_1_r3_4_eq k
  · exact column4_1_r3_5_eq k
  · exact column4_1_r3_6_eq k
  · exact column4_1_r3_7_eq k
  · exact column4_1_r3_8_eq k
  · exact column4_1_r3_9_eq k
  · exact column4_1_r3_10_eq k
  · exact column4_1_r3_11_eq k
  · exact column4_1_r3_12_eq k
  · exact column4_1_r3_13_eq k
  · exact column4_1_r3_14_eq k
  · exact column4_1_r3_15_eq k
lemma column4_1_r4_0_eq : ∀ k : Fin 16, column4_1Expr 4 0 k = column4_1_r4_0 k := by decide +kernel
lemma column4_1_r4_1_eq : ∀ k : Fin 16, column4_1Expr 4 1 k = column4_1_r4_1 k := by decide +kernel
lemma column4_1_r4_2_eq : ∀ k : Fin 16, column4_1Expr 4 2 k = column4_1_r4_2 k := by decide +kernel
lemma column4_1_r4_3_eq : ∀ k : Fin 16, column4_1Expr 4 3 k = column4_1_r4_3 k := by decide +kernel
lemma column4_1_r4_4_eq : ∀ k : Fin 16, column4_1Expr 4 4 k = column4_1_r4_4 k := by decide +kernel
lemma column4_1_r4_5_eq : ∀ k : Fin 16, column4_1Expr 4 5 k = column4_1_r4_5 k := by decide +kernel
lemma column4_1_r4_6_eq : ∀ k : Fin 16, column4_1Expr 4 6 k = column4_1_r4_6 k := by decide +kernel
lemma column4_1_r4_7_eq : ∀ k : Fin 16, column4_1Expr 4 7 k = column4_1_r4_7 k := by decide +kernel
lemma column4_1_r4_8_eq : ∀ k : Fin 16, column4_1Expr 4 8 k = column4_1_r4_8 k := by decide +kernel
lemma column4_1_r4_9_eq : ∀ k : Fin 16, column4_1Expr 4 9 k = column4_1_r4_9 k := by decide +kernel
lemma column4_1_r4_10_eq : ∀ k : Fin 16, column4_1Expr 4 10 k = column4_1_r4_10 k := by decide +kernel
lemma column4_1_r4_11_eq : ∀ k : Fin 16, column4_1Expr 4 11 k = column4_1_r4_11 k := by decide +kernel
lemma column4_1_r4_12_eq : ∀ k : Fin 16, column4_1Expr 4 12 k = column4_1_r4_12 k := by decide +kernel
lemma column4_1_r4_13_eq : ∀ k : Fin 16, column4_1Expr 4 13 k = column4_1_r4_13 k := by decide +kernel
lemma column4_1_r4_14_eq : ∀ k : Fin 16, column4_1Expr 4 14 k = column4_1_r4_14 k := by decide +kernel
lemma column4_1_r4_15_eq : ∀ k : Fin 16, column4_1Expr 4 15 k = column4_1_r4_15 k := by decide +kernel
lemma column4_1_r4_eq (i k : Fin 16) : column4_1Expr 4 i k = column4_1_r4 i k := by
  fin_cases i
  · exact column4_1_r4_0_eq k
  · exact column4_1_r4_1_eq k
  · exact column4_1_r4_2_eq k
  · exact column4_1_r4_3_eq k
  · exact column4_1_r4_4_eq k
  · exact column4_1_r4_5_eq k
  · exact column4_1_r4_6_eq k
  · exact column4_1_r4_7_eq k
  · exact column4_1_r4_8_eq k
  · exact column4_1_r4_9_eq k
  · exact column4_1_r4_10_eq k
  · exact column4_1_r4_11_eq k
  · exact column4_1_r4_12_eq k
  · exact column4_1_r4_13_eq k
  · exact column4_1_r4_14_eq k
  · exact column4_1_r4_15_eq k
lemma column4_1_r5_0_eq : ∀ k : Fin 16, column4_1Expr 5 0 k = column4_1_r5_0 k := by decide +kernel
lemma column4_1_r5_1_eq : ∀ k : Fin 16, column4_1Expr 5 1 k = column4_1_r5_1 k := by decide +kernel
lemma column4_1_r5_2_eq : ∀ k : Fin 16, column4_1Expr 5 2 k = column4_1_r5_2 k := by decide +kernel
lemma column4_1_r5_3_eq : ∀ k : Fin 16, column4_1Expr 5 3 k = column4_1_r5_3 k := by decide +kernel
lemma column4_1_r5_4_eq : ∀ k : Fin 16, column4_1Expr 5 4 k = column4_1_r5_4 k := by decide +kernel
lemma column4_1_r5_5_eq : ∀ k : Fin 16, column4_1Expr 5 5 k = column4_1_r5_5 k := by decide +kernel
lemma column4_1_r5_6_eq : ∀ k : Fin 16, column4_1Expr 5 6 k = column4_1_r5_6 k := by decide +kernel
lemma column4_1_r5_7_eq : ∀ k : Fin 16, column4_1Expr 5 7 k = column4_1_r5_7 k := by decide +kernel
lemma column4_1_r5_8_eq : ∀ k : Fin 16, column4_1Expr 5 8 k = column4_1_r5_8 k := by decide +kernel
lemma column4_1_r5_9_eq : ∀ k : Fin 16, column4_1Expr 5 9 k = column4_1_r5_9 k := by decide +kernel
lemma column4_1_r5_10_eq : ∀ k : Fin 16, column4_1Expr 5 10 k = column4_1_r5_10 k := by decide +kernel
lemma column4_1_r5_11_eq : ∀ k : Fin 16, column4_1Expr 5 11 k = column4_1_r5_11 k := by decide +kernel
lemma column4_1_r5_12_eq : ∀ k : Fin 16, column4_1Expr 5 12 k = column4_1_r5_12 k := by decide +kernel
lemma column4_1_r5_13_eq : ∀ k : Fin 16, column4_1Expr 5 13 k = column4_1_r5_13 k := by decide +kernel
lemma column4_1_r5_14_eq : ∀ k : Fin 16, column4_1Expr 5 14 k = column4_1_r5_14 k := by decide +kernel
lemma column4_1_r5_15_eq : ∀ k : Fin 16, column4_1Expr 5 15 k = column4_1_r5_15 k := by decide +kernel
lemma column4_1_r5_eq (i k : Fin 16) : column4_1Expr 5 i k = column4_1_r5 i k := by
  fin_cases i
  · exact column4_1_r5_0_eq k
  · exact column4_1_r5_1_eq k
  · exact column4_1_r5_2_eq k
  · exact column4_1_r5_3_eq k
  · exact column4_1_r5_4_eq k
  · exact column4_1_r5_5_eq k
  · exact column4_1_r5_6_eq k
  · exact column4_1_r5_7_eq k
  · exact column4_1_r5_8_eq k
  · exact column4_1_r5_9_eq k
  · exact column4_1_r5_10_eq k
  · exact column4_1_r5_11_eq k
  · exact column4_1_r5_12_eq k
  · exact column4_1_r5_13_eq k
  · exact column4_1_r5_14_eq k
  · exact column4_1_r5_15_eq k
lemma column4_1_eq (j : Fin 6) (i k : Fin 16) : column4_1Expr j i k = column4_1 j i k := by
  fin_cases j
  · exact column4_1_r0_eq i k
  · exact column4_1_r1_eq i k
  · exact column4_1_r2_eq i k
  · exact column4_1_r3_eq i k
  · exact column4_1_r4_eq i k
  · exact column4_1_r5_eq i k
lemma column4_1_contains_e_oai (j : Fin 6) (i k : Fin 16) :
    (column4_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction true 4 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column4_1_eq,basisFunction_wave,← mul_assoc]
  unfold column4_1Expr
  apply CBox.contains_mul_e
  · rw [← waveAmplitude_mod true 4 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp4_1_contains j i k
  · exact power4_contains j i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.column4_1_contains_e_oai := @OAI.SharpPlanar.CachedData.column4_1_contains_e_oai
