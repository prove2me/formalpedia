-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.column52_0_contains_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T00:21:00.507864+00:00
-- url     : https://prove2.me/submissions/d525f9cc-59e5-4eb8-a363-06bba3f3c9af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_CachedData_amp4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_power48_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_exp_direct_step_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_phase12_periodic_e
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma phase12_mod (n : ℕ) : phase12 (n%12) = phase12 n :=
  (show Function.Periodic phase12 12 from phase12_periodic_e).map_mod_nat n

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

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma waveAmplitude_mod (d : Bool) (n j : ℕ) (t : ℝ) :
    waveAmplitude d (n%12) j t = waveAmplitude d n j t := by
  simp only [waveAmplitude,basisAlpha_mod,basisBeta_mod]
lemma basisFunction_wave (d : Bool) (n j : ℕ) (t : ℝ) :
    basisFunction d n j t = waveAmplitude d n j t*Complex.exp (-Complex.I*Real.pi*t*n) := by
  cases d <;> simp only [basisFunction,waveAmplitude,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  · rw [u_factored]; ring
  · rw [v_factored]; ring

end SharpPlanar.IntegerBasis

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers50
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
lemma power49_r0_0_eq : ∀ k : Fin 16, power49Expr 0 0 k = power49_r0_0 k := by decide +kernel
lemma power49_r0_1_eq : ∀ k : Fin 16, power49Expr 0 1 k = power49_r0_1 k := by decide +kernel
lemma power49_r0_2_eq : ∀ k : Fin 16, power49Expr 0 2 k = power49_r0_2 k := by decide +kernel
lemma power49_r0_3_eq : ∀ k : Fin 16, power49Expr 0 3 k = power49_r0_3 k := by decide +kernel
lemma power49_r0_4_eq : ∀ k : Fin 16, power49Expr 0 4 k = power49_r0_4 k := by decide +kernel
lemma power49_r0_5_eq : ∀ k : Fin 16, power49Expr 0 5 k = power49_r0_5 k := by decide +kernel
lemma power49_r0_6_eq : ∀ k : Fin 16, power49Expr 0 6 k = power49_r0_6 k := by decide +kernel
lemma power49_r0_7_eq : ∀ k : Fin 16, power49Expr 0 7 k = power49_r0_7 k := by decide +kernel
lemma power49_r0_8_eq : ∀ k : Fin 16, power49Expr 0 8 k = power49_r0_8 k := by decide +kernel
lemma power49_r0_9_eq : ∀ k : Fin 16, power49Expr 0 9 k = power49_r0_9 k := by decide +kernel
lemma power49_r0_10_eq : ∀ k : Fin 16, power49Expr 0 10 k = power49_r0_10 k := by decide +kernel
lemma power49_r0_11_eq : ∀ k : Fin 16, power49Expr 0 11 k = power49_r0_11 k := by decide +kernel
lemma power49_r0_12_eq : ∀ k : Fin 16, power49Expr 0 12 k = power49_r0_12 k := by decide +kernel
lemma power49_r0_13_eq : ∀ k : Fin 16, power49Expr 0 13 k = power49_r0_13 k := by decide +kernel
lemma power49_r0_14_eq : ∀ k : Fin 16, power49Expr 0 14 k = power49_r0_14 k := by decide +kernel
lemma power49_r0_15_eq : ∀ k : Fin 16, power49Expr 0 15 k = power49_r0_15 k := by decide +kernel
lemma power49_r0_eq (i k : Fin 16) : power49Expr 0 i k = power49_r0 i k := by
  fin_cases i
  · exact power49_r0_0_eq k
  · exact power49_r0_1_eq k
  · exact power49_r0_2_eq k
  · exact power49_r0_3_eq k
  · exact power49_r0_4_eq k
  · exact power49_r0_5_eq k
  · exact power49_r0_6_eq k
  · exact power49_r0_7_eq k
  · exact power49_r0_8_eq k
  · exact power49_r0_9_eq k
  · exact power49_r0_10_eq k
  · exact power49_r0_11_eq k
  · exact power49_r0_12_eq k
  · exact power49_r0_13_eq k
  · exact power49_r0_14_eq k
  · exact power49_r0_15_eq k
lemma power49_r1_0_eq : ∀ k : Fin 16, power49Expr 1 0 k = power49_r1_0 k := by decide +kernel
lemma power49_r1_1_eq : ∀ k : Fin 16, power49Expr 1 1 k = power49_r1_1 k := by decide +kernel
lemma power49_r1_2_eq : ∀ k : Fin 16, power49Expr 1 2 k = power49_r1_2 k := by decide +kernel
lemma power49_r1_3_eq : ∀ k : Fin 16, power49Expr 1 3 k = power49_r1_3 k := by decide +kernel
lemma power49_r1_4_eq : ∀ k : Fin 16, power49Expr 1 4 k = power49_r1_4 k := by decide +kernel
lemma power49_r1_5_eq : ∀ k : Fin 16, power49Expr 1 5 k = power49_r1_5 k := by decide +kernel
lemma power49_r1_6_eq : ∀ k : Fin 16, power49Expr 1 6 k = power49_r1_6 k := by decide +kernel
lemma power49_r1_7_eq : ∀ k : Fin 16, power49Expr 1 7 k = power49_r1_7 k := by decide +kernel
lemma power49_r1_8_eq : ∀ k : Fin 16, power49Expr 1 8 k = power49_r1_8 k := by decide +kernel
lemma power49_r1_9_eq : ∀ k : Fin 16, power49Expr 1 9 k = power49_r1_9 k := by decide +kernel
lemma power49_r1_10_eq : ∀ k : Fin 16, power49Expr 1 10 k = power49_r1_10 k := by decide +kernel
lemma power49_r1_11_eq : ∀ k : Fin 16, power49Expr 1 11 k = power49_r1_11 k := by decide +kernel
lemma power49_r1_12_eq : ∀ k : Fin 16, power49Expr 1 12 k = power49_r1_12 k := by decide +kernel
lemma power49_r1_13_eq : ∀ k : Fin 16, power49Expr 1 13 k = power49_r1_13 k := by decide +kernel
lemma power49_r1_14_eq : ∀ k : Fin 16, power49Expr 1 14 k = power49_r1_14 k := by decide +kernel
lemma power49_r1_15_eq : ∀ k : Fin 16, power49Expr 1 15 k = power49_r1_15 k := by decide +kernel
lemma power49_r1_eq (i k : Fin 16) : power49Expr 1 i k = power49_r1 i k := by
  fin_cases i
  · exact power49_r1_0_eq k
  · exact power49_r1_1_eq k
  · exact power49_r1_2_eq k
  · exact power49_r1_3_eq k
  · exact power49_r1_4_eq k
  · exact power49_r1_5_eq k
  · exact power49_r1_6_eq k
  · exact power49_r1_7_eq k
  · exact power49_r1_8_eq k
  · exact power49_r1_9_eq k
  · exact power49_r1_10_eq k
  · exact power49_r1_11_eq k
  · exact power49_r1_12_eq k
  · exact power49_r1_13_eq k
  · exact power49_r1_14_eq k
  · exact power49_r1_15_eq k
lemma power49_r2_0_eq : ∀ k : Fin 16, power49Expr 2 0 k = power49_r2_0 k := by decide +kernel
lemma power49_r2_1_eq : ∀ k : Fin 16, power49Expr 2 1 k = power49_r2_1 k := by decide +kernel
lemma power49_r2_2_eq : ∀ k : Fin 16, power49Expr 2 2 k = power49_r2_2 k := by decide +kernel
lemma power49_r2_3_eq : ∀ k : Fin 16, power49Expr 2 3 k = power49_r2_3 k := by decide +kernel
lemma power49_r2_4_eq : ∀ k : Fin 16, power49Expr 2 4 k = power49_r2_4 k := by decide +kernel
lemma power49_r2_5_eq : ∀ k : Fin 16, power49Expr 2 5 k = power49_r2_5 k := by decide +kernel
lemma power49_r2_6_eq : ∀ k : Fin 16, power49Expr 2 6 k = power49_r2_6 k := by decide +kernel
lemma power49_r2_7_eq : ∀ k : Fin 16, power49Expr 2 7 k = power49_r2_7 k := by decide +kernel
lemma power49_r2_8_eq : ∀ k : Fin 16, power49Expr 2 8 k = power49_r2_8 k := by decide +kernel
lemma power49_r2_9_eq : ∀ k : Fin 16, power49Expr 2 9 k = power49_r2_9 k := by decide +kernel
lemma power49_r2_10_eq : ∀ k : Fin 16, power49Expr 2 10 k = power49_r2_10 k := by decide +kernel
lemma power49_r2_11_eq : ∀ k : Fin 16, power49Expr 2 11 k = power49_r2_11 k := by decide +kernel
lemma power49_r2_12_eq : ∀ k : Fin 16, power49Expr 2 12 k = power49_r2_12 k := by decide +kernel
lemma power49_r2_13_eq : ∀ k : Fin 16, power49Expr 2 13 k = power49_r2_13 k := by decide +kernel
lemma power49_r2_14_eq : ∀ k : Fin 16, power49Expr 2 14 k = power49_r2_14 k := by decide +kernel
lemma power49_r2_15_eq : ∀ k : Fin 16, power49Expr 2 15 k = power49_r2_15 k := by decide +kernel
lemma power49_r2_eq (i k : Fin 16) : power49Expr 2 i k = power49_r2 i k := by
  fin_cases i
  · exact power49_r2_0_eq k
  · exact power49_r2_1_eq k
  · exact power49_r2_2_eq k
  · exact power49_r2_3_eq k
  · exact power49_r2_4_eq k
  · exact power49_r2_5_eq k
  · exact power49_r2_6_eq k
  · exact power49_r2_7_eq k
  · exact power49_r2_8_eq k
  · exact power49_r2_9_eq k
  · exact power49_r2_10_eq k
  · exact power49_r2_11_eq k
  · exact power49_r2_12_eq k
  · exact power49_r2_13_eq k
  · exact power49_r2_14_eq k
  · exact power49_r2_15_eq k
lemma power49_r3_0_eq : ∀ k : Fin 16, power49Expr 3 0 k = power49_r3_0 k := by decide +kernel
lemma power49_r3_1_eq : ∀ k : Fin 16, power49Expr 3 1 k = power49_r3_1 k := by decide +kernel
lemma power49_r3_2_eq : ∀ k : Fin 16, power49Expr 3 2 k = power49_r3_2 k := by decide +kernel
lemma power49_r3_3_eq : ∀ k : Fin 16, power49Expr 3 3 k = power49_r3_3 k := by decide +kernel
lemma power49_r3_4_eq : ∀ k : Fin 16, power49Expr 3 4 k = power49_r3_4 k := by decide +kernel
lemma power49_r3_5_eq : ∀ k : Fin 16, power49Expr 3 5 k = power49_r3_5 k := by decide +kernel
lemma power49_r3_6_eq : ∀ k : Fin 16, power49Expr 3 6 k = power49_r3_6 k := by decide +kernel
lemma power49_r3_7_eq : ∀ k : Fin 16, power49Expr 3 7 k = power49_r3_7 k := by decide +kernel
lemma power49_r3_8_eq : ∀ k : Fin 16, power49Expr 3 8 k = power49_r3_8 k := by decide +kernel
lemma power49_r3_9_eq : ∀ k : Fin 16, power49Expr 3 9 k = power49_r3_9 k := by decide +kernel
lemma power49_r3_10_eq : ∀ k : Fin 16, power49Expr 3 10 k = power49_r3_10 k := by decide +kernel
lemma power49_r3_11_eq : ∀ k : Fin 16, power49Expr 3 11 k = power49_r3_11 k := by decide +kernel
lemma power49_r3_12_eq : ∀ k : Fin 16, power49Expr 3 12 k = power49_r3_12 k := by decide +kernel
lemma power49_r3_13_eq : ∀ k : Fin 16, power49Expr 3 13 k = power49_r3_13 k := by decide +kernel
lemma power49_r3_14_eq : ∀ k : Fin 16, power49Expr 3 14 k = power49_r3_14 k := by decide +kernel
lemma power49_r3_15_eq : ∀ k : Fin 16, power49Expr 3 15 k = power49_r3_15 k := by decide +kernel
lemma power49_r3_eq (i k : Fin 16) : power49Expr 3 i k = power49_r3 i k := by
  fin_cases i
  · exact power49_r3_0_eq k
  · exact power49_r3_1_eq k
  · exact power49_r3_2_eq k
  · exact power49_r3_3_eq k
  · exact power49_r3_4_eq k
  · exact power49_r3_5_eq k
  · exact power49_r3_6_eq k
  · exact power49_r3_7_eq k
  · exact power49_r3_8_eq k
  · exact power49_r3_9_eq k
  · exact power49_r3_10_eq k
  · exact power49_r3_11_eq k
  · exact power49_r3_12_eq k
  · exact power49_r3_13_eq k
  · exact power49_r3_14_eq k
  · exact power49_r3_15_eq k
lemma power49_r4_0_eq : ∀ k : Fin 16, power49Expr 4 0 k = power49_r4_0 k := by decide +kernel
lemma power49_r4_1_eq : ∀ k : Fin 16, power49Expr 4 1 k = power49_r4_1 k := by decide +kernel
lemma power49_r4_2_eq : ∀ k : Fin 16, power49Expr 4 2 k = power49_r4_2 k := by decide +kernel
lemma power49_r4_3_eq : ∀ k : Fin 16, power49Expr 4 3 k = power49_r4_3 k := by decide +kernel
lemma power49_r4_4_eq : ∀ k : Fin 16, power49Expr 4 4 k = power49_r4_4 k := by decide +kernel
lemma power49_r4_5_eq : ∀ k : Fin 16, power49Expr 4 5 k = power49_r4_5 k := by decide +kernel
lemma power49_r4_6_eq : ∀ k : Fin 16, power49Expr 4 6 k = power49_r4_6 k := by decide +kernel
lemma power49_r4_7_eq : ∀ k : Fin 16, power49Expr 4 7 k = power49_r4_7 k := by decide +kernel
lemma power49_r4_8_eq : ∀ k : Fin 16, power49Expr 4 8 k = power49_r4_8 k := by decide +kernel
lemma power49_r4_9_eq : ∀ k : Fin 16, power49Expr 4 9 k = power49_r4_9 k := by decide +kernel
lemma power49_r4_10_eq : ∀ k : Fin 16, power49Expr 4 10 k = power49_r4_10 k := by decide +kernel
lemma power49_r4_11_eq : ∀ k : Fin 16, power49Expr 4 11 k = power49_r4_11 k := by decide +kernel
lemma power49_r4_12_eq : ∀ k : Fin 16, power49Expr 4 12 k = power49_r4_12 k := by decide +kernel
lemma power49_r4_13_eq : ∀ k : Fin 16, power49Expr 4 13 k = power49_r4_13 k := by decide +kernel
lemma power49_r4_14_eq : ∀ k : Fin 16, power49Expr 4 14 k = power49_r4_14 k := by decide +kernel
lemma power49_r4_15_eq : ∀ k : Fin 16, power49Expr 4 15 k = power49_r4_15 k := by decide +kernel
lemma power49_r4_eq (i k : Fin 16) : power49Expr 4 i k = power49_r4 i k := by
  fin_cases i
  · exact power49_r4_0_eq k
  · exact power49_r4_1_eq k
  · exact power49_r4_2_eq k
  · exact power49_r4_3_eq k
  · exact power49_r4_4_eq k
  · exact power49_r4_5_eq k
  · exact power49_r4_6_eq k
  · exact power49_r4_7_eq k
  · exact power49_r4_8_eq k
  · exact power49_r4_9_eq k
  · exact power49_r4_10_eq k
  · exact power49_r4_11_eq k
  · exact power49_r4_12_eq k
  · exact power49_r4_13_eq k
  · exact power49_r4_14_eq k
  · exact power49_r4_15_eq k
lemma power49_r5_0_eq : ∀ k : Fin 16, power49Expr 5 0 k = power49_r5_0 k := by decide +kernel
lemma power49_r5_1_eq : ∀ k : Fin 16, power49Expr 5 1 k = power49_r5_1 k := by decide +kernel
lemma power49_r5_2_eq : ∀ k : Fin 16, power49Expr 5 2 k = power49_r5_2 k := by decide +kernel
lemma power49_r5_3_eq : ∀ k : Fin 16, power49Expr 5 3 k = power49_r5_3 k := by decide +kernel
lemma power49_r5_4_eq : ∀ k : Fin 16, power49Expr 5 4 k = power49_r5_4 k := by decide +kernel
lemma power49_r5_5_eq : ∀ k : Fin 16, power49Expr 5 5 k = power49_r5_5 k := by decide +kernel
lemma power49_r5_6_eq : ∀ k : Fin 16, power49Expr 5 6 k = power49_r5_6 k := by decide +kernel
lemma power49_r5_7_eq : ∀ k : Fin 16, power49Expr 5 7 k = power49_r5_7 k := by decide +kernel
lemma power49_r5_8_eq : ∀ k : Fin 16, power49Expr 5 8 k = power49_r5_8 k := by decide +kernel
lemma power49_r5_9_eq : ∀ k : Fin 16, power49Expr 5 9 k = power49_r5_9 k := by decide +kernel
lemma power49_r5_10_eq : ∀ k : Fin 16, power49Expr 5 10 k = power49_r5_10 k := by decide +kernel
lemma power49_r5_11_eq : ∀ k : Fin 16, power49Expr 5 11 k = power49_r5_11 k := by decide +kernel
lemma power49_r5_12_eq : ∀ k : Fin 16, power49Expr 5 12 k = power49_r5_12 k := by decide +kernel
lemma power49_r5_13_eq : ∀ k : Fin 16, power49Expr 5 13 k = power49_r5_13 k := by decide +kernel
lemma power49_r5_14_eq : ∀ k : Fin 16, power49Expr 5 14 k = power49_r5_14 k := by decide +kernel
lemma power49_r5_15_eq : ∀ k : Fin 16, power49Expr 5 15 k = power49_r5_15 k := by decide +kernel
lemma power49_r5_eq (i k : Fin 16) : power49Expr 5 i k = power49_r5 i k := by
  fin_cases i
  · exact power49_r5_0_eq k
  · exact power49_r5_1_eq k
  · exact power49_r5_2_eq k
  · exact power49_r5_3_eq k
  · exact power49_r5_4_eq k
  · exact power49_r5_5_eq k
  · exact power49_r5_6_eq k
  · exact power49_r5_7_eq k
  · exact power49_r5_8_eq k
  · exact power49_r5_9_eq k
  · exact power49_r5_10_eq k
  · exact power49_r5_11_eq k
  · exact power49_r5_12_eq k
  · exact power49_r5_13_eq k
  · exact power49_r5_14_eq k
  · exact power49_r5_15_eq k
lemma power49_eq (j : Fin 6) (i k : Fin 16) : power49Expr j i k = power49 j i k := by
  fin_cases j
  · exact power49_r0_eq i k
  · exact power49_r1_eq i k
  · exact power49_r2_eq i k
  · exact power49_r3_eq i k
  · exact power49_r4_eq i k
  · exact power49_r5_eq i k
lemma power49_contains (j : Fin 6) (i k : Fin 16) :
    (power49 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(49:ℕ))) := by
  rw [← power49_eq]
  unfold power49Expr
  convert exp_direct_step_e (power48_contains_e j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power50_r0_0_eq : ∀ k : Fin 16, power50Expr 0 0 k = power50_r0_0 k := by decide +kernel
lemma power50_r0_1_eq : ∀ k : Fin 16, power50Expr 0 1 k = power50_r0_1 k := by decide +kernel
lemma power50_r0_2_eq : ∀ k : Fin 16, power50Expr 0 2 k = power50_r0_2 k := by decide +kernel
lemma power50_r0_3_eq : ∀ k : Fin 16, power50Expr 0 3 k = power50_r0_3 k := by decide +kernel
lemma power50_r0_4_eq : ∀ k : Fin 16, power50Expr 0 4 k = power50_r0_4 k := by decide +kernel
lemma power50_r0_5_eq : ∀ k : Fin 16, power50Expr 0 5 k = power50_r0_5 k := by decide +kernel
lemma power50_r0_6_eq : ∀ k : Fin 16, power50Expr 0 6 k = power50_r0_6 k := by decide +kernel
lemma power50_r0_7_eq : ∀ k : Fin 16, power50Expr 0 7 k = power50_r0_7 k := by decide +kernel
lemma power50_r0_8_eq : ∀ k : Fin 16, power50Expr 0 8 k = power50_r0_8 k := by decide +kernel
lemma power50_r0_9_eq : ∀ k : Fin 16, power50Expr 0 9 k = power50_r0_9 k := by decide +kernel
lemma power50_r0_10_eq : ∀ k : Fin 16, power50Expr 0 10 k = power50_r0_10 k := by decide +kernel
lemma power50_r0_11_eq : ∀ k : Fin 16, power50Expr 0 11 k = power50_r0_11 k := by decide +kernel
lemma power50_r0_12_eq : ∀ k : Fin 16, power50Expr 0 12 k = power50_r0_12 k := by decide +kernel
lemma power50_r0_13_eq : ∀ k : Fin 16, power50Expr 0 13 k = power50_r0_13 k := by decide +kernel
lemma power50_r0_14_eq : ∀ k : Fin 16, power50Expr 0 14 k = power50_r0_14 k := by decide +kernel
lemma power50_r0_15_eq : ∀ k : Fin 16, power50Expr 0 15 k = power50_r0_15 k := by decide +kernel
lemma power50_r0_eq (i k : Fin 16) : power50Expr 0 i k = power50_r0 i k := by
  fin_cases i
  · exact power50_r0_0_eq k
  · exact power50_r0_1_eq k
  · exact power50_r0_2_eq k
  · exact power50_r0_3_eq k
  · exact power50_r0_4_eq k
  · exact power50_r0_5_eq k
  · exact power50_r0_6_eq k
  · exact power50_r0_7_eq k
  · exact power50_r0_8_eq k
  · exact power50_r0_9_eq k
  · exact power50_r0_10_eq k
  · exact power50_r0_11_eq k
  · exact power50_r0_12_eq k
  · exact power50_r0_13_eq k
  · exact power50_r0_14_eq k
  · exact power50_r0_15_eq k
lemma power50_r1_0_eq : ∀ k : Fin 16, power50Expr 1 0 k = power50_r1_0 k := by decide +kernel
lemma power50_r1_1_eq : ∀ k : Fin 16, power50Expr 1 1 k = power50_r1_1 k := by decide +kernel
lemma power50_r1_2_eq : ∀ k : Fin 16, power50Expr 1 2 k = power50_r1_2 k := by decide +kernel
lemma power50_r1_3_eq : ∀ k : Fin 16, power50Expr 1 3 k = power50_r1_3 k := by decide +kernel
lemma power50_r1_4_eq : ∀ k : Fin 16, power50Expr 1 4 k = power50_r1_4 k := by decide +kernel
lemma power50_r1_5_eq : ∀ k : Fin 16, power50Expr 1 5 k = power50_r1_5 k := by decide +kernel
lemma power50_r1_6_eq : ∀ k : Fin 16, power50Expr 1 6 k = power50_r1_6 k := by decide +kernel
lemma power50_r1_7_eq : ∀ k : Fin 16, power50Expr 1 7 k = power50_r1_7 k := by decide +kernel
lemma power50_r1_8_eq : ∀ k : Fin 16, power50Expr 1 8 k = power50_r1_8 k := by decide +kernel
lemma power50_r1_9_eq : ∀ k : Fin 16, power50Expr 1 9 k = power50_r1_9 k := by decide +kernel
lemma power50_r1_10_eq : ∀ k : Fin 16, power50Expr 1 10 k = power50_r1_10 k := by decide +kernel
lemma power50_r1_11_eq : ∀ k : Fin 16, power50Expr 1 11 k = power50_r1_11 k := by decide +kernel
lemma power50_r1_12_eq : ∀ k : Fin 16, power50Expr 1 12 k = power50_r1_12 k := by decide +kernel
lemma power50_r1_13_eq : ∀ k : Fin 16, power50Expr 1 13 k = power50_r1_13 k := by decide +kernel
lemma power50_r1_14_eq : ∀ k : Fin 16, power50Expr 1 14 k = power50_r1_14 k := by decide +kernel
lemma power50_r1_15_eq : ∀ k : Fin 16, power50Expr 1 15 k = power50_r1_15 k := by decide +kernel
lemma power50_r1_eq (i k : Fin 16) : power50Expr 1 i k = power50_r1 i k := by
  fin_cases i
  · exact power50_r1_0_eq k
  · exact power50_r1_1_eq k
  · exact power50_r1_2_eq k
  · exact power50_r1_3_eq k
  · exact power50_r1_4_eq k
  · exact power50_r1_5_eq k
  · exact power50_r1_6_eq k
  · exact power50_r1_7_eq k
  · exact power50_r1_8_eq k
  · exact power50_r1_9_eq k
  · exact power50_r1_10_eq k
  · exact power50_r1_11_eq k
  · exact power50_r1_12_eq k
  · exact power50_r1_13_eq k
  · exact power50_r1_14_eq k
  · exact power50_r1_15_eq k
lemma power50_r2_0_eq : ∀ k : Fin 16, power50Expr 2 0 k = power50_r2_0 k := by decide +kernel
lemma power50_r2_1_eq : ∀ k : Fin 16, power50Expr 2 1 k = power50_r2_1 k := by decide +kernel
lemma power50_r2_2_eq : ∀ k : Fin 16, power50Expr 2 2 k = power50_r2_2 k := by decide +kernel
lemma power50_r2_3_eq : ∀ k : Fin 16, power50Expr 2 3 k = power50_r2_3 k := by decide +kernel
lemma power50_r2_4_eq : ∀ k : Fin 16, power50Expr 2 4 k = power50_r2_4 k := by decide +kernel
lemma power50_r2_5_eq : ∀ k : Fin 16, power50Expr 2 5 k = power50_r2_5 k := by decide +kernel
lemma power50_r2_6_eq : ∀ k : Fin 16, power50Expr 2 6 k = power50_r2_6 k := by decide +kernel
lemma power50_r2_7_eq : ∀ k : Fin 16, power50Expr 2 7 k = power50_r2_7 k := by decide +kernel
lemma power50_r2_8_eq : ∀ k : Fin 16, power50Expr 2 8 k = power50_r2_8 k := by decide +kernel
lemma power50_r2_9_eq : ∀ k : Fin 16, power50Expr 2 9 k = power50_r2_9 k := by decide +kernel
lemma power50_r2_10_eq : ∀ k : Fin 16, power50Expr 2 10 k = power50_r2_10 k := by decide +kernel
lemma power50_r2_11_eq : ∀ k : Fin 16, power50Expr 2 11 k = power50_r2_11 k := by decide +kernel
lemma power50_r2_12_eq : ∀ k : Fin 16, power50Expr 2 12 k = power50_r2_12 k := by decide +kernel
lemma power50_r2_13_eq : ∀ k : Fin 16, power50Expr 2 13 k = power50_r2_13 k := by decide +kernel
lemma power50_r2_14_eq : ∀ k : Fin 16, power50Expr 2 14 k = power50_r2_14 k := by decide +kernel
lemma power50_r2_15_eq : ∀ k : Fin 16, power50Expr 2 15 k = power50_r2_15 k := by decide +kernel
lemma power50_r2_eq (i k : Fin 16) : power50Expr 2 i k = power50_r2 i k := by
  fin_cases i
  · exact power50_r2_0_eq k
  · exact power50_r2_1_eq k
  · exact power50_r2_2_eq k
  · exact power50_r2_3_eq k
  · exact power50_r2_4_eq k
  · exact power50_r2_5_eq k
  · exact power50_r2_6_eq k
  · exact power50_r2_7_eq k
  · exact power50_r2_8_eq k
  · exact power50_r2_9_eq k
  · exact power50_r2_10_eq k
  · exact power50_r2_11_eq k
  · exact power50_r2_12_eq k
  · exact power50_r2_13_eq k
  · exact power50_r2_14_eq k
  · exact power50_r2_15_eq k
lemma power50_r3_0_eq : ∀ k : Fin 16, power50Expr 3 0 k = power50_r3_0 k := by decide +kernel
lemma power50_r3_1_eq : ∀ k : Fin 16, power50Expr 3 1 k = power50_r3_1 k := by decide +kernel
lemma power50_r3_2_eq : ∀ k : Fin 16, power50Expr 3 2 k = power50_r3_2 k := by decide +kernel
lemma power50_r3_3_eq : ∀ k : Fin 16, power50Expr 3 3 k = power50_r3_3 k := by decide +kernel
lemma power50_r3_4_eq : ∀ k : Fin 16, power50Expr 3 4 k = power50_r3_4 k := by decide +kernel
lemma power50_r3_5_eq : ∀ k : Fin 16, power50Expr 3 5 k = power50_r3_5 k := by decide +kernel
lemma power50_r3_6_eq : ∀ k : Fin 16, power50Expr 3 6 k = power50_r3_6 k := by decide +kernel
lemma power50_r3_7_eq : ∀ k : Fin 16, power50Expr 3 7 k = power50_r3_7 k := by decide +kernel
lemma power50_r3_8_eq : ∀ k : Fin 16, power50Expr 3 8 k = power50_r3_8 k := by decide +kernel
lemma power50_r3_9_eq : ∀ k : Fin 16, power50Expr 3 9 k = power50_r3_9 k := by decide +kernel
lemma power50_r3_10_eq : ∀ k : Fin 16, power50Expr 3 10 k = power50_r3_10 k := by decide +kernel
lemma power50_r3_11_eq : ∀ k : Fin 16, power50Expr 3 11 k = power50_r3_11 k := by decide +kernel
lemma power50_r3_12_eq : ∀ k : Fin 16, power50Expr 3 12 k = power50_r3_12 k := by decide +kernel
lemma power50_r3_13_eq : ∀ k : Fin 16, power50Expr 3 13 k = power50_r3_13 k := by decide +kernel
lemma power50_r3_14_eq : ∀ k : Fin 16, power50Expr 3 14 k = power50_r3_14 k := by decide +kernel
lemma power50_r3_15_eq : ∀ k : Fin 16, power50Expr 3 15 k = power50_r3_15 k := by decide +kernel
lemma power50_r3_eq (i k : Fin 16) : power50Expr 3 i k = power50_r3 i k := by
  fin_cases i
  · exact power50_r3_0_eq k
  · exact power50_r3_1_eq k
  · exact power50_r3_2_eq k
  · exact power50_r3_3_eq k
  · exact power50_r3_4_eq k
  · exact power50_r3_5_eq k
  · exact power50_r3_6_eq k
  · exact power50_r3_7_eq k
  · exact power50_r3_8_eq k
  · exact power50_r3_9_eq k
  · exact power50_r3_10_eq k
  · exact power50_r3_11_eq k
  · exact power50_r3_12_eq k
  · exact power50_r3_13_eq k
  · exact power50_r3_14_eq k
  · exact power50_r3_15_eq k
lemma power50_r4_0_eq : ∀ k : Fin 16, power50Expr 4 0 k = power50_r4_0 k := by decide +kernel
lemma power50_r4_1_eq : ∀ k : Fin 16, power50Expr 4 1 k = power50_r4_1 k := by decide +kernel
lemma power50_r4_2_eq : ∀ k : Fin 16, power50Expr 4 2 k = power50_r4_2 k := by decide +kernel
lemma power50_r4_3_eq : ∀ k : Fin 16, power50Expr 4 3 k = power50_r4_3 k := by decide +kernel
lemma power50_r4_4_eq : ∀ k : Fin 16, power50Expr 4 4 k = power50_r4_4 k := by decide +kernel
lemma power50_r4_5_eq : ∀ k : Fin 16, power50Expr 4 5 k = power50_r4_5 k := by decide +kernel
lemma power50_r4_6_eq : ∀ k : Fin 16, power50Expr 4 6 k = power50_r4_6 k := by decide +kernel
lemma power50_r4_7_eq : ∀ k : Fin 16, power50Expr 4 7 k = power50_r4_7 k := by decide +kernel
lemma power50_r4_8_eq : ∀ k : Fin 16, power50Expr 4 8 k = power50_r4_8 k := by decide +kernel
lemma power50_r4_9_eq : ∀ k : Fin 16, power50Expr 4 9 k = power50_r4_9 k := by decide +kernel
lemma power50_r4_10_eq : ∀ k : Fin 16, power50Expr 4 10 k = power50_r4_10 k := by decide +kernel
lemma power50_r4_11_eq : ∀ k : Fin 16, power50Expr 4 11 k = power50_r4_11 k := by decide +kernel
lemma power50_r4_12_eq : ∀ k : Fin 16, power50Expr 4 12 k = power50_r4_12 k := by decide +kernel
lemma power50_r4_13_eq : ∀ k : Fin 16, power50Expr 4 13 k = power50_r4_13 k := by decide +kernel
lemma power50_r4_14_eq : ∀ k : Fin 16, power50Expr 4 14 k = power50_r4_14 k := by decide +kernel
lemma power50_r4_15_eq : ∀ k : Fin 16, power50Expr 4 15 k = power50_r4_15 k := by decide +kernel
lemma power50_r4_eq (i k : Fin 16) : power50Expr 4 i k = power50_r4 i k := by
  fin_cases i
  · exact power50_r4_0_eq k
  · exact power50_r4_1_eq k
  · exact power50_r4_2_eq k
  · exact power50_r4_3_eq k
  · exact power50_r4_4_eq k
  · exact power50_r4_5_eq k
  · exact power50_r4_6_eq k
  · exact power50_r4_7_eq k
  · exact power50_r4_8_eq k
  · exact power50_r4_9_eq k
  · exact power50_r4_10_eq k
  · exact power50_r4_11_eq k
  · exact power50_r4_12_eq k
  · exact power50_r4_13_eq k
  · exact power50_r4_14_eq k
  · exact power50_r4_15_eq k
lemma power50_r5_0_eq : ∀ k : Fin 16, power50Expr 5 0 k = power50_r5_0 k := by decide +kernel
lemma power50_r5_1_eq : ∀ k : Fin 16, power50Expr 5 1 k = power50_r5_1 k := by decide +kernel
lemma power50_r5_2_eq : ∀ k : Fin 16, power50Expr 5 2 k = power50_r5_2 k := by decide +kernel
lemma power50_r5_3_eq : ∀ k : Fin 16, power50Expr 5 3 k = power50_r5_3 k := by decide +kernel
lemma power50_r5_4_eq : ∀ k : Fin 16, power50Expr 5 4 k = power50_r5_4 k := by decide +kernel
lemma power50_r5_5_eq : ∀ k : Fin 16, power50Expr 5 5 k = power50_r5_5 k := by decide +kernel
lemma power50_r5_6_eq : ∀ k : Fin 16, power50Expr 5 6 k = power50_r5_6 k := by decide +kernel
lemma power50_r5_7_eq : ∀ k : Fin 16, power50Expr 5 7 k = power50_r5_7 k := by decide +kernel
lemma power50_r5_8_eq : ∀ k : Fin 16, power50Expr 5 8 k = power50_r5_8 k := by decide +kernel
lemma power50_r5_9_eq : ∀ k : Fin 16, power50Expr 5 9 k = power50_r5_9 k := by decide +kernel
lemma power50_r5_10_eq : ∀ k : Fin 16, power50Expr 5 10 k = power50_r5_10 k := by decide +kernel
lemma power50_r5_11_eq : ∀ k : Fin 16, power50Expr 5 11 k = power50_r5_11 k := by decide +kernel
lemma power50_r5_12_eq : ∀ k : Fin 16, power50Expr 5 12 k = power50_r5_12 k := by decide +kernel
lemma power50_r5_13_eq : ∀ k : Fin 16, power50Expr 5 13 k = power50_r5_13 k := by decide +kernel
lemma power50_r5_14_eq : ∀ k : Fin 16, power50Expr 5 14 k = power50_r5_14 k := by decide +kernel
lemma power50_r5_15_eq : ∀ k : Fin 16, power50Expr 5 15 k = power50_r5_15 k := by decide +kernel
lemma power50_r5_eq (i k : Fin 16) : power50Expr 5 i k = power50_r5 i k := by
  fin_cases i
  · exact power50_r5_0_eq k
  · exact power50_r5_1_eq k
  · exact power50_r5_2_eq k
  · exact power50_r5_3_eq k
  · exact power50_r5_4_eq k
  · exact power50_r5_5_eq k
  · exact power50_r5_6_eq k
  · exact power50_r5_7_eq k
  · exact power50_r5_8_eq k
  · exact power50_r5_9_eq k
  · exact power50_r5_10_eq k
  · exact power50_r5_11_eq k
  · exact power50_r5_12_eq k
  · exact power50_r5_13_eq k
  · exact power50_r5_14_eq k
  · exact power50_r5_15_eq k
lemma power50_eq (j : Fin 6) (i k : Fin 16) : power50Expr j i k = power50 j i k := by
  fin_cases j
  · exact power50_r0_eq i k
  · exact power50_r1_eq i k
  · exact power50_r2_eq i k
  · exact power50_r3_eq i k
  · exact power50_r4_eq i k
  · exact power50_r5_eq i k
lemma power50_contains (j : Fin 6) (i k : Fin 16) :
    (power50 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(50:ℕ))) := by
  rw [← power50_eq]
  unfold power50Expr
  convert exp_direct_step_e (power49_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers60
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
lemma power51_r0_0_eq : ∀ k : Fin 16, power51Expr 0 0 k = power51_r0_0 k := by decide +kernel
lemma power51_r0_1_eq : ∀ k : Fin 16, power51Expr 0 1 k = power51_r0_1 k := by decide +kernel
lemma power51_r0_2_eq : ∀ k : Fin 16, power51Expr 0 2 k = power51_r0_2 k := by decide +kernel
lemma power51_r0_3_eq : ∀ k : Fin 16, power51Expr 0 3 k = power51_r0_3 k := by decide +kernel
lemma power51_r0_4_eq : ∀ k : Fin 16, power51Expr 0 4 k = power51_r0_4 k := by decide +kernel
lemma power51_r0_5_eq : ∀ k : Fin 16, power51Expr 0 5 k = power51_r0_5 k := by decide +kernel
lemma power51_r0_6_eq : ∀ k : Fin 16, power51Expr 0 6 k = power51_r0_6 k := by decide +kernel
lemma power51_r0_7_eq : ∀ k : Fin 16, power51Expr 0 7 k = power51_r0_7 k := by decide +kernel
lemma power51_r0_8_eq : ∀ k : Fin 16, power51Expr 0 8 k = power51_r0_8 k := by decide +kernel
lemma power51_r0_9_eq : ∀ k : Fin 16, power51Expr 0 9 k = power51_r0_9 k := by decide +kernel
lemma power51_r0_10_eq : ∀ k : Fin 16, power51Expr 0 10 k = power51_r0_10 k := by decide +kernel
lemma power51_r0_11_eq : ∀ k : Fin 16, power51Expr 0 11 k = power51_r0_11 k := by decide +kernel
lemma power51_r0_12_eq : ∀ k : Fin 16, power51Expr 0 12 k = power51_r0_12 k := by decide +kernel
lemma power51_r0_13_eq : ∀ k : Fin 16, power51Expr 0 13 k = power51_r0_13 k := by decide +kernel
lemma power51_r0_14_eq : ∀ k : Fin 16, power51Expr 0 14 k = power51_r0_14 k := by decide +kernel
lemma power51_r0_15_eq : ∀ k : Fin 16, power51Expr 0 15 k = power51_r0_15 k := by decide +kernel
lemma power51_r0_eq (i k : Fin 16) : power51Expr 0 i k = power51_r0 i k := by
  fin_cases i
  · exact power51_r0_0_eq k
  · exact power51_r0_1_eq k
  · exact power51_r0_2_eq k
  · exact power51_r0_3_eq k
  · exact power51_r0_4_eq k
  · exact power51_r0_5_eq k
  · exact power51_r0_6_eq k
  · exact power51_r0_7_eq k
  · exact power51_r0_8_eq k
  · exact power51_r0_9_eq k
  · exact power51_r0_10_eq k
  · exact power51_r0_11_eq k
  · exact power51_r0_12_eq k
  · exact power51_r0_13_eq k
  · exact power51_r0_14_eq k
  · exact power51_r0_15_eq k
lemma power51_r1_0_eq : ∀ k : Fin 16, power51Expr 1 0 k = power51_r1_0 k := by decide +kernel
lemma power51_r1_1_eq : ∀ k : Fin 16, power51Expr 1 1 k = power51_r1_1 k := by decide +kernel
lemma power51_r1_2_eq : ∀ k : Fin 16, power51Expr 1 2 k = power51_r1_2 k := by decide +kernel
lemma power51_r1_3_eq : ∀ k : Fin 16, power51Expr 1 3 k = power51_r1_3 k := by decide +kernel
lemma power51_r1_4_eq : ∀ k : Fin 16, power51Expr 1 4 k = power51_r1_4 k := by decide +kernel
lemma power51_r1_5_eq : ∀ k : Fin 16, power51Expr 1 5 k = power51_r1_5 k := by decide +kernel
lemma power51_r1_6_eq : ∀ k : Fin 16, power51Expr 1 6 k = power51_r1_6 k := by decide +kernel
lemma power51_r1_7_eq : ∀ k : Fin 16, power51Expr 1 7 k = power51_r1_7 k := by decide +kernel
lemma power51_r1_8_eq : ∀ k : Fin 16, power51Expr 1 8 k = power51_r1_8 k := by decide +kernel
lemma power51_r1_9_eq : ∀ k : Fin 16, power51Expr 1 9 k = power51_r1_9 k := by decide +kernel
lemma power51_r1_10_eq : ∀ k : Fin 16, power51Expr 1 10 k = power51_r1_10 k := by decide +kernel
lemma power51_r1_11_eq : ∀ k : Fin 16, power51Expr 1 11 k = power51_r1_11 k := by decide +kernel
lemma power51_r1_12_eq : ∀ k : Fin 16, power51Expr 1 12 k = power51_r1_12 k := by decide +kernel
lemma power51_r1_13_eq : ∀ k : Fin 16, power51Expr 1 13 k = power51_r1_13 k := by decide +kernel
lemma power51_r1_14_eq : ∀ k : Fin 16, power51Expr 1 14 k = power51_r1_14 k := by decide +kernel
lemma power51_r1_15_eq : ∀ k : Fin 16, power51Expr 1 15 k = power51_r1_15 k := by decide +kernel
lemma power51_r1_eq (i k : Fin 16) : power51Expr 1 i k = power51_r1 i k := by
  fin_cases i
  · exact power51_r1_0_eq k
  · exact power51_r1_1_eq k
  · exact power51_r1_2_eq k
  · exact power51_r1_3_eq k
  · exact power51_r1_4_eq k
  · exact power51_r1_5_eq k
  · exact power51_r1_6_eq k
  · exact power51_r1_7_eq k
  · exact power51_r1_8_eq k
  · exact power51_r1_9_eq k
  · exact power51_r1_10_eq k
  · exact power51_r1_11_eq k
  · exact power51_r1_12_eq k
  · exact power51_r1_13_eq k
  · exact power51_r1_14_eq k
  · exact power51_r1_15_eq k
lemma power51_r2_0_eq : ∀ k : Fin 16, power51Expr 2 0 k = power51_r2_0 k := by decide +kernel
lemma power51_r2_1_eq : ∀ k : Fin 16, power51Expr 2 1 k = power51_r2_1 k := by decide +kernel
lemma power51_r2_2_eq : ∀ k : Fin 16, power51Expr 2 2 k = power51_r2_2 k := by decide +kernel
lemma power51_r2_3_eq : ∀ k : Fin 16, power51Expr 2 3 k = power51_r2_3 k := by decide +kernel
lemma power51_r2_4_eq : ∀ k : Fin 16, power51Expr 2 4 k = power51_r2_4 k := by decide +kernel
lemma power51_r2_5_eq : ∀ k : Fin 16, power51Expr 2 5 k = power51_r2_5 k := by decide +kernel
lemma power51_r2_6_eq : ∀ k : Fin 16, power51Expr 2 6 k = power51_r2_6 k := by decide +kernel
lemma power51_r2_7_eq : ∀ k : Fin 16, power51Expr 2 7 k = power51_r2_7 k := by decide +kernel
lemma power51_r2_8_eq : ∀ k : Fin 16, power51Expr 2 8 k = power51_r2_8 k := by decide +kernel
lemma power51_r2_9_eq : ∀ k : Fin 16, power51Expr 2 9 k = power51_r2_9 k := by decide +kernel
lemma power51_r2_10_eq : ∀ k : Fin 16, power51Expr 2 10 k = power51_r2_10 k := by decide +kernel
lemma power51_r2_11_eq : ∀ k : Fin 16, power51Expr 2 11 k = power51_r2_11 k := by decide +kernel
lemma power51_r2_12_eq : ∀ k : Fin 16, power51Expr 2 12 k = power51_r2_12 k := by decide +kernel
lemma power51_r2_13_eq : ∀ k : Fin 16, power51Expr 2 13 k = power51_r2_13 k := by decide +kernel
lemma power51_r2_14_eq : ∀ k : Fin 16, power51Expr 2 14 k = power51_r2_14 k := by decide +kernel
lemma power51_r2_15_eq : ∀ k : Fin 16, power51Expr 2 15 k = power51_r2_15 k := by decide +kernel
lemma power51_r2_eq (i k : Fin 16) : power51Expr 2 i k = power51_r2 i k := by
  fin_cases i
  · exact power51_r2_0_eq k
  · exact power51_r2_1_eq k
  · exact power51_r2_2_eq k
  · exact power51_r2_3_eq k
  · exact power51_r2_4_eq k
  · exact power51_r2_5_eq k
  · exact power51_r2_6_eq k
  · exact power51_r2_7_eq k
  · exact power51_r2_8_eq k
  · exact power51_r2_9_eq k
  · exact power51_r2_10_eq k
  · exact power51_r2_11_eq k
  · exact power51_r2_12_eq k
  · exact power51_r2_13_eq k
  · exact power51_r2_14_eq k
  · exact power51_r2_15_eq k
lemma power51_r3_0_eq : ∀ k : Fin 16, power51Expr 3 0 k = power51_r3_0 k := by decide +kernel
lemma power51_r3_1_eq : ∀ k : Fin 16, power51Expr 3 1 k = power51_r3_1 k := by decide +kernel
lemma power51_r3_2_eq : ∀ k : Fin 16, power51Expr 3 2 k = power51_r3_2 k := by decide +kernel
lemma power51_r3_3_eq : ∀ k : Fin 16, power51Expr 3 3 k = power51_r3_3 k := by decide +kernel
lemma power51_r3_4_eq : ∀ k : Fin 16, power51Expr 3 4 k = power51_r3_4 k := by decide +kernel
lemma power51_r3_5_eq : ∀ k : Fin 16, power51Expr 3 5 k = power51_r3_5 k := by decide +kernel
lemma power51_r3_6_eq : ∀ k : Fin 16, power51Expr 3 6 k = power51_r3_6 k := by decide +kernel
lemma power51_r3_7_eq : ∀ k : Fin 16, power51Expr 3 7 k = power51_r3_7 k := by decide +kernel
lemma power51_r3_8_eq : ∀ k : Fin 16, power51Expr 3 8 k = power51_r3_8 k := by decide +kernel
lemma power51_r3_9_eq : ∀ k : Fin 16, power51Expr 3 9 k = power51_r3_9 k := by decide +kernel
lemma power51_r3_10_eq : ∀ k : Fin 16, power51Expr 3 10 k = power51_r3_10 k := by decide +kernel
lemma power51_r3_11_eq : ∀ k : Fin 16, power51Expr 3 11 k = power51_r3_11 k := by decide +kernel
lemma power51_r3_12_eq : ∀ k : Fin 16, power51Expr 3 12 k = power51_r3_12 k := by decide +kernel
lemma power51_r3_13_eq : ∀ k : Fin 16, power51Expr 3 13 k = power51_r3_13 k := by decide +kernel
lemma power51_r3_14_eq : ∀ k : Fin 16, power51Expr 3 14 k = power51_r3_14 k := by decide +kernel
lemma power51_r3_15_eq : ∀ k : Fin 16, power51Expr 3 15 k = power51_r3_15 k := by decide +kernel
lemma power51_r3_eq (i k : Fin 16) : power51Expr 3 i k = power51_r3 i k := by
  fin_cases i
  · exact power51_r3_0_eq k
  · exact power51_r3_1_eq k
  · exact power51_r3_2_eq k
  · exact power51_r3_3_eq k
  · exact power51_r3_4_eq k
  · exact power51_r3_5_eq k
  · exact power51_r3_6_eq k
  · exact power51_r3_7_eq k
  · exact power51_r3_8_eq k
  · exact power51_r3_9_eq k
  · exact power51_r3_10_eq k
  · exact power51_r3_11_eq k
  · exact power51_r3_12_eq k
  · exact power51_r3_13_eq k
  · exact power51_r3_14_eq k
  · exact power51_r3_15_eq k
lemma power51_r4_0_eq : ∀ k : Fin 16, power51Expr 4 0 k = power51_r4_0 k := by decide +kernel
lemma power51_r4_1_eq : ∀ k : Fin 16, power51Expr 4 1 k = power51_r4_1 k := by decide +kernel
lemma power51_r4_2_eq : ∀ k : Fin 16, power51Expr 4 2 k = power51_r4_2 k := by decide +kernel
lemma power51_r4_3_eq : ∀ k : Fin 16, power51Expr 4 3 k = power51_r4_3 k := by decide +kernel
lemma power51_r4_4_eq : ∀ k : Fin 16, power51Expr 4 4 k = power51_r4_4 k := by decide +kernel
lemma power51_r4_5_eq : ∀ k : Fin 16, power51Expr 4 5 k = power51_r4_5 k := by decide +kernel
lemma power51_r4_6_eq : ∀ k : Fin 16, power51Expr 4 6 k = power51_r4_6 k := by decide +kernel
lemma power51_r4_7_eq : ∀ k : Fin 16, power51Expr 4 7 k = power51_r4_7 k := by decide +kernel
lemma power51_r4_8_eq : ∀ k : Fin 16, power51Expr 4 8 k = power51_r4_8 k := by decide +kernel
lemma power51_r4_9_eq : ∀ k : Fin 16, power51Expr 4 9 k = power51_r4_9 k := by decide +kernel
lemma power51_r4_10_eq : ∀ k : Fin 16, power51Expr 4 10 k = power51_r4_10 k := by decide +kernel
lemma power51_r4_11_eq : ∀ k : Fin 16, power51Expr 4 11 k = power51_r4_11 k := by decide +kernel
lemma power51_r4_12_eq : ∀ k : Fin 16, power51Expr 4 12 k = power51_r4_12 k := by decide +kernel
lemma power51_r4_13_eq : ∀ k : Fin 16, power51Expr 4 13 k = power51_r4_13 k := by decide +kernel
lemma power51_r4_14_eq : ∀ k : Fin 16, power51Expr 4 14 k = power51_r4_14 k := by decide +kernel
lemma power51_r4_15_eq : ∀ k : Fin 16, power51Expr 4 15 k = power51_r4_15 k := by decide +kernel
lemma power51_r4_eq (i k : Fin 16) : power51Expr 4 i k = power51_r4 i k := by
  fin_cases i
  · exact power51_r4_0_eq k
  · exact power51_r4_1_eq k
  · exact power51_r4_2_eq k
  · exact power51_r4_3_eq k
  · exact power51_r4_4_eq k
  · exact power51_r4_5_eq k
  · exact power51_r4_6_eq k
  · exact power51_r4_7_eq k
  · exact power51_r4_8_eq k
  · exact power51_r4_9_eq k
  · exact power51_r4_10_eq k
  · exact power51_r4_11_eq k
  · exact power51_r4_12_eq k
  · exact power51_r4_13_eq k
  · exact power51_r4_14_eq k
  · exact power51_r4_15_eq k
lemma power51_r5_0_eq : ∀ k : Fin 16, power51Expr 5 0 k = power51_r5_0 k := by decide +kernel
lemma power51_r5_1_eq : ∀ k : Fin 16, power51Expr 5 1 k = power51_r5_1 k := by decide +kernel
lemma power51_r5_2_eq : ∀ k : Fin 16, power51Expr 5 2 k = power51_r5_2 k := by decide +kernel
lemma power51_r5_3_eq : ∀ k : Fin 16, power51Expr 5 3 k = power51_r5_3 k := by decide +kernel
lemma power51_r5_4_eq : ∀ k : Fin 16, power51Expr 5 4 k = power51_r5_4 k := by decide +kernel
lemma power51_r5_5_eq : ∀ k : Fin 16, power51Expr 5 5 k = power51_r5_5 k := by decide +kernel
lemma power51_r5_6_eq : ∀ k : Fin 16, power51Expr 5 6 k = power51_r5_6 k := by decide +kernel
lemma power51_r5_7_eq : ∀ k : Fin 16, power51Expr 5 7 k = power51_r5_7 k := by decide +kernel
lemma power51_r5_8_eq : ∀ k : Fin 16, power51Expr 5 8 k = power51_r5_8 k := by decide +kernel
lemma power51_r5_9_eq : ∀ k : Fin 16, power51Expr 5 9 k = power51_r5_9 k := by decide +kernel
lemma power51_r5_10_eq : ∀ k : Fin 16, power51Expr 5 10 k = power51_r5_10 k := by decide +kernel
lemma power51_r5_11_eq : ∀ k : Fin 16, power51Expr 5 11 k = power51_r5_11 k := by decide +kernel
lemma power51_r5_12_eq : ∀ k : Fin 16, power51Expr 5 12 k = power51_r5_12 k := by decide +kernel
lemma power51_r5_13_eq : ∀ k : Fin 16, power51Expr 5 13 k = power51_r5_13 k := by decide +kernel
lemma power51_r5_14_eq : ∀ k : Fin 16, power51Expr 5 14 k = power51_r5_14 k := by decide +kernel
lemma power51_r5_15_eq : ∀ k : Fin 16, power51Expr 5 15 k = power51_r5_15 k := by decide +kernel
lemma power51_r5_eq (i k : Fin 16) : power51Expr 5 i k = power51_r5 i k := by
  fin_cases i
  · exact power51_r5_0_eq k
  · exact power51_r5_1_eq k
  · exact power51_r5_2_eq k
  · exact power51_r5_3_eq k
  · exact power51_r5_4_eq k
  · exact power51_r5_5_eq k
  · exact power51_r5_6_eq k
  · exact power51_r5_7_eq k
  · exact power51_r5_8_eq k
  · exact power51_r5_9_eq k
  · exact power51_r5_10_eq k
  · exact power51_r5_11_eq k
  · exact power51_r5_12_eq k
  · exact power51_r5_13_eq k
  · exact power51_r5_14_eq k
  · exact power51_r5_15_eq k
lemma power51_eq (j : Fin 6) (i k : Fin 16) : power51Expr j i k = power51 j i k := by
  fin_cases j
  · exact power51_r0_eq i k
  · exact power51_r1_eq i k
  · exact power51_r2_eq i k
  · exact power51_r3_eq i k
  · exact power51_r4_eq i k
  · exact power51_r5_eq i k
lemma power51_contains (j : Fin 6) (i k : Fin 16) :
    (power51 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(51:ℕ))) := by
  rw [← power51_eq]
  unfold power51Expr
  convert exp_direct_step_e (power50_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power52_r0_0_eq : ∀ k : Fin 16, power52Expr 0 0 k = power52_r0_0 k := by decide +kernel
lemma power52_r0_1_eq : ∀ k : Fin 16, power52Expr 0 1 k = power52_r0_1 k := by decide +kernel
lemma power52_r0_2_eq : ∀ k : Fin 16, power52Expr 0 2 k = power52_r0_2 k := by decide +kernel
lemma power52_r0_3_eq : ∀ k : Fin 16, power52Expr 0 3 k = power52_r0_3 k := by decide +kernel
lemma power52_r0_4_eq : ∀ k : Fin 16, power52Expr 0 4 k = power52_r0_4 k := by decide +kernel
lemma power52_r0_5_eq : ∀ k : Fin 16, power52Expr 0 5 k = power52_r0_5 k := by decide +kernel
lemma power52_r0_6_eq : ∀ k : Fin 16, power52Expr 0 6 k = power52_r0_6 k := by decide +kernel
lemma power52_r0_7_eq : ∀ k : Fin 16, power52Expr 0 7 k = power52_r0_7 k := by decide +kernel
lemma power52_r0_8_eq : ∀ k : Fin 16, power52Expr 0 8 k = power52_r0_8 k := by decide +kernel
lemma power52_r0_9_eq : ∀ k : Fin 16, power52Expr 0 9 k = power52_r0_9 k := by decide +kernel
lemma power52_r0_10_eq : ∀ k : Fin 16, power52Expr 0 10 k = power52_r0_10 k := by decide +kernel
lemma power52_r0_11_eq : ∀ k : Fin 16, power52Expr 0 11 k = power52_r0_11 k := by decide +kernel
lemma power52_r0_12_eq : ∀ k : Fin 16, power52Expr 0 12 k = power52_r0_12 k := by decide +kernel
lemma power52_r0_13_eq : ∀ k : Fin 16, power52Expr 0 13 k = power52_r0_13 k := by decide +kernel
lemma power52_r0_14_eq : ∀ k : Fin 16, power52Expr 0 14 k = power52_r0_14 k := by decide +kernel
lemma power52_r0_15_eq : ∀ k : Fin 16, power52Expr 0 15 k = power52_r0_15 k := by decide +kernel
lemma power52_r0_eq (i k : Fin 16) : power52Expr 0 i k = power52_r0 i k := by
  fin_cases i
  · exact power52_r0_0_eq k
  · exact power52_r0_1_eq k
  · exact power52_r0_2_eq k
  · exact power52_r0_3_eq k
  · exact power52_r0_4_eq k
  · exact power52_r0_5_eq k
  · exact power52_r0_6_eq k
  · exact power52_r0_7_eq k
  · exact power52_r0_8_eq k
  · exact power52_r0_9_eq k
  · exact power52_r0_10_eq k
  · exact power52_r0_11_eq k
  · exact power52_r0_12_eq k
  · exact power52_r0_13_eq k
  · exact power52_r0_14_eq k
  · exact power52_r0_15_eq k
lemma power52_r1_0_eq : ∀ k : Fin 16, power52Expr 1 0 k = power52_r1_0 k := by decide +kernel
lemma power52_r1_1_eq : ∀ k : Fin 16, power52Expr 1 1 k = power52_r1_1 k := by decide +kernel
lemma power52_r1_2_eq : ∀ k : Fin 16, power52Expr 1 2 k = power52_r1_2 k := by decide +kernel
lemma power52_r1_3_eq : ∀ k : Fin 16, power52Expr 1 3 k = power52_r1_3 k := by decide +kernel
lemma power52_r1_4_eq : ∀ k : Fin 16, power52Expr 1 4 k = power52_r1_4 k := by decide +kernel
lemma power52_r1_5_eq : ∀ k : Fin 16, power52Expr 1 5 k = power52_r1_5 k := by decide +kernel
lemma power52_r1_6_eq : ∀ k : Fin 16, power52Expr 1 6 k = power52_r1_6 k := by decide +kernel
lemma power52_r1_7_eq : ∀ k : Fin 16, power52Expr 1 7 k = power52_r1_7 k := by decide +kernel
lemma power52_r1_8_eq : ∀ k : Fin 16, power52Expr 1 8 k = power52_r1_8 k := by decide +kernel
lemma power52_r1_9_eq : ∀ k : Fin 16, power52Expr 1 9 k = power52_r1_9 k := by decide +kernel
lemma power52_r1_10_eq : ∀ k : Fin 16, power52Expr 1 10 k = power52_r1_10 k := by decide +kernel
lemma power52_r1_11_eq : ∀ k : Fin 16, power52Expr 1 11 k = power52_r1_11 k := by decide +kernel
lemma power52_r1_12_eq : ∀ k : Fin 16, power52Expr 1 12 k = power52_r1_12 k := by decide +kernel
lemma power52_r1_13_eq : ∀ k : Fin 16, power52Expr 1 13 k = power52_r1_13 k := by decide +kernel
lemma power52_r1_14_eq : ∀ k : Fin 16, power52Expr 1 14 k = power52_r1_14 k := by decide +kernel
lemma power52_r1_15_eq : ∀ k : Fin 16, power52Expr 1 15 k = power52_r1_15 k := by decide +kernel
lemma power52_r1_eq (i k : Fin 16) : power52Expr 1 i k = power52_r1 i k := by
  fin_cases i
  · exact power52_r1_0_eq k
  · exact power52_r1_1_eq k
  · exact power52_r1_2_eq k
  · exact power52_r1_3_eq k
  · exact power52_r1_4_eq k
  · exact power52_r1_5_eq k
  · exact power52_r1_6_eq k
  · exact power52_r1_7_eq k
  · exact power52_r1_8_eq k
  · exact power52_r1_9_eq k
  · exact power52_r1_10_eq k
  · exact power52_r1_11_eq k
  · exact power52_r1_12_eq k
  · exact power52_r1_13_eq k
  · exact power52_r1_14_eq k
  · exact power52_r1_15_eq k
lemma power52_r2_0_eq : ∀ k : Fin 16, power52Expr 2 0 k = power52_r2_0 k := by decide +kernel
lemma power52_r2_1_eq : ∀ k : Fin 16, power52Expr 2 1 k = power52_r2_1 k := by decide +kernel
lemma power52_r2_2_eq : ∀ k : Fin 16, power52Expr 2 2 k = power52_r2_2 k := by decide +kernel
lemma power52_r2_3_eq : ∀ k : Fin 16, power52Expr 2 3 k = power52_r2_3 k := by decide +kernel
lemma power52_r2_4_eq : ∀ k : Fin 16, power52Expr 2 4 k = power52_r2_4 k := by decide +kernel
lemma power52_r2_5_eq : ∀ k : Fin 16, power52Expr 2 5 k = power52_r2_5 k := by decide +kernel
lemma power52_r2_6_eq : ∀ k : Fin 16, power52Expr 2 6 k = power52_r2_6 k := by decide +kernel
lemma power52_r2_7_eq : ∀ k : Fin 16, power52Expr 2 7 k = power52_r2_7 k := by decide +kernel
lemma power52_r2_8_eq : ∀ k : Fin 16, power52Expr 2 8 k = power52_r2_8 k := by decide +kernel
lemma power52_r2_9_eq : ∀ k : Fin 16, power52Expr 2 9 k = power52_r2_9 k := by decide +kernel
lemma power52_r2_10_eq : ∀ k : Fin 16, power52Expr 2 10 k = power52_r2_10 k := by decide +kernel
lemma power52_r2_11_eq : ∀ k : Fin 16, power52Expr 2 11 k = power52_r2_11 k := by decide +kernel
lemma power52_r2_12_eq : ∀ k : Fin 16, power52Expr 2 12 k = power52_r2_12 k := by decide +kernel
lemma power52_r2_13_eq : ∀ k : Fin 16, power52Expr 2 13 k = power52_r2_13 k := by decide +kernel
lemma power52_r2_14_eq : ∀ k : Fin 16, power52Expr 2 14 k = power52_r2_14 k := by decide +kernel
lemma power52_r2_15_eq : ∀ k : Fin 16, power52Expr 2 15 k = power52_r2_15 k := by decide +kernel
lemma power52_r2_eq (i k : Fin 16) : power52Expr 2 i k = power52_r2 i k := by
  fin_cases i
  · exact power52_r2_0_eq k
  · exact power52_r2_1_eq k
  · exact power52_r2_2_eq k
  · exact power52_r2_3_eq k
  · exact power52_r2_4_eq k
  · exact power52_r2_5_eq k
  · exact power52_r2_6_eq k
  · exact power52_r2_7_eq k
  · exact power52_r2_8_eq k
  · exact power52_r2_9_eq k
  · exact power52_r2_10_eq k
  · exact power52_r2_11_eq k
  · exact power52_r2_12_eq k
  · exact power52_r2_13_eq k
  · exact power52_r2_14_eq k
  · exact power52_r2_15_eq k
lemma power52_r3_0_eq : ∀ k : Fin 16, power52Expr 3 0 k = power52_r3_0 k := by decide +kernel
lemma power52_r3_1_eq : ∀ k : Fin 16, power52Expr 3 1 k = power52_r3_1 k := by decide +kernel
lemma power52_r3_2_eq : ∀ k : Fin 16, power52Expr 3 2 k = power52_r3_2 k := by decide +kernel
lemma power52_r3_3_eq : ∀ k : Fin 16, power52Expr 3 3 k = power52_r3_3 k := by decide +kernel
lemma power52_r3_4_eq : ∀ k : Fin 16, power52Expr 3 4 k = power52_r3_4 k := by decide +kernel
lemma power52_r3_5_eq : ∀ k : Fin 16, power52Expr 3 5 k = power52_r3_5 k := by decide +kernel
lemma power52_r3_6_eq : ∀ k : Fin 16, power52Expr 3 6 k = power52_r3_6 k := by decide +kernel
lemma power52_r3_7_eq : ∀ k : Fin 16, power52Expr 3 7 k = power52_r3_7 k := by decide +kernel
lemma power52_r3_8_eq : ∀ k : Fin 16, power52Expr 3 8 k = power52_r3_8 k := by decide +kernel
lemma power52_r3_9_eq : ∀ k : Fin 16, power52Expr 3 9 k = power52_r3_9 k := by decide +kernel
lemma power52_r3_10_eq : ∀ k : Fin 16, power52Expr 3 10 k = power52_r3_10 k := by decide +kernel
lemma power52_r3_11_eq : ∀ k : Fin 16, power52Expr 3 11 k = power52_r3_11 k := by decide +kernel
lemma power52_r3_12_eq : ∀ k : Fin 16, power52Expr 3 12 k = power52_r3_12 k := by decide +kernel
lemma power52_r3_13_eq : ∀ k : Fin 16, power52Expr 3 13 k = power52_r3_13 k := by decide +kernel
lemma power52_r3_14_eq : ∀ k : Fin 16, power52Expr 3 14 k = power52_r3_14 k := by decide +kernel
lemma power52_r3_15_eq : ∀ k : Fin 16, power52Expr 3 15 k = power52_r3_15 k := by decide +kernel
lemma power52_r3_eq (i k : Fin 16) : power52Expr 3 i k = power52_r3 i k := by
  fin_cases i
  · exact power52_r3_0_eq k
  · exact power52_r3_1_eq k
  · exact power52_r3_2_eq k
  · exact power52_r3_3_eq k
  · exact power52_r3_4_eq k
  · exact power52_r3_5_eq k
  · exact power52_r3_6_eq k
  · exact power52_r3_7_eq k
  · exact power52_r3_8_eq k
  · exact power52_r3_9_eq k
  · exact power52_r3_10_eq k
  · exact power52_r3_11_eq k
  · exact power52_r3_12_eq k
  · exact power52_r3_13_eq k
  · exact power52_r3_14_eq k
  · exact power52_r3_15_eq k
lemma power52_r4_0_eq : ∀ k : Fin 16, power52Expr 4 0 k = power52_r4_0 k := by decide +kernel
lemma power52_r4_1_eq : ∀ k : Fin 16, power52Expr 4 1 k = power52_r4_1 k := by decide +kernel
lemma power52_r4_2_eq : ∀ k : Fin 16, power52Expr 4 2 k = power52_r4_2 k := by decide +kernel
lemma power52_r4_3_eq : ∀ k : Fin 16, power52Expr 4 3 k = power52_r4_3 k := by decide +kernel
lemma power52_r4_4_eq : ∀ k : Fin 16, power52Expr 4 4 k = power52_r4_4 k := by decide +kernel
lemma power52_r4_5_eq : ∀ k : Fin 16, power52Expr 4 5 k = power52_r4_5 k := by decide +kernel
lemma power52_r4_6_eq : ∀ k : Fin 16, power52Expr 4 6 k = power52_r4_6 k := by decide +kernel
lemma power52_r4_7_eq : ∀ k : Fin 16, power52Expr 4 7 k = power52_r4_7 k := by decide +kernel
lemma power52_r4_8_eq : ∀ k : Fin 16, power52Expr 4 8 k = power52_r4_8 k := by decide +kernel
lemma power52_r4_9_eq : ∀ k : Fin 16, power52Expr 4 9 k = power52_r4_9 k := by decide +kernel
lemma power52_r4_10_eq : ∀ k : Fin 16, power52Expr 4 10 k = power52_r4_10 k := by decide +kernel
lemma power52_r4_11_eq : ∀ k : Fin 16, power52Expr 4 11 k = power52_r4_11 k := by decide +kernel
lemma power52_r4_12_eq : ∀ k : Fin 16, power52Expr 4 12 k = power52_r4_12 k := by decide +kernel
lemma power52_r4_13_eq : ∀ k : Fin 16, power52Expr 4 13 k = power52_r4_13 k := by decide +kernel
lemma power52_r4_14_eq : ∀ k : Fin 16, power52Expr 4 14 k = power52_r4_14 k := by decide +kernel
lemma power52_r4_15_eq : ∀ k : Fin 16, power52Expr 4 15 k = power52_r4_15 k := by decide +kernel
lemma power52_r4_eq (i k : Fin 16) : power52Expr 4 i k = power52_r4 i k := by
  fin_cases i
  · exact power52_r4_0_eq k
  · exact power52_r4_1_eq k
  · exact power52_r4_2_eq k
  · exact power52_r4_3_eq k
  · exact power52_r4_4_eq k
  · exact power52_r4_5_eq k
  · exact power52_r4_6_eq k
  · exact power52_r4_7_eq k
  · exact power52_r4_8_eq k
  · exact power52_r4_9_eq k
  · exact power52_r4_10_eq k
  · exact power52_r4_11_eq k
  · exact power52_r4_12_eq k
  · exact power52_r4_13_eq k
  · exact power52_r4_14_eq k
  · exact power52_r4_15_eq k
lemma power52_r5_0_eq : ∀ k : Fin 16, power52Expr 5 0 k = power52_r5_0 k := by decide +kernel
lemma power52_r5_1_eq : ∀ k : Fin 16, power52Expr 5 1 k = power52_r5_1 k := by decide +kernel
lemma power52_r5_2_eq : ∀ k : Fin 16, power52Expr 5 2 k = power52_r5_2 k := by decide +kernel
lemma power52_r5_3_eq : ∀ k : Fin 16, power52Expr 5 3 k = power52_r5_3 k := by decide +kernel
lemma power52_r5_4_eq : ∀ k : Fin 16, power52Expr 5 4 k = power52_r5_4 k := by decide +kernel
lemma power52_r5_5_eq : ∀ k : Fin 16, power52Expr 5 5 k = power52_r5_5 k := by decide +kernel
lemma power52_r5_6_eq : ∀ k : Fin 16, power52Expr 5 6 k = power52_r5_6 k := by decide +kernel
lemma power52_r5_7_eq : ∀ k : Fin 16, power52Expr 5 7 k = power52_r5_7 k := by decide +kernel
lemma power52_r5_8_eq : ∀ k : Fin 16, power52Expr 5 8 k = power52_r5_8 k := by decide +kernel
lemma power52_r5_9_eq : ∀ k : Fin 16, power52Expr 5 9 k = power52_r5_9 k := by decide +kernel
lemma power52_r5_10_eq : ∀ k : Fin 16, power52Expr 5 10 k = power52_r5_10 k := by decide +kernel
lemma power52_r5_11_eq : ∀ k : Fin 16, power52Expr 5 11 k = power52_r5_11 k := by decide +kernel
lemma power52_r5_12_eq : ∀ k : Fin 16, power52Expr 5 12 k = power52_r5_12 k := by decide +kernel
lemma power52_r5_13_eq : ∀ k : Fin 16, power52Expr 5 13 k = power52_r5_13 k := by decide +kernel
lemma power52_r5_14_eq : ∀ k : Fin 16, power52Expr 5 14 k = power52_r5_14 k := by decide +kernel
lemma power52_r5_15_eq : ∀ k : Fin 16, power52Expr 5 15 k = power52_r5_15 k := by decide +kernel
lemma power52_r5_eq (i k : Fin 16) : power52Expr 5 i k = power52_r5 i k := by
  fin_cases i
  · exact power52_r5_0_eq k
  · exact power52_r5_1_eq k
  · exact power52_r5_2_eq k
  · exact power52_r5_3_eq k
  · exact power52_r5_4_eq k
  · exact power52_r5_5_eq k
  · exact power52_r5_6_eq k
  · exact power52_r5_7_eq k
  · exact power52_r5_8_eq k
  · exact power52_r5_9_eq k
  · exact power52_r5_10_eq k
  · exact power52_r5_11_eq k
  · exact power52_r5_12_eq k
  · exact power52_r5_13_eq k
  · exact power52_r5_14_eq k
  · exact power52_r5_15_eq k
lemma power52_eq (j : Fin 6) (i k : Fin 16) : power52Expr j i k = power52 j i k := by
  fin_cases j
  · exact power52_r0_eq i k
  · exact power52_r1_eq i k
  · exact power52_r2_eq i k
  · exact power52_r3_eq i k
  · exact power52_r4_eq i k
  · exact power52_r5_eq i k
lemma power52_contains (j : Fin 6) (i k : Fin 16) :
    (power52 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(52:ℕ))) := by
  rw [← power52_eq]
  unfold power52Expr
  convert exp_direct_step_e (power51_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns60
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
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
lemma column52_0_r0_0_eq : ∀ k : Fin 16, column52_0Expr 0 0 k = column52_0_r0_0 k := by decide +kernel
lemma column52_0_r0_1_eq : ∀ k : Fin 16, column52_0Expr 0 1 k = column52_0_r0_1 k := by decide +kernel
lemma column52_0_r0_2_eq : ∀ k : Fin 16, column52_0Expr 0 2 k = column52_0_r0_2 k := by decide +kernel
lemma column52_0_r0_3_eq : ∀ k : Fin 16, column52_0Expr 0 3 k = column52_0_r0_3 k := by decide +kernel
lemma column52_0_r0_4_eq : ∀ k : Fin 16, column52_0Expr 0 4 k = column52_0_r0_4 k := by decide +kernel
lemma column52_0_r0_5_eq : ∀ k : Fin 16, column52_0Expr 0 5 k = column52_0_r0_5 k := by decide +kernel
lemma column52_0_r0_6_eq : ∀ k : Fin 16, column52_0Expr 0 6 k = column52_0_r0_6 k := by decide +kernel
lemma column52_0_r0_7_eq : ∀ k : Fin 16, column52_0Expr 0 7 k = column52_0_r0_7 k := by decide +kernel
lemma column52_0_r0_8_eq : ∀ k : Fin 16, column52_0Expr 0 8 k = column52_0_r0_8 k := by decide +kernel
lemma column52_0_r0_9_eq : ∀ k : Fin 16, column52_0Expr 0 9 k = column52_0_r0_9 k := by decide +kernel
lemma column52_0_r0_10_eq : ∀ k : Fin 16, column52_0Expr 0 10 k = column52_0_r0_10 k := by decide +kernel
lemma column52_0_r0_11_eq : ∀ k : Fin 16, column52_0Expr 0 11 k = column52_0_r0_11 k := by decide +kernel
lemma column52_0_r0_12_eq : ∀ k : Fin 16, column52_0Expr 0 12 k = column52_0_r0_12 k := by decide +kernel
lemma column52_0_r0_13_eq : ∀ k : Fin 16, column52_0Expr 0 13 k = column52_0_r0_13 k := by decide +kernel
lemma column52_0_r0_14_eq : ∀ k : Fin 16, column52_0Expr 0 14 k = column52_0_r0_14 k := by decide +kernel
lemma column52_0_r0_15_eq : ∀ k : Fin 16, column52_0Expr 0 15 k = column52_0_r0_15 k := by decide +kernel
lemma column52_0_r0_eq (i k : Fin 16) : column52_0Expr 0 i k = column52_0_r0 i k := by
  fin_cases i
  · exact column52_0_r0_0_eq k
  · exact column52_0_r0_1_eq k
  · exact column52_0_r0_2_eq k
  · exact column52_0_r0_3_eq k
  · exact column52_0_r0_4_eq k
  · exact column52_0_r0_5_eq k
  · exact column52_0_r0_6_eq k
  · exact column52_0_r0_7_eq k
  · exact column52_0_r0_8_eq k
  · exact column52_0_r0_9_eq k
  · exact column52_0_r0_10_eq k
  · exact column52_0_r0_11_eq k
  · exact column52_0_r0_12_eq k
  · exact column52_0_r0_13_eq k
  · exact column52_0_r0_14_eq k
  · exact column52_0_r0_15_eq k
lemma column52_0_r1_0_eq : ∀ k : Fin 16, column52_0Expr 1 0 k = column52_0_r1_0 k := by decide +kernel
lemma column52_0_r1_1_eq : ∀ k : Fin 16, column52_0Expr 1 1 k = column52_0_r1_1 k := by decide +kernel
lemma column52_0_r1_2_eq : ∀ k : Fin 16, column52_0Expr 1 2 k = column52_0_r1_2 k := by decide +kernel
lemma column52_0_r1_3_eq : ∀ k : Fin 16, column52_0Expr 1 3 k = column52_0_r1_3 k := by decide +kernel
lemma column52_0_r1_4_eq : ∀ k : Fin 16, column52_0Expr 1 4 k = column52_0_r1_4 k := by decide +kernel
lemma column52_0_r1_5_eq : ∀ k : Fin 16, column52_0Expr 1 5 k = column52_0_r1_5 k := by decide +kernel
lemma column52_0_r1_6_eq : ∀ k : Fin 16, column52_0Expr 1 6 k = column52_0_r1_6 k := by decide +kernel
lemma column52_0_r1_7_eq : ∀ k : Fin 16, column52_0Expr 1 7 k = column52_0_r1_7 k := by decide +kernel
lemma column52_0_r1_8_eq : ∀ k : Fin 16, column52_0Expr 1 8 k = column52_0_r1_8 k := by decide +kernel
lemma column52_0_r1_9_eq : ∀ k : Fin 16, column52_0Expr 1 9 k = column52_0_r1_9 k := by decide +kernel
lemma column52_0_r1_10_eq : ∀ k : Fin 16, column52_0Expr 1 10 k = column52_0_r1_10 k := by decide +kernel
lemma column52_0_r1_11_eq : ∀ k : Fin 16, column52_0Expr 1 11 k = column52_0_r1_11 k := by decide +kernel
lemma column52_0_r1_12_eq : ∀ k : Fin 16, column52_0Expr 1 12 k = column52_0_r1_12 k := by decide +kernel
lemma column52_0_r1_13_eq : ∀ k : Fin 16, column52_0Expr 1 13 k = column52_0_r1_13 k := by decide +kernel
lemma column52_0_r1_14_eq : ∀ k : Fin 16, column52_0Expr 1 14 k = column52_0_r1_14 k := by decide +kernel
lemma column52_0_r1_15_eq : ∀ k : Fin 16, column52_0Expr 1 15 k = column52_0_r1_15 k := by decide +kernel
lemma column52_0_r1_eq (i k : Fin 16) : column52_0Expr 1 i k = column52_0_r1 i k := by
  fin_cases i
  · exact column52_0_r1_0_eq k
  · exact column52_0_r1_1_eq k
  · exact column52_0_r1_2_eq k
  · exact column52_0_r1_3_eq k
  · exact column52_0_r1_4_eq k
  · exact column52_0_r1_5_eq k
  · exact column52_0_r1_6_eq k
  · exact column52_0_r1_7_eq k
  · exact column52_0_r1_8_eq k
  · exact column52_0_r1_9_eq k
  · exact column52_0_r1_10_eq k
  · exact column52_0_r1_11_eq k
  · exact column52_0_r1_12_eq k
  · exact column52_0_r1_13_eq k
  · exact column52_0_r1_14_eq k
  · exact column52_0_r1_15_eq k
lemma column52_0_r2_0_eq : ∀ k : Fin 16, column52_0Expr 2 0 k = column52_0_r2_0 k := by decide +kernel
lemma column52_0_r2_1_eq : ∀ k : Fin 16, column52_0Expr 2 1 k = column52_0_r2_1 k := by decide +kernel
lemma column52_0_r2_2_eq : ∀ k : Fin 16, column52_0Expr 2 2 k = column52_0_r2_2 k := by decide +kernel
lemma column52_0_r2_3_eq : ∀ k : Fin 16, column52_0Expr 2 3 k = column52_0_r2_3 k := by decide +kernel
lemma column52_0_r2_4_eq : ∀ k : Fin 16, column52_0Expr 2 4 k = column52_0_r2_4 k := by decide +kernel
lemma column52_0_r2_5_eq : ∀ k : Fin 16, column52_0Expr 2 5 k = column52_0_r2_5 k := by decide +kernel
lemma column52_0_r2_6_eq : ∀ k : Fin 16, column52_0Expr 2 6 k = column52_0_r2_6 k := by decide +kernel
lemma column52_0_r2_7_eq : ∀ k : Fin 16, column52_0Expr 2 7 k = column52_0_r2_7 k := by decide +kernel
lemma column52_0_r2_8_eq : ∀ k : Fin 16, column52_0Expr 2 8 k = column52_0_r2_8 k := by decide +kernel
lemma column52_0_r2_9_eq : ∀ k : Fin 16, column52_0Expr 2 9 k = column52_0_r2_9 k := by decide +kernel
lemma column52_0_r2_10_eq : ∀ k : Fin 16, column52_0Expr 2 10 k = column52_0_r2_10 k := by decide +kernel
lemma column52_0_r2_11_eq : ∀ k : Fin 16, column52_0Expr 2 11 k = column52_0_r2_11 k := by decide +kernel
lemma column52_0_r2_12_eq : ∀ k : Fin 16, column52_0Expr 2 12 k = column52_0_r2_12 k := by decide +kernel
lemma column52_0_r2_13_eq : ∀ k : Fin 16, column52_0Expr 2 13 k = column52_0_r2_13 k := by decide +kernel
lemma column52_0_r2_14_eq : ∀ k : Fin 16, column52_0Expr 2 14 k = column52_0_r2_14 k := by decide +kernel
lemma column52_0_r2_15_eq : ∀ k : Fin 16, column52_0Expr 2 15 k = column52_0_r2_15 k := by decide +kernel
lemma column52_0_r2_eq (i k : Fin 16) : column52_0Expr 2 i k = column52_0_r2 i k := by
  fin_cases i
  · exact column52_0_r2_0_eq k
  · exact column52_0_r2_1_eq k
  · exact column52_0_r2_2_eq k
  · exact column52_0_r2_3_eq k
  · exact column52_0_r2_4_eq k
  · exact column52_0_r2_5_eq k
  · exact column52_0_r2_6_eq k
  · exact column52_0_r2_7_eq k
  · exact column52_0_r2_8_eq k
  · exact column52_0_r2_9_eq k
  · exact column52_0_r2_10_eq k
  · exact column52_0_r2_11_eq k
  · exact column52_0_r2_12_eq k
  · exact column52_0_r2_13_eq k
  · exact column52_0_r2_14_eq k
  · exact column52_0_r2_15_eq k
lemma column52_0_r3_0_eq : ∀ k : Fin 16, column52_0Expr 3 0 k = column52_0_r3_0 k := by decide +kernel
lemma column52_0_r3_1_eq : ∀ k : Fin 16, column52_0Expr 3 1 k = column52_0_r3_1 k := by decide +kernel
lemma column52_0_r3_2_eq : ∀ k : Fin 16, column52_0Expr 3 2 k = column52_0_r3_2 k := by decide +kernel
lemma column52_0_r3_3_eq : ∀ k : Fin 16, column52_0Expr 3 3 k = column52_0_r3_3 k := by decide +kernel
lemma column52_0_r3_4_eq : ∀ k : Fin 16, column52_0Expr 3 4 k = column52_0_r3_4 k := by decide +kernel
lemma column52_0_r3_5_eq : ∀ k : Fin 16, column52_0Expr 3 5 k = column52_0_r3_5 k := by decide +kernel
lemma column52_0_r3_6_eq : ∀ k : Fin 16, column52_0Expr 3 6 k = column52_0_r3_6 k := by decide +kernel
lemma column52_0_r3_7_eq : ∀ k : Fin 16, column52_0Expr 3 7 k = column52_0_r3_7 k := by decide +kernel
lemma column52_0_r3_8_eq : ∀ k : Fin 16, column52_0Expr 3 8 k = column52_0_r3_8 k := by decide +kernel
lemma column52_0_r3_9_eq : ∀ k : Fin 16, column52_0Expr 3 9 k = column52_0_r3_9 k := by decide +kernel
lemma column52_0_r3_10_eq : ∀ k : Fin 16, column52_0Expr 3 10 k = column52_0_r3_10 k := by decide +kernel
lemma column52_0_r3_11_eq : ∀ k : Fin 16, column52_0Expr 3 11 k = column52_0_r3_11 k := by decide +kernel
lemma column52_0_r3_12_eq : ∀ k : Fin 16, column52_0Expr 3 12 k = column52_0_r3_12 k := by decide +kernel
lemma column52_0_r3_13_eq : ∀ k : Fin 16, column52_0Expr 3 13 k = column52_0_r3_13 k := by decide +kernel
lemma column52_0_r3_14_eq : ∀ k : Fin 16, column52_0Expr 3 14 k = column52_0_r3_14 k := by decide +kernel
lemma column52_0_r3_15_eq : ∀ k : Fin 16, column52_0Expr 3 15 k = column52_0_r3_15 k := by decide +kernel
lemma column52_0_r3_eq (i k : Fin 16) : column52_0Expr 3 i k = column52_0_r3 i k := by
  fin_cases i
  · exact column52_0_r3_0_eq k
  · exact column52_0_r3_1_eq k
  · exact column52_0_r3_2_eq k
  · exact column52_0_r3_3_eq k
  · exact column52_0_r3_4_eq k
  · exact column52_0_r3_5_eq k
  · exact column52_0_r3_6_eq k
  · exact column52_0_r3_7_eq k
  · exact column52_0_r3_8_eq k
  · exact column52_0_r3_9_eq k
  · exact column52_0_r3_10_eq k
  · exact column52_0_r3_11_eq k
  · exact column52_0_r3_12_eq k
  · exact column52_0_r3_13_eq k
  · exact column52_0_r3_14_eq k
  · exact column52_0_r3_15_eq k
lemma column52_0_r4_0_eq : ∀ k : Fin 16, column52_0Expr 4 0 k = column52_0_r4_0 k := by decide +kernel
lemma column52_0_r4_1_eq : ∀ k : Fin 16, column52_0Expr 4 1 k = column52_0_r4_1 k := by decide +kernel
lemma column52_0_r4_2_eq : ∀ k : Fin 16, column52_0Expr 4 2 k = column52_0_r4_2 k := by decide +kernel
lemma column52_0_r4_3_eq : ∀ k : Fin 16, column52_0Expr 4 3 k = column52_0_r4_3 k := by decide +kernel
lemma column52_0_r4_4_eq : ∀ k : Fin 16, column52_0Expr 4 4 k = column52_0_r4_4 k := by decide +kernel
lemma column52_0_r4_5_eq : ∀ k : Fin 16, column52_0Expr 4 5 k = column52_0_r4_5 k := by decide +kernel
lemma column52_0_r4_6_eq : ∀ k : Fin 16, column52_0Expr 4 6 k = column52_0_r4_6 k := by decide +kernel
lemma column52_0_r4_7_eq : ∀ k : Fin 16, column52_0Expr 4 7 k = column52_0_r4_7 k := by decide +kernel
lemma column52_0_r4_8_eq : ∀ k : Fin 16, column52_0Expr 4 8 k = column52_0_r4_8 k := by decide +kernel
lemma column52_0_r4_9_eq : ∀ k : Fin 16, column52_0Expr 4 9 k = column52_0_r4_9 k := by decide +kernel
lemma column52_0_r4_10_eq : ∀ k : Fin 16, column52_0Expr 4 10 k = column52_0_r4_10 k := by decide +kernel
lemma column52_0_r4_11_eq : ∀ k : Fin 16, column52_0Expr 4 11 k = column52_0_r4_11 k := by decide +kernel
lemma column52_0_r4_12_eq : ∀ k : Fin 16, column52_0Expr 4 12 k = column52_0_r4_12 k := by decide +kernel
lemma column52_0_r4_13_eq : ∀ k : Fin 16, column52_0Expr 4 13 k = column52_0_r4_13 k := by decide +kernel
lemma column52_0_r4_14_eq : ∀ k : Fin 16, column52_0Expr 4 14 k = column52_0_r4_14 k := by decide +kernel
lemma column52_0_r4_15_eq : ∀ k : Fin 16, column52_0Expr 4 15 k = column52_0_r4_15 k := by decide +kernel
lemma column52_0_r4_eq (i k : Fin 16) : column52_0Expr 4 i k = column52_0_r4 i k := by
  fin_cases i
  · exact column52_0_r4_0_eq k
  · exact column52_0_r4_1_eq k
  · exact column52_0_r4_2_eq k
  · exact column52_0_r4_3_eq k
  · exact column52_0_r4_4_eq k
  · exact column52_0_r4_5_eq k
  · exact column52_0_r4_6_eq k
  · exact column52_0_r4_7_eq k
  · exact column52_0_r4_8_eq k
  · exact column52_0_r4_9_eq k
  · exact column52_0_r4_10_eq k
  · exact column52_0_r4_11_eq k
  · exact column52_0_r4_12_eq k
  · exact column52_0_r4_13_eq k
  · exact column52_0_r4_14_eq k
  · exact column52_0_r4_15_eq k
lemma column52_0_r5_0_eq : ∀ k : Fin 16, column52_0Expr 5 0 k = column52_0_r5_0 k := by decide +kernel
lemma column52_0_r5_1_eq : ∀ k : Fin 16, column52_0Expr 5 1 k = column52_0_r5_1 k := by decide +kernel
lemma column52_0_r5_2_eq : ∀ k : Fin 16, column52_0Expr 5 2 k = column52_0_r5_2 k := by decide +kernel
lemma column52_0_r5_3_eq : ∀ k : Fin 16, column52_0Expr 5 3 k = column52_0_r5_3 k := by decide +kernel
lemma column52_0_r5_4_eq : ∀ k : Fin 16, column52_0Expr 5 4 k = column52_0_r5_4 k := by decide +kernel
lemma column52_0_r5_5_eq : ∀ k : Fin 16, column52_0Expr 5 5 k = column52_0_r5_5 k := by decide +kernel
lemma column52_0_r5_6_eq : ∀ k : Fin 16, column52_0Expr 5 6 k = column52_0_r5_6 k := by decide +kernel
lemma column52_0_r5_7_eq : ∀ k : Fin 16, column52_0Expr 5 7 k = column52_0_r5_7 k := by decide +kernel
lemma column52_0_r5_8_eq : ∀ k : Fin 16, column52_0Expr 5 8 k = column52_0_r5_8 k := by decide +kernel
lemma column52_0_r5_9_eq : ∀ k : Fin 16, column52_0Expr 5 9 k = column52_0_r5_9 k := by decide +kernel
lemma column52_0_r5_10_eq : ∀ k : Fin 16, column52_0Expr 5 10 k = column52_0_r5_10 k := by decide +kernel
lemma column52_0_r5_11_eq : ∀ k : Fin 16, column52_0Expr 5 11 k = column52_0_r5_11 k := by decide +kernel
lemma column52_0_r5_12_eq : ∀ k : Fin 16, column52_0Expr 5 12 k = column52_0_r5_12 k := by decide +kernel
lemma column52_0_r5_13_eq : ∀ k : Fin 16, column52_0Expr 5 13 k = column52_0_r5_13 k := by decide +kernel
lemma column52_0_r5_14_eq : ∀ k : Fin 16, column52_0Expr 5 14 k = column52_0_r5_14 k := by decide +kernel
lemma column52_0_r5_15_eq : ∀ k : Fin 16, column52_0Expr 5 15 k = column52_0_r5_15 k := by decide +kernel
lemma column52_0_r5_eq (i k : Fin 16) : column52_0Expr 5 i k = column52_0_r5 i k := by
  fin_cases i
  · exact column52_0_r5_0_eq k
  · exact column52_0_r5_1_eq k
  · exact column52_0_r5_2_eq k
  · exact column52_0_r5_3_eq k
  · exact column52_0_r5_4_eq k
  · exact column52_0_r5_5_eq k
  · exact column52_0_r5_6_eq k
  · exact column52_0_r5_7_eq k
  · exact column52_0_r5_8_eq k
  · exact column52_0_r5_9_eq k
  · exact column52_0_r5_10_eq k
  · exact column52_0_r5_11_eq k
  · exact column52_0_r5_12_eq k
  · exact column52_0_r5_13_eq k
  · exact column52_0_r5_14_eq k
  · exact column52_0_r5_15_eq k
lemma column52_0_eq (j : Fin 6) (i k : Fin 16) : column52_0Expr j i k = column52_0 j i k := by
  fin_cases j
  · exact column52_0_r0_eq i k
  · exact column52_0_r1_eq i k
  · exact column52_0_r2_eq i k
  · exact column52_0_r3_eq i k
  · exact column52_0_r4_eq i k
  · exact column52_0_r5_eq i k
lemma column52_0_contains_e_oai (j : Fin 6) (i k : Fin 16) :
    (column52_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction false 52 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column52_0_eq,basisFunction_wave,← mul_assoc]
  unfold column52_0Expr
  apply CBox.contains_mul_e
  · rw [← waveAmplitude_mod false 52 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp4_0_contains_e j i k
  · exact power52_contains j i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.column52_0_contains_e_oai := @OAI.SharpPlanar.CachedData.column52_0_contains_e_oai
