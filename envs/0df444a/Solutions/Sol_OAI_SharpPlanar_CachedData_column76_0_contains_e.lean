-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.column76_0_contains_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T23:52:40.921432+00:00
-- url     : https://prove2.me/submissions/b7d217d6-9911-43cf-8d78-5771c717c7b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_CachedData_amp4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_power72_contains_e
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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers80
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
lemma power73_r0_0_eq : ∀ k : Fin 16, power73Expr 0 0 k = power73_r0_0 k := by decide +kernel
lemma power73_r0_1_eq : ∀ k : Fin 16, power73Expr 0 1 k = power73_r0_1 k := by decide +kernel
lemma power73_r0_2_eq : ∀ k : Fin 16, power73Expr 0 2 k = power73_r0_2 k := by decide +kernel
lemma power73_r0_3_eq : ∀ k : Fin 16, power73Expr 0 3 k = power73_r0_3 k := by decide +kernel
lemma power73_r0_4_eq : ∀ k : Fin 16, power73Expr 0 4 k = power73_r0_4 k := by decide +kernel
lemma power73_r0_5_eq : ∀ k : Fin 16, power73Expr 0 5 k = power73_r0_5 k := by decide +kernel
lemma power73_r0_6_eq : ∀ k : Fin 16, power73Expr 0 6 k = power73_r0_6 k := by decide +kernel
lemma power73_r0_7_eq : ∀ k : Fin 16, power73Expr 0 7 k = power73_r0_7 k := by decide +kernel
lemma power73_r0_8_eq : ∀ k : Fin 16, power73Expr 0 8 k = power73_r0_8 k := by decide +kernel
lemma power73_r0_9_eq : ∀ k : Fin 16, power73Expr 0 9 k = power73_r0_9 k := by decide +kernel
lemma power73_r0_10_eq : ∀ k : Fin 16, power73Expr 0 10 k = power73_r0_10 k := by decide +kernel
lemma power73_r0_11_eq : ∀ k : Fin 16, power73Expr 0 11 k = power73_r0_11 k := by decide +kernel
lemma power73_r0_12_eq : ∀ k : Fin 16, power73Expr 0 12 k = power73_r0_12 k := by decide +kernel
lemma power73_r0_13_eq : ∀ k : Fin 16, power73Expr 0 13 k = power73_r0_13 k := by decide +kernel
lemma power73_r0_14_eq : ∀ k : Fin 16, power73Expr 0 14 k = power73_r0_14 k := by decide +kernel
lemma power73_r0_15_eq : ∀ k : Fin 16, power73Expr 0 15 k = power73_r0_15 k := by decide +kernel
lemma power73_r0_eq (i k : Fin 16) : power73Expr 0 i k = power73_r0 i k := by
  fin_cases i
  · exact power73_r0_0_eq k
  · exact power73_r0_1_eq k
  · exact power73_r0_2_eq k
  · exact power73_r0_3_eq k
  · exact power73_r0_4_eq k
  · exact power73_r0_5_eq k
  · exact power73_r0_6_eq k
  · exact power73_r0_7_eq k
  · exact power73_r0_8_eq k
  · exact power73_r0_9_eq k
  · exact power73_r0_10_eq k
  · exact power73_r0_11_eq k
  · exact power73_r0_12_eq k
  · exact power73_r0_13_eq k
  · exact power73_r0_14_eq k
  · exact power73_r0_15_eq k
lemma power73_r1_0_eq : ∀ k : Fin 16, power73Expr 1 0 k = power73_r1_0 k := by decide +kernel
lemma power73_r1_1_eq : ∀ k : Fin 16, power73Expr 1 1 k = power73_r1_1 k := by decide +kernel
lemma power73_r1_2_eq : ∀ k : Fin 16, power73Expr 1 2 k = power73_r1_2 k := by decide +kernel
lemma power73_r1_3_eq : ∀ k : Fin 16, power73Expr 1 3 k = power73_r1_3 k := by decide +kernel
lemma power73_r1_4_eq : ∀ k : Fin 16, power73Expr 1 4 k = power73_r1_4 k := by decide +kernel
lemma power73_r1_5_eq : ∀ k : Fin 16, power73Expr 1 5 k = power73_r1_5 k := by decide +kernel
lemma power73_r1_6_eq : ∀ k : Fin 16, power73Expr 1 6 k = power73_r1_6 k := by decide +kernel
lemma power73_r1_7_eq : ∀ k : Fin 16, power73Expr 1 7 k = power73_r1_7 k := by decide +kernel
lemma power73_r1_8_eq : ∀ k : Fin 16, power73Expr 1 8 k = power73_r1_8 k := by decide +kernel
lemma power73_r1_9_eq : ∀ k : Fin 16, power73Expr 1 9 k = power73_r1_9 k := by decide +kernel
lemma power73_r1_10_eq : ∀ k : Fin 16, power73Expr 1 10 k = power73_r1_10 k := by decide +kernel
lemma power73_r1_11_eq : ∀ k : Fin 16, power73Expr 1 11 k = power73_r1_11 k := by decide +kernel
lemma power73_r1_12_eq : ∀ k : Fin 16, power73Expr 1 12 k = power73_r1_12 k := by decide +kernel
lemma power73_r1_13_eq : ∀ k : Fin 16, power73Expr 1 13 k = power73_r1_13 k := by decide +kernel
lemma power73_r1_14_eq : ∀ k : Fin 16, power73Expr 1 14 k = power73_r1_14 k := by decide +kernel
lemma power73_r1_15_eq : ∀ k : Fin 16, power73Expr 1 15 k = power73_r1_15 k := by decide +kernel
lemma power73_r1_eq (i k : Fin 16) : power73Expr 1 i k = power73_r1 i k := by
  fin_cases i
  · exact power73_r1_0_eq k
  · exact power73_r1_1_eq k
  · exact power73_r1_2_eq k
  · exact power73_r1_3_eq k
  · exact power73_r1_4_eq k
  · exact power73_r1_5_eq k
  · exact power73_r1_6_eq k
  · exact power73_r1_7_eq k
  · exact power73_r1_8_eq k
  · exact power73_r1_9_eq k
  · exact power73_r1_10_eq k
  · exact power73_r1_11_eq k
  · exact power73_r1_12_eq k
  · exact power73_r1_13_eq k
  · exact power73_r1_14_eq k
  · exact power73_r1_15_eq k
lemma power73_r2_0_eq : ∀ k : Fin 16, power73Expr 2 0 k = power73_r2_0 k := by decide +kernel
lemma power73_r2_1_eq : ∀ k : Fin 16, power73Expr 2 1 k = power73_r2_1 k := by decide +kernel
lemma power73_r2_2_eq : ∀ k : Fin 16, power73Expr 2 2 k = power73_r2_2 k := by decide +kernel
lemma power73_r2_3_eq : ∀ k : Fin 16, power73Expr 2 3 k = power73_r2_3 k := by decide +kernel
lemma power73_r2_4_eq : ∀ k : Fin 16, power73Expr 2 4 k = power73_r2_4 k := by decide +kernel
lemma power73_r2_5_eq : ∀ k : Fin 16, power73Expr 2 5 k = power73_r2_5 k := by decide +kernel
lemma power73_r2_6_eq : ∀ k : Fin 16, power73Expr 2 6 k = power73_r2_6 k := by decide +kernel
lemma power73_r2_7_eq : ∀ k : Fin 16, power73Expr 2 7 k = power73_r2_7 k := by decide +kernel
lemma power73_r2_8_eq : ∀ k : Fin 16, power73Expr 2 8 k = power73_r2_8 k := by decide +kernel
lemma power73_r2_9_eq : ∀ k : Fin 16, power73Expr 2 9 k = power73_r2_9 k := by decide +kernel
lemma power73_r2_10_eq : ∀ k : Fin 16, power73Expr 2 10 k = power73_r2_10 k := by decide +kernel
lemma power73_r2_11_eq : ∀ k : Fin 16, power73Expr 2 11 k = power73_r2_11 k := by decide +kernel
lemma power73_r2_12_eq : ∀ k : Fin 16, power73Expr 2 12 k = power73_r2_12 k := by decide +kernel
lemma power73_r2_13_eq : ∀ k : Fin 16, power73Expr 2 13 k = power73_r2_13 k := by decide +kernel
lemma power73_r2_14_eq : ∀ k : Fin 16, power73Expr 2 14 k = power73_r2_14 k := by decide +kernel
lemma power73_r2_15_eq : ∀ k : Fin 16, power73Expr 2 15 k = power73_r2_15 k := by decide +kernel
lemma power73_r2_eq (i k : Fin 16) : power73Expr 2 i k = power73_r2 i k := by
  fin_cases i
  · exact power73_r2_0_eq k
  · exact power73_r2_1_eq k
  · exact power73_r2_2_eq k
  · exact power73_r2_3_eq k
  · exact power73_r2_4_eq k
  · exact power73_r2_5_eq k
  · exact power73_r2_6_eq k
  · exact power73_r2_7_eq k
  · exact power73_r2_8_eq k
  · exact power73_r2_9_eq k
  · exact power73_r2_10_eq k
  · exact power73_r2_11_eq k
  · exact power73_r2_12_eq k
  · exact power73_r2_13_eq k
  · exact power73_r2_14_eq k
  · exact power73_r2_15_eq k
lemma power73_r3_0_eq : ∀ k : Fin 16, power73Expr 3 0 k = power73_r3_0 k := by decide +kernel
lemma power73_r3_1_eq : ∀ k : Fin 16, power73Expr 3 1 k = power73_r3_1 k := by decide +kernel
lemma power73_r3_2_eq : ∀ k : Fin 16, power73Expr 3 2 k = power73_r3_2 k := by decide +kernel
lemma power73_r3_3_eq : ∀ k : Fin 16, power73Expr 3 3 k = power73_r3_3 k := by decide +kernel
lemma power73_r3_4_eq : ∀ k : Fin 16, power73Expr 3 4 k = power73_r3_4 k := by decide +kernel
lemma power73_r3_5_eq : ∀ k : Fin 16, power73Expr 3 5 k = power73_r3_5 k := by decide +kernel
lemma power73_r3_6_eq : ∀ k : Fin 16, power73Expr 3 6 k = power73_r3_6 k := by decide +kernel
lemma power73_r3_7_eq : ∀ k : Fin 16, power73Expr 3 7 k = power73_r3_7 k := by decide +kernel
lemma power73_r3_8_eq : ∀ k : Fin 16, power73Expr 3 8 k = power73_r3_8 k := by decide +kernel
lemma power73_r3_9_eq : ∀ k : Fin 16, power73Expr 3 9 k = power73_r3_9 k := by decide +kernel
lemma power73_r3_10_eq : ∀ k : Fin 16, power73Expr 3 10 k = power73_r3_10 k := by decide +kernel
lemma power73_r3_11_eq : ∀ k : Fin 16, power73Expr 3 11 k = power73_r3_11 k := by decide +kernel
lemma power73_r3_12_eq : ∀ k : Fin 16, power73Expr 3 12 k = power73_r3_12 k := by decide +kernel
lemma power73_r3_13_eq : ∀ k : Fin 16, power73Expr 3 13 k = power73_r3_13 k := by decide +kernel
lemma power73_r3_14_eq : ∀ k : Fin 16, power73Expr 3 14 k = power73_r3_14 k := by decide +kernel
lemma power73_r3_15_eq : ∀ k : Fin 16, power73Expr 3 15 k = power73_r3_15 k := by decide +kernel
lemma power73_r3_eq (i k : Fin 16) : power73Expr 3 i k = power73_r3 i k := by
  fin_cases i
  · exact power73_r3_0_eq k
  · exact power73_r3_1_eq k
  · exact power73_r3_2_eq k
  · exact power73_r3_3_eq k
  · exact power73_r3_4_eq k
  · exact power73_r3_5_eq k
  · exact power73_r3_6_eq k
  · exact power73_r3_7_eq k
  · exact power73_r3_8_eq k
  · exact power73_r3_9_eq k
  · exact power73_r3_10_eq k
  · exact power73_r3_11_eq k
  · exact power73_r3_12_eq k
  · exact power73_r3_13_eq k
  · exact power73_r3_14_eq k
  · exact power73_r3_15_eq k
lemma power73_r4_0_eq : ∀ k : Fin 16, power73Expr 4 0 k = power73_r4_0 k := by decide +kernel
lemma power73_r4_1_eq : ∀ k : Fin 16, power73Expr 4 1 k = power73_r4_1 k := by decide +kernel
lemma power73_r4_2_eq : ∀ k : Fin 16, power73Expr 4 2 k = power73_r4_2 k := by decide +kernel
lemma power73_r4_3_eq : ∀ k : Fin 16, power73Expr 4 3 k = power73_r4_3 k := by decide +kernel
lemma power73_r4_4_eq : ∀ k : Fin 16, power73Expr 4 4 k = power73_r4_4 k := by decide +kernel
lemma power73_r4_5_eq : ∀ k : Fin 16, power73Expr 4 5 k = power73_r4_5 k := by decide +kernel
lemma power73_r4_6_eq : ∀ k : Fin 16, power73Expr 4 6 k = power73_r4_6 k := by decide +kernel
lemma power73_r4_7_eq : ∀ k : Fin 16, power73Expr 4 7 k = power73_r4_7 k := by decide +kernel
lemma power73_r4_8_eq : ∀ k : Fin 16, power73Expr 4 8 k = power73_r4_8 k := by decide +kernel
lemma power73_r4_9_eq : ∀ k : Fin 16, power73Expr 4 9 k = power73_r4_9 k := by decide +kernel
lemma power73_r4_10_eq : ∀ k : Fin 16, power73Expr 4 10 k = power73_r4_10 k := by decide +kernel
lemma power73_r4_11_eq : ∀ k : Fin 16, power73Expr 4 11 k = power73_r4_11 k := by decide +kernel
lemma power73_r4_12_eq : ∀ k : Fin 16, power73Expr 4 12 k = power73_r4_12 k := by decide +kernel
lemma power73_r4_13_eq : ∀ k : Fin 16, power73Expr 4 13 k = power73_r4_13 k := by decide +kernel
lemma power73_r4_14_eq : ∀ k : Fin 16, power73Expr 4 14 k = power73_r4_14 k := by decide +kernel
lemma power73_r4_15_eq : ∀ k : Fin 16, power73Expr 4 15 k = power73_r4_15 k := by decide +kernel
lemma power73_r4_eq (i k : Fin 16) : power73Expr 4 i k = power73_r4 i k := by
  fin_cases i
  · exact power73_r4_0_eq k
  · exact power73_r4_1_eq k
  · exact power73_r4_2_eq k
  · exact power73_r4_3_eq k
  · exact power73_r4_4_eq k
  · exact power73_r4_5_eq k
  · exact power73_r4_6_eq k
  · exact power73_r4_7_eq k
  · exact power73_r4_8_eq k
  · exact power73_r4_9_eq k
  · exact power73_r4_10_eq k
  · exact power73_r4_11_eq k
  · exact power73_r4_12_eq k
  · exact power73_r4_13_eq k
  · exact power73_r4_14_eq k
  · exact power73_r4_15_eq k
lemma power73_r5_0_eq : ∀ k : Fin 16, power73Expr 5 0 k = power73_r5_0 k := by decide +kernel
lemma power73_r5_1_eq : ∀ k : Fin 16, power73Expr 5 1 k = power73_r5_1 k := by decide +kernel
lemma power73_r5_2_eq : ∀ k : Fin 16, power73Expr 5 2 k = power73_r5_2 k := by decide +kernel
lemma power73_r5_3_eq : ∀ k : Fin 16, power73Expr 5 3 k = power73_r5_3 k := by decide +kernel
lemma power73_r5_4_eq : ∀ k : Fin 16, power73Expr 5 4 k = power73_r5_4 k := by decide +kernel
lemma power73_r5_5_eq : ∀ k : Fin 16, power73Expr 5 5 k = power73_r5_5 k := by decide +kernel
lemma power73_r5_6_eq : ∀ k : Fin 16, power73Expr 5 6 k = power73_r5_6 k := by decide +kernel
lemma power73_r5_7_eq : ∀ k : Fin 16, power73Expr 5 7 k = power73_r5_7 k := by decide +kernel
lemma power73_r5_8_eq : ∀ k : Fin 16, power73Expr 5 8 k = power73_r5_8 k := by decide +kernel
lemma power73_r5_9_eq : ∀ k : Fin 16, power73Expr 5 9 k = power73_r5_9 k := by decide +kernel
lemma power73_r5_10_eq : ∀ k : Fin 16, power73Expr 5 10 k = power73_r5_10 k := by decide +kernel
lemma power73_r5_11_eq : ∀ k : Fin 16, power73Expr 5 11 k = power73_r5_11 k := by decide +kernel
lemma power73_r5_12_eq : ∀ k : Fin 16, power73Expr 5 12 k = power73_r5_12 k := by decide +kernel
lemma power73_r5_13_eq : ∀ k : Fin 16, power73Expr 5 13 k = power73_r5_13 k := by decide +kernel
lemma power73_r5_14_eq : ∀ k : Fin 16, power73Expr 5 14 k = power73_r5_14 k := by decide +kernel
lemma power73_r5_15_eq : ∀ k : Fin 16, power73Expr 5 15 k = power73_r5_15 k := by decide +kernel
lemma power73_r5_eq (i k : Fin 16) : power73Expr 5 i k = power73_r5 i k := by
  fin_cases i
  · exact power73_r5_0_eq k
  · exact power73_r5_1_eq k
  · exact power73_r5_2_eq k
  · exact power73_r5_3_eq k
  · exact power73_r5_4_eq k
  · exact power73_r5_5_eq k
  · exact power73_r5_6_eq k
  · exact power73_r5_7_eq k
  · exact power73_r5_8_eq k
  · exact power73_r5_9_eq k
  · exact power73_r5_10_eq k
  · exact power73_r5_11_eq k
  · exact power73_r5_12_eq k
  · exact power73_r5_13_eq k
  · exact power73_r5_14_eq k
  · exact power73_r5_15_eq k
lemma power73_eq (j : Fin 6) (i k : Fin 16) : power73Expr j i k = power73 j i k := by
  fin_cases j
  · exact power73_r0_eq i k
  · exact power73_r1_eq i k
  · exact power73_r2_eq i k
  · exact power73_r3_eq i k
  · exact power73_r4_eq i k
  · exact power73_r5_eq i k
lemma power73_contains (j : Fin 6) (i k : Fin 16) :
    (power73 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(73:ℕ))) := by
  rw [← power73_eq]
  unfold power73Expr
  convert exp_direct_step_e (power72_contains_e j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power74_r0_0_eq : ∀ k : Fin 16, power74Expr 0 0 k = power74_r0_0 k := by decide +kernel
lemma power74_r0_1_eq : ∀ k : Fin 16, power74Expr 0 1 k = power74_r0_1 k := by decide +kernel
lemma power74_r0_2_eq : ∀ k : Fin 16, power74Expr 0 2 k = power74_r0_2 k := by decide +kernel
lemma power74_r0_3_eq : ∀ k : Fin 16, power74Expr 0 3 k = power74_r0_3 k := by decide +kernel
lemma power74_r0_4_eq : ∀ k : Fin 16, power74Expr 0 4 k = power74_r0_4 k := by decide +kernel
lemma power74_r0_5_eq : ∀ k : Fin 16, power74Expr 0 5 k = power74_r0_5 k := by decide +kernel
lemma power74_r0_6_eq : ∀ k : Fin 16, power74Expr 0 6 k = power74_r0_6 k := by decide +kernel
lemma power74_r0_7_eq : ∀ k : Fin 16, power74Expr 0 7 k = power74_r0_7 k := by decide +kernel
lemma power74_r0_8_eq : ∀ k : Fin 16, power74Expr 0 8 k = power74_r0_8 k := by decide +kernel
lemma power74_r0_9_eq : ∀ k : Fin 16, power74Expr 0 9 k = power74_r0_9 k := by decide +kernel
lemma power74_r0_10_eq : ∀ k : Fin 16, power74Expr 0 10 k = power74_r0_10 k := by decide +kernel
lemma power74_r0_11_eq : ∀ k : Fin 16, power74Expr 0 11 k = power74_r0_11 k := by decide +kernel
lemma power74_r0_12_eq : ∀ k : Fin 16, power74Expr 0 12 k = power74_r0_12 k := by decide +kernel
lemma power74_r0_13_eq : ∀ k : Fin 16, power74Expr 0 13 k = power74_r0_13 k := by decide +kernel
lemma power74_r0_14_eq : ∀ k : Fin 16, power74Expr 0 14 k = power74_r0_14 k := by decide +kernel
lemma power74_r0_15_eq : ∀ k : Fin 16, power74Expr 0 15 k = power74_r0_15 k := by decide +kernel
lemma power74_r0_eq (i k : Fin 16) : power74Expr 0 i k = power74_r0 i k := by
  fin_cases i
  · exact power74_r0_0_eq k
  · exact power74_r0_1_eq k
  · exact power74_r0_2_eq k
  · exact power74_r0_3_eq k
  · exact power74_r0_4_eq k
  · exact power74_r0_5_eq k
  · exact power74_r0_6_eq k
  · exact power74_r0_7_eq k
  · exact power74_r0_8_eq k
  · exact power74_r0_9_eq k
  · exact power74_r0_10_eq k
  · exact power74_r0_11_eq k
  · exact power74_r0_12_eq k
  · exact power74_r0_13_eq k
  · exact power74_r0_14_eq k
  · exact power74_r0_15_eq k
lemma power74_r1_0_eq : ∀ k : Fin 16, power74Expr 1 0 k = power74_r1_0 k := by decide +kernel
lemma power74_r1_1_eq : ∀ k : Fin 16, power74Expr 1 1 k = power74_r1_1 k := by decide +kernel
lemma power74_r1_2_eq : ∀ k : Fin 16, power74Expr 1 2 k = power74_r1_2 k := by decide +kernel
lemma power74_r1_3_eq : ∀ k : Fin 16, power74Expr 1 3 k = power74_r1_3 k := by decide +kernel
lemma power74_r1_4_eq : ∀ k : Fin 16, power74Expr 1 4 k = power74_r1_4 k := by decide +kernel
lemma power74_r1_5_eq : ∀ k : Fin 16, power74Expr 1 5 k = power74_r1_5 k := by decide +kernel
lemma power74_r1_6_eq : ∀ k : Fin 16, power74Expr 1 6 k = power74_r1_6 k := by decide +kernel
lemma power74_r1_7_eq : ∀ k : Fin 16, power74Expr 1 7 k = power74_r1_7 k := by decide +kernel
lemma power74_r1_8_eq : ∀ k : Fin 16, power74Expr 1 8 k = power74_r1_8 k := by decide +kernel
lemma power74_r1_9_eq : ∀ k : Fin 16, power74Expr 1 9 k = power74_r1_9 k := by decide +kernel
lemma power74_r1_10_eq : ∀ k : Fin 16, power74Expr 1 10 k = power74_r1_10 k := by decide +kernel
lemma power74_r1_11_eq : ∀ k : Fin 16, power74Expr 1 11 k = power74_r1_11 k := by decide +kernel
lemma power74_r1_12_eq : ∀ k : Fin 16, power74Expr 1 12 k = power74_r1_12 k := by decide +kernel
lemma power74_r1_13_eq : ∀ k : Fin 16, power74Expr 1 13 k = power74_r1_13 k := by decide +kernel
lemma power74_r1_14_eq : ∀ k : Fin 16, power74Expr 1 14 k = power74_r1_14 k := by decide +kernel
lemma power74_r1_15_eq : ∀ k : Fin 16, power74Expr 1 15 k = power74_r1_15 k := by decide +kernel
lemma power74_r1_eq (i k : Fin 16) : power74Expr 1 i k = power74_r1 i k := by
  fin_cases i
  · exact power74_r1_0_eq k
  · exact power74_r1_1_eq k
  · exact power74_r1_2_eq k
  · exact power74_r1_3_eq k
  · exact power74_r1_4_eq k
  · exact power74_r1_5_eq k
  · exact power74_r1_6_eq k
  · exact power74_r1_7_eq k
  · exact power74_r1_8_eq k
  · exact power74_r1_9_eq k
  · exact power74_r1_10_eq k
  · exact power74_r1_11_eq k
  · exact power74_r1_12_eq k
  · exact power74_r1_13_eq k
  · exact power74_r1_14_eq k
  · exact power74_r1_15_eq k
lemma power74_r2_0_eq : ∀ k : Fin 16, power74Expr 2 0 k = power74_r2_0 k := by decide +kernel
lemma power74_r2_1_eq : ∀ k : Fin 16, power74Expr 2 1 k = power74_r2_1 k := by decide +kernel
lemma power74_r2_2_eq : ∀ k : Fin 16, power74Expr 2 2 k = power74_r2_2 k := by decide +kernel
lemma power74_r2_3_eq : ∀ k : Fin 16, power74Expr 2 3 k = power74_r2_3 k := by decide +kernel
lemma power74_r2_4_eq : ∀ k : Fin 16, power74Expr 2 4 k = power74_r2_4 k := by decide +kernel
lemma power74_r2_5_eq : ∀ k : Fin 16, power74Expr 2 5 k = power74_r2_5 k := by decide +kernel
lemma power74_r2_6_eq : ∀ k : Fin 16, power74Expr 2 6 k = power74_r2_6 k := by decide +kernel
lemma power74_r2_7_eq : ∀ k : Fin 16, power74Expr 2 7 k = power74_r2_7 k := by decide +kernel
lemma power74_r2_8_eq : ∀ k : Fin 16, power74Expr 2 8 k = power74_r2_8 k := by decide +kernel
lemma power74_r2_9_eq : ∀ k : Fin 16, power74Expr 2 9 k = power74_r2_9 k := by decide +kernel
lemma power74_r2_10_eq : ∀ k : Fin 16, power74Expr 2 10 k = power74_r2_10 k := by decide +kernel
lemma power74_r2_11_eq : ∀ k : Fin 16, power74Expr 2 11 k = power74_r2_11 k := by decide +kernel
lemma power74_r2_12_eq : ∀ k : Fin 16, power74Expr 2 12 k = power74_r2_12 k := by decide +kernel
lemma power74_r2_13_eq : ∀ k : Fin 16, power74Expr 2 13 k = power74_r2_13 k := by decide +kernel
lemma power74_r2_14_eq : ∀ k : Fin 16, power74Expr 2 14 k = power74_r2_14 k := by decide +kernel
lemma power74_r2_15_eq : ∀ k : Fin 16, power74Expr 2 15 k = power74_r2_15 k := by decide +kernel
lemma power74_r2_eq (i k : Fin 16) : power74Expr 2 i k = power74_r2 i k := by
  fin_cases i
  · exact power74_r2_0_eq k
  · exact power74_r2_1_eq k
  · exact power74_r2_2_eq k
  · exact power74_r2_3_eq k
  · exact power74_r2_4_eq k
  · exact power74_r2_5_eq k
  · exact power74_r2_6_eq k
  · exact power74_r2_7_eq k
  · exact power74_r2_8_eq k
  · exact power74_r2_9_eq k
  · exact power74_r2_10_eq k
  · exact power74_r2_11_eq k
  · exact power74_r2_12_eq k
  · exact power74_r2_13_eq k
  · exact power74_r2_14_eq k
  · exact power74_r2_15_eq k
lemma power74_r3_0_eq : ∀ k : Fin 16, power74Expr 3 0 k = power74_r3_0 k := by decide +kernel
lemma power74_r3_1_eq : ∀ k : Fin 16, power74Expr 3 1 k = power74_r3_1 k := by decide +kernel
lemma power74_r3_2_eq : ∀ k : Fin 16, power74Expr 3 2 k = power74_r3_2 k := by decide +kernel
lemma power74_r3_3_eq : ∀ k : Fin 16, power74Expr 3 3 k = power74_r3_3 k := by decide +kernel
lemma power74_r3_4_eq : ∀ k : Fin 16, power74Expr 3 4 k = power74_r3_4 k := by decide +kernel
lemma power74_r3_5_eq : ∀ k : Fin 16, power74Expr 3 5 k = power74_r3_5 k := by decide +kernel
lemma power74_r3_6_eq : ∀ k : Fin 16, power74Expr 3 6 k = power74_r3_6 k := by decide +kernel
lemma power74_r3_7_eq : ∀ k : Fin 16, power74Expr 3 7 k = power74_r3_7 k := by decide +kernel
lemma power74_r3_8_eq : ∀ k : Fin 16, power74Expr 3 8 k = power74_r3_8 k := by decide +kernel
lemma power74_r3_9_eq : ∀ k : Fin 16, power74Expr 3 9 k = power74_r3_9 k := by decide +kernel
lemma power74_r3_10_eq : ∀ k : Fin 16, power74Expr 3 10 k = power74_r3_10 k := by decide +kernel
lemma power74_r3_11_eq : ∀ k : Fin 16, power74Expr 3 11 k = power74_r3_11 k := by decide +kernel
lemma power74_r3_12_eq : ∀ k : Fin 16, power74Expr 3 12 k = power74_r3_12 k := by decide +kernel
lemma power74_r3_13_eq : ∀ k : Fin 16, power74Expr 3 13 k = power74_r3_13 k := by decide +kernel
lemma power74_r3_14_eq : ∀ k : Fin 16, power74Expr 3 14 k = power74_r3_14 k := by decide +kernel
lemma power74_r3_15_eq : ∀ k : Fin 16, power74Expr 3 15 k = power74_r3_15 k := by decide +kernel
lemma power74_r3_eq (i k : Fin 16) : power74Expr 3 i k = power74_r3 i k := by
  fin_cases i
  · exact power74_r3_0_eq k
  · exact power74_r3_1_eq k
  · exact power74_r3_2_eq k
  · exact power74_r3_3_eq k
  · exact power74_r3_4_eq k
  · exact power74_r3_5_eq k
  · exact power74_r3_6_eq k
  · exact power74_r3_7_eq k
  · exact power74_r3_8_eq k
  · exact power74_r3_9_eq k
  · exact power74_r3_10_eq k
  · exact power74_r3_11_eq k
  · exact power74_r3_12_eq k
  · exact power74_r3_13_eq k
  · exact power74_r3_14_eq k
  · exact power74_r3_15_eq k
lemma power74_r4_0_eq : ∀ k : Fin 16, power74Expr 4 0 k = power74_r4_0 k := by decide +kernel
lemma power74_r4_1_eq : ∀ k : Fin 16, power74Expr 4 1 k = power74_r4_1 k := by decide +kernel
lemma power74_r4_2_eq : ∀ k : Fin 16, power74Expr 4 2 k = power74_r4_2 k := by decide +kernel
lemma power74_r4_3_eq : ∀ k : Fin 16, power74Expr 4 3 k = power74_r4_3 k := by decide +kernel
lemma power74_r4_4_eq : ∀ k : Fin 16, power74Expr 4 4 k = power74_r4_4 k := by decide +kernel
lemma power74_r4_5_eq : ∀ k : Fin 16, power74Expr 4 5 k = power74_r4_5 k := by decide +kernel
lemma power74_r4_6_eq : ∀ k : Fin 16, power74Expr 4 6 k = power74_r4_6 k := by decide +kernel
lemma power74_r4_7_eq : ∀ k : Fin 16, power74Expr 4 7 k = power74_r4_7 k := by decide +kernel
lemma power74_r4_8_eq : ∀ k : Fin 16, power74Expr 4 8 k = power74_r4_8 k := by decide +kernel
lemma power74_r4_9_eq : ∀ k : Fin 16, power74Expr 4 9 k = power74_r4_9 k := by decide +kernel
lemma power74_r4_10_eq : ∀ k : Fin 16, power74Expr 4 10 k = power74_r4_10 k := by decide +kernel
lemma power74_r4_11_eq : ∀ k : Fin 16, power74Expr 4 11 k = power74_r4_11 k := by decide +kernel
lemma power74_r4_12_eq : ∀ k : Fin 16, power74Expr 4 12 k = power74_r4_12 k := by decide +kernel
lemma power74_r4_13_eq : ∀ k : Fin 16, power74Expr 4 13 k = power74_r4_13 k := by decide +kernel
lemma power74_r4_14_eq : ∀ k : Fin 16, power74Expr 4 14 k = power74_r4_14 k := by decide +kernel
lemma power74_r4_15_eq : ∀ k : Fin 16, power74Expr 4 15 k = power74_r4_15 k := by decide +kernel
lemma power74_r4_eq (i k : Fin 16) : power74Expr 4 i k = power74_r4 i k := by
  fin_cases i
  · exact power74_r4_0_eq k
  · exact power74_r4_1_eq k
  · exact power74_r4_2_eq k
  · exact power74_r4_3_eq k
  · exact power74_r4_4_eq k
  · exact power74_r4_5_eq k
  · exact power74_r4_6_eq k
  · exact power74_r4_7_eq k
  · exact power74_r4_8_eq k
  · exact power74_r4_9_eq k
  · exact power74_r4_10_eq k
  · exact power74_r4_11_eq k
  · exact power74_r4_12_eq k
  · exact power74_r4_13_eq k
  · exact power74_r4_14_eq k
  · exact power74_r4_15_eq k
lemma power74_r5_0_eq : ∀ k : Fin 16, power74Expr 5 0 k = power74_r5_0 k := by decide +kernel
lemma power74_r5_1_eq : ∀ k : Fin 16, power74Expr 5 1 k = power74_r5_1 k := by decide +kernel
lemma power74_r5_2_eq : ∀ k : Fin 16, power74Expr 5 2 k = power74_r5_2 k := by decide +kernel
lemma power74_r5_3_eq : ∀ k : Fin 16, power74Expr 5 3 k = power74_r5_3 k := by decide +kernel
lemma power74_r5_4_eq : ∀ k : Fin 16, power74Expr 5 4 k = power74_r5_4 k := by decide +kernel
lemma power74_r5_5_eq : ∀ k : Fin 16, power74Expr 5 5 k = power74_r5_5 k := by decide +kernel
lemma power74_r5_6_eq : ∀ k : Fin 16, power74Expr 5 6 k = power74_r5_6 k := by decide +kernel
lemma power74_r5_7_eq : ∀ k : Fin 16, power74Expr 5 7 k = power74_r5_7 k := by decide +kernel
lemma power74_r5_8_eq : ∀ k : Fin 16, power74Expr 5 8 k = power74_r5_8 k := by decide +kernel
lemma power74_r5_9_eq : ∀ k : Fin 16, power74Expr 5 9 k = power74_r5_9 k := by decide +kernel
lemma power74_r5_10_eq : ∀ k : Fin 16, power74Expr 5 10 k = power74_r5_10 k := by decide +kernel
lemma power74_r5_11_eq : ∀ k : Fin 16, power74Expr 5 11 k = power74_r5_11 k := by decide +kernel
lemma power74_r5_12_eq : ∀ k : Fin 16, power74Expr 5 12 k = power74_r5_12 k := by decide +kernel
lemma power74_r5_13_eq : ∀ k : Fin 16, power74Expr 5 13 k = power74_r5_13 k := by decide +kernel
lemma power74_r5_14_eq : ∀ k : Fin 16, power74Expr 5 14 k = power74_r5_14 k := by decide +kernel
lemma power74_r5_15_eq : ∀ k : Fin 16, power74Expr 5 15 k = power74_r5_15 k := by decide +kernel
lemma power74_r5_eq (i k : Fin 16) : power74Expr 5 i k = power74_r5 i k := by
  fin_cases i
  · exact power74_r5_0_eq k
  · exact power74_r5_1_eq k
  · exact power74_r5_2_eq k
  · exact power74_r5_3_eq k
  · exact power74_r5_4_eq k
  · exact power74_r5_5_eq k
  · exact power74_r5_6_eq k
  · exact power74_r5_7_eq k
  · exact power74_r5_8_eq k
  · exact power74_r5_9_eq k
  · exact power74_r5_10_eq k
  · exact power74_r5_11_eq k
  · exact power74_r5_12_eq k
  · exact power74_r5_13_eq k
  · exact power74_r5_14_eq k
  · exact power74_r5_15_eq k
lemma power74_eq (j : Fin 6) (i k : Fin 16) : power74Expr j i k = power74 j i k := by
  fin_cases j
  · exact power74_r0_eq i k
  · exact power74_r1_eq i k
  · exact power74_r2_eq i k
  · exact power74_r3_eq i k
  · exact power74_r4_eq i k
  · exact power74_r5_eq i k
lemma power74_contains (j : Fin 6) (i k : Fin 16) :
    (power74 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(74:ℕ))) := by
  rw [← power74_eq]
  unfold power74Expr
  convert exp_direct_step_e (power73_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power75_r0_0_eq : ∀ k : Fin 16, power75Expr 0 0 k = power75_r0_0 k := by decide +kernel
lemma power75_r0_1_eq : ∀ k : Fin 16, power75Expr 0 1 k = power75_r0_1 k := by decide +kernel
lemma power75_r0_2_eq : ∀ k : Fin 16, power75Expr 0 2 k = power75_r0_2 k := by decide +kernel
lemma power75_r0_3_eq : ∀ k : Fin 16, power75Expr 0 3 k = power75_r0_3 k := by decide +kernel
lemma power75_r0_4_eq : ∀ k : Fin 16, power75Expr 0 4 k = power75_r0_4 k := by decide +kernel
lemma power75_r0_5_eq : ∀ k : Fin 16, power75Expr 0 5 k = power75_r0_5 k := by decide +kernel
lemma power75_r0_6_eq : ∀ k : Fin 16, power75Expr 0 6 k = power75_r0_6 k := by decide +kernel
lemma power75_r0_7_eq : ∀ k : Fin 16, power75Expr 0 7 k = power75_r0_7 k := by decide +kernel
lemma power75_r0_8_eq : ∀ k : Fin 16, power75Expr 0 8 k = power75_r0_8 k := by decide +kernel
lemma power75_r0_9_eq : ∀ k : Fin 16, power75Expr 0 9 k = power75_r0_9 k := by decide +kernel
lemma power75_r0_10_eq : ∀ k : Fin 16, power75Expr 0 10 k = power75_r0_10 k := by decide +kernel
lemma power75_r0_11_eq : ∀ k : Fin 16, power75Expr 0 11 k = power75_r0_11 k := by decide +kernel
lemma power75_r0_12_eq : ∀ k : Fin 16, power75Expr 0 12 k = power75_r0_12 k := by decide +kernel
lemma power75_r0_13_eq : ∀ k : Fin 16, power75Expr 0 13 k = power75_r0_13 k := by decide +kernel
lemma power75_r0_14_eq : ∀ k : Fin 16, power75Expr 0 14 k = power75_r0_14 k := by decide +kernel
lemma power75_r0_15_eq : ∀ k : Fin 16, power75Expr 0 15 k = power75_r0_15 k := by decide +kernel
lemma power75_r0_eq (i k : Fin 16) : power75Expr 0 i k = power75_r0 i k := by
  fin_cases i
  · exact power75_r0_0_eq k
  · exact power75_r0_1_eq k
  · exact power75_r0_2_eq k
  · exact power75_r0_3_eq k
  · exact power75_r0_4_eq k
  · exact power75_r0_5_eq k
  · exact power75_r0_6_eq k
  · exact power75_r0_7_eq k
  · exact power75_r0_8_eq k
  · exact power75_r0_9_eq k
  · exact power75_r0_10_eq k
  · exact power75_r0_11_eq k
  · exact power75_r0_12_eq k
  · exact power75_r0_13_eq k
  · exact power75_r0_14_eq k
  · exact power75_r0_15_eq k
lemma power75_r1_0_eq : ∀ k : Fin 16, power75Expr 1 0 k = power75_r1_0 k := by decide +kernel
lemma power75_r1_1_eq : ∀ k : Fin 16, power75Expr 1 1 k = power75_r1_1 k := by decide +kernel
lemma power75_r1_2_eq : ∀ k : Fin 16, power75Expr 1 2 k = power75_r1_2 k := by decide +kernel
lemma power75_r1_3_eq : ∀ k : Fin 16, power75Expr 1 3 k = power75_r1_3 k := by decide +kernel
lemma power75_r1_4_eq : ∀ k : Fin 16, power75Expr 1 4 k = power75_r1_4 k := by decide +kernel
lemma power75_r1_5_eq : ∀ k : Fin 16, power75Expr 1 5 k = power75_r1_5 k := by decide +kernel
lemma power75_r1_6_eq : ∀ k : Fin 16, power75Expr 1 6 k = power75_r1_6 k := by decide +kernel
lemma power75_r1_7_eq : ∀ k : Fin 16, power75Expr 1 7 k = power75_r1_7 k := by decide +kernel
lemma power75_r1_8_eq : ∀ k : Fin 16, power75Expr 1 8 k = power75_r1_8 k := by decide +kernel
lemma power75_r1_9_eq : ∀ k : Fin 16, power75Expr 1 9 k = power75_r1_9 k := by decide +kernel
lemma power75_r1_10_eq : ∀ k : Fin 16, power75Expr 1 10 k = power75_r1_10 k := by decide +kernel
lemma power75_r1_11_eq : ∀ k : Fin 16, power75Expr 1 11 k = power75_r1_11 k := by decide +kernel
lemma power75_r1_12_eq : ∀ k : Fin 16, power75Expr 1 12 k = power75_r1_12 k := by decide +kernel
lemma power75_r1_13_eq : ∀ k : Fin 16, power75Expr 1 13 k = power75_r1_13 k := by decide +kernel
lemma power75_r1_14_eq : ∀ k : Fin 16, power75Expr 1 14 k = power75_r1_14 k := by decide +kernel
lemma power75_r1_15_eq : ∀ k : Fin 16, power75Expr 1 15 k = power75_r1_15 k := by decide +kernel
lemma power75_r1_eq (i k : Fin 16) : power75Expr 1 i k = power75_r1 i k := by
  fin_cases i
  · exact power75_r1_0_eq k
  · exact power75_r1_1_eq k
  · exact power75_r1_2_eq k
  · exact power75_r1_3_eq k
  · exact power75_r1_4_eq k
  · exact power75_r1_5_eq k
  · exact power75_r1_6_eq k
  · exact power75_r1_7_eq k
  · exact power75_r1_8_eq k
  · exact power75_r1_9_eq k
  · exact power75_r1_10_eq k
  · exact power75_r1_11_eq k
  · exact power75_r1_12_eq k
  · exact power75_r1_13_eq k
  · exact power75_r1_14_eq k
  · exact power75_r1_15_eq k
lemma power75_r2_0_eq : ∀ k : Fin 16, power75Expr 2 0 k = power75_r2_0 k := by decide +kernel
lemma power75_r2_1_eq : ∀ k : Fin 16, power75Expr 2 1 k = power75_r2_1 k := by decide +kernel
lemma power75_r2_2_eq : ∀ k : Fin 16, power75Expr 2 2 k = power75_r2_2 k := by decide +kernel
lemma power75_r2_3_eq : ∀ k : Fin 16, power75Expr 2 3 k = power75_r2_3 k := by decide +kernel
lemma power75_r2_4_eq : ∀ k : Fin 16, power75Expr 2 4 k = power75_r2_4 k := by decide +kernel
lemma power75_r2_5_eq : ∀ k : Fin 16, power75Expr 2 5 k = power75_r2_5 k := by decide +kernel
lemma power75_r2_6_eq : ∀ k : Fin 16, power75Expr 2 6 k = power75_r2_6 k := by decide +kernel
lemma power75_r2_7_eq : ∀ k : Fin 16, power75Expr 2 7 k = power75_r2_7 k := by decide +kernel
lemma power75_r2_8_eq : ∀ k : Fin 16, power75Expr 2 8 k = power75_r2_8 k := by decide +kernel
lemma power75_r2_9_eq : ∀ k : Fin 16, power75Expr 2 9 k = power75_r2_9 k := by decide +kernel
lemma power75_r2_10_eq : ∀ k : Fin 16, power75Expr 2 10 k = power75_r2_10 k := by decide +kernel
lemma power75_r2_11_eq : ∀ k : Fin 16, power75Expr 2 11 k = power75_r2_11 k := by decide +kernel
lemma power75_r2_12_eq : ∀ k : Fin 16, power75Expr 2 12 k = power75_r2_12 k := by decide +kernel
lemma power75_r2_13_eq : ∀ k : Fin 16, power75Expr 2 13 k = power75_r2_13 k := by decide +kernel
lemma power75_r2_14_eq : ∀ k : Fin 16, power75Expr 2 14 k = power75_r2_14 k := by decide +kernel
lemma power75_r2_15_eq : ∀ k : Fin 16, power75Expr 2 15 k = power75_r2_15 k := by decide +kernel
lemma power75_r2_eq (i k : Fin 16) : power75Expr 2 i k = power75_r2 i k := by
  fin_cases i
  · exact power75_r2_0_eq k
  · exact power75_r2_1_eq k
  · exact power75_r2_2_eq k
  · exact power75_r2_3_eq k
  · exact power75_r2_4_eq k
  · exact power75_r2_5_eq k
  · exact power75_r2_6_eq k
  · exact power75_r2_7_eq k
  · exact power75_r2_8_eq k
  · exact power75_r2_9_eq k
  · exact power75_r2_10_eq k
  · exact power75_r2_11_eq k
  · exact power75_r2_12_eq k
  · exact power75_r2_13_eq k
  · exact power75_r2_14_eq k
  · exact power75_r2_15_eq k
lemma power75_r3_0_eq : ∀ k : Fin 16, power75Expr 3 0 k = power75_r3_0 k := by decide +kernel
lemma power75_r3_1_eq : ∀ k : Fin 16, power75Expr 3 1 k = power75_r3_1 k := by decide +kernel
lemma power75_r3_2_eq : ∀ k : Fin 16, power75Expr 3 2 k = power75_r3_2 k := by decide +kernel
lemma power75_r3_3_eq : ∀ k : Fin 16, power75Expr 3 3 k = power75_r3_3 k := by decide +kernel
lemma power75_r3_4_eq : ∀ k : Fin 16, power75Expr 3 4 k = power75_r3_4 k := by decide +kernel
lemma power75_r3_5_eq : ∀ k : Fin 16, power75Expr 3 5 k = power75_r3_5 k := by decide +kernel
lemma power75_r3_6_eq : ∀ k : Fin 16, power75Expr 3 6 k = power75_r3_6 k := by decide +kernel
lemma power75_r3_7_eq : ∀ k : Fin 16, power75Expr 3 7 k = power75_r3_7 k := by decide +kernel
lemma power75_r3_8_eq : ∀ k : Fin 16, power75Expr 3 8 k = power75_r3_8 k := by decide +kernel
lemma power75_r3_9_eq : ∀ k : Fin 16, power75Expr 3 9 k = power75_r3_9 k := by decide +kernel
lemma power75_r3_10_eq : ∀ k : Fin 16, power75Expr 3 10 k = power75_r3_10 k := by decide +kernel
lemma power75_r3_11_eq : ∀ k : Fin 16, power75Expr 3 11 k = power75_r3_11 k := by decide +kernel
lemma power75_r3_12_eq : ∀ k : Fin 16, power75Expr 3 12 k = power75_r3_12 k := by decide +kernel
lemma power75_r3_13_eq : ∀ k : Fin 16, power75Expr 3 13 k = power75_r3_13 k := by decide +kernel
lemma power75_r3_14_eq : ∀ k : Fin 16, power75Expr 3 14 k = power75_r3_14 k := by decide +kernel
lemma power75_r3_15_eq : ∀ k : Fin 16, power75Expr 3 15 k = power75_r3_15 k := by decide +kernel
lemma power75_r3_eq (i k : Fin 16) : power75Expr 3 i k = power75_r3 i k := by
  fin_cases i
  · exact power75_r3_0_eq k
  · exact power75_r3_1_eq k
  · exact power75_r3_2_eq k
  · exact power75_r3_3_eq k
  · exact power75_r3_4_eq k
  · exact power75_r3_5_eq k
  · exact power75_r3_6_eq k
  · exact power75_r3_7_eq k
  · exact power75_r3_8_eq k
  · exact power75_r3_9_eq k
  · exact power75_r3_10_eq k
  · exact power75_r3_11_eq k
  · exact power75_r3_12_eq k
  · exact power75_r3_13_eq k
  · exact power75_r3_14_eq k
  · exact power75_r3_15_eq k
lemma power75_r4_0_eq : ∀ k : Fin 16, power75Expr 4 0 k = power75_r4_0 k := by decide +kernel
lemma power75_r4_1_eq : ∀ k : Fin 16, power75Expr 4 1 k = power75_r4_1 k := by decide +kernel
lemma power75_r4_2_eq : ∀ k : Fin 16, power75Expr 4 2 k = power75_r4_2 k := by decide +kernel
lemma power75_r4_3_eq : ∀ k : Fin 16, power75Expr 4 3 k = power75_r4_3 k := by decide +kernel
lemma power75_r4_4_eq : ∀ k : Fin 16, power75Expr 4 4 k = power75_r4_4 k := by decide +kernel
lemma power75_r4_5_eq : ∀ k : Fin 16, power75Expr 4 5 k = power75_r4_5 k := by decide +kernel
lemma power75_r4_6_eq : ∀ k : Fin 16, power75Expr 4 6 k = power75_r4_6 k := by decide +kernel
lemma power75_r4_7_eq : ∀ k : Fin 16, power75Expr 4 7 k = power75_r4_7 k := by decide +kernel
lemma power75_r4_8_eq : ∀ k : Fin 16, power75Expr 4 8 k = power75_r4_8 k := by decide +kernel
lemma power75_r4_9_eq : ∀ k : Fin 16, power75Expr 4 9 k = power75_r4_9 k := by decide +kernel
lemma power75_r4_10_eq : ∀ k : Fin 16, power75Expr 4 10 k = power75_r4_10 k := by decide +kernel
lemma power75_r4_11_eq : ∀ k : Fin 16, power75Expr 4 11 k = power75_r4_11 k := by decide +kernel
lemma power75_r4_12_eq : ∀ k : Fin 16, power75Expr 4 12 k = power75_r4_12 k := by decide +kernel
lemma power75_r4_13_eq : ∀ k : Fin 16, power75Expr 4 13 k = power75_r4_13 k := by decide +kernel
lemma power75_r4_14_eq : ∀ k : Fin 16, power75Expr 4 14 k = power75_r4_14 k := by decide +kernel
lemma power75_r4_15_eq : ∀ k : Fin 16, power75Expr 4 15 k = power75_r4_15 k := by decide +kernel
lemma power75_r4_eq (i k : Fin 16) : power75Expr 4 i k = power75_r4 i k := by
  fin_cases i
  · exact power75_r4_0_eq k
  · exact power75_r4_1_eq k
  · exact power75_r4_2_eq k
  · exact power75_r4_3_eq k
  · exact power75_r4_4_eq k
  · exact power75_r4_5_eq k
  · exact power75_r4_6_eq k
  · exact power75_r4_7_eq k
  · exact power75_r4_8_eq k
  · exact power75_r4_9_eq k
  · exact power75_r4_10_eq k
  · exact power75_r4_11_eq k
  · exact power75_r4_12_eq k
  · exact power75_r4_13_eq k
  · exact power75_r4_14_eq k
  · exact power75_r4_15_eq k
lemma power75_r5_0_eq : ∀ k : Fin 16, power75Expr 5 0 k = power75_r5_0 k := by decide +kernel
lemma power75_r5_1_eq : ∀ k : Fin 16, power75Expr 5 1 k = power75_r5_1 k := by decide +kernel
lemma power75_r5_2_eq : ∀ k : Fin 16, power75Expr 5 2 k = power75_r5_2 k := by decide +kernel
lemma power75_r5_3_eq : ∀ k : Fin 16, power75Expr 5 3 k = power75_r5_3 k := by decide +kernel
lemma power75_r5_4_eq : ∀ k : Fin 16, power75Expr 5 4 k = power75_r5_4 k := by decide +kernel
lemma power75_r5_5_eq : ∀ k : Fin 16, power75Expr 5 5 k = power75_r5_5 k := by decide +kernel
lemma power75_r5_6_eq : ∀ k : Fin 16, power75Expr 5 6 k = power75_r5_6 k := by decide +kernel
lemma power75_r5_7_eq : ∀ k : Fin 16, power75Expr 5 7 k = power75_r5_7 k := by decide +kernel
lemma power75_r5_8_eq : ∀ k : Fin 16, power75Expr 5 8 k = power75_r5_8 k := by decide +kernel
lemma power75_r5_9_eq : ∀ k : Fin 16, power75Expr 5 9 k = power75_r5_9 k := by decide +kernel
lemma power75_r5_10_eq : ∀ k : Fin 16, power75Expr 5 10 k = power75_r5_10 k := by decide +kernel
lemma power75_r5_11_eq : ∀ k : Fin 16, power75Expr 5 11 k = power75_r5_11 k := by decide +kernel
lemma power75_r5_12_eq : ∀ k : Fin 16, power75Expr 5 12 k = power75_r5_12 k := by decide +kernel
lemma power75_r5_13_eq : ∀ k : Fin 16, power75Expr 5 13 k = power75_r5_13 k := by decide +kernel
lemma power75_r5_14_eq : ∀ k : Fin 16, power75Expr 5 14 k = power75_r5_14 k := by decide +kernel
lemma power75_r5_15_eq : ∀ k : Fin 16, power75Expr 5 15 k = power75_r5_15 k := by decide +kernel
lemma power75_r5_eq (i k : Fin 16) : power75Expr 5 i k = power75_r5 i k := by
  fin_cases i
  · exact power75_r5_0_eq k
  · exact power75_r5_1_eq k
  · exact power75_r5_2_eq k
  · exact power75_r5_3_eq k
  · exact power75_r5_4_eq k
  · exact power75_r5_5_eq k
  · exact power75_r5_6_eq k
  · exact power75_r5_7_eq k
  · exact power75_r5_8_eq k
  · exact power75_r5_9_eq k
  · exact power75_r5_10_eq k
  · exact power75_r5_11_eq k
  · exact power75_r5_12_eq k
  · exact power75_r5_13_eq k
  · exact power75_r5_14_eq k
  · exact power75_r5_15_eq k
lemma power75_eq (j : Fin 6) (i k : Fin 16) : power75Expr j i k = power75 j i k := by
  fin_cases j
  · exact power75_r0_eq i k
  · exact power75_r1_eq i k
  · exact power75_r2_eq i k
  · exact power75_r3_eq i k
  · exact power75_r4_eq i k
  · exact power75_r5_eq i k
lemma power75_contains (j : Fin 6) (i k : Fin 16) :
    (power75 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(75:ℕ))) := by
  rw [← power75_eq]
  unfold power75Expr
  convert exp_direct_step_e (power74_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power76_r0_0_eq : ∀ k : Fin 16, power76Expr 0 0 k = power76_r0_0 k := by decide +kernel
lemma power76_r0_1_eq : ∀ k : Fin 16, power76Expr 0 1 k = power76_r0_1 k := by decide +kernel
lemma power76_r0_2_eq : ∀ k : Fin 16, power76Expr 0 2 k = power76_r0_2 k := by decide +kernel
lemma power76_r0_3_eq : ∀ k : Fin 16, power76Expr 0 3 k = power76_r0_3 k := by decide +kernel
lemma power76_r0_4_eq : ∀ k : Fin 16, power76Expr 0 4 k = power76_r0_4 k := by decide +kernel
lemma power76_r0_5_eq : ∀ k : Fin 16, power76Expr 0 5 k = power76_r0_5 k := by decide +kernel
lemma power76_r0_6_eq : ∀ k : Fin 16, power76Expr 0 6 k = power76_r0_6 k := by decide +kernel
lemma power76_r0_7_eq : ∀ k : Fin 16, power76Expr 0 7 k = power76_r0_7 k := by decide +kernel
lemma power76_r0_8_eq : ∀ k : Fin 16, power76Expr 0 8 k = power76_r0_8 k := by decide +kernel
lemma power76_r0_9_eq : ∀ k : Fin 16, power76Expr 0 9 k = power76_r0_9 k := by decide +kernel
lemma power76_r0_10_eq : ∀ k : Fin 16, power76Expr 0 10 k = power76_r0_10 k := by decide +kernel
lemma power76_r0_11_eq : ∀ k : Fin 16, power76Expr 0 11 k = power76_r0_11 k := by decide +kernel
lemma power76_r0_12_eq : ∀ k : Fin 16, power76Expr 0 12 k = power76_r0_12 k := by decide +kernel
lemma power76_r0_13_eq : ∀ k : Fin 16, power76Expr 0 13 k = power76_r0_13 k := by decide +kernel
lemma power76_r0_14_eq : ∀ k : Fin 16, power76Expr 0 14 k = power76_r0_14 k := by decide +kernel
lemma power76_r0_15_eq : ∀ k : Fin 16, power76Expr 0 15 k = power76_r0_15 k := by decide +kernel
lemma power76_r0_eq (i k : Fin 16) : power76Expr 0 i k = power76_r0 i k := by
  fin_cases i
  · exact power76_r0_0_eq k
  · exact power76_r0_1_eq k
  · exact power76_r0_2_eq k
  · exact power76_r0_3_eq k
  · exact power76_r0_4_eq k
  · exact power76_r0_5_eq k
  · exact power76_r0_6_eq k
  · exact power76_r0_7_eq k
  · exact power76_r0_8_eq k
  · exact power76_r0_9_eq k
  · exact power76_r0_10_eq k
  · exact power76_r0_11_eq k
  · exact power76_r0_12_eq k
  · exact power76_r0_13_eq k
  · exact power76_r0_14_eq k
  · exact power76_r0_15_eq k
lemma power76_r1_0_eq : ∀ k : Fin 16, power76Expr 1 0 k = power76_r1_0 k := by decide +kernel
lemma power76_r1_1_eq : ∀ k : Fin 16, power76Expr 1 1 k = power76_r1_1 k := by decide +kernel
lemma power76_r1_2_eq : ∀ k : Fin 16, power76Expr 1 2 k = power76_r1_2 k := by decide +kernel
lemma power76_r1_3_eq : ∀ k : Fin 16, power76Expr 1 3 k = power76_r1_3 k := by decide +kernel
lemma power76_r1_4_eq : ∀ k : Fin 16, power76Expr 1 4 k = power76_r1_4 k := by decide +kernel
lemma power76_r1_5_eq : ∀ k : Fin 16, power76Expr 1 5 k = power76_r1_5 k := by decide +kernel
lemma power76_r1_6_eq : ∀ k : Fin 16, power76Expr 1 6 k = power76_r1_6 k := by decide +kernel
lemma power76_r1_7_eq : ∀ k : Fin 16, power76Expr 1 7 k = power76_r1_7 k := by decide +kernel
lemma power76_r1_8_eq : ∀ k : Fin 16, power76Expr 1 8 k = power76_r1_8 k := by decide +kernel
lemma power76_r1_9_eq : ∀ k : Fin 16, power76Expr 1 9 k = power76_r1_9 k := by decide +kernel
lemma power76_r1_10_eq : ∀ k : Fin 16, power76Expr 1 10 k = power76_r1_10 k := by decide +kernel
lemma power76_r1_11_eq : ∀ k : Fin 16, power76Expr 1 11 k = power76_r1_11 k := by decide +kernel
lemma power76_r1_12_eq : ∀ k : Fin 16, power76Expr 1 12 k = power76_r1_12 k := by decide +kernel
lemma power76_r1_13_eq : ∀ k : Fin 16, power76Expr 1 13 k = power76_r1_13 k := by decide +kernel
lemma power76_r1_14_eq : ∀ k : Fin 16, power76Expr 1 14 k = power76_r1_14 k := by decide +kernel
lemma power76_r1_15_eq : ∀ k : Fin 16, power76Expr 1 15 k = power76_r1_15 k := by decide +kernel
lemma power76_r1_eq (i k : Fin 16) : power76Expr 1 i k = power76_r1 i k := by
  fin_cases i
  · exact power76_r1_0_eq k
  · exact power76_r1_1_eq k
  · exact power76_r1_2_eq k
  · exact power76_r1_3_eq k
  · exact power76_r1_4_eq k
  · exact power76_r1_5_eq k
  · exact power76_r1_6_eq k
  · exact power76_r1_7_eq k
  · exact power76_r1_8_eq k
  · exact power76_r1_9_eq k
  · exact power76_r1_10_eq k
  · exact power76_r1_11_eq k
  · exact power76_r1_12_eq k
  · exact power76_r1_13_eq k
  · exact power76_r1_14_eq k
  · exact power76_r1_15_eq k
lemma power76_r2_0_eq : ∀ k : Fin 16, power76Expr 2 0 k = power76_r2_0 k := by decide +kernel
lemma power76_r2_1_eq : ∀ k : Fin 16, power76Expr 2 1 k = power76_r2_1 k := by decide +kernel
lemma power76_r2_2_eq : ∀ k : Fin 16, power76Expr 2 2 k = power76_r2_2 k := by decide +kernel
lemma power76_r2_3_eq : ∀ k : Fin 16, power76Expr 2 3 k = power76_r2_3 k := by decide +kernel
lemma power76_r2_4_eq : ∀ k : Fin 16, power76Expr 2 4 k = power76_r2_4 k := by decide +kernel
lemma power76_r2_5_eq : ∀ k : Fin 16, power76Expr 2 5 k = power76_r2_5 k := by decide +kernel
lemma power76_r2_6_eq : ∀ k : Fin 16, power76Expr 2 6 k = power76_r2_6 k := by decide +kernel
lemma power76_r2_7_eq : ∀ k : Fin 16, power76Expr 2 7 k = power76_r2_7 k := by decide +kernel
lemma power76_r2_8_eq : ∀ k : Fin 16, power76Expr 2 8 k = power76_r2_8 k := by decide +kernel
lemma power76_r2_9_eq : ∀ k : Fin 16, power76Expr 2 9 k = power76_r2_9 k := by decide +kernel
lemma power76_r2_10_eq : ∀ k : Fin 16, power76Expr 2 10 k = power76_r2_10 k := by decide +kernel
lemma power76_r2_11_eq : ∀ k : Fin 16, power76Expr 2 11 k = power76_r2_11 k := by decide +kernel
lemma power76_r2_12_eq : ∀ k : Fin 16, power76Expr 2 12 k = power76_r2_12 k := by decide +kernel
lemma power76_r2_13_eq : ∀ k : Fin 16, power76Expr 2 13 k = power76_r2_13 k := by decide +kernel
lemma power76_r2_14_eq : ∀ k : Fin 16, power76Expr 2 14 k = power76_r2_14 k := by decide +kernel
lemma power76_r2_15_eq : ∀ k : Fin 16, power76Expr 2 15 k = power76_r2_15 k := by decide +kernel
lemma power76_r2_eq (i k : Fin 16) : power76Expr 2 i k = power76_r2 i k := by
  fin_cases i
  · exact power76_r2_0_eq k
  · exact power76_r2_1_eq k
  · exact power76_r2_2_eq k
  · exact power76_r2_3_eq k
  · exact power76_r2_4_eq k
  · exact power76_r2_5_eq k
  · exact power76_r2_6_eq k
  · exact power76_r2_7_eq k
  · exact power76_r2_8_eq k
  · exact power76_r2_9_eq k
  · exact power76_r2_10_eq k
  · exact power76_r2_11_eq k
  · exact power76_r2_12_eq k
  · exact power76_r2_13_eq k
  · exact power76_r2_14_eq k
  · exact power76_r2_15_eq k
lemma power76_r3_0_eq : ∀ k : Fin 16, power76Expr 3 0 k = power76_r3_0 k := by decide +kernel
lemma power76_r3_1_eq : ∀ k : Fin 16, power76Expr 3 1 k = power76_r3_1 k := by decide +kernel
lemma power76_r3_2_eq : ∀ k : Fin 16, power76Expr 3 2 k = power76_r3_2 k := by decide +kernel
lemma power76_r3_3_eq : ∀ k : Fin 16, power76Expr 3 3 k = power76_r3_3 k := by decide +kernel
lemma power76_r3_4_eq : ∀ k : Fin 16, power76Expr 3 4 k = power76_r3_4 k := by decide +kernel
lemma power76_r3_5_eq : ∀ k : Fin 16, power76Expr 3 5 k = power76_r3_5 k := by decide +kernel
lemma power76_r3_6_eq : ∀ k : Fin 16, power76Expr 3 6 k = power76_r3_6 k := by decide +kernel
lemma power76_r3_7_eq : ∀ k : Fin 16, power76Expr 3 7 k = power76_r3_7 k := by decide +kernel
lemma power76_r3_8_eq : ∀ k : Fin 16, power76Expr 3 8 k = power76_r3_8 k := by decide +kernel
lemma power76_r3_9_eq : ∀ k : Fin 16, power76Expr 3 9 k = power76_r3_9 k := by decide +kernel
lemma power76_r3_10_eq : ∀ k : Fin 16, power76Expr 3 10 k = power76_r3_10 k := by decide +kernel
lemma power76_r3_11_eq : ∀ k : Fin 16, power76Expr 3 11 k = power76_r3_11 k := by decide +kernel
lemma power76_r3_12_eq : ∀ k : Fin 16, power76Expr 3 12 k = power76_r3_12 k := by decide +kernel
lemma power76_r3_13_eq : ∀ k : Fin 16, power76Expr 3 13 k = power76_r3_13 k := by decide +kernel
lemma power76_r3_14_eq : ∀ k : Fin 16, power76Expr 3 14 k = power76_r3_14 k := by decide +kernel
lemma power76_r3_15_eq : ∀ k : Fin 16, power76Expr 3 15 k = power76_r3_15 k := by decide +kernel
lemma power76_r3_eq (i k : Fin 16) : power76Expr 3 i k = power76_r3 i k := by
  fin_cases i
  · exact power76_r3_0_eq k
  · exact power76_r3_1_eq k
  · exact power76_r3_2_eq k
  · exact power76_r3_3_eq k
  · exact power76_r3_4_eq k
  · exact power76_r3_5_eq k
  · exact power76_r3_6_eq k
  · exact power76_r3_7_eq k
  · exact power76_r3_8_eq k
  · exact power76_r3_9_eq k
  · exact power76_r3_10_eq k
  · exact power76_r3_11_eq k
  · exact power76_r3_12_eq k
  · exact power76_r3_13_eq k
  · exact power76_r3_14_eq k
  · exact power76_r3_15_eq k
lemma power76_r4_0_eq : ∀ k : Fin 16, power76Expr 4 0 k = power76_r4_0 k := by decide +kernel
lemma power76_r4_1_eq : ∀ k : Fin 16, power76Expr 4 1 k = power76_r4_1 k := by decide +kernel
lemma power76_r4_2_eq : ∀ k : Fin 16, power76Expr 4 2 k = power76_r4_2 k := by decide +kernel
lemma power76_r4_3_eq : ∀ k : Fin 16, power76Expr 4 3 k = power76_r4_3 k := by decide +kernel
lemma power76_r4_4_eq : ∀ k : Fin 16, power76Expr 4 4 k = power76_r4_4 k := by decide +kernel
lemma power76_r4_5_eq : ∀ k : Fin 16, power76Expr 4 5 k = power76_r4_5 k := by decide +kernel
lemma power76_r4_6_eq : ∀ k : Fin 16, power76Expr 4 6 k = power76_r4_6 k := by decide +kernel
lemma power76_r4_7_eq : ∀ k : Fin 16, power76Expr 4 7 k = power76_r4_7 k := by decide +kernel
lemma power76_r4_8_eq : ∀ k : Fin 16, power76Expr 4 8 k = power76_r4_8 k := by decide +kernel
lemma power76_r4_9_eq : ∀ k : Fin 16, power76Expr 4 9 k = power76_r4_9 k := by decide +kernel
lemma power76_r4_10_eq : ∀ k : Fin 16, power76Expr 4 10 k = power76_r4_10 k := by decide +kernel
lemma power76_r4_11_eq : ∀ k : Fin 16, power76Expr 4 11 k = power76_r4_11 k := by decide +kernel
lemma power76_r4_12_eq : ∀ k : Fin 16, power76Expr 4 12 k = power76_r4_12 k := by decide +kernel
lemma power76_r4_13_eq : ∀ k : Fin 16, power76Expr 4 13 k = power76_r4_13 k := by decide +kernel
lemma power76_r4_14_eq : ∀ k : Fin 16, power76Expr 4 14 k = power76_r4_14 k := by decide +kernel
lemma power76_r4_15_eq : ∀ k : Fin 16, power76Expr 4 15 k = power76_r4_15 k := by decide +kernel
lemma power76_r4_eq (i k : Fin 16) : power76Expr 4 i k = power76_r4 i k := by
  fin_cases i
  · exact power76_r4_0_eq k
  · exact power76_r4_1_eq k
  · exact power76_r4_2_eq k
  · exact power76_r4_3_eq k
  · exact power76_r4_4_eq k
  · exact power76_r4_5_eq k
  · exact power76_r4_6_eq k
  · exact power76_r4_7_eq k
  · exact power76_r4_8_eq k
  · exact power76_r4_9_eq k
  · exact power76_r4_10_eq k
  · exact power76_r4_11_eq k
  · exact power76_r4_12_eq k
  · exact power76_r4_13_eq k
  · exact power76_r4_14_eq k
  · exact power76_r4_15_eq k
lemma power76_r5_0_eq : ∀ k : Fin 16, power76Expr 5 0 k = power76_r5_0 k := by decide +kernel
lemma power76_r5_1_eq : ∀ k : Fin 16, power76Expr 5 1 k = power76_r5_1 k := by decide +kernel
lemma power76_r5_2_eq : ∀ k : Fin 16, power76Expr 5 2 k = power76_r5_2 k := by decide +kernel
lemma power76_r5_3_eq : ∀ k : Fin 16, power76Expr 5 3 k = power76_r5_3 k := by decide +kernel
lemma power76_r5_4_eq : ∀ k : Fin 16, power76Expr 5 4 k = power76_r5_4 k := by decide +kernel
lemma power76_r5_5_eq : ∀ k : Fin 16, power76Expr 5 5 k = power76_r5_5 k := by decide +kernel
lemma power76_r5_6_eq : ∀ k : Fin 16, power76Expr 5 6 k = power76_r5_6 k := by decide +kernel
lemma power76_r5_7_eq : ∀ k : Fin 16, power76Expr 5 7 k = power76_r5_7 k := by decide +kernel
lemma power76_r5_8_eq : ∀ k : Fin 16, power76Expr 5 8 k = power76_r5_8 k := by decide +kernel
lemma power76_r5_9_eq : ∀ k : Fin 16, power76Expr 5 9 k = power76_r5_9 k := by decide +kernel
lemma power76_r5_10_eq : ∀ k : Fin 16, power76Expr 5 10 k = power76_r5_10 k := by decide +kernel
lemma power76_r5_11_eq : ∀ k : Fin 16, power76Expr 5 11 k = power76_r5_11 k := by decide +kernel
lemma power76_r5_12_eq : ∀ k : Fin 16, power76Expr 5 12 k = power76_r5_12 k := by decide +kernel
lemma power76_r5_13_eq : ∀ k : Fin 16, power76Expr 5 13 k = power76_r5_13 k := by decide +kernel
lemma power76_r5_14_eq : ∀ k : Fin 16, power76Expr 5 14 k = power76_r5_14 k := by decide +kernel
lemma power76_r5_15_eq : ∀ k : Fin 16, power76Expr 5 15 k = power76_r5_15 k := by decide +kernel
lemma power76_r5_eq (i k : Fin 16) : power76Expr 5 i k = power76_r5 i k := by
  fin_cases i
  · exact power76_r5_0_eq k
  · exact power76_r5_1_eq k
  · exact power76_r5_2_eq k
  · exact power76_r5_3_eq k
  · exact power76_r5_4_eq k
  · exact power76_r5_5_eq k
  · exact power76_r5_6_eq k
  · exact power76_r5_7_eq k
  · exact power76_r5_8_eq k
  · exact power76_r5_9_eq k
  · exact power76_r5_10_eq k
  · exact power76_r5_11_eq k
  · exact power76_r5_12_eq k
  · exact power76_r5_13_eq k
  · exact power76_r5_14_eq k
  · exact power76_r5_15_eq k
lemma power76_eq (j : Fin 6) (i k : Fin 16) : power76Expr j i k = power76 j i k := by
  fin_cases j
  · exact power76_r0_eq i k
  · exact power76_r1_eq i k
  · exact power76_r2_eq i k
  · exact power76_r3_eq i k
  · exact power76_r4_eq i k
  · exact power76_r5_eq i k
lemma power76_contains (j : Fin 6) (i k : Fin 16) :
    (power76 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(76:ℕ))) := by
  rw [← power76_eq]
  unfold power76Expr
  convert exp_direct_step_e (power75_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns80
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
lemma column76_0_r0_0_eq : ∀ k : Fin 16, column76_0Expr 0 0 k = column76_0_r0_0 k := by decide +kernel
lemma column76_0_r0_1_eq : ∀ k : Fin 16, column76_0Expr 0 1 k = column76_0_r0_1 k := by decide +kernel
lemma column76_0_r0_2_eq : ∀ k : Fin 16, column76_0Expr 0 2 k = column76_0_r0_2 k := by decide +kernel
lemma column76_0_r0_3_eq : ∀ k : Fin 16, column76_0Expr 0 3 k = column76_0_r0_3 k := by decide +kernel
lemma column76_0_r0_4_eq : ∀ k : Fin 16, column76_0Expr 0 4 k = column76_0_r0_4 k := by decide +kernel
lemma column76_0_r0_5_eq : ∀ k : Fin 16, column76_0Expr 0 5 k = column76_0_r0_5 k := by decide +kernel
lemma column76_0_r0_6_eq : ∀ k : Fin 16, column76_0Expr 0 6 k = column76_0_r0_6 k := by decide +kernel
lemma column76_0_r0_7_eq : ∀ k : Fin 16, column76_0Expr 0 7 k = column76_0_r0_7 k := by decide +kernel
lemma column76_0_r0_8_eq : ∀ k : Fin 16, column76_0Expr 0 8 k = column76_0_r0_8 k := by decide +kernel
lemma column76_0_r0_9_eq : ∀ k : Fin 16, column76_0Expr 0 9 k = column76_0_r0_9 k := by decide +kernel
lemma column76_0_r0_10_eq : ∀ k : Fin 16, column76_0Expr 0 10 k = column76_0_r0_10 k := by decide +kernel
lemma column76_0_r0_11_eq : ∀ k : Fin 16, column76_0Expr 0 11 k = column76_0_r0_11 k := by decide +kernel
lemma column76_0_r0_12_eq : ∀ k : Fin 16, column76_0Expr 0 12 k = column76_0_r0_12 k := by decide +kernel
lemma column76_0_r0_13_eq : ∀ k : Fin 16, column76_0Expr 0 13 k = column76_0_r0_13 k := by decide +kernel
lemma column76_0_r0_14_eq : ∀ k : Fin 16, column76_0Expr 0 14 k = column76_0_r0_14 k := by decide +kernel
lemma column76_0_r0_15_eq : ∀ k : Fin 16, column76_0Expr 0 15 k = column76_0_r0_15 k := by decide +kernel
lemma column76_0_r0_eq (i k : Fin 16) : column76_0Expr 0 i k = column76_0_r0 i k := by
  fin_cases i
  · exact column76_0_r0_0_eq k
  · exact column76_0_r0_1_eq k
  · exact column76_0_r0_2_eq k
  · exact column76_0_r0_3_eq k
  · exact column76_0_r0_4_eq k
  · exact column76_0_r0_5_eq k
  · exact column76_0_r0_6_eq k
  · exact column76_0_r0_7_eq k
  · exact column76_0_r0_8_eq k
  · exact column76_0_r0_9_eq k
  · exact column76_0_r0_10_eq k
  · exact column76_0_r0_11_eq k
  · exact column76_0_r0_12_eq k
  · exact column76_0_r0_13_eq k
  · exact column76_0_r0_14_eq k
  · exact column76_0_r0_15_eq k
lemma column76_0_r1_0_eq : ∀ k : Fin 16, column76_0Expr 1 0 k = column76_0_r1_0 k := by decide +kernel
lemma column76_0_r1_1_eq : ∀ k : Fin 16, column76_0Expr 1 1 k = column76_0_r1_1 k := by decide +kernel
lemma column76_0_r1_2_eq : ∀ k : Fin 16, column76_0Expr 1 2 k = column76_0_r1_2 k := by decide +kernel
lemma column76_0_r1_3_eq : ∀ k : Fin 16, column76_0Expr 1 3 k = column76_0_r1_3 k := by decide +kernel
lemma column76_0_r1_4_eq : ∀ k : Fin 16, column76_0Expr 1 4 k = column76_0_r1_4 k := by decide +kernel
lemma column76_0_r1_5_eq : ∀ k : Fin 16, column76_0Expr 1 5 k = column76_0_r1_5 k := by decide +kernel
lemma column76_0_r1_6_eq : ∀ k : Fin 16, column76_0Expr 1 6 k = column76_0_r1_6 k := by decide +kernel
lemma column76_0_r1_7_eq : ∀ k : Fin 16, column76_0Expr 1 7 k = column76_0_r1_7 k := by decide +kernel
lemma column76_0_r1_8_eq : ∀ k : Fin 16, column76_0Expr 1 8 k = column76_0_r1_8 k := by decide +kernel
lemma column76_0_r1_9_eq : ∀ k : Fin 16, column76_0Expr 1 9 k = column76_0_r1_9 k := by decide +kernel
lemma column76_0_r1_10_eq : ∀ k : Fin 16, column76_0Expr 1 10 k = column76_0_r1_10 k := by decide +kernel
lemma column76_0_r1_11_eq : ∀ k : Fin 16, column76_0Expr 1 11 k = column76_0_r1_11 k := by decide +kernel
lemma column76_0_r1_12_eq : ∀ k : Fin 16, column76_0Expr 1 12 k = column76_0_r1_12 k := by decide +kernel
lemma column76_0_r1_13_eq : ∀ k : Fin 16, column76_0Expr 1 13 k = column76_0_r1_13 k := by decide +kernel
lemma column76_0_r1_14_eq : ∀ k : Fin 16, column76_0Expr 1 14 k = column76_0_r1_14 k := by decide +kernel
lemma column76_0_r1_15_eq : ∀ k : Fin 16, column76_0Expr 1 15 k = column76_0_r1_15 k := by decide +kernel
lemma column76_0_r1_eq (i k : Fin 16) : column76_0Expr 1 i k = column76_0_r1 i k := by
  fin_cases i
  · exact column76_0_r1_0_eq k
  · exact column76_0_r1_1_eq k
  · exact column76_0_r1_2_eq k
  · exact column76_0_r1_3_eq k
  · exact column76_0_r1_4_eq k
  · exact column76_0_r1_5_eq k
  · exact column76_0_r1_6_eq k
  · exact column76_0_r1_7_eq k
  · exact column76_0_r1_8_eq k
  · exact column76_0_r1_9_eq k
  · exact column76_0_r1_10_eq k
  · exact column76_0_r1_11_eq k
  · exact column76_0_r1_12_eq k
  · exact column76_0_r1_13_eq k
  · exact column76_0_r1_14_eq k
  · exact column76_0_r1_15_eq k
lemma column76_0_r2_0_eq : ∀ k : Fin 16, column76_0Expr 2 0 k = column76_0_r2_0 k := by decide +kernel
lemma column76_0_r2_1_eq : ∀ k : Fin 16, column76_0Expr 2 1 k = column76_0_r2_1 k := by decide +kernel
lemma column76_0_r2_2_eq : ∀ k : Fin 16, column76_0Expr 2 2 k = column76_0_r2_2 k := by decide +kernel
lemma column76_0_r2_3_eq : ∀ k : Fin 16, column76_0Expr 2 3 k = column76_0_r2_3 k := by decide +kernel
lemma column76_0_r2_4_eq : ∀ k : Fin 16, column76_0Expr 2 4 k = column76_0_r2_4 k := by decide +kernel
lemma column76_0_r2_5_eq : ∀ k : Fin 16, column76_0Expr 2 5 k = column76_0_r2_5 k := by decide +kernel
lemma column76_0_r2_6_eq : ∀ k : Fin 16, column76_0Expr 2 6 k = column76_0_r2_6 k := by decide +kernel
lemma column76_0_r2_7_eq : ∀ k : Fin 16, column76_0Expr 2 7 k = column76_0_r2_7 k := by decide +kernel
lemma column76_0_r2_8_eq : ∀ k : Fin 16, column76_0Expr 2 8 k = column76_0_r2_8 k := by decide +kernel
lemma column76_0_r2_9_eq : ∀ k : Fin 16, column76_0Expr 2 9 k = column76_0_r2_9 k := by decide +kernel
lemma column76_0_r2_10_eq : ∀ k : Fin 16, column76_0Expr 2 10 k = column76_0_r2_10 k := by decide +kernel
lemma column76_0_r2_11_eq : ∀ k : Fin 16, column76_0Expr 2 11 k = column76_0_r2_11 k := by decide +kernel
lemma column76_0_r2_12_eq : ∀ k : Fin 16, column76_0Expr 2 12 k = column76_0_r2_12 k := by decide +kernel
lemma column76_0_r2_13_eq : ∀ k : Fin 16, column76_0Expr 2 13 k = column76_0_r2_13 k := by decide +kernel
lemma column76_0_r2_14_eq : ∀ k : Fin 16, column76_0Expr 2 14 k = column76_0_r2_14 k := by decide +kernel
lemma column76_0_r2_15_eq : ∀ k : Fin 16, column76_0Expr 2 15 k = column76_0_r2_15 k := by decide +kernel
lemma column76_0_r2_eq (i k : Fin 16) : column76_0Expr 2 i k = column76_0_r2 i k := by
  fin_cases i
  · exact column76_0_r2_0_eq k
  · exact column76_0_r2_1_eq k
  · exact column76_0_r2_2_eq k
  · exact column76_0_r2_3_eq k
  · exact column76_0_r2_4_eq k
  · exact column76_0_r2_5_eq k
  · exact column76_0_r2_6_eq k
  · exact column76_0_r2_7_eq k
  · exact column76_0_r2_8_eq k
  · exact column76_0_r2_9_eq k
  · exact column76_0_r2_10_eq k
  · exact column76_0_r2_11_eq k
  · exact column76_0_r2_12_eq k
  · exact column76_0_r2_13_eq k
  · exact column76_0_r2_14_eq k
  · exact column76_0_r2_15_eq k
lemma column76_0_r3_0_eq : ∀ k : Fin 16, column76_0Expr 3 0 k = column76_0_r3_0 k := by decide +kernel
lemma column76_0_r3_1_eq : ∀ k : Fin 16, column76_0Expr 3 1 k = column76_0_r3_1 k := by decide +kernel
lemma column76_0_r3_2_eq : ∀ k : Fin 16, column76_0Expr 3 2 k = column76_0_r3_2 k := by decide +kernel
lemma column76_0_r3_3_eq : ∀ k : Fin 16, column76_0Expr 3 3 k = column76_0_r3_3 k := by decide +kernel
lemma column76_0_r3_4_eq : ∀ k : Fin 16, column76_0Expr 3 4 k = column76_0_r3_4 k := by decide +kernel
lemma column76_0_r3_5_eq : ∀ k : Fin 16, column76_0Expr 3 5 k = column76_0_r3_5 k := by decide +kernel
lemma column76_0_r3_6_eq : ∀ k : Fin 16, column76_0Expr 3 6 k = column76_0_r3_6 k := by decide +kernel
lemma column76_0_r3_7_eq : ∀ k : Fin 16, column76_0Expr 3 7 k = column76_0_r3_7 k := by decide +kernel
lemma column76_0_r3_8_eq : ∀ k : Fin 16, column76_0Expr 3 8 k = column76_0_r3_8 k := by decide +kernel
lemma column76_0_r3_9_eq : ∀ k : Fin 16, column76_0Expr 3 9 k = column76_0_r3_9 k := by decide +kernel
lemma column76_0_r3_10_eq : ∀ k : Fin 16, column76_0Expr 3 10 k = column76_0_r3_10 k := by decide +kernel
lemma column76_0_r3_11_eq : ∀ k : Fin 16, column76_0Expr 3 11 k = column76_0_r3_11 k := by decide +kernel
lemma column76_0_r3_12_eq : ∀ k : Fin 16, column76_0Expr 3 12 k = column76_0_r3_12 k := by decide +kernel
lemma column76_0_r3_13_eq : ∀ k : Fin 16, column76_0Expr 3 13 k = column76_0_r3_13 k := by decide +kernel
lemma column76_0_r3_14_eq : ∀ k : Fin 16, column76_0Expr 3 14 k = column76_0_r3_14 k := by decide +kernel
lemma column76_0_r3_15_eq : ∀ k : Fin 16, column76_0Expr 3 15 k = column76_0_r3_15 k := by decide +kernel
lemma column76_0_r3_eq (i k : Fin 16) : column76_0Expr 3 i k = column76_0_r3 i k := by
  fin_cases i
  · exact column76_0_r3_0_eq k
  · exact column76_0_r3_1_eq k
  · exact column76_0_r3_2_eq k
  · exact column76_0_r3_3_eq k
  · exact column76_0_r3_4_eq k
  · exact column76_0_r3_5_eq k
  · exact column76_0_r3_6_eq k
  · exact column76_0_r3_7_eq k
  · exact column76_0_r3_8_eq k
  · exact column76_0_r3_9_eq k
  · exact column76_0_r3_10_eq k
  · exact column76_0_r3_11_eq k
  · exact column76_0_r3_12_eq k
  · exact column76_0_r3_13_eq k
  · exact column76_0_r3_14_eq k
  · exact column76_0_r3_15_eq k
lemma column76_0_r4_0_eq : ∀ k : Fin 16, column76_0Expr 4 0 k = column76_0_r4_0 k := by decide +kernel
lemma column76_0_r4_1_eq : ∀ k : Fin 16, column76_0Expr 4 1 k = column76_0_r4_1 k := by decide +kernel
lemma column76_0_r4_2_eq : ∀ k : Fin 16, column76_0Expr 4 2 k = column76_0_r4_2 k := by decide +kernel
lemma column76_0_r4_3_eq : ∀ k : Fin 16, column76_0Expr 4 3 k = column76_0_r4_3 k := by decide +kernel
lemma column76_0_r4_4_eq : ∀ k : Fin 16, column76_0Expr 4 4 k = column76_0_r4_4 k := by decide +kernel
lemma column76_0_r4_5_eq : ∀ k : Fin 16, column76_0Expr 4 5 k = column76_0_r4_5 k := by decide +kernel
lemma column76_0_r4_6_eq : ∀ k : Fin 16, column76_0Expr 4 6 k = column76_0_r4_6 k := by decide +kernel
lemma column76_0_r4_7_eq : ∀ k : Fin 16, column76_0Expr 4 7 k = column76_0_r4_7 k := by decide +kernel
lemma column76_0_r4_8_eq : ∀ k : Fin 16, column76_0Expr 4 8 k = column76_0_r4_8 k := by decide +kernel
lemma column76_0_r4_9_eq : ∀ k : Fin 16, column76_0Expr 4 9 k = column76_0_r4_9 k := by decide +kernel
lemma column76_0_r4_10_eq : ∀ k : Fin 16, column76_0Expr 4 10 k = column76_0_r4_10 k := by decide +kernel
lemma column76_0_r4_11_eq : ∀ k : Fin 16, column76_0Expr 4 11 k = column76_0_r4_11 k := by decide +kernel
lemma column76_0_r4_12_eq : ∀ k : Fin 16, column76_0Expr 4 12 k = column76_0_r4_12 k := by decide +kernel
lemma column76_0_r4_13_eq : ∀ k : Fin 16, column76_0Expr 4 13 k = column76_0_r4_13 k := by decide +kernel
lemma column76_0_r4_14_eq : ∀ k : Fin 16, column76_0Expr 4 14 k = column76_0_r4_14 k := by decide +kernel
lemma column76_0_r4_15_eq : ∀ k : Fin 16, column76_0Expr 4 15 k = column76_0_r4_15 k := by decide +kernel
lemma column76_0_r4_eq (i k : Fin 16) : column76_0Expr 4 i k = column76_0_r4 i k := by
  fin_cases i
  · exact column76_0_r4_0_eq k
  · exact column76_0_r4_1_eq k
  · exact column76_0_r4_2_eq k
  · exact column76_0_r4_3_eq k
  · exact column76_0_r4_4_eq k
  · exact column76_0_r4_5_eq k
  · exact column76_0_r4_6_eq k
  · exact column76_0_r4_7_eq k
  · exact column76_0_r4_8_eq k
  · exact column76_0_r4_9_eq k
  · exact column76_0_r4_10_eq k
  · exact column76_0_r4_11_eq k
  · exact column76_0_r4_12_eq k
  · exact column76_0_r4_13_eq k
  · exact column76_0_r4_14_eq k
  · exact column76_0_r4_15_eq k
lemma column76_0_r5_0_eq : ∀ k : Fin 16, column76_0Expr 5 0 k = column76_0_r5_0 k := by decide +kernel
lemma column76_0_r5_1_eq : ∀ k : Fin 16, column76_0Expr 5 1 k = column76_0_r5_1 k := by decide +kernel
lemma column76_0_r5_2_eq : ∀ k : Fin 16, column76_0Expr 5 2 k = column76_0_r5_2 k := by decide +kernel
lemma column76_0_r5_3_eq : ∀ k : Fin 16, column76_0Expr 5 3 k = column76_0_r5_3 k := by decide +kernel
lemma column76_0_r5_4_eq : ∀ k : Fin 16, column76_0Expr 5 4 k = column76_0_r5_4 k := by decide +kernel
lemma column76_0_r5_5_eq : ∀ k : Fin 16, column76_0Expr 5 5 k = column76_0_r5_5 k := by decide +kernel
lemma column76_0_r5_6_eq : ∀ k : Fin 16, column76_0Expr 5 6 k = column76_0_r5_6 k := by decide +kernel
lemma column76_0_r5_7_eq : ∀ k : Fin 16, column76_0Expr 5 7 k = column76_0_r5_7 k := by decide +kernel
lemma column76_0_r5_8_eq : ∀ k : Fin 16, column76_0Expr 5 8 k = column76_0_r5_8 k := by decide +kernel
lemma column76_0_r5_9_eq : ∀ k : Fin 16, column76_0Expr 5 9 k = column76_0_r5_9 k := by decide +kernel
lemma column76_0_r5_10_eq : ∀ k : Fin 16, column76_0Expr 5 10 k = column76_0_r5_10 k := by decide +kernel
lemma column76_0_r5_11_eq : ∀ k : Fin 16, column76_0Expr 5 11 k = column76_0_r5_11 k := by decide +kernel
lemma column76_0_r5_12_eq : ∀ k : Fin 16, column76_0Expr 5 12 k = column76_0_r5_12 k := by decide +kernel
lemma column76_0_r5_13_eq : ∀ k : Fin 16, column76_0Expr 5 13 k = column76_0_r5_13 k := by decide +kernel
lemma column76_0_r5_14_eq : ∀ k : Fin 16, column76_0Expr 5 14 k = column76_0_r5_14 k := by decide +kernel
lemma column76_0_r5_15_eq : ∀ k : Fin 16, column76_0Expr 5 15 k = column76_0_r5_15 k := by decide +kernel
lemma column76_0_r5_eq (i k : Fin 16) : column76_0Expr 5 i k = column76_0_r5 i k := by
  fin_cases i
  · exact column76_0_r5_0_eq k
  · exact column76_0_r5_1_eq k
  · exact column76_0_r5_2_eq k
  · exact column76_0_r5_3_eq k
  · exact column76_0_r5_4_eq k
  · exact column76_0_r5_5_eq k
  · exact column76_0_r5_6_eq k
  · exact column76_0_r5_7_eq k
  · exact column76_0_r5_8_eq k
  · exact column76_0_r5_9_eq k
  · exact column76_0_r5_10_eq k
  · exact column76_0_r5_11_eq k
  · exact column76_0_r5_12_eq k
  · exact column76_0_r5_13_eq k
  · exact column76_0_r5_14_eq k
  · exact column76_0_r5_15_eq k
lemma column76_0_eq (j : Fin 6) (i k : Fin 16) : column76_0Expr j i k = column76_0 j i k := by
  fin_cases j
  · exact column76_0_r0_eq i k
  · exact column76_0_r1_eq i k
  · exact column76_0_r2_eq i k
  · exact column76_0_r3_eq i k
  · exact column76_0_r4_eq i k
  · exact column76_0_r5_eq i k
lemma column76_0_contains_e_oai (j : Fin 6) (i k : Fin 16) :
    (column76_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction false 76 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column76_0_eq,basisFunction_wave,← mul_assoc]
  unfold column76_0Expr
  apply CBox.contains_mul_e
  · rw [← waveAmplitude_mod false 76 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp4_0_contains_e j i k
  · exact power76_contains j i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.column76_0_contains_e_oai := @OAI.SharpPlanar.CachedData.column76_0_contains_e_oai
