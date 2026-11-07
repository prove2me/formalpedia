-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.column19_1_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T19:49:16.722998+00:00
-- url     : https://prove2.me/submissions/9d83442f-b99e-4d0f-bccf-6f54b0cd00b9

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_CachedData_power16_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aTable_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bTable_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_exp_direct_step_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_phase12_periodic_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_waveAmplitudeBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weightRows_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_e

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

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aLookup_contains (n : ℕ) (j : Fin 6) : (aLookup n j).Contains (basisAlpha n j.val) := by
  simpa only [aLookup,basisAlpha_mod] using aTable_contains_e ⟨n%12,by omega⟩ j
lemma bLookup_contains (n : ℕ) (j : Fin 6) : (bLookup n j).Contains (basisBeta n j.val) := by
  simpa only [bLookup,basisBeta_mod] using bTable_contains_e ⟨n%12,by omega⟩ j
end SharpPlanar.IntegerAlpha

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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Amplitudes
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
lemma amp7_10_0_eq : ∀ k : Fin 16, amp7_1Expr 0 0 k = amp7_10_0 k := by decide +kernel
lemma amp7_10_1_eq : ∀ k : Fin 16, amp7_1Expr 0 1 k = amp7_10_1 k := by decide +kernel
lemma amp7_10_2_eq : ∀ k : Fin 16, amp7_1Expr 0 2 k = amp7_10_2 k := by decide +kernel
lemma amp7_10_3_eq : ∀ k : Fin 16, amp7_1Expr 0 3 k = amp7_10_3 k := by decide +kernel
lemma amp7_10_4_eq : ∀ k : Fin 16, amp7_1Expr 0 4 k = amp7_10_4 k := by decide +kernel
lemma amp7_10_5_eq : ∀ k : Fin 16, amp7_1Expr 0 5 k = amp7_10_5 k := by decide +kernel
lemma amp7_10_6_eq : ∀ k : Fin 16, amp7_1Expr 0 6 k = amp7_10_6 k := by decide +kernel
lemma amp7_10_7_eq : ∀ k : Fin 16, amp7_1Expr 0 7 k = amp7_10_7 k := by decide +kernel
lemma amp7_10_8_eq : ∀ k : Fin 16, amp7_1Expr 0 8 k = amp7_10_8 k := by decide +kernel
lemma amp7_10_9_eq : ∀ k : Fin 16, amp7_1Expr 0 9 k = amp7_10_9 k := by decide +kernel
lemma amp7_10_10_eq : ∀ k : Fin 16, amp7_1Expr 0 10 k = amp7_10_10 k := by decide +kernel
lemma amp7_10_11_eq : ∀ k : Fin 16, amp7_1Expr 0 11 k = amp7_10_11 k := by decide +kernel
lemma amp7_10_12_eq : ∀ k : Fin 16, amp7_1Expr 0 12 k = amp7_10_12 k := by decide +kernel
lemma amp7_10_13_eq : ∀ k : Fin 16, amp7_1Expr 0 13 k = amp7_10_13 k := by decide +kernel
lemma amp7_10_14_eq : ∀ k : Fin 16, amp7_1Expr 0 14 k = amp7_10_14 k := by decide +kernel
lemma amp7_10_15_eq : ∀ k : Fin 16, amp7_1Expr 0 15 k = amp7_10_15 k := by decide +kernel
lemma amp7_10_eq (i k : Fin 16) : amp7_1Expr 0 i k = amp7_10 i k := by
  fin_cases i
  · exact amp7_10_0_eq k
  · exact amp7_10_1_eq k
  · exact amp7_10_2_eq k
  · exact amp7_10_3_eq k
  · exact amp7_10_4_eq k
  · exact amp7_10_5_eq k
  · exact amp7_10_6_eq k
  · exact amp7_10_7_eq k
  · exact amp7_10_8_eq k
  · exact amp7_10_9_eq k
  · exact amp7_10_10_eq k
  · exact amp7_10_11_eq k
  · exact amp7_10_12_eq k
  · exact amp7_10_13_eq k
  · exact amp7_10_14_eq k
  · exact amp7_10_15_eq k
lemma amp7_11_0_eq : ∀ k : Fin 16, amp7_1Expr 1 0 k = amp7_11_0 k := by decide +kernel
lemma amp7_11_1_eq : ∀ k : Fin 16, amp7_1Expr 1 1 k = amp7_11_1 k := by decide +kernel
lemma amp7_11_2_eq : ∀ k : Fin 16, amp7_1Expr 1 2 k = amp7_11_2 k := by decide +kernel
lemma amp7_11_3_eq : ∀ k : Fin 16, amp7_1Expr 1 3 k = amp7_11_3 k := by decide +kernel
lemma amp7_11_4_eq : ∀ k : Fin 16, amp7_1Expr 1 4 k = amp7_11_4 k := by decide +kernel
lemma amp7_11_5_eq : ∀ k : Fin 16, amp7_1Expr 1 5 k = amp7_11_5 k := by decide +kernel
lemma amp7_11_6_eq : ∀ k : Fin 16, amp7_1Expr 1 6 k = amp7_11_6 k := by decide +kernel
lemma amp7_11_7_eq : ∀ k : Fin 16, amp7_1Expr 1 7 k = amp7_11_7 k := by decide +kernel
lemma amp7_11_8_eq : ∀ k : Fin 16, amp7_1Expr 1 8 k = amp7_11_8 k := by decide +kernel
lemma amp7_11_9_eq : ∀ k : Fin 16, amp7_1Expr 1 9 k = amp7_11_9 k := by decide +kernel
lemma amp7_11_10_eq : ∀ k : Fin 16, amp7_1Expr 1 10 k = amp7_11_10 k := by decide +kernel
lemma amp7_11_11_eq : ∀ k : Fin 16, amp7_1Expr 1 11 k = amp7_11_11 k := by decide +kernel
lemma amp7_11_12_eq : ∀ k : Fin 16, amp7_1Expr 1 12 k = amp7_11_12 k := by decide +kernel
lemma amp7_11_13_eq : ∀ k : Fin 16, amp7_1Expr 1 13 k = amp7_11_13 k := by decide +kernel
lemma amp7_11_14_eq : ∀ k : Fin 16, amp7_1Expr 1 14 k = amp7_11_14 k := by decide +kernel
lemma amp7_11_15_eq : ∀ k : Fin 16, amp7_1Expr 1 15 k = amp7_11_15 k := by decide +kernel
lemma amp7_11_eq (i k : Fin 16) : amp7_1Expr 1 i k = amp7_11 i k := by
  fin_cases i
  · exact amp7_11_0_eq k
  · exact amp7_11_1_eq k
  · exact amp7_11_2_eq k
  · exact amp7_11_3_eq k
  · exact amp7_11_4_eq k
  · exact amp7_11_5_eq k
  · exact amp7_11_6_eq k
  · exact amp7_11_7_eq k
  · exact amp7_11_8_eq k
  · exact amp7_11_9_eq k
  · exact amp7_11_10_eq k
  · exact amp7_11_11_eq k
  · exact amp7_11_12_eq k
  · exact amp7_11_13_eq k
  · exact amp7_11_14_eq k
  · exact amp7_11_15_eq k
lemma amp7_12_0_eq : ∀ k : Fin 16, amp7_1Expr 2 0 k = amp7_12_0 k := by decide +kernel
lemma amp7_12_1_eq : ∀ k : Fin 16, amp7_1Expr 2 1 k = amp7_12_1 k := by decide +kernel
lemma amp7_12_2_eq : ∀ k : Fin 16, amp7_1Expr 2 2 k = amp7_12_2 k := by decide +kernel
lemma amp7_12_3_eq : ∀ k : Fin 16, amp7_1Expr 2 3 k = amp7_12_3 k := by decide +kernel
lemma amp7_12_4_eq : ∀ k : Fin 16, amp7_1Expr 2 4 k = amp7_12_4 k := by decide +kernel
lemma amp7_12_5_eq : ∀ k : Fin 16, amp7_1Expr 2 5 k = amp7_12_5 k := by decide +kernel
lemma amp7_12_6_eq : ∀ k : Fin 16, amp7_1Expr 2 6 k = amp7_12_6 k := by decide +kernel
lemma amp7_12_7_eq : ∀ k : Fin 16, amp7_1Expr 2 7 k = amp7_12_7 k := by decide +kernel
lemma amp7_12_8_eq : ∀ k : Fin 16, amp7_1Expr 2 8 k = amp7_12_8 k := by decide +kernel
lemma amp7_12_9_eq : ∀ k : Fin 16, amp7_1Expr 2 9 k = amp7_12_9 k := by decide +kernel
lemma amp7_12_10_eq : ∀ k : Fin 16, amp7_1Expr 2 10 k = amp7_12_10 k := by decide +kernel
lemma amp7_12_11_eq : ∀ k : Fin 16, amp7_1Expr 2 11 k = amp7_12_11 k := by decide +kernel
lemma amp7_12_12_eq : ∀ k : Fin 16, amp7_1Expr 2 12 k = amp7_12_12 k := by decide +kernel
lemma amp7_12_13_eq : ∀ k : Fin 16, amp7_1Expr 2 13 k = amp7_12_13 k := by decide +kernel
lemma amp7_12_14_eq : ∀ k : Fin 16, amp7_1Expr 2 14 k = amp7_12_14 k := by decide +kernel
lemma amp7_12_15_eq : ∀ k : Fin 16, amp7_1Expr 2 15 k = amp7_12_15 k := by decide +kernel
lemma amp7_12_eq (i k : Fin 16) : amp7_1Expr 2 i k = amp7_12 i k := by
  fin_cases i
  · exact amp7_12_0_eq k
  · exact amp7_12_1_eq k
  · exact amp7_12_2_eq k
  · exact amp7_12_3_eq k
  · exact amp7_12_4_eq k
  · exact amp7_12_5_eq k
  · exact amp7_12_6_eq k
  · exact amp7_12_7_eq k
  · exact amp7_12_8_eq k
  · exact amp7_12_9_eq k
  · exact amp7_12_10_eq k
  · exact amp7_12_11_eq k
  · exact amp7_12_12_eq k
  · exact amp7_12_13_eq k
  · exact amp7_12_14_eq k
  · exact amp7_12_15_eq k
lemma amp7_13_0_eq : ∀ k : Fin 16, amp7_1Expr 3 0 k = amp7_13_0 k := by decide +kernel
lemma amp7_13_1_eq : ∀ k : Fin 16, amp7_1Expr 3 1 k = amp7_13_1 k := by decide +kernel
lemma amp7_13_2_eq : ∀ k : Fin 16, amp7_1Expr 3 2 k = amp7_13_2 k := by decide +kernel
lemma amp7_13_3_eq : ∀ k : Fin 16, amp7_1Expr 3 3 k = amp7_13_3 k := by decide +kernel
lemma amp7_13_4_eq : ∀ k : Fin 16, amp7_1Expr 3 4 k = amp7_13_4 k := by decide +kernel
lemma amp7_13_5_eq : ∀ k : Fin 16, amp7_1Expr 3 5 k = amp7_13_5 k := by decide +kernel
lemma amp7_13_6_eq : ∀ k : Fin 16, amp7_1Expr 3 6 k = amp7_13_6 k := by decide +kernel
lemma amp7_13_7_eq : ∀ k : Fin 16, amp7_1Expr 3 7 k = amp7_13_7 k := by decide +kernel
lemma amp7_13_8_eq : ∀ k : Fin 16, amp7_1Expr 3 8 k = amp7_13_8 k := by decide +kernel
lemma amp7_13_9_eq : ∀ k : Fin 16, amp7_1Expr 3 9 k = amp7_13_9 k := by decide +kernel
lemma amp7_13_10_eq : ∀ k : Fin 16, amp7_1Expr 3 10 k = amp7_13_10 k := by decide +kernel
lemma amp7_13_11_eq : ∀ k : Fin 16, amp7_1Expr 3 11 k = amp7_13_11 k := by decide +kernel
lemma amp7_13_12_eq : ∀ k : Fin 16, amp7_1Expr 3 12 k = amp7_13_12 k := by decide +kernel
lemma amp7_13_13_eq : ∀ k : Fin 16, amp7_1Expr 3 13 k = amp7_13_13 k := by decide +kernel
lemma amp7_13_14_eq : ∀ k : Fin 16, amp7_1Expr 3 14 k = amp7_13_14 k := by decide +kernel
lemma amp7_13_15_eq : ∀ k : Fin 16, amp7_1Expr 3 15 k = amp7_13_15 k := by decide +kernel
lemma amp7_13_eq (i k : Fin 16) : amp7_1Expr 3 i k = amp7_13 i k := by
  fin_cases i
  · exact amp7_13_0_eq k
  · exact amp7_13_1_eq k
  · exact amp7_13_2_eq k
  · exact amp7_13_3_eq k
  · exact amp7_13_4_eq k
  · exact amp7_13_5_eq k
  · exact amp7_13_6_eq k
  · exact amp7_13_7_eq k
  · exact amp7_13_8_eq k
  · exact amp7_13_9_eq k
  · exact amp7_13_10_eq k
  · exact amp7_13_11_eq k
  · exact amp7_13_12_eq k
  · exact amp7_13_13_eq k
  · exact amp7_13_14_eq k
  · exact amp7_13_15_eq k
lemma amp7_14_0_eq : ∀ k : Fin 16, amp7_1Expr 4 0 k = amp7_14_0 k := by decide +kernel
lemma amp7_14_1_eq : ∀ k : Fin 16, amp7_1Expr 4 1 k = amp7_14_1 k := by decide +kernel
lemma amp7_14_2_eq : ∀ k : Fin 16, amp7_1Expr 4 2 k = amp7_14_2 k := by decide +kernel
lemma amp7_14_3_eq : ∀ k : Fin 16, amp7_1Expr 4 3 k = amp7_14_3 k := by decide +kernel
lemma amp7_14_4_eq : ∀ k : Fin 16, amp7_1Expr 4 4 k = amp7_14_4 k := by decide +kernel
lemma amp7_14_5_eq : ∀ k : Fin 16, amp7_1Expr 4 5 k = amp7_14_5 k := by decide +kernel
lemma amp7_14_6_eq : ∀ k : Fin 16, amp7_1Expr 4 6 k = amp7_14_6 k := by decide +kernel
lemma amp7_14_7_eq : ∀ k : Fin 16, amp7_1Expr 4 7 k = amp7_14_7 k := by decide +kernel
lemma amp7_14_8_eq : ∀ k : Fin 16, amp7_1Expr 4 8 k = amp7_14_8 k := by decide +kernel
lemma amp7_14_9_eq : ∀ k : Fin 16, amp7_1Expr 4 9 k = amp7_14_9 k := by decide +kernel
lemma amp7_14_10_eq : ∀ k : Fin 16, amp7_1Expr 4 10 k = amp7_14_10 k := by decide +kernel
lemma amp7_14_11_eq : ∀ k : Fin 16, amp7_1Expr 4 11 k = amp7_14_11 k := by decide +kernel
lemma amp7_14_12_eq : ∀ k : Fin 16, amp7_1Expr 4 12 k = amp7_14_12 k := by decide +kernel
lemma amp7_14_13_eq : ∀ k : Fin 16, amp7_1Expr 4 13 k = amp7_14_13 k := by decide +kernel
lemma amp7_14_14_eq : ∀ k : Fin 16, amp7_1Expr 4 14 k = amp7_14_14 k := by decide +kernel
lemma amp7_14_15_eq : ∀ k : Fin 16, amp7_1Expr 4 15 k = amp7_14_15 k := by decide +kernel
lemma amp7_14_eq (i k : Fin 16) : amp7_1Expr 4 i k = amp7_14 i k := by
  fin_cases i
  · exact amp7_14_0_eq k
  · exact amp7_14_1_eq k
  · exact amp7_14_2_eq k
  · exact amp7_14_3_eq k
  · exact amp7_14_4_eq k
  · exact amp7_14_5_eq k
  · exact amp7_14_6_eq k
  · exact amp7_14_7_eq k
  · exact amp7_14_8_eq k
  · exact amp7_14_9_eq k
  · exact amp7_14_10_eq k
  · exact amp7_14_11_eq k
  · exact amp7_14_12_eq k
  · exact amp7_14_13_eq k
  · exact amp7_14_14_eq k
  · exact amp7_14_15_eq k
lemma amp7_15_0_eq : ∀ k : Fin 16, amp7_1Expr 5 0 k = amp7_15_0 k := by decide +kernel
lemma amp7_15_1_eq : ∀ k : Fin 16, amp7_1Expr 5 1 k = amp7_15_1 k := by decide +kernel
lemma amp7_15_2_eq : ∀ k : Fin 16, amp7_1Expr 5 2 k = amp7_15_2 k := by decide +kernel
lemma amp7_15_3_eq : ∀ k : Fin 16, amp7_1Expr 5 3 k = amp7_15_3 k := by decide +kernel
lemma amp7_15_4_eq : ∀ k : Fin 16, amp7_1Expr 5 4 k = amp7_15_4 k := by decide +kernel
lemma amp7_15_5_eq : ∀ k : Fin 16, amp7_1Expr 5 5 k = amp7_15_5 k := by decide +kernel
lemma amp7_15_6_eq : ∀ k : Fin 16, amp7_1Expr 5 6 k = amp7_15_6 k := by decide +kernel
lemma amp7_15_7_eq : ∀ k : Fin 16, amp7_1Expr 5 7 k = amp7_15_7 k := by decide +kernel
lemma amp7_15_8_eq : ∀ k : Fin 16, amp7_1Expr 5 8 k = amp7_15_8 k := by decide +kernel
lemma amp7_15_9_eq : ∀ k : Fin 16, amp7_1Expr 5 9 k = amp7_15_9 k := by decide +kernel
lemma amp7_15_10_eq : ∀ k : Fin 16, amp7_1Expr 5 10 k = amp7_15_10 k := by decide +kernel
lemma amp7_15_11_eq : ∀ k : Fin 16, amp7_1Expr 5 11 k = amp7_15_11 k := by decide +kernel
lemma amp7_15_12_eq : ∀ k : Fin 16, amp7_1Expr 5 12 k = amp7_15_12 k := by decide +kernel
lemma amp7_15_13_eq : ∀ k : Fin 16, amp7_1Expr 5 13 k = amp7_15_13 k := by decide +kernel
lemma amp7_15_14_eq : ∀ k : Fin 16, amp7_1Expr 5 14 k = amp7_15_14 k := by decide +kernel
lemma amp7_15_15_eq : ∀ k : Fin 16, amp7_1Expr 5 15 k = amp7_15_15 k := by decide +kernel
lemma amp7_15_eq (i k : Fin 16) : amp7_1Expr 5 i k = amp7_15 i k := by
  fin_cases i
  · exact amp7_15_0_eq k
  · exact amp7_15_1_eq k
  · exact amp7_15_2_eq k
  · exact amp7_15_3_eq k
  · exact amp7_15_4_eq k
  · exact amp7_15_5_eq k
  · exact amp7_15_6_eq k
  · exact amp7_15_7_eq k
  · exact amp7_15_8_eq k
  · exact amp7_15_9_eq k
  · exact amp7_15_10_eq k
  · exact amp7_15_11_eq k
  · exact amp7_15_12_eq k
  · exact amp7_15_13_eq k
  · exact amp7_15_14_eq k
  · exact amp7_15_15_eq k
lemma amp7_1_eq (j : Fin 6) (i k : Fin 16) : amp7_1Expr j i k = amp7_1 j i k := by
  fin_cases j
  · exact amp7_10_eq i k
  · exact amp7_11_eq i k
  · exact amp7_12_eq i k
  · exact amp7_13_eq i k
  · exact amp7_14_eq i k
  · exact amp7_15_eq i k
lemma amp7_1_contains (j : Fin 6) (i k : Fin 16) :
    (amp7_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*waveAmplitude true 7 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← amp7_1_eq]
  exact CBox.contains_mul_e (rcast_contains_e (weightRows_contains_e i k))
    (waveAmplitudeBox_contains_e (gridRows_contains_e j i k) (aLookup_contains 7 j) (bLookup_contains 7 j) true)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers20
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
lemma power17_r0_0_eq : ∀ k : Fin 16, power17Expr 0 0 k = power17_r0_0 k := by decide +kernel
lemma power17_r0_1_eq : ∀ k : Fin 16, power17Expr 0 1 k = power17_r0_1 k := by decide +kernel
lemma power17_r0_2_eq : ∀ k : Fin 16, power17Expr 0 2 k = power17_r0_2 k := by decide +kernel
lemma power17_r0_3_eq : ∀ k : Fin 16, power17Expr 0 3 k = power17_r0_3 k := by decide +kernel
lemma power17_r0_4_eq : ∀ k : Fin 16, power17Expr 0 4 k = power17_r0_4 k := by decide +kernel
lemma power17_r0_5_eq : ∀ k : Fin 16, power17Expr 0 5 k = power17_r0_5 k := by decide +kernel
lemma power17_r0_6_eq : ∀ k : Fin 16, power17Expr 0 6 k = power17_r0_6 k := by decide +kernel
lemma power17_r0_7_eq : ∀ k : Fin 16, power17Expr 0 7 k = power17_r0_7 k := by decide +kernel
lemma power17_r0_8_eq : ∀ k : Fin 16, power17Expr 0 8 k = power17_r0_8 k := by decide +kernel
lemma power17_r0_9_eq : ∀ k : Fin 16, power17Expr 0 9 k = power17_r0_9 k := by decide +kernel
lemma power17_r0_10_eq : ∀ k : Fin 16, power17Expr 0 10 k = power17_r0_10 k := by decide +kernel
lemma power17_r0_11_eq : ∀ k : Fin 16, power17Expr 0 11 k = power17_r0_11 k := by decide +kernel
lemma power17_r0_12_eq : ∀ k : Fin 16, power17Expr 0 12 k = power17_r0_12 k := by decide +kernel
lemma power17_r0_13_eq : ∀ k : Fin 16, power17Expr 0 13 k = power17_r0_13 k := by decide +kernel
lemma power17_r0_14_eq : ∀ k : Fin 16, power17Expr 0 14 k = power17_r0_14 k := by decide +kernel
lemma power17_r0_15_eq : ∀ k : Fin 16, power17Expr 0 15 k = power17_r0_15 k := by decide +kernel
lemma power17_r0_eq (i k : Fin 16) : power17Expr 0 i k = power17_r0 i k := by
  fin_cases i
  · exact power17_r0_0_eq k
  · exact power17_r0_1_eq k
  · exact power17_r0_2_eq k
  · exact power17_r0_3_eq k
  · exact power17_r0_4_eq k
  · exact power17_r0_5_eq k
  · exact power17_r0_6_eq k
  · exact power17_r0_7_eq k
  · exact power17_r0_8_eq k
  · exact power17_r0_9_eq k
  · exact power17_r0_10_eq k
  · exact power17_r0_11_eq k
  · exact power17_r0_12_eq k
  · exact power17_r0_13_eq k
  · exact power17_r0_14_eq k
  · exact power17_r0_15_eq k
lemma power17_r1_0_eq : ∀ k : Fin 16, power17Expr 1 0 k = power17_r1_0 k := by decide +kernel
lemma power17_r1_1_eq : ∀ k : Fin 16, power17Expr 1 1 k = power17_r1_1 k := by decide +kernel
lemma power17_r1_2_eq : ∀ k : Fin 16, power17Expr 1 2 k = power17_r1_2 k := by decide +kernel
lemma power17_r1_3_eq : ∀ k : Fin 16, power17Expr 1 3 k = power17_r1_3 k := by decide +kernel
lemma power17_r1_4_eq : ∀ k : Fin 16, power17Expr 1 4 k = power17_r1_4 k := by decide +kernel
lemma power17_r1_5_eq : ∀ k : Fin 16, power17Expr 1 5 k = power17_r1_5 k := by decide +kernel
lemma power17_r1_6_eq : ∀ k : Fin 16, power17Expr 1 6 k = power17_r1_6 k := by decide +kernel
lemma power17_r1_7_eq : ∀ k : Fin 16, power17Expr 1 7 k = power17_r1_7 k := by decide +kernel
lemma power17_r1_8_eq : ∀ k : Fin 16, power17Expr 1 8 k = power17_r1_8 k := by decide +kernel
lemma power17_r1_9_eq : ∀ k : Fin 16, power17Expr 1 9 k = power17_r1_9 k := by decide +kernel
lemma power17_r1_10_eq : ∀ k : Fin 16, power17Expr 1 10 k = power17_r1_10 k := by decide +kernel
lemma power17_r1_11_eq : ∀ k : Fin 16, power17Expr 1 11 k = power17_r1_11 k := by decide +kernel
lemma power17_r1_12_eq : ∀ k : Fin 16, power17Expr 1 12 k = power17_r1_12 k := by decide +kernel
lemma power17_r1_13_eq : ∀ k : Fin 16, power17Expr 1 13 k = power17_r1_13 k := by decide +kernel
lemma power17_r1_14_eq : ∀ k : Fin 16, power17Expr 1 14 k = power17_r1_14 k := by decide +kernel
lemma power17_r1_15_eq : ∀ k : Fin 16, power17Expr 1 15 k = power17_r1_15 k := by decide +kernel
lemma power17_r1_eq (i k : Fin 16) : power17Expr 1 i k = power17_r1 i k := by
  fin_cases i
  · exact power17_r1_0_eq k
  · exact power17_r1_1_eq k
  · exact power17_r1_2_eq k
  · exact power17_r1_3_eq k
  · exact power17_r1_4_eq k
  · exact power17_r1_5_eq k
  · exact power17_r1_6_eq k
  · exact power17_r1_7_eq k
  · exact power17_r1_8_eq k
  · exact power17_r1_9_eq k
  · exact power17_r1_10_eq k
  · exact power17_r1_11_eq k
  · exact power17_r1_12_eq k
  · exact power17_r1_13_eq k
  · exact power17_r1_14_eq k
  · exact power17_r1_15_eq k
lemma power17_r2_0_eq : ∀ k : Fin 16, power17Expr 2 0 k = power17_r2_0 k := by decide +kernel
lemma power17_r2_1_eq : ∀ k : Fin 16, power17Expr 2 1 k = power17_r2_1 k := by decide +kernel
lemma power17_r2_2_eq : ∀ k : Fin 16, power17Expr 2 2 k = power17_r2_2 k := by decide +kernel
lemma power17_r2_3_eq : ∀ k : Fin 16, power17Expr 2 3 k = power17_r2_3 k := by decide +kernel
lemma power17_r2_4_eq : ∀ k : Fin 16, power17Expr 2 4 k = power17_r2_4 k := by decide +kernel
lemma power17_r2_5_eq : ∀ k : Fin 16, power17Expr 2 5 k = power17_r2_5 k := by decide +kernel
lemma power17_r2_6_eq : ∀ k : Fin 16, power17Expr 2 6 k = power17_r2_6 k := by decide +kernel
lemma power17_r2_7_eq : ∀ k : Fin 16, power17Expr 2 7 k = power17_r2_7 k := by decide +kernel
lemma power17_r2_8_eq : ∀ k : Fin 16, power17Expr 2 8 k = power17_r2_8 k := by decide +kernel
lemma power17_r2_9_eq : ∀ k : Fin 16, power17Expr 2 9 k = power17_r2_9 k := by decide +kernel
lemma power17_r2_10_eq : ∀ k : Fin 16, power17Expr 2 10 k = power17_r2_10 k := by decide +kernel
lemma power17_r2_11_eq : ∀ k : Fin 16, power17Expr 2 11 k = power17_r2_11 k := by decide +kernel
lemma power17_r2_12_eq : ∀ k : Fin 16, power17Expr 2 12 k = power17_r2_12 k := by decide +kernel
lemma power17_r2_13_eq : ∀ k : Fin 16, power17Expr 2 13 k = power17_r2_13 k := by decide +kernel
lemma power17_r2_14_eq : ∀ k : Fin 16, power17Expr 2 14 k = power17_r2_14 k := by decide +kernel
lemma power17_r2_15_eq : ∀ k : Fin 16, power17Expr 2 15 k = power17_r2_15 k := by decide +kernel
lemma power17_r2_eq (i k : Fin 16) : power17Expr 2 i k = power17_r2 i k := by
  fin_cases i
  · exact power17_r2_0_eq k
  · exact power17_r2_1_eq k
  · exact power17_r2_2_eq k
  · exact power17_r2_3_eq k
  · exact power17_r2_4_eq k
  · exact power17_r2_5_eq k
  · exact power17_r2_6_eq k
  · exact power17_r2_7_eq k
  · exact power17_r2_8_eq k
  · exact power17_r2_9_eq k
  · exact power17_r2_10_eq k
  · exact power17_r2_11_eq k
  · exact power17_r2_12_eq k
  · exact power17_r2_13_eq k
  · exact power17_r2_14_eq k
  · exact power17_r2_15_eq k
lemma power17_r3_0_eq : ∀ k : Fin 16, power17Expr 3 0 k = power17_r3_0 k := by decide +kernel
lemma power17_r3_1_eq : ∀ k : Fin 16, power17Expr 3 1 k = power17_r3_1 k := by decide +kernel
lemma power17_r3_2_eq : ∀ k : Fin 16, power17Expr 3 2 k = power17_r3_2 k := by decide +kernel
lemma power17_r3_3_eq : ∀ k : Fin 16, power17Expr 3 3 k = power17_r3_3 k := by decide +kernel
lemma power17_r3_4_eq : ∀ k : Fin 16, power17Expr 3 4 k = power17_r3_4 k := by decide +kernel
lemma power17_r3_5_eq : ∀ k : Fin 16, power17Expr 3 5 k = power17_r3_5 k := by decide +kernel
lemma power17_r3_6_eq : ∀ k : Fin 16, power17Expr 3 6 k = power17_r3_6 k := by decide +kernel
lemma power17_r3_7_eq : ∀ k : Fin 16, power17Expr 3 7 k = power17_r3_7 k := by decide +kernel
lemma power17_r3_8_eq : ∀ k : Fin 16, power17Expr 3 8 k = power17_r3_8 k := by decide +kernel
lemma power17_r3_9_eq : ∀ k : Fin 16, power17Expr 3 9 k = power17_r3_9 k := by decide +kernel
lemma power17_r3_10_eq : ∀ k : Fin 16, power17Expr 3 10 k = power17_r3_10 k := by decide +kernel
lemma power17_r3_11_eq : ∀ k : Fin 16, power17Expr 3 11 k = power17_r3_11 k := by decide +kernel
lemma power17_r3_12_eq : ∀ k : Fin 16, power17Expr 3 12 k = power17_r3_12 k := by decide +kernel
lemma power17_r3_13_eq : ∀ k : Fin 16, power17Expr 3 13 k = power17_r3_13 k := by decide +kernel
lemma power17_r3_14_eq : ∀ k : Fin 16, power17Expr 3 14 k = power17_r3_14 k := by decide +kernel
lemma power17_r3_15_eq : ∀ k : Fin 16, power17Expr 3 15 k = power17_r3_15 k := by decide +kernel
lemma power17_r3_eq (i k : Fin 16) : power17Expr 3 i k = power17_r3 i k := by
  fin_cases i
  · exact power17_r3_0_eq k
  · exact power17_r3_1_eq k
  · exact power17_r3_2_eq k
  · exact power17_r3_3_eq k
  · exact power17_r3_4_eq k
  · exact power17_r3_5_eq k
  · exact power17_r3_6_eq k
  · exact power17_r3_7_eq k
  · exact power17_r3_8_eq k
  · exact power17_r3_9_eq k
  · exact power17_r3_10_eq k
  · exact power17_r3_11_eq k
  · exact power17_r3_12_eq k
  · exact power17_r3_13_eq k
  · exact power17_r3_14_eq k
  · exact power17_r3_15_eq k
lemma power17_r4_0_eq : ∀ k : Fin 16, power17Expr 4 0 k = power17_r4_0 k := by decide +kernel
lemma power17_r4_1_eq : ∀ k : Fin 16, power17Expr 4 1 k = power17_r4_1 k := by decide +kernel
lemma power17_r4_2_eq : ∀ k : Fin 16, power17Expr 4 2 k = power17_r4_2 k := by decide +kernel
lemma power17_r4_3_eq : ∀ k : Fin 16, power17Expr 4 3 k = power17_r4_3 k := by decide +kernel
lemma power17_r4_4_eq : ∀ k : Fin 16, power17Expr 4 4 k = power17_r4_4 k := by decide +kernel
lemma power17_r4_5_eq : ∀ k : Fin 16, power17Expr 4 5 k = power17_r4_5 k := by decide +kernel
lemma power17_r4_6_eq : ∀ k : Fin 16, power17Expr 4 6 k = power17_r4_6 k := by decide +kernel
lemma power17_r4_7_eq : ∀ k : Fin 16, power17Expr 4 7 k = power17_r4_7 k := by decide +kernel
lemma power17_r4_8_eq : ∀ k : Fin 16, power17Expr 4 8 k = power17_r4_8 k := by decide +kernel
lemma power17_r4_9_eq : ∀ k : Fin 16, power17Expr 4 9 k = power17_r4_9 k := by decide +kernel
lemma power17_r4_10_eq : ∀ k : Fin 16, power17Expr 4 10 k = power17_r4_10 k := by decide +kernel
lemma power17_r4_11_eq : ∀ k : Fin 16, power17Expr 4 11 k = power17_r4_11 k := by decide +kernel
lemma power17_r4_12_eq : ∀ k : Fin 16, power17Expr 4 12 k = power17_r4_12 k := by decide +kernel
lemma power17_r4_13_eq : ∀ k : Fin 16, power17Expr 4 13 k = power17_r4_13 k := by decide +kernel
lemma power17_r4_14_eq : ∀ k : Fin 16, power17Expr 4 14 k = power17_r4_14 k := by decide +kernel
lemma power17_r4_15_eq : ∀ k : Fin 16, power17Expr 4 15 k = power17_r4_15 k := by decide +kernel
lemma power17_r4_eq (i k : Fin 16) : power17Expr 4 i k = power17_r4 i k := by
  fin_cases i
  · exact power17_r4_0_eq k
  · exact power17_r4_1_eq k
  · exact power17_r4_2_eq k
  · exact power17_r4_3_eq k
  · exact power17_r4_4_eq k
  · exact power17_r4_5_eq k
  · exact power17_r4_6_eq k
  · exact power17_r4_7_eq k
  · exact power17_r4_8_eq k
  · exact power17_r4_9_eq k
  · exact power17_r4_10_eq k
  · exact power17_r4_11_eq k
  · exact power17_r4_12_eq k
  · exact power17_r4_13_eq k
  · exact power17_r4_14_eq k
  · exact power17_r4_15_eq k
lemma power17_r5_0_eq : ∀ k : Fin 16, power17Expr 5 0 k = power17_r5_0 k := by decide +kernel
lemma power17_r5_1_eq : ∀ k : Fin 16, power17Expr 5 1 k = power17_r5_1 k := by decide +kernel
lemma power17_r5_2_eq : ∀ k : Fin 16, power17Expr 5 2 k = power17_r5_2 k := by decide +kernel
lemma power17_r5_3_eq : ∀ k : Fin 16, power17Expr 5 3 k = power17_r5_3 k := by decide +kernel
lemma power17_r5_4_eq : ∀ k : Fin 16, power17Expr 5 4 k = power17_r5_4 k := by decide +kernel
lemma power17_r5_5_eq : ∀ k : Fin 16, power17Expr 5 5 k = power17_r5_5 k := by decide +kernel
lemma power17_r5_6_eq : ∀ k : Fin 16, power17Expr 5 6 k = power17_r5_6 k := by decide +kernel
lemma power17_r5_7_eq : ∀ k : Fin 16, power17Expr 5 7 k = power17_r5_7 k := by decide +kernel
lemma power17_r5_8_eq : ∀ k : Fin 16, power17Expr 5 8 k = power17_r5_8 k := by decide +kernel
lemma power17_r5_9_eq : ∀ k : Fin 16, power17Expr 5 9 k = power17_r5_9 k := by decide +kernel
lemma power17_r5_10_eq : ∀ k : Fin 16, power17Expr 5 10 k = power17_r5_10 k := by decide +kernel
lemma power17_r5_11_eq : ∀ k : Fin 16, power17Expr 5 11 k = power17_r5_11 k := by decide +kernel
lemma power17_r5_12_eq : ∀ k : Fin 16, power17Expr 5 12 k = power17_r5_12 k := by decide +kernel
lemma power17_r5_13_eq : ∀ k : Fin 16, power17Expr 5 13 k = power17_r5_13 k := by decide +kernel
lemma power17_r5_14_eq : ∀ k : Fin 16, power17Expr 5 14 k = power17_r5_14 k := by decide +kernel
lemma power17_r5_15_eq : ∀ k : Fin 16, power17Expr 5 15 k = power17_r5_15 k := by decide +kernel
lemma power17_r5_eq (i k : Fin 16) : power17Expr 5 i k = power17_r5 i k := by
  fin_cases i
  · exact power17_r5_0_eq k
  · exact power17_r5_1_eq k
  · exact power17_r5_2_eq k
  · exact power17_r5_3_eq k
  · exact power17_r5_4_eq k
  · exact power17_r5_5_eq k
  · exact power17_r5_6_eq k
  · exact power17_r5_7_eq k
  · exact power17_r5_8_eq k
  · exact power17_r5_9_eq k
  · exact power17_r5_10_eq k
  · exact power17_r5_11_eq k
  · exact power17_r5_12_eq k
  · exact power17_r5_13_eq k
  · exact power17_r5_14_eq k
  · exact power17_r5_15_eq k
lemma power17_eq (j : Fin 6) (i k : Fin 16) : power17Expr j i k = power17 j i k := by
  fin_cases j
  · exact power17_r0_eq i k
  · exact power17_r1_eq i k
  · exact power17_r2_eq i k
  · exact power17_r3_eq i k
  · exact power17_r4_eq i k
  · exact power17_r5_eq i k
lemma power17_contains (j : Fin 6) (i k : Fin 16) :
    (power17 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(17:ℕ))) := by
  rw [← power17_eq]
  unfold power17Expr
  convert exp_direct_step_e (power16_contains_e j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power18_r0_0_eq : ∀ k : Fin 16, power18Expr 0 0 k = power18_r0_0 k := by decide +kernel
lemma power18_r0_1_eq : ∀ k : Fin 16, power18Expr 0 1 k = power18_r0_1 k := by decide +kernel
lemma power18_r0_2_eq : ∀ k : Fin 16, power18Expr 0 2 k = power18_r0_2 k := by decide +kernel
lemma power18_r0_3_eq : ∀ k : Fin 16, power18Expr 0 3 k = power18_r0_3 k := by decide +kernel
lemma power18_r0_4_eq : ∀ k : Fin 16, power18Expr 0 4 k = power18_r0_4 k := by decide +kernel
lemma power18_r0_5_eq : ∀ k : Fin 16, power18Expr 0 5 k = power18_r0_5 k := by decide +kernel
lemma power18_r0_6_eq : ∀ k : Fin 16, power18Expr 0 6 k = power18_r0_6 k := by decide +kernel
lemma power18_r0_7_eq : ∀ k : Fin 16, power18Expr 0 7 k = power18_r0_7 k := by decide +kernel
lemma power18_r0_8_eq : ∀ k : Fin 16, power18Expr 0 8 k = power18_r0_8 k := by decide +kernel
lemma power18_r0_9_eq : ∀ k : Fin 16, power18Expr 0 9 k = power18_r0_9 k := by decide +kernel
lemma power18_r0_10_eq : ∀ k : Fin 16, power18Expr 0 10 k = power18_r0_10 k := by decide +kernel
lemma power18_r0_11_eq : ∀ k : Fin 16, power18Expr 0 11 k = power18_r0_11 k := by decide +kernel
lemma power18_r0_12_eq : ∀ k : Fin 16, power18Expr 0 12 k = power18_r0_12 k := by decide +kernel
lemma power18_r0_13_eq : ∀ k : Fin 16, power18Expr 0 13 k = power18_r0_13 k := by decide +kernel
lemma power18_r0_14_eq : ∀ k : Fin 16, power18Expr 0 14 k = power18_r0_14 k := by decide +kernel
lemma power18_r0_15_eq : ∀ k : Fin 16, power18Expr 0 15 k = power18_r0_15 k := by decide +kernel
lemma power18_r0_eq (i k : Fin 16) : power18Expr 0 i k = power18_r0 i k := by
  fin_cases i
  · exact power18_r0_0_eq k
  · exact power18_r0_1_eq k
  · exact power18_r0_2_eq k
  · exact power18_r0_3_eq k
  · exact power18_r0_4_eq k
  · exact power18_r0_5_eq k
  · exact power18_r0_6_eq k
  · exact power18_r0_7_eq k
  · exact power18_r0_8_eq k
  · exact power18_r0_9_eq k
  · exact power18_r0_10_eq k
  · exact power18_r0_11_eq k
  · exact power18_r0_12_eq k
  · exact power18_r0_13_eq k
  · exact power18_r0_14_eq k
  · exact power18_r0_15_eq k
lemma power18_r1_0_eq : ∀ k : Fin 16, power18Expr 1 0 k = power18_r1_0 k := by decide +kernel
lemma power18_r1_1_eq : ∀ k : Fin 16, power18Expr 1 1 k = power18_r1_1 k := by decide +kernel
lemma power18_r1_2_eq : ∀ k : Fin 16, power18Expr 1 2 k = power18_r1_2 k := by decide +kernel
lemma power18_r1_3_eq : ∀ k : Fin 16, power18Expr 1 3 k = power18_r1_3 k := by decide +kernel
lemma power18_r1_4_eq : ∀ k : Fin 16, power18Expr 1 4 k = power18_r1_4 k := by decide +kernel
lemma power18_r1_5_eq : ∀ k : Fin 16, power18Expr 1 5 k = power18_r1_5 k := by decide +kernel
lemma power18_r1_6_eq : ∀ k : Fin 16, power18Expr 1 6 k = power18_r1_6 k := by decide +kernel
lemma power18_r1_7_eq : ∀ k : Fin 16, power18Expr 1 7 k = power18_r1_7 k := by decide +kernel
lemma power18_r1_8_eq : ∀ k : Fin 16, power18Expr 1 8 k = power18_r1_8 k := by decide +kernel
lemma power18_r1_9_eq : ∀ k : Fin 16, power18Expr 1 9 k = power18_r1_9 k := by decide +kernel
lemma power18_r1_10_eq : ∀ k : Fin 16, power18Expr 1 10 k = power18_r1_10 k := by decide +kernel
lemma power18_r1_11_eq : ∀ k : Fin 16, power18Expr 1 11 k = power18_r1_11 k := by decide +kernel
lemma power18_r1_12_eq : ∀ k : Fin 16, power18Expr 1 12 k = power18_r1_12 k := by decide +kernel
lemma power18_r1_13_eq : ∀ k : Fin 16, power18Expr 1 13 k = power18_r1_13 k := by decide +kernel
lemma power18_r1_14_eq : ∀ k : Fin 16, power18Expr 1 14 k = power18_r1_14 k := by decide +kernel
lemma power18_r1_15_eq : ∀ k : Fin 16, power18Expr 1 15 k = power18_r1_15 k := by decide +kernel
lemma power18_r1_eq (i k : Fin 16) : power18Expr 1 i k = power18_r1 i k := by
  fin_cases i
  · exact power18_r1_0_eq k
  · exact power18_r1_1_eq k
  · exact power18_r1_2_eq k
  · exact power18_r1_3_eq k
  · exact power18_r1_4_eq k
  · exact power18_r1_5_eq k
  · exact power18_r1_6_eq k
  · exact power18_r1_7_eq k
  · exact power18_r1_8_eq k
  · exact power18_r1_9_eq k
  · exact power18_r1_10_eq k
  · exact power18_r1_11_eq k
  · exact power18_r1_12_eq k
  · exact power18_r1_13_eq k
  · exact power18_r1_14_eq k
  · exact power18_r1_15_eq k
lemma power18_r2_0_eq : ∀ k : Fin 16, power18Expr 2 0 k = power18_r2_0 k := by decide +kernel
lemma power18_r2_1_eq : ∀ k : Fin 16, power18Expr 2 1 k = power18_r2_1 k := by decide +kernel
lemma power18_r2_2_eq : ∀ k : Fin 16, power18Expr 2 2 k = power18_r2_2 k := by decide +kernel
lemma power18_r2_3_eq : ∀ k : Fin 16, power18Expr 2 3 k = power18_r2_3 k := by decide +kernel
lemma power18_r2_4_eq : ∀ k : Fin 16, power18Expr 2 4 k = power18_r2_4 k := by decide +kernel
lemma power18_r2_5_eq : ∀ k : Fin 16, power18Expr 2 5 k = power18_r2_5 k := by decide +kernel
lemma power18_r2_6_eq : ∀ k : Fin 16, power18Expr 2 6 k = power18_r2_6 k := by decide +kernel
lemma power18_r2_7_eq : ∀ k : Fin 16, power18Expr 2 7 k = power18_r2_7 k := by decide +kernel
lemma power18_r2_8_eq : ∀ k : Fin 16, power18Expr 2 8 k = power18_r2_8 k := by decide +kernel
lemma power18_r2_9_eq : ∀ k : Fin 16, power18Expr 2 9 k = power18_r2_9 k := by decide +kernel
lemma power18_r2_10_eq : ∀ k : Fin 16, power18Expr 2 10 k = power18_r2_10 k := by decide +kernel
lemma power18_r2_11_eq : ∀ k : Fin 16, power18Expr 2 11 k = power18_r2_11 k := by decide +kernel
lemma power18_r2_12_eq : ∀ k : Fin 16, power18Expr 2 12 k = power18_r2_12 k := by decide +kernel
lemma power18_r2_13_eq : ∀ k : Fin 16, power18Expr 2 13 k = power18_r2_13 k := by decide +kernel
lemma power18_r2_14_eq : ∀ k : Fin 16, power18Expr 2 14 k = power18_r2_14 k := by decide +kernel
lemma power18_r2_15_eq : ∀ k : Fin 16, power18Expr 2 15 k = power18_r2_15 k := by decide +kernel
lemma power18_r2_eq (i k : Fin 16) : power18Expr 2 i k = power18_r2 i k := by
  fin_cases i
  · exact power18_r2_0_eq k
  · exact power18_r2_1_eq k
  · exact power18_r2_2_eq k
  · exact power18_r2_3_eq k
  · exact power18_r2_4_eq k
  · exact power18_r2_5_eq k
  · exact power18_r2_6_eq k
  · exact power18_r2_7_eq k
  · exact power18_r2_8_eq k
  · exact power18_r2_9_eq k
  · exact power18_r2_10_eq k
  · exact power18_r2_11_eq k
  · exact power18_r2_12_eq k
  · exact power18_r2_13_eq k
  · exact power18_r2_14_eq k
  · exact power18_r2_15_eq k
lemma power18_r3_0_eq : ∀ k : Fin 16, power18Expr 3 0 k = power18_r3_0 k := by decide +kernel
lemma power18_r3_1_eq : ∀ k : Fin 16, power18Expr 3 1 k = power18_r3_1 k := by decide +kernel
lemma power18_r3_2_eq : ∀ k : Fin 16, power18Expr 3 2 k = power18_r3_2 k := by decide +kernel
lemma power18_r3_3_eq : ∀ k : Fin 16, power18Expr 3 3 k = power18_r3_3 k := by decide +kernel
lemma power18_r3_4_eq : ∀ k : Fin 16, power18Expr 3 4 k = power18_r3_4 k := by decide +kernel
lemma power18_r3_5_eq : ∀ k : Fin 16, power18Expr 3 5 k = power18_r3_5 k := by decide +kernel
lemma power18_r3_6_eq : ∀ k : Fin 16, power18Expr 3 6 k = power18_r3_6 k := by decide +kernel
lemma power18_r3_7_eq : ∀ k : Fin 16, power18Expr 3 7 k = power18_r3_7 k := by decide +kernel
lemma power18_r3_8_eq : ∀ k : Fin 16, power18Expr 3 8 k = power18_r3_8 k := by decide +kernel
lemma power18_r3_9_eq : ∀ k : Fin 16, power18Expr 3 9 k = power18_r3_9 k := by decide +kernel
lemma power18_r3_10_eq : ∀ k : Fin 16, power18Expr 3 10 k = power18_r3_10 k := by decide +kernel
lemma power18_r3_11_eq : ∀ k : Fin 16, power18Expr 3 11 k = power18_r3_11 k := by decide +kernel
lemma power18_r3_12_eq : ∀ k : Fin 16, power18Expr 3 12 k = power18_r3_12 k := by decide +kernel
lemma power18_r3_13_eq : ∀ k : Fin 16, power18Expr 3 13 k = power18_r3_13 k := by decide +kernel
lemma power18_r3_14_eq : ∀ k : Fin 16, power18Expr 3 14 k = power18_r3_14 k := by decide +kernel
lemma power18_r3_15_eq : ∀ k : Fin 16, power18Expr 3 15 k = power18_r3_15 k := by decide +kernel
lemma power18_r3_eq (i k : Fin 16) : power18Expr 3 i k = power18_r3 i k := by
  fin_cases i
  · exact power18_r3_0_eq k
  · exact power18_r3_1_eq k
  · exact power18_r3_2_eq k
  · exact power18_r3_3_eq k
  · exact power18_r3_4_eq k
  · exact power18_r3_5_eq k
  · exact power18_r3_6_eq k
  · exact power18_r3_7_eq k
  · exact power18_r3_8_eq k
  · exact power18_r3_9_eq k
  · exact power18_r3_10_eq k
  · exact power18_r3_11_eq k
  · exact power18_r3_12_eq k
  · exact power18_r3_13_eq k
  · exact power18_r3_14_eq k
  · exact power18_r3_15_eq k
lemma power18_r4_0_eq : ∀ k : Fin 16, power18Expr 4 0 k = power18_r4_0 k := by decide +kernel
lemma power18_r4_1_eq : ∀ k : Fin 16, power18Expr 4 1 k = power18_r4_1 k := by decide +kernel
lemma power18_r4_2_eq : ∀ k : Fin 16, power18Expr 4 2 k = power18_r4_2 k := by decide +kernel
lemma power18_r4_3_eq : ∀ k : Fin 16, power18Expr 4 3 k = power18_r4_3 k := by decide +kernel
lemma power18_r4_4_eq : ∀ k : Fin 16, power18Expr 4 4 k = power18_r4_4 k := by decide +kernel
lemma power18_r4_5_eq : ∀ k : Fin 16, power18Expr 4 5 k = power18_r4_5 k := by decide +kernel
lemma power18_r4_6_eq : ∀ k : Fin 16, power18Expr 4 6 k = power18_r4_6 k := by decide +kernel
lemma power18_r4_7_eq : ∀ k : Fin 16, power18Expr 4 7 k = power18_r4_7 k := by decide +kernel
lemma power18_r4_8_eq : ∀ k : Fin 16, power18Expr 4 8 k = power18_r4_8 k := by decide +kernel
lemma power18_r4_9_eq : ∀ k : Fin 16, power18Expr 4 9 k = power18_r4_9 k := by decide +kernel
lemma power18_r4_10_eq : ∀ k : Fin 16, power18Expr 4 10 k = power18_r4_10 k := by decide +kernel
lemma power18_r4_11_eq : ∀ k : Fin 16, power18Expr 4 11 k = power18_r4_11 k := by decide +kernel
lemma power18_r4_12_eq : ∀ k : Fin 16, power18Expr 4 12 k = power18_r4_12 k := by decide +kernel
lemma power18_r4_13_eq : ∀ k : Fin 16, power18Expr 4 13 k = power18_r4_13 k := by decide +kernel
lemma power18_r4_14_eq : ∀ k : Fin 16, power18Expr 4 14 k = power18_r4_14 k := by decide +kernel
lemma power18_r4_15_eq : ∀ k : Fin 16, power18Expr 4 15 k = power18_r4_15 k := by decide +kernel
lemma power18_r4_eq (i k : Fin 16) : power18Expr 4 i k = power18_r4 i k := by
  fin_cases i
  · exact power18_r4_0_eq k
  · exact power18_r4_1_eq k
  · exact power18_r4_2_eq k
  · exact power18_r4_3_eq k
  · exact power18_r4_4_eq k
  · exact power18_r4_5_eq k
  · exact power18_r4_6_eq k
  · exact power18_r4_7_eq k
  · exact power18_r4_8_eq k
  · exact power18_r4_9_eq k
  · exact power18_r4_10_eq k
  · exact power18_r4_11_eq k
  · exact power18_r4_12_eq k
  · exact power18_r4_13_eq k
  · exact power18_r4_14_eq k
  · exact power18_r4_15_eq k
lemma power18_r5_0_eq : ∀ k : Fin 16, power18Expr 5 0 k = power18_r5_0 k := by decide +kernel
lemma power18_r5_1_eq : ∀ k : Fin 16, power18Expr 5 1 k = power18_r5_1 k := by decide +kernel
lemma power18_r5_2_eq : ∀ k : Fin 16, power18Expr 5 2 k = power18_r5_2 k := by decide +kernel
lemma power18_r5_3_eq : ∀ k : Fin 16, power18Expr 5 3 k = power18_r5_3 k := by decide +kernel
lemma power18_r5_4_eq : ∀ k : Fin 16, power18Expr 5 4 k = power18_r5_4 k := by decide +kernel
lemma power18_r5_5_eq : ∀ k : Fin 16, power18Expr 5 5 k = power18_r5_5 k := by decide +kernel
lemma power18_r5_6_eq : ∀ k : Fin 16, power18Expr 5 6 k = power18_r5_6 k := by decide +kernel
lemma power18_r5_7_eq : ∀ k : Fin 16, power18Expr 5 7 k = power18_r5_7 k := by decide +kernel
lemma power18_r5_8_eq : ∀ k : Fin 16, power18Expr 5 8 k = power18_r5_8 k := by decide +kernel
lemma power18_r5_9_eq : ∀ k : Fin 16, power18Expr 5 9 k = power18_r5_9 k := by decide +kernel
lemma power18_r5_10_eq : ∀ k : Fin 16, power18Expr 5 10 k = power18_r5_10 k := by decide +kernel
lemma power18_r5_11_eq : ∀ k : Fin 16, power18Expr 5 11 k = power18_r5_11 k := by decide +kernel
lemma power18_r5_12_eq : ∀ k : Fin 16, power18Expr 5 12 k = power18_r5_12 k := by decide +kernel
lemma power18_r5_13_eq : ∀ k : Fin 16, power18Expr 5 13 k = power18_r5_13 k := by decide +kernel
lemma power18_r5_14_eq : ∀ k : Fin 16, power18Expr 5 14 k = power18_r5_14 k := by decide +kernel
lemma power18_r5_15_eq : ∀ k : Fin 16, power18Expr 5 15 k = power18_r5_15 k := by decide +kernel
lemma power18_r5_eq (i k : Fin 16) : power18Expr 5 i k = power18_r5 i k := by
  fin_cases i
  · exact power18_r5_0_eq k
  · exact power18_r5_1_eq k
  · exact power18_r5_2_eq k
  · exact power18_r5_3_eq k
  · exact power18_r5_4_eq k
  · exact power18_r5_5_eq k
  · exact power18_r5_6_eq k
  · exact power18_r5_7_eq k
  · exact power18_r5_8_eq k
  · exact power18_r5_9_eq k
  · exact power18_r5_10_eq k
  · exact power18_r5_11_eq k
  · exact power18_r5_12_eq k
  · exact power18_r5_13_eq k
  · exact power18_r5_14_eq k
  · exact power18_r5_15_eq k
lemma power18_eq (j : Fin 6) (i k : Fin 16) : power18Expr j i k = power18 j i k := by
  fin_cases j
  · exact power18_r0_eq i k
  · exact power18_r1_eq i k
  · exact power18_r2_eq i k
  · exact power18_r3_eq i k
  · exact power18_r4_eq i k
  · exact power18_r5_eq i k
lemma power18_contains (j : Fin 6) (i k : Fin 16) :
    (power18 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(18:ℕ))) := by
  rw [← power18_eq]
  unfold power18Expr
  convert exp_direct_step_e (power17_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power19_r0_0_eq : ∀ k : Fin 16, power19Expr 0 0 k = power19_r0_0 k := by decide +kernel
lemma power19_r0_1_eq : ∀ k : Fin 16, power19Expr 0 1 k = power19_r0_1 k := by decide +kernel
lemma power19_r0_2_eq : ∀ k : Fin 16, power19Expr 0 2 k = power19_r0_2 k := by decide +kernel
lemma power19_r0_3_eq : ∀ k : Fin 16, power19Expr 0 3 k = power19_r0_3 k := by decide +kernel
lemma power19_r0_4_eq : ∀ k : Fin 16, power19Expr 0 4 k = power19_r0_4 k := by decide +kernel
lemma power19_r0_5_eq : ∀ k : Fin 16, power19Expr 0 5 k = power19_r0_5 k := by decide +kernel
lemma power19_r0_6_eq : ∀ k : Fin 16, power19Expr 0 6 k = power19_r0_6 k := by decide +kernel
lemma power19_r0_7_eq : ∀ k : Fin 16, power19Expr 0 7 k = power19_r0_7 k := by decide +kernel
lemma power19_r0_8_eq : ∀ k : Fin 16, power19Expr 0 8 k = power19_r0_8 k := by decide +kernel
lemma power19_r0_9_eq : ∀ k : Fin 16, power19Expr 0 9 k = power19_r0_9 k := by decide +kernel
lemma power19_r0_10_eq : ∀ k : Fin 16, power19Expr 0 10 k = power19_r0_10 k := by decide +kernel
lemma power19_r0_11_eq : ∀ k : Fin 16, power19Expr 0 11 k = power19_r0_11 k := by decide +kernel
lemma power19_r0_12_eq : ∀ k : Fin 16, power19Expr 0 12 k = power19_r0_12 k := by decide +kernel
lemma power19_r0_13_eq : ∀ k : Fin 16, power19Expr 0 13 k = power19_r0_13 k := by decide +kernel
lemma power19_r0_14_eq : ∀ k : Fin 16, power19Expr 0 14 k = power19_r0_14 k := by decide +kernel
lemma power19_r0_15_eq : ∀ k : Fin 16, power19Expr 0 15 k = power19_r0_15 k := by decide +kernel
lemma power19_r0_eq (i k : Fin 16) : power19Expr 0 i k = power19_r0 i k := by
  fin_cases i
  · exact power19_r0_0_eq k
  · exact power19_r0_1_eq k
  · exact power19_r0_2_eq k
  · exact power19_r0_3_eq k
  · exact power19_r0_4_eq k
  · exact power19_r0_5_eq k
  · exact power19_r0_6_eq k
  · exact power19_r0_7_eq k
  · exact power19_r0_8_eq k
  · exact power19_r0_9_eq k
  · exact power19_r0_10_eq k
  · exact power19_r0_11_eq k
  · exact power19_r0_12_eq k
  · exact power19_r0_13_eq k
  · exact power19_r0_14_eq k
  · exact power19_r0_15_eq k
lemma power19_r1_0_eq : ∀ k : Fin 16, power19Expr 1 0 k = power19_r1_0 k := by decide +kernel
lemma power19_r1_1_eq : ∀ k : Fin 16, power19Expr 1 1 k = power19_r1_1 k := by decide +kernel
lemma power19_r1_2_eq : ∀ k : Fin 16, power19Expr 1 2 k = power19_r1_2 k := by decide +kernel
lemma power19_r1_3_eq : ∀ k : Fin 16, power19Expr 1 3 k = power19_r1_3 k := by decide +kernel
lemma power19_r1_4_eq : ∀ k : Fin 16, power19Expr 1 4 k = power19_r1_4 k := by decide +kernel
lemma power19_r1_5_eq : ∀ k : Fin 16, power19Expr 1 5 k = power19_r1_5 k := by decide +kernel
lemma power19_r1_6_eq : ∀ k : Fin 16, power19Expr 1 6 k = power19_r1_6 k := by decide +kernel
lemma power19_r1_7_eq : ∀ k : Fin 16, power19Expr 1 7 k = power19_r1_7 k := by decide +kernel
lemma power19_r1_8_eq : ∀ k : Fin 16, power19Expr 1 8 k = power19_r1_8 k := by decide +kernel
lemma power19_r1_9_eq : ∀ k : Fin 16, power19Expr 1 9 k = power19_r1_9 k := by decide +kernel
lemma power19_r1_10_eq : ∀ k : Fin 16, power19Expr 1 10 k = power19_r1_10 k := by decide +kernel
lemma power19_r1_11_eq : ∀ k : Fin 16, power19Expr 1 11 k = power19_r1_11 k := by decide +kernel
lemma power19_r1_12_eq : ∀ k : Fin 16, power19Expr 1 12 k = power19_r1_12 k := by decide +kernel
lemma power19_r1_13_eq : ∀ k : Fin 16, power19Expr 1 13 k = power19_r1_13 k := by decide +kernel
lemma power19_r1_14_eq : ∀ k : Fin 16, power19Expr 1 14 k = power19_r1_14 k := by decide +kernel
lemma power19_r1_15_eq : ∀ k : Fin 16, power19Expr 1 15 k = power19_r1_15 k := by decide +kernel
lemma power19_r1_eq (i k : Fin 16) : power19Expr 1 i k = power19_r1 i k := by
  fin_cases i
  · exact power19_r1_0_eq k
  · exact power19_r1_1_eq k
  · exact power19_r1_2_eq k
  · exact power19_r1_3_eq k
  · exact power19_r1_4_eq k
  · exact power19_r1_5_eq k
  · exact power19_r1_6_eq k
  · exact power19_r1_7_eq k
  · exact power19_r1_8_eq k
  · exact power19_r1_9_eq k
  · exact power19_r1_10_eq k
  · exact power19_r1_11_eq k
  · exact power19_r1_12_eq k
  · exact power19_r1_13_eq k
  · exact power19_r1_14_eq k
  · exact power19_r1_15_eq k
lemma power19_r2_0_eq : ∀ k : Fin 16, power19Expr 2 0 k = power19_r2_0 k := by decide +kernel
lemma power19_r2_1_eq : ∀ k : Fin 16, power19Expr 2 1 k = power19_r2_1 k := by decide +kernel
lemma power19_r2_2_eq : ∀ k : Fin 16, power19Expr 2 2 k = power19_r2_2 k := by decide +kernel
lemma power19_r2_3_eq : ∀ k : Fin 16, power19Expr 2 3 k = power19_r2_3 k := by decide +kernel
lemma power19_r2_4_eq : ∀ k : Fin 16, power19Expr 2 4 k = power19_r2_4 k := by decide +kernel
lemma power19_r2_5_eq : ∀ k : Fin 16, power19Expr 2 5 k = power19_r2_5 k := by decide +kernel
lemma power19_r2_6_eq : ∀ k : Fin 16, power19Expr 2 6 k = power19_r2_6 k := by decide +kernel
lemma power19_r2_7_eq : ∀ k : Fin 16, power19Expr 2 7 k = power19_r2_7 k := by decide +kernel
lemma power19_r2_8_eq : ∀ k : Fin 16, power19Expr 2 8 k = power19_r2_8 k := by decide +kernel
lemma power19_r2_9_eq : ∀ k : Fin 16, power19Expr 2 9 k = power19_r2_9 k := by decide +kernel
lemma power19_r2_10_eq : ∀ k : Fin 16, power19Expr 2 10 k = power19_r2_10 k := by decide +kernel
lemma power19_r2_11_eq : ∀ k : Fin 16, power19Expr 2 11 k = power19_r2_11 k := by decide +kernel
lemma power19_r2_12_eq : ∀ k : Fin 16, power19Expr 2 12 k = power19_r2_12 k := by decide +kernel
lemma power19_r2_13_eq : ∀ k : Fin 16, power19Expr 2 13 k = power19_r2_13 k := by decide +kernel
lemma power19_r2_14_eq : ∀ k : Fin 16, power19Expr 2 14 k = power19_r2_14 k := by decide +kernel
lemma power19_r2_15_eq : ∀ k : Fin 16, power19Expr 2 15 k = power19_r2_15 k := by decide +kernel
lemma power19_r2_eq (i k : Fin 16) : power19Expr 2 i k = power19_r2 i k := by
  fin_cases i
  · exact power19_r2_0_eq k
  · exact power19_r2_1_eq k
  · exact power19_r2_2_eq k
  · exact power19_r2_3_eq k
  · exact power19_r2_4_eq k
  · exact power19_r2_5_eq k
  · exact power19_r2_6_eq k
  · exact power19_r2_7_eq k
  · exact power19_r2_8_eq k
  · exact power19_r2_9_eq k
  · exact power19_r2_10_eq k
  · exact power19_r2_11_eq k
  · exact power19_r2_12_eq k
  · exact power19_r2_13_eq k
  · exact power19_r2_14_eq k
  · exact power19_r2_15_eq k
lemma power19_r3_0_eq : ∀ k : Fin 16, power19Expr 3 0 k = power19_r3_0 k := by decide +kernel
lemma power19_r3_1_eq : ∀ k : Fin 16, power19Expr 3 1 k = power19_r3_1 k := by decide +kernel
lemma power19_r3_2_eq : ∀ k : Fin 16, power19Expr 3 2 k = power19_r3_2 k := by decide +kernel
lemma power19_r3_3_eq : ∀ k : Fin 16, power19Expr 3 3 k = power19_r3_3 k := by decide +kernel
lemma power19_r3_4_eq : ∀ k : Fin 16, power19Expr 3 4 k = power19_r3_4 k := by decide +kernel
lemma power19_r3_5_eq : ∀ k : Fin 16, power19Expr 3 5 k = power19_r3_5 k := by decide +kernel
lemma power19_r3_6_eq : ∀ k : Fin 16, power19Expr 3 6 k = power19_r3_6 k := by decide +kernel
lemma power19_r3_7_eq : ∀ k : Fin 16, power19Expr 3 7 k = power19_r3_7 k := by decide +kernel
lemma power19_r3_8_eq : ∀ k : Fin 16, power19Expr 3 8 k = power19_r3_8 k := by decide +kernel
lemma power19_r3_9_eq : ∀ k : Fin 16, power19Expr 3 9 k = power19_r3_9 k := by decide +kernel
lemma power19_r3_10_eq : ∀ k : Fin 16, power19Expr 3 10 k = power19_r3_10 k := by decide +kernel
lemma power19_r3_11_eq : ∀ k : Fin 16, power19Expr 3 11 k = power19_r3_11 k := by decide +kernel
lemma power19_r3_12_eq : ∀ k : Fin 16, power19Expr 3 12 k = power19_r3_12 k := by decide +kernel
lemma power19_r3_13_eq : ∀ k : Fin 16, power19Expr 3 13 k = power19_r3_13 k := by decide +kernel
lemma power19_r3_14_eq : ∀ k : Fin 16, power19Expr 3 14 k = power19_r3_14 k := by decide +kernel
lemma power19_r3_15_eq : ∀ k : Fin 16, power19Expr 3 15 k = power19_r3_15 k := by decide +kernel
lemma power19_r3_eq (i k : Fin 16) : power19Expr 3 i k = power19_r3 i k := by
  fin_cases i
  · exact power19_r3_0_eq k
  · exact power19_r3_1_eq k
  · exact power19_r3_2_eq k
  · exact power19_r3_3_eq k
  · exact power19_r3_4_eq k
  · exact power19_r3_5_eq k
  · exact power19_r3_6_eq k
  · exact power19_r3_7_eq k
  · exact power19_r3_8_eq k
  · exact power19_r3_9_eq k
  · exact power19_r3_10_eq k
  · exact power19_r3_11_eq k
  · exact power19_r3_12_eq k
  · exact power19_r3_13_eq k
  · exact power19_r3_14_eq k
  · exact power19_r3_15_eq k
lemma power19_r4_0_eq : ∀ k : Fin 16, power19Expr 4 0 k = power19_r4_0 k := by decide +kernel
lemma power19_r4_1_eq : ∀ k : Fin 16, power19Expr 4 1 k = power19_r4_1 k := by decide +kernel
lemma power19_r4_2_eq : ∀ k : Fin 16, power19Expr 4 2 k = power19_r4_2 k := by decide +kernel
lemma power19_r4_3_eq : ∀ k : Fin 16, power19Expr 4 3 k = power19_r4_3 k := by decide +kernel
lemma power19_r4_4_eq : ∀ k : Fin 16, power19Expr 4 4 k = power19_r4_4 k := by decide +kernel
lemma power19_r4_5_eq : ∀ k : Fin 16, power19Expr 4 5 k = power19_r4_5 k := by decide +kernel
lemma power19_r4_6_eq : ∀ k : Fin 16, power19Expr 4 6 k = power19_r4_6 k := by decide +kernel
lemma power19_r4_7_eq : ∀ k : Fin 16, power19Expr 4 7 k = power19_r4_7 k := by decide +kernel
lemma power19_r4_8_eq : ∀ k : Fin 16, power19Expr 4 8 k = power19_r4_8 k := by decide +kernel
lemma power19_r4_9_eq : ∀ k : Fin 16, power19Expr 4 9 k = power19_r4_9 k := by decide +kernel
lemma power19_r4_10_eq : ∀ k : Fin 16, power19Expr 4 10 k = power19_r4_10 k := by decide +kernel
lemma power19_r4_11_eq : ∀ k : Fin 16, power19Expr 4 11 k = power19_r4_11 k := by decide +kernel
lemma power19_r4_12_eq : ∀ k : Fin 16, power19Expr 4 12 k = power19_r4_12 k := by decide +kernel
lemma power19_r4_13_eq : ∀ k : Fin 16, power19Expr 4 13 k = power19_r4_13 k := by decide +kernel
lemma power19_r4_14_eq : ∀ k : Fin 16, power19Expr 4 14 k = power19_r4_14 k := by decide +kernel
lemma power19_r4_15_eq : ∀ k : Fin 16, power19Expr 4 15 k = power19_r4_15 k := by decide +kernel
lemma power19_r4_eq (i k : Fin 16) : power19Expr 4 i k = power19_r4 i k := by
  fin_cases i
  · exact power19_r4_0_eq k
  · exact power19_r4_1_eq k
  · exact power19_r4_2_eq k
  · exact power19_r4_3_eq k
  · exact power19_r4_4_eq k
  · exact power19_r4_5_eq k
  · exact power19_r4_6_eq k
  · exact power19_r4_7_eq k
  · exact power19_r4_8_eq k
  · exact power19_r4_9_eq k
  · exact power19_r4_10_eq k
  · exact power19_r4_11_eq k
  · exact power19_r4_12_eq k
  · exact power19_r4_13_eq k
  · exact power19_r4_14_eq k
  · exact power19_r4_15_eq k
lemma power19_r5_0_eq : ∀ k : Fin 16, power19Expr 5 0 k = power19_r5_0 k := by decide +kernel
lemma power19_r5_1_eq : ∀ k : Fin 16, power19Expr 5 1 k = power19_r5_1 k := by decide +kernel
lemma power19_r5_2_eq : ∀ k : Fin 16, power19Expr 5 2 k = power19_r5_2 k := by decide +kernel
lemma power19_r5_3_eq : ∀ k : Fin 16, power19Expr 5 3 k = power19_r5_3 k := by decide +kernel
lemma power19_r5_4_eq : ∀ k : Fin 16, power19Expr 5 4 k = power19_r5_4 k := by decide +kernel
lemma power19_r5_5_eq : ∀ k : Fin 16, power19Expr 5 5 k = power19_r5_5 k := by decide +kernel
lemma power19_r5_6_eq : ∀ k : Fin 16, power19Expr 5 6 k = power19_r5_6 k := by decide +kernel
lemma power19_r5_7_eq : ∀ k : Fin 16, power19Expr 5 7 k = power19_r5_7 k := by decide +kernel
lemma power19_r5_8_eq : ∀ k : Fin 16, power19Expr 5 8 k = power19_r5_8 k := by decide +kernel
lemma power19_r5_9_eq : ∀ k : Fin 16, power19Expr 5 9 k = power19_r5_9 k := by decide +kernel
lemma power19_r5_10_eq : ∀ k : Fin 16, power19Expr 5 10 k = power19_r5_10 k := by decide +kernel
lemma power19_r5_11_eq : ∀ k : Fin 16, power19Expr 5 11 k = power19_r5_11 k := by decide +kernel
lemma power19_r5_12_eq : ∀ k : Fin 16, power19Expr 5 12 k = power19_r5_12 k := by decide +kernel
lemma power19_r5_13_eq : ∀ k : Fin 16, power19Expr 5 13 k = power19_r5_13 k := by decide +kernel
lemma power19_r5_14_eq : ∀ k : Fin 16, power19Expr 5 14 k = power19_r5_14 k := by decide +kernel
lemma power19_r5_15_eq : ∀ k : Fin 16, power19Expr 5 15 k = power19_r5_15 k := by decide +kernel
lemma power19_r5_eq (i k : Fin 16) : power19Expr 5 i k = power19_r5 i k := by
  fin_cases i
  · exact power19_r5_0_eq k
  · exact power19_r5_1_eq k
  · exact power19_r5_2_eq k
  · exact power19_r5_3_eq k
  · exact power19_r5_4_eq k
  · exact power19_r5_5_eq k
  · exact power19_r5_6_eq k
  · exact power19_r5_7_eq k
  · exact power19_r5_8_eq k
  · exact power19_r5_9_eq k
  · exact power19_r5_10_eq k
  · exact power19_r5_11_eq k
  · exact power19_r5_12_eq k
  · exact power19_r5_13_eq k
  · exact power19_r5_14_eq k
  · exact power19_r5_15_eq k
lemma power19_eq (j : Fin 6) (i k : Fin 16) : power19Expr j i k = power19 j i k := by
  fin_cases j
  · exact power19_r0_eq i k
  · exact power19_r1_eq i k
  · exact power19_r2_eq i k
  · exact power19_r3_eq i k
  · exact power19_r4_eq i k
  · exact power19_r5_eq i k
lemma power19_contains (j : Fin 6) (i k : Fin 16) :
    (power19 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(19:ℕ))) := by
  rw [← power19_eq]
  unfold power19Expr
  convert exp_direct_step_e (power18_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns20
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
lemma column19_1_r0_0_eq : ∀ k : Fin 16, column19_1Expr 0 0 k = column19_1_r0_0 k := by decide +kernel
lemma column19_1_r0_1_eq : ∀ k : Fin 16, column19_1Expr 0 1 k = column19_1_r0_1 k := by decide +kernel
lemma column19_1_r0_2_eq : ∀ k : Fin 16, column19_1Expr 0 2 k = column19_1_r0_2 k := by decide +kernel
lemma column19_1_r0_3_eq : ∀ k : Fin 16, column19_1Expr 0 3 k = column19_1_r0_3 k := by decide +kernel
lemma column19_1_r0_4_eq : ∀ k : Fin 16, column19_1Expr 0 4 k = column19_1_r0_4 k := by decide +kernel
lemma column19_1_r0_5_eq : ∀ k : Fin 16, column19_1Expr 0 5 k = column19_1_r0_5 k := by decide +kernel
lemma column19_1_r0_6_eq : ∀ k : Fin 16, column19_1Expr 0 6 k = column19_1_r0_6 k := by decide +kernel
lemma column19_1_r0_7_eq : ∀ k : Fin 16, column19_1Expr 0 7 k = column19_1_r0_7 k := by decide +kernel
lemma column19_1_r0_8_eq : ∀ k : Fin 16, column19_1Expr 0 8 k = column19_1_r0_8 k := by decide +kernel
lemma column19_1_r0_9_eq : ∀ k : Fin 16, column19_1Expr 0 9 k = column19_1_r0_9 k := by decide +kernel
lemma column19_1_r0_10_eq : ∀ k : Fin 16, column19_1Expr 0 10 k = column19_1_r0_10 k := by decide +kernel
lemma column19_1_r0_11_eq : ∀ k : Fin 16, column19_1Expr 0 11 k = column19_1_r0_11 k := by decide +kernel
lemma column19_1_r0_12_eq : ∀ k : Fin 16, column19_1Expr 0 12 k = column19_1_r0_12 k := by decide +kernel
lemma column19_1_r0_13_eq : ∀ k : Fin 16, column19_1Expr 0 13 k = column19_1_r0_13 k := by decide +kernel
lemma column19_1_r0_14_eq : ∀ k : Fin 16, column19_1Expr 0 14 k = column19_1_r0_14 k := by decide +kernel
lemma column19_1_r0_15_eq : ∀ k : Fin 16, column19_1Expr 0 15 k = column19_1_r0_15 k := by decide +kernel
lemma column19_1_r0_eq (i k : Fin 16) : column19_1Expr 0 i k = column19_1_r0 i k := by
  fin_cases i
  · exact column19_1_r0_0_eq k
  · exact column19_1_r0_1_eq k
  · exact column19_1_r0_2_eq k
  · exact column19_1_r0_3_eq k
  · exact column19_1_r0_4_eq k
  · exact column19_1_r0_5_eq k
  · exact column19_1_r0_6_eq k
  · exact column19_1_r0_7_eq k
  · exact column19_1_r0_8_eq k
  · exact column19_1_r0_9_eq k
  · exact column19_1_r0_10_eq k
  · exact column19_1_r0_11_eq k
  · exact column19_1_r0_12_eq k
  · exact column19_1_r0_13_eq k
  · exact column19_1_r0_14_eq k
  · exact column19_1_r0_15_eq k
lemma column19_1_r1_0_eq : ∀ k : Fin 16, column19_1Expr 1 0 k = column19_1_r1_0 k := by decide +kernel
lemma column19_1_r1_1_eq : ∀ k : Fin 16, column19_1Expr 1 1 k = column19_1_r1_1 k := by decide +kernel
lemma column19_1_r1_2_eq : ∀ k : Fin 16, column19_1Expr 1 2 k = column19_1_r1_2 k := by decide +kernel
lemma column19_1_r1_3_eq : ∀ k : Fin 16, column19_1Expr 1 3 k = column19_1_r1_3 k := by decide +kernel
lemma column19_1_r1_4_eq : ∀ k : Fin 16, column19_1Expr 1 4 k = column19_1_r1_4 k := by decide +kernel
lemma column19_1_r1_5_eq : ∀ k : Fin 16, column19_1Expr 1 5 k = column19_1_r1_5 k := by decide +kernel
lemma column19_1_r1_6_eq : ∀ k : Fin 16, column19_1Expr 1 6 k = column19_1_r1_6 k := by decide +kernel
lemma column19_1_r1_7_eq : ∀ k : Fin 16, column19_1Expr 1 7 k = column19_1_r1_7 k := by decide +kernel
lemma column19_1_r1_8_eq : ∀ k : Fin 16, column19_1Expr 1 8 k = column19_1_r1_8 k := by decide +kernel
lemma column19_1_r1_9_eq : ∀ k : Fin 16, column19_1Expr 1 9 k = column19_1_r1_9 k := by decide +kernel
lemma column19_1_r1_10_eq : ∀ k : Fin 16, column19_1Expr 1 10 k = column19_1_r1_10 k := by decide +kernel
lemma column19_1_r1_11_eq : ∀ k : Fin 16, column19_1Expr 1 11 k = column19_1_r1_11 k := by decide +kernel
lemma column19_1_r1_12_eq : ∀ k : Fin 16, column19_1Expr 1 12 k = column19_1_r1_12 k := by decide +kernel
lemma column19_1_r1_13_eq : ∀ k : Fin 16, column19_1Expr 1 13 k = column19_1_r1_13 k := by decide +kernel
lemma column19_1_r1_14_eq : ∀ k : Fin 16, column19_1Expr 1 14 k = column19_1_r1_14 k := by decide +kernel
lemma column19_1_r1_15_eq : ∀ k : Fin 16, column19_1Expr 1 15 k = column19_1_r1_15 k := by decide +kernel
lemma column19_1_r1_eq (i k : Fin 16) : column19_1Expr 1 i k = column19_1_r1 i k := by
  fin_cases i
  · exact column19_1_r1_0_eq k
  · exact column19_1_r1_1_eq k
  · exact column19_1_r1_2_eq k
  · exact column19_1_r1_3_eq k
  · exact column19_1_r1_4_eq k
  · exact column19_1_r1_5_eq k
  · exact column19_1_r1_6_eq k
  · exact column19_1_r1_7_eq k
  · exact column19_1_r1_8_eq k
  · exact column19_1_r1_9_eq k
  · exact column19_1_r1_10_eq k
  · exact column19_1_r1_11_eq k
  · exact column19_1_r1_12_eq k
  · exact column19_1_r1_13_eq k
  · exact column19_1_r1_14_eq k
  · exact column19_1_r1_15_eq k
lemma column19_1_r2_0_eq : ∀ k : Fin 16, column19_1Expr 2 0 k = column19_1_r2_0 k := by decide +kernel
lemma column19_1_r2_1_eq : ∀ k : Fin 16, column19_1Expr 2 1 k = column19_1_r2_1 k := by decide +kernel
lemma column19_1_r2_2_eq : ∀ k : Fin 16, column19_1Expr 2 2 k = column19_1_r2_2 k := by decide +kernel
lemma column19_1_r2_3_eq : ∀ k : Fin 16, column19_1Expr 2 3 k = column19_1_r2_3 k := by decide +kernel
lemma column19_1_r2_4_eq : ∀ k : Fin 16, column19_1Expr 2 4 k = column19_1_r2_4 k := by decide +kernel
lemma column19_1_r2_5_eq : ∀ k : Fin 16, column19_1Expr 2 5 k = column19_1_r2_5 k := by decide +kernel
lemma column19_1_r2_6_eq : ∀ k : Fin 16, column19_1Expr 2 6 k = column19_1_r2_6 k := by decide +kernel
lemma column19_1_r2_7_eq : ∀ k : Fin 16, column19_1Expr 2 7 k = column19_1_r2_7 k := by decide +kernel
lemma column19_1_r2_8_eq : ∀ k : Fin 16, column19_1Expr 2 8 k = column19_1_r2_8 k := by decide +kernel
lemma column19_1_r2_9_eq : ∀ k : Fin 16, column19_1Expr 2 9 k = column19_1_r2_9 k := by decide +kernel
lemma column19_1_r2_10_eq : ∀ k : Fin 16, column19_1Expr 2 10 k = column19_1_r2_10 k := by decide +kernel
lemma column19_1_r2_11_eq : ∀ k : Fin 16, column19_1Expr 2 11 k = column19_1_r2_11 k := by decide +kernel
lemma column19_1_r2_12_eq : ∀ k : Fin 16, column19_1Expr 2 12 k = column19_1_r2_12 k := by decide +kernel
lemma column19_1_r2_13_eq : ∀ k : Fin 16, column19_1Expr 2 13 k = column19_1_r2_13 k := by decide +kernel
lemma column19_1_r2_14_eq : ∀ k : Fin 16, column19_1Expr 2 14 k = column19_1_r2_14 k := by decide +kernel
lemma column19_1_r2_15_eq : ∀ k : Fin 16, column19_1Expr 2 15 k = column19_1_r2_15 k := by decide +kernel
lemma column19_1_r2_eq (i k : Fin 16) : column19_1Expr 2 i k = column19_1_r2 i k := by
  fin_cases i
  · exact column19_1_r2_0_eq k
  · exact column19_1_r2_1_eq k
  · exact column19_1_r2_2_eq k
  · exact column19_1_r2_3_eq k
  · exact column19_1_r2_4_eq k
  · exact column19_1_r2_5_eq k
  · exact column19_1_r2_6_eq k
  · exact column19_1_r2_7_eq k
  · exact column19_1_r2_8_eq k
  · exact column19_1_r2_9_eq k
  · exact column19_1_r2_10_eq k
  · exact column19_1_r2_11_eq k
  · exact column19_1_r2_12_eq k
  · exact column19_1_r2_13_eq k
  · exact column19_1_r2_14_eq k
  · exact column19_1_r2_15_eq k
lemma column19_1_r3_0_eq : ∀ k : Fin 16, column19_1Expr 3 0 k = column19_1_r3_0 k := by decide +kernel
lemma column19_1_r3_1_eq : ∀ k : Fin 16, column19_1Expr 3 1 k = column19_1_r3_1 k := by decide +kernel
lemma column19_1_r3_2_eq : ∀ k : Fin 16, column19_1Expr 3 2 k = column19_1_r3_2 k := by decide +kernel
lemma column19_1_r3_3_eq : ∀ k : Fin 16, column19_1Expr 3 3 k = column19_1_r3_3 k := by decide +kernel
lemma column19_1_r3_4_eq : ∀ k : Fin 16, column19_1Expr 3 4 k = column19_1_r3_4 k := by decide +kernel
lemma column19_1_r3_5_eq : ∀ k : Fin 16, column19_1Expr 3 5 k = column19_1_r3_5 k := by decide +kernel
lemma column19_1_r3_6_eq : ∀ k : Fin 16, column19_1Expr 3 6 k = column19_1_r3_6 k := by decide +kernel
lemma column19_1_r3_7_eq : ∀ k : Fin 16, column19_1Expr 3 7 k = column19_1_r3_7 k := by decide +kernel
lemma column19_1_r3_8_eq : ∀ k : Fin 16, column19_1Expr 3 8 k = column19_1_r3_8 k := by decide +kernel
lemma column19_1_r3_9_eq : ∀ k : Fin 16, column19_1Expr 3 9 k = column19_1_r3_9 k := by decide +kernel
lemma column19_1_r3_10_eq : ∀ k : Fin 16, column19_1Expr 3 10 k = column19_1_r3_10 k := by decide +kernel
lemma column19_1_r3_11_eq : ∀ k : Fin 16, column19_1Expr 3 11 k = column19_1_r3_11 k := by decide +kernel
lemma column19_1_r3_12_eq : ∀ k : Fin 16, column19_1Expr 3 12 k = column19_1_r3_12 k := by decide +kernel
lemma column19_1_r3_13_eq : ∀ k : Fin 16, column19_1Expr 3 13 k = column19_1_r3_13 k := by decide +kernel
lemma column19_1_r3_14_eq : ∀ k : Fin 16, column19_1Expr 3 14 k = column19_1_r3_14 k := by decide +kernel
lemma column19_1_r3_15_eq : ∀ k : Fin 16, column19_1Expr 3 15 k = column19_1_r3_15 k := by decide +kernel
lemma column19_1_r3_eq (i k : Fin 16) : column19_1Expr 3 i k = column19_1_r3 i k := by
  fin_cases i
  · exact column19_1_r3_0_eq k
  · exact column19_1_r3_1_eq k
  · exact column19_1_r3_2_eq k
  · exact column19_1_r3_3_eq k
  · exact column19_1_r3_4_eq k
  · exact column19_1_r3_5_eq k
  · exact column19_1_r3_6_eq k
  · exact column19_1_r3_7_eq k
  · exact column19_1_r3_8_eq k
  · exact column19_1_r3_9_eq k
  · exact column19_1_r3_10_eq k
  · exact column19_1_r3_11_eq k
  · exact column19_1_r3_12_eq k
  · exact column19_1_r3_13_eq k
  · exact column19_1_r3_14_eq k
  · exact column19_1_r3_15_eq k
lemma column19_1_r4_0_eq : ∀ k : Fin 16, column19_1Expr 4 0 k = column19_1_r4_0 k := by decide +kernel
lemma column19_1_r4_1_eq : ∀ k : Fin 16, column19_1Expr 4 1 k = column19_1_r4_1 k := by decide +kernel
lemma column19_1_r4_2_eq : ∀ k : Fin 16, column19_1Expr 4 2 k = column19_1_r4_2 k := by decide +kernel
lemma column19_1_r4_3_eq : ∀ k : Fin 16, column19_1Expr 4 3 k = column19_1_r4_3 k := by decide +kernel
lemma column19_1_r4_4_eq : ∀ k : Fin 16, column19_1Expr 4 4 k = column19_1_r4_4 k := by decide +kernel
lemma column19_1_r4_5_eq : ∀ k : Fin 16, column19_1Expr 4 5 k = column19_1_r4_5 k := by decide +kernel
lemma column19_1_r4_6_eq : ∀ k : Fin 16, column19_1Expr 4 6 k = column19_1_r4_6 k := by decide +kernel
lemma column19_1_r4_7_eq : ∀ k : Fin 16, column19_1Expr 4 7 k = column19_1_r4_7 k := by decide +kernel
lemma column19_1_r4_8_eq : ∀ k : Fin 16, column19_1Expr 4 8 k = column19_1_r4_8 k := by decide +kernel
lemma column19_1_r4_9_eq : ∀ k : Fin 16, column19_1Expr 4 9 k = column19_1_r4_9 k := by decide +kernel
lemma column19_1_r4_10_eq : ∀ k : Fin 16, column19_1Expr 4 10 k = column19_1_r4_10 k := by decide +kernel
lemma column19_1_r4_11_eq : ∀ k : Fin 16, column19_1Expr 4 11 k = column19_1_r4_11 k := by decide +kernel
lemma column19_1_r4_12_eq : ∀ k : Fin 16, column19_1Expr 4 12 k = column19_1_r4_12 k := by decide +kernel
lemma column19_1_r4_13_eq : ∀ k : Fin 16, column19_1Expr 4 13 k = column19_1_r4_13 k := by decide +kernel
lemma column19_1_r4_14_eq : ∀ k : Fin 16, column19_1Expr 4 14 k = column19_1_r4_14 k := by decide +kernel
lemma column19_1_r4_15_eq : ∀ k : Fin 16, column19_1Expr 4 15 k = column19_1_r4_15 k := by decide +kernel
lemma column19_1_r4_eq (i k : Fin 16) : column19_1Expr 4 i k = column19_1_r4 i k := by
  fin_cases i
  · exact column19_1_r4_0_eq k
  · exact column19_1_r4_1_eq k
  · exact column19_1_r4_2_eq k
  · exact column19_1_r4_3_eq k
  · exact column19_1_r4_4_eq k
  · exact column19_1_r4_5_eq k
  · exact column19_1_r4_6_eq k
  · exact column19_1_r4_7_eq k
  · exact column19_1_r4_8_eq k
  · exact column19_1_r4_9_eq k
  · exact column19_1_r4_10_eq k
  · exact column19_1_r4_11_eq k
  · exact column19_1_r4_12_eq k
  · exact column19_1_r4_13_eq k
  · exact column19_1_r4_14_eq k
  · exact column19_1_r4_15_eq k
lemma column19_1_r5_0_eq : ∀ k : Fin 16, column19_1Expr 5 0 k = column19_1_r5_0 k := by decide +kernel
lemma column19_1_r5_1_eq : ∀ k : Fin 16, column19_1Expr 5 1 k = column19_1_r5_1 k := by decide +kernel
lemma column19_1_r5_2_eq : ∀ k : Fin 16, column19_1Expr 5 2 k = column19_1_r5_2 k := by decide +kernel
lemma column19_1_r5_3_eq : ∀ k : Fin 16, column19_1Expr 5 3 k = column19_1_r5_3 k := by decide +kernel
lemma column19_1_r5_4_eq : ∀ k : Fin 16, column19_1Expr 5 4 k = column19_1_r5_4 k := by decide +kernel
lemma column19_1_r5_5_eq : ∀ k : Fin 16, column19_1Expr 5 5 k = column19_1_r5_5 k := by decide +kernel
lemma column19_1_r5_6_eq : ∀ k : Fin 16, column19_1Expr 5 6 k = column19_1_r5_6 k := by decide +kernel
lemma column19_1_r5_7_eq : ∀ k : Fin 16, column19_1Expr 5 7 k = column19_1_r5_7 k := by decide +kernel
lemma column19_1_r5_8_eq : ∀ k : Fin 16, column19_1Expr 5 8 k = column19_1_r5_8 k := by decide +kernel
lemma column19_1_r5_9_eq : ∀ k : Fin 16, column19_1Expr 5 9 k = column19_1_r5_9 k := by decide +kernel
lemma column19_1_r5_10_eq : ∀ k : Fin 16, column19_1Expr 5 10 k = column19_1_r5_10 k := by decide +kernel
lemma column19_1_r5_11_eq : ∀ k : Fin 16, column19_1Expr 5 11 k = column19_1_r5_11 k := by decide +kernel
lemma column19_1_r5_12_eq : ∀ k : Fin 16, column19_1Expr 5 12 k = column19_1_r5_12 k := by decide +kernel
lemma column19_1_r5_13_eq : ∀ k : Fin 16, column19_1Expr 5 13 k = column19_1_r5_13 k := by decide +kernel
lemma column19_1_r5_14_eq : ∀ k : Fin 16, column19_1Expr 5 14 k = column19_1_r5_14 k := by decide +kernel
lemma column19_1_r5_15_eq : ∀ k : Fin 16, column19_1Expr 5 15 k = column19_1_r5_15 k := by decide +kernel
lemma column19_1_r5_eq (i k : Fin 16) : column19_1Expr 5 i k = column19_1_r5 i k := by
  fin_cases i
  · exact column19_1_r5_0_eq k
  · exact column19_1_r5_1_eq k
  · exact column19_1_r5_2_eq k
  · exact column19_1_r5_3_eq k
  · exact column19_1_r5_4_eq k
  · exact column19_1_r5_5_eq k
  · exact column19_1_r5_6_eq k
  · exact column19_1_r5_7_eq k
  · exact column19_1_r5_8_eq k
  · exact column19_1_r5_9_eq k
  · exact column19_1_r5_10_eq k
  · exact column19_1_r5_11_eq k
  · exact column19_1_r5_12_eq k
  · exact column19_1_r5_13_eq k
  · exact column19_1_r5_14_eq k
  · exact column19_1_r5_15_eq k
lemma column19_1_eq (j : Fin 6) (i k : Fin 16) : column19_1Expr j i k = column19_1 j i k := by
  fin_cases j
  · exact column19_1_r0_eq i k
  · exact column19_1_r1_eq i k
  · exact column19_1_r2_eq i k
  · exact column19_1_r3_eq i k
  · exact column19_1_r4_eq i k
  · exact column19_1_r5_eq i k
lemma column19_1_contains_e_oai (j : Fin 6) (i k : Fin 16) :
    (column19_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction true 19 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column19_1_eq,basisFunction_wave,← mul_assoc]
  unfold column19_1Expr
  apply CBox.contains_mul_e
  · rw [← waveAmplitude_mod true 19 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp7_1_contains j i k
  · exact power19_contains j i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.column19_1_contains_e_oai := @OAI.SharpPlanar.CachedData.column19_1_contains_e_oai
