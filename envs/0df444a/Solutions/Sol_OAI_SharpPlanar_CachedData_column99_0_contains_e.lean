-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.column99_0_contains_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T00:33:17.130077+00:00
-- url     : https://prove2.me/submissions/1ca910b0-1b64-4599-9521-42eab3696417
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_CachedData_power96_contains_e
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
lemma amp3_00_0_eq : ∀ k : Fin 16, amp3_0Expr 0 0 k = amp3_00_0 k := by decide +kernel
lemma amp3_00_1_eq : ∀ k : Fin 16, amp3_0Expr 0 1 k = amp3_00_1 k := by decide +kernel
lemma amp3_00_2_eq : ∀ k : Fin 16, amp3_0Expr 0 2 k = amp3_00_2 k := by decide +kernel
lemma amp3_00_3_eq : ∀ k : Fin 16, amp3_0Expr 0 3 k = amp3_00_3 k := by decide +kernel
lemma amp3_00_4_eq : ∀ k : Fin 16, amp3_0Expr 0 4 k = amp3_00_4 k := by decide +kernel
lemma amp3_00_5_eq : ∀ k : Fin 16, amp3_0Expr 0 5 k = amp3_00_5 k := by decide +kernel
lemma amp3_00_6_eq : ∀ k : Fin 16, amp3_0Expr 0 6 k = amp3_00_6 k := by decide +kernel
lemma amp3_00_7_eq : ∀ k : Fin 16, amp3_0Expr 0 7 k = amp3_00_7 k := by decide +kernel
lemma amp3_00_8_eq : ∀ k : Fin 16, amp3_0Expr 0 8 k = amp3_00_8 k := by decide +kernel
lemma amp3_00_9_eq : ∀ k : Fin 16, amp3_0Expr 0 9 k = amp3_00_9 k := by decide +kernel
lemma amp3_00_10_eq : ∀ k : Fin 16, amp3_0Expr 0 10 k = amp3_00_10 k := by decide +kernel
lemma amp3_00_11_eq : ∀ k : Fin 16, amp3_0Expr 0 11 k = amp3_00_11 k := by decide +kernel
lemma amp3_00_12_eq : ∀ k : Fin 16, amp3_0Expr 0 12 k = amp3_00_12 k := by decide +kernel
lemma amp3_00_13_eq : ∀ k : Fin 16, amp3_0Expr 0 13 k = amp3_00_13 k := by decide +kernel
lemma amp3_00_14_eq : ∀ k : Fin 16, amp3_0Expr 0 14 k = amp3_00_14 k := by decide +kernel
lemma amp3_00_15_eq : ∀ k : Fin 16, amp3_0Expr 0 15 k = amp3_00_15 k := by decide +kernel
lemma amp3_00_eq (i k : Fin 16) : amp3_0Expr 0 i k = amp3_00 i k := by
  fin_cases i
  · exact amp3_00_0_eq k
  · exact amp3_00_1_eq k
  · exact amp3_00_2_eq k
  · exact amp3_00_3_eq k
  · exact amp3_00_4_eq k
  · exact amp3_00_5_eq k
  · exact amp3_00_6_eq k
  · exact amp3_00_7_eq k
  · exact amp3_00_8_eq k
  · exact amp3_00_9_eq k
  · exact amp3_00_10_eq k
  · exact amp3_00_11_eq k
  · exact amp3_00_12_eq k
  · exact amp3_00_13_eq k
  · exact amp3_00_14_eq k
  · exact amp3_00_15_eq k
lemma amp3_01_0_eq : ∀ k : Fin 16, amp3_0Expr 1 0 k = amp3_01_0 k := by decide +kernel
lemma amp3_01_1_eq : ∀ k : Fin 16, amp3_0Expr 1 1 k = amp3_01_1 k := by decide +kernel
lemma amp3_01_2_eq : ∀ k : Fin 16, amp3_0Expr 1 2 k = amp3_01_2 k := by decide +kernel
lemma amp3_01_3_eq : ∀ k : Fin 16, amp3_0Expr 1 3 k = amp3_01_3 k := by decide +kernel
lemma amp3_01_4_eq : ∀ k : Fin 16, amp3_0Expr 1 4 k = amp3_01_4 k := by decide +kernel
lemma amp3_01_5_eq : ∀ k : Fin 16, amp3_0Expr 1 5 k = amp3_01_5 k := by decide +kernel
lemma amp3_01_6_eq : ∀ k : Fin 16, amp3_0Expr 1 6 k = amp3_01_6 k := by decide +kernel
lemma amp3_01_7_eq : ∀ k : Fin 16, amp3_0Expr 1 7 k = amp3_01_7 k := by decide +kernel
lemma amp3_01_8_eq : ∀ k : Fin 16, amp3_0Expr 1 8 k = amp3_01_8 k := by decide +kernel
lemma amp3_01_9_eq : ∀ k : Fin 16, amp3_0Expr 1 9 k = amp3_01_9 k := by decide +kernel
lemma amp3_01_10_eq : ∀ k : Fin 16, amp3_0Expr 1 10 k = amp3_01_10 k := by decide +kernel
lemma amp3_01_11_eq : ∀ k : Fin 16, amp3_0Expr 1 11 k = amp3_01_11 k := by decide +kernel
lemma amp3_01_12_eq : ∀ k : Fin 16, amp3_0Expr 1 12 k = amp3_01_12 k := by decide +kernel
lemma amp3_01_13_eq : ∀ k : Fin 16, amp3_0Expr 1 13 k = amp3_01_13 k := by decide +kernel
lemma amp3_01_14_eq : ∀ k : Fin 16, amp3_0Expr 1 14 k = amp3_01_14 k := by decide +kernel
lemma amp3_01_15_eq : ∀ k : Fin 16, amp3_0Expr 1 15 k = amp3_01_15 k := by decide +kernel
lemma amp3_01_eq (i k : Fin 16) : amp3_0Expr 1 i k = amp3_01 i k := by
  fin_cases i
  · exact amp3_01_0_eq k
  · exact amp3_01_1_eq k
  · exact amp3_01_2_eq k
  · exact amp3_01_3_eq k
  · exact amp3_01_4_eq k
  · exact amp3_01_5_eq k
  · exact amp3_01_6_eq k
  · exact amp3_01_7_eq k
  · exact amp3_01_8_eq k
  · exact amp3_01_9_eq k
  · exact amp3_01_10_eq k
  · exact amp3_01_11_eq k
  · exact amp3_01_12_eq k
  · exact amp3_01_13_eq k
  · exact amp3_01_14_eq k
  · exact amp3_01_15_eq k
lemma amp3_02_0_eq : ∀ k : Fin 16, amp3_0Expr 2 0 k = amp3_02_0 k := by decide +kernel
lemma amp3_02_1_eq : ∀ k : Fin 16, amp3_0Expr 2 1 k = amp3_02_1 k := by decide +kernel
lemma amp3_02_2_eq : ∀ k : Fin 16, amp3_0Expr 2 2 k = amp3_02_2 k := by decide +kernel
lemma amp3_02_3_eq : ∀ k : Fin 16, amp3_0Expr 2 3 k = amp3_02_3 k := by decide +kernel
lemma amp3_02_4_eq : ∀ k : Fin 16, amp3_0Expr 2 4 k = amp3_02_4 k := by decide +kernel
lemma amp3_02_5_eq : ∀ k : Fin 16, amp3_0Expr 2 5 k = amp3_02_5 k := by decide +kernel
lemma amp3_02_6_eq : ∀ k : Fin 16, amp3_0Expr 2 6 k = amp3_02_6 k := by decide +kernel
lemma amp3_02_7_eq : ∀ k : Fin 16, amp3_0Expr 2 7 k = amp3_02_7 k := by decide +kernel
lemma amp3_02_8_eq : ∀ k : Fin 16, amp3_0Expr 2 8 k = amp3_02_8 k := by decide +kernel
lemma amp3_02_9_eq : ∀ k : Fin 16, amp3_0Expr 2 9 k = amp3_02_9 k := by decide +kernel
lemma amp3_02_10_eq : ∀ k : Fin 16, amp3_0Expr 2 10 k = amp3_02_10 k := by decide +kernel
lemma amp3_02_11_eq : ∀ k : Fin 16, amp3_0Expr 2 11 k = amp3_02_11 k := by decide +kernel
lemma amp3_02_12_eq : ∀ k : Fin 16, amp3_0Expr 2 12 k = amp3_02_12 k := by decide +kernel
lemma amp3_02_13_eq : ∀ k : Fin 16, amp3_0Expr 2 13 k = amp3_02_13 k := by decide +kernel
lemma amp3_02_14_eq : ∀ k : Fin 16, amp3_0Expr 2 14 k = amp3_02_14 k := by decide +kernel
lemma amp3_02_15_eq : ∀ k : Fin 16, amp3_0Expr 2 15 k = amp3_02_15 k := by decide +kernel
lemma amp3_02_eq (i k : Fin 16) : amp3_0Expr 2 i k = amp3_02 i k := by
  fin_cases i
  · exact amp3_02_0_eq k
  · exact amp3_02_1_eq k
  · exact amp3_02_2_eq k
  · exact amp3_02_3_eq k
  · exact amp3_02_4_eq k
  · exact amp3_02_5_eq k
  · exact amp3_02_6_eq k
  · exact amp3_02_7_eq k
  · exact amp3_02_8_eq k
  · exact amp3_02_9_eq k
  · exact amp3_02_10_eq k
  · exact amp3_02_11_eq k
  · exact amp3_02_12_eq k
  · exact amp3_02_13_eq k
  · exact amp3_02_14_eq k
  · exact amp3_02_15_eq k
lemma amp3_03_0_eq : ∀ k : Fin 16, amp3_0Expr 3 0 k = amp3_03_0 k := by decide +kernel
lemma amp3_03_1_eq : ∀ k : Fin 16, amp3_0Expr 3 1 k = amp3_03_1 k := by decide +kernel
lemma amp3_03_2_eq : ∀ k : Fin 16, amp3_0Expr 3 2 k = amp3_03_2 k := by decide +kernel
lemma amp3_03_3_eq : ∀ k : Fin 16, amp3_0Expr 3 3 k = amp3_03_3 k := by decide +kernel
lemma amp3_03_4_eq : ∀ k : Fin 16, amp3_0Expr 3 4 k = amp3_03_4 k := by decide +kernel
lemma amp3_03_5_eq : ∀ k : Fin 16, amp3_0Expr 3 5 k = amp3_03_5 k := by decide +kernel
lemma amp3_03_6_eq : ∀ k : Fin 16, amp3_0Expr 3 6 k = amp3_03_6 k := by decide +kernel
lemma amp3_03_7_eq : ∀ k : Fin 16, amp3_0Expr 3 7 k = amp3_03_7 k := by decide +kernel
lemma amp3_03_8_eq : ∀ k : Fin 16, amp3_0Expr 3 8 k = amp3_03_8 k := by decide +kernel
lemma amp3_03_9_eq : ∀ k : Fin 16, amp3_0Expr 3 9 k = amp3_03_9 k := by decide +kernel
lemma amp3_03_10_eq : ∀ k : Fin 16, amp3_0Expr 3 10 k = amp3_03_10 k := by decide +kernel
lemma amp3_03_11_eq : ∀ k : Fin 16, amp3_0Expr 3 11 k = amp3_03_11 k := by decide +kernel
lemma amp3_03_12_eq : ∀ k : Fin 16, amp3_0Expr 3 12 k = amp3_03_12 k := by decide +kernel
lemma amp3_03_13_eq : ∀ k : Fin 16, amp3_0Expr 3 13 k = amp3_03_13 k := by decide +kernel
lemma amp3_03_14_eq : ∀ k : Fin 16, amp3_0Expr 3 14 k = amp3_03_14 k := by decide +kernel
lemma amp3_03_15_eq : ∀ k : Fin 16, amp3_0Expr 3 15 k = amp3_03_15 k := by decide +kernel
lemma amp3_03_eq (i k : Fin 16) : amp3_0Expr 3 i k = amp3_03 i k := by
  fin_cases i
  · exact amp3_03_0_eq k
  · exact amp3_03_1_eq k
  · exact amp3_03_2_eq k
  · exact amp3_03_3_eq k
  · exact amp3_03_4_eq k
  · exact amp3_03_5_eq k
  · exact amp3_03_6_eq k
  · exact amp3_03_7_eq k
  · exact amp3_03_8_eq k
  · exact amp3_03_9_eq k
  · exact amp3_03_10_eq k
  · exact amp3_03_11_eq k
  · exact amp3_03_12_eq k
  · exact amp3_03_13_eq k
  · exact amp3_03_14_eq k
  · exact amp3_03_15_eq k
lemma amp3_04_0_eq : ∀ k : Fin 16, amp3_0Expr 4 0 k = amp3_04_0 k := by decide +kernel
lemma amp3_04_1_eq : ∀ k : Fin 16, amp3_0Expr 4 1 k = amp3_04_1 k := by decide +kernel
lemma amp3_04_2_eq : ∀ k : Fin 16, amp3_0Expr 4 2 k = amp3_04_2 k := by decide +kernel
lemma amp3_04_3_eq : ∀ k : Fin 16, amp3_0Expr 4 3 k = amp3_04_3 k := by decide +kernel
lemma amp3_04_4_eq : ∀ k : Fin 16, amp3_0Expr 4 4 k = amp3_04_4 k := by decide +kernel
lemma amp3_04_5_eq : ∀ k : Fin 16, amp3_0Expr 4 5 k = amp3_04_5 k := by decide +kernel
lemma amp3_04_6_eq : ∀ k : Fin 16, amp3_0Expr 4 6 k = amp3_04_6 k := by decide +kernel
lemma amp3_04_7_eq : ∀ k : Fin 16, amp3_0Expr 4 7 k = amp3_04_7 k := by decide +kernel
lemma amp3_04_8_eq : ∀ k : Fin 16, amp3_0Expr 4 8 k = amp3_04_8 k := by decide +kernel
lemma amp3_04_9_eq : ∀ k : Fin 16, amp3_0Expr 4 9 k = amp3_04_9 k := by decide +kernel
lemma amp3_04_10_eq : ∀ k : Fin 16, amp3_0Expr 4 10 k = amp3_04_10 k := by decide +kernel
lemma amp3_04_11_eq : ∀ k : Fin 16, amp3_0Expr 4 11 k = amp3_04_11 k := by decide +kernel
lemma amp3_04_12_eq : ∀ k : Fin 16, amp3_0Expr 4 12 k = amp3_04_12 k := by decide +kernel
lemma amp3_04_13_eq : ∀ k : Fin 16, amp3_0Expr 4 13 k = amp3_04_13 k := by decide +kernel
lemma amp3_04_14_eq : ∀ k : Fin 16, amp3_0Expr 4 14 k = amp3_04_14 k := by decide +kernel
lemma amp3_04_15_eq : ∀ k : Fin 16, amp3_0Expr 4 15 k = amp3_04_15 k := by decide +kernel
lemma amp3_04_eq (i k : Fin 16) : amp3_0Expr 4 i k = amp3_04 i k := by
  fin_cases i
  · exact amp3_04_0_eq k
  · exact amp3_04_1_eq k
  · exact amp3_04_2_eq k
  · exact amp3_04_3_eq k
  · exact amp3_04_4_eq k
  · exact amp3_04_5_eq k
  · exact amp3_04_6_eq k
  · exact amp3_04_7_eq k
  · exact amp3_04_8_eq k
  · exact amp3_04_9_eq k
  · exact amp3_04_10_eq k
  · exact amp3_04_11_eq k
  · exact amp3_04_12_eq k
  · exact amp3_04_13_eq k
  · exact amp3_04_14_eq k
  · exact amp3_04_15_eq k
lemma amp3_05_0_eq : ∀ k : Fin 16, amp3_0Expr 5 0 k = amp3_05_0 k := by decide +kernel
lemma amp3_05_1_eq : ∀ k : Fin 16, amp3_0Expr 5 1 k = amp3_05_1 k := by decide +kernel
lemma amp3_05_2_eq : ∀ k : Fin 16, amp3_0Expr 5 2 k = amp3_05_2 k := by decide +kernel
lemma amp3_05_3_eq : ∀ k : Fin 16, amp3_0Expr 5 3 k = amp3_05_3 k := by decide +kernel
lemma amp3_05_4_eq : ∀ k : Fin 16, amp3_0Expr 5 4 k = amp3_05_4 k := by decide +kernel
lemma amp3_05_5_eq : ∀ k : Fin 16, amp3_0Expr 5 5 k = amp3_05_5 k := by decide +kernel
lemma amp3_05_6_eq : ∀ k : Fin 16, amp3_0Expr 5 6 k = amp3_05_6 k := by decide +kernel
lemma amp3_05_7_eq : ∀ k : Fin 16, amp3_0Expr 5 7 k = amp3_05_7 k := by decide +kernel
lemma amp3_05_8_eq : ∀ k : Fin 16, amp3_0Expr 5 8 k = amp3_05_8 k := by decide +kernel
lemma amp3_05_9_eq : ∀ k : Fin 16, amp3_0Expr 5 9 k = amp3_05_9 k := by decide +kernel
lemma amp3_05_10_eq : ∀ k : Fin 16, amp3_0Expr 5 10 k = amp3_05_10 k := by decide +kernel
lemma amp3_05_11_eq : ∀ k : Fin 16, amp3_0Expr 5 11 k = amp3_05_11 k := by decide +kernel
lemma amp3_05_12_eq : ∀ k : Fin 16, amp3_0Expr 5 12 k = amp3_05_12 k := by decide +kernel
lemma amp3_05_13_eq : ∀ k : Fin 16, amp3_0Expr 5 13 k = amp3_05_13 k := by decide +kernel
lemma amp3_05_14_eq : ∀ k : Fin 16, amp3_0Expr 5 14 k = amp3_05_14 k := by decide +kernel
lemma amp3_05_15_eq : ∀ k : Fin 16, amp3_0Expr 5 15 k = amp3_05_15 k := by decide +kernel
lemma amp3_05_eq (i k : Fin 16) : amp3_0Expr 5 i k = amp3_05 i k := by
  fin_cases i
  · exact amp3_05_0_eq k
  · exact amp3_05_1_eq k
  · exact amp3_05_2_eq k
  · exact amp3_05_3_eq k
  · exact amp3_05_4_eq k
  · exact amp3_05_5_eq k
  · exact amp3_05_6_eq k
  · exact amp3_05_7_eq k
  · exact amp3_05_8_eq k
  · exact amp3_05_9_eq k
  · exact amp3_05_10_eq k
  · exact amp3_05_11_eq k
  · exact amp3_05_12_eq k
  · exact amp3_05_13_eq k
  · exact amp3_05_14_eq k
  · exact amp3_05_15_eq k
lemma amp3_0_eq (j : Fin 6) (i k : Fin 16) : amp3_0Expr j i k = amp3_0 j i k := by
  fin_cases j
  · exact amp3_00_eq i k
  · exact amp3_01_eq i k
  · exact amp3_02_eq i k
  · exact amp3_03_eq i k
  · exact amp3_04_eq i k
  · exact amp3_05_eq i k
lemma amp3_0_contains (j : Fin 6) (i k : Fin 16) :
    (amp3_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*waveAmplitude false 3 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← amp3_0_eq]
  exact CBox.contains_mul_e (rcast_contains_e (weightRows_contains_e i k))
    (waveAmplitudeBox_contains_e (gridRows_contains_e j i k) (aLookup_contains 3 j) (bLookup_contains 3 j) false)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers100
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
lemma power97_r0_0_eq : ∀ k : Fin 16, power97Expr 0 0 k = power97_r0_0 k := by decide +kernel
lemma power97_r0_1_eq : ∀ k : Fin 16, power97Expr 0 1 k = power97_r0_1 k := by decide +kernel
lemma power97_r0_2_eq : ∀ k : Fin 16, power97Expr 0 2 k = power97_r0_2 k := by decide +kernel
lemma power97_r0_3_eq : ∀ k : Fin 16, power97Expr 0 3 k = power97_r0_3 k := by decide +kernel
lemma power97_r0_4_eq : ∀ k : Fin 16, power97Expr 0 4 k = power97_r0_4 k := by decide +kernel
lemma power97_r0_5_eq : ∀ k : Fin 16, power97Expr 0 5 k = power97_r0_5 k := by decide +kernel
lemma power97_r0_6_eq : ∀ k : Fin 16, power97Expr 0 6 k = power97_r0_6 k := by decide +kernel
lemma power97_r0_7_eq : ∀ k : Fin 16, power97Expr 0 7 k = power97_r0_7 k := by decide +kernel
lemma power97_r0_8_eq : ∀ k : Fin 16, power97Expr 0 8 k = power97_r0_8 k := by decide +kernel
lemma power97_r0_9_eq : ∀ k : Fin 16, power97Expr 0 9 k = power97_r0_9 k := by decide +kernel
lemma power97_r0_10_eq : ∀ k : Fin 16, power97Expr 0 10 k = power97_r0_10 k := by decide +kernel
lemma power97_r0_11_eq : ∀ k : Fin 16, power97Expr 0 11 k = power97_r0_11 k := by decide +kernel
lemma power97_r0_12_eq : ∀ k : Fin 16, power97Expr 0 12 k = power97_r0_12 k := by decide +kernel
lemma power97_r0_13_eq : ∀ k : Fin 16, power97Expr 0 13 k = power97_r0_13 k := by decide +kernel
lemma power97_r0_14_eq : ∀ k : Fin 16, power97Expr 0 14 k = power97_r0_14 k := by decide +kernel
lemma power97_r0_15_eq : ∀ k : Fin 16, power97Expr 0 15 k = power97_r0_15 k := by decide +kernel
lemma power97_r0_eq (i k : Fin 16) : power97Expr 0 i k = power97_r0 i k := by
  fin_cases i
  · exact power97_r0_0_eq k
  · exact power97_r0_1_eq k
  · exact power97_r0_2_eq k
  · exact power97_r0_3_eq k
  · exact power97_r0_4_eq k
  · exact power97_r0_5_eq k
  · exact power97_r0_6_eq k
  · exact power97_r0_7_eq k
  · exact power97_r0_8_eq k
  · exact power97_r0_9_eq k
  · exact power97_r0_10_eq k
  · exact power97_r0_11_eq k
  · exact power97_r0_12_eq k
  · exact power97_r0_13_eq k
  · exact power97_r0_14_eq k
  · exact power97_r0_15_eq k
lemma power97_r1_0_eq : ∀ k : Fin 16, power97Expr 1 0 k = power97_r1_0 k := by decide +kernel
lemma power97_r1_1_eq : ∀ k : Fin 16, power97Expr 1 1 k = power97_r1_1 k := by decide +kernel
lemma power97_r1_2_eq : ∀ k : Fin 16, power97Expr 1 2 k = power97_r1_2 k := by decide +kernel
lemma power97_r1_3_eq : ∀ k : Fin 16, power97Expr 1 3 k = power97_r1_3 k := by decide +kernel
lemma power97_r1_4_eq : ∀ k : Fin 16, power97Expr 1 4 k = power97_r1_4 k := by decide +kernel
lemma power97_r1_5_eq : ∀ k : Fin 16, power97Expr 1 5 k = power97_r1_5 k := by decide +kernel
lemma power97_r1_6_eq : ∀ k : Fin 16, power97Expr 1 6 k = power97_r1_6 k := by decide +kernel
lemma power97_r1_7_eq : ∀ k : Fin 16, power97Expr 1 7 k = power97_r1_7 k := by decide +kernel
lemma power97_r1_8_eq : ∀ k : Fin 16, power97Expr 1 8 k = power97_r1_8 k := by decide +kernel
lemma power97_r1_9_eq : ∀ k : Fin 16, power97Expr 1 9 k = power97_r1_9 k := by decide +kernel
lemma power97_r1_10_eq : ∀ k : Fin 16, power97Expr 1 10 k = power97_r1_10 k := by decide +kernel
lemma power97_r1_11_eq : ∀ k : Fin 16, power97Expr 1 11 k = power97_r1_11 k := by decide +kernel
lemma power97_r1_12_eq : ∀ k : Fin 16, power97Expr 1 12 k = power97_r1_12 k := by decide +kernel
lemma power97_r1_13_eq : ∀ k : Fin 16, power97Expr 1 13 k = power97_r1_13 k := by decide +kernel
lemma power97_r1_14_eq : ∀ k : Fin 16, power97Expr 1 14 k = power97_r1_14 k := by decide +kernel
lemma power97_r1_15_eq : ∀ k : Fin 16, power97Expr 1 15 k = power97_r1_15 k := by decide +kernel
lemma power97_r1_eq (i k : Fin 16) : power97Expr 1 i k = power97_r1 i k := by
  fin_cases i
  · exact power97_r1_0_eq k
  · exact power97_r1_1_eq k
  · exact power97_r1_2_eq k
  · exact power97_r1_3_eq k
  · exact power97_r1_4_eq k
  · exact power97_r1_5_eq k
  · exact power97_r1_6_eq k
  · exact power97_r1_7_eq k
  · exact power97_r1_8_eq k
  · exact power97_r1_9_eq k
  · exact power97_r1_10_eq k
  · exact power97_r1_11_eq k
  · exact power97_r1_12_eq k
  · exact power97_r1_13_eq k
  · exact power97_r1_14_eq k
  · exact power97_r1_15_eq k
lemma power97_r2_0_eq : ∀ k : Fin 16, power97Expr 2 0 k = power97_r2_0 k := by decide +kernel
lemma power97_r2_1_eq : ∀ k : Fin 16, power97Expr 2 1 k = power97_r2_1 k := by decide +kernel
lemma power97_r2_2_eq : ∀ k : Fin 16, power97Expr 2 2 k = power97_r2_2 k := by decide +kernel
lemma power97_r2_3_eq : ∀ k : Fin 16, power97Expr 2 3 k = power97_r2_3 k := by decide +kernel
lemma power97_r2_4_eq : ∀ k : Fin 16, power97Expr 2 4 k = power97_r2_4 k := by decide +kernel
lemma power97_r2_5_eq : ∀ k : Fin 16, power97Expr 2 5 k = power97_r2_5 k := by decide +kernel
lemma power97_r2_6_eq : ∀ k : Fin 16, power97Expr 2 6 k = power97_r2_6 k := by decide +kernel
lemma power97_r2_7_eq : ∀ k : Fin 16, power97Expr 2 7 k = power97_r2_7 k := by decide +kernel
lemma power97_r2_8_eq : ∀ k : Fin 16, power97Expr 2 8 k = power97_r2_8 k := by decide +kernel
lemma power97_r2_9_eq : ∀ k : Fin 16, power97Expr 2 9 k = power97_r2_9 k := by decide +kernel
lemma power97_r2_10_eq : ∀ k : Fin 16, power97Expr 2 10 k = power97_r2_10 k := by decide +kernel
lemma power97_r2_11_eq : ∀ k : Fin 16, power97Expr 2 11 k = power97_r2_11 k := by decide +kernel
lemma power97_r2_12_eq : ∀ k : Fin 16, power97Expr 2 12 k = power97_r2_12 k := by decide +kernel
lemma power97_r2_13_eq : ∀ k : Fin 16, power97Expr 2 13 k = power97_r2_13 k := by decide +kernel
lemma power97_r2_14_eq : ∀ k : Fin 16, power97Expr 2 14 k = power97_r2_14 k := by decide +kernel
lemma power97_r2_15_eq : ∀ k : Fin 16, power97Expr 2 15 k = power97_r2_15 k := by decide +kernel
lemma power97_r2_eq (i k : Fin 16) : power97Expr 2 i k = power97_r2 i k := by
  fin_cases i
  · exact power97_r2_0_eq k
  · exact power97_r2_1_eq k
  · exact power97_r2_2_eq k
  · exact power97_r2_3_eq k
  · exact power97_r2_4_eq k
  · exact power97_r2_5_eq k
  · exact power97_r2_6_eq k
  · exact power97_r2_7_eq k
  · exact power97_r2_8_eq k
  · exact power97_r2_9_eq k
  · exact power97_r2_10_eq k
  · exact power97_r2_11_eq k
  · exact power97_r2_12_eq k
  · exact power97_r2_13_eq k
  · exact power97_r2_14_eq k
  · exact power97_r2_15_eq k
lemma power97_r3_0_eq : ∀ k : Fin 16, power97Expr 3 0 k = power97_r3_0 k := by decide +kernel
lemma power97_r3_1_eq : ∀ k : Fin 16, power97Expr 3 1 k = power97_r3_1 k := by decide +kernel
lemma power97_r3_2_eq : ∀ k : Fin 16, power97Expr 3 2 k = power97_r3_2 k := by decide +kernel
lemma power97_r3_3_eq : ∀ k : Fin 16, power97Expr 3 3 k = power97_r3_3 k := by decide +kernel
lemma power97_r3_4_eq : ∀ k : Fin 16, power97Expr 3 4 k = power97_r3_4 k := by decide +kernel
lemma power97_r3_5_eq : ∀ k : Fin 16, power97Expr 3 5 k = power97_r3_5 k := by decide +kernel
lemma power97_r3_6_eq : ∀ k : Fin 16, power97Expr 3 6 k = power97_r3_6 k := by decide +kernel
lemma power97_r3_7_eq : ∀ k : Fin 16, power97Expr 3 7 k = power97_r3_7 k := by decide +kernel
lemma power97_r3_8_eq : ∀ k : Fin 16, power97Expr 3 8 k = power97_r3_8 k := by decide +kernel
lemma power97_r3_9_eq : ∀ k : Fin 16, power97Expr 3 9 k = power97_r3_9 k := by decide +kernel
lemma power97_r3_10_eq : ∀ k : Fin 16, power97Expr 3 10 k = power97_r3_10 k := by decide +kernel
lemma power97_r3_11_eq : ∀ k : Fin 16, power97Expr 3 11 k = power97_r3_11 k := by decide +kernel
lemma power97_r3_12_eq : ∀ k : Fin 16, power97Expr 3 12 k = power97_r3_12 k := by decide +kernel
lemma power97_r3_13_eq : ∀ k : Fin 16, power97Expr 3 13 k = power97_r3_13 k := by decide +kernel
lemma power97_r3_14_eq : ∀ k : Fin 16, power97Expr 3 14 k = power97_r3_14 k := by decide +kernel
lemma power97_r3_15_eq : ∀ k : Fin 16, power97Expr 3 15 k = power97_r3_15 k := by decide +kernel
lemma power97_r3_eq (i k : Fin 16) : power97Expr 3 i k = power97_r3 i k := by
  fin_cases i
  · exact power97_r3_0_eq k
  · exact power97_r3_1_eq k
  · exact power97_r3_2_eq k
  · exact power97_r3_3_eq k
  · exact power97_r3_4_eq k
  · exact power97_r3_5_eq k
  · exact power97_r3_6_eq k
  · exact power97_r3_7_eq k
  · exact power97_r3_8_eq k
  · exact power97_r3_9_eq k
  · exact power97_r3_10_eq k
  · exact power97_r3_11_eq k
  · exact power97_r3_12_eq k
  · exact power97_r3_13_eq k
  · exact power97_r3_14_eq k
  · exact power97_r3_15_eq k
lemma power97_r4_0_eq : ∀ k : Fin 16, power97Expr 4 0 k = power97_r4_0 k := by decide +kernel
lemma power97_r4_1_eq : ∀ k : Fin 16, power97Expr 4 1 k = power97_r4_1 k := by decide +kernel
lemma power97_r4_2_eq : ∀ k : Fin 16, power97Expr 4 2 k = power97_r4_2 k := by decide +kernel
lemma power97_r4_3_eq : ∀ k : Fin 16, power97Expr 4 3 k = power97_r4_3 k := by decide +kernel
lemma power97_r4_4_eq : ∀ k : Fin 16, power97Expr 4 4 k = power97_r4_4 k := by decide +kernel
lemma power97_r4_5_eq : ∀ k : Fin 16, power97Expr 4 5 k = power97_r4_5 k := by decide +kernel
lemma power97_r4_6_eq : ∀ k : Fin 16, power97Expr 4 6 k = power97_r4_6 k := by decide +kernel
lemma power97_r4_7_eq : ∀ k : Fin 16, power97Expr 4 7 k = power97_r4_7 k := by decide +kernel
lemma power97_r4_8_eq : ∀ k : Fin 16, power97Expr 4 8 k = power97_r4_8 k := by decide +kernel
lemma power97_r4_9_eq : ∀ k : Fin 16, power97Expr 4 9 k = power97_r4_9 k := by decide +kernel
lemma power97_r4_10_eq : ∀ k : Fin 16, power97Expr 4 10 k = power97_r4_10 k := by decide +kernel
lemma power97_r4_11_eq : ∀ k : Fin 16, power97Expr 4 11 k = power97_r4_11 k := by decide +kernel
lemma power97_r4_12_eq : ∀ k : Fin 16, power97Expr 4 12 k = power97_r4_12 k := by decide +kernel
lemma power97_r4_13_eq : ∀ k : Fin 16, power97Expr 4 13 k = power97_r4_13 k := by decide +kernel
lemma power97_r4_14_eq : ∀ k : Fin 16, power97Expr 4 14 k = power97_r4_14 k := by decide +kernel
lemma power97_r4_15_eq : ∀ k : Fin 16, power97Expr 4 15 k = power97_r4_15 k := by decide +kernel
lemma power97_r4_eq (i k : Fin 16) : power97Expr 4 i k = power97_r4 i k := by
  fin_cases i
  · exact power97_r4_0_eq k
  · exact power97_r4_1_eq k
  · exact power97_r4_2_eq k
  · exact power97_r4_3_eq k
  · exact power97_r4_4_eq k
  · exact power97_r4_5_eq k
  · exact power97_r4_6_eq k
  · exact power97_r4_7_eq k
  · exact power97_r4_8_eq k
  · exact power97_r4_9_eq k
  · exact power97_r4_10_eq k
  · exact power97_r4_11_eq k
  · exact power97_r4_12_eq k
  · exact power97_r4_13_eq k
  · exact power97_r4_14_eq k
  · exact power97_r4_15_eq k
lemma power97_r5_0_eq : ∀ k : Fin 16, power97Expr 5 0 k = power97_r5_0 k := by decide +kernel
lemma power97_r5_1_eq : ∀ k : Fin 16, power97Expr 5 1 k = power97_r5_1 k := by decide +kernel
lemma power97_r5_2_eq : ∀ k : Fin 16, power97Expr 5 2 k = power97_r5_2 k := by decide +kernel
lemma power97_r5_3_eq : ∀ k : Fin 16, power97Expr 5 3 k = power97_r5_3 k := by decide +kernel
lemma power97_r5_4_eq : ∀ k : Fin 16, power97Expr 5 4 k = power97_r5_4 k := by decide +kernel
lemma power97_r5_5_eq : ∀ k : Fin 16, power97Expr 5 5 k = power97_r5_5 k := by decide +kernel
lemma power97_r5_6_eq : ∀ k : Fin 16, power97Expr 5 6 k = power97_r5_6 k := by decide +kernel
lemma power97_r5_7_eq : ∀ k : Fin 16, power97Expr 5 7 k = power97_r5_7 k := by decide +kernel
lemma power97_r5_8_eq : ∀ k : Fin 16, power97Expr 5 8 k = power97_r5_8 k := by decide +kernel
lemma power97_r5_9_eq : ∀ k : Fin 16, power97Expr 5 9 k = power97_r5_9 k := by decide +kernel
lemma power97_r5_10_eq : ∀ k : Fin 16, power97Expr 5 10 k = power97_r5_10 k := by decide +kernel
lemma power97_r5_11_eq : ∀ k : Fin 16, power97Expr 5 11 k = power97_r5_11 k := by decide +kernel
lemma power97_r5_12_eq : ∀ k : Fin 16, power97Expr 5 12 k = power97_r5_12 k := by decide +kernel
lemma power97_r5_13_eq : ∀ k : Fin 16, power97Expr 5 13 k = power97_r5_13 k := by decide +kernel
lemma power97_r5_14_eq : ∀ k : Fin 16, power97Expr 5 14 k = power97_r5_14 k := by decide +kernel
lemma power97_r5_15_eq : ∀ k : Fin 16, power97Expr 5 15 k = power97_r5_15 k := by decide +kernel
lemma power97_r5_eq (i k : Fin 16) : power97Expr 5 i k = power97_r5 i k := by
  fin_cases i
  · exact power97_r5_0_eq k
  · exact power97_r5_1_eq k
  · exact power97_r5_2_eq k
  · exact power97_r5_3_eq k
  · exact power97_r5_4_eq k
  · exact power97_r5_5_eq k
  · exact power97_r5_6_eq k
  · exact power97_r5_7_eq k
  · exact power97_r5_8_eq k
  · exact power97_r5_9_eq k
  · exact power97_r5_10_eq k
  · exact power97_r5_11_eq k
  · exact power97_r5_12_eq k
  · exact power97_r5_13_eq k
  · exact power97_r5_14_eq k
  · exact power97_r5_15_eq k
lemma power97_eq (j : Fin 6) (i k : Fin 16) : power97Expr j i k = power97 j i k := by
  fin_cases j
  · exact power97_r0_eq i k
  · exact power97_r1_eq i k
  · exact power97_r2_eq i k
  · exact power97_r3_eq i k
  · exact power97_r4_eq i k
  · exact power97_r5_eq i k
lemma power97_contains (j : Fin 6) (i k : Fin 16) :
    (power97 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(97:ℕ))) := by
  rw [← power97_eq]
  unfold power97Expr
  convert exp_direct_step_e (power96_contains_e j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power98_r0_0_eq : ∀ k : Fin 16, power98Expr 0 0 k = power98_r0_0 k := by decide +kernel
lemma power98_r0_1_eq : ∀ k : Fin 16, power98Expr 0 1 k = power98_r0_1 k := by decide +kernel
lemma power98_r0_2_eq : ∀ k : Fin 16, power98Expr 0 2 k = power98_r0_2 k := by decide +kernel
lemma power98_r0_3_eq : ∀ k : Fin 16, power98Expr 0 3 k = power98_r0_3 k := by decide +kernel
lemma power98_r0_4_eq : ∀ k : Fin 16, power98Expr 0 4 k = power98_r0_4 k := by decide +kernel
lemma power98_r0_5_eq : ∀ k : Fin 16, power98Expr 0 5 k = power98_r0_5 k := by decide +kernel
lemma power98_r0_6_eq : ∀ k : Fin 16, power98Expr 0 6 k = power98_r0_6 k := by decide +kernel
lemma power98_r0_7_eq : ∀ k : Fin 16, power98Expr 0 7 k = power98_r0_7 k := by decide +kernel
lemma power98_r0_8_eq : ∀ k : Fin 16, power98Expr 0 8 k = power98_r0_8 k := by decide +kernel
lemma power98_r0_9_eq : ∀ k : Fin 16, power98Expr 0 9 k = power98_r0_9 k := by decide +kernel
lemma power98_r0_10_eq : ∀ k : Fin 16, power98Expr 0 10 k = power98_r0_10 k := by decide +kernel
lemma power98_r0_11_eq : ∀ k : Fin 16, power98Expr 0 11 k = power98_r0_11 k := by decide +kernel
lemma power98_r0_12_eq : ∀ k : Fin 16, power98Expr 0 12 k = power98_r0_12 k := by decide +kernel
lemma power98_r0_13_eq : ∀ k : Fin 16, power98Expr 0 13 k = power98_r0_13 k := by decide +kernel
lemma power98_r0_14_eq : ∀ k : Fin 16, power98Expr 0 14 k = power98_r0_14 k := by decide +kernel
lemma power98_r0_15_eq : ∀ k : Fin 16, power98Expr 0 15 k = power98_r0_15 k := by decide +kernel
lemma power98_r0_eq (i k : Fin 16) : power98Expr 0 i k = power98_r0 i k := by
  fin_cases i
  · exact power98_r0_0_eq k
  · exact power98_r0_1_eq k
  · exact power98_r0_2_eq k
  · exact power98_r0_3_eq k
  · exact power98_r0_4_eq k
  · exact power98_r0_5_eq k
  · exact power98_r0_6_eq k
  · exact power98_r0_7_eq k
  · exact power98_r0_8_eq k
  · exact power98_r0_9_eq k
  · exact power98_r0_10_eq k
  · exact power98_r0_11_eq k
  · exact power98_r0_12_eq k
  · exact power98_r0_13_eq k
  · exact power98_r0_14_eq k
  · exact power98_r0_15_eq k
lemma power98_r1_0_eq : ∀ k : Fin 16, power98Expr 1 0 k = power98_r1_0 k := by decide +kernel
lemma power98_r1_1_eq : ∀ k : Fin 16, power98Expr 1 1 k = power98_r1_1 k := by decide +kernel
lemma power98_r1_2_eq : ∀ k : Fin 16, power98Expr 1 2 k = power98_r1_2 k := by decide +kernel
lemma power98_r1_3_eq : ∀ k : Fin 16, power98Expr 1 3 k = power98_r1_3 k := by decide +kernel
lemma power98_r1_4_eq : ∀ k : Fin 16, power98Expr 1 4 k = power98_r1_4 k := by decide +kernel
lemma power98_r1_5_eq : ∀ k : Fin 16, power98Expr 1 5 k = power98_r1_5 k := by decide +kernel
lemma power98_r1_6_eq : ∀ k : Fin 16, power98Expr 1 6 k = power98_r1_6 k := by decide +kernel
lemma power98_r1_7_eq : ∀ k : Fin 16, power98Expr 1 7 k = power98_r1_7 k := by decide +kernel
lemma power98_r1_8_eq : ∀ k : Fin 16, power98Expr 1 8 k = power98_r1_8 k := by decide +kernel
lemma power98_r1_9_eq : ∀ k : Fin 16, power98Expr 1 9 k = power98_r1_9 k := by decide +kernel
lemma power98_r1_10_eq : ∀ k : Fin 16, power98Expr 1 10 k = power98_r1_10 k := by decide +kernel
lemma power98_r1_11_eq : ∀ k : Fin 16, power98Expr 1 11 k = power98_r1_11 k := by decide +kernel
lemma power98_r1_12_eq : ∀ k : Fin 16, power98Expr 1 12 k = power98_r1_12 k := by decide +kernel
lemma power98_r1_13_eq : ∀ k : Fin 16, power98Expr 1 13 k = power98_r1_13 k := by decide +kernel
lemma power98_r1_14_eq : ∀ k : Fin 16, power98Expr 1 14 k = power98_r1_14 k := by decide +kernel
lemma power98_r1_15_eq : ∀ k : Fin 16, power98Expr 1 15 k = power98_r1_15 k := by decide +kernel
lemma power98_r1_eq (i k : Fin 16) : power98Expr 1 i k = power98_r1 i k := by
  fin_cases i
  · exact power98_r1_0_eq k
  · exact power98_r1_1_eq k
  · exact power98_r1_2_eq k
  · exact power98_r1_3_eq k
  · exact power98_r1_4_eq k
  · exact power98_r1_5_eq k
  · exact power98_r1_6_eq k
  · exact power98_r1_7_eq k
  · exact power98_r1_8_eq k
  · exact power98_r1_9_eq k
  · exact power98_r1_10_eq k
  · exact power98_r1_11_eq k
  · exact power98_r1_12_eq k
  · exact power98_r1_13_eq k
  · exact power98_r1_14_eq k
  · exact power98_r1_15_eq k
lemma power98_r2_0_eq : ∀ k : Fin 16, power98Expr 2 0 k = power98_r2_0 k := by decide +kernel
lemma power98_r2_1_eq : ∀ k : Fin 16, power98Expr 2 1 k = power98_r2_1 k := by decide +kernel
lemma power98_r2_2_eq : ∀ k : Fin 16, power98Expr 2 2 k = power98_r2_2 k := by decide +kernel
lemma power98_r2_3_eq : ∀ k : Fin 16, power98Expr 2 3 k = power98_r2_3 k := by decide +kernel
lemma power98_r2_4_eq : ∀ k : Fin 16, power98Expr 2 4 k = power98_r2_4 k := by decide +kernel
lemma power98_r2_5_eq : ∀ k : Fin 16, power98Expr 2 5 k = power98_r2_5 k := by decide +kernel
lemma power98_r2_6_eq : ∀ k : Fin 16, power98Expr 2 6 k = power98_r2_6 k := by decide +kernel
lemma power98_r2_7_eq : ∀ k : Fin 16, power98Expr 2 7 k = power98_r2_7 k := by decide +kernel
lemma power98_r2_8_eq : ∀ k : Fin 16, power98Expr 2 8 k = power98_r2_8 k := by decide +kernel
lemma power98_r2_9_eq : ∀ k : Fin 16, power98Expr 2 9 k = power98_r2_9 k := by decide +kernel
lemma power98_r2_10_eq : ∀ k : Fin 16, power98Expr 2 10 k = power98_r2_10 k := by decide +kernel
lemma power98_r2_11_eq : ∀ k : Fin 16, power98Expr 2 11 k = power98_r2_11 k := by decide +kernel
lemma power98_r2_12_eq : ∀ k : Fin 16, power98Expr 2 12 k = power98_r2_12 k := by decide +kernel
lemma power98_r2_13_eq : ∀ k : Fin 16, power98Expr 2 13 k = power98_r2_13 k := by decide +kernel
lemma power98_r2_14_eq : ∀ k : Fin 16, power98Expr 2 14 k = power98_r2_14 k := by decide +kernel
lemma power98_r2_15_eq : ∀ k : Fin 16, power98Expr 2 15 k = power98_r2_15 k := by decide +kernel
lemma power98_r2_eq (i k : Fin 16) : power98Expr 2 i k = power98_r2 i k := by
  fin_cases i
  · exact power98_r2_0_eq k
  · exact power98_r2_1_eq k
  · exact power98_r2_2_eq k
  · exact power98_r2_3_eq k
  · exact power98_r2_4_eq k
  · exact power98_r2_5_eq k
  · exact power98_r2_6_eq k
  · exact power98_r2_7_eq k
  · exact power98_r2_8_eq k
  · exact power98_r2_9_eq k
  · exact power98_r2_10_eq k
  · exact power98_r2_11_eq k
  · exact power98_r2_12_eq k
  · exact power98_r2_13_eq k
  · exact power98_r2_14_eq k
  · exact power98_r2_15_eq k
lemma power98_r3_0_eq : ∀ k : Fin 16, power98Expr 3 0 k = power98_r3_0 k := by decide +kernel
lemma power98_r3_1_eq : ∀ k : Fin 16, power98Expr 3 1 k = power98_r3_1 k := by decide +kernel
lemma power98_r3_2_eq : ∀ k : Fin 16, power98Expr 3 2 k = power98_r3_2 k := by decide +kernel
lemma power98_r3_3_eq : ∀ k : Fin 16, power98Expr 3 3 k = power98_r3_3 k := by decide +kernel
lemma power98_r3_4_eq : ∀ k : Fin 16, power98Expr 3 4 k = power98_r3_4 k := by decide +kernel
lemma power98_r3_5_eq : ∀ k : Fin 16, power98Expr 3 5 k = power98_r3_5 k := by decide +kernel
lemma power98_r3_6_eq : ∀ k : Fin 16, power98Expr 3 6 k = power98_r3_6 k := by decide +kernel
lemma power98_r3_7_eq : ∀ k : Fin 16, power98Expr 3 7 k = power98_r3_7 k := by decide +kernel
lemma power98_r3_8_eq : ∀ k : Fin 16, power98Expr 3 8 k = power98_r3_8 k := by decide +kernel
lemma power98_r3_9_eq : ∀ k : Fin 16, power98Expr 3 9 k = power98_r3_9 k := by decide +kernel
lemma power98_r3_10_eq : ∀ k : Fin 16, power98Expr 3 10 k = power98_r3_10 k := by decide +kernel
lemma power98_r3_11_eq : ∀ k : Fin 16, power98Expr 3 11 k = power98_r3_11 k := by decide +kernel
lemma power98_r3_12_eq : ∀ k : Fin 16, power98Expr 3 12 k = power98_r3_12 k := by decide +kernel
lemma power98_r3_13_eq : ∀ k : Fin 16, power98Expr 3 13 k = power98_r3_13 k := by decide +kernel
lemma power98_r3_14_eq : ∀ k : Fin 16, power98Expr 3 14 k = power98_r3_14 k := by decide +kernel
lemma power98_r3_15_eq : ∀ k : Fin 16, power98Expr 3 15 k = power98_r3_15 k := by decide +kernel
lemma power98_r3_eq (i k : Fin 16) : power98Expr 3 i k = power98_r3 i k := by
  fin_cases i
  · exact power98_r3_0_eq k
  · exact power98_r3_1_eq k
  · exact power98_r3_2_eq k
  · exact power98_r3_3_eq k
  · exact power98_r3_4_eq k
  · exact power98_r3_5_eq k
  · exact power98_r3_6_eq k
  · exact power98_r3_7_eq k
  · exact power98_r3_8_eq k
  · exact power98_r3_9_eq k
  · exact power98_r3_10_eq k
  · exact power98_r3_11_eq k
  · exact power98_r3_12_eq k
  · exact power98_r3_13_eq k
  · exact power98_r3_14_eq k
  · exact power98_r3_15_eq k
lemma power98_r4_0_eq : ∀ k : Fin 16, power98Expr 4 0 k = power98_r4_0 k := by decide +kernel
lemma power98_r4_1_eq : ∀ k : Fin 16, power98Expr 4 1 k = power98_r4_1 k := by decide +kernel
lemma power98_r4_2_eq : ∀ k : Fin 16, power98Expr 4 2 k = power98_r4_2 k := by decide +kernel
lemma power98_r4_3_eq : ∀ k : Fin 16, power98Expr 4 3 k = power98_r4_3 k := by decide +kernel
lemma power98_r4_4_eq : ∀ k : Fin 16, power98Expr 4 4 k = power98_r4_4 k := by decide +kernel
lemma power98_r4_5_eq : ∀ k : Fin 16, power98Expr 4 5 k = power98_r4_5 k := by decide +kernel
lemma power98_r4_6_eq : ∀ k : Fin 16, power98Expr 4 6 k = power98_r4_6 k := by decide +kernel
lemma power98_r4_7_eq : ∀ k : Fin 16, power98Expr 4 7 k = power98_r4_7 k := by decide +kernel
lemma power98_r4_8_eq : ∀ k : Fin 16, power98Expr 4 8 k = power98_r4_8 k := by decide +kernel
lemma power98_r4_9_eq : ∀ k : Fin 16, power98Expr 4 9 k = power98_r4_9 k := by decide +kernel
lemma power98_r4_10_eq : ∀ k : Fin 16, power98Expr 4 10 k = power98_r4_10 k := by decide +kernel
lemma power98_r4_11_eq : ∀ k : Fin 16, power98Expr 4 11 k = power98_r4_11 k := by decide +kernel
lemma power98_r4_12_eq : ∀ k : Fin 16, power98Expr 4 12 k = power98_r4_12 k := by decide +kernel
lemma power98_r4_13_eq : ∀ k : Fin 16, power98Expr 4 13 k = power98_r4_13 k := by decide +kernel
lemma power98_r4_14_eq : ∀ k : Fin 16, power98Expr 4 14 k = power98_r4_14 k := by decide +kernel
lemma power98_r4_15_eq : ∀ k : Fin 16, power98Expr 4 15 k = power98_r4_15 k := by decide +kernel
lemma power98_r4_eq (i k : Fin 16) : power98Expr 4 i k = power98_r4 i k := by
  fin_cases i
  · exact power98_r4_0_eq k
  · exact power98_r4_1_eq k
  · exact power98_r4_2_eq k
  · exact power98_r4_3_eq k
  · exact power98_r4_4_eq k
  · exact power98_r4_5_eq k
  · exact power98_r4_6_eq k
  · exact power98_r4_7_eq k
  · exact power98_r4_8_eq k
  · exact power98_r4_9_eq k
  · exact power98_r4_10_eq k
  · exact power98_r4_11_eq k
  · exact power98_r4_12_eq k
  · exact power98_r4_13_eq k
  · exact power98_r4_14_eq k
  · exact power98_r4_15_eq k
lemma power98_r5_0_eq : ∀ k : Fin 16, power98Expr 5 0 k = power98_r5_0 k := by decide +kernel
lemma power98_r5_1_eq : ∀ k : Fin 16, power98Expr 5 1 k = power98_r5_1 k := by decide +kernel
lemma power98_r5_2_eq : ∀ k : Fin 16, power98Expr 5 2 k = power98_r5_2 k := by decide +kernel
lemma power98_r5_3_eq : ∀ k : Fin 16, power98Expr 5 3 k = power98_r5_3 k := by decide +kernel
lemma power98_r5_4_eq : ∀ k : Fin 16, power98Expr 5 4 k = power98_r5_4 k := by decide +kernel
lemma power98_r5_5_eq : ∀ k : Fin 16, power98Expr 5 5 k = power98_r5_5 k := by decide +kernel
lemma power98_r5_6_eq : ∀ k : Fin 16, power98Expr 5 6 k = power98_r5_6 k := by decide +kernel
lemma power98_r5_7_eq : ∀ k : Fin 16, power98Expr 5 7 k = power98_r5_7 k := by decide +kernel
lemma power98_r5_8_eq : ∀ k : Fin 16, power98Expr 5 8 k = power98_r5_8 k := by decide +kernel
lemma power98_r5_9_eq : ∀ k : Fin 16, power98Expr 5 9 k = power98_r5_9 k := by decide +kernel
lemma power98_r5_10_eq : ∀ k : Fin 16, power98Expr 5 10 k = power98_r5_10 k := by decide +kernel
lemma power98_r5_11_eq : ∀ k : Fin 16, power98Expr 5 11 k = power98_r5_11 k := by decide +kernel
lemma power98_r5_12_eq : ∀ k : Fin 16, power98Expr 5 12 k = power98_r5_12 k := by decide +kernel
lemma power98_r5_13_eq : ∀ k : Fin 16, power98Expr 5 13 k = power98_r5_13 k := by decide +kernel
lemma power98_r5_14_eq : ∀ k : Fin 16, power98Expr 5 14 k = power98_r5_14 k := by decide +kernel
lemma power98_r5_15_eq : ∀ k : Fin 16, power98Expr 5 15 k = power98_r5_15 k := by decide +kernel
lemma power98_r5_eq (i k : Fin 16) : power98Expr 5 i k = power98_r5 i k := by
  fin_cases i
  · exact power98_r5_0_eq k
  · exact power98_r5_1_eq k
  · exact power98_r5_2_eq k
  · exact power98_r5_3_eq k
  · exact power98_r5_4_eq k
  · exact power98_r5_5_eq k
  · exact power98_r5_6_eq k
  · exact power98_r5_7_eq k
  · exact power98_r5_8_eq k
  · exact power98_r5_9_eq k
  · exact power98_r5_10_eq k
  · exact power98_r5_11_eq k
  · exact power98_r5_12_eq k
  · exact power98_r5_13_eq k
  · exact power98_r5_14_eq k
  · exact power98_r5_15_eq k
lemma power98_eq (j : Fin 6) (i k : Fin 16) : power98Expr j i k = power98 j i k := by
  fin_cases j
  · exact power98_r0_eq i k
  · exact power98_r1_eq i k
  · exact power98_r2_eq i k
  · exact power98_r3_eq i k
  · exact power98_r4_eq i k
  · exact power98_r5_eq i k
lemma power98_contains (j : Fin 6) (i k : Fin 16) :
    (power98 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(98:ℕ))) := by
  rw [← power98_eq]
  unfold power98Expr
  convert exp_direct_step_e (power97_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma power99_r0_0_eq : ∀ k : Fin 16, power99Expr 0 0 k = power99_r0_0 k := by decide +kernel
lemma power99_r0_1_eq : ∀ k : Fin 16, power99Expr 0 1 k = power99_r0_1 k := by decide +kernel
lemma power99_r0_2_eq : ∀ k : Fin 16, power99Expr 0 2 k = power99_r0_2 k := by decide +kernel
lemma power99_r0_3_eq : ∀ k : Fin 16, power99Expr 0 3 k = power99_r0_3 k := by decide +kernel
lemma power99_r0_4_eq : ∀ k : Fin 16, power99Expr 0 4 k = power99_r0_4 k := by decide +kernel
lemma power99_r0_5_eq : ∀ k : Fin 16, power99Expr 0 5 k = power99_r0_5 k := by decide +kernel
lemma power99_r0_6_eq : ∀ k : Fin 16, power99Expr 0 6 k = power99_r0_6 k := by decide +kernel
lemma power99_r0_7_eq : ∀ k : Fin 16, power99Expr 0 7 k = power99_r0_7 k := by decide +kernel
lemma power99_r0_8_eq : ∀ k : Fin 16, power99Expr 0 8 k = power99_r0_8 k := by decide +kernel
lemma power99_r0_9_eq : ∀ k : Fin 16, power99Expr 0 9 k = power99_r0_9 k := by decide +kernel
lemma power99_r0_10_eq : ∀ k : Fin 16, power99Expr 0 10 k = power99_r0_10 k := by decide +kernel
lemma power99_r0_11_eq : ∀ k : Fin 16, power99Expr 0 11 k = power99_r0_11 k := by decide +kernel
lemma power99_r0_12_eq : ∀ k : Fin 16, power99Expr 0 12 k = power99_r0_12 k := by decide +kernel
lemma power99_r0_13_eq : ∀ k : Fin 16, power99Expr 0 13 k = power99_r0_13 k := by decide +kernel
lemma power99_r0_14_eq : ∀ k : Fin 16, power99Expr 0 14 k = power99_r0_14 k := by decide +kernel
lemma power99_r0_15_eq : ∀ k : Fin 16, power99Expr 0 15 k = power99_r0_15 k := by decide +kernel
lemma power99_r0_eq (i k : Fin 16) : power99Expr 0 i k = power99_r0 i k := by
  fin_cases i
  · exact power99_r0_0_eq k
  · exact power99_r0_1_eq k
  · exact power99_r0_2_eq k
  · exact power99_r0_3_eq k
  · exact power99_r0_4_eq k
  · exact power99_r0_5_eq k
  · exact power99_r0_6_eq k
  · exact power99_r0_7_eq k
  · exact power99_r0_8_eq k
  · exact power99_r0_9_eq k
  · exact power99_r0_10_eq k
  · exact power99_r0_11_eq k
  · exact power99_r0_12_eq k
  · exact power99_r0_13_eq k
  · exact power99_r0_14_eq k
  · exact power99_r0_15_eq k
lemma power99_r1_0_eq : ∀ k : Fin 16, power99Expr 1 0 k = power99_r1_0 k := by decide +kernel
lemma power99_r1_1_eq : ∀ k : Fin 16, power99Expr 1 1 k = power99_r1_1 k := by decide +kernel
lemma power99_r1_2_eq : ∀ k : Fin 16, power99Expr 1 2 k = power99_r1_2 k := by decide +kernel
lemma power99_r1_3_eq : ∀ k : Fin 16, power99Expr 1 3 k = power99_r1_3 k := by decide +kernel
lemma power99_r1_4_eq : ∀ k : Fin 16, power99Expr 1 4 k = power99_r1_4 k := by decide +kernel
lemma power99_r1_5_eq : ∀ k : Fin 16, power99Expr 1 5 k = power99_r1_5 k := by decide +kernel
lemma power99_r1_6_eq : ∀ k : Fin 16, power99Expr 1 6 k = power99_r1_6 k := by decide +kernel
lemma power99_r1_7_eq : ∀ k : Fin 16, power99Expr 1 7 k = power99_r1_7 k := by decide +kernel
lemma power99_r1_8_eq : ∀ k : Fin 16, power99Expr 1 8 k = power99_r1_8 k := by decide +kernel
lemma power99_r1_9_eq : ∀ k : Fin 16, power99Expr 1 9 k = power99_r1_9 k := by decide +kernel
lemma power99_r1_10_eq : ∀ k : Fin 16, power99Expr 1 10 k = power99_r1_10 k := by decide +kernel
lemma power99_r1_11_eq : ∀ k : Fin 16, power99Expr 1 11 k = power99_r1_11 k := by decide +kernel
lemma power99_r1_12_eq : ∀ k : Fin 16, power99Expr 1 12 k = power99_r1_12 k := by decide +kernel
lemma power99_r1_13_eq : ∀ k : Fin 16, power99Expr 1 13 k = power99_r1_13 k := by decide +kernel
lemma power99_r1_14_eq : ∀ k : Fin 16, power99Expr 1 14 k = power99_r1_14 k := by decide +kernel
lemma power99_r1_15_eq : ∀ k : Fin 16, power99Expr 1 15 k = power99_r1_15 k := by decide +kernel
lemma power99_r1_eq (i k : Fin 16) : power99Expr 1 i k = power99_r1 i k := by
  fin_cases i
  · exact power99_r1_0_eq k
  · exact power99_r1_1_eq k
  · exact power99_r1_2_eq k
  · exact power99_r1_3_eq k
  · exact power99_r1_4_eq k
  · exact power99_r1_5_eq k
  · exact power99_r1_6_eq k
  · exact power99_r1_7_eq k
  · exact power99_r1_8_eq k
  · exact power99_r1_9_eq k
  · exact power99_r1_10_eq k
  · exact power99_r1_11_eq k
  · exact power99_r1_12_eq k
  · exact power99_r1_13_eq k
  · exact power99_r1_14_eq k
  · exact power99_r1_15_eq k
lemma power99_r2_0_eq : ∀ k : Fin 16, power99Expr 2 0 k = power99_r2_0 k := by decide +kernel
lemma power99_r2_1_eq : ∀ k : Fin 16, power99Expr 2 1 k = power99_r2_1 k := by decide +kernel
lemma power99_r2_2_eq : ∀ k : Fin 16, power99Expr 2 2 k = power99_r2_2 k := by decide +kernel
lemma power99_r2_3_eq : ∀ k : Fin 16, power99Expr 2 3 k = power99_r2_3 k := by decide +kernel
lemma power99_r2_4_eq : ∀ k : Fin 16, power99Expr 2 4 k = power99_r2_4 k := by decide +kernel
lemma power99_r2_5_eq : ∀ k : Fin 16, power99Expr 2 5 k = power99_r2_5 k := by decide +kernel
lemma power99_r2_6_eq : ∀ k : Fin 16, power99Expr 2 6 k = power99_r2_6 k := by decide +kernel
lemma power99_r2_7_eq : ∀ k : Fin 16, power99Expr 2 7 k = power99_r2_7 k := by decide +kernel
lemma power99_r2_8_eq : ∀ k : Fin 16, power99Expr 2 8 k = power99_r2_8 k := by decide +kernel
lemma power99_r2_9_eq : ∀ k : Fin 16, power99Expr 2 9 k = power99_r2_9 k := by decide +kernel
lemma power99_r2_10_eq : ∀ k : Fin 16, power99Expr 2 10 k = power99_r2_10 k := by decide +kernel
lemma power99_r2_11_eq : ∀ k : Fin 16, power99Expr 2 11 k = power99_r2_11 k := by decide +kernel
lemma power99_r2_12_eq : ∀ k : Fin 16, power99Expr 2 12 k = power99_r2_12 k := by decide +kernel
lemma power99_r2_13_eq : ∀ k : Fin 16, power99Expr 2 13 k = power99_r2_13 k := by decide +kernel
lemma power99_r2_14_eq : ∀ k : Fin 16, power99Expr 2 14 k = power99_r2_14 k := by decide +kernel
lemma power99_r2_15_eq : ∀ k : Fin 16, power99Expr 2 15 k = power99_r2_15 k := by decide +kernel
lemma power99_r2_eq (i k : Fin 16) : power99Expr 2 i k = power99_r2 i k := by
  fin_cases i
  · exact power99_r2_0_eq k
  · exact power99_r2_1_eq k
  · exact power99_r2_2_eq k
  · exact power99_r2_3_eq k
  · exact power99_r2_4_eq k
  · exact power99_r2_5_eq k
  · exact power99_r2_6_eq k
  · exact power99_r2_7_eq k
  · exact power99_r2_8_eq k
  · exact power99_r2_9_eq k
  · exact power99_r2_10_eq k
  · exact power99_r2_11_eq k
  · exact power99_r2_12_eq k
  · exact power99_r2_13_eq k
  · exact power99_r2_14_eq k
  · exact power99_r2_15_eq k
lemma power99_r3_0_eq : ∀ k : Fin 16, power99Expr 3 0 k = power99_r3_0 k := by decide +kernel
lemma power99_r3_1_eq : ∀ k : Fin 16, power99Expr 3 1 k = power99_r3_1 k := by decide +kernel
lemma power99_r3_2_eq : ∀ k : Fin 16, power99Expr 3 2 k = power99_r3_2 k := by decide +kernel
lemma power99_r3_3_eq : ∀ k : Fin 16, power99Expr 3 3 k = power99_r3_3 k := by decide +kernel
lemma power99_r3_4_eq : ∀ k : Fin 16, power99Expr 3 4 k = power99_r3_4 k := by decide +kernel
lemma power99_r3_5_eq : ∀ k : Fin 16, power99Expr 3 5 k = power99_r3_5 k := by decide +kernel
lemma power99_r3_6_eq : ∀ k : Fin 16, power99Expr 3 6 k = power99_r3_6 k := by decide +kernel
lemma power99_r3_7_eq : ∀ k : Fin 16, power99Expr 3 7 k = power99_r3_7 k := by decide +kernel
lemma power99_r3_8_eq : ∀ k : Fin 16, power99Expr 3 8 k = power99_r3_8 k := by decide +kernel
lemma power99_r3_9_eq : ∀ k : Fin 16, power99Expr 3 9 k = power99_r3_9 k := by decide +kernel
lemma power99_r3_10_eq : ∀ k : Fin 16, power99Expr 3 10 k = power99_r3_10 k := by decide +kernel
lemma power99_r3_11_eq : ∀ k : Fin 16, power99Expr 3 11 k = power99_r3_11 k := by decide +kernel
lemma power99_r3_12_eq : ∀ k : Fin 16, power99Expr 3 12 k = power99_r3_12 k := by decide +kernel
lemma power99_r3_13_eq : ∀ k : Fin 16, power99Expr 3 13 k = power99_r3_13 k := by decide +kernel
lemma power99_r3_14_eq : ∀ k : Fin 16, power99Expr 3 14 k = power99_r3_14 k := by decide +kernel
lemma power99_r3_15_eq : ∀ k : Fin 16, power99Expr 3 15 k = power99_r3_15 k := by decide +kernel
lemma power99_r3_eq (i k : Fin 16) : power99Expr 3 i k = power99_r3 i k := by
  fin_cases i
  · exact power99_r3_0_eq k
  · exact power99_r3_1_eq k
  · exact power99_r3_2_eq k
  · exact power99_r3_3_eq k
  · exact power99_r3_4_eq k
  · exact power99_r3_5_eq k
  · exact power99_r3_6_eq k
  · exact power99_r3_7_eq k
  · exact power99_r3_8_eq k
  · exact power99_r3_9_eq k
  · exact power99_r3_10_eq k
  · exact power99_r3_11_eq k
  · exact power99_r3_12_eq k
  · exact power99_r3_13_eq k
  · exact power99_r3_14_eq k
  · exact power99_r3_15_eq k
lemma power99_r4_0_eq : ∀ k : Fin 16, power99Expr 4 0 k = power99_r4_0 k := by decide +kernel
lemma power99_r4_1_eq : ∀ k : Fin 16, power99Expr 4 1 k = power99_r4_1 k := by decide +kernel
lemma power99_r4_2_eq : ∀ k : Fin 16, power99Expr 4 2 k = power99_r4_2 k := by decide +kernel
lemma power99_r4_3_eq : ∀ k : Fin 16, power99Expr 4 3 k = power99_r4_3 k := by decide +kernel
lemma power99_r4_4_eq : ∀ k : Fin 16, power99Expr 4 4 k = power99_r4_4 k := by decide +kernel
lemma power99_r4_5_eq : ∀ k : Fin 16, power99Expr 4 5 k = power99_r4_5 k := by decide +kernel
lemma power99_r4_6_eq : ∀ k : Fin 16, power99Expr 4 6 k = power99_r4_6 k := by decide +kernel
lemma power99_r4_7_eq : ∀ k : Fin 16, power99Expr 4 7 k = power99_r4_7 k := by decide +kernel
lemma power99_r4_8_eq : ∀ k : Fin 16, power99Expr 4 8 k = power99_r4_8 k := by decide +kernel
lemma power99_r4_9_eq : ∀ k : Fin 16, power99Expr 4 9 k = power99_r4_9 k := by decide +kernel
lemma power99_r4_10_eq : ∀ k : Fin 16, power99Expr 4 10 k = power99_r4_10 k := by decide +kernel
lemma power99_r4_11_eq : ∀ k : Fin 16, power99Expr 4 11 k = power99_r4_11 k := by decide +kernel
lemma power99_r4_12_eq : ∀ k : Fin 16, power99Expr 4 12 k = power99_r4_12 k := by decide +kernel
lemma power99_r4_13_eq : ∀ k : Fin 16, power99Expr 4 13 k = power99_r4_13 k := by decide +kernel
lemma power99_r4_14_eq : ∀ k : Fin 16, power99Expr 4 14 k = power99_r4_14 k := by decide +kernel
lemma power99_r4_15_eq : ∀ k : Fin 16, power99Expr 4 15 k = power99_r4_15 k := by decide +kernel
lemma power99_r4_eq (i k : Fin 16) : power99Expr 4 i k = power99_r4 i k := by
  fin_cases i
  · exact power99_r4_0_eq k
  · exact power99_r4_1_eq k
  · exact power99_r4_2_eq k
  · exact power99_r4_3_eq k
  · exact power99_r4_4_eq k
  · exact power99_r4_5_eq k
  · exact power99_r4_6_eq k
  · exact power99_r4_7_eq k
  · exact power99_r4_8_eq k
  · exact power99_r4_9_eq k
  · exact power99_r4_10_eq k
  · exact power99_r4_11_eq k
  · exact power99_r4_12_eq k
  · exact power99_r4_13_eq k
  · exact power99_r4_14_eq k
  · exact power99_r4_15_eq k
lemma power99_r5_0_eq : ∀ k : Fin 16, power99Expr 5 0 k = power99_r5_0 k := by decide +kernel
lemma power99_r5_1_eq : ∀ k : Fin 16, power99Expr 5 1 k = power99_r5_1 k := by decide +kernel
lemma power99_r5_2_eq : ∀ k : Fin 16, power99Expr 5 2 k = power99_r5_2 k := by decide +kernel
lemma power99_r5_3_eq : ∀ k : Fin 16, power99Expr 5 3 k = power99_r5_3 k := by decide +kernel
lemma power99_r5_4_eq : ∀ k : Fin 16, power99Expr 5 4 k = power99_r5_4 k := by decide +kernel
lemma power99_r5_5_eq : ∀ k : Fin 16, power99Expr 5 5 k = power99_r5_5 k := by decide +kernel
lemma power99_r5_6_eq : ∀ k : Fin 16, power99Expr 5 6 k = power99_r5_6 k := by decide +kernel
lemma power99_r5_7_eq : ∀ k : Fin 16, power99Expr 5 7 k = power99_r5_7 k := by decide +kernel
lemma power99_r5_8_eq : ∀ k : Fin 16, power99Expr 5 8 k = power99_r5_8 k := by decide +kernel
lemma power99_r5_9_eq : ∀ k : Fin 16, power99Expr 5 9 k = power99_r5_9 k := by decide +kernel
lemma power99_r5_10_eq : ∀ k : Fin 16, power99Expr 5 10 k = power99_r5_10 k := by decide +kernel
lemma power99_r5_11_eq : ∀ k : Fin 16, power99Expr 5 11 k = power99_r5_11 k := by decide +kernel
lemma power99_r5_12_eq : ∀ k : Fin 16, power99Expr 5 12 k = power99_r5_12 k := by decide +kernel
lemma power99_r5_13_eq : ∀ k : Fin 16, power99Expr 5 13 k = power99_r5_13 k := by decide +kernel
lemma power99_r5_14_eq : ∀ k : Fin 16, power99Expr 5 14 k = power99_r5_14 k := by decide +kernel
lemma power99_r5_15_eq : ∀ k : Fin 16, power99Expr 5 15 k = power99_r5_15 k := by decide +kernel
lemma power99_r5_eq (i k : Fin 16) : power99Expr 5 i k = power99_r5 i k := by
  fin_cases i
  · exact power99_r5_0_eq k
  · exact power99_r5_1_eq k
  · exact power99_r5_2_eq k
  · exact power99_r5_3_eq k
  · exact power99_r5_4_eq k
  · exact power99_r5_5_eq k
  · exact power99_r5_6_eq k
  · exact power99_r5_7_eq k
  · exact power99_r5_8_eq k
  · exact power99_r5_9_eq k
  · exact power99_r5_10_eq k
  · exact power99_r5_11_eq k
  · exact power99_r5_12_eq k
  · exact power99_r5_13_eq k
  · exact power99_r5_14_eq k
  · exact power99_r5_15_eq k
lemma power99_eq (j : Fin 6) (i k : Fin 16) : power99Expr j i k = power99 j i k := by
  fin_cases j
  · exact power99_r0_eq i k
  · exact power99_r1_eq i k
  · exact power99_r2_eq i k
  · exact power99_r3_eq i k
  · exact power99_r4_eq i k
  · exact power99_r5_eq i k
lemma power99_contains (j : Fin 6) (i k : Fin 16) :
    (power99 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(99:ℕ))) := by
  rw [← power99_eq]
  unfold power99Expr
  convert exp_direct_step_e (power98_contains j i k) (gridRows_contains_e j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns100
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
lemma column99_0_r0_0_eq : ∀ k : Fin 16, column99_0Expr 0 0 k = column99_0_r0_0 k := by decide +kernel
lemma column99_0_r0_1_eq : ∀ k : Fin 16, column99_0Expr 0 1 k = column99_0_r0_1 k := by decide +kernel
lemma column99_0_r0_2_eq : ∀ k : Fin 16, column99_0Expr 0 2 k = column99_0_r0_2 k := by decide +kernel
lemma column99_0_r0_3_eq : ∀ k : Fin 16, column99_0Expr 0 3 k = column99_0_r0_3 k := by decide +kernel
lemma column99_0_r0_4_eq : ∀ k : Fin 16, column99_0Expr 0 4 k = column99_0_r0_4 k := by decide +kernel
lemma column99_0_r0_5_eq : ∀ k : Fin 16, column99_0Expr 0 5 k = column99_0_r0_5 k := by decide +kernel
lemma column99_0_r0_6_eq : ∀ k : Fin 16, column99_0Expr 0 6 k = column99_0_r0_6 k := by decide +kernel
lemma column99_0_r0_7_eq : ∀ k : Fin 16, column99_0Expr 0 7 k = column99_0_r0_7 k := by decide +kernel
lemma column99_0_r0_8_eq : ∀ k : Fin 16, column99_0Expr 0 8 k = column99_0_r0_8 k := by decide +kernel
lemma column99_0_r0_9_eq : ∀ k : Fin 16, column99_0Expr 0 9 k = column99_0_r0_9 k := by decide +kernel
lemma column99_0_r0_10_eq : ∀ k : Fin 16, column99_0Expr 0 10 k = column99_0_r0_10 k := by decide +kernel
lemma column99_0_r0_11_eq : ∀ k : Fin 16, column99_0Expr 0 11 k = column99_0_r0_11 k := by decide +kernel
lemma column99_0_r0_12_eq : ∀ k : Fin 16, column99_0Expr 0 12 k = column99_0_r0_12 k := by decide +kernel
lemma column99_0_r0_13_eq : ∀ k : Fin 16, column99_0Expr 0 13 k = column99_0_r0_13 k := by decide +kernel
lemma column99_0_r0_14_eq : ∀ k : Fin 16, column99_0Expr 0 14 k = column99_0_r0_14 k := by decide +kernel
lemma column99_0_r0_15_eq : ∀ k : Fin 16, column99_0Expr 0 15 k = column99_0_r0_15 k := by decide +kernel
lemma column99_0_r0_eq (i k : Fin 16) : column99_0Expr 0 i k = column99_0_r0 i k := by
  fin_cases i
  · exact column99_0_r0_0_eq k
  · exact column99_0_r0_1_eq k
  · exact column99_0_r0_2_eq k
  · exact column99_0_r0_3_eq k
  · exact column99_0_r0_4_eq k
  · exact column99_0_r0_5_eq k
  · exact column99_0_r0_6_eq k
  · exact column99_0_r0_7_eq k
  · exact column99_0_r0_8_eq k
  · exact column99_0_r0_9_eq k
  · exact column99_0_r0_10_eq k
  · exact column99_0_r0_11_eq k
  · exact column99_0_r0_12_eq k
  · exact column99_0_r0_13_eq k
  · exact column99_0_r0_14_eq k
  · exact column99_0_r0_15_eq k
lemma column99_0_r1_0_eq : ∀ k : Fin 16, column99_0Expr 1 0 k = column99_0_r1_0 k := by decide +kernel
lemma column99_0_r1_1_eq : ∀ k : Fin 16, column99_0Expr 1 1 k = column99_0_r1_1 k := by decide +kernel
lemma column99_0_r1_2_eq : ∀ k : Fin 16, column99_0Expr 1 2 k = column99_0_r1_2 k := by decide +kernel
lemma column99_0_r1_3_eq : ∀ k : Fin 16, column99_0Expr 1 3 k = column99_0_r1_3 k := by decide +kernel
lemma column99_0_r1_4_eq : ∀ k : Fin 16, column99_0Expr 1 4 k = column99_0_r1_4 k := by decide +kernel
lemma column99_0_r1_5_eq : ∀ k : Fin 16, column99_0Expr 1 5 k = column99_0_r1_5 k := by decide +kernel
lemma column99_0_r1_6_eq : ∀ k : Fin 16, column99_0Expr 1 6 k = column99_0_r1_6 k := by decide +kernel
lemma column99_0_r1_7_eq : ∀ k : Fin 16, column99_0Expr 1 7 k = column99_0_r1_7 k := by decide +kernel
lemma column99_0_r1_8_eq : ∀ k : Fin 16, column99_0Expr 1 8 k = column99_0_r1_8 k := by decide +kernel
lemma column99_0_r1_9_eq : ∀ k : Fin 16, column99_0Expr 1 9 k = column99_0_r1_9 k := by decide +kernel
lemma column99_0_r1_10_eq : ∀ k : Fin 16, column99_0Expr 1 10 k = column99_0_r1_10 k := by decide +kernel
lemma column99_0_r1_11_eq : ∀ k : Fin 16, column99_0Expr 1 11 k = column99_0_r1_11 k := by decide +kernel
lemma column99_0_r1_12_eq : ∀ k : Fin 16, column99_0Expr 1 12 k = column99_0_r1_12 k := by decide +kernel
lemma column99_0_r1_13_eq : ∀ k : Fin 16, column99_0Expr 1 13 k = column99_0_r1_13 k := by decide +kernel
lemma column99_0_r1_14_eq : ∀ k : Fin 16, column99_0Expr 1 14 k = column99_0_r1_14 k := by decide +kernel
lemma column99_0_r1_15_eq : ∀ k : Fin 16, column99_0Expr 1 15 k = column99_0_r1_15 k := by decide +kernel
lemma column99_0_r1_eq (i k : Fin 16) : column99_0Expr 1 i k = column99_0_r1 i k := by
  fin_cases i
  · exact column99_0_r1_0_eq k
  · exact column99_0_r1_1_eq k
  · exact column99_0_r1_2_eq k
  · exact column99_0_r1_3_eq k
  · exact column99_0_r1_4_eq k
  · exact column99_0_r1_5_eq k
  · exact column99_0_r1_6_eq k
  · exact column99_0_r1_7_eq k
  · exact column99_0_r1_8_eq k
  · exact column99_0_r1_9_eq k
  · exact column99_0_r1_10_eq k
  · exact column99_0_r1_11_eq k
  · exact column99_0_r1_12_eq k
  · exact column99_0_r1_13_eq k
  · exact column99_0_r1_14_eq k
  · exact column99_0_r1_15_eq k
lemma column99_0_r2_0_eq : ∀ k : Fin 16, column99_0Expr 2 0 k = column99_0_r2_0 k := by decide +kernel
lemma column99_0_r2_1_eq : ∀ k : Fin 16, column99_0Expr 2 1 k = column99_0_r2_1 k := by decide +kernel
lemma column99_0_r2_2_eq : ∀ k : Fin 16, column99_0Expr 2 2 k = column99_0_r2_2 k := by decide +kernel
lemma column99_0_r2_3_eq : ∀ k : Fin 16, column99_0Expr 2 3 k = column99_0_r2_3 k := by decide +kernel
lemma column99_0_r2_4_eq : ∀ k : Fin 16, column99_0Expr 2 4 k = column99_0_r2_4 k := by decide +kernel
lemma column99_0_r2_5_eq : ∀ k : Fin 16, column99_0Expr 2 5 k = column99_0_r2_5 k := by decide +kernel
lemma column99_0_r2_6_eq : ∀ k : Fin 16, column99_0Expr 2 6 k = column99_0_r2_6 k := by decide +kernel
lemma column99_0_r2_7_eq : ∀ k : Fin 16, column99_0Expr 2 7 k = column99_0_r2_7 k := by decide +kernel
lemma column99_0_r2_8_eq : ∀ k : Fin 16, column99_0Expr 2 8 k = column99_0_r2_8 k := by decide +kernel
lemma column99_0_r2_9_eq : ∀ k : Fin 16, column99_0Expr 2 9 k = column99_0_r2_9 k := by decide +kernel
lemma column99_0_r2_10_eq : ∀ k : Fin 16, column99_0Expr 2 10 k = column99_0_r2_10 k := by decide +kernel
lemma column99_0_r2_11_eq : ∀ k : Fin 16, column99_0Expr 2 11 k = column99_0_r2_11 k := by decide +kernel
lemma column99_0_r2_12_eq : ∀ k : Fin 16, column99_0Expr 2 12 k = column99_0_r2_12 k := by decide +kernel
lemma column99_0_r2_13_eq : ∀ k : Fin 16, column99_0Expr 2 13 k = column99_0_r2_13 k := by decide +kernel
lemma column99_0_r2_14_eq : ∀ k : Fin 16, column99_0Expr 2 14 k = column99_0_r2_14 k := by decide +kernel
lemma column99_0_r2_15_eq : ∀ k : Fin 16, column99_0Expr 2 15 k = column99_0_r2_15 k := by decide +kernel
lemma column99_0_r2_eq (i k : Fin 16) : column99_0Expr 2 i k = column99_0_r2 i k := by
  fin_cases i
  · exact column99_0_r2_0_eq k
  · exact column99_0_r2_1_eq k
  · exact column99_0_r2_2_eq k
  · exact column99_0_r2_3_eq k
  · exact column99_0_r2_4_eq k
  · exact column99_0_r2_5_eq k
  · exact column99_0_r2_6_eq k
  · exact column99_0_r2_7_eq k
  · exact column99_0_r2_8_eq k
  · exact column99_0_r2_9_eq k
  · exact column99_0_r2_10_eq k
  · exact column99_0_r2_11_eq k
  · exact column99_0_r2_12_eq k
  · exact column99_0_r2_13_eq k
  · exact column99_0_r2_14_eq k
  · exact column99_0_r2_15_eq k
lemma column99_0_r3_0_eq : ∀ k : Fin 16, column99_0Expr 3 0 k = column99_0_r3_0 k := by decide +kernel
lemma column99_0_r3_1_eq : ∀ k : Fin 16, column99_0Expr 3 1 k = column99_0_r3_1 k := by decide +kernel
lemma column99_0_r3_2_eq : ∀ k : Fin 16, column99_0Expr 3 2 k = column99_0_r3_2 k := by decide +kernel
lemma column99_0_r3_3_eq : ∀ k : Fin 16, column99_0Expr 3 3 k = column99_0_r3_3 k := by decide +kernel
lemma column99_0_r3_4_eq : ∀ k : Fin 16, column99_0Expr 3 4 k = column99_0_r3_4 k := by decide +kernel
lemma column99_0_r3_5_eq : ∀ k : Fin 16, column99_0Expr 3 5 k = column99_0_r3_5 k := by decide +kernel
lemma column99_0_r3_6_eq : ∀ k : Fin 16, column99_0Expr 3 6 k = column99_0_r3_6 k := by decide +kernel
lemma column99_0_r3_7_eq : ∀ k : Fin 16, column99_0Expr 3 7 k = column99_0_r3_7 k := by decide +kernel
lemma column99_0_r3_8_eq : ∀ k : Fin 16, column99_0Expr 3 8 k = column99_0_r3_8 k := by decide +kernel
lemma column99_0_r3_9_eq : ∀ k : Fin 16, column99_0Expr 3 9 k = column99_0_r3_9 k := by decide +kernel
lemma column99_0_r3_10_eq : ∀ k : Fin 16, column99_0Expr 3 10 k = column99_0_r3_10 k := by decide +kernel
lemma column99_0_r3_11_eq : ∀ k : Fin 16, column99_0Expr 3 11 k = column99_0_r3_11 k := by decide +kernel
lemma column99_0_r3_12_eq : ∀ k : Fin 16, column99_0Expr 3 12 k = column99_0_r3_12 k := by decide +kernel
lemma column99_0_r3_13_eq : ∀ k : Fin 16, column99_0Expr 3 13 k = column99_0_r3_13 k := by decide +kernel
lemma column99_0_r3_14_eq : ∀ k : Fin 16, column99_0Expr 3 14 k = column99_0_r3_14 k := by decide +kernel
lemma column99_0_r3_15_eq : ∀ k : Fin 16, column99_0Expr 3 15 k = column99_0_r3_15 k := by decide +kernel
lemma column99_0_r3_eq (i k : Fin 16) : column99_0Expr 3 i k = column99_0_r3 i k := by
  fin_cases i
  · exact column99_0_r3_0_eq k
  · exact column99_0_r3_1_eq k
  · exact column99_0_r3_2_eq k
  · exact column99_0_r3_3_eq k
  · exact column99_0_r3_4_eq k
  · exact column99_0_r3_5_eq k
  · exact column99_0_r3_6_eq k
  · exact column99_0_r3_7_eq k
  · exact column99_0_r3_8_eq k
  · exact column99_0_r3_9_eq k
  · exact column99_0_r3_10_eq k
  · exact column99_0_r3_11_eq k
  · exact column99_0_r3_12_eq k
  · exact column99_0_r3_13_eq k
  · exact column99_0_r3_14_eq k
  · exact column99_0_r3_15_eq k
lemma column99_0_r4_0_eq : ∀ k : Fin 16, column99_0Expr 4 0 k = column99_0_r4_0 k := by decide +kernel
lemma column99_0_r4_1_eq : ∀ k : Fin 16, column99_0Expr 4 1 k = column99_0_r4_1 k := by decide +kernel
lemma column99_0_r4_2_eq : ∀ k : Fin 16, column99_0Expr 4 2 k = column99_0_r4_2 k := by decide +kernel
lemma column99_0_r4_3_eq : ∀ k : Fin 16, column99_0Expr 4 3 k = column99_0_r4_3 k := by decide +kernel
lemma column99_0_r4_4_eq : ∀ k : Fin 16, column99_0Expr 4 4 k = column99_0_r4_4 k := by decide +kernel
lemma column99_0_r4_5_eq : ∀ k : Fin 16, column99_0Expr 4 5 k = column99_0_r4_5 k := by decide +kernel
lemma column99_0_r4_6_eq : ∀ k : Fin 16, column99_0Expr 4 6 k = column99_0_r4_6 k := by decide +kernel
lemma column99_0_r4_7_eq : ∀ k : Fin 16, column99_0Expr 4 7 k = column99_0_r4_7 k := by decide +kernel
lemma column99_0_r4_8_eq : ∀ k : Fin 16, column99_0Expr 4 8 k = column99_0_r4_8 k := by decide +kernel
lemma column99_0_r4_9_eq : ∀ k : Fin 16, column99_0Expr 4 9 k = column99_0_r4_9 k := by decide +kernel
lemma column99_0_r4_10_eq : ∀ k : Fin 16, column99_0Expr 4 10 k = column99_0_r4_10 k := by decide +kernel
lemma column99_0_r4_11_eq : ∀ k : Fin 16, column99_0Expr 4 11 k = column99_0_r4_11 k := by decide +kernel
lemma column99_0_r4_12_eq : ∀ k : Fin 16, column99_0Expr 4 12 k = column99_0_r4_12 k := by decide +kernel
lemma column99_0_r4_13_eq : ∀ k : Fin 16, column99_0Expr 4 13 k = column99_0_r4_13 k := by decide +kernel
lemma column99_0_r4_14_eq : ∀ k : Fin 16, column99_0Expr 4 14 k = column99_0_r4_14 k := by decide +kernel
lemma column99_0_r4_15_eq : ∀ k : Fin 16, column99_0Expr 4 15 k = column99_0_r4_15 k := by decide +kernel
lemma column99_0_r4_eq (i k : Fin 16) : column99_0Expr 4 i k = column99_0_r4 i k := by
  fin_cases i
  · exact column99_0_r4_0_eq k
  · exact column99_0_r4_1_eq k
  · exact column99_0_r4_2_eq k
  · exact column99_0_r4_3_eq k
  · exact column99_0_r4_4_eq k
  · exact column99_0_r4_5_eq k
  · exact column99_0_r4_6_eq k
  · exact column99_0_r4_7_eq k
  · exact column99_0_r4_8_eq k
  · exact column99_0_r4_9_eq k
  · exact column99_0_r4_10_eq k
  · exact column99_0_r4_11_eq k
  · exact column99_0_r4_12_eq k
  · exact column99_0_r4_13_eq k
  · exact column99_0_r4_14_eq k
  · exact column99_0_r4_15_eq k
lemma column99_0_r5_0_eq : ∀ k : Fin 16, column99_0Expr 5 0 k = column99_0_r5_0 k := by decide +kernel
lemma column99_0_r5_1_eq : ∀ k : Fin 16, column99_0Expr 5 1 k = column99_0_r5_1 k := by decide +kernel
lemma column99_0_r5_2_eq : ∀ k : Fin 16, column99_0Expr 5 2 k = column99_0_r5_2 k := by decide +kernel
lemma column99_0_r5_3_eq : ∀ k : Fin 16, column99_0Expr 5 3 k = column99_0_r5_3 k := by decide +kernel
lemma column99_0_r5_4_eq : ∀ k : Fin 16, column99_0Expr 5 4 k = column99_0_r5_4 k := by decide +kernel
lemma column99_0_r5_5_eq : ∀ k : Fin 16, column99_0Expr 5 5 k = column99_0_r5_5 k := by decide +kernel
lemma column99_0_r5_6_eq : ∀ k : Fin 16, column99_0Expr 5 6 k = column99_0_r5_6 k := by decide +kernel
lemma column99_0_r5_7_eq : ∀ k : Fin 16, column99_0Expr 5 7 k = column99_0_r5_7 k := by decide +kernel
lemma column99_0_r5_8_eq : ∀ k : Fin 16, column99_0Expr 5 8 k = column99_0_r5_8 k := by decide +kernel
lemma column99_0_r5_9_eq : ∀ k : Fin 16, column99_0Expr 5 9 k = column99_0_r5_9 k := by decide +kernel
lemma column99_0_r5_10_eq : ∀ k : Fin 16, column99_0Expr 5 10 k = column99_0_r5_10 k := by decide +kernel
lemma column99_0_r5_11_eq : ∀ k : Fin 16, column99_0Expr 5 11 k = column99_0_r5_11 k := by decide +kernel
lemma column99_0_r5_12_eq : ∀ k : Fin 16, column99_0Expr 5 12 k = column99_0_r5_12 k := by decide +kernel
lemma column99_0_r5_13_eq : ∀ k : Fin 16, column99_0Expr 5 13 k = column99_0_r5_13 k := by decide +kernel
lemma column99_0_r5_14_eq : ∀ k : Fin 16, column99_0Expr 5 14 k = column99_0_r5_14 k := by decide +kernel
lemma column99_0_r5_15_eq : ∀ k : Fin 16, column99_0Expr 5 15 k = column99_0_r5_15 k := by decide +kernel
lemma column99_0_r5_eq (i k : Fin 16) : column99_0Expr 5 i k = column99_0_r5 i k := by
  fin_cases i
  · exact column99_0_r5_0_eq k
  · exact column99_0_r5_1_eq k
  · exact column99_0_r5_2_eq k
  · exact column99_0_r5_3_eq k
  · exact column99_0_r5_4_eq k
  · exact column99_0_r5_5_eq k
  · exact column99_0_r5_6_eq k
  · exact column99_0_r5_7_eq k
  · exact column99_0_r5_8_eq k
  · exact column99_0_r5_9_eq k
  · exact column99_0_r5_10_eq k
  · exact column99_0_r5_11_eq k
  · exact column99_0_r5_12_eq k
  · exact column99_0_r5_13_eq k
  · exact column99_0_r5_14_eq k
  · exact column99_0_r5_15_eq k
lemma column99_0_eq (j : Fin 6) (i k : Fin 16) : column99_0Expr j i k = column99_0 j i k := by
  fin_cases j
  · exact column99_0_r0_eq i k
  · exact column99_0_r1_eq i k
  · exact column99_0_r2_eq i k
  · exact column99_0_r3_eq i k
  · exact column99_0_r4_eq i k
  · exact column99_0_r5_eq i k
lemma column99_0_contains_e_oai (j : Fin 6) (i k : Fin 16) :
    (column99_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction false 99 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column99_0_eq,basisFunction_wave,← mul_assoc]
  unfold column99_0Expr
  apply CBox.contains_mul_e
  · rw [← waveAmplitude_mod false 99 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp3_0_contains j i k
  · exact power99_contains j i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.column99_0_contains_e_oai := @OAI.SharpPlanar.CachedData.column99_0_contains_e_oai
