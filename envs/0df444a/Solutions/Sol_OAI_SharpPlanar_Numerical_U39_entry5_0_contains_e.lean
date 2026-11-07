-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.U39.entry5_0_contains_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T20:26:56.973261+00:00
-- url     : https://prove2.me/submissions/a24a1df1-9759-4077-ab01-4a9771e8af6c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel4_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_power39_contains_e
import Theorems.Thm_OAI_SharpPlanar_D_0_e
import Theorems.Thm_OAI_SharpPlanar_D_1_e
import Theorems.Thm_OAI_SharpPlanar_D_3_e
import Theorems.Thm_OAI_SharpPlanar_D_4_e
import Theorems.Thm_OAI_SharpPlanar_D_7_e
import Theorems.Thm_OAI_SharpPlanar_D_9_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aTable_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bTable_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_cachedMomentRuleBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_phase12_periodic_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_waveAmplitudeBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weightRows_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_bBounds_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_K_column_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_qiBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_S_apply_e

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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns40
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
lemma column39_0_r0_0_eq : ∀ k : Fin 16, column39_0Expr 0 0 k = column39_0_r0_0 k := by decide +kernel
lemma column39_0_r0_1_eq : ∀ k : Fin 16, column39_0Expr 0 1 k = column39_0_r0_1 k := by decide +kernel
lemma column39_0_r0_2_eq : ∀ k : Fin 16, column39_0Expr 0 2 k = column39_0_r0_2 k := by decide +kernel
lemma column39_0_r0_3_eq : ∀ k : Fin 16, column39_0Expr 0 3 k = column39_0_r0_3 k := by decide +kernel
lemma column39_0_r0_4_eq : ∀ k : Fin 16, column39_0Expr 0 4 k = column39_0_r0_4 k := by decide +kernel
lemma column39_0_r0_5_eq : ∀ k : Fin 16, column39_0Expr 0 5 k = column39_0_r0_5 k := by decide +kernel
lemma column39_0_r0_6_eq : ∀ k : Fin 16, column39_0Expr 0 6 k = column39_0_r0_6 k := by decide +kernel
lemma column39_0_r0_7_eq : ∀ k : Fin 16, column39_0Expr 0 7 k = column39_0_r0_7 k := by decide +kernel
lemma column39_0_r0_8_eq : ∀ k : Fin 16, column39_0Expr 0 8 k = column39_0_r0_8 k := by decide +kernel
lemma column39_0_r0_9_eq : ∀ k : Fin 16, column39_0Expr 0 9 k = column39_0_r0_9 k := by decide +kernel
lemma column39_0_r0_10_eq : ∀ k : Fin 16, column39_0Expr 0 10 k = column39_0_r0_10 k := by decide +kernel
lemma column39_0_r0_11_eq : ∀ k : Fin 16, column39_0Expr 0 11 k = column39_0_r0_11 k := by decide +kernel
lemma column39_0_r0_12_eq : ∀ k : Fin 16, column39_0Expr 0 12 k = column39_0_r0_12 k := by decide +kernel
lemma column39_0_r0_13_eq : ∀ k : Fin 16, column39_0Expr 0 13 k = column39_0_r0_13 k := by decide +kernel
lemma column39_0_r0_14_eq : ∀ k : Fin 16, column39_0Expr 0 14 k = column39_0_r0_14 k := by decide +kernel
lemma column39_0_r0_15_eq : ∀ k : Fin 16, column39_0Expr 0 15 k = column39_0_r0_15 k := by decide +kernel
lemma column39_0_r0_eq (i k : Fin 16) : column39_0Expr 0 i k = column39_0_r0 i k := by
  fin_cases i
  · exact column39_0_r0_0_eq k
  · exact column39_0_r0_1_eq k
  · exact column39_0_r0_2_eq k
  · exact column39_0_r0_3_eq k
  · exact column39_0_r0_4_eq k
  · exact column39_0_r0_5_eq k
  · exact column39_0_r0_6_eq k
  · exact column39_0_r0_7_eq k
  · exact column39_0_r0_8_eq k
  · exact column39_0_r0_9_eq k
  · exact column39_0_r0_10_eq k
  · exact column39_0_r0_11_eq k
  · exact column39_0_r0_12_eq k
  · exact column39_0_r0_13_eq k
  · exact column39_0_r0_14_eq k
  · exact column39_0_r0_15_eq k
lemma column39_0_r1_0_eq : ∀ k : Fin 16, column39_0Expr 1 0 k = column39_0_r1_0 k := by decide +kernel
lemma column39_0_r1_1_eq : ∀ k : Fin 16, column39_0Expr 1 1 k = column39_0_r1_1 k := by decide +kernel
lemma column39_0_r1_2_eq : ∀ k : Fin 16, column39_0Expr 1 2 k = column39_0_r1_2 k := by decide +kernel
lemma column39_0_r1_3_eq : ∀ k : Fin 16, column39_0Expr 1 3 k = column39_0_r1_3 k := by decide +kernel
lemma column39_0_r1_4_eq : ∀ k : Fin 16, column39_0Expr 1 4 k = column39_0_r1_4 k := by decide +kernel
lemma column39_0_r1_5_eq : ∀ k : Fin 16, column39_0Expr 1 5 k = column39_0_r1_5 k := by decide +kernel
lemma column39_0_r1_6_eq : ∀ k : Fin 16, column39_0Expr 1 6 k = column39_0_r1_6 k := by decide +kernel
lemma column39_0_r1_7_eq : ∀ k : Fin 16, column39_0Expr 1 7 k = column39_0_r1_7 k := by decide +kernel
lemma column39_0_r1_8_eq : ∀ k : Fin 16, column39_0Expr 1 8 k = column39_0_r1_8 k := by decide +kernel
lemma column39_0_r1_9_eq : ∀ k : Fin 16, column39_0Expr 1 9 k = column39_0_r1_9 k := by decide +kernel
lemma column39_0_r1_10_eq : ∀ k : Fin 16, column39_0Expr 1 10 k = column39_0_r1_10 k := by decide +kernel
lemma column39_0_r1_11_eq : ∀ k : Fin 16, column39_0Expr 1 11 k = column39_0_r1_11 k := by decide +kernel
lemma column39_0_r1_12_eq : ∀ k : Fin 16, column39_0Expr 1 12 k = column39_0_r1_12 k := by decide +kernel
lemma column39_0_r1_13_eq : ∀ k : Fin 16, column39_0Expr 1 13 k = column39_0_r1_13 k := by decide +kernel
lemma column39_0_r1_14_eq : ∀ k : Fin 16, column39_0Expr 1 14 k = column39_0_r1_14 k := by decide +kernel
lemma column39_0_r1_15_eq : ∀ k : Fin 16, column39_0Expr 1 15 k = column39_0_r1_15 k := by decide +kernel
lemma column39_0_r1_eq (i k : Fin 16) : column39_0Expr 1 i k = column39_0_r1 i k := by
  fin_cases i
  · exact column39_0_r1_0_eq k
  · exact column39_0_r1_1_eq k
  · exact column39_0_r1_2_eq k
  · exact column39_0_r1_3_eq k
  · exact column39_0_r1_4_eq k
  · exact column39_0_r1_5_eq k
  · exact column39_0_r1_6_eq k
  · exact column39_0_r1_7_eq k
  · exact column39_0_r1_8_eq k
  · exact column39_0_r1_9_eq k
  · exact column39_0_r1_10_eq k
  · exact column39_0_r1_11_eq k
  · exact column39_0_r1_12_eq k
  · exact column39_0_r1_13_eq k
  · exact column39_0_r1_14_eq k
  · exact column39_0_r1_15_eq k
lemma column39_0_r2_0_eq : ∀ k : Fin 16, column39_0Expr 2 0 k = column39_0_r2_0 k := by decide +kernel
lemma column39_0_r2_1_eq : ∀ k : Fin 16, column39_0Expr 2 1 k = column39_0_r2_1 k := by decide +kernel
lemma column39_0_r2_2_eq : ∀ k : Fin 16, column39_0Expr 2 2 k = column39_0_r2_2 k := by decide +kernel
lemma column39_0_r2_3_eq : ∀ k : Fin 16, column39_0Expr 2 3 k = column39_0_r2_3 k := by decide +kernel
lemma column39_0_r2_4_eq : ∀ k : Fin 16, column39_0Expr 2 4 k = column39_0_r2_4 k := by decide +kernel
lemma column39_0_r2_5_eq : ∀ k : Fin 16, column39_0Expr 2 5 k = column39_0_r2_5 k := by decide +kernel
lemma column39_0_r2_6_eq : ∀ k : Fin 16, column39_0Expr 2 6 k = column39_0_r2_6 k := by decide +kernel
lemma column39_0_r2_7_eq : ∀ k : Fin 16, column39_0Expr 2 7 k = column39_0_r2_7 k := by decide +kernel
lemma column39_0_r2_8_eq : ∀ k : Fin 16, column39_0Expr 2 8 k = column39_0_r2_8 k := by decide +kernel
lemma column39_0_r2_9_eq : ∀ k : Fin 16, column39_0Expr 2 9 k = column39_0_r2_9 k := by decide +kernel
lemma column39_0_r2_10_eq : ∀ k : Fin 16, column39_0Expr 2 10 k = column39_0_r2_10 k := by decide +kernel
lemma column39_0_r2_11_eq : ∀ k : Fin 16, column39_0Expr 2 11 k = column39_0_r2_11 k := by decide +kernel
lemma column39_0_r2_12_eq : ∀ k : Fin 16, column39_0Expr 2 12 k = column39_0_r2_12 k := by decide +kernel
lemma column39_0_r2_13_eq : ∀ k : Fin 16, column39_0Expr 2 13 k = column39_0_r2_13 k := by decide +kernel
lemma column39_0_r2_14_eq : ∀ k : Fin 16, column39_0Expr 2 14 k = column39_0_r2_14 k := by decide +kernel
lemma column39_0_r2_15_eq : ∀ k : Fin 16, column39_0Expr 2 15 k = column39_0_r2_15 k := by decide +kernel
lemma column39_0_r2_eq (i k : Fin 16) : column39_0Expr 2 i k = column39_0_r2 i k := by
  fin_cases i
  · exact column39_0_r2_0_eq k
  · exact column39_0_r2_1_eq k
  · exact column39_0_r2_2_eq k
  · exact column39_0_r2_3_eq k
  · exact column39_0_r2_4_eq k
  · exact column39_0_r2_5_eq k
  · exact column39_0_r2_6_eq k
  · exact column39_0_r2_7_eq k
  · exact column39_0_r2_8_eq k
  · exact column39_0_r2_9_eq k
  · exact column39_0_r2_10_eq k
  · exact column39_0_r2_11_eq k
  · exact column39_0_r2_12_eq k
  · exact column39_0_r2_13_eq k
  · exact column39_0_r2_14_eq k
  · exact column39_0_r2_15_eq k
lemma column39_0_r3_0_eq : ∀ k : Fin 16, column39_0Expr 3 0 k = column39_0_r3_0 k := by decide +kernel
lemma column39_0_r3_1_eq : ∀ k : Fin 16, column39_0Expr 3 1 k = column39_0_r3_1 k := by decide +kernel
lemma column39_0_r3_2_eq : ∀ k : Fin 16, column39_0Expr 3 2 k = column39_0_r3_2 k := by decide +kernel
lemma column39_0_r3_3_eq : ∀ k : Fin 16, column39_0Expr 3 3 k = column39_0_r3_3 k := by decide +kernel
lemma column39_0_r3_4_eq : ∀ k : Fin 16, column39_0Expr 3 4 k = column39_0_r3_4 k := by decide +kernel
lemma column39_0_r3_5_eq : ∀ k : Fin 16, column39_0Expr 3 5 k = column39_0_r3_5 k := by decide +kernel
lemma column39_0_r3_6_eq : ∀ k : Fin 16, column39_0Expr 3 6 k = column39_0_r3_6 k := by decide +kernel
lemma column39_0_r3_7_eq : ∀ k : Fin 16, column39_0Expr 3 7 k = column39_0_r3_7 k := by decide +kernel
lemma column39_0_r3_8_eq : ∀ k : Fin 16, column39_0Expr 3 8 k = column39_0_r3_8 k := by decide +kernel
lemma column39_0_r3_9_eq : ∀ k : Fin 16, column39_0Expr 3 9 k = column39_0_r3_9 k := by decide +kernel
lemma column39_0_r3_10_eq : ∀ k : Fin 16, column39_0Expr 3 10 k = column39_0_r3_10 k := by decide +kernel
lemma column39_0_r3_11_eq : ∀ k : Fin 16, column39_0Expr 3 11 k = column39_0_r3_11 k := by decide +kernel
lemma column39_0_r3_12_eq : ∀ k : Fin 16, column39_0Expr 3 12 k = column39_0_r3_12 k := by decide +kernel
lemma column39_0_r3_13_eq : ∀ k : Fin 16, column39_0Expr 3 13 k = column39_0_r3_13 k := by decide +kernel
lemma column39_0_r3_14_eq : ∀ k : Fin 16, column39_0Expr 3 14 k = column39_0_r3_14 k := by decide +kernel
lemma column39_0_r3_15_eq : ∀ k : Fin 16, column39_0Expr 3 15 k = column39_0_r3_15 k := by decide +kernel
lemma column39_0_r3_eq (i k : Fin 16) : column39_0Expr 3 i k = column39_0_r3 i k := by
  fin_cases i
  · exact column39_0_r3_0_eq k
  · exact column39_0_r3_1_eq k
  · exact column39_0_r3_2_eq k
  · exact column39_0_r3_3_eq k
  · exact column39_0_r3_4_eq k
  · exact column39_0_r3_5_eq k
  · exact column39_0_r3_6_eq k
  · exact column39_0_r3_7_eq k
  · exact column39_0_r3_8_eq k
  · exact column39_0_r3_9_eq k
  · exact column39_0_r3_10_eq k
  · exact column39_0_r3_11_eq k
  · exact column39_0_r3_12_eq k
  · exact column39_0_r3_13_eq k
  · exact column39_0_r3_14_eq k
  · exact column39_0_r3_15_eq k
lemma column39_0_r4_0_eq : ∀ k : Fin 16, column39_0Expr 4 0 k = column39_0_r4_0 k := by decide +kernel
lemma column39_0_r4_1_eq : ∀ k : Fin 16, column39_0Expr 4 1 k = column39_0_r4_1 k := by decide +kernel
lemma column39_0_r4_2_eq : ∀ k : Fin 16, column39_0Expr 4 2 k = column39_0_r4_2 k := by decide +kernel
lemma column39_0_r4_3_eq : ∀ k : Fin 16, column39_0Expr 4 3 k = column39_0_r4_3 k := by decide +kernel
lemma column39_0_r4_4_eq : ∀ k : Fin 16, column39_0Expr 4 4 k = column39_0_r4_4 k := by decide +kernel
lemma column39_0_r4_5_eq : ∀ k : Fin 16, column39_0Expr 4 5 k = column39_0_r4_5 k := by decide +kernel
lemma column39_0_r4_6_eq : ∀ k : Fin 16, column39_0Expr 4 6 k = column39_0_r4_6 k := by decide +kernel
lemma column39_0_r4_7_eq : ∀ k : Fin 16, column39_0Expr 4 7 k = column39_0_r4_7 k := by decide +kernel
lemma column39_0_r4_8_eq : ∀ k : Fin 16, column39_0Expr 4 8 k = column39_0_r4_8 k := by decide +kernel
lemma column39_0_r4_9_eq : ∀ k : Fin 16, column39_0Expr 4 9 k = column39_0_r4_9 k := by decide +kernel
lemma column39_0_r4_10_eq : ∀ k : Fin 16, column39_0Expr 4 10 k = column39_0_r4_10 k := by decide +kernel
lemma column39_0_r4_11_eq : ∀ k : Fin 16, column39_0Expr 4 11 k = column39_0_r4_11 k := by decide +kernel
lemma column39_0_r4_12_eq : ∀ k : Fin 16, column39_0Expr 4 12 k = column39_0_r4_12 k := by decide +kernel
lemma column39_0_r4_13_eq : ∀ k : Fin 16, column39_0Expr 4 13 k = column39_0_r4_13 k := by decide +kernel
lemma column39_0_r4_14_eq : ∀ k : Fin 16, column39_0Expr 4 14 k = column39_0_r4_14 k := by decide +kernel
lemma column39_0_r4_15_eq : ∀ k : Fin 16, column39_0Expr 4 15 k = column39_0_r4_15 k := by decide +kernel
lemma column39_0_r4_eq (i k : Fin 16) : column39_0Expr 4 i k = column39_0_r4 i k := by
  fin_cases i
  · exact column39_0_r4_0_eq k
  · exact column39_0_r4_1_eq k
  · exact column39_0_r4_2_eq k
  · exact column39_0_r4_3_eq k
  · exact column39_0_r4_4_eq k
  · exact column39_0_r4_5_eq k
  · exact column39_0_r4_6_eq k
  · exact column39_0_r4_7_eq k
  · exact column39_0_r4_8_eq k
  · exact column39_0_r4_9_eq k
  · exact column39_0_r4_10_eq k
  · exact column39_0_r4_11_eq k
  · exact column39_0_r4_12_eq k
  · exact column39_0_r4_13_eq k
  · exact column39_0_r4_14_eq k
  · exact column39_0_r4_15_eq k
lemma column39_0_r5_0_eq : ∀ k : Fin 16, column39_0Expr 5 0 k = column39_0_r5_0 k := by decide +kernel
lemma column39_0_r5_1_eq : ∀ k : Fin 16, column39_0Expr 5 1 k = column39_0_r5_1 k := by decide +kernel
lemma column39_0_r5_2_eq : ∀ k : Fin 16, column39_0Expr 5 2 k = column39_0_r5_2 k := by decide +kernel
lemma column39_0_r5_3_eq : ∀ k : Fin 16, column39_0Expr 5 3 k = column39_0_r5_3 k := by decide +kernel
lemma column39_0_r5_4_eq : ∀ k : Fin 16, column39_0Expr 5 4 k = column39_0_r5_4 k := by decide +kernel
lemma column39_0_r5_5_eq : ∀ k : Fin 16, column39_0Expr 5 5 k = column39_0_r5_5 k := by decide +kernel
lemma column39_0_r5_6_eq : ∀ k : Fin 16, column39_0Expr 5 6 k = column39_0_r5_6 k := by decide +kernel
lemma column39_0_r5_7_eq : ∀ k : Fin 16, column39_0Expr 5 7 k = column39_0_r5_7 k := by decide +kernel
lemma column39_0_r5_8_eq : ∀ k : Fin 16, column39_0Expr 5 8 k = column39_0_r5_8 k := by decide +kernel
lemma column39_0_r5_9_eq : ∀ k : Fin 16, column39_0Expr 5 9 k = column39_0_r5_9 k := by decide +kernel
lemma column39_0_r5_10_eq : ∀ k : Fin 16, column39_0Expr 5 10 k = column39_0_r5_10 k := by decide +kernel
lemma column39_0_r5_11_eq : ∀ k : Fin 16, column39_0Expr 5 11 k = column39_0_r5_11 k := by decide +kernel
lemma column39_0_r5_12_eq : ∀ k : Fin 16, column39_0Expr 5 12 k = column39_0_r5_12 k := by decide +kernel
lemma column39_0_r5_13_eq : ∀ k : Fin 16, column39_0Expr 5 13 k = column39_0_r5_13 k := by decide +kernel
lemma column39_0_r5_14_eq : ∀ k : Fin 16, column39_0Expr 5 14 k = column39_0_r5_14 k := by decide +kernel
lemma column39_0_r5_15_eq : ∀ k : Fin 16, column39_0Expr 5 15 k = column39_0_r5_15 k := by decide +kernel
lemma column39_0_r5_eq (i k : Fin 16) : column39_0Expr 5 i k = column39_0_r5 i k := by
  fin_cases i
  · exact column39_0_r5_0_eq k
  · exact column39_0_r5_1_eq k
  · exact column39_0_r5_2_eq k
  · exact column39_0_r5_3_eq k
  · exact column39_0_r5_4_eq k
  · exact column39_0_r5_5_eq k
  · exact column39_0_r5_6_eq k
  · exact column39_0_r5_7_eq k
  · exact column39_0_r5_8_eq k
  · exact column39_0_r5_9_eq k
  · exact column39_0_r5_10_eq k
  · exact column39_0_r5_11_eq k
  · exact column39_0_r5_12_eq k
  · exact column39_0_r5_13_eq k
  · exact column39_0_r5_14_eq k
  · exact column39_0_r5_15_eq k
lemma column39_0_eq (j : Fin 6) (i k : Fin 16) : column39_0Expr j i k = column39_0 j i k := by
  fin_cases j
  · exact column39_0_r0_eq i k
  · exact column39_0_r1_eq i k
  · exact column39_0_r2_eq i k
  · exact column39_0_r3_eq i k
  · exact column39_0_r4_eq i k
  · exact column39_0_r5_eq i k
lemma column39_0_contains (j : Fin 6) (i k : Fin 16) :
    (column39_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction false 39 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column39_0_eq,basisFunction_wave,← mul_assoc]
  unfold column39_0Expr
  apply CBox.contains_mul_e
  · rw [← waveAmplitude_mod false 39 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp3_0_contains j i k
  · exact power39_contains_e j i k
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments39
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace cm39_4_0_0
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
lemma checked : cachedMomentRuleBox column39_0 kernel4_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 39 4 false false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains_e column39_0_contains kernel4_0_contains_e
end cm39_4_0_0
namespace cm39_4_0_1
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
lemma checked : cachedMomentRuleBox column39_0 kernel4_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 39 4 false true) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains_e column39_0_contains kernel4_1_contains_e
end cm39_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entries of the cardinal interpolation operator

The columns of the interpolation operator are cardinal basis functions, and
certified quadrature controls their value and derivative entries.
-/

namespace SharpPlanar
open IntegerBasis IntegerIntervals IntegerGrid


lemma S_column_derivative (n m : Node) (d : Bool) :
    S (columnVector n d) (m,true) =
      (D m.val * K (positiveData (columnVector n d)) 0 m.val -
        K (positiveData (columnVector n d)) 1 m.val) / Q m.val := by
  simp [S_apply_e,Scoords]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_NodeIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

lemma dSmall_contains : dSmall.Contains (Real.pi*(3+2*b)/18) := by
  have hb := RBox.contains_add_e (RBox.contains_rat_e 3 1 (by norm_num))
    (RBox.contains_scale_e bBounds_contains_e 2 1 (by norm_num))
  convert RBox.contains_scale_e (RBox.contains_mul_e piBounds_contains_e hb) 1 18 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma dOther_contains : dOther.Contains (Real.pi*(3-2*b)/18) := by
  have hb := RBox.contains_add_e (RBox.contains_rat_e 3 1 (by norm_num))
    (RBox.contains_scale_e bBounds_contains_e (-2) 1 (by norm_num))
  convert RBox.contains_scale_e (RBox.contains_mul_e piBounds_contains_e hb) 1 18 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma dBase_contains : dBase.Contains (7*Real.pi*b/9) := by
  convert RBox.contains_scale_e (RBox.contains_mul_e piBounds_contains_e bBounds_contains_e) 7 9 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)

lemma dBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (dBox n).Contains (D n) := by
  have hh : D n = D (n%12) := by simp [D]
  rw [hh]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn|hn|hn|hn|hn|hn
  · simpa [D_0_e,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_e dBase_contains
  · simpa [D_1_e,hn,dBox] using dSmall_contains
  · simpa [D_3_e,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_e dSmall_contains
  · simpa [D_4_e,hn,dBox] using dBase_contains
  · simpa [D_7_e,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_e dOther_contains
  · simpa [D_9_e,hn,dBox] using dOther_contains

lemma S_column_derivative_contains {n m : Node} {d : Bool} {a c : RBox}
    (ha : a.Contains (K (positiveData (columnVector n d)) 0 m.val))
    (hc : c.Contains (K (positiveData (columnVector n d)) 1 m.val)) :
    (((dBox m.val).mul a).add c.neg |>.mul (qiBox m.val)).Contains (S (columnVector n d) (m,true)) := by
  rw [S_column_derivative,div_eq_mul_inv,sub_eq_add_neg]
  exact RBox.contains_mul_e
    (RBox.contains_add_e (RBox.contains_mul_e (dBox_contains m.val m.property.2) ha) (RBox.neg_contains_e hc))
    (qiBox_contains_e m.val m.property.2)
end Numerical
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert39
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

namespace SharpPlanar.Numerical.U39
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma entry5_0_contains_e_oai : entry5_0.Contains (umat 5 0) := by
  have h0 := K_column_contains_e (n:=node) (m:=4) (by decide) (by decide) false false cm39_4_0_0.contains
  have h1 := K_column_contains_e (n:=node) (m:=4) (by decide) (by decide) false true cm39_4_0_1.contains
  have hh := S_column_derivative_contains (m:=node4) h0 h1
  change entry5_0.Contains (S (columnVector node false) (node4,true))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  decide +kernel
end SharpPlanar.Numerical.U39

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.U39.entry5_0_contains_e_oai := @OAI.SharpPlanar.Numerical.U39.entry5_0_contains_e_oai
