-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.signedVU_norm_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T04:40:39.503524+00:00
-- url     : https://prove2.me/submissions/dcb8d999-228f-45fc-a272-62d5f5180ff7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel3_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel3_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel4_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_power48_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aTable_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bTable_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_cachedMomentRuleBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_phase12_periodic_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_waveAmplitudeBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_weightRows_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_abs_bound_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_K_column_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U100_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U100_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U12_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U12_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U13_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U13_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U15_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U15_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U16_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U16_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U19_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U19_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U21_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U24_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U24_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U25_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U25_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U27_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U27_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U28_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U28_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U31_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U31_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U33_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U33_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U36_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U36_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U37_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U37_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U39_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U39_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U40_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U40_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U43_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U43_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U45_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U45_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U48_entry0_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U48_entry0_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U48_entry1_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U48_entry2_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U48_entry3_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U48_entry3_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U48_entry4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U48_entry4_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U48_entry5_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U48_entry5_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U49_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U49_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U51_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U51_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U52_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U52_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U55_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U55_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U57_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U57_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U60_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U60_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U61_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U61_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U63_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U63_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U64_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U64_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U67_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U67_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U69_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U69_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U7_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U7_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U72_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U72_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U73_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U73_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U75_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U75_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U76_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U76_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U79_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U79_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U81_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U81_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U84_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U84_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U85_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U85_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U87_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U87_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U88_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U88_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U9_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U9_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U91_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U91_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U93_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U93_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U96_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U96_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U97_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U97_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U99_wuminus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_U99_wuplus_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_centralIndex_injective_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectminus_norm_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectplus_norm_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_qiBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_S_apply_e
import Theorems.Thm_OAI_SharpPlanar_finiteRestriction_apply_e
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_e

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

namespace SharpPlanar
namespace IntegerIntervals

lemma precision_pos : (0:ℝ) < precision := by norm_num [precision]

end IntegerIntervals
end SharpPlanar

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
lemma amp0_10_0_eq : ∀ k : Fin 16, amp0_1Expr 0 0 k = amp0_10_0 k := by decide +kernel
lemma amp0_10_1_eq : ∀ k : Fin 16, amp0_1Expr 0 1 k = amp0_10_1 k := by decide +kernel
lemma amp0_10_2_eq : ∀ k : Fin 16, amp0_1Expr 0 2 k = amp0_10_2 k := by decide +kernel
lemma amp0_10_3_eq : ∀ k : Fin 16, amp0_1Expr 0 3 k = amp0_10_3 k := by decide +kernel
lemma amp0_10_4_eq : ∀ k : Fin 16, amp0_1Expr 0 4 k = amp0_10_4 k := by decide +kernel
lemma amp0_10_5_eq : ∀ k : Fin 16, amp0_1Expr 0 5 k = amp0_10_5 k := by decide +kernel
lemma amp0_10_6_eq : ∀ k : Fin 16, amp0_1Expr 0 6 k = amp0_10_6 k := by decide +kernel
lemma amp0_10_7_eq : ∀ k : Fin 16, amp0_1Expr 0 7 k = amp0_10_7 k := by decide +kernel
lemma amp0_10_8_eq : ∀ k : Fin 16, amp0_1Expr 0 8 k = amp0_10_8 k := by decide +kernel
lemma amp0_10_9_eq : ∀ k : Fin 16, amp0_1Expr 0 9 k = amp0_10_9 k := by decide +kernel
lemma amp0_10_10_eq : ∀ k : Fin 16, amp0_1Expr 0 10 k = amp0_10_10 k := by decide +kernel
lemma amp0_10_11_eq : ∀ k : Fin 16, amp0_1Expr 0 11 k = amp0_10_11 k := by decide +kernel
lemma amp0_10_12_eq : ∀ k : Fin 16, amp0_1Expr 0 12 k = amp0_10_12 k := by decide +kernel
lemma amp0_10_13_eq : ∀ k : Fin 16, amp0_1Expr 0 13 k = amp0_10_13 k := by decide +kernel
lemma amp0_10_14_eq : ∀ k : Fin 16, amp0_1Expr 0 14 k = amp0_10_14 k := by decide +kernel
lemma amp0_10_15_eq : ∀ k : Fin 16, amp0_1Expr 0 15 k = amp0_10_15 k := by decide +kernel
lemma amp0_10_eq (i k : Fin 16) : amp0_1Expr 0 i k = amp0_10 i k := by
  fin_cases i
  · exact amp0_10_0_eq k
  · exact amp0_10_1_eq k
  · exact amp0_10_2_eq k
  · exact amp0_10_3_eq k
  · exact amp0_10_4_eq k
  · exact amp0_10_5_eq k
  · exact amp0_10_6_eq k
  · exact amp0_10_7_eq k
  · exact amp0_10_8_eq k
  · exact amp0_10_9_eq k
  · exact amp0_10_10_eq k
  · exact amp0_10_11_eq k
  · exact amp0_10_12_eq k
  · exact amp0_10_13_eq k
  · exact amp0_10_14_eq k
  · exact amp0_10_15_eq k
lemma amp0_11_0_eq : ∀ k : Fin 16, amp0_1Expr 1 0 k = amp0_11_0 k := by decide +kernel
lemma amp0_11_1_eq : ∀ k : Fin 16, amp0_1Expr 1 1 k = amp0_11_1 k := by decide +kernel
lemma amp0_11_2_eq : ∀ k : Fin 16, amp0_1Expr 1 2 k = amp0_11_2 k := by decide +kernel
lemma amp0_11_3_eq : ∀ k : Fin 16, amp0_1Expr 1 3 k = amp0_11_3 k := by decide +kernel
lemma amp0_11_4_eq : ∀ k : Fin 16, amp0_1Expr 1 4 k = amp0_11_4 k := by decide +kernel
lemma amp0_11_5_eq : ∀ k : Fin 16, amp0_1Expr 1 5 k = amp0_11_5 k := by decide +kernel
lemma amp0_11_6_eq : ∀ k : Fin 16, amp0_1Expr 1 6 k = amp0_11_6 k := by decide +kernel
lemma amp0_11_7_eq : ∀ k : Fin 16, amp0_1Expr 1 7 k = amp0_11_7 k := by decide +kernel
lemma amp0_11_8_eq : ∀ k : Fin 16, amp0_1Expr 1 8 k = amp0_11_8 k := by decide +kernel
lemma amp0_11_9_eq : ∀ k : Fin 16, amp0_1Expr 1 9 k = amp0_11_9 k := by decide +kernel
lemma amp0_11_10_eq : ∀ k : Fin 16, amp0_1Expr 1 10 k = amp0_11_10 k := by decide +kernel
lemma amp0_11_11_eq : ∀ k : Fin 16, amp0_1Expr 1 11 k = amp0_11_11 k := by decide +kernel
lemma amp0_11_12_eq : ∀ k : Fin 16, amp0_1Expr 1 12 k = amp0_11_12 k := by decide +kernel
lemma amp0_11_13_eq : ∀ k : Fin 16, amp0_1Expr 1 13 k = amp0_11_13 k := by decide +kernel
lemma amp0_11_14_eq : ∀ k : Fin 16, amp0_1Expr 1 14 k = amp0_11_14 k := by decide +kernel
lemma amp0_11_15_eq : ∀ k : Fin 16, amp0_1Expr 1 15 k = amp0_11_15 k := by decide +kernel
lemma amp0_11_eq (i k : Fin 16) : amp0_1Expr 1 i k = amp0_11 i k := by
  fin_cases i
  · exact amp0_11_0_eq k
  · exact amp0_11_1_eq k
  · exact amp0_11_2_eq k
  · exact amp0_11_3_eq k
  · exact amp0_11_4_eq k
  · exact amp0_11_5_eq k
  · exact amp0_11_6_eq k
  · exact amp0_11_7_eq k
  · exact amp0_11_8_eq k
  · exact amp0_11_9_eq k
  · exact amp0_11_10_eq k
  · exact amp0_11_11_eq k
  · exact amp0_11_12_eq k
  · exact amp0_11_13_eq k
  · exact amp0_11_14_eq k
  · exact amp0_11_15_eq k
lemma amp0_12_0_eq : ∀ k : Fin 16, amp0_1Expr 2 0 k = amp0_12_0 k := by decide +kernel
lemma amp0_12_1_eq : ∀ k : Fin 16, amp0_1Expr 2 1 k = amp0_12_1 k := by decide +kernel
lemma amp0_12_2_eq : ∀ k : Fin 16, amp0_1Expr 2 2 k = amp0_12_2 k := by decide +kernel
lemma amp0_12_3_eq : ∀ k : Fin 16, amp0_1Expr 2 3 k = amp0_12_3 k := by decide +kernel
lemma amp0_12_4_eq : ∀ k : Fin 16, amp0_1Expr 2 4 k = amp0_12_4 k := by decide +kernel
lemma amp0_12_5_eq : ∀ k : Fin 16, amp0_1Expr 2 5 k = amp0_12_5 k := by decide +kernel
lemma amp0_12_6_eq : ∀ k : Fin 16, amp0_1Expr 2 6 k = amp0_12_6 k := by decide +kernel
lemma amp0_12_7_eq : ∀ k : Fin 16, amp0_1Expr 2 7 k = amp0_12_7 k := by decide +kernel
lemma amp0_12_8_eq : ∀ k : Fin 16, amp0_1Expr 2 8 k = amp0_12_8 k := by decide +kernel
lemma amp0_12_9_eq : ∀ k : Fin 16, amp0_1Expr 2 9 k = amp0_12_9 k := by decide +kernel
lemma amp0_12_10_eq : ∀ k : Fin 16, amp0_1Expr 2 10 k = amp0_12_10 k := by decide +kernel
lemma amp0_12_11_eq : ∀ k : Fin 16, amp0_1Expr 2 11 k = amp0_12_11 k := by decide +kernel
lemma amp0_12_12_eq : ∀ k : Fin 16, amp0_1Expr 2 12 k = amp0_12_12 k := by decide +kernel
lemma amp0_12_13_eq : ∀ k : Fin 16, amp0_1Expr 2 13 k = amp0_12_13 k := by decide +kernel
lemma amp0_12_14_eq : ∀ k : Fin 16, amp0_1Expr 2 14 k = amp0_12_14 k := by decide +kernel
lemma amp0_12_15_eq : ∀ k : Fin 16, amp0_1Expr 2 15 k = amp0_12_15 k := by decide +kernel
lemma amp0_12_eq (i k : Fin 16) : amp0_1Expr 2 i k = amp0_12 i k := by
  fin_cases i
  · exact amp0_12_0_eq k
  · exact amp0_12_1_eq k
  · exact amp0_12_2_eq k
  · exact amp0_12_3_eq k
  · exact amp0_12_4_eq k
  · exact amp0_12_5_eq k
  · exact amp0_12_6_eq k
  · exact amp0_12_7_eq k
  · exact amp0_12_8_eq k
  · exact amp0_12_9_eq k
  · exact amp0_12_10_eq k
  · exact amp0_12_11_eq k
  · exact amp0_12_12_eq k
  · exact amp0_12_13_eq k
  · exact amp0_12_14_eq k
  · exact amp0_12_15_eq k
lemma amp0_13_0_eq : ∀ k : Fin 16, amp0_1Expr 3 0 k = amp0_13_0 k := by decide +kernel
lemma amp0_13_1_eq : ∀ k : Fin 16, amp0_1Expr 3 1 k = amp0_13_1 k := by decide +kernel
lemma amp0_13_2_eq : ∀ k : Fin 16, amp0_1Expr 3 2 k = amp0_13_2 k := by decide +kernel
lemma amp0_13_3_eq : ∀ k : Fin 16, amp0_1Expr 3 3 k = amp0_13_3 k := by decide +kernel
lemma amp0_13_4_eq : ∀ k : Fin 16, amp0_1Expr 3 4 k = amp0_13_4 k := by decide +kernel
lemma amp0_13_5_eq : ∀ k : Fin 16, amp0_1Expr 3 5 k = amp0_13_5 k := by decide +kernel
lemma amp0_13_6_eq : ∀ k : Fin 16, amp0_1Expr 3 6 k = amp0_13_6 k := by decide +kernel
lemma amp0_13_7_eq : ∀ k : Fin 16, amp0_1Expr 3 7 k = amp0_13_7 k := by decide +kernel
lemma amp0_13_8_eq : ∀ k : Fin 16, amp0_1Expr 3 8 k = amp0_13_8 k := by decide +kernel
lemma amp0_13_9_eq : ∀ k : Fin 16, amp0_1Expr 3 9 k = amp0_13_9 k := by decide +kernel
lemma amp0_13_10_eq : ∀ k : Fin 16, amp0_1Expr 3 10 k = amp0_13_10 k := by decide +kernel
lemma amp0_13_11_eq : ∀ k : Fin 16, amp0_1Expr 3 11 k = amp0_13_11 k := by decide +kernel
lemma amp0_13_12_eq : ∀ k : Fin 16, amp0_1Expr 3 12 k = amp0_13_12 k := by decide +kernel
lemma amp0_13_13_eq : ∀ k : Fin 16, amp0_1Expr 3 13 k = amp0_13_13 k := by decide +kernel
lemma amp0_13_14_eq : ∀ k : Fin 16, amp0_1Expr 3 14 k = amp0_13_14 k := by decide +kernel
lemma amp0_13_15_eq : ∀ k : Fin 16, amp0_1Expr 3 15 k = amp0_13_15 k := by decide +kernel
lemma amp0_13_eq (i k : Fin 16) : amp0_1Expr 3 i k = amp0_13 i k := by
  fin_cases i
  · exact amp0_13_0_eq k
  · exact amp0_13_1_eq k
  · exact amp0_13_2_eq k
  · exact amp0_13_3_eq k
  · exact amp0_13_4_eq k
  · exact amp0_13_5_eq k
  · exact amp0_13_6_eq k
  · exact amp0_13_7_eq k
  · exact amp0_13_8_eq k
  · exact amp0_13_9_eq k
  · exact amp0_13_10_eq k
  · exact amp0_13_11_eq k
  · exact amp0_13_12_eq k
  · exact amp0_13_13_eq k
  · exact amp0_13_14_eq k
  · exact amp0_13_15_eq k
lemma amp0_14_0_eq : ∀ k : Fin 16, amp0_1Expr 4 0 k = amp0_14_0 k := by decide +kernel
lemma amp0_14_1_eq : ∀ k : Fin 16, amp0_1Expr 4 1 k = amp0_14_1 k := by decide +kernel
lemma amp0_14_2_eq : ∀ k : Fin 16, amp0_1Expr 4 2 k = amp0_14_2 k := by decide +kernel
lemma amp0_14_3_eq : ∀ k : Fin 16, amp0_1Expr 4 3 k = amp0_14_3 k := by decide +kernel
lemma amp0_14_4_eq : ∀ k : Fin 16, amp0_1Expr 4 4 k = amp0_14_4 k := by decide +kernel
lemma amp0_14_5_eq : ∀ k : Fin 16, amp0_1Expr 4 5 k = amp0_14_5 k := by decide +kernel
lemma amp0_14_6_eq : ∀ k : Fin 16, amp0_1Expr 4 6 k = amp0_14_6 k := by decide +kernel
lemma amp0_14_7_eq : ∀ k : Fin 16, amp0_1Expr 4 7 k = amp0_14_7 k := by decide +kernel
lemma amp0_14_8_eq : ∀ k : Fin 16, amp0_1Expr 4 8 k = amp0_14_8 k := by decide +kernel
lemma amp0_14_9_eq : ∀ k : Fin 16, amp0_1Expr 4 9 k = amp0_14_9 k := by decide +kernel
lemma amp0_14_10_eq : ∀ k : Fin 16, amp0_1Expr 4 10 k = amp0_14_10 k := by decide +kernel
lemma amp0_14_11_eq : ∀ k : Fin 16, amp0_1Expr 4 11 k = amp0_14_11 k := by decide +kernel
lemma amp0_14_12_eq : ∀ k : Fin 16, amp0_1Expr 4 12 k = amp0_14_12 k := by decide +kernel
lemma amp0_14_13_eq : ∀ k : Fin 16, amp0_1Expr 4 13 k = amp0_14_13 k := by decide +kernel
lemma amp0_14_14_eq : ∀ k : Fin 16, amp0_1Expr 4 14 k = amp0_14_14 k := by decide +kernel
lemma amp0_14_15_eq : ∀ k : Fin 16, amp0_1Expr 4 15 k = amp0_14_15 k := by decide +kernel
lemma amp0_14_eq (i k : Fin 16) : amp0_1Expr 4 i k = amp0_14 i k := by
  fin_cases i
  · exact amp0_14_0_eq k
  · exact amp0_14_1_eq k
  · exact amp0_14_2_eq k
  · exact amp0_14_3_eq k
  · exact amp0_14_4_eq k
  · exact amp0_14_5_eq k
  · exact amp0_14_6_eq k
  · exact amp0_14_7_eq k
  · exact amp0_14_8_eq k
  · exact amp0_14_9_eq k
  · exact amp0_14_10_eq k
  · exact amp0_14_11_eq k
  · exact amp0_14_12_eq k
  · exact amp0_14_13_eq k
  · exact amp0_14_14_eq k
  · exact amp0_14_15_eq k
lemma amp0_15_0_eq : ∀ k : Fin 16, amp0_1Expr 5 0 k = amp0_15_0 k := by decide +kernel
lemma amp0_15_1_eq : ∀ k : Fin 16, amp0_1Expr 5 1 k = amp0_15_1 k := by decide +kernel
lemma amp0_15_2_eq : ∀ k : Fin 16, amp0_1Expr 5 2 k = amp0_15_2 k := by decide +kernel
lemma amp0_15_3_eq : ∀ k : Fin 16, amp0_1Expr 5 3 k = amp0_15_3 k := by decide +kernel
lemma amp0_15_4_eq : ∀ k : Fin 16, amp0_1Expr 5 4 k = amp0_15_4 k := by decide +kernel
lemma amp0_15_5_eq : ∀ k : Fin 16, amp0_1Expr 5 5 k = amp0_15_5 k := by decide +kernel
lemma amp0_15_6_eq : ∀ k : Fin 16, amp0_1Expr 5 6 k = amp0_15_6 k := by decide +kernel
lemma amp0_15_7_eq : ∀ k : Fin 16, amp0_1Expr 5 7 k = amp0_15_7 k := by decide +kernel
lemma amp0_15_8_eq : ∀ k : Fin 16, amp0_1Expr 5 8 k = amp0_15_8 k := by decide +kernel
lemma amp0_15_9_eq : ∀ k : Fin 16, amp0_1Expr 5 9 k = amp0_15_9 k := by decide +kernel
lemma amp0_15_10_eq : ∀ k : Fin 16, amp0_1Expr 5 10 k = amp0_15_10 k := by decide +kernel
lemma amp0_15_11_eq : ∀ k : Fin 16, amp0_1Expr 5 11 k = amp0_15_11 k := by decide +kernel
lemma amp0_15_12_eq : ∀ k : Fin 16, amp0_1Expr 5 12 k = amp0_15_12 k := by decide +kernel
lemma amp0_15_13_eq : ∀ k : Fin 16, amp0_1Expr 5 13 k = amp0_15_13 k := by decide +kernel
lemma amp0_15_14_eq : ∀ k : Fin 16, amp0_1Expr 5 14 k = amp0_15_14 k := by decide +kernel
lemma amp0_15_15_eq : ∀ k : Fin 16, amp0_1Expr 5 15 k = amp0_15_15 k := by decide +kernel
lemma amp0_15_eq (i k : Fin 16) : amp0_1Expr 5 i k = amp0_15 i k := by
  fin_cases i
  · exact amp0_15_0_eq k
  · exact amp0_15_1_eq k
  · exact amp0_15_2_eq k
  · exact amp0_15_3_eq k
  · exact amp0_15_4_eq k
  · exact amp0_15_5_eq k
  · exact amp0_15_6_eq k
  · exact amp0_15_7_eq k
  · exact amp0_15_8_eq k
  · exact amp0_15_9_eq k
  · exact amp0_15_10_eq k
  · exact amp0_15_11_eq k
  · exact amp0_15_12_eq k
  · exact amp0_15_13_eq k
  · exact amp0_15_14_eq k
  · exact amp0_15_15_eq k
lemma amp0_1_eq (j : Fin 6) (i k : Fin 16) : amp0_1Expr j i k = amp0_1 j i k := by
  fin_cases j
  · exact amp0_10_eq i k
  · exact amp0_11_eq i k
  · exact amp0_12_eq i k
  · exact amp0_13_eq i k
  · exact amp0_14_eq i k
  · exact amp0_15_eq i k
lemma amp0_1_contains (j : Fin 6) (i k : Fin 16) :
    (amp0_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*waveAmplitude true 0 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← amp0_1_eq]
  exact CBox.contains_mul_e (rcast_contains_e (weightRows_contains_e i k))
    (waveAmplitudeBox_contains_e (gridRows_contains_e j i k) (aLookup_contains 0 j) (bLookup_contains 0 j) true)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns50
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
lemma column48_1_r0_0_eq : ∀ k : Fin 16, column48_1Expr 0 0 k = column48_1_r0_0 k := by decide +kernel
lemma column48_1_r0_1_eq : ∀ k : Fin 16, column48_1Expr 0 1 k = column48_1_r0_1 k := by decide +kernel
lemma column48_1_r0_2_eq : ∀ k : Fin 16, column48_1Expr 0 2 k = column48_1_r0_2 k := by decide +kernel
lemma column48_1_r0_3_eq : ∀ k : Fin 16, column48_1Expr 0 3 k = column48_1_r0_3 k := by decide +kernel
lemma column48_1_r0_4_eq : ∀ k : Fin 16, column48_1Expr 0 4 k = column48_1_r0_4 k := by decide +kernel
lemma column48_1_r0_5_eq : ∀ k : Fin 16, column48_1Expr 0 5 k = column48_1_r0_5 k := by decide +kernel
lemma column48_1_r0_6_eq : ∀ k : Fin 16, column48_1Expr 0 6 k = column48_1_r0_6 k := by decide +kernel
lemma column48_1_r0_7_eq : ∀ k : Fin 16, column48_1Expr 0 7 k = column48_1_r0_7 k := by decide +kernel
lemma column48_1_r0_8_eq : ∀ k : Fin 16, column48_1Expr 0 8 k = column48_1_r0_8 k := by decide +kernel
lemma column48_1_r0_9_eq : ∀ k : Fin 16, column48_1Expr 0 9 k = column48_1_r0_9 k := by decide +kernel
lemma column48_1_r0_10_eq : ∀ k : Fin 16, column48_1Expr 0 10 k = column48_1_r0_10 k := by decide +kernel
lemma column48_1_r0_11_eq : ∀ k : Fin 16, column48_1Expr 0 11 k = column48_1_r0_11 k := by decide +kernel
lemma column48_1_r0_12_eq : ∀ k : Fin 16, column48_1Expr 0 12 k = column48_1_r0_12 k := by decide +kernel
lemma column48_1_r0_13_eq : ∀ k : Fin 16, column48_1Expr 0 13 k = column48_1_r0_13 k := by decide +kernel
lemma column48_1_r0_14_eq : ∀ k : Fin 16, column48_1Expr 0 14 k = column48_1_r0_14 k := by decide +kernel
lemma column48_1_r0_15_eq : ∀ k : Fin 16, column48_1Expr 0 15 k = column48_1_r0_15 k := by decide +kernel
lemma column48_1_r0_eq (i k : Fin 16) : column48_1Expr 0 i k = column48_1_r0 i k := by
  fin_cases i
  · exact column48_1_r0_0_eq k
  · exact column48_1_r0_1_eq k
  · exact column48_1_r0_2_eq k
  · exact column48_1_r0_3_eq k
  · exact column48_1_r0_4_eq k
  · exact column48_1_r0_5_eq k
  · exact column48_1_r0_6_eq k
  · exact column48_1_r0_7_eq k
  · exact column48_1_r0_8_eq k
  · exact column48_1_r0_9_eq k
  · exact column48_1_r0_10_eq k
  · exact column48_1_r0_11_eq k
  · exact column48_1_r0_12_eq k
  · exact column48_1_r0_13_eq k
  · exact column48_1_r0_14_eq k
  · exact column48_1_r0_15_eq k
lemma column48_1_r1_0_eq : ∀ k : Fin 16, column48_1Expr 1 0 k = column48_1_r1_0 k := by decide +kernel
lemma column48_1_r1_1_eq : ∀ k : Fin 16, column48_1Expr 1 1 k = column48_1_r1_1 k := by decide +kernel
lemma column48_1_r1_2_eq : ∀ k : Fin 16, column48_1Expr 1 2 k = column48_1_r1_2 k := by decide +kernel
lemma column48_1_r1_3_eq : ∀ k : Fin 16, column48_1Expr 1 3 k = column48_1_r1_3 k := by decide +kernel
lemma column48_1_r1_4_eq : ∀ k : Fin 16, column48_1Expr 1 4 k = column48_1_r1_4 k := by decide +kernel
lemma column48_1_r1_5_eq : ∀ k : Fin 16, column48_1Expr 1 5 k = column48_1_r1_5 k := by decide +kernel
lemma column48_1_r1_6_eq : ∀ k : Fin 16, column48_1Expr 1 6 k = column48_1_r1_6 k := by decide +kernel
lemma column48_1_r1_7_eq : ∀ k : Fin 16, column48_1Expr 1 7 k = column48_1_r1_7 k := by decide +kernel
lemma column48_1_r1_8_eq : ∀ k : Fin 16, column48_1Expr 1 8 k = column48_1_r1_8 k := by decide +kernel
lemma column48_1_r1_9_eq : ∀ k : Fin 16, column48_1Expr 1 9 k = column48_1_r1_9 k := by decide +kernel
lemma column48_1_r1_10_eq : ∀ k : Fin 16, column48_1Expr 1 10 k = column48_1_r1_10 k := by decide +kernel
lemma column48_1_r1_11_eq : ∀ k : Fin 16, column48_1Expr 1 11 k = column48_1_r1_11 k := by decide +kernel
lemma column48_1_r1_12_eq : ∀ k : Fin 16, column48_1Expr 1 12 k = column48_1_r1_12 k := by decide +kernel
lemma column48_1_r1_13_eq : ∀ k : Fin 16, column48_1Expr 1 13 k = column48_1_r1_13 k := by decide +kernel
lemma column48_1_r1_14_eq : ∀ k : Fin 16, column48_1Expr 1 14 k = column48_1_r1_14 k := by decide +kernel
lemma column48_1_r1_15_eq : ∀ k : Fin 16, column48_1Expr 1 15 k = column48_1_r1_15 k := by decide +kernel
lemma column48_1_r1_eq (i k : Fin 16) : column48_1Expr 1 i k = column48_1_r1 i k := by
  fin_cases i
  · exact column48_1_r1_0_eq k
  · exact column48_1_r1_1_eq k
  · exact column48_1_r1_2_eq k
  · exact column48_1_r1_3_eq k
  · exact column48_1_r1_4_eq k
  · exact column48_1_r1_5_eq k
  · exact column48_1_r1_6_eq k
  · exact column48_1_r1_7_eq k
  · exact column48_1_r1_8_eq k
  · exact column48_1_r1_9_eq k
  · exact column48_1_r1_10_eq k
  · exact column48_1_r1_11_eq k
  · exact column48_1_r1_12_eq k
  · exact column48_1_r1_13_eq k
  · exact column48_1_r1_14_eq k
  · exact column48_1_r1_15_eq k
lemma column48_1_r2_0_eq : ∀ k : Fin 16, column48_1Expr 2 0 k = column48_1_r2_0 k := by decide +kernel
lemma column48_1_r2_1_eq : ∀ k : Fin 16, column48_1Expr 2 1 k = column48_1_r2_1 k := by decide +kernel
lemma column48_1_r2_2_eq : ∀ k : Fin 16, column48_1Expr 2 2 k = column48_1_r2_2 k := by decide +kernel
lemma column48_1_r2_3_eq : ∀ k : Fin 16, column48_1Expr 2 3 k = column48_1_r2_3 k := by decide +kernel
lemma column48_1_r2_4_eq : ∀ k : Fin 16, column48_1Expr 2 4 k = column48_1_r2_4 k := by decide +kernel
lemma column48_1_r2_5_eq : ∀ k : Fin 16, column48_1Expr 2 5 k = column48_1_r2_5 k := by decide +kernel
lemma column48_1_r2_6_eq : ∀ k : Fin 16, column48_1Expr 2 6 k = column48_1_r2_6 k := by decide +kernel
lemma column48_1_r2_7_eq : ∀ k : Fin 16, column48_1Expr 2 7 k = column48_1_r2_7 k := by decide +kernel
lemma column48_1_r2_8_eq : ∀ k : Fin 16, column48_1Expr 2 8 k = column48_1_r2_8 k := by decide +kernel
lemma column48_1_r2_9_eq : ∀ k : Fin 16, column48_1Expr 2 9 k = column48_1_r2_9 k := by decide +kernel
lemma column48_1_r2_10_eq : ∀ k : Fin 16, column48_1Expr 2 10 k = column48_1_r2_10 k := by decide +kernel
lemma column48_1_r2_11_eq : ∀ k : Fin 16, column48_1Expr 2 11 k = column48_1_r2_11 k := by decide +kernel
lemma column48_1_r2_12_eq : ∀ k : Fin 16, column48_1Expr 2 12 k = column48_1_r2_12 k := by decide +kernel
lemma column48_1_r2_13_eq : ∀ k : Fin 16, column48_1Expr 2 13 k = column48_1_r2_13 k := by decide +kernel
lemma column48_1_r2_14_eq : ∀ k : Fin 16, column48_1Expr 2 14 k = column48_1_r2_14 k := by decide +kernel
lemma column48_1_r2_15_eq : ∀ k : Fin 16, column48_1Expr 2 15 k = column48_1_r2_15 k := by decide +kernel
lemma column48_1_r2_eq (i k : Fin 16) : column48_1Expr 2 i k = column48_1_r2 i k := by
  fin_cases i
  · exact column48_1_r2_0_eq k
  · exact column48_1_r2_1_eq k
  · exact column48_1_r2_2_eq k
  · exact column48_1_r2_3_eq k
  · exact column48_1_r2_4_eq k
  · exact column48_1_r2_5_eq k
  · exact column48_1_r2_6_eq k
  · exact column48_1_r2_7_eq k
  · exact column48_1_r2_8_eq k
  · exact column48_1_r2_9_eq k
  · exact column48_1_r2_10_eq k
  · exact column48_1_r2_11_eq k
  · exact column48_1_r2_12_eq k
  · exact column48_1_r2_13_eq k
  · exact column48_1_r2_14_eq k
  · exact column48_1_r2_15_eq k
lemma column48_1_r3_0_eq : ∀ k : Fin 16, column48_1Expr 3 0 k = column48_1_r3_0 k := by decide +kernel
lemma column48_1_r3_1_eq : ∀ k : Fin 16, column48_1Expr 3 1 k = column48_1_r3_1 k := by decide +kernel
lemma column48_1_r3_2_eq : ∀ k : Fin 16, column48_1Expr 3 2 k = column48_1_r3_2 k := by decide +kernel
lemma column48_1_r3_3_eq : ∀ k : Fin 16, column48_1Expr 3 3 k = column48_1_r3_3 k := by decide +kernel
lemma column48_1_r3_4_eq : ∀ k : Fin 16, column48_1Expr 3 4 k = column48_1_r3_4 k := by decide +kernel
lemma column48_1_r3_5_eq : ∀ k : Fin 16, column48_1Expr 3 5 k = column48_1_r3_5 k := by decide +kernel
lemma column48_1_r3_6_eq : ∀ k : Fin 16, column48_1Expr 3 6 k = column48_1_r3_6 k := by decide +kernel
lemma column48_1_r3_7_eq : ∀ k : Fin 16, column48_1Expr 3 7 k = column48_1_r3_7 k := by decide +kernel
lemma column48_1_r3_8_eq : ∀ k : Fin 16, column48_1Expr 3 8 k = column48_1_r3_8 k := by decide +kernel
lemma column48_1_r3_9_eq : ∀ k : Fin 16, column48_1Expr 3 9 k = column48_1_r3_9 k := by decide +kernel
lemma column48_1_r3_10_eq : ∀ k : Fin 16, column48_1Expr 3 10 k = column48_1_r3_10 k := by decide +kernel
lemma column48_1_r3_11_eq : ∀ k : Fin 16, column48_1Expr 3 11 k = column48_1_r3_11 k := by decide +kernel
lemma column48_1_r3_12_eq : ∀ k : Fin 16, column48_1Expr 3 12 k = column48_1_r3_12 k := by decide +kernel
lemma column48_1_r3_13_eq : ∀ k : Fin 16, column48_1Expr 3 13 k = column48_1_r3_13 k := by decide +kernel
lemma column48_1_r3_14_eq : ∀ k : Fin 16, column48_1Expr 3 14 k = column48_1_r3_14 k := by decide +kernel
lemma column48_1_r3_15_eq : ∀ k : Fin 16, column48_1Expr 3 15 k = column48_1_r3_15 k := by decide +kernel
lemma column48_1_r3_eq (i k : Fin 16) : column48_1Expr 3 i k = column48_1_r3 i k := by
  fin_cases i
  · exact column48_1_r3_0_eq k
  · exact column48_1_r3_1_eq k
  · exact column48_1_r3_2_eq k
  · exact column48_1_r3_3_eq k
  · exact column48_1_r3_4_eq k
  · exact column48_1_r3_5_eq k
  · exact column48_1_r3_6_eq k
  · exact column48_1_r3_7_eq k
  · exact column48_1_r3_8_eq k
  · exact column48_1_r3_9_eq k
  · exact column48_1_r3_10_eq k
  · exact column48_1_r3_11_eq k
  · exact column48_1_r3_12_eq k
  · exact column48_1_r3_13_eq k
  · exact column48_1_r3_14_eq k
  · exact column48_1_r3_15_eq k
lemma column48_1_r4_0_eq : ∀ k : Fin 16, column48_1Expr 4 0 k = column48_1_r4_0 k := by decide +kernel
lemma column48_1_r4_1_eq : ∀ k : Fin 16, column48_1Expr 4 1 k = column48_1_r4_1 k := by decide +kernel
lemma column48_1_r4_2_eq : ∀ k : Fin 16, column48_1Expr 4 2 k = column48_1_r4_2 k := by decide +kernel
lemma column48_1_r4_3_eq : ∀ k : Fin 16, column48_1Expr 4 3 k = column48_1_r4_3 k := by decide +kernel
lemma column48_1_r4_4_eq : ∀ k : Fin 16, column48_1Expr 4 4 k = column48_1_r4_4 k := by decide +kernel
lemma column48_1_r4_5_eq : ∀ k : Fin 16, column48_1Expr 4 5 k = column48_1_r4_5 k := by decide +kernel
lemma column48_1_r4_6_eq : ∀ k : Fin 16, column48_1Expr 4 6 k = column48_1_r4_6 k := by decide +kernel
lemma column48_1_r4_7_eq : ∀ k : Fin 16, column48_1Expr 4 7 k = column48_1_r4_7 k := by decide +kernel
lemma column48_1_r4_8_eq : ∀ k : Fin 16, column48_1Expr 4 8 k = column48_1_r4_8 k := by decide +kernel
lemma column48_1_r4_9_eq : ∀ k : Fin 16, column48_1Expr 4 9 k = column48_1_r4_9 k := by decide +kernel
lemma column48_1_r4_10_eq : ∀ k : Fin 16, column48_1Expr 4 10 k = column48_1_r4_10 k := by decide +kernel
lemma column48_1_r4_11_eq : ∀ k : Fin 16, column48_1Expr 4 11 k = column48_1_r4_11 k := by decide +kernel
lemma column48_1_r4_12_eq : ∀ k : Fin 16, column48_1Expr 4 12 k = column48_1_r4_12 k := by decide +kernel
lemma column48_1_r4_13_eq : ∀ k : Fin 16, column48_1Expr 4 13 k = column48_1_r4_13 k := by decide +kernel
lemma column48_1_r4_14_eq : ∀ k : Fin 16, column48_1Expr 4 14 k = column48_1_r4_14 k := by decide +kernel
lemma column48_1_r4_15_eq : ∀ k : Fin 16, column48_1Expr 4 15 k = column48_1_r4_15 k := by decide +kernel
lemma column48_1_r4_eq (i k : Fin 16) : column48_1Expr 4 i k = column48_1_r4 i k := by
  fin_cases i
  · exact column48_1_r4_0_eq k
  · exact column48_1_r4_1_eq k
  · exact column48_1_r4_2_eq k
  · exact column48_1_r4_3_eq k
  · exact column48_1_r4_4_eq k
  · exact column48_1_r4_5_eq k
  · exact column48_1_r4_6_eq k
  · exact column48_1_r4_7_eq k
  · exact column48_1_r4_8_eq k
  · exact column48_1_r4_9_eq k
  · exact column48_1_r4_10_eq k
  · exact column48_1_r4_11_eq k
  · exact column48_1_r4_12_eq k
  · exact column48_1_r4_13_eq k
  · exact column48_1_r4_14_eq k
  · exact column48_1_r4_15_eq k
lemma column48_1_r5_0_eq : ∀ k : Fin 16, column48_1Expr 5 0 k = column48_1_r5_0 k := by decide +kernel
lemma column48_1_r5_1_eq : ∀ k : Fin 16, column48_1Expr 5 1 k = column48_1_r5_1 k := by decide +kernel
lemma column48_1_r5_2_eq : ∀ k : Fin 16, column48_1Expr 5 2 k = column48_1_r5_2 k := by decide +kernel
lemma column48_1_r5_3_eq : ∀ k : Fin 16, column48_1Expr 5 3 k = column48_1_r5_3 k := by decide +kernel
lemma column48_1_r5_4_eq : ∀ k : Fin 16, column48_1Expr 5 4 k = column48_1_r5_4 k := by decide +kernel
lemma column48_1_r5_5_eq : ∀ k : Fin 16, column48_1Expr 5 5 k = column48_1_r5_5 k := by decide +kernel
lemma column48_1_r5_6_eq : ∀ k : Fin 16, column48_1Expr 5 6 k = column48_1_r5_6 k := by decide +kernel
lemma column48_1_r5_7_eq : ∀ k : Fin 16, column48_1Expr 5 7 k = column48_1_r5_7 k := by decide +kernel
lemma column48_1_r5_8_eq : ∀ k : Fin 16, column48_1Expr 5 8 k = column48_1_r5_8 k := by decide +kernel
lemma column48_1_r5_9_eq : ∀ k : Fin 16, column48_1Expr 5 9 k = column48_1_r5_9 k := by decide +kernel
lemma column48_1_r5_10_eq : ∀ k : Fin 16, column48_1Expr 5 10 k = column48_1_r5_10 k := by decide +kernel
lemma column48_1_r5_11_eq : ∀ k : Fin 16, column48_1Expr 5 11 k = column48_1_r5_11 k := by decide +kernel
lemma column48_1_r5_12_eq : ∀ k : Fin 16, column48_1Expr 5 12 k = column48_1_r5_12 k := by decide +kernel
lemma column48_1_r5_13_eq : ∀ k : Fin 16, column48_1Expr 5 13 k = column48_1_r5_13 k := by decide +kernel
lemma column48_1_r5_14_eq : ∀ k : Fin 16, column48_1Expr 5 14 k = column48_1_r5_14 k := by decide +kernel
lemma column48_1_r5_15_eq : ∀ k : Fin 16, column48_1Expr 5 15 k = column48_1_r5_15 k := by decide +kernel
lemma column48_1_r5_eq (i k : Fin 16) : column48_1Expr 5 i k = column48_1_r5 i k := by
  fin_cases i
  · exact column48_1_r5_0_eq k
  · exact column48_1_r5_1_eq k
  · exact column48_1_r5_2_eq k
  · exact column48_1_r5_3_eq k
  · exact column48_1_r5_4_eq k
  · exact column48_1_r5_5_eq k
  · exact column48_1_r5_6_eq k
  · exact column48_1_r5_7_eq k
  · exact column48_1_r5_8_eq k
  · exact column48_1_r5_9_eq k
  · exact column48_1_r5_10_eq k
  · exact column48_1_r5_11_eq k
  · exact column48_1_r5_12_eq k
  · exact column48_1_r5_13_eq k
  · exact column48_1_r5_14_eq k
  · exact column48_1_r5_15_eq k
lemma column48_1_eq (j : Fin 6) (i k : Fin 16) : column48_1Expr j i k = column48_1 j i k := by
  fin_cases j
  · exact column48_1_r0_eq i k
  · exact column48_1_r1_eq i k
  · exact column48_1_r2_eq i k
  · exact column48_1_r3_eq i k
  · exact column48_1_r4_eq i k
  · exact column48_1_r5_eq i k
lemma column48_1_contains (j : Fin 6) (i k : Fin 16) :
    (column48_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction true 48 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column48_1_eq,basisFunction_wave,← mul_assoc]
  unfold column48_1Expr
  apply CBox.contains_mul_e
  · rw [← waveAmplitude_mod true 48 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp0_1_contains j i k
  · exact power48_contains_e j i k
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments48
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
namespace cm48_3_1_0
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
lemma checked : cachedMomentRuleBox column48_1 kernel3_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 48 3 true false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains_e column48_1_contains kernel3_0_contains_e
end cm48_3_1_0
namespace cm48_3_1_1
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
lemma checked : cachedMomentRuleBox column48_1 kernel3_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 48 3 true true) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains_e column48_1_contains kernel3_1_contains_e
end cm48_3_1_1
namespace cm48_4_1_0
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
lemma checked : cachedMomentRuleBox column48_1 kernel4_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 48 4 true false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains_e column48_1_contains kernel4_0_contains_e
end cm48_4_1_0
namespace cm48_4_1_1
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
lemma checked : cachedMomentRuleBox column48_1 kernel4_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 48 4 true true) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains_e column48_1_contains kernel4_1_contains_e
end cm48_4_1_1
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


lemma S_column_value (n m : Node) (d : Bool) :
    S (columnVector n d) (m,false) = -K (positiveData (columnVector n d)) 0 m.val / Q m.val := by
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

lemma S_column_value_contains {n m : Node} {d : Bool} {a : RBox}
    (ha : a.Contains (K (positiveData (columnVector n d)) 0 m.val)) :
    (a.neg.mul (qiBox m.val)).Contains (S (columnVector n d) (m,false)) := by
  rw [S_column_value,div_eq_mul_inv]
  exact RBox.contains_mul_e (RBox.neg_contains_e ha) (qiBox_contains_e m.val m.property.2)
end Numerical
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals
open scoped BigOperators

lemma sumBox_contains {ι : Type*} [Fintype ι] {a : ι → RBox} {x : ι → ℝ}
    (ha : ∀ i, (a i).Contains (x i)) : (sumBox a).Contains (∑ i, x i) := by
  constructor
  · simpa only [sumBox,Int.cast_sum,Finset.mul_sum] using Finset.sum_le_sum (fun i _ => (ha i).1)
  · simpa only [sumBox,Int.cast_sum,Finset.mul_sum] using Finset.sum_le_sum (fun i _ => (ha i).2)

lemma matrixMulBox_contains {n m k : ℕ} {a : Matrix (Fin n) (Fin m) RBox}
    {b : Matrix (Fin m) (Fin k) RBox} {A : Matrix (Fin n) (Fin m) ℝ}
    {B : Matrix (Fin m) (Fin k) ℝ} (ha : ∀ i j, (a i j).Contains (A i j))
    (hb : ∀ i j, (b i j).Contains (B i j)) (i j) :
    (matrixMulBox a b i j).Contains ((A*B) i j) := by
  exact sumBox_contains (fun l => RBox.contains_mul_e (ha i l) (hb l j))

lemma column_bound_lt {n m : ℕ} {a : Matrix (Fin n) (Fin m) RBox}
    {A : Matrix (Fin n) (Fin m) ℝ} {u v : ℤ} (hv : 0 < v)
    (ha : ∀ i j, (a i j).Contains (A i j))
    (hc : ∀ j, (∑ i, (a i j).bound)*v < precision*u) :
    ∀ j, ∑ i, |A i j| < (u:ℝ)/v := by
  intro j
  have h₁ : (precision:ℝ)*(∑ i, |A i j|) ≤ (∑ i, ((a i j).bound:ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => RBox.abs_bound_e (ha i j)
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have h₂ : (∑ i, ((a i j).bound:ℝ))*(v:ℝ) < (precision:ℝ)*u := by
    exact_mod_cast hc j
  apply (mul_lt_mul_iff_right₀ precision_pos).mp
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hv').mpr
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h₁ hv'.le) h₂

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WCertificates
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

namespace SharpPlanar.Numerical
open IntegerIntervals
open scoped BigOperators
lemma WplusBox_contains (i j : Fin 6) : (WplusBox i j).Contains (Wplus i j) := RBox.contains_rat_e _ _ (by norm_num)
lemma WminusBox_contains (i j : Fin 6) : (WminusBox i j).Contains (Wminus i j) := RBox.contains_rat_e _ _ (by norm_num)
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert48
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

namespace SharpPlanar.Numerical.U48
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma entry1_1_contains : entry1_1.Contains (umat 1 1) := by
  have h0 := K_column_contains_e (n:=node) (m:=3) (by decide) (by decide) true false cm48_3_1_0.contains
  have h1 := K_column_contains_e (n:=node) (m:=3) (by decide) (by decide) true true cm48_3_1_1.contains
  have hh := S_column_value_contains (m:=node3) h0
  change entry1_1.Contains (S (columnVector node true) (node3,false))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  decide +kernel
lemma entry2_1_contains : entry2_1.Contains (umat 2 1) := by
  have h0 := K_column_contains_e (n:=node) (m:=4) (by decide) (by decide) true false cm48_4_1_0.contains
  have h1 := K_column_contains_e (n:=node) (m:=4) (by decide) (by decide) true true cm48_4_1_1.contains
  have hh := S_column_value_contains (m:=node4) h0
  change entry2_1.Contains (S (columnVector node true) (node4,false))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  decide +kernel
lemma entries_contains (i : Fin 6) (j : Fin 2) : (entries i j).Contains (umat i j) := by
  fin_cases i <;> fin_cases j
  · exact entry0_0_contains_e
  · exact entry0_1_contains_e
  · exact entry1_0_contains_e
  · exact entry1_1_contains
  · exact entry2_0_contains_e
  · exact entry2_1_contains
  · exact entry3_0_contains_e
  · exact entry3_1_contains_e
  · exact entry4_0_contains_e
  · exact entry4_1_contains_e
  · exact entry5_0_contains_e
  · exact entry5_1_contains_e
lemma wuplus_contains (i : Fin 6) (j : Fin 2) : (wuplusBox i j).Contains ((Wplus*umat) i j) := matrixMulBox_contains WplusBox_contains entries_contains i j
lemma wuplus_column (j : Fin 2) : ∑ i, |((Wplus*umat) i j)| < (25:ℝ)/100 := by
  have hh := column_bound_lt (u:=25) (v:=100) (a:=wuplusBox) (by norm_num) wuplus_contains (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
lemma wuminus_contains (i : Fin 6) (j : Fin 2) : (wuminusBox i j).Contains ((Wminus*umat) i j) := matrixMulBox_contains WminusBox_contains entries_contains i j
lemma wuminus_column (j : Fin 2) : ∑ i, |((Wminus*umat) i j)| < (17:ℝ)/100 := by
  have hh := column_bound_lt (u:=17) (v:=100) (a:=wuminusBox) (by norm_num) wuminus_contains (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
end SharpPlanar.Numerical.U48

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators

section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [DecidableEq ι] in
lemma matrixL1_apply (A : Matrix ι κ ℝ) (x : L1Finite κ) (i : ι) :
    matrixL1 A x i = ∑ j, A i j*x j := rfl

omit [DecidableEq ι] in
lemma matrixL1_mul (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    matrixL1 (A*B) = (matrixL1 A).comp (matrixL1 B) := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toLpLin 1 1 (A*B) x = Matrix.toLpLin 1 1 A (Matrix.toLpLin 1 1 B x)
  rw [Matrix.toLpLin_mul (q:=1)]
  rfl

omit [DecidableEq ι] in
lemma matrixL1_norm_le {A : Matrix ι κ ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ j, ∑ i, |A i j| ≤ b) : ‖matrixL1 A‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  rw [l1Finite_norm_e,l1Finite_norm_e,Finset.mul_sum]
  calc
    ∑ i, |matrixL1 A x i| ≤ ∑ i, ∑ j, |A i j| * |x j| := by
      apply Finset.sum_le_sum
      intro i _
      rw [matrixL1_apply]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => A i j*x j) Finset.univ
    _ = ∑ j, (∑ i, |A i j|)* |x j| := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ ≤ ∑ j, b* |x j| := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hA j) (abs_nonneg _)

omit [DecidableEq ι] in
lemma matrixL1_norm_lt [Nonempty κ] {A : Matrix ι κ ℝ} {b : ℝ}
    (hA : ∀ j, ∑ i, |A i j| < b) : ‖matrixL1 A‖ < b := by
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun j : κ => ∑ i, |A i j|) Finset.univ_nonempty
  exact (matrixL1_norm_le (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    (fun k => hj k (Finset.mem_univ _))).trans_lt (hA j)
end

section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma approximate_inverse_estimate (A W : E →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) (x : E) :
    ‖x‖ ≤ ‖W (A x)‖/(1-δ) := by
  have he : x = W (A x)+(1-W*A) x := by simp
  have hx : ‖x‖ ≤ ‖W (A x)‖+δ*‖x‖ := calc
    _ = ‖W (A x)+(1-W*A) x‖ := congrArg norm he
    _ ≤ ‖W (A x)‖+‖(1-W*A) x‖ := norm_add_le _ _
    _ ≤ ‖W (A x)‖+δ*‖x‖ := add_le_add le_rfl ((1-W*A).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right h (norm_nonneg _)))
  apply (le_div_iff₀ (by linarith : 0 < 1-δ)).mpr
  nlinarith
end Inverse
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  (e : ι → Node × Bool) (he : Function.Injective e)
  (f : κ → Node × Bool)
lemma compressed_S_matrix :
    (finiteRestriction e he).comp (S.comp (finiteEmbedding f)) =
      matrixL1 (fun i j => S (lp.single 1 (f j) 1) (e i)) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply,finiteRestriction_apply_e]
  change S (∑ j, lp.single 1 (f j) (x j)) (e i) = _
  rw [map_sum]
  simp only [lp.coeFn_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (lp.single 1 (f j) (x j) : X) = (x j) • (lp.single 1 (f j) 1 : X) := by
    rw [← lp.single_smul]; simp
  rw [hs,map_smul]
  change x j * S (lp.single 1 (f j) 1) (e i) = S (lp.single 1 (f j) 1) (e i) * x j
  ring
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma certified_inverse_comp_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A W : E →L[ℝ] E) (U : F →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) :
    ‖((certifiedEquiv A W (h.trans_lt hd)).symm.toContinuousLinearMap).comp U‖ ≤
      ‖W.comp U‖/(1-δ) := by
  have hd0 : 0 < 1-δ := sub_pos.mpr hd
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hd0.le)
  intro x
  have he : A ((certifiedEquiv A W (h.trans_lt hd)).symm (U x)) = U x :=
    (certifiedEquiv A W (h.trans_lt hd)).apply_symm_apply _
  calc
    ‖(certifiedEquiv A W (h.trans_lt hd)).symm (U x)‖ ≤
        ‖W (A ((certifiedEquiv A W (h.trans_lt hd)).symm (U x)))‖/(1-δ) :=
      approximate_inverse_estimate A W hd h _
    _ = ‖W (U x)‖/(1-δ) := by rw [he]
    _ ≤ (‖W.comp U‖*‖x‖)/(1-δ) := div_le_div_of_nonneg_right ((W.comp U).le_opNorm x) hd0.le
    _ = (‖W.comp U‖/(1-δ))*‖x‖ := by ring
end Inverse
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteU
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exterior coupling in the finite interpolation system

Column estimates control the coupling between the central and exterior coordinates.
-/

namespace SharpPlanar.Numerical
open scoped BigOperators
lemma WUplus_column (j : Fin 48 × Fin 2) : ∑ i, |((Wplus*Umat) i j)| < (354:ℝ)/100 := by
  rcases j with ⟨n,d⟩
  fin_cases n
  · change ∑ i, |((Wplus*U7.umat) i d)| < (354:ℝ)/100
    exact (U7.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U9.umat) i d)| < (354:ℝ)/100
    exact (U9.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U12.umat) i d)| < (354:ℝ)/100
    exact (U12.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U13.umat) i d)| < (354:ℝ)/100
    exact (U13.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U15.umat) i d)| < (354:ℝ)/100
    exact (U15.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U16.umat) i d)| < (354:ℝ)/100
    exact (U16.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U19.umat) i d)| < (354:ℝ)/100
    exact (U19.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U21.umat) i d)| < (354:ℝ)/100
    exact (U21.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U24.umat) i d)| < (354:ℝ)/100
    exact (U24.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U25.umat) i d)| < (354:ℝ)/100
    exact (U25.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U27.umat) i d)| < (354:ℝ)/100
    exact (U27.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U28.umat) i d)| < (354:ℝ)/100
    exact (U28.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U31.umat) i d)| < (354:ℝ)/100
    exact (U31.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U33.umat) i d)| < (354:ℝ)/100
    exact (U33.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U36.umat) i d)| < (354:ℝ)/100
    exact (U36.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U37.umat) i d)| < (354:ℝ)/100
    exact (U37.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U39.umat) i d)| < (354:ℝ)/100
    exact (U39.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U40.umat) i d)| < (354:ℝ)/100
    exact (U40.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U43.umat) i d)| < (354:ℝ)/100
    exact (U43.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U45.umat) i d)| < (354:ℝ)/100
    exact (U45.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U48.umat) i d)| < (354:ℝ)/100
    exact (U48.wuplus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U49.umat) i d)| < (354:ℝ)/100
    exact (U49.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U51.umat) i d)| < (354:ℝ)/100
    exact (U51.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U52.umat) i d)| < (354:ℝ)/100
    exact (U52.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U55.umat) i d)| < (354:ℝ)/100
    exact (U55.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U57.umat) i d)| < (354:ℝ)/100
    exact (U57.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U60.umat) i d)| < (354:ℝ)/100
    exact (U60.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U61.umat) i d)| < (354:ℝ)/100
    exact (U61.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U63.umat) i d)| < (354:ℝ)/100
    exact (U63.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U64.umat) i d)| < (354:ℝ)/100
    exact (U64.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U67.umat) i d)| < (354:ℝ)/100
    exact (U67.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U69.umat) i d)| < (354:ℝ)/100
    exact (U69.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U72.umat) i d)| < (354:ℝ)/100
    exact (U72.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U73.umat) i d)| < (354:ℝ)/100
    exact (U73.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U75.umat) i d)| < (354:ℝ)/100
    exact (U75.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U76.umat) i d)| < (354:ℝ)/100
    exact (U76.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U79.umat) i d)| < (354:ℝ)/100
    exact (U79.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U81.umat) i d)| < (354:ℝ)/100
    exact (U81.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U84.umat) i d)| < (354:ℝ)/100
    exact (U84.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U85.umat) i d)| < (354:ℝ)/100
    exact (U85.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U87.umat) i d)| < (354:ℝ)/100
    exact (U87.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U88.umat) i d)| < (354:ℝ)/100
    exact (U88.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U91.umat) i d)| < (354:ℝ)/100
    exact (U91.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U93.umat) i d)| < (354:ℝ)/100
    exact (U93.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U96.umat) i d)| < (354:ℝ)/100
    exact (U96.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U97.umat) i d)| < (354:ℝ)/100
    exact (U97.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U99.umat) i d)| < (354:ℝ)/100
    exact (U99.wuplus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wplus*U100.umat) i d)| < (354:ℝ)/100
    exact (U100.wuplus_column_e d).trans_le (by norm_num)
lemma WUplus_norm : ‖(matrixL1 Wplus).comp (matrixL1 Umat)‖ < (354:ℝ)/100 := by
  rw [← matrixL1_mul]
  exact matrixL1_norm_lt WUplus_column
lemma inversePlus_U_norm : ‖inversePlusEquiv.toContinuousLinearMap.comp (matrixL1 Umat)‖ < (37:ℝ)/10 := by
  have hh := certified_inverse_comp_norm_le (matrixL1 Aplus) (matrixL1 Wplus) (matrixL1 Umat)
    (by norm_num : (1:ℝ)/1000 < 1) defectplus_norm_e.le
  change ‖inversePlusEquiv.toContinuousLinearMap.comp (matrixL1 Umat)‖ ≤ _ at hh
  apply hh.trans_lt
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-1/1000)).mpr
  nlinarith [WUplus_norm]
lemma WUminus_column (j : Fin 48 × Fin 2) : ∑ i, |((Wminus*Umat) i j)| < (73:ℝ)/100 := by
  rcases j with ⟨n,d⟩
  fin_cases n
  · change ∑ i, |((Wminus*U7.umat) i d)| < (73:ℝ)/100
    exact (U7.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U9.umat) i d)| < (73:ℝ)/100
    exact (U9.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U12.umat) i d)| < (73:ℝ)/100
    exact (U12.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U13.umat) i d)| < (73:ℝ)/100
    exact (U13.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U15.umat) i d)| < (73:ℝ)/100
    exact (U15.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U16.umat) i d)| < (73:ℝ)/100
    exact (U16.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U19.umat) i d)| < (73:ℝ)/100
    exact (U19.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U21.umat) i d)| < (73:ℝ)/100
    exact (U21.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U24.umat) i d)| < (73:ℝ)/100
    exact (U24.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U25.umat) i d)| < (73:ℝ)/100
    exact (U25.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U27.umat) i d)| < (73:ℝ)/100
    exact (U27.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U28.umat) i d)| < (73:ℝ)/100
    exact (U28.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U31.umat) i d)| < (73:ℝ)/100
    exact (U31.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U33.umat) i d)| < (73:ℝ)/100
    exact (U33.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U36.umat) i d)| < (73:ℝ)/100
    exact (U36.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U37.umat) i d)| < (73:ℝ)/100
    exact (U37.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U39.umat) i d)| < (73:ℝ)/100
    exact (U39.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U40.umat) i d)| < (73:ℝ)/100
    exact (U40.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U43.umat) i d)| < (73:ℝ)/100
    exact (U43.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U45.umat) i d)| < (73:ℝ)/100
    exact (U45.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U48.umat) i d)| < (73:ℝ)/100
    exact (U48.wuminus_column d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U49.umat) i d)| < (73:ℝ)/100
    exact (U49.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U51.umat) i d)| < (73:ℝ)/100
    exact (U51.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U52.umat) i d)| < (73:ℝ)/100
    exact (U52.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U55.umat) i d)| < (73:ℝ)/100
    exact (U55.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U57.umat) i d)| < (73:ℝ)/100
    exact (U57.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U60.umat) i d)| < (73:ℝ)/100
    exact (U60.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U61.umat) i d)| < (73:ℝ)/100
    exact (U61.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U63.umat) i d)| < (73:ℝ)/100
    exact (U63.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U64.umat) i d)| < (73:ℝ)/100
    exact (U64.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U67.umat) i d)| < (73:ℝ)/100
    exact (U67.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U69.umat) i d)| < (73:ℝ)/100
    exact (U69.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U72.umat) i d)| < (73:ℝ)/100
    exact (U72.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U73.umat) i d)| < (73:ℝ)/100
    exact (U73.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U75.umat) i d)| < (73:ℝ)/100
    exact (U75.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U76.umat) i d)| < (73:ℝ)/100
    exact (U76.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U79.umat) i d)| < (73:ℝ)/100
    exact (U79.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U81.umat) i d)| < (73:ℝ)/100
    exact (U81.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U84.umat) i d)| < (73:ℝ)/100
    exact (U84.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U85.umat) i d)| < (73:ℝ)/100
    exact (U85.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U87.umat) i d)| < (73:ℝ)/100
    exact (U87.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U88.umat) i d)| < (73:ℝ)/100
    exact (U88.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U91.umat) i d)| < (73:ℝ)/100
    exact (U91.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U93.umat) i d)| < (73:ℝ)/100
    exact (U93.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U96.umat) i d)| < (73:ℝ)/100
    exact (U96.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U97.umat) i d)| < (73:ℝ)/100
    exact (U97.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U99.umat) i d)| < (73:ℝ)/100
    exact (U99.wuminus_column_e d).trans_le (by norm_num)
  · change ∑ i, |((Wminus*U100.umat) i d)| < (73:ℝ)/100
    exact (U100.wuminus_column_e d).trans_le (by norm_num)
lemma WUminus_norm : ‖(matrixL1 Wminus).comp (matrixL1 Umat)‖ < (73:ℝ)/100 := by
  rw [← matrixL1_mul]
  exact matrixL1_norm_lt WUminus_column
lemma inverseMinus_U_norm : ‖inverseMinusEquiv.toContinuousLinearMap.comp (matrixL1 Umat)‖ < (37:ℝ)/10 := by
  have hh := certified_inverse_comp_norm_le (matrixL1 Aminus) (matrixL1 Wminus) (matrixL1 Umat)
    (by norm_num : (1:ℝ)/1000 < 1) defectminus_norm_e.le
  change ‖inverseMinusEquiv.toContinuousLinearMap.comp (matrixL1 Umat)‖ ≤ _ at hh
  apply hh.trans_lt
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-1/1000)).mpr
  nlinarith [WUminus_norm]
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite interpolation system

Schur complements give existence, uniqueness and norm bounds for the finite system.
-/

namespace SharpPlanar.Numerical
lemma compressed_U : RJ.comp (S.comp IE) = matrixL1 Umat := by
  rw [compressed_S_matrix]; rfl
lemma signedVU_norm_e_oai (neg : Bool) : ‖(centralV neg).comp (signedU neg)‖ ≤ (37:ℝ)/10 := by
  cases neg
  · exact (by simpa only [centralV,signedU,signedS,Bool.false_eq_true,ite_false, if_false,compressed_U] using inversePlus_U_norm.le)
  · simpa only [centralV,signedU,signedS,ite_true, if_true,ContinuousLinearMap.neg_comp,
      ContinuousLinearMap.comp_neg,compressed_U,norm_neg] using inverseMinus_U_norm.le
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.signedVU_norm_e_oai := @OAI.SharpPlanar.Numerical.signedVU_norm_e_oai
